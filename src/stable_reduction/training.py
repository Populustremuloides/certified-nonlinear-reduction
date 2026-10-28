"""Fresh matched fitting; no archived checkpoints and no instability selection."""

import copy
import json
import time
from pathlib import Path
import numpy as np
import scipy.linalg as la
import torch
from torch.utils.checkpoint import checkpoint
from .model import Model, initialize_observables, balance
from .balancing import ridge_map
from .rollout import segment_for
from .optimizer import packed, install, curvature_direction
from .certificate import certify
from .data import cases, write


def memory():
    return dict(s=[], y=[], previous_x=None, previous_g=None, moment=None)


def loss(model, V, W, pack, grad=False, window=None, starts=None):
    full, red = model.tensors(), model.tensors(V, W)
    if window is None:
        target = pack["truth"][:, 1:]
        u = pack["u"]
        f = model.lift(pack["z"][:, 0])
        r = f @ W.T
    else:
        # Truth supplies initial states only during the declared warm-up stage.
        rows = torch.arange(len(pack["truth"]))
        ids = starts[:, None] + torch.arange(window + 1)[None, :]
        target = pack["truth"][rows[:, None], ids][:, 1:]
        u = pack["u"][rows[:, None], ids[:, :-1]]
        f = model.lift(pack["z"][rows, starts])
        r = f @ W.T
    if grad:
        f.requires_grad_(True)
        r.requires_grad_(True)
    errors = torch.zeros(4, len(target))
    segment = segment_for(model)
    for offset in range(0, target.shape[1], 200):
        args = (
            f,
            r,
            target[:, offset : offset + 200],
            u[:, offset : offset + 200],
            full,
            red,
        )
        f, r, e = (
            checkpoint(segment, *args, use_reentrant=True) if grad else segment(*args)
        )
        errors = errors + e
    den = torch.stack(
        [target[:, :, :96].square().sum((1, 2)), target[:, :, -1].square().sum(1)] * 2
    ).clamp_min(1e-20)
    scores = errors / den
    full_loss = scores[:2].sum(0).mean()
    reduced_loss = scores[2:].sum(0).mean()
    z = model.lift(pack["az"])
    n = model.lift(pack["an"])
    pred = model.step(z, torch.zeros(len(z), 1), model.tensors())
    nominal = z @ model.nominal.T
    closure = (
        sum(
            ((p[:, g] - n[:, g]).square().sum() / pack["closure_energy"][i])
            for p in [pred, nominal]
            for i, g in enumerate([slice(0, 96), slice(96, 104)])
        )
        * 0.005
    )
    total = 10 * full_loss + reduced_loss + closure
    detail = dict(
        full_prediction=float(full_loss.detach()),
        reduced_prediction=float(reduced_loss.detach()),
        primary_prediction=float((10 * full_loss + reduced_loss).detach()),
        closure=float(closure.detach()),
    )
    return total, detail


def make_pack(data_cases, model, closure_energy=None):
    truth = torch.tensor(np.stack([c["truth"] for c in data_cases]))
    z = torch.tensor(np.stack([c["z"] for c in data_cases]))
    u = torch.tensor(np.stack([c["u"] for c in data_cases]))
    az = []
    an = []
    for c in data_cases[::2]:
        release = min(round(c["pulse_us"] / float(model._dt_us)), len(c["z"]) - 2)
        ids = np.arange(release, len(c["z"]) - 1, 10)
        if not len(ids):
            ids = np.arange(0, len(c["z"]) - 1, 10)
        az.append(c["z"][ids])
        an.append(c["z"][ids + 1])
    pack = dict(
        truth=truth,
        z=z,
        u=u,
        az=torch.tensor(np.concatenate(az)),
        an=torch.tensor(np.concatenate(an)),
    )
    with torch.no_grad():
        if closure_energy is None:
            a, b = model.lift(pack["az"]), model.lift(pack["an"])
            closure_energy = torch.stack(
                [
                    (b[:, g] - a[:, g]).square().sum().clamp_min(1e-16)
                    for g in [slice(0, 96), slice(96, 104)]
                ]
            )
    pack["closure_energy"] = closure_energy
    return pack


@torch.no_grad()
def matrix_fit(model, V, W, pack, rank):
    saved = {k: v.clone() for k, v in model.state_dict().items()}
    before = float(loss(model, V, W, pack)[0])
    z = model.lift(pack["az"])
    n = model.lift(pack["an"])
    a, _ = model.factors(z, torch.zeros(len(z), 1))
    anchor = np.column_stack([model.nominal.numpy(), 2 * model.aut_port.numpy()])
    proposal = ridge_map(n.numpy(), torch.cat([z, a], 1).numpy(), anchor, 0.01)
    az = model.lift(pack["z"][:, :-1:20].reshape(-1, 96))
    an = model.lift(pack["z"][:, 1::20].reshape(-1, 96))
    u = pack["u"][:, ::20].reshape(-1, 1)
    af, cf = model.factors(az, u)
    residual = (
        an.numpy() - az.numpy() @ proposal[:, :104].T - af.numpy() @ proposal[:, 104:].T
    )
    control = ridge_map(
        residual,
        cf.numpy(),
        np.column_stack([p.numpy() for p in model.control_ports]),
        0.01,
    )
    attempts = []
    for trial in range(12):
        model.load_state_dict(saved)
        f = 0.5**trial
        model.nominal.copy_(
            torch.tensor(
                saved["nominal"].numpy()
                + f * (proposal[:, :104] - saved["nominal"].numpy())
            )
        )
        model.aut_port.copy_(
            torch.tensor(
                saved["aut_port"].numpy()
                + f * (proposal[:, 104:] / 2 - saved["aut_port"].numpy())
            )
        )
        for j, p in enumerate(model.control_ports):
            p.copy_(
                saved[f"control_ports.{j}"]
                + f
                * (
                    torch.tensor(control[:, 17 * j : 17 * (j + 1)])
                    - saved[f"control_ports.{j}"]
                )
            )
        try:
            v, w, _, _ = balance(model, rank)
            certify(model, v, w, interval=False)
            value = float(loss(model, v, w, pack)[0])
            if np.isfinite(value) and value < before:
                certify(model, v, w, interval=True)
                return v, w, dict(accepted=True, fraction=f, before=before, after=value)
        except (ValueError, AssertionError, la.LinAlgError):
            pass
        attempts.append(f)
    model.load_state_dict(saved)
    return V, W, dict(accepted=False, attempted_fractions=attempts)


def plateau(history, cfg):
    if len(history) < cfg["patience"] + 1:
        return False
    recent = history[-cfg["patience"] - 1 :]
    if (
        "accepted_updates" in recent[0]
        and recent[-1]["accepted_updates"] == recent[0]["accepted_updates"]
    ):
        return False
    for key in ["full_prediction", "reduced_prediction", "primary_prediction"]:
        start = recent[0][key]
        best = min(row[key] for row in recent[1:])
        if (start - best) / max(abs(start), 1e-20) > cfg["relative_improvement"]:
            return False
    return True


def train(folder, cfg):
    folder = Path(folder)
    out = folder / "training"
    out.mkdir()
    data = dict(np.load(folder / "data/chart.npz"))
    train_cases = cases(folder / "data", "training", cfg["train_horizon_us"])
    dev_cases = cases(folder / "data", "development", cfg["train_horizon_us"])
    seed = Model(data, True, cfg["seed"])
    seed._dt_us = cfg["dt_us"]
    init = initialize_observables(seed, train_cases)
    # Both fresh arms share all coefficients before removing normalization.
    attempts = []
    snapshot = copy.deepcopy(seed.state_dict())
    for factor in [1.0, 0.5, 0.25, 0.125, 0.0625, 0.03125, 0.015625, 0.0]:
        seed.load_state_dict(snapshot)
        seed.aut_port.data.mul_(factor)
        try:
            V, W, hsv, audit = balance(seed, cfg["target_rank"])
            certify(seed, V, W, interval=False)
            certify(seed, V, W)
            attempts.append(dict(scale=factor, accepted=True))
            break
        except (ValueError, AssertionError, la.LinAlgError) as e:
            attempts.append(dict(scale=factor, accepted=False, reason=str(e)))
        write(out / "initialization_search.json", dict(attempts=attempts))
    else:
        raise ValueError(
            "No certified fresh balanced initialization; see initialization attempts. No basis substitution."
        )
    write(
        out / "initialization.json",
        dict(
            observables=init,
            port_scaling=attempts,
            balance=audit,
            seed=cfg["seed"],
            historical_checkpoint_used=False,
        ),
    )
    models = {a: copy.deepcopy(seed) for a in ["normalized", "raw"]}
    models["raw"].normalized = False
    pack = make_pack(train_cases, seed)
    dev = make_pack(dev_cases, seed, pack["closure_energy"])
    # A declared common initialization search, using training/development finiteness only.
    # This is not a seed search or selection for reduced instability.
    heads = {
        a: [copy.deepcopy(net[3].state_dict()) for net in m.nets]
        for a, m in models.items()
    }
    finite_attempts = []
    for scale in [
        1.0,
        0.5,
        0.25,
        0.125,
        0.0625,
        0.03125,
        0.015625,
        0.0078125,
        0.00390625,
        0.001,
        0.0,
    ]:
        values = {}
        with torch.no_grad():
            for arm, m in models.items():
                for net, state in zip(m.nets, heads[arm]):
                    net[3].load_state_dict(state)
                    net[3].weight.mul_(scale)
                    net[3].bias.mul_(scale)
                value = float(loss(m, V, W, pack)[0])
                development = float(loss(m, V, W, dev)[0])
                values[arm] = (
                    value if np.isfinite(value) and np.isfinite(development) else None
                )
        finite_attempts.append(
            dict(common_coefficient_head_scale=scale, training_objectives=values)
        )
        write(out / "finite_initialization.json", dict(attempts=finite_attempts))
        if all(v is not None for v in values.values()):
            break
    else:
        raise ValueError("No common finite fresh training initialization")
    geometry = {a: (V.clone(), W.clone()) for a in models}
    histories = {a: [] for a in models}
    steps = {a: 0 for a in models}
    rng = np.random.default_rng(cfg["seed"])
    phase_reports = []
    from .plotting import plot_losses

    for phase in ["warmup", "full"]:
        memories = {a: memory() for a in models}
        optimizers = {
            a: torch.optim.Adam(
                [p for p in m.parameters() if p.requires_grad], lr=cfg["warmup_lr"]
            )
            for a, m in models.items()
        }
        accepted_counts = {a: 0 for a in models}
        best = {a: float("inf") for a in models}
        wait = {a: [] for a in models}
        recovering = False
        stop_reason = "update_limit"
        for update in range(cfg[phase + "_updates"] + 1):
            window = cfg["window_steps"] if phase == "warmup" else None
            starts = (
                torch.tensor(
                    rng.integers(
                        0, pack["truth"].shape[1] - window, size=len(pack["truth"])
                    )
                )
                if window
                else None
            )
            validation_every = (
                cfg.get("warmup_validation_every", cfg["validation_every"])
                if phase == "warmup"
                else cfg["validation_every"]
            )
            if update % validation_every == 0 or update == cfg[phase + "_updates"]:
                for arm, model in models.items():
                    v, w = geometry[arm]
                    with torch.no_grad():
                        value, detail = loss(model, v, w, pack)
                        dv, dd = loss(model, v, w, dev)
                    if not np.isfinite(float(value)) or not np.isfinite(float(dv)):
                        if (
                            phase != "warmup"
                            or not (out / f"{arm}_selected.pt").exists()
                        ):
                            raise ValueError(
                                f"Nonfinite {arm} {phase} validation; no certified result reported"
                            )
                        # A window fit can damage free predictions. Reject that block,
                        # restore the last validated model, and disclose the rollback.
                        ck = torch.load(out / f"{arm}_selected.pt", weights_only=False)
                        model.load_state_dict(ck["model"])
                        v, w = ck["V"], ck["W"]
                        geometry[arm] = (v, w)
                        optimizers[arm].state.clear()
                        for group in optimizers[arm].param_groups:
                            group["lr"] *= 0.3
                        with (out / "rejected_blocks.jsonl").open("a") as f:
                            f.write(
                                json.dumps(
                                    dict(
                                        arm=arm,
                                        update=steps[arm],
                                        reason="Nonfinite free validation; warm-up block rolled back",
                                    )
                                )
                                + "\n"
                            )
                        with torch.no_grad():
                            value, detail = loss(model, v, w, pack)
                            dv, dd = loss(model, v, w, dev)
                    row = dict(
                        update=steps[arm],
                        phase=phase,
                        phase_update=update,
                        accepted_updates=accepted_counts[arm],
                        objective=float(value),
                        development_primary=dd["primary_prediction"],
                        **detail,
                    )
                    histories[arm].append(row)
                    wait[arm].append(row)
                    write(out / f"{arm}_history.json", histories[arm])
                    plot_losses(histories, out / "losses")
                    print(
                        json.dumps(dict(stage="validation", arm=arm, **row)), flush=True
                    )
                    if dd["primary_prediction"] < best[arm]:
                        best[arm] = dd["primary_prediction"]
                        torch.save(
                            dict(
                                model=model.state_dict(),
                                V=v,
                                W=w,
                                update=steps[arm],
                                phase=phase,
                                validation=dd,
                                normalized=model.normalized,
                                architecture="state-inclusive-104",
                                dt_us=cfg["dt_us"],
                            ),
                            out / f"{arm}_selected.pt",
                        )
                if (
                    phase == "full"
                    and update >= cfg["minimum_full_updates"]
                    and all(plateau(wait[a], cfg) for a in models)
                ):
                    if recovering:
                        stop_reason = "measured_plateau_after_step_size_recovery"
                        break
                    recovering = True
                    memories = {a: memory() for a in models}
                    for a in wait:
                        wait[a] = [wait[a][-1]]
                    print(
                        json.dumps(
                            dict(
                                stage="plateau_recovery",
                                action="Reset curvature and alternate 0.3x/3x diagonal step scale",
                            )
                        ),
                        flush=True,
                    )
            if update == cfg[phase + "_updates"]:
                break
            for arm, model in models.items():
                v, w = geometry[arm]
                parameters = [p for p in model.parameters() if p.requires_grad]
                model.zero_grad()
                objective, detail = loss(model, v, w, pack, True, window, starts)
                objective.backward()
                g = torch.cat(
                    [
                        (
                            p.grad.reshape(-1)
                            if p.grad is not None
                            else torch.zeros_like(p).reshape(-1)
                        )
                        for p in parameters
                    ]
                )
                if not torch.isfinite(g).all():
                    raise ValueError(f"Nonfinite {arm} gradient")
                if phase == "warmup":
                    optimizers[arm].step()
                    accepted = True
                else:
                    x = packed(parameters)
                    multiplier = (0.3 if update % 2 else 3.0) if recovering else 1.0
                    direction = curvature_direction(
                        memories[arm], x, g, cfg["full_lr"] * multiplier
                    )
                    slope = float(g @ direction)
                    before = float(objective.detach())
                    accepted = False
                    with torch.no_grad():
                        for trial in range(32):
                            install(parameters, x + (0.5**trial) * direction)
                            candidate = float(loss(model, v, w, pack)[0])
                            if (
                                np.isfinite(candidate)
                                and candidate <= before + 1e-4 * (0.5**trial) * slope
                            ):
                                dev_candidate = float(loss(model, v, w, dev)[0])
                                if np.isfinite(dev_candidate):
                                    accepted = True
                                    break
                        if not accepted:
                            install(parameters, x)
                    memories[arm]["previous_x"] = x
                    memories[arm]["previous_g"] = g
                if accepted:
                    accepted_counts[arm] += 1
                steps[arm] += 1
                with (out / "updates.jsonl").open("a") as f:
                    f.write(
                        json.dumps(
                            dict(
                                arm=arm,
                                phase=phase,
                                update=steps[arm],
                                accepted=accepted,
                                gradient_norm=float(g.norm()),
                                **detail,
                            )
                        )
                        + "\n"
                    )
                if phase == "full" and (update + 1) % cfg["matrix_every"] == 0:
                    nv, nw, matrix_report = matrix_fit(
                        model, v, w, pack, cfg["target_rank"]
                    )
                    geometry[arm] = (nv, nw)
                    with (out / "matrix_updates.jsonl").open("a") as f:
                        f.write(
                            json.dumps(
                                dict(arm=arm, update=steps[arm], **matrix_report)
                            )
                            + "\n"
                        )
                    memories[arm] = memory()
            if (
                phase == "full"
                and recovering
                and all(len(wait[a]) > cfg["patience"] for a in models)
            ):
                if any(not plateau(wait[a], cfg) for a in models):
                    recovering = False
        phase_reports.append(
            dict(phase=phase, stop_reason=stop_reason, completed_updates=update)
        )
        # Continue from the best development checkpoint, not the latest weights.
        for arm, model in models.items():
            ck = torch.load(out / f"{arm}_selected.pt", weights_only=False)
            model.load_state_dict(ck["model"])
            geometry[arm] = (ck["V"], ck["W"])
            torch.save(ck, out / f"{arm}_{phase}_selected.pt")
    for arm, model in models.items():
        V, W = geometry[arm]
        report = certify(model, V, W, out / f"{arm}_certificate")
        write(out / f"{arm}_scope.json", dict(**report, selection_uses_reserved=False))
    write(
        out / "stopping.json",
        dict(
            phases=phase_reports,
            updates=steps,
            plateau_criterion=cfg["relative_improvement"],
            patience_validation_checks=cfg["patience"],
            validation_every_updates=cfg["validation_every"],
        ),
    )
    return histories

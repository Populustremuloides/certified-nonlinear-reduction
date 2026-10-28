"""Reserved tests after freezing; stopped trajectories retain finite lower bounds."""

import csv
from pathlib import Path
import numpy as np
import torch
from .model import Model, balance
from .rollout import segment_for
from .certificate import certify
from .data import cases, write, sha
from .plotting import main_figure


@torch.no_grad()
def trajectory(model, V, W, case, threshold):
    params = model.tensors(V, W)
    state = model.lift(torch.tensor(case["z"][0:1])) @ W.T
    # Execute the exact same scripted step used in fitting, without relifting.
    segment = segment_for(model)
    outputs = [(state @ params[4].T).numpy()[0]]
    stop = None
    for k, command in enumerate(case["u"]):
        state = segment.step(state, torch.tensor(command[None]), params)
        y = (state @ params[4].T).numpy()[0]
        if not np.isfinite(y).all():
            stop = dict(step=k + 1, reason="nonfinite")
            break
        outputs.append(y)
        if np.linalg.norm(y) > threshold:
            stop = dict(
                step=k + 1,
                reason="numerical_growth_threshold",
                output_norm=float(np.linalg.norm(y)),
            )
            break
    y = np.asarray(outputs)
    n = len(y)
    truth = case["truth"]
    squared = float(np.sum((y[1:, :96] - truth[1:n, :96]) ** 2))
    energy = float(np.sum(truth[1:, :96] ** 2))
    center_squared = float(np.sum((y[1:, -1] - truth[1:n, -1]) ** 2))
    center_energy = float(np.sum(truth[1:, -1] ** 2))
    record = dict(
        state_nrmse=(
            float(np.sqrt(squared / max(energy, 1e-30))) if stop is None else None
        ),
        center_nrmse=(
            float(np.sqrt(center_squared / max(center_energy, 1e-30)))
            if stop is None
            else None
        ),
        observed_prefix_error_lower_bound=float(np.sqrt(squared / max(energy, 1e-30))),
        growth_stop=stop,
        completed_steps=n - 1,
        total_steps=len(truth) - 1,
    )
    return y, record


def evaluate(folder, cfg):
    folder = Path(folder)
    out = folder / "evaluation"
    out.mkdir()
    data = dict(np.load(folder / "data/chart.npz"))
    illustrated = (
        next(
            c
            for c in cases(folder / "data", "training")
            if c["voltage"] == 5.5 and c["pulse_us"] == 100.0
        )
        if not cfg.get("smoke")
        else cases(folder / "data", "training")[0]
    )
    test_cases = cases(folder / "data", "reserved")
    rows = []
    example = []
    series = {}
    coords = [5, 17, 59]
    n = len(illustrated["truth"])
    series["truth"] = illustrated["truth"][:, coords]
    series["time_us"] = np.arange(n) * cfg["dt_us"]
    series["input"] = np.r_[illustrated["u"][:, 0] * 5.5, 0.0]
    certification = {}
    checkpoint_hashes = {}
    for arm in ["normalized", "raw"]:
        checkpoint = folder / "training" / f"{arm}_selected.pt"
        ck = torch.load(checkpoint, weights_only=False)
        checkpoint_hashes[arm] = sha(checkpoint)
        model = Model(data, normalized=arm == "normalized", seed=cfg["seed"])
        model.load_state_dict(ck["model"])
        for rank in sorted(set([104, 9, cfg["target_rank"]] + cfg["orders"])):
            if rank == 104:
                V, W = torch.eye(104), torch.eye(104)
            else:
                V, W, _, _ = balance(model, rank)
            if arm == "normalized" and rank in [9, cfg["target_rank"]]:
                try:
                    proof = certify(model, V, W, out / f"certificate_r{rank}")
                    proof["checkpoint_sha256"] = checkpoint_hashes[arm]
                    write(out / f"certificate_r{rank}/report.json", proof)
                    certification[str(rank)] = proof
                except (ValueError, AssertionError) as e:
                    certification[str(rank)] = dict(
                        certifies_nonlinear_recurrence=False, reason=str(e)
                    )
            y, record = trajectory(model, V, W, illustrated, cfg["growth_threshold"])
            record.update(arm=arm, rank=rank)
            example.append(record)
            filled = np.full((n, 97), np.nan)
            filled[: len(y)] = y
            if rank in [104, cfg["target_rank"]]:
                series[arm + ("_full" if rank == 104 else "_r" + str(rank))] = filled[
                    :, coords
                ]
            if rank == 9:
                series[arm + "_r9_norm"] = np.linalg.norm(filled, axis=1)
            if rank in [104, 9, cfg["target_rank"]]:
                for i, case in enumerate(test_cases):
                    _, r = trajectory(model, V, W, case, cfg["growth_threshold"])
                    rows.append(
                        dict(
                            arm=arm,
                            rank=rank,
                            protocol=i,
                            voltage=case["voltage"],
                            pulse_us=case["pulse_us"],
                            **r,
                        )
                    )
    np.savez_compressed(out / "illustrated.npz", **series)
    write(
        out / "report.json",
        dict(
            illustrated=example,
            reserved=rows,
            certificates=certification,
            checkpoints=checkpoint_hashes,
            numerical_growth_is_not_proof_of_divergence=True,
            selection_used_reserved=False,
            fresh_run=True,
            published_weights_used=False,
            smoke=cfg.get("smoke", False),
        ),
    )
    with (out / "reserved_metrics.csv").open("w", newline="") as f:
        fields = [
            "arm",
            "rank",
            "protocol",
            "voltage",
            "pulse_us",
            "state_nrmse",
            "center_nrmse",
            "observed_prefix_error_lower_bound",
            "growth_stop",
            "completed_steps",
            "total_steps",
        ]
        writer = csv.DictWriter(f, fieldnames=fields)
        writer.writeheader()
        writer.writerows(rows)
    main_figure(folder, cfg)
    raw9 = next(r for r in example if r["arm"] == "raw" and r["rank"] == 9)
    norm19 = next(
        r
        for r in example
        if r["arm"] == "normalized" and r["rank"] == cfg["target_rank"]
    )
    full = [r for r in rows if r["rank"] == 104]
    reduced = [
        r for r in rows if r["arm"] == "normalized" and r["rank"] == cfg["target_rank"]
    ]
    qualifies = dict(
        certified_target=certification[str(cfg["target_rank"])][
            "certifies_nonlinear_recurrence"
        ],
        certified_nine=certification["9"]["certifies_nonlinear_recurrence"],
        raw_nine_observed_growth=raw9["growth_stop"] is not None,
        normalized_target_completed=norm19["growth_stop"] is None,
        full_reserved_under_five_percent=all(
            r["state_nrmse"] is not None
            and max(r["state_nrmse"], r["center_nrmse"]) <= 0.05
            for r in full
        ),
        normalized_target_reserved_under_fifteen_percent=all(
            r["state_nrmse"] is not None
            and max(r["state_nrmse"], r["center_nrmse"]) <= 0.15
            for r in reduced
        ),
    )
    qualifies["paper_contrast_reproduced"] = all(qualifies.values()) and not cfg.get(
        "smoke", False
    )
    qualifies["smoke_only"] = cfg.get("smoke", False)
    write(out / "qualification.json", qualifies)
    return qualifies

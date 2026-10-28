"""Physical data products generated locally, with training-only scaling."""

import hashlib
import json
from pathlib import Path
import numpy as np
import scipy.linalg as la
from scipy.integrate import solve_ivp
from .physics import Switch

TRAIN = [
    (2.0, 100.0),
    (4.0, 100.0),
    (5.5, 60.0),
    (5.5, 100.0),
    (5.5, 130.0),
    (6.4, 100.0),
]
DEVELOPMENT = [(3.1, 80.0), (4.8, 110.0), (5.8, 90.0), (6.1, 120.0)]
RESERVED = [
    (2.73, 91.0),
    (3.63, 76.0),
    (4.43, 109.0),
    (5.33, 96.0),
    (5.83, 124.0),
    (6.23, 108.0),
]


def sha(path):
    h = hashlib.sha256()
    with open(path, "rb") as f:
        for block in iter(lambda: f.read(1024 * 1024), b""):
            h.update(block)
    return h.hexdigest()


def write(path, value):
    path = Path(path)
    path.parent.mkdir(parents=True, exist_ok=True)
    tmp = path.with_suffix(path.suffix + ".tmp")
    tmp.write_text(json.dumps(value, indent=2, allow_nan=False) + "\n")
    tmp.replace(path)


def simulate(plant, voltage, pulse_us, horizon_us, dt_us):
    steps = round(horizon_us / dt_us)
    times = np.arange(steps + 1) * dt_us / 10
    states = np.zeros((steps + 1, plant.N))
    initial = np.zeros(plant.N)
    release = min(pulse_us, horizon_us) / 10
    for start, stop, command in [
        (0.0, release, voltage),
        (release, horizon_us / 10, 0.0),
    ]:
        if start == stop:
            continue

        def gap(t, x):
            return np.min(1 + x[: plant.n]) - 0.05

        gap.terminal, gap.direction = True, -1
        sol = solve_ivp(
            lambda t, x: plant.F(x, command),
            (start, stop),
            initial,
            method="BDF",
            dense_output=True,
            rtol=2e-9,
            atol=1e-11,
            max_step=0.1,
            events=gap,
        )
        if not sol.success or sol.status != 0:
            raise ValueError(
                f"Physical reference failed: {sol.message}; no clipping applied"
            )
        mask = (times >= start) & (times <= stop)
        states[mask] = sol.sol(times[mask]).T
        initial = sol.y[:, -1]
    return states


def generate(folder, cfg, groups=("training", "development")):
    folder = Path(folder)
    folder.mkdir(parents=True, exist_ok=True)
    plant = Switch()
    protocols = {"training": TRAIN, "development": DEVELOPMENT, "reserved": RESERVED}
    products = {}
    for group in groups:
        specifications = protocols[group][
            : cfg.get("protocol_limit", len(protocols[group]))
        ]
        rows = []
        for i, (voltage, pulse) in enumerate(specifications):
            path = folder / f"{group}_{i:02d}.npy"
            states = simulate(
                plant, voltage, pulse, cfg["data_horizon_us"], cfg["dt_us"]
            )
            np.save(path, states)
            rows.append(
                dict(path=path.name, voltage=voltage, pulse_us=pulse, sha256=sha(path))
            )
            print(
                json.dumps(
                    dict(
                        stage="physical_data",
                        group=group,
                        completed=i + 1,
                        total=len(specifications),
                    )
                ),
                flush=True,
            )
        products[group] = rows
    if "training" in products:
        energy = np.zeros(plant.N)
        count = 0
        for s in products["training"]:
            x = np.load(folder / s["path"])
            energy += (x * x).sum(0)
            count += len(x)
        scale = np.ones(plant.N)
        for lo, hi in [(0, plant.n), (plant.n, 2 * plant.n), (2 * plant.n, plant.N)]:
            scale[lo:hi] = max(
                float(np.sqrt(energy[lo:hi].sum() / (count * (hi - lo)))), 1e-6
            )
        J = plant.jacobian(np.zeros(plant.N)) * scale[None, :] / scale[:, None]
        block = np.zeros((97, 97))
        block[:96, :96] = J
        block[:96, -1:] = plant.B / scale[:, None] * 5.5**2
        flow = la.expm(cfg["dt_us"] / 10 * block)
        P = la.solve_discrete_lyapunov(flow[:96, :96], np.eye(96))
        readout = la.cholesky((P + P.T) / 2, lower=True)
        inverse = la.solve_triangular(readout, np.eye(96), lower=True)
        observation = np.vstack(
            [readout, (plant.C * scale) @ readout / (0.05e-6 / plant.g0)]
        )
        feature_scale = np.sqrt(energy / count) / scale
        feature_scale = np.maximum(feature_scale, 1e-6)
        np.savez_compressed(
            folder / "chart.npz",
            A=inverse @ flow[:96, :96] @ readout,
            port=inverse @ flow[:96, -1:],
            readout=readout,
            inverse=inverse,
            observation=observation,
            scale=scale,
            feature_physical_scale=feature_scale,
            dt_us=cfg["dt_us"],
        )
    manifest_path = folder / "manifest.json"
    old = json.loads(manifest_path.read_text()) if manifest_path.exists() else {}
    old.update(products)
    old["chart_sha256"] = sha(folder / "chart.npz")
    old["configuration"] = cfg
    old["scaling_uses_training_only"] = True
    write(manifest_path, old)
    return old


def cases(folder, group, horizon_us=None):
    folder = Path(folder)
    manifest = json.loads((folder / "manifest.json").read_text())
    data = dict(np.load(folder / "chart.npz"))
    sensor = la.solve(data["readout"].T, data["observation"][-1])
    result = []
    for spec in manifest[group]:
        path = folder / spec["path"]
        if sha(path) != spec["sha256"]:
            raise ValueError(f"Physical input hash mismatch: {path}")
        x = np.load(path) / data["scale"]
        if horizon_us is not None:
            x = x[: round(horizon_us / float(data["dt_us"])) + 1]
        truth = np.column_stack([x, x @ sensor])
        z = x @ data["inverse"].T
        for sign in [1.0, -1.0]:
            u = np.full((len(x) - 1, 1), sign * spec["voltage"] / 5.5)
            u[round(spec["pulse_us"] / float(data["dt_us"])) :] = 0.0
            result.append(
                dict(
                    z=z,
                    truth=truth,
                    u=u,
                    voltage=sign * spec["voltage"],
                    pulse_us=spec["pulse_us"],
                )
            )
    return result

"""Certify the actual deployed linear blocks, not approximate projection identities."""

import hashlib
import json
import numpy as np
import torch
import mpmath as mp
from .certification import storage, verify
from .interval import iv_matrix
from .data import write, sha

_CACHE = {}


@torch.no_grad()
def channels(model, V, W):
    params = model.tensors(V, W)
    return {
        "full": dict(
            A=model.nominal.numpy(),
            K=model.aut_port.numpy(),
            P=np.column_stack([p.numpy() for p in model.control_ports]),
            O=np.eye(model.q),
        ),
        "reduced": dict(
            A=params[1].numpy(),
            K=params[2].numpy(),
            P=np.column_stack([p.numpy() for p in params[3]]),
            O=V.numpy(),
        ),
    }


@torch.no_grad()
def certify(model, V, W, output=None, interval=True):
    mp.iv.dps = 60
    blocks = channels(model, V, W)
    reports = {}
    arrays = {}
    for name, c in blocks.items():
        arrays.update({name + "_" + k: v for k, v in c.items()})
        for kind in ["autonomous", "control"]:
            B = 2 * c["K"] if kind == "autonomous" else np.sqrt(2) * c["P"]
            key = name + "_" + kind
            digest = hashlib.sha256(kind.encode() + str(interval).encode())
            for k in ["A", "K", "P", "O"]:
                digest.update(np.ascontiguousarray(c[k]).tobytes())
            cache_key = digest.hexdigest()
            if cache_key in _CACHE:
                X, g, entry = _CACHE[cache_key]
            else:
                X, g = storage(c["A"], B, c["O"], kind)
                if interval:
                    print(
                        json.dumps(
                            dict(
                                stage="interval_certificate",
                                channel=key,
                                states=len(c["A"]),
                                status="checking",
                            )
                        ),
                        flush=True,
                    )
                    Bi = (
                        2 * iv_matrix(c["K"])
                        if kind == "autonomous"
                        else mp.iv.sqrt(2) * iv_matrix(c["P"])
                    )
                    entry = verify(iv_matrix(c["A"]), Bi, iv_matrix(c["O"]), X, g)
                else:
                    entry = {"gain_upper": g, "status": "Numerical candidate only"}
                _CACHE[cache_key] = (X, g, entry)
            arrays[key + "_X"] = X
            arrays[key + "_g"] = np.array(g)
            reports[key] = entry
    C = iv_matrix(model.readout.numpy())
    norm = mp.iv.sqrt(sum((v * v for v in C), mp.iv.mpf(0)))
    gf = reports["full_autonomous"]["gain_upper"]
    gr = reports["reduced_autonomous"]["gain_upper"]
    bound = norm * (
        mp.iv.mpf(reports["full_control"]["gain_upper"]) / (1 - mp.iv.mpf(gf))
        + mp.iv.mpf(reports["reduced_control"]["gain_upper"]) / (1 - mp.iv.mpf(gr))
    )
    report = dict(
        normalized=model.normalized,
        certifies_nonlinear_recurrence=bool(model.normalized and interval),
        interval_verified=interval,
        retained_dimension=V.shape[1],
        matrix_signature=model.matrix_signature(),
        gains=reports,
        complete_error_gain_upper=float(np.nextafter(float(bound.b), np.inf)),
        nominal_input_map_exactly_zero=True,
        scope="Exact-real stored full/reduced recurrence with architectural envelopes. No plant-accuracy or IEEE execution guarantee.",
    )
    if output is not None:
        output.mkdir(parents=True, exist_ok=True)
        np.savez_compressed(
            output / "witness.npz",
            V=V.numpy(),
            W=W.numpy(),
            C=model.readout.numpy(),
            **arrays
        )
        report["witness_sha256"] = sha(output / "witness.npz")
        write(output / "report.json", report)
    return report

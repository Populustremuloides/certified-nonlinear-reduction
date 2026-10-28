"""Original diagonal limited-memory BFGS direction with shared proposal cap."""

import torch


def packed(parameters):
    return torch.cat([p.detach().reshape(-1) for p in parameters])


@torch.no_grad()
def install(parameters, vector):
    offset = 0
    for p in parameters:
        p.copy_(vector[offset : offset + p.numel()].reshape_as(p))
        offset += p.numel()
    assert offset == len(vector)


def curvature_direction(memory, x, g, lr):
    if memory.get("previous_x") is not None:
        s = x - memory["previous_x"]
        y = g - memory["previous_g"]
        sy = float(s @ y)
        if sy > 1e-8 * float(s.norm() * y.norm()) and sy > 0:
            memory["s"].append(s.clone())
            memory["y"].append(y.clone())
            memory["s"] = memory["s"][-10:]
            memory["y"] = memory["y"][-10:]
    moment = memory.get("moment")
    moment = g.square() if moment is None else 0.99 * moment + 0.01 * g.square()
    memory["moment"] = moment
    diagonal = lr / (moment.sqrt() + 1e-8)
    q = g.clone()
    alphas = []
    for s, y in zip(reversed(memory["s"]), reversed(memory["y"])):
        alpha = (s @ q) / (s @ y)
        alphas.append(alpha)
        q -= alpha * y
    result = diagonal * q
    for s, y, alpha in zip(memory["s"], memory["y"], reversed(alphas)):
        result += s * (alpha - (y @ result) / (s @ y))
    direction = -result
    if not torch.isfinite(direction).all() or float(g @ direction) >= 0:
        memory["s"] = []
        memory["y"] = []
        direction = -diagonal * g
    # A common proposal cap protects line-search cost, not model dynamics.
    scale = min(1.0, 0.0005 / max(float(direction.abs().max()), 1e-30))
    return direction * scale

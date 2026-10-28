"""Original scripted recurrence; full state gradients cross checkpoint boundaries."""

from typing import List, Tuple
from weakref import WeakKeyDictionary
import torch
from torch import Tensor, nn
from torch.utils.checkpoint import checkpoint

Parameters = Tuple[Tensor, Tensor, Tensor, List[Tensor], Tensor, List[Tensor]]
_segments = WeakKeyDictionary()


class Segment(nn.Module):
    __constants__ = ["normalized", "q"]

    def __init__(self, model):
        super().__init__()
        self.nets = model.nets
        self.normalized = model.normalized
        self.q = model.q

    def step(self, state: Tensor, u: Tensor, parameters: Parameters) -> Tensor:
        V, A, K, controls, C, origins = parameters
        z = state @ V.T
        nz = torch.norm(z, p=2.0, dim=[1], keepdim=True)
        out = state @ A.T
        for j, net in enumerate(self.nets):
            if j < 2:
                h = net(z) - origins[j]
                factor = nz * h[:, :8]
            else:
                h = net(torch.cat([z, u], 1))
                factor = torch.cat([u.abs() * h, u], 1)
            if self.normalized:
                factor = factor / torch.sqrt(1 + h.square().sum(1, keepdim=True))
            if j < 2:
                out = out + factor @ K.T
            else:
                out = out + factor @ controls[j - 2].T
        return out

    def forward(
        self,
        f: Tensor,
        r: Tensor,
        reference: Tensor,
        control: Tensor,
        full: Parameters,
        red: Parameters,
    ) -> Tuple[Tensor, Tensor, Tensor]:
        # Recompute the identical zero-input network origins inside each chunk,
        # retaining their parameter derivatives during reentrant checkpointing.
        origins_f = torch.jit.annotate(List[Tensor], [])
        origins_r = torch.jit.annotate(List[Tensor], [])
        zero = torch.zeros((1, self.q), dtype=f.dtype, device=f.device)
        for j, net in enumerate(self.nets):
            if j < 2:
                origins_f.append(net(zero))
                origins_r.append(net(zero))
        full = (full[0], full[1], full[2], full[3], full[4], origins_f)
        red = (red[0], red[1], red[2], red[3], red[4], origins_r)
        errors = torch.zeros((4, reference.shape[0]), dtype=f.dtype, device=f.device)
        for actual, u in zip(reference.unbind(1), control.unbind(1)):
            f = self.step(f, u, full)
            r = self.step(r, u, red)
            df = f @ full[4].T - actual
            dr = r @ red[4].T - actual
            errors = errors + torch.stack(
                [
                    df[:, :96].square().sum(1),
                    df[:, -1].square(),
                    dr[:, :96].square().sum(1),
                    dr[:, -1].square(),
                ]
            )
        return f, r, errors


def segment_for(model):
    if model not in _segments:
        compiled = torch.jit.script(Segment(model))
        actual = dict(model.nets.named_parameters())
        scripted = dict(compiled.nets.named_parameters())
        assert actual.keys() == scripted.keys()
        assert all(
            actual[name] is scripted[name] for name in actual
        ), "Compiled parameters must be the original leaves"
        _segments[model] = compiled
    return _segments[model]

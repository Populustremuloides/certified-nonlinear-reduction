"""State-inclusive published recurrence, initialized without historical weights.

Network dimensions and normalization match mems_plateau_models_20261015.Model.
Fresh initialization is deliberately separate from the archived warm starts.
"""

import copy
import hashlib
import numpy as np
import scipy.linalg as la
import torch
from torch import nn
from .balancing import ridge_map, square_root_balance


class FixedMap(nn.Module):
    def __init__(self, matrix):
        super().__init__()
        self.register_buffer("matrix", matrix.clone())

    def forward(self, x):
        return x @ self.matrix.T


class ObservableEncoder(nn.Module):
    def __init__(self, net):
        super().__init__()
        self.net = copy.deepcopy(net)
        self.scale = 0.25

    def forward(self, z):
        h = (self.net(z) - self.net(torch.zeros(1, 96)))[:, :7]
        direction = torch.cat([h, torch.ones_like(h[:, :1])], 1) / torch.sqrt(
            1 + h.square().sum(1, keepdim=True)
        )
        return self.scale * z.norm(dim=1, keepdim=True) * direction


class Model(nn.Module):
    def __init__(self, data, normalized=True, seed=2718):
        super().__init__()
        torch.manual_seed(seed)
        self.q, self.lifted, self.normalized = 104, True, normalized
        A = torch.zeros(104, 104)
        A[:96, :96] = torch.tensor(data["A"])
        self.nominal = nn.Parameter(A, requires_grad=False)
        self.aut_port = nn.Parameter(torch.zeros(104, 8), requires_grad=False)
        self.control_ports = nn.ParameterList(
            [nn.Parameter(torch.zeros(104, 17), requires_grad=False) for _ in range(2)]
        )
        self.register_buffer("B", torch.zeros(104, 1))
        self.register_buffer(
            "readout",
            torch.cat([torch.tensor(data["observation"]), torch.zeros(97, 8)], 1),
        )
        physical_map = torch.tensor(
            data["readout"] / data["feature_physical_scale"][:, None]
        )
        old_net = nn.Sequential(
            FixedMap(physical_map), nn.Linear(96, 64), nn.ReLU(), nn.Linear(64, 16)
        )
        self.encoder = ObservableEncoder(old_net)
        nets = []
        for j in range(4):
            size = 104 + int(j >= 2)
            M = torch.eye(size)
            M[:96, :96] = physical_map
            first, last = nn.Linear(size, 64), nn.Linear(64, 16)
            with torch.no_grad():
                first.weight[:, 96:104].zero_()
                if j >= 2:
                    first.weight.zero_()
                    first.bias.zero_()
                    first.weight[0, -1] = 1.0
                    first.weight[1, -1] = -1.0
                    first.weight[2:] = 0.001 * torch.randn_like(first.weight[2:])
                    last.weight.zero_()
                    last.bias.zero_()
                    last.weight[0, :2] = 0.02
                    last.weight[1:] = 0.001 * torch.randn_like(last.weight[1:])
            nets.append(nn.Sequential(FixedMap(M), first, nn.ReLU(), last))
        self.nets = nn.ModuleList(nets)
        # The published architecture uses two identical autonomous coefficient nets.
        self.nets[1].load_state_dict(self.nets[0].state_dict())
        for p in self.control_ports:
            p.data[:96, 0] = torch.tensor(25.0 * data["port"][:, 0])
        # Well-conditioned, small nonzero autonomous injections. Subsequent scaling
        # is accepted only after full and reduced small-gain checks.
        X = la.solve_discrete_lyapunov(data["A"].T, np.eye(96))
        L = la.cholesky((X + X.T) / 2, lower=True)
        _, R = la.qr(
            np.vstack([np.sqrt(2) * L.T, 2 * data["A"].T @ X]), mode="economic"
        )
        self.aut_port.data[:96] = torch.tensor(
            la.solve_triangular(
                R, np.random.default_rng(seed).normal(size=(96, 8)), lower=False
            )
            * 0.001
        )
        self.double()

    def lift(self, z):
        return torch.cat([z, self.encoder(z)], 1)

    def tensors(self, V=None, W=None):
        if V is None:
            V, W = torch.eye(self.q), torch.eye(self.q)
        origins = [net(torch.zeros(1, self.q)) for net in self.nets[:2]]
        return (
            V,
            W @ self.nominal @ V,
            W @ self.aut_port,
            [W @ p for p in self.control_ports],
            self.readout @ V,
            origins,
        )

    def step(self, state, u, parameters):
        V, A, K, controls, C, origins = parameters
        z = state @ V.T
        out = state @ A.T
        for j, net in enumerate(self.nets):
            h = net(z) - origins[j] if j < 2 else net(torch.cat([z, u], 1))
            factor = (
                z.norm(dim=1, keepdim=True) * h[:, :8]
                if j < 2
                else torch.cat([u.abs() * h, u], 1)
            )
            if self.normalized:
                factor = factor / torch.sqrt(1 + h.square().sum(1, keepdim=True))
            out = out + factor @ (K.T if j < 2 else controls[j - 2].T)
        return out

    def factors(self, z, u):
        origins = [net(torch.zeros(1, self.q)) for net in self.nets[:2]]
        aut, control = [], []
        for j, net in enumerate(self.nets):
            h = net(z) - origins[j] if j < 2 else net(torch.cat([z, u], 1))
            value = (
                z.norm(dim=1, keepdim=True) * h[:, :8]
                if j < 2
                else torch.cat([u.abs() * h, u], 1)
            )
            if self.normalized:
                value = value / torch.sqrt(1 + h.square().sum(1, keepdim=True))
            (aut if j < 2 else control).append(value)
        return (aut[0] + aut[1]) / 2, torch.cat(control, 1)

    def matrix_signature(self):
        h = hashlib.sha256()
        for x in [
            self.nominal,
            self.aut_port,
            *self.control_ports,
            self.B,
            self.readout,
        ]:
            h.update(x.detach().numpy().tobytes())
        return h.hexdigest()


@torch.no_grad()
def initialize_observables(model, cases):
    """Regress observable closure on training data only; never insert latent poles."""
    auto = []
    following = []
    for c in cases[::2]:
        release = min(round(c["pulse_us"] / model._dt_us), len(c["z"]) - 2)
        ids = np.arange(release, len(c["z"]) - 1, 10)
        auto.append(c["z"][ids])
        following.append(c["z"][ids + 1])
    z = torch.tensor(np.concatenate(auto))
    nz = torch.tensor(np.concatenate(following))
    phi, nxt = model.encoder(z).numpy(), model.encoder(nz).numpy()
    trials = []
    for strength in [0.001, 0.01, 0.1, 1.0, 10.0, 100.0]:
        A = ridge_map(nxt, phi, strength=strength)
        radius = float(max(abs(la.eigvals(A))))
        trials.append(dict(ridge_strength=strength, radius=radius))
        if radius < 1:
            break
    else:
        raise ValueError(
            "No Schur autonomous observable regression in declared ridge grid. No synthetic poles inserted."
        )
    model.nominal[96:, 96:] = torch.tensor(A)
    physical_defect = (nz - z @ model.nominal[:96, :96].T).numpy()
    coupling = ridge_map(physical_defect, phi, strength=0.01)
    model.nominal[:96, 96:] = torch.tensor(0.01 * coupling)
    scale = np.sqrt(np.mean(phi**2, axis=0)).clip(min=1e-9)
    for net in model.nets:
        net[0].matrix[96:104, 96:104] = torch.diag(torch.tensor(1 / scale))
    # Initial forced observable injection comes from the same actual commands.
    fz = torch.tensor(np.concatenate([c["z"][:-1:20] for c in cases]))
    fn = torch.tensor(np.concatenate([c["z"][1::20] for c in cases]))
    u = torch.tensor(np.concatenate([c["u"][::20] for c in cases]))
    fp = model.encoder(fz)
    fpn = model.encoder(fn)
    _, features = model.factors(torch.cat([fz, fp], 1), u)
    K = ridge_map(
        (fpn - fp @ torch.tensor(A).T).numpy(), features.numpy(), strength=0.01
    )
    for j, port in enumerate(model.control_ports):
        port[96:] = torch.tensor(K[:, 17 * j : 17 * (j + 1)])
    return {
        "latent_nominal_radius": radius,
        "state_inclusive": True,
        "training_only": True,
        "regression_trials": trials,
    }


@torch.no_grad()
def balance(model, rank):
    U = np.column_stack(
        [
            2 * model.aut_port.numpy(),
            np.sqrt(2) * np.column_stack([p.numpy() for p in model.control_ports]),
        ]
    )
    V, W, hsv, audit = square_root_balance(
        model.nominal.numpy(), U, model.readout.numpy(), rank
    )
    if audit["retained_left_inverse_residual"] > 1e-6:
        raise ValueError("Unresolved retained projection inverse")
    return torch.tensor(V), torch.tensor(W), hsv, audit

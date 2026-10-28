"""Original square-root Stein doubling and ridge regression, without run paths."""

import numpy as np
import scipy.linalg as la


def ridge_map(target, features, anchor=None, strength=0.01):
    X = features.T
    Y = target.T
    scale = np.sqrt(np.mean(X * X, axis=1)).clip(min=1e-12)
    Z = X / scale[:, None]
    base = np.zeros((Y.shape[0], X.shape[0])) if anchor is None else anchor
    delta = (
        la.solve(
            Z @ Z.T + strength * Z.shape[1] * np.eye(Z.shape[0]),
            Z @ (Y - base @ X).T,
            assume_a="pos",
        ).T
        / scale[None, :]
    )
    return base + delta


def square_root_balance(A, U, C, rank=10):
    def compress(M):
        return la.qr(M.T, mode="economic", check_finite=False)[1].T

    lp = compress(U)
    lq = compress(C.T)
    power = A.copy()
    doublings = 0
    for _ in range(32):
        lp = compress(np.column_stack([lp, power @ lp]))
        lq = compress(np.column_stack([lq, power.T @ lq]))
        power = power @ power
        doublings += 1
        if doublings >= 18 and la.norm(power) < 1e-24:
            break
    if la.norm(power) >= 1e-24:
        raise ValueError("Infinite Stein tail did not converge")
    u, s, vt = la.svd(lq.T @ lp, full_matrices=False, check_finite=False)
    if s[rank - 1] <= 0:
        raise ValueError("No positive retained Hankel spectrum")
    V = (lp @ vt[:rank].T) / np.sqrt(s[:rank])[None, :]
    W = (u[:, :rank].T @ lq.T) / np.sqrt(s[:rank])[:, None]
    P = lp @ lp.T
    Q = lq @ lq.T
    audit = dict(
        power_norm=float(la.norm(power)),
        doublings=doublings,
        P_relative_Stein_residual=float(
            la.norm(P - A @ P @ A.T - U @ U.T) / la.norm(P)
        ),
        Q_relative_Stein_residual=float(
            la.norm(Q - A.T @ Q @ A - C.T @ C) / la.norm(Q)
        ),
        retained_left_inverse_residual=float(la.norm(W @ V - np.eye(rank))),
        cut_values=s[rank - 1 : rank + 1].tolist(),
        algorithm="Square-root Stein doubling using QR factors, at least 18 doublings and tail norm below 1e-24, dominant Hankel SVD; no Gramian ridge or eigenvalue clipping.",
    )
    return V, W, s, audit

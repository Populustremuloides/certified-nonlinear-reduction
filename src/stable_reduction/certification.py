"""Original bounded-real witnesses and directed-rounding validation."""

import numpy as np
import scipy.linalg as la
import mpmath as mp
from .interval import iv_matrix, positive_ldl


def storage(a, b, c, kind):
    n = len(a)
    if kind == "autonomous":
        for gamma in [0.995] if n == 96 else [0.8, 0.9, 0.995]:
            try:
                eps = 1e-5 * max(1.0, la.norm(c, 2) ** 2)
                x = la.solve_discrete_are(
                    a, b, c.T @ c + eps * np.eye(n), -(gamma**2) * np.eye(b.shape[1])
                )
                x = (x + x.T) / 2
                bot = b.T @ x @ b - gamma**2 * np.eye(b.shape[1])
                cross = a.T @ x @ b
                schur = a.T @ x @ a - x + c.T @ c - cross @ la.solve(bot, cross.T)
                if (
                    la.eigvalsh(x)[0] > 0
                    and la.eigvalsh(bot)[-1] < 0
                    and la.eigvalsh((schur + schur.T) / 2)[-1] < -eps / 2
                ):
                    return x, gamma
            except (ValueError, la.LinAlgError):
                continue
        raise ValueError("No subunit autonomous BRL storage found")
    eps = 1e-3 * max(1.0, la.norm(c, 2) ** 2)
    q = la.solve_discrete_lyapunov(a.T, c.T @ c + eps * np.eye(n))
    x = q + q.T
    top = x - a.T @ x @ a - c.T @ c
    top = (top + top.T) / 2
    if la.eigvalsh(top)[0] <= 0:
        raise ValueError("Auxiliary control storage top block not positive")
    cross = a.T @ x @ b
    g = b.T @ x @ b + cross.T @ la.solve(top, cross)
    gamma = 1.02 * np.sqrt(max(la.eigvalsh((g + g.T) / 2)[-1], 0.0))
    return x, float(gamma)


def verify(ai, bi, ci, x, gamma):
    xx = iv_matrix(x)
    storage_proof = positive_ldl(xx)
    top = xx - ai.T * xx * ai - ci.T * ci
    cross = -ai.T * xx * bi
    bottom = mp.iv.mpf(gamma) ** 2 * mp.iv.eye(bi.cols) - bi.T * xx * bi
    n = ai.rows
    ports = bi.cols
    block = mp.iv.matrix(n + ports)
    for i in range(n + ports):
        for j in range(n + ports):
            block[i, j] = (
                top[i, j]
                if i < n and j < n
                else (
                    cross[i, j - n]
                    if i < n
                    else cross[j, i - n] if j < n else bottom[i - n, j - n]
                )
            )
    return {
        "gain_upper": gamma,
        "positive_storage": storage_proof,
        "strict_negative_BRL": positive_ldl(block),
    }

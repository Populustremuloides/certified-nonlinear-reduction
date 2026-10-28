"""Directed-rounding LDL checks on exact stored binary coefficients."""

import mpmath as mp


def iv_matrix(array):
    return mp.iv.matrix([[mp.iv.mpf(float(v)) for v in row] for row in array])


def positive_ldl(matrix):
    n = matrix.rows
    l = [[mp.iv.mpf(0) for _ in range(n)] for _ in range(n)]
    d = []
    smallest = None
    for j in range(n):
        pivot = matrix[j, j] - sum(
            (l[j][k] ** 2 * d[k] for k in range(j)), mp.iv.mpf(0)
        )
        lower = float(pivot.a)
        upper = float(pivot.b)
        if lower <= 0:
            raise ValueError(
                f"Interval LDL pivot {j} is not strictly positive: [{lower},{upper}]"
            )
        smallest = lower if smallest is None else min(smallest, lower)
        d.append(pivot)
        l[j][j] = mp.iv.mpf(1)
        for i in range(j + 1, n):
            l[i][j] = (
                matrix[i, j]
                - sum((l[i][k] * l[j][k] * d[k] for k in range(j)), mp.iv.mpf(0))
            ) / pivot
    return {"positive_pivots": n, "minimum_pivot_lower_bound": smallest}

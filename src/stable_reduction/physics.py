"""Physical MEMS switch reconstructed from Rewienski (2003). See docs/method.md."""

import numpy as np
import scipy.linalg as la
from scipy.integrate import solve_ivp


class Switch:
    def __init__(self, n=12, m=6):
        self.n, self.m, self.N = n, m, n * (m + 2)
        self.l, self.w, self.h, self.g0 = 610e-6, 40e-6, 2.2e-6, 2.3e-6
        self.E, self.stress, self.rho = 149e9, -3.7e6, 2330.0
        self.Pa, self.mu, self.lam, self.eps = (
            1.013e5,
            1.82e-5,
            0.064e-6,
            8.8541878128e-12,
        )
        self.tau = 1e-5
        dx, dy = self.l / (n + 1), self.w / (m + 1)

        def second(k):
            return (
                np.diag(np.full(k, -2.0))
                + np.diag(np.ones(k - 1), 1)
                + np.diag(np.ones(k - 1), -1)
            )

        d2 = second(n)
        d2[0, 0] = d2[-1, -1] = -1
        d4 = (
            np.diag(np.full(n, 6.0))
            + np.diag(np.full(n - 1, -4.0), 1)
            + np.diag(np.full(n - 1, -4.0), -1)
            + np.diag(np.ones(n - 2), 2)
            + np.diag(np.ones(n - 2), -2)
        )
        d4[0, 0] = d4[-1, -1] = 7
        self.K = (
            self.tau**2
            / self.rho
            * (self.E * self.h**2 / 12 * d4 / dx**4 - self.stress * d2 / dx**2)
        )
        deriv = (np.diag(np.ones(n - 1), 1) - np.diag(np.ones(n - 1), -1)) / (2 * dx)
        self.gx = deriv
        deriv = deriv.copy()
        deriv[0, 0] = -1 / (2 * dx)
        deriv[-1, -1] = 1 / (2 * dx)
        self.px = np.kron(deriv, np.eye(m))
        self.py = np.kron(
            np.eye(n),
            (np.diag(np.ones(m - 1), 1) - np.diag(np.ones(m - 1), -1)) / (2 * dy),
        )
        self.lap = np.kron(d2 / dx**2, np.eye(m)) + np.kron(
            np.eye(n), second(m) / dy**2
        )
        self.pressure = self.tau**2 * self.Pa / (self.rho * self.h * self.g0)
        self.fluid = self.tau * self.Pa * self.g0**2 / (12 * self.mu)
        self.input_factor = (
            -3 * self.tau**2 * self.eps / (2 * self.rho * self.h * self.g0**3)
        )
        self.B = np.zeros((self.N, 1))
        self.B[n : 2 * n, 0] = self.input_factor
        self.C = np.zeros((1, self.N))
        # Interpolate to the physical center for either parity of spatial grid.
        grid = np.arange(1, n + 1) * dx
        j = np.searchsorted(grid, self.l / 2)
        if j == 0:
            self.C[0, 0] = -1
        else:
            weight = (self.l / 2 - grid[j - 1]) / (grid[j] - grid[j - 1])
            self.C[0, j - 1] = -(1 - weight)
            self.C[0, j] = -weight
        self.integral_weight = dy / self.w

    def F(self, x, voltage=0.0):
        n, m = self.n, self.m
        g = 1 + x[:n]
        v = x[n : 2 * n]
        p = x[2 * n :]
        if not np.isfinite(x).all() or np.min(g.real) <= 0.01:
            raise ValueError("Outside positive-gap domain; no clipping applied")
        gp = np.repeat(g, m)
        vp = np.repeat(v, m)
        gdot = v / (3 * g**2)
        pressure = self.pressure * self.integral_weight * p.reshape(n, m).sum(1)
        vdot = (
            2 * v**2 / (3 * g**3)
            + 3 * g**2 * (pressure - self.K @ x[:n])
            + self.input_factor * voltage**2
        )
        px, py = self.px @ p, self.py @ p
        pdot = -vp * (1 + p) / (3 * gp**3)
        pdot += (
            3
            * self.fluid
            * (gp + 4 * self.lam / self.g0)
            * np.repeat(self.gx @ x[:n], m)
            * (1 + p)
            * px
        )
        pdot += (
            self.fluid
            * (gp**2 + 6 * self.lam / self.g0 * gp)
            * ((1 + p) * (self.lap @ p) + px**2 + py**2)
        )
        return np.r_[gdot, vdot, pdot]

    def jacobian(self, x, voltage=0.0):
        eye = np.eye(self.N) * 1e-25
        return np.column_stack(
            [np.imag(self.F(x.astype(complex) + 1j * d, voltage)) / 1e-25 for d in eye]
        )

    def simulate(
        self, voltage, end=100.0, pulse_end=10.0, V=None, W=None, rtol=2e-8, atol=1e-10
    ):
        V = np.eye(self.N) if V is None else V
        W = np.eye(self.N) if W is None else W
        t_all = []
        x_all = []
        z = np.zeros(V.shape[1])
        failure = None
        for start, stop, u in [
            (0.0, min(pulse_end, end), voltage),
            (min(pulse_end, end), end, 0.0),
        ]:
            if start == stop:
                continue

            def rhs(t, a):
                return W @ self.F(V @ a, u)

            def gap(t, a):
                return np.min(1 + (V @ a)[: self.n]) - 0.05

            gap.terminal = True
            gap.direction = -1

            def excess(t, a):
                return 1e4 - np.linalg.norm(V @ a)

            excess.terminal = True
            excess.direction = -1
            try:
                sol = solve_ivp(
                    rhs,
                    (start, stop),
                    z,
                    method="BDF",
                    rtol=rtol,
                    atol=atol,
                    events=[gap, excess],
                    dense_output=True,
                    max_step=0.5,
                )
                times = np.linspace(
                    start, sol.t[-1], max(2, int((sol.t[-1] - start) * 10) + 1)
                )
                states = (V @ sol.sol(times)).T
                if t_all:
                    times = times[1:]
                    states = states[1:]
                t_all.extend(times)
                x_all.extend(states)
                z = sol.y[:, -1]
                if sol.status != 0:
                    failure = (
                        "gap_domain_exit"
                        if len(sol.t_events[0])
                        else (
                            "state_growth_threshold"
                            if len(sol.t_events[1])
                            else sol.message
                        )
                    )
                    break
            except (ValueError, FloatingPointError) as ex:
                failure = str(ex)
                break
        return np.asarray(t_all), np.asarray(x_all), failure

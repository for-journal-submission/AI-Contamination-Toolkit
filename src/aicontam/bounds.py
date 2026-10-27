"""Bounds of Theorem 2(ii)-(iv) when the effect of AI is not homogeneous.

(ii) bounded outcome (Manski): needs TPR and a detector that errs at the same rates for
     everyone, whatever the answer. For every arm z,
     E[g(Y(0),X)] in [G_z + alpha_z (g_min - A_z), G_z + alpha_z (g_max - A_z)],
     with alpha_z = (S_z - FPR)/(TPR - FPR) and A_z = (H_z - FPR G_z)/(S_z - FPR), H_z = E[g S | z].
(iii) monotone treatment response: G_0 < G_1 gives E[g(Y(0),X)] >= G_M, and G_0 > G_1 gives <= G_M.
(iv) monotone treatment selection (M >= 2): arm M-1 below the line through arms M-2 and M
     gives E[g(Y(0),X)] >= theta_{M-1,M}; above gives <=.
"""

from dataclasses import dataclass

import numpy as np
import pandas as pd

from ._data import Arm, prepare, split_arms
from .calibrate import as_rate
from .estimate import theta


def _bounds_from_arms(A, fpr, tpr, gmin, gmax):
    """All bounds for every column, from arm moments and point values of FPR and TPR."""
    M = len(A) - 1
    K = A[0].Y.shape[1]
    rows = {}
    if tpr is not None:
        for z, arm in enumerate(A):
            alpha = (arm.Sbar - fpr) / (tpr - fpr)
            Az = (arm.H - fpr * arm.G) / (arm.Sbar - fpr)
            rows[f"(ii) arm {z}"] = (arm.G + alpha * (gmin - Az), arm.G + alpha * (gmax - Az))
    lo, hi = np.full(K, -np.inf), np.full(K, np.inf)
    up = A[0].G < A[1].G
    rows["(iii) MTR"] = (np.where(up, A[M].G, -np.inf), np.where(up, np.inf, A[M].G))
    if M >= 2:
        a, m, b = A[M - 2], A[M - 1], A[M]
        line = b.G + (a.G - b.G) * (m.Sbar - b.Sbar) / (a.Sbar - b.Sbar)
        t = theta(m.G, b.G, m.Sbar, b.Sbar, fpr)
        below, above = m.G < line, m.G > line
        rows["(iv) MTS"] = (np.where(below, t, -np.inf), np.where(above, t, np.inf))
    for l, h in rows.values():
        lo, hi = np.maximum(lo, l), np.minimum(hi, h)
    rows["intersection"] = (lo, hi)
    return rows


@dataclass
class BoundsResult:
    labels: list
    rows: dict
    ci: dict
    level: float

    def summary(self):
        out = []
        for name, (lo, hi) in self.rows.items():
            for k, lab in enumerate(self.labels):
                r = {"bound": name, "category": lab, "low": lo[k], "high": hi[k]}
                if name in self.ci:
                    r["ci_low"], r["ci_high"] = self.ci[name][0][k], self.ci[name][1][k]
                out.append(r)
        return pd.DataFrame(out).set_index(["category", "bound"]).sort_index(level=0, sort_remaining=False)

    @property
    def crossed(self):
        """Categories whose estimated bounds cross: sampling noise, or the assumptions fail.
        Use the bootstrap confidence bounds there."""
        lo, hi = self.rows["intersection"]
        return [lab for lab, l, h in zip(self.labels, lo, hi) if l > h]

    def __str__(self):
        out = self.summary().to_string(float_format=lambda v: f"{v:.4f}")
        if self.crossed:
            out += f"\nThe estimated bounds cross for {self.crossed}; read the ci columns there."
        return out


def bounds(y, s, z, fpr, tpr=None, gmin=0.0, gmax=1.0, n_boot=0, level=0.95, seed=0,
           categorical=None, categories=None):
    """Bounds of Theorem 2(ii)-(iv) and their intersection.

    With `n_boot > 0`, each endpoint also gets a one-sided bootstrap confidence bound (the
    lower endpoint's lower quantile and the upper endpoint's upper quantile, each at
    1 - level), resampling participants within arms and redrawing FPR and TPR from their
    samples. Part (ii) is reported only when `tpr` is given.
    """
    Y, S, z, labels = prepare(y, s, z, categorical, categories)
    fpr, tpr = as_rate(fpr), as_rate(tpr)
    A = split_arms(Y, S, z)
    rows = _bounds_from_arms(A, fpr.value, None if tpr is None else tpr.value, gmin, gmax)
    ci = {}
    if n_boot:
        rng = np.random.default_rng(seed)
        draws = {k: ([], []) for k in rows}
        for _ in range(n_boot):
            Ab = []
            for arm in A:
                i = rng.integers(0, arm.n, arm.n)
                Ab.append(Arm(arm.Y[i], arm.S[i]))
            rb = _bounds_from_arms(Ab, fpr.draw(rng), None if tpr is None else tpr.draw(rng), gmin, gmax)
            for k, (l, h) in rb.items():
                draws[k][0].append(l)
                draws[k][1].append(h)
        q = 1 - level
        ci = {k: (np.quantile(np.array(l), q, axis=0, method="lower"),
                  np.quantile(np.array(h), 1 - q, axis=0, method="higher"))
              for k, (l, h) in draws.items()}
    return BoundsResult(labels, rows, ci, level)

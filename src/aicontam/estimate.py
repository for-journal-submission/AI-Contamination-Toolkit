"""The IV estimator of Theorem 2(i), its standard error, and the Anderson-Rubin set (Theorem 3).

Notation follows the paper. Arm z has flagged share S_z and mean answer G_z. The estimate
from arms a (weaker friction) and b (stronger friction) is the height at FPR of the line
through the two arms,

    theta_ab = G_b - (G_a - G_b) (S_b - FPR) / (S_a - S_b).
"""

from dataclasses import dataclass, field

import numpy as np
import pandas as pd
from scipy.stats import norm

from ._data import prepare, split_arms
from .calibrate import as_rate


def theta(Ga, Gb, Sa, Sb, fpr):
    """Height at FPR of the line through arms a and b."""
    return Gb - (Ga - Gb) * (Sb - fpr) / (Sa - Sb)


def _moment_variance(arm_a, arm_b, fpr, k, t):
    """Variance of the identifying equation M(t) for column k, divided by nothing (finite N)."""
    Ya, Yb = arm_a.Y[:, k], arm_b.Y[:, k]
    Ga, Gb, Sa, Sb = Ya.mean(), Yb.mean(), arm_a.Sbar, arm_b.Sbar
    vb = np.var((Sa - fpr.value) * Yb + (t - Ga) * arm_b.S) / arm_b.n
    va = np.var((Sb - fpr.value) * Ya + (t - Gb) * arm_a.S) / arm_a.n
    vf = (Gb - Ga) ** 2 * fpr.value * (1 - fpr.value) / fpr.n
    return vb + va + vf


def _quadratic_set(coef):
    """Solve c2 t^2 + c1 t + c0 <= 0. Returns a list of closed intervals (may be unbounded)."""
    c2, c1, c0 = coef
    if abs(c2) < 1e-14:
        if abs(c1) < 1e-14:
            return [(-np.inf, np.inf)] if c0 <= 0 else []
        r = -c0 / c1
        return [(-np.inf, r)] if c1 > 0 else [(r, np.inf)]
    disc = c1 ** 2 - 4 * c2 * c0
    if disc < 0:
        return [] if c2 > 0 else [(-np.inf, np.inf)]
    r1, r2 = sorted(((-c1 - np.sqrt(disc)) / (2 * c2), (-c1 + np.sqrt(disc)) / (2 * c2)))
    return [(r1, r2)] if c2 > 0 else [(-np.inf, r1), (r2, np.inf)]


def anderson_rubin(arm_a, arm_b, fpr, k, level=0.95):
    """Anderson-Rubin set {t : M(t)^2 <= z^2 Var M(t)}, valid at any first-stage strength."""
    c = norm.ppf(0.5 + level / 2)
    Ga, Gb = arm_a.G[k], arm_b.G[k]
    D = arm_a.Sbar - arm_b.Sbar

    def f(t):
        M = (t - Gb) * D - (arm_b.Sbar - fpr.value) * (Gb - Ga)
        return M ** 2 - c ** 2 * _moment_variance(arm_a, arm_b, fpr, k, t)

    # f is a quadratic in t, so three values give its coefficients exactly
    f0, f1, fm = f(0.0), f(1.0), f(-1.0)
    return _quadratic_set(((f1 + fm) / 2 - f0, (f1 - fm) / 2, f0))


@dataclass
class IVResult:
    """Estimates of E[g(Y(0), X)] from one pair of arms."""

    labels: list
    estimate: np.ndarray
    se: np.ndarray
    ar_sets: list
    arms: tuple
    first_stage: float
    first_stage_se: float
    fpr: object
    level: float
    lam: float = field(repr=False, default=np.nan)

    def ci(self):
        c = norm.ppf(0.5 + self.level / 2)
        return np.column_stack([self.estimate - c * self.se, self.estimate + c * self.se])

    def summary(self):
        ci = self.ci()
        ar = ["  U  ".join(f"[{lo:.4f}, {hi:.4f}]" for lo, hi in s) or "empty" for s in self.ar_sets]
        return pd.DataFrame({"estimate": self.estimate, "se": self.se, "ci_low": ci[:, 0],
                             "ci_high": ci[:, 1], "anderson_rubin": ar}, index=self.labels)

    def __str__(self):
        a, b = self.arms
        head = (f"IV design, arms {a} and {b}: first stage {self.first_stage:.4f} "
                f"(se {self.first_stage_se:.4f}), FPR {self.fpr.value:.4f}, lambda {self.lam:.3f}\n")
        return head + self.summary().to_string(float_format=lambda v: f"{v:.4f}")


def friction_iv(y, s, z, fpr, arms=None, level=0.95, categorical=None, categories=None):
    """IV estimate of the distribution of human answers (Theorem 2(i)).

    Parameters
    ----------
    y : answers, one per participant. Text labels give the share of each category; a numeric
        vector gives its mean; a 2-D array gives the mean of each column (one g per column).
    s : detector signal, 0 or 1.
    z : arm, coded 0 (most relaxed friction) to M (strongest).
    fpr : `Rate` from `estimate_fpr`, or a float if FPR is known.
    arms : the pair of arms (a, b) with a < b. Default (M - 1, M), the two strongest.
    level : coverage of the Wald interval and the Anderson-Rubin set.
    """
    Y, S, z, labels = prepare(y, s, z, categorical, categories)
    fpr = as_rate(fpr)
    a, b = arms if arms is not None else (z.max() - 1, z.max())
    if not 0 <= a < b <= z.max():
        raise ValueError("arms must satisfy 0 <= a < b <= M")
    A = split_arms(Y, S, z)
    arm_a, arm_b = A[a], A[b]
    D = arm_a.Sbar - arm_b.Sbar
    est = theta(arm_a.G, arm_b.G, arm_a.Sbar, arm_b.Sbar, fpr.value)
    se = np.sqrt([_moment_variance(arm_a, arm_b, fpr, k, est[k]) / D ** 2 for k in range(Y.shape[1])])
    ar = [anderson_rubin(arm_a, arm_b, fpr, k, level) for k in range(Y.shape[1])]
    fs_se = np.sqrt(np.var(arm_a.S) / arm_a.n + np.var(arm_b.S) / arm_b.n)
    return IVResult(labels, est, se, ar, (a, b), D, fs_se, fpr, level, (arm_b.Sbar - fpr.value) / D)


def no_correction(y, categorical=None, categories=None):
    """Mean of every answer as observed, with its binomial standard error."""
    from ._data import outcome_matrix
    Y, labels = outcome_matrix(y, categorical, categories)
    return pd.DataFrame({"estimate": Y.mean(0), "se": Y.std(0) / np.sqrt(len(Y))}, index=labels)


def delete_flagged(y, s, categorical=None, categories=None):
    """Mean of the answers the detector does not flag (biased: Theorem 1)."""
    from ._data import outcome_matrix
    Y, labels = outcome_matrix(y, categorical, categories)
    kept = Y[np.asarray(s) == 0]
    return pd.DataFrame({"estimate": kept.mean(0), "se": kept.std(0) / np.sqrt(len(kept))}, index=labels)


def compare(y, s, z, fpr, arms=None, categorical=None, categories=None):
    """Estimates of the three methods of Table 2 side by side."""
    iv = friction_iv(y, s, z, fpr, arms, categorical=categorical, categories=categories)
    out = pd.concat({"no correction": no_correction(y, categorical, categories),
                     "delete flagged": delete_flagged(y, s, categorical, categories),
                     "IV design": iv.summary()[["estimate", "se"]]}, axis=1)
    return out

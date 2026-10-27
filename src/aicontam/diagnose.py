"""Diagnostics: the arms, the first stage, a test of homogeneity, and a plot of the contamination curve."""

import numpy as np
import pandas as pd
from scipy.stats import norm

from ._data import Arm, prepare, split_arms
from .calibrate import as_rate
from .estimate import friction_iv


def arm_table(y, s, z, categorical=None, categories=None):
    """Size, flagged share, and mean answer of every arm: the points of the contamination curve."""
    Y, S, z, labels = prepare(y, s, z, categorical, categories)
    rows = []
    for a, arm in enumerate(split_arms(Y, S, z)):
        r = {"arm": a, "n": arm.n, "flagged": arm.Sbar, "flagged_se": arm.S.std() / np.sqrt(arm.n)}
        r.update({f"mean[{lab}]": g for lab, g in zip(labels, arm.G)})
        rows.append(r)
    return pd.DataFrame(rows).set_index("arm")


def first_stage(s, z):
    """Drop in the flagged share between adjacent arms, S_z - S_{z+1}, with its t statistic.

    A small t (say below 3) means a weak first stage: use the Anderson-Rubin set rather than
    the Wald interval.
    """
    S = np.asarray(s, dtype=float)
    z = np.asarray(z)
    rows = []
    for a in range(z.max()):
        sa, sb = S[z == a], S[z == a + 1]
        d = sa.mean() - sb.mean()
        se = np.sqrt(sa.var() / len(sa) + sb.var() / len(sb))
        rows.append({"arms": f"{a}-{a + 1}", "drop": d, "se": se, "t": d / se})
    return pd.DataFrame(rows).set_index("arms")


def _gaps(A):
    """Height of each middle arm above the line through its two neighbors."""
    out = []
    for m in range(1, len(A) - 1):
        a, c, b = A[m - 1], A[m], A[m + 1]
        line = b.G + (a.G - b.G) * (c.Sbar - b.Sbar) / (a.Sbar - b.Sbar)
        out.append(c.G - line)
    return np.array(out)


def homogeneity_test(y, s, z, n_boot=999, seed=0, categorical=None, categories=None):
    """With three or more arms, test that every middle arm lies on the line through its neighbors.

    Under homogeneity (Theorem 2(i)) all arms lie on one line. A gap far from zero rejects it;
    its sign says whether the curve is convex (arm below) or concave (arm above), which
    Theorem 2(iv) uses. Standard errors come from a bootstrap within arms.
    """
    Y, S, z, labels = prepare(y, s, z, categorical, categories)
    if z.max() < 2:
        raise ValueError("the test needs at least three arms")
    A = split_arms(Y, S, z)
    gap = _gaps(A)
    rng = np.random.default_rng(seed)
    boot = []
    for _ in range(n_boot):
        Ab = [Arm(arm.Y[i], arm.S[i]) for arm in A for i in [rng.integers(0, arm.n, arm.n)]]
        boot.append(_gaps(Ab))
    se = np.array(boot).std(0)
    rows = []
    for m in range(len(gap)):
        for k, lab in enumerate(labels):
            t = gap[m, k] / se[m, k]
            rows.append({"middle arm": m + 1, "category": lab, "gap": gap[m, k], "se": se[m, k],
                         "p_value": 2 * norm.sf(abs(t)), "side": "below" if gap[m, k] < 0 else "above"})
    return pd.DataFrame(rows).set_index(["middle arm", "category"])


def plot_curve(y, s, z, fpr, column=0, ax=None, categorical=None, categories=None):
    """Plot the arms at (flagged share, mean answer), the line through the two strongest arms,
    and the IV estimate at FPR, as in Figure 1 of the paper. `column` picks the category."""
    import matplotlib.pyplot as plt

    Y, S, z, labels = prepare(y, s, z, categorical, categories)
    fpr = as_rate(fpr)
    k = labels.index(column) if column in labels else column
    A = split_arms(Y, S, z)
    if ax is None:
        _, ax = plt.subplots(figsize=(4.5, 3.5))
    xs = np.array([a.Sbar for a in A])
    ys = np.array([a.G[k] for a in A])
    ax.errorbar(xs, ys, xerr=[1.96 * a.S.std() / np.sqrt(a.n) for a in A],
                yerr=[1.96 * a.Y[:, k].std() / np.sqrt(a.n) for a in A], fmt="o", color="k", capsize=2)
    for a, (x, v) in enumerate(zip(xs, ys)):
        ax.annotate(f"arm {a}", (x, v), textcoords="offset points", xytext=(5, 5), fontsize=8)
    iv = friction_iv(Y, S, z, fpr)
    a, b = iv.arms
    grid = np.linspace(fpr.value, xs[a], 50)
    ax.plot(grid, ys[b] + (ys[a] - ys[b]) * (grid - xs[b]) / (xs[a] - xs[b]), "--", color="tab:blue")
    ax.errorbar([fpr.value], [iv.estimate[k]], yerr=[1.96 * iv.se[k]], fmt="*", ms=10, color="tab:blue",
                capsize=2, label=f"IV estimate {iv.estimate[k]:.3f}")
    ax.axvline(fpr.value, color="gray", lw=0.8)
    ax.set_xlabel("flagged share")
    ax.set_ylabel("mean answer" if labels[k] == "mean" else f"share {labels[k]}")
    ax.legend(frameon=False, fontsize=8)
    return ax

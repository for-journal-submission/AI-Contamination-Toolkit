"""Table 2: Monte Carlo of no correction, deleting flagged answers, and the IV design.

Each simulated survey draws n employees from a population built by build_populations.py. The friction is kept
for 80% of them (Z = 1) and relaxed for the rest (Z = 0). Without the friction, 70% use AI, more often in low
rating groups. The friction stops 80% of them. FPR is estimated from 300 pre-AI answers. For each theme:
  no correction   share of answers coded as the theme
  deletion        share among the answers the detector does not flag
  IV design       theta_01 = G1 - (G0 - G1)(S1 - FPR)/(S0 - S1), with a delta-method interval
Bias, error, and coverage are averaged over the 18 theme shares (six themes in three questions). Bias and error
are relative to the true share.

    python3 table2.py        # about 30 s; prints the rows of Table 2
"""
from pathlib import Path

import numpy as np
from scipy.stats import norm

HERE = Path(__file__).resolve().parent
ITEMS = ["headline", "pros", "cons"]
COLUMNS = [("fpr10", 0.0), ("fpr15", 0.0), ("fpr20", 0.0), ("fpr15", 0.3)]   # detector, share of AI answers evading it
RHO, ALPHA0, SHIFT, STOP, M, REPS = 0.8, 0.70, np.array([1.5, 0.5, 0.0]), 0.8, 300, 1000
Z95 = norm.ppf(0.975)


def population(item, detector, evade):
    pop = dict(np.load(HERE / "populations" / f"pop_{item}_{detector}.npz"))
    if evade:
        pop["f1"] = pop["f1"] * (np.random.default_rng(5).uniform(size=len(pop["f1"])) >= evade)
    # Pr(use AI without the friction): logistic in the rating group, intercept chosen by bisection so the mean is ALPHA0
    lo, hi = -20.0, 20.0
    for _ in range(100):
        b = (lo + hi) / 2
        lo, hi = (b, hi) if (1 / (1 + np.exp(-(SHIFT[pop["x"]] + b)))).mean() < ALPHA0 else (lo, b)
    pop["use"] = 1 / (1 + np.exp(-(SHIFT[pop["x"]] + b)))
    return pop


def survey(pop, n, rng):
    """Estimates and standard errors of the six theme shares in one simulated survey."""
    i = rng.integers(0, len(pop["x"]), size=n)
    Z = rng.uniform(size=n) < RHO
    W = (rng.uniform(size=n) < pop["use"][i]) & (~Z | (rng.uniform(size=n) >= STOP))
    Y = np.eye(6)[np.where(W, pop["r1"][i], pop["r0"][i])]
    S = np.where(W, pop["f1"][i], pop["f0"][i])
    fpr = rng.choice(pop["f0"], size=M).mean()
    kept = Y[S == 0].mean(0)
    G1, G0, S1, S0 = Y[Z].mean(0), Y[~Z].mean(0), S[Z].mean(), S[~Z].mean()
    lam, slope = (S1 - fpr) / (S0 - S1), (G0 - G1) / (S0 - S1)
    var_iv = ((1 + lam) ** 2 * (Y[Z] - np.outer(S[Z], slope)).var(0) / Z.sum()
              + lam ** 2 * (Y[~Z] - np.outer(S[~Z], slope)).var(0) / (~Z).sum() + slope ** 2 * fpr * (1 - fpr) / M)
    est = {"none": Y.mean(0), "delete": kept, "iv": G1 + lam * (G1 - G0)}
    se = {"none": np.sqrt(Y.mean(0) * (1 - Y.mean(0)) / n), "delete": np.sqrt(kept * (1 - kept) / (S == 0).sum()),
          "iv": np.sqrt(var_iv)}
    return est, se


LABELS = {"none": "No correction", "delete": "Delete flagged answers", "iv": "IV Design"}
for panel, n in (("A", 3000), ("B", 6000)):
    print(f"% Panel {panel}: N = {n:,}; columns TPR/FPR 89/10, 92/15, 94/21, 64/15; Bias | Error | Coverage (%)")
    cells = {k: np.zeros((3, len(COLUMNS))) for k in LABELS}
    for c, (detector, evade) in enumerate(COLUMNS):
        stats = {k: [[], [], []] for k in LABELS}
        for item in ITEMS:
            pop = population(item, detector, evade)
            truth = np.eye(6)[pop["r0"]].mean(0)
            rng = np.random.default_rng(1)
            runs = [survey(pop, n, rng) for _ in range(REPS)]
            for k in LABELS:
                est = np.array([r[0][k] for r in runs])
                se = np.array([r[1][k] for r in runs])
                stats[k][0].append(np.abs(est.mean(0) - truth) / truth)
                stats[k][1].append(np.abs(est - truth).mean(0) / truth)
                stats[k][2].append((np.abs(est - truth) <= Z95 * se).mean(0))
        for k in LABELS:
            cells[k][:, c] = [100 * np.concatenate(s).mean() for s in stats[k]]
    for k, label in LABELS.items():
        print(label + " & " + " & ".join(f"{v:.1f}" for v in cells[k].ravel()) + r" \\")

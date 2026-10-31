"""Simulated data: the bat-and-ball example of Figure 1 of the paper.

Participants answer the bat-and-ball question. Y = 1 if the answer is wrong (10 cents), the
target is the share who would answer wrong without AI, and AI always answers right. There
are three arms of friction. As in Figure 1 of the paper:

    type            share   uses AI in arms   wrong without AI
    always-taker      5%    0, 1, 2           80%
    stopped by 2      5%    0, 1              60%
    complier         20%    0                 40%
    never-taker      70%    none              50%

so 30, 10, and 5% use AI in arms 0, 1, and 2, and the truth is 50%. The detector flags human
answers at FPR = 0.1 and AI answers at TPR = 0.9.
"""

import numpy as np
import pandas as pd

TYPES = pd.DataFrame({"share": [0.05, 0.05, 0.20, 0.70], "uses_ai_up_to_arm": [2, 1, 0, -1],
                      "wrong": [0.8, 0.6, 0.4, 0.5]},
                     index=["always-taker", "stopped by 2", "complier", "never-taker"])


def simulate_batball(n=3000, arm_shares=(1 / 3, 1 / 3, 1 / 3), wrong=None, ai_wrong=0.0, fpr=0.1,
                     tpr=0.9, arms=None, seed=None):
    """One simulated survey. Returns a DataFrame with the observed columns `arm`, `wrong`,
    `flagged` and, for teaching, the hidden columns `type`, `uses_ai`, `wrong_without_ai`.

    `wrong` overrides the four types' error rates without AI; equal rates make the effect of
    AI homogeneous (Theorem 2(i) holds exactly). `arms` takes an assignment from
    `assign_arms` instead of drawing one from `arm_shares`.
    """
    from .design import assign_arms

    rng = np.random.default_rng(seed)
    rates = TYPES["wrong"].to_numpy() if wrong is None else np.asarray(wrong, dtype=float)
    k = rng.choice(len(TYPES), size=n, p=TYPES["share"].to_numpy())
    z = assign_arms(n, arm_shares, rng) if arms is None else np.asarray(arms)
    w = (z <= TYPES["uses_ai_up_to_arm"].to_numpy()[k]).astype(int)
    y0 = (rng.uniform(size=n) < rates[k]).astype(int)
    y1 = (rng.uniform(size=n) < ai_wrong).astype(int)
    s = np.where(w == 1, rng.uniform(size=n) < tpr, rng.uniform(size=n) < fpr).astype(int)
    return pd.DataFrame({"arm": z, "wrong": np.where(w == 1, y1, y0), "flagged": s,
                         "type": TYPES.index[k], "uses_ai": w, "wrong_without_ai": y0})


def batball_population(n_per_arm=100_000):
    """Exact version of Figure 1: every arm holds the population shares with no sampling noise
    (each type, answer and signal cell has exactly its expected count). Arm means then equal
    the population values of the paper: (0.34, 0.35), (0.18, 0.43), (0.14, 0.46)."""
    rows = []
    for z in range(3):
        for (_, t) in TYPES.iterrows():
            nt = round(n_per_arm * t["share"])
            ai = z <= t["uses_ai_up_to_arm"]
            for y in (1, 0):
                ny = round(nt * (t["wrong"] if y else 1 - t["wrong"]))
                yobs = 0 if ai else y
                rate = 0.9 if ai else 0.1
                nf = round(ny * rate)
                rows.append(pd.DataFrame({"arm": z, "wrong": yobs, "flagged": [1] * nf + [0] * (ny - nf)}))
    return pd.concat(rows, ignore_index=True)


def pre_ai_signals(m=300, fpr=0.1, seed=None):
    """Signals on m answers written before AI, from which FPR is estimated."""
    return (np.random.default_rng(seed).uniform(size=m) < fpr).astype(int)


def deletion_bias(y0, y1, w, s):
    """The two terms of Theorem 1 in data where the potential answers are known (a simulation).

    Returns (AI answers kept, human answers selected); their sum is the bias of deleting
    flagged answers.
    """
    y0, y1, w, s = (np.asarray(v, dtype=float) for v in (y0, y1, w, s))
    kept = s == 0
    q = w[kept].mean()
    h_kept = y0[kept & (w == 0)].mean()
    ai_term = q * (y1[kept & (w == 1)].mean() - h_kept) if q > 0 else 0.0
    return ai_term, h_kept - y0.mean()

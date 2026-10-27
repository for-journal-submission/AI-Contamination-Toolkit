"""Coding open-ended answers with an LLM, corrected by a random human-coded subset (Lemma coding).

Each answer is sent to a human coder with a known probability pi_i (xi_i = 1 if it was). The
pseudo-outcome

    Y~_i = mu_i + (xi_i / pi_i) (1{human code = y} - mu_i),

with mu_i the LLM's code (or its probability of each category), has the mean of the human
codes in every arm, whatever errors the LLM makes. Pass it as `y` to `friction_iv`.
"""

import numpy as np

from ._data import outcome_matrix


def human_coding_probs(z, budget, lam, arms=None, floor=0.02):
    """Probabilities pi_i that put the human coding where the IV estimate puts its weight.

    The estimate from arms (a, b) is (1 + lam) G_b - lam G_a, so its variance falls fastest
    when pi is proportional to the arm weight: 1 + lam in arm b and lam in arm a. Other arms
    get `floor`. `budget` is the expected share of all answers coded by humans; `lam` is a
    pilot value of lambda = (S_b - FPR)/(S_a - S_b).
    """
    z = np.asarray(z)
    a, b = arms if arms is not None else (z.max() - 1, z.max())
    w = np.where(z == b, 1 + lam, np.where(z == a, lam, 0.0))
    pi = np.full(len(z), floor)
    free = budget * len(z) - floor * np.sum(w == 0)
    if free <= 0:
        raise ValueError("budget too small for the floor")
    pi[w > 0] = np.minimum(1, w[w > 0] * free / w.sum())
    return np.maximum(pi, floor)


def draw_human_coding(pi, seed=None):
    """xi_i = 1 with probability pi_i: which answers go to human coders."""
    return (np.random.default_rng(seed).uniform(size=len(pi)) < np.asarray(pi)).astype(int)


def pseudo_outcome(llm, human, xi, pi, categories=None):
    """Doubly robust pseudo-outcome Y~ (n x K). `llm` is the LLM's label per answer, or an
    n x K matrix of its category probabilities. `human` is the human label (ignored where
    xi = 0, so it may be missing there)."""
    xi = np.asarray(xi, dtype=float)
    pi = np.asarray(pi, dtype=float)
    if (pi <= 0).any():
        raise ValueError("every answer needs a positive chance of human coding")
    llm = np.asarray(llm)
    if llm.ndim == 2:
        mu = llm.astype(float)
        labels = list(categories) if categories is not None else list(range(mu.shape[1]))
    else:
        mu, labels = outcome_matrix(llm, categorical=True, categories=categories)
    human = np.asarray(human, dtype=object)
    H = np.column_stack([(human == c).astype(float) for c in labels])
    return mu + (xi / pi)[:, None] * (H - mu), labels

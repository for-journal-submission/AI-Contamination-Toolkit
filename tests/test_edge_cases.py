"""Two edge cases: equal means in arms 0 and 1, and a human-coding budget that hits the caps."""

import numpy as np
import pytest

import aicontam as ac


def test_mtr_equal_means_bound_nothing():
    # Arms 0 and 1 have the same mean answer (0), so Theorem 1(iii) gives no direction.
    # A population consistent with these moments: alpha_0 = 0.3, alpha_1 = 0.1, the 10% who use
    # AI in both arms have Y(0) = 1 and Y(1) = 0, everyone else has Y(0) = Y(1) = 0. AI never
    # raises an answer, yet the truth is 0.1, so (iii) must not cap the target at G_M = 0.
    n = 1000
    y = np.zeros(2 * n)
    z = np.repeat([0, 1], n)
    s = np.r_[np.arange(n) < 340, np.arange(n) < 180].astype(float)
    r = ac.bounds(y, s, z, fpr=0.1, tpr=0.9).rows
    lo, hi = r["(iii) MTR"]
    assert np.isneginf(lo[0]) and np.isposinf(hi[0])
    assert np.allclose(np.r_[r["intersection"]], [0.0, 0.1])


def test_coding_budget_spent_after_caps():
    # Probabilities are capped at 1 (first case) or raised to the floor (second case); the rest
    # of the budget is spread again, so the mean of pi still equals the budget.
    z = np.repeat([0, 1], 1000)
    for budget, lam in [(0.9, 1.0), (0.02, 0.01), (0.3, 1.0)]:
        pi = ac.human_coding_probs(z, budget=budget, lam=lam)
        assert pi.mean() == pytest.approx(budget, abs=1e-9)
        assert pi.min() >= 0.02 and pi.max() <= 1


def test_coding_budget_out_of_range():
    with pytest.raises(ValueError):
        ac.human_coding_probs(np.repeat([0, 1, 2], 100), budget=0.9, lam=1.0)

"""Standard errors, Anderson-Rubin sets and sample-size planning."""

import numpy as np
import pytest

import aicontam as ac

HOMOG = [0.5, 0.5, 0.5, 0.5]


def test_se_matches_table2_formula():
    d = ac.simulate_batball(4000, (0.3, 0.7), seed=1)
    fpr = ac.estimate_fpr(ac.pre_ai_signals(300, seed=2))
    r = ac.friction_iv(d.wrong, d.flagged, d.arm, fpr)
    Y, S, Z = d.wrong.to_numpy(float), d.flagged.to_numpy(float), d.arm.to_numpy() == 1
    G1, G0, S1, S0 = Y[Z].mean(), Y[~Z].mean(), S[Z].mean(), S[~Z].mean()
    lam, slope = (S1 - fpr.value) / (S0 - S1), (G0 - G1) / (S0 - S1)
    var = ((1 + lam) ** 2 * np.var(Y[Z] - S[Z] * slope) / Z.sum()
           + lam ** 2 * np.var(Y[~Z] - S[~Z] * slope) / (~Z).sum() + slope ** 2 * fpr.value * (1 - fpr.value) / 300)
    assert r.estimate[0] == pytest.approx(G1 + lam * (G1 - G0))
    assert r.se[0] == pytest.approx(np.sqrt(var))


def test_coverage_homogeneous():
    hits_wald = hits_ar = 0
    reps = 400
    for rep in range(reps):
        d = ac.simulate_batball(3000, (0.4, 0.3, 0.3), wrong=HOMOG, seed=rep)
        fpr = ac.estimate_fpr(ac.pre_ai_signals(300, seed=10_000 + rep))
        r = ac.friction_iv(d.wrong, d.flagged, d.arm, fpr)
        lo, hi = r.ci()[0]
        hits_wald += lo <= 0.5 <= hi
        hits_ar += any(a <= 0.5 <= b for a, b in r.ar_sets[0])
    assert 0.92 <= hits_wald / reps <= 0.98
    assert 0.92 <= hits_ar / reps <= 0.98


def test_ar_unbounded_without_first_stage():
    rng = np.random.default_rng(0)
    n = 2000
    z = ac.assign_arms(n, [0.5, 0.5], seed=0)
    s = (rng.uniform(size=n) < 0.2).astype(int)  # the friction does not move the signal
    y = (rng.uniform(size=n) < 0.5).astype(int)
    r = ac.friction_iv(y, s, z, 0.2)
    assert any(np.isinf(a) or np.isinf(b) for a, b in r.ar_sets[0])


def test_plan_matches_simulation():
    # two arms, AI shares 0.30 and 0.05, human share wrong 0.5, AI always right
    plan = ac.plan_sample_size(0.03, (0.30, 0.05), 0.5, 0.0, 0.1, 0.9, shares=(0.5, 0.5))
    n = int(np.ceil(plan.n))
    est = []
    for rep in range(300):
        rng = np.random.default_rng(rep)
        z = ac.assign_arms(n, [0.5, 0.5], seed=rng)
        w = rng.uniform(size=n) < np.where(z == 0, 0.30, 0.05)
        y = np.where(w, 0, rng.uniform(size=n) < 0.5)
        s = np.where(w, rng.uniform(size=n) < 0.9, rng.uniform(size=n) < 0.1)
        est.append(ac.friction_iv(y.astype(int), s.astype(int), z, 0.1).estimate[0])
    assert np.std(est) == pytest.approx(0.03, rel=0.12)


def test_assign_arms():
    z = ac.assign_arms(1001, [0.2, 0.8], seed=3)
    assert np.bincount(z).tolist() == [200, 801]

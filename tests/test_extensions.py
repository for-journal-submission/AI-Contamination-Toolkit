"""AI coding correction and latent class IPW."""

import numpy as np
import pytest

import aicontam as ac


def test_pseudo_outcome_unbiased_with_bad_llm():
    rng = np.random.default_rng(0)
    n = 200_000
    human = rng.choice(["pay", "management", "culture"], size=n, p=[0.5, 0.3, 0.2])
    # the LLM codes every 'culture' answer as 'pay', and 10% of the rest at random
    llm = np.where(human == "culture", "pay", human)
    noise = rng.uniform(size=n) < 0.1
    llm = np.where(noise, rng.choice(["pay", "management", "culture"], size=n), llm)
    pi = np.where(rng.uniform(size=n) < 0.5, 0.05, 0.2)
    xi = ac.draw_human_coding(pi, seed=1)
    Yt, labels = ac.pseudo_outcome(llm, np.where(xi == 1, human, None), xi, pi,
                                   categories=["pay", "management", "culture"])
    assert np.allclose(Yt.mean(0), [0.5, 0.3, 0.2], atol=0.01)


def test_coding_then_iv():
    d = ac.simulate_batball(60_000, (0.4, 0.3, 0.3), wrong=[0.5] * 4, seed=3)
    rng = np.random.default_rng(4)
    llm = np.where(rng.uniform(size=len(d)) < 0.3, 1 - d.wrong, d.wrong)  # LLM errs on 30%
    pi = ac.human_coding_probs(d.arm, budget=0.2, lam=1.0)
    xi = ac.draw_human_coding(pi, seed=5)
    Yt, labels = ac.pseudo_outcome(llm, np.where(xi == 1, d.wrong, -1), xi, pi, categories=[0, 1])
    r = ac.friction_iv(Yt, d.flagged, d.arm, 0.1, categories=labels)
    assert r.estimate[1] == pytest.approx(0.5, abs=3 * r.se[1])
    assert pi.mean() == pytest.approx(0.2, abs=0.01)


def test_latent_ipw_recovers_truth():
    rng = np.random.default_rng(7)
    n = 20_000
    c = (rng.uniform(size=n) < 0.4).astype(int)
    e = np.array([0.1, 0.5])[c]
    w = rng.uniform(size=n) < e
    p0 = np.array([0.2, 0.7])[c]  # human answer 'yes' by class
    target = np.where(w, rng.uniform(size=n) < 0.05, rng.uniform(size=n) < p0).astype(int)
    q = np.array([0.15, 0.85])[c]  # three closed-ended questions that AI does not answer
    other = [(rng.uniform(size=n) < q).astype(int) for _ in range(3)]
    s = np.where(w, rng.uniform(size=n) < 0.9, rng.uniform(size=n) < 0.1).astype(int)
    truth = np.mean(np.where(c == 1, 0.7, 0.2))
    r = ac.latent_ipw(np.column_stack([target] + other), s, fpr=0.1, tpr=0.9, ai_free=(1, 2, 3), n_classes=2, seed=1)
    assert r.ipw[1] == pytest.approx(truth, abs=0.03)
    assert ac.delete_flagged(target, s)["estimate"].iloc[0] < truth - 0.04

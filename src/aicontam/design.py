"""Design: assign the friction at random and choose the sample size."""

from dataclasses import dataclass

import numpy as np


def assign_arms(n, shares, seed=None):
    """Randomly assign n participants to arms 0..M with the given shares (complete randomization).

    Arm 0 is the most relaxed friction. Example: `assign_arms(3000, [0.2, 0.8])` relaxes the
    friction for 20% of participants and keeps it for the rest.
    """
    shares = np.asarray(shares, dtype=float)
    if (shares <= 0).any() or not np.isclose(shares.sum(), 1):
        raise ValueError("shares must be positive and sum to 1")
    counts = np.floor(shares * n).astype(int)
    counts[np.argsort(-(shares * n - counts))[: n - counts.sum()]] += 1
    z = np.repeat(np.arange(len(shares)), counts)
    return np.random.default_rng(seed).permutation(z)


@dataclass
class Plan:
    n: float
    se: float
    first_stage: float
    lam: float

    def __str__(self):
        return (f"N = {np.ceil(self.n):,.0f} participants for a standard error of {self.se:.4f} "
                f"(first stage {self.first_stage:.3f}, lambda {self.lam:.2f})")


def _arm_moments(alpha, mu, ai_mean, fpr, tpr):
    """Mean of Y, of S, and Var(Y - b S) pieces for a binary answer in an arm with AI share alpha."""
    EY = mu + alpha * (ai_mean - mu)
    ES = fpr + alpha * (tpr - fpr)
    EYS = (1 - alpha) * mu * fpr + alpha * ai_mean * tpr
    return EY, ES, EY * (1 - EY), ES * (1 - ES), EYS - EY * ES


def iv_se(n, alpha, mu, ai_mean, fpr, tpr, shares=(0.5, 0.5), m=np.inf):
    """Standard error of the two-arm IV estimate of a share, under homogeneity.

    alpha = (alpha_a, alpha_b): AI shares in the relaxed and the strong arm. mu: share among
    human answers (the target). ai_mean: share among AI answers. The detector flags human
    answers at fpr and AI answers at tpr. shares: sizes of the two arms. m: size of the
    pre-AI sample that estimates FPR.
    """
    (Ya, Sa, VYa, VSa, Ca), (Yb, Sb, VYb, VSb, Cb) = (_arm_moments(a, mu, ai_mean, fpr, tpr) for a in alpha)
    D = Sa - Sb
    lam = (Sb - fpr) / D
    b = (Ya - Yb) / D
    var = ((1 + lam) ** 2 * (VYb + b * b * VSb - 2 * b * Cb) / (n * shares[1])
           + lam ** 2 * (VYa + b * b * VSa - 2 * b * Ca) / (n * shares[0]) + b * b * fpr * (1 - fpr) / m)
    return float(np.sqrt(var))


def plan_sample_size(target_se, alpha, mu, ai_mean, fpr, tpr, shares=(0.5, 0.5), m=np.inf):
    """Smallest N whose IV standard error is at most target_se (see `iv_se` for the inputs)."""
    one = iv_se(1, alpha, mu, ai_mean, fpr, tpr, shares, np.inf) ** 2
    Sa, Sb = (fpr + a * (tpr - fpr) for a in alpha)
    b = (alpha[0] - alpha[1]) * (ai_mean - mu) / (Sa - Sb)
    room = target_se ** 2 - b * b * fpr * (1 - fpr) / m
    n = one / room if room > 0 else np.inf
    return Plan(n, target_se, Sa - Sb, (Sb - fpr) / (Sa - Sb))

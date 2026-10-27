"""Detector rates: FPR from answers written before AI, TPR from answers written by AI."""

from dataclasses import dataclass

import numpy as np


@dataclass(frozen=True)
class Rate:
    """A detector rate estimated from `n` answers (n = inf for a known rate)."""

    value: float
    n: float = np.inf

    @property
    def se(self):
        return float(np.sqrt(self.value * (1 - self.value) / self.n))

    def draw(self, rng):
        """One bootstrap draw of the estimated rate."""
        if np.isinf(self.n):
            return self.value
        return rng.binomial(int(self.n), self.value) / self.n


def as_rate(rate):
    if rate is None or isinstance(rate, Rate):
        return rate
    return Rate(float(rate))


def estimate_rate(signals):
    """Flagged share of a sample of answers whose author is known."""
    s = np.asarray(signals, dtype=float)
    if not np.isin(s, (0.0, 1.0)).all():
        raise ValueError("signals must be 0 or 1")
    return Rate(float(s.mean()), len(s))


def estimate_fpr(human_signals):
    """FPR from the signals on answers written before AI (or by verified humans)."""
    return estimate_rate(human_signals)


def estimate_tpr(ai_signals):
    """TPR from the signals on answers written by AI. Only the bounds need it."""
    return estimate_rate(ai_signals)


def threshold_for_fpr(human_scores, fpr):
    """Score threshold at which a continuous detector flags a share `fpr` of human answers."""
    return float(np.quantile(np.asarray(human_scores, dtype=float), 1 - fpr))


def flag(scores, threshold):
    """Signal S = 1 if the detector's score exceeds the threshold."""
    return (np.asarray(scores, dtype=float) > threshold).astype(int)

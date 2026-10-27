"""Input checks and per-arm moments shared by the estimators."""

from dataclasses import dataclass

import numpy as np


def outcome_matrix(y, categorical=None, categories=None):
    """Return the answers as an n x K float matrix and the K column labels.

    A 2-D array is used as is (each column is one function g). A 1-D numeric array is one
    column unless `categorical=True`. Text labels, or `categorical=True`, give one indicator
    column per category, so the estimates are the shares of the categories.
    """
    y = np.asarray(y)
    if y.ndim == 2:
        labels = list(categories) if categories is not None else list(range(y.shape[1]))
        return y.astype(float), labels
    if categorical is None:
        categorical = not np.issubdtype(y.dtype, np.number) and y.dtype != bool
    if not categorical:
        return y.astype(float)[:, None], ["mean"]
    labels = list(categories) if categories is not None else sorted(set(y.tolist()))
    return np.column_stack([(y == c).astype(float) for c in labels]), labels


def signal_vector(s, n):
    s = np.asarray(s, dtype=float)
    if s.shape != (n,):
        raise ValueError(f"signal must have length {n}")
    if not np.isin(s, (0.0, 1.0)).all():
        raise ValueError("signal must be 0 or 1")
    return s


def arm_vector(z, n):
    z = np.asarray(z)
    if z.shape != (n,):
        raise ValueError(f"arm must have length {n}")
    arms = np.unique(z)
    if not np.issubdtype(z.dtype, np.integer) or arms[0] != 0 or not np.array_equal(arms, np.arange(len(arms))):
        raise ValueError("arms must be coded 0, 1, ..., M, with 0 the most relaxed friction")
    if len(arms) < 2:
        raise ValueError("the design needs at least two arms")
    return z


@dataclass
class Arm:
    """Sample moments of one arm: answers Y (n x K) and signals S (n)."""

    Y: np.ndarray
    S: np.ndarray

    @property
    def n(self):
        return len(self.S)

    @property
    def G(self):
        return self.Y.mean(0)

    @property
    def Sbar(self):
        return self.S.mean()

    @property
    def H(self):
        return (self.Y * self.S[:, None]).mean(0)


def split_arms(Y, S, z):
    return [Arm(Y[z == a], S[z == a]) for a in range(z.max() + 1)]


def prepare(y, s, z, categorical=None, categories=None):
    Y, labels = outcome_matrix(y, categorical, categories)
    S = signal_vector(s, len(Y))
    z = arm_vector(z, len(Y))
    return Y, S, z, labels

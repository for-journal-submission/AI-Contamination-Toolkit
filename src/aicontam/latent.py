"""Weighting without an instrument: IPW under latent ignorability (Theorem latent, Appendix G).

A latent class model treats each participant's class C and AI use W as unobserved. Given the
state (C, W), the answers to the J questions are independent, and the signal follows the
detector's known rates (FPR if W = 0, TPR if W = 1). Questions AI cannot answer for the
participant (closed-ended items, demographics, `ai_free`) depend on C alone. They are what
identifies the class of an AI user, so the model needs at least two of them. Ignorability
holds within a class: the human answer does not depend on W given C. The model is fitted by EM. The weight

    E[omega_IPW | O_i] = sum_c Pr(W = 0, C = c | O_i) / (1 - e(c)),   e(c) = Pr(W = 1 | C = c),

identifies the distribution of human answers (Theorem latent (b)). This module is a
prototype: it handles discrete answers and no covariates (fit it within strata of X).
"""

from dataclasses import dataclass

import numpy as np
import pandas as pd

from .calibrate import as_rate


@dataclass
class LatentResult:
    labels: list
    ipw: np.ndarray          # weighted share of each category of the target question
    model: np.ndarray        # the same share implied by the fitted model
    weights: np.ndarray      # E[omega_IPW | O_i] for every participant
    posterior_ai: np.ndarray  # Pr(W_i = 1 | O_i)
    class_shares: np.ndarray
    ai_by_class: np.ndarray
    loglik: float

    def summary(self):
        return pd.DataFrame({"ipw": self.ipw, "model": self.model}, index=self.labels)


def _codes(col):
    labels, idx = np.unique(np.asarray(col).astype(str), return_inverse=True)
    return idx, list(labels)


def latent_ipw(answers, s, fpr, tpr, target=0, ai_free=(), n_classes=2, n_starts=10, max_iter=500,
               tol=1e-8, smooth=0.5, seed=0):
    """Fit the latent class model and return the IPW estimate for the `target` question.

    answers : n x J array (or DataFrame) of discrete answers; column `target` is the one
              whose human distribution we want.
    ai_free : indices of the columns AI does not write (closed-ended items, demographics).
    s : detector signal, 0 or 1. fpr, tpr : the detector's rates (floats or `Rate`).
    """
    A = answers.to_numpy() if isinstance(answers, pd.DataFrame) else np.asarray(answers)
    if A.ndim == 1:
        A = A[:, None]
    s = np.asarray(s, dtype=int)
    f, t = as_rate(fpr).value, as_rate(tpr).value
    cols = [_codes(A[:, j]) for j in range(A.shape[1])]
    X = [c[0] for c in cols]
    n, C = len(s), n_classes
    ps = np.stack([np.where(s == 1, f, 1 - f), np.where(s == 1, t, 1 - t)], axis=1)  # n x 2 (w)
    rng = np.random.default_rng(seed)
    best = None
    for _ in range(n_starts):
        pc = np.full(C, 1 / C)
        e = rng.uniform(0.1, 0.5, C)
        th = [rng.dirichlet(np.ones(len(c[1])), size=(C, 2)) for c in cols]  # C x 2 x L_j
        for j in ai_free:
            th[j][:, 1] = th[j][:, 0]
        old = -np.inf
        for _ in range(max_iter):
            # E step: joint posterior over (c, w)
            lik = pc[None, :, None] * np.stack([1 - e, e], axis=1)[None] * ps[:, None, :]
            for j, x in enumerate(X):
                lik = lik * th[j][:, :, x].transpose(2, 0, 1)
            tot = lik.sum((1, 2))
            ll = np.log(tot).sum()
            post = lik / tot[:, None, None]
            # M step
            pc = post.sum((0, 2)) / n
            e = post[:, :, 1].sum(0) / post.sum((0, 2))
            for j, x in enumerate(X):
                L = th[j].shape[2]
                cnt = np.stack([post[x == l].sum(0) for l in range(L)], axis=2) + smooth / L
                if j in ai_free:
                    cnt = np.repeat(cnt.sum(1, keepdims=True), 2, axis=1)
                th[j] = cnt / cnt.sum(2, keepdims=True)
            if ll - old < tol * abs(ll):
                break
            old = ll
        if best is None or ll > best[0]:
            best = (ll, pc, e, th, post)
    ll, pc, e, th, post = best
    w = (post[:, :, 0] / (1 - e)[None]).sum(1)
    onehot = np.eye(len(cols[target][1]))[X[target]]
    ipw = (w[:, None] * onehot).sum(0) / w.sum()
    model = (pc[:, None] * th[target][:, 0, :]).sum(0)
    return LatentResult(cols[target][1], ipw, model, w, post[:, :, 1].sum(1), pc, e, float(ll))

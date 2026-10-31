# AI Contamination Toolkit

Estimate how survey participants would answer without AI, when some of them use AI to answer.

The package implements *Dealing with AI Contamination in Behavioral Research*. AI use is an unobserved treatment. An AI detector gives a noisy signal of it. A randomized friction, such as disabling copy and paste for some participants and not others, serves as an instrument. For the IV estimate, the detector needs to be accurate enough to move with the friction, nothing more.

The Python package is `aicontam`.

```bash
pip install git+https://github.com/for-journal-submission/AI-Contamination-Toolkit                  # numpy, scipy, pandas
pip install "aicontam[plot] @ git+https://github.com/for-journal-submission/AI-Contamination-Toolkit"  # adds matplotlib
```

## Workflow

```python
import aicontam as ac

z = ac.assign_arms(6000, [1/3, 1/3, 1/3], seed=1)        # 0 = most relaxed friction
# ... run the survey: answer y, detector signal s (0/1), arm z for every participant
fpr = ac.estimate_fpr(pre_ai_signals)                    # signals on answers written before AI

ac.arm_table(y, s, z)                                    # the points of the contamination curve
ac.first_stage(s, z)                                     # does the friction move the signal?
iv = ac.friction_iv(y, s, z, fpr)                        # Theorem 2(i), with Wald and AR sets
print(iv)
ac.compare(y, s, z, fpr)                                 # no correction vs delete flagged vs IV
ac.bounds(y, s, z, fpr, tpr, n_boot=999)                 # Theorem 2(ii)-(iv)
ac.plot_curve(y, s, z, fpr)
```

`y` may be text labels (the estimate is the share of each category), a numeric vector (its mean), or an n x K matrix (the mean of each column, one function g per column).

`examples/batball_tutorial.py` runs every step on the bat-and-ball example of the paper. Its output is in `examples/batball_tutorial_output.txt`.

## Functions

| Step | Function | Paper |
|---|---|---|
| Design | `assign_arms` randomizes the friction. `plan_sample_size` and `iv_se` give the N for a target standard error. | Section 3 |
| Detector | `estimate_fpr` uses pre-AI answers and `estimate_tpr` uses AI answers. `threshold_for_fpr` and `flag` turn a detector's scores into signals. | Section 2 |
| Estimate | `friction_iv` gives the IV estimate from any two arms (default the two strongest), a delta-method standard error, and the Anderson–Rubin set, which stays valid when the first stage is weak. | Theorem 2(i), Theorem 3 |
| Compare | `no_correction`, `delete_flagged` and `compare`. `deletion_bias` gives the two terms of Theorem 1 in simulated data. | Theorem 1, Table 2 |
| Diagnose | `arm_table`, `first_stage`, `homogeneity_test` (is a middle arm on the line?) and `plot_curve`. | Section 3, Figure 1 |
| Bounds | `bounds` covers bounded outcomes (Manski, needs TPR and a detector that errs at the same rates for every participant and answer), monotone treatment response and monotone treatment selection, plus their intersection and bootstrap confidence bounds. | Theorem 2(ii)–(iv) |
| AI coding | `human_coding_probs` chooses which answers humans code. `draw_human_coding` draws them. `pseudo_outcome` builds the corrected outcome to pass to `friction_iv`. | Lemma coding |
| No instrument | `latent_ipw` fits a latent class model and returns IPW weights. It needs at least two questions that AI does not write for the participant (`ai_free`). | Theorem latent |
| Data | `simulate_batball` gives a simulated survey. `batball_population` gives the exact population of Figure 1. `pre_ai_signals` gives a pre-AI sample. | Figure 1 |

## Tests

```bash
pip install -e ".[test]" && pytest
```

The tests reproduce the paper's numbers:
- arms (0.34, 0.35), (0.18, 0.43) and (0.14, 0.46)
- θ01 = 0.47 and θ12 = 0.49
- bounds [0.43, 0.53] and [0.46, 0.51], and their intersection [0.49, 0.51]

They also check the following:
- The standard error equals the formula of the Table 2 code.
- Wald and Anderson–Rubin coverage is about 95%.
- The Anderson–Rubin set is unbounded when the friction does not move the signal.
- The planned N gives the planned standard error.
- The coding correction is unbiased with a bad LLM.
- The latent class IPW recovers the truth.

## Scope

This is a prototype. Inference for the bounds uses a bootstrap, not the Anderson–Rubin union of Theorem 3, and `latent_ipw` handles discrete answers without covariates (fit it within strata of X).

## The paper's computational appendix

`paper/` holds what the paper itself needs (see `paper/README.md`).
- `paper/lean/`: Lean 4 proofs of the theorems and of the numbers in Figure 1.
- `paper/replication/`: the code that rebuilds the Glassdoor test bed and reproduces Table 2.

License: MIT.

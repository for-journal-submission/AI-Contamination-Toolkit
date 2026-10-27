# Computational Appendix

This folder accompanies *Dealing with AI Contamination in Behavioral Research*. It has two parts.

- `lean/`: a Lean 4 project that checks with Mathlib every result of the paper whose proof is exact algebra or finite probability, and every number in Table 1 and Figure 1.
- `replication/`: the Python code that rebuilds the Glassdoor test bed and reproduces Table 2.

## Lean

**Versions.** Lean `v4.35.0-rc4` and Mathlib commit `fad34067088f101a9a302d9393aacbffa190694c`, pinned in `lean/lean-toolchain` and `lean/lake-manifest.json`.

**Status.** The project has 77 theorems and no `sorry`. `lean/AxiomAudit.lean` prints the axioms of every theorem. Each one uses only `propext`, `Classical.choice` and `Quot.sound` (see `lean/axiom_audit.txt`).

```bash
cd lean
lake exe cache get              # prebuilt Mathlib for the pinned commit
lake build                      # checks every proof
lake env lean AxiomAudit.lean   # prints the axioms
```

**Model.** The population is a finite set of participant types with weights `p`, so every expectation is a finite sum and every statement is exact. A function `g(Y, X)` enters as real-valued maps, so the results hold for every `g`. A conditional mean is `E[f 1_A] / P(A)` (`Basic.lean`). For Theorem 2, `Curve` lists the participants' resistances `V` with masses `p`, thresholds `r`, and the effects `τ(v)` (on the answer) and `κ(v)` (on the signal). An arm with threshold `a` lets AI write the answers of the participants with `r(v) ≤ a`.

### Map from the paper to Lean

| Paper | Lean (namespace `AIC`) | File |
|---|---|---|
| Theorem 1, bias of deleting flagged answers (two terms) | `thm1_deletion_bias` | `Thm1Deletion.lean` |
| Theorem 1, second term with a perfect detector (Appendix B) | `perfect_detector` | `Thm1Deletion.lean` |
| Arm means under random assignment, and eq. (curve) | `armMean_eq`, `eq_curve` | `Thm2Curve.lean` |
| Eq. (line), the line through an arm | `Curve.eq_line` | `Thm2Curve.lean` |
| Theorem 2(i), homogeneity gives `θ_{zz'} = μ` | `Curve.thm2_i`, `Curve.theta_weights`, `Curve.S_strict` | `Thm2Curve.lean` |
| Lemma setid, eq. (setmom) | `setmom`, `setid`, `setid_adjacent` | `Thm2Curve.lean` |
| Theorem 2(ii), bound under the detector condition (Lean assumes only the four moments `DetectorRates` that the condition implies) | `thm2_ii` | `Thm2Curve.lean` |
| Theorem 2(iii), MTR | `Curve.thm2_iii` | `Thm2Curve.lean` |
| Theorem 2(iv), MTS | `Curve.thm2_iv` | `Thm2Curve.lean` |
| Theorem 3 (inference): identifying equation `ψ(θ₀)` (`M` in Lean) is zero at the truth, and its form for the bounds | `M_zero_at_truth`, `bound_equation`, `M_linear`, `M_root_iff` | `Thm3Inference.lean` |
| Theorem 3: gradient for the delta method | `M_gradient`, `thetaHat_gradient` | `Thm3Inference.lean` |
| Theorem 3: Anderson–Rubin set is a quadratic set, bounded or not | `AR_quadratic`, `quad_set_bounded`, `quad_set_unbounded` | `Thm3Inference.lean` |
| Lemma balance (Appendix G) | `balance_identity`, `balance_cells`, `balance_unbiased_iff`, `balance_unbiased_iff_wmass` | `Balance.lean` |
| Theorem latent (a), IPW | `Latent.latent_a`, `Latent.latent_a_unbiased` | `ThmLatent.lean` |
| Theorem latent (b), expectation given observed data | `Latent.latent_b`, `Latent.latent_b_formula` | `ThmLatent.lean` |
| Lemma coding (Appendix H) | `coding_a`, `coding_a_arm` | `LemCoding.lean` |
| Table 1: reported shares, misclassified answers, weights, biases | `Examples.table1_*` | `Examples.lean` |
| Figure 1 example (Appendix D): arms, `θ_{01} = 0.47`, `θ_{12} = 0.49`, slopes, bounds, MTS | `Examples.fig_arms`, `fig_theta`, `fig_slopes`, `fig_manski`, `fig_below`, `fig_mts` | `Examples.lean` |

Not formalized:

- Theorem 3's asymptotic coverage, its uniformity, and the split of the 5% error when the admissible range of the bounds is estimated (Appendix E). These are standard results (Anderson and Rubin 1949, Staiger and Stock 1997, Imbens and Manski 2004), cited in the paper.
- In Appendix D, the nesting of the Theorem 2(ii) intervals across arms and the sharpness of the interval of arm `M`.
- The remark in Appendix D that Theorem 2(iii) and (iv) need their conditions only for `v ≤ α_0`. Lean assumes them for every `v`. Its Figure 1 example therefore sets the never-takers' `τ`, which no arm reveals, to 0.

## Replication of Table 2

See `replication/README.md`. Two scripts rebuild the test bed and print the rows of Table 2. The run takes about one minute.

import AIContamination.Balance

/-!
# Theorem 1 (`thm:weights`): the bias of deleting flagged answers

`W : Ω → Bool` is AI use and `S : Ω → Bool` the detector's signal `S^obs`. `G0 G1 : Ω → ℝ` are
`g(Y(0),X)` and `g(Y(1),X)` for an arbitrary `g`. Deleting flagged answers estimates
`E[g(Y^obs,X) | S^obs = 0]` (the law of large numbers, not formalized).
-/

open Finset

namespace AIC

set_option linter.unusedSectionVars false

variable {Ω : Type*} [Fintype Ω]

/-- **Theorem 1.** With `q = Pr(W = 1 | S^obs = 0)`,
`E[g(Y^obs,X) | S^obs = 0] − E[g(Y(0),X)]
  = q {E[g(Y(1),X) | W = 1, S^obs = 0] − E[g(Y(0),X) | W = 0, S^obs = 0]}
    + E[g(Y(0),X) | W = 0, S^obs = 0] − E[g(Y(0),X)]`. -/
theorem thm1_deletion_bias {p : Ω → ℝ} (hp : ∀ i, 0 ≤ p i) (W S : Ω → Bool) (G0 G1 : Ω → ℝ)
    (hS : 0 < P p (fun i => S i = false)) :
    condMean p (fun i => S i = false) (obsVal W G0 G1) - E p G0 =
      P p (fun i => W i = true ∧ S i = false) / P p (fun i => S i = false)
          * (condMean p (fun i => W i = true ∧ S i = false) G1
            - condMean p (fun i => W i = false ∧ S i = false) G0)
        + (condMean p (fun i => W i = false ∧ S i = false) G0 - E p G0) := by
  have hsplitP : P p (fun i => S i = false)
      = P p (fun i => W i = true ∧ S i = false) + P p (fun i => W i = false ∧ S i = false) := by
    unfold P; rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rcases Bool.eq_false_or_eq_true (W i) with h | h <;>
      rcases Bool.eq_false_or_eq_true (S i) with h' | h' <;> simp [h, h']
  have hsplitE : EOn p (fun i => S i = false) (obsVal W G0 G1)
      = EOn p (fun i => W i = true ∧ S i = false) G1
        + EOn p (fun i => W i = false ∧ S i = false) G0 := by
    unfold EOn obsVal; rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rcases Bool.eq_false_or_eq_true (W i) with h | h <;>
      rcases Bool.eq_false_or_eq_true (S i) with h' | h' <;> simp [h, h']
  have e1 := P_mul_condMean hp (fun i => W i = true ∧ S i = false) G1
  have e0 := P_mul_condMean hp (fun i => W i = false ∧ S i = false) G0
  have hne : P p (fun i => S i = false) ≠ 0 := hS.ne'
  have hk : condMean p (fun i => S i = false) (obsVal W G0 G1)
      = EOn p (fun i => S i = false) (obsVal W G0 G1) / P p (fun i => S i = false) := rfl
  have hab : P p (fun i => W i = true ∧ S i = false) + P p (fun i => W i = false ∧ S i = false)
      ≠ 0 := by rw [← hsplitP]; exact hne
  rw [hk, hsplitE, ← e1, ← e0, hsplitP]
  field_simp
  ring

/-- **A perfect detector** (`S^obs = W`). The first term of Theorem 1 vanishes, and the bias is
`α {E[g(Y(0),X) | W = 0] − E[g(Y(0),X) | W = 1]}` with `α = Pr(W = 1)`. -/
theorem perfect_detector {p : Ω → ℝ} (hp : ∀ i, 0 ≤ p i) (hsum : ∑ i, p i = 1)
    (W : Ω → Bool) (G0 G1 : Ω → ℝ) :
    P p (fun i => W i = true ∧ W i = false) = 0 ∧
    condMean p (fun i => W i = false) (obsVal W G0 G1) - E p G0 =
      P p (fun i => W i = true) *
        (condMean p (fun i => W i = false) G0 - condMean p (fun i => W i = true) G0) := by
  refine ⟨by unfold P; simp, ?_⟩
  have hobs : condMean p (fun i => W i = false) (obsVal W G0 G1)
      = condMean p (fun i => W i = false) G0 := by
    unfold condMean EOn obsVal
    congr 1
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rcases Bool.eq_false_or_eq_true (W i) with h | h <;> simp [h]
  have hE : E p G0 = EOn p (fun i => W i = true) G0 + EOn p (fun i => W i = false) G0 := by
    unfold E EOn
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rcases Bool.eq_false_or_eq_true (W i) with h | h <;> simp [h]
  have hβ : P p (fun i => W i = false) = 1 - P p (fun i => W i = true) := by
    have := P_true_add_false p hsum W; linarith
  rw [hobs, hE, ← P_mul_condMean hp (fun i => W i = true) G0,
    ← P_mul_condMean hp (fun i => W i = false) G0, hβ]
  ring

end AIC

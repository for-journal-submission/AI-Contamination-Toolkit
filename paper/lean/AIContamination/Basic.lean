import Mathlib.Algebra.BigOperators.Field
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Basic.Real.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.Prod

/-!
# Finite populations

A population is a finite type `Ω` of participant types with probability weights `p`.
Every expectation is a finite sum, so every statement below is exact.
-/

open Finset

namespace AIC

variable {Ω : Type*} [Fintype Ω]

/-- Expectation `E[f] = ∑ p_i f_i`. -/
def E (p : Ω → ℝ) (f : Ω → ℝ) : ℝ := ∑ i, p i * f i

/-- Probability of an event `A`. -/
def P (p : Ω → ℝ) (A : Ω → Prop) [DecidablePred A] : ℝ := ∑ i, if A i then p i else 0

/-- Unnormalized mean of `f` on the event `A`: `E[f · 1_A]`. -/
def EOn (p : Ω → ℝ) (A : Ω → Prop) [DecidablePred A] (f : Ω → ℝ) : ℝ :=
  ∑ i, if A i then p i * f i else 0

/-- Conditional mean `E[f | A] = E[f 1_A] / P(A)` (zero if `P(A) = 0`). -/
noncomputable def condMean (p : Ω → ℝ) (A : Ω → Prop) [DecidablePred A] (f : Ω → ℝ) : ℝ :=
  EOn p A f / P p A

/-- If the weights are nonnegative, an event of probability zero carries no mass. -/
lemma EOn_eq_zero_of_P_eq_zero {p : Ω → ℝ} (hp : ∀ i, 0 ≤ p i) {A : Ω → Prop}
    [DecidablePred A] (f : Ω → ℝ) (h : P p A = 0) : EOn p A f = 0 := by
  unfold P at h
  have hz : ∀ i ∈ (univ : Finset Ω), (if A i then p i else 0) = 0 := by
    have := (Finset.sum_eq_zero_iff_of_nonneg (s := univ)
      (f := fun i => if A i then p i else 0) (fun i _ => by split_ifs <;> simp [hp i])).1 h
    exact this
  unfold EOn
  refine Finset.sum_eq_zero (fun i hi => ?_)
  have := hz i hi
  split_ifs at this ⊢ with hA
  · simp [this]
  · rfl

/-- `P(A) · E[f | A] = E[f 1_A]` for nonnegative weights. -/
lemma P_mul_condMean {p : Ω → ℝ} (hp : ∀ i, 0 ≤ p i) (A : Ω → Prop) [DecidablePred A]
    (f : Ω → ℝ) : P p A * condMean p A f = EOn p A f := by
  unfold condMean
  by_cases h : P p A = 0
  · rw [h, EOn_eq_zero_of_P_eq_zero hp f h]; simp
  · field_simp

/-- Fiber decomposition: a sum over participants grouped by the cell `o i`. -/
lemma sum_fiber {κ : Type*} [Fintype κ] [DecidableEq κ] (o : Ω → κ) (a : Ω → ℝ)
    (g : κ → ℝ) :
    ∑ i, a i * g (o i) = ∑ k, (∑ i, if o i = k then a i else 0) * g k := by
  simp only [Finset.sum_mul, ite_mul, zero_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [Finset.sum_ite_eq]
  simp

end AIC

import AIContamination.Basic

/-!
# Lemma `lem:coding` (coding by AI)

`Ω` lists the values of `(O, Y^obs)`. `A i = 1{Y^obs = y}`, `μ i = μ(O)` is any prediction and
`π i = π(O) > 0` the hand-coding probability. The joint distribution of `(O, Y^obs, ξ)` has
`Pr(ξ = 1 | O, Y^obs) = π(O)`.
-/

open Finset

namespace AIC

set_option linter.unusedSectionVars false

variable {Ω : Type*} [Fintype Ω]

/-- Joint weight of `((O, Y^obs), ξ)`. -/
def qXi (p π : Ω → ℝ) (x : Ω × Bool) : ℝ := p x.1 * (if x.2 then π x.1 else 1 - π x.1)

/-- The pseudo-outcome `Ỹ = μ + (ξ/π)(1{Y^obs = y} − μ)`. -/
noncomputable def Ytil (A μ π : Ω → ℝ) (x : Ω × Bool) : ℝ :=
  μ x.1 + (if x.2 then 1 else 0) / π x.1 * (A x.1 - μ x.1)

/-- **Lemma (a), conditional mean.** `E[Ỹ | O, Y^obs] = 1{Y^obs = y}`, whatever `μ`. -/
theorem coding_a_pointwise (A μ π : Ω → ℝ) (i : Ω) (hπ : π i ≠ 0) :
    π i * Ytil A μ π (i, true) + (1 - π i) * Ytil A μ π (i, false) = A i := by
  unfold Ytil; simp only [ite_true, Bool.false_eq_true, ite_false]; field_simp; ring

/-- **Lemma (a).** For every function `h` of `(O, Y^obs)`, `E[h Ỹ] = E[h 1{Y^obs = y}]`;
with `h = 1{Z = z}` this gives `E[Ỹ | Z = z] = Pr(Y^obs = y | Z = z)` (next theorem). -/
theorem coding_a (p A μ π h : Ω → ℝ) (hπ : ∀ i, π i ≠ 0) :
    E (qXi p π) (fun x => h x.1 * Ytil A μ π x) = E p (fun i => h i * A i) := by
  unfold E qXi
  rw [Fintype.sum_prod_type]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  simp only [Fintype.sum_bool, ite_true, Bool.false_eq_true, ite_false]
  rw [← coding_a_pointwise A μ π i (hπ i)]
  ring

/-- The arm `Z` is recorded in `O`, so it has the same distribution under `qXi`. -/
theorem coding_a_arm (p A μ π : Ω → ℝ) (hπ : ∀ i, π i ≠ 0) (Z : Ω → Bool) (z : Bool) :
    condMean (qXi p π) (fun x => Z x.1 = z) (Ytil A μ π) = condMean p (fun i => Z i = z) A := by
  unfold condMean
  have h1 : EOn (qXi p π) (fun x => Z x.1 = z) (Ytil A μ π) = EOn p (fun i => Z i = z) A := by
    have := coding_a p A μ π (fun i => if Z i = z then 1 else 0) hπ
    unfold E at this; unfold EOn
    rw [← Finset.sum_congr rfl (fun x _ => by split_ifs <;> ring :
      ∀ x ∈ (univ : Finset (Ω × Bool)), qXi p π x * ((if Z x.1 = z then 1 else 0) * Ytil A μ π x)
        = if Z x.1 = z then qXi p π x * Ytil A μ π x else 0)]
    rw [this]
    refine Finset.sum_congr rfl (fun i _ => by by_cases h : Z i = z <;> simp [h])
  have h2 : P (qXi p π) (fun x => Z x.1 = z) = P p (fun i => Z i = z) := by
    unfold P qXi
    rw [Fintype.sum_prod_type]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    simp only [Fintype.sum_bool, ite_true, Bool.false_eq_true, ite_false]
    split_ifs <;> ring
  rw [h1, h2]

end AIC

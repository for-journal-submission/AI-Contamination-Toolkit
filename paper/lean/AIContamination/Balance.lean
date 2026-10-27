import AIContamination.Basic

/-!
# Lemma `lem:balance` (Appendix G): when weighting estimators are unbiased

Cells `κ` stand for the finitely many values of `(Y, X)`. The map `obs : Ω → κ` is
`(Y_i^obs, X_i)` and `tru : Ω → κ` is `(Y_i(0), X_i)`. A function `g : κ → ℝ` is any
`g(y, x)`.
-/

open Finset

namespace AIC

set_option linter.unusedSectionVars false

variable {Ω : Type*} [Fintype Ω] {κ : Type*} [Fintype κ] [DecidableEq κ]

/-- `Pr(c_i = k)`. -/
def mass (p : Ω → ℝ) (c : Ω → κ) (k : κ) : ℝ := ∑ i, if c i = k then p i else 0

/-- `E[ω 1{c_i = k}]`. -/
def wmass (p ω : Ω → ℝ) (c : Ω → κ) (k : κ) : ℝ := ∑ i, if c i = k then p i * ω i else 0

/-- `ω̄(k) = E[ω | (Y^obs, X) = k]`. -/
noncomputable def omegaBar (p ω : Ω → ℝ) (obs : Ω → κ) (k : κ) : ℝ :=
  wmass p ω obs k / mass p obs k

/-- `ω*(k) = Pr{(Y(0), X) = k} / Pr((Y^obs, X) = k)`. -/
noncomputable def omegaStar (p : Ω → ℝ) (tru obs : Ω → κ) (k : κ) : ℝ :=
  mass p tru k / mass p obs k

/-- Bias of the weighting estimator for `g`. -/
def bias (p ω : Ω → ℝ) (tru obs : Ω → κ) (g : κ → ℝ) : ℝ :=
  E p (fun i => ω i * g (obs i)) - E p (fun i => g (tru i))

lemma wmass_eq_zero_of_mass {p : Ω → ℝ} (hp : ∀ i, 0 ≤ p i) (ω : Ω → ℝ) (c : Ω → κ)
    (k : κ) (h : mass p c k = 0) : wmass p ω c k = 0 := by
  have := EOn_eq_zero_of_P_eq_zero (A := fun i => c i = k) hp ω (by simpa [P, mass] using h)
  simpa [EOn, wmass] using this

lemma mass_nonneg {p : Ω → ℝ} (hp : ∀ i, 0 ≤ p i) (c : Ω → κ) (k : κ) : 0 ≤ mass p c k :=
  Finset.sum_nonneg (fun i _ => by split_ifs <;> simp [hp i])

lemma E_comp (p f : Ω → ℝ) (c : Ω → κ) (g : κ → ℝ) :
    E p (fun i => f i * g (c i)) = ∑ k, wmass p f c k * g k := by
  unfold E wmass
  have := sum_fiber c (fun i => p i * f i) g
  simpa [mul_assoc] using this

lemma E_comp_one (p : Ω → ℝ) (c : Ω → κ) (g : κ → ℝ) :
    E p (fun i => g (c i)) = ∑ k, mass p c k * g k := by
  have := E_comp p (fun _ => 1) c g
  simpa [wmass, mass] using this

/-- `mass_obs(k) · ω̄(k) = E[ω 1{obs = k}]`. -/
lemma mass_mul_omegaBar {p : Ω → ℝ} (hp : ∀ i, 0 ≤ p i) (ω : Ω → ℝ) (obs : Ω → κ) (k : κ) :
    mass p obs k * omegaBar p ω obs k = wmass p ω obs k := by
  unfold omegaBar
  by_cases h : mass p obs k = 0
  · rw [h, wmass_eq_zero_of_mass hp ω obs k h]; simp
  · field_simp

/-- Under positivity, `mass_obs(k) · ω*(k) = Pr{(Y(0),X) = k}`. -/
lemma mass_mul_omegaStar (p : Ω → ℝ) (tru obs : Ω → κ)
    (hpos : ∀ k, mass p obs k = 0 → mass p tru k = 0) (k : κ) :
    mass p obs k * omegaStar p tru obs k = mass p tru k := by
  unfold omegaStar
  by_cases h : mass p obs k = 0
  · rw [h, hpos k h]; simp
  · field_simp

/-- **Lemma `lem:balance`, bias identity.** For every `g`,
`E[ω g(Y^obs,X)] − E[g(Y(0),X)] = E[{ω̄ − ω*}(Y^obs,X) g(Y^obs,X)]`. -/
theorem balance_identity {p : Ω → ℝ} (hp : ∀ i, 0 ≤ p i) (ω : Ω → ℝ) (tru obs : Ω → κ)
    (hpos : ∀ k, mass p obs k = 0 → mass p tru k = 0) (g : κ → ℝ) :
    bias p ω tru obs g =
      E p (fun i => (omegaBar p ω obs (obs i) - omegaStar p tru obs (obs i)) * g (obs i)) := by
  unfold bias
  rw [E_comp, E_comp_one]
  have h3 : E p (fun i => (omegaBar p ω obs (obs i) - omegaStar p tru obs (obs i)) * g (obs i))
      = ∑ k, mass p obs k * ((omegaBar p ω obs k - omegaStar p tru obs k) * g k) := by
    have := E_comp_one p obs (fun k => (omegaBar p ω obs k - omegaStar p tru obs k) * g k)
    simpa using this
  rw [h3, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl (fun k _ => ?_)
  have h1 := mass_mul_omegaBar hp ω obs k
  have h2 := mass_mul_omegaStar p tru obs hpos k
  rw [← h1, ← h2]; ring

/-- The bias as a sum over cells: `∑_k Pr(obs = k) {ω̄(k) − ω*(k)} g(k)`. -/
theorem balance_cells {p : Ω → ℝ} (hp : ∀ i, 0 ≤ p i) (ω : Ω → ℝ) (tru obs : Ω → κ)
    (hpos : ∀ k, mass p obs k = 0 → mass p tru k = 0) (g : κ → ℝ) :
    bias p ω tru obs g =
      ∑ k, mass p obs k * (omegaBar p ω obs k - omegaStar p tru obs k) * g k := by
  rw [balance_identity hp ω tru obs hpos g]
  have := E_comp_one p obs (fun k => (omegaBar p ω obs k - omegaStar p tru obs k) * g k)
  rw [this]
  refine Finset.sum_congr rfl (fun k _ => by ring)

/-- **Lemma `lem:balance`, characterization.** The correction is unbiased for every `g` if and only if
`ω̄ = ω*` on the support of `(Y^obs, X)`. -/
theorem balance_unbiased_iff {p : Ω → ℝ} (hp : ∀ i, 0 ≤ p i) (ω : Ω → ℝ) (tru obs : Ω → κ)
    (hpos : ∀ k, mass p obs k = 0 → mass p tru k = 0) :
    (∀ g : κ → ℝ, bias p ω tru obs g = 0) ↔
      (∀ k, 0 < mass p obs k → omegaBar p ω obs k = omegaStar p tru obs k) := by
  constructor
  · intro h k hk
    have := h (fun k' => if k' = k then 1 else 0)
    rw [balance_cells hp ω tru obs hpos] at this
    simp only [mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, ite_true]
      at this
    rcases mul_eq_zero.1 this with h0 | h0
    · exact absurd h0 hk.ne'
    · linarith
  · intro h g
    rw [balance_cells hp ω tru obs hpos]
    refine Finset.sum_eq_zero (fun k _ => ?_)
    rcases (mass_nonneg hp obs k).lt_or_eq with hk | hk
    · rw [h k hk]; ring
    · rw [← hk]; ring

/-- Equivalent form: unbiased for every `g` iff the `ω`-weighted distribution of `(Y^obs, X)`
equals the distribution of `(Y(0), X)`, cell by cell. -/
theorem balance_unbiased_iff_wmass (p : Ω → ℝ) (ω : Ω → ℝ)
    (tru obs : Ω → κ) :
    (∀ g : κ → ℝ, bias p ω tru obs g = 0) ↔ (∀ k, wmass p ω obs k = mass p tru k) := by
  constructor
  · intro h k
    have := h (fun k' => if k' = k then 1 else 0)
    unfold bias at this
    rw [E_comp p ω obs (fun k' => if k' = k then (1:ℝ) else 0),
      E_comp_one p tru (fun k' => if k' = k then (1:ℝ) else 0)] at this
    simp only [mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, ite_true]
      at this
    linarith
  · intro h g
    unfold bias
    rw [E_comp, E_comp_one]
    simp [h]

/-! ## Observed answers -/

/-- `g(Y^obs, X)` under SUTVA: `W : Ω → Bool` is AI use, `G0 G1` are `g(Y(0),X)`, `g(Y(1),X)`. -/
def obsVal (W : Ω → Bool) (G0 G1 : Ω → ℝ) (i : Ω) : ℝ := if W i then G1 i else G0 i

/-- Probabilities of `W = 1` and `W = 0` add up to one. -/
lemma P_true_add_false (p : Ω → ℝ) (hsum : ∑ i, p i = 1) (W : Ω → Bool) :
    P p (fun i => W i = true) + P p (fun i => W i = false) = 1 := by
  unfold P
  rw [← Finset.sum_add_distrib, ← hsum]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rcases Bool.eq_false_or_eq_true (W i) with h | h <;> simp [h]

end AIC

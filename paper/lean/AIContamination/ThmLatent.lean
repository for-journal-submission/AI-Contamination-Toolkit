import AIContamination.Balance

/-!
# Theorem `thm:latent` (Appendix G): weighting without an instrument

`C` is the latent class, `X` the covariates, `W` AI use, `Y0` the own answer and `Yobs` the
observed answer. Ignorability `W ⫫ Y(0) | (X, C)` is stated in its multiplicative form
`Pr(W=0, Y(0)=y, x, c) Pr(x, c) = Pr(W=0, x, c) Pr(Y(0)=y, x, c)`, which is the definition of
conditional independence for finite distributions (and needs no division).
-/

open Finset

namespace AIC

set_option linter.unusedSectionVars false

variable {Ω : Type*} [Fintype Ω]

lemma P_le_of_imp {p : Ω → ℝ} (hp : ∀ i, 0 ≤ p i) {A B : Ω → Prop} [DecidablePred A]
    [DecidablePred B] (h : ∀ i, A i → B i) : P p A ≤ P p B := by
  unfold P
  refine Finset.sum_le_sum (fun i _ => ?_)
  by_cases hA : A i
  · simp [hA, h i hA]
  · by_cases hB : B i <;> simp [hA, hB, hp i]

lemma P_nonneg {p : Ω → ℝ} (hp : ∀ i, 0 ≤ p i) (A : Ω → Prop) [DecidablePred A] :
    0 ≤ P p A :=
  Finset.sum_nonneg (fun i _ => by split_ifs <;> simp [hp i])

/-- A population for Theorem `thm:latent`. -/
structure Latent (Ω 𝒴 𝒳 𝒞 : Type*) [Fintype Ω] where
  p : Ω → ℝ
  hp : ∀ i, 0 ≤ p i
  W : Ω → Bool
  X : Ω → 𝒳
  C : Ω → 𝒞
  Y0 : Ω → 𝒴
  Yobs : Ω → 𝒴
  /-- SUTVA: a participant who does not use AI reports the own answer. -/
  sutva : ∀ i, W i = false → Yobs i = Y0 i

namespace Latent

variable {𝒴 𝒳 𝒞 : Type*} [Fintype 𝒴] [DecidableEq 𝒴] [Fintype 𝒳] [DecidableEq 𝒳]
  [Fintype 𝒞] [DecidableEq 𝒞] (L : Latent Ω 𝒴 𝒳 𝒞)

/-- `Pr(X = x, C = c)`. -/
def pXC (x : 𝒳) (c : 𝒞) : ℝ := P L.p (fun i => L.X i = x ∧ L.C i = c)
/-- `Pr(W = 1, X = x, C = c)`. -/
def p1XC (x : 𝒳) (c : 𝒞) : ℝ := P L.p (fun i => L.W i = true ∧ L.X i = x ∧ L.C i = c)
/-- `Pr(W = 0, X = x, C = c)`. -/
def p0XC (x : 𝒳) (c : 𝒞) : ℝ := P L.p (fun i => L.W i = false ∧ L.X i = x ∧ L.C i = c)
/-- `Pr(W = 0, Y(0) = y, X = x, C = c)`. -/
def p0YXC (y : 𝒴) (x : 𝒳) (c : 𝒞) : ℝ :=
  P L.p (fun i => L.W i = false ∧ L.Y0 i = y ∧ L.X i = x ∧ L.C i = c)
/-- `Pr(Y(0) = y, X = x, C = c)`. -/
def pYXC (y : 𝒴) (x : 𝒳) (c : 𝒞) : ℝ := P L.p (fun i => L.Y0 i = y ∧ L.X i = x ∧ L.C i = c)

/-- Propensity `e(x, c) = Pr(W = 1 | X = x, C = c)`. -/
noncomputable def e (x : 𝒳) (c : 𝒞) : ℝ := L.p1XC x c / L.pXC x c

/-- Ignorability given the class: `W ⫫ Y(0) | (X, C)`. -/
def Ignorable : Prop := ∀ y x c, L.p0YXC y x c * L.pXC x c = L.p0XC x c * L.pYXC y x c

/-- Overlap: `e(x, c) < 1` wherever `(x, c)` has positive probability. -/
def Overlap : Prop := ∀ x c, 0 < L.pXC x c → L.e x c < 1

/-- The inverse probability weight `ω^IPW = (1 − W)/{1 − e(X, C)}`. -/
noncomputable def omegaIPW (i : Ω) : ℝ := if L.W i then 0 else 1 / (1 - L.e (L.X i) (L.C i))

/-- Observed cell `(Y^obs, X)` and true cell `(Y(0), X)`. -/
def obs (i : Ω) : 𝒴 × 𝒳 := (L.Yobs i, L.X i)
def tru (i : Ω) : 𝒴 × 𝒳 := (L.Y0 i, L.X i)

lemma p1_add_p0 (x : 𝒳) (c : 𝒞) : L.p1XC x c + L.p0XC x c = L.pXC x c := by
  unfold p1XC p0XC pXC P
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rcases Bool.eq_false_or_eq_true (L.W i) with h | h <;> simp [h]

/-- One class at a time: `Pr(W=0, Y(0)=y, x, c)/(1 − e(x,c)) = Pr(Y(0)=y, x, c)`. -/
lemma cell_step (hI : L.Ignorable) (hO : L.Overlap) (y : 𝒴) (x : 𝒳) (c : 𝒞) :
    L.p0YXC y x c * (1 / (1 - L.e x c)) = L.pYXC y x c := by
  rcases (P_nonneg L.hp (fun i => L.X i = x ∧ L.C i = c)).lt_or_eq with hpos | hzero
  · have hpos' : 0 < L.pXC x c := hpos
    have he := hO x c hpos'
    have hne : L.pXC x c ≠ 0 := hpos'.ne'
    have h1e : 1 - L.e x c = L.p0XC x c / L.pXC x c := by
      unfold e; rw [eq_div_iff hne, sub_mul, div_mul_cancel₀ _ hne, one_mul]
      linarith [L.p1_add_p0 x c]
    have hp0 : 0 < L.p0XC x c := by
      have : 0 < 1 - L.e x c := by linarith
      rw [h1e] at this
      exact (div_pos_iff_of_pos_right hpos').1 this
    rw [h1e]
    have := hI y x c
    field_simp
    linarith
  · have hz : L.pXC x c = 0 := hzero.symm
    have h1 : L.p0YXC y x c = 0 := by
      apply le_antisymm _ (P_nonneg L.hp _)
      rw [← hz]; exact P_le_of_imp L.hp (fun i h => ⟨h.2.2.1, h.2.2.2⟩)
    have h2 : L.pYXC y x c = 0 := by
      apply le_antisymm _ (P_nonneg L.hp _)
      rw [← hz]; exact P_le_of_imp L.hp (fun i h => ⟨h.2.1, h.2.2⟩)
    rw [h1, h2]; simp

/-- **Theorem `thm:latent` (a).** Under SUTVA, ignorability given the class, and overlap, the
`ω^IPW`-weighted distribution of `(Y^obs, X)` is the distribution of `(Y(0), X)`. -/
theorem latent_a_wmass (hI : L.Ignorable) (hO : L.Overlap) (k : 𝒴 × 𝒳) :
    wmass L.p L.omegaIPW L.obs k = mass L.p L.tru k := by
  obtain ⟨y, x⟩ := k
  -- Step 1: only non-users contribute, and for them `Y^obs = Y(0)`.
  have s1 : wmass L.p L.omegaIPW L.obs (y, x)
      = ∑ i, (if L.W i = false ∧ L.Y0 i = y ∧ L.X i = x then L.p i else 0)
          * (fun c => 1 / (1 - L.e x c)) (L.C i) := by
    unfold wmass
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rcases Bool.eq_false_or_eq_true (L.W i) with h | h
    · simp [omegaIPW, h]
    · have hs := L.sutva i h
      by_cases hy : L.Y0 i = y <;> by_cases hx : L.X i = x <;>
        simp [obs, omegaIPW, h, hs, hy, hx]
  -- Step 2: group by the latent class.
  rw [s1, sum_fiber L.C (fun i => if L.W i = false ∧ L.Y0 i = y ∧ L.X i = x then L.p i else 0)
    (fun c => 1 / (1 - L.e x c))]
  have s2 : ∀ c, (∑ i, if L.C i = c then
      (if L.W i = false ∧ L.Y0 i = y ∧ L.X i = x then L.p i else 0) else 0) = L.p0YXC y x c := by
    intro c; unfold p0YXC P
    refine Finset.sum_congr rfl (fun i _ => ?_)
    by_cases hc : L.C i = c <;> simp [hc]
  simp only [s2, L.cell_step hI hO]
  -- Step 3: sum the classes back.
  unfold pYXC mass tru P
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  beta_reduce
  by_cases hy : L.Y0 i = y <;> by_cases hx : L.X i = x <;> simp [hy, hx]

/-- **Theorem `thm:latent` (a): `ω̄^IPW = ω*`** (on every cell; off the support both are 0). -/
theorem latent_a (hI : L.Ignorable) (hO : L.Overlap) (k : 𝒴 × 𝒳) :
    omegaBar L.p L.omegaIPW L.obs k = omegaStar L.p L.tru L.obs k := by
  unfold omegaBar omegaStar; rw [L.latent_a_wmass hI hO k]

/-- ... and so the IPW estimator is unbiased for every `g` (Lemma `lem:balance`). -/
theorem latent_a_unbiased (hI : L.Ignorable) (hO : L.Overlap) (g : 𝒴 × 𝒳 → ℝ) :
    bias L.p L.omegaIPW L.tru L.obs g = 0 :=
  (balance_unbiased_iff_wmass L.p L.omegaIPW L.tru L.obs).2 (L.latent_a_wmass hI hO) g

/-! ### Part (b): the posterior mean of the weight given the observed data `O` -/

variable {𝒪 : Type*} [Fintype 𝒪] [DecidableEq 𝒪]

/-- `E[ω | O = o]`. -/
noncomputable def postO (ω : Ω → ℝ) (O : Ω → 𝒪) (o : 𝒪) : ℝ := wmass L.p ω O o / mass L.p O o

/-- **Theorem `thm:latent` (b), first part.** If `O` includes `(Y^obs, X)`, replacing `ω` by
`E[ω | O]` leaves `E[ω 1{(Y^obs, X) = k}]`, hence `ω̄`, unchanged. -/
theorem latent_b_same_wmass (ω : Ω → ℝ) (O : Ω → 𝒪) (fY : 𝒪 → 𝒴) (fX : 𝒪 → 𝒳)
    (hY : ∀ i, L.Yobs i = fY (O i)) (hX : ∀ i, L.X i = fX (O i)) (k : 𝒴 × 𝒳) :
    wmass L.p (fun i => L.postO ω O (O i)) L.obs k = wmass L.p ω L.obs k := by
  have hobs : ∀ i, L.obs i = (fY (O i), fX (O i)) := fun i => by simp [obs, hY i, hX i]
  let h : 𝒪 → ℝ := fun o => if (fY o, fX o) = k then 1 else 0
  have lhs : wmass L.p (fun i => L.postO ω O (O i)) L.obs k
      = ∑ i, L.p i * (fun o => L.postO ω O o * h o) (O i) := by
    unfold wmass; refine Finset.sum_congr rfl (fun i _ => ?_)
    simp only [h, hobs i]; split_ifs <;> ring
  have rhs : wmass L.p ω L.obs k = ∑ i, (L.p i * ω i) * h (O i) := by
    unfold wmass; refine Finset.sum_congr rfl (fun i _ => ?_)
    simp only [h, hobs i]; split_ifs <;> ring
  rw [lhs, rhs, sum_fiber O L.p (fun o => L.postO ω O o * h o),
    sum_fiber O (fun i => L.p i * ω i) h]
  refine Finset.sum_congr rfl (fun o _ => ?_)
  have hm := mass_mul_omegaBar L.hp ω O o
  unfold omegaBar at hm
  unfold postO
  have e1 : (∑ i, if O i = o then L.p i else 0) = mass L.p O o := rfl
  have e2 : (∑ i, if O i = o then L.p i * ω i else 0) = wmass L.p ω O o := rfl
  rw [e1, e2, show mass L.p O o * (wmass L.p ω O o / mass L.p O o * h o)
    = (mass L.p O o * (wmass L.p ω O o / mass L.p O o)) * h o by ring, hm]

/-- Hence the posterior-mean weight also satisfies `ω̄ = ω*`. -/
theorem latent_b (hI : L.Ignorable) (hO : L.Overlap) (O : Ω → 𝒪) (fY : 𝒪 → 𝒴)
    (fX : 𝒪 → 𝒳) (hY : ∀ i, L.Yobs i = fY (O i)) (hX : ∀ i, L.X i = fX (O i))
    (k : 𝒴 × 𝒳) :
    omegaBar L.p (fun i => L.postO L.omegaIPW O (O i)) L.obs k = omegaStar L.p L.tru L.obs k := by
  unfold omegaBar omegaStar
  rw [L.latent_b_same_wmass L.omegaIPW O fY fX hY hX k, L.latent_a_wmass hI hO k]

/-- **Theorem `thm:latent` (b), formula.**
`E[ω^IPW | O = o] = ∑_c Pr(W = 0, C = c | O = o)/{1 − e(x(o), c)}`. -/
theorem latent_b_formula (O : Ω → 𝒪) (fX : 𝒪 → 𝒳) (hX : ∀ i, L.X i = fX (O i)) (o : 𝒪) :
    L.postO L.omegaIPW O o = ∑ c, (P L.p (fun i => L.W i = false ∧ L.C i = c ∧ O i = o)
      / mass L.p O o) / (1 - L.e (fX o) c) := by
  have hw : wmass L.p L.omegaIPW O o = ∑ i, (if L.W i = false ∧ O i = o then L.p i else 0)
      * (fun c => 1 / (1 - L.e (fX o) c)) (L.C i) := by
    unfold wmass; refine Finset.sum_congr rfl (fun i _ => ?_)
    by_cases ho : O i = o
    · rcases Bool.eq_false_or_eq_true (L.W i) with h | h
      · simp [omegaIPW, h, ho]
      · simp [omegaIPW, h, ho, hX i]
    · simp [ho]
  unfold postO
  rw [hw, sum_fiber L.C (fun i => if L.W i = false ∧ O i = o then L.p i else 0)
    (fun c => 1 / (1 - L.e (fX o) c)), Finset.sum_div]
  refine Finset.sum_congr rfl (fun c _ => ?_)
  have hs : (∑ i, if L.C i = c then (if L.W i = false ∧ O i = o then L.p i else 0) else 0)
      = P L.p (fun i => L.W i = false ∧ L.C i = c ∧ O i = o) := by
    unfold P; refine Finset.sum_congr rfl (fun i _ => ?_)
    by_cases hc : L.C i = c <;> by_cases ho : O i = o <;> simp [hc, ho]
  rw [hs]; ring

end Latent

end AIC

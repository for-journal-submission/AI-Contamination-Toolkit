import AIContamination.Balance

/-!
# Theorem 2 (`thm:friction`): the contamination curve

**Model.** `Ω` is a finite set of resistance values `v` with weights `p v = Pr(V = v)`; `r v` is
the resistance itself (only its order matters, as in the paper). `τ v` and `κ v` are the
marginal treatment effects of AI on `g` and on the signal, `μ = E[g(Y(0),X)]` is the target,
and `fpr = FPR`. An arm is its threshold `a`: those with `r v ≤ a` use AI (Assumption A4(iii),
`W(z) = 1{V ≤ α_z}`). `eq_curve` derives this model from participant-level potential
outcomes.

Arms are compared through their thresholds, so `a' < a` means arm `a` is the more relaxed one.
-/

open Finset

namespace AIC

set_option linter.unusedSectionVars false

/-! ## From potential outcomes to Equation (`eq:curve`) -/

section Derivation

variable {Ι : Type*} [Fintype Ι] {Ω : Type*} [Fintype Ω] [DecidableEq Ω]

/-- **Assumption A4 (i)–(ii) and SUTVA at work.** With the arm `Z` drawn independently with
`Pr(Z = z) = ρ z`, the mean of `f(i, Z_i)` among participants with `Z = z` is the population mean
of `f(i, z)`. With `f(i, z) = g(Y_i(W_i(z)), X_i)` this says that each arm reveals the
distribution of `(Y(W(z)), S(W(z)))`. -/
theorem armMean_eq {𝒵 : Type*} [Fintype 𝒵] [DecidableEq 𝒵] (p : Ι → ℝ) (hsum : ∑ i, p i = 1)
    (ρ : 𝒵 → ℝ) (z : 𝒵) (hρ : ρ z ≠ 0) (f : Ι → 𝒵 → ℝ) :
    condMean (fun x : Ι × 𝒵 => p x.1 * ρ x.2) (fun x => x.2 = z) (fun x => f x.1 x.2)
      = E p (fun i => f i z) := by
  have hP : P (fun x : Ι × 𝒵 => p x.1 * ρ x.2) (fun x => x.2 = z) = ρ z := by
    unfold P; rw [Fintype.sum_prod_type]
    have : ∀ i, (∑ z', if z' = z then p i * ρ z' else 0) = p i * ρ z := fun i => by
      rw [Finset.sum_ite_eq']; simp
    simp only [this]; rw [← Finset.sum_mul, hsum, one_mul]
  have hE : EOn (fun x : Ι × 𝒵 => p x.1 * ρ x.2) (fun x => x.2 = z) (fun x => f x.1 x.2)
      = ρ z * E p (fun i => f i z) := by
    unfold EOn E; rw [Fintype.sum_prod_type, Finset.mul_sum]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    have : (∑ z', if z' = z then p i * ρ z' * f i z' else 0) = p i * ρ z * f i z := by
      rw [Finset.sum_ite_eq']; simp
    rw [this]; ring
  unfold condMean; rw [hP, hE]; field_simp

/-- **Equation (`eq:curve`).** Participants `i` with weights `q`, resistance `V i`, and
`g(Y(0),X)`, `g(Y(1),X)` given by `G0 G1`. In the arm with threshold `a`, AI is used iff
`r (V i) ≤ a`. Then the arm mean of `g(Y^obs,X)` is
`E[g(Y(0),X)] + ∑_v Pr(V = v) E[τ | V = v] 1{r v ≤ a}`. By `armMean_eq`, this population mean
is the mean of `g(Y^obs,X)` among participants assigned to the arm. -/
theorem eq_curve (q : Ι → ℝ) (hq : ∀ i, 0 ≤ q i) (V : Ι → Ω) (r : Ω → ℝ) (a : ℝ)
    (G0 G1 : Ι → ℝ) :
    E q (fun i => if r (V i) ≤ a then G1 i else G0 i)
      = E q G0 + ∑ v, if r v ≤ a then
          P q (fun i => V i = v) * condMean q (fun i => V i = v) (fun i => G1 i - G0 i) else 0 := by
  have h1 : E q (fun i => if r (V i) ≤ a then G1 i else G0 i) - E q G0
      = ∑ i, q i * (if r (V i) ≤ a then G1 i - G0 i else 0) := by
    unfold E; rw [← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    by_cases h : r (V i) ≤ a <;> simp [h]; ring
  have h2 : (∑ v, if r v ≤ a then
        P q (fun i => V i = v) * condMean q (fun i => V i = v) (fun i => G1 i - G0 i) else 0)
      = ∑ v, ∑ i, if V i = v then q i * (if r (V i) ≤ a then G1 i - G0 i else 0) else 0 := by
    refine Finset.sum_congr rfl (fun v _ => ?_)
    rw [P_mul_condMean hq]
    unfold EOn
    split_ifs with hv
    · refine Finset.sum_congr rfl (fun i _ => ?_)
      by_cases hi : V i = v
      · simp [hi, hv]
      · simp [hi]
    · symm; refine Finset.sum_eq_zero (fun i _ => ?_)
      by_cases hi : V i = v
      · simp [hi, hv]
      · simp [hi]
  have h3 : (∑ v, ∑ i, if V i = v then q i * (if r (V i) ≤ a then G1 i - G0 i else 0) else 0)
      = ∑ i, q i * (if r (V i) ≤ a then G1 i - G0 i else 0) := by
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [Finset.sum_ite_eq]; simp
  linarith

end Derivation

/-! ## The curve -/

/-- The marginal-treatment-effect model of Section 3 on finitely many resistance values. -/
structure Curve (Ω : Type*) [Fintype Ω] where
  p : Ω → ℝ
  hp : ∀ v, 0 ≤ p v
  r : Ω → ℝ
  τ : Ω → ℝ
  κ : Ω → ℝ
  μ : ℝ
  fpr : ℝ

namespace Curve

variable {Ω : Type*} [Fintype Ω] (C : Curve Ω)

/-- `I a f = ∑_{r v ≤ a} p v f v`, the integral `∫_0^{α} f(v) dv` of the paper. -/
noncomputable def I (a : ℝ) (f : Ω → ℝ) : ℝ := ∑ v, if C.r v ≤ a then C.p v * f v else 0

/-- Sum over the resistance values between two arms, `a' < r v ≤ a`. -/
noncomputable def Ibetween (a' a : ℝ) (f : Ω → ℝ) : ℝ :=
  ∑ v, if a' < C.r v ∧ C.r v ≤ a then C.p v * f v else 0

/-- Share of AI users in the arm with threshold `a`, `α = Pr(V ≤ a)`. -/
noncomputable def α (a : ℝ) : ℝ := C.I a (fun _ => 1)

/-- Flagged share of the arm (Equation `eq:curve`): `S̄ = FPR + ∫_0^α κ`. -/
noncomputable def S (a : ℝ) : ℝ := C.fpr + C.I a C.κ

/-- Mean of `g` in the arm (Equation `eq:curve`): `Ḡ = E[g(Y(0),X)] + ∫_0^α τ`. -/
noncomputable def G (a : ℝ) : ℝ := C.μ + C.I a C.τ

/-- `θ_{zz'}`: height at FPR of the straight line through arms `a` and `a'`. -/
noncomputable def θ (a a' : ℝ) : ℝ :=
  C.G a' - (C.G a - C.G a') * (C.S a' - C.fpr) / (C.S a - C.S a')

/-- The slope `β(v) = τ(v)/κ(v)` of the tangent. -/
noncomputable def β (v : Ω) : ℝ := C.τ v / C.κ v

/-- Differencing between arms: `I a f − I a' f = ∑_{a' < r v ≤ a} p v f v` for `a' ≤ a`. -/
lemma I_sub (a' a : ℝ) (h : a' ≤ a) (f : Ω → ℝ) :
    C.I a f - C.I a' f = C.Ibetween a' a f := by
  unfold I Ibetween; rw [← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl (fun v _ => ?_)
  by_cases h1 : C.r v ≤ a' <;> by_cases h2 : C.r v ≤ a
  · have : ¬ (a' < C.r v ∧ C.r v ≤ a) := fun hh => absurd hh.1 (not_lt.2 h1)
    simp [h1, h2, this]
  · exact absurd (le_trans h1 h) h2
  · have : a' < C.r v ∧ C.r v ≤ a := ⟨lt_of_not_ge h1, h2⟩
    simp [h1, h2, this]
  · have : ¬ (a' < C.r v ∧ C.r v ≤ a) := fun hh => h2 hh.2
    simp [h1, h2, this]

/-- **Equation (`eq:line`).** `E[g(Y(0),X)] = Ḡ_M − β_M (S̄_M − FPR)`, with `β_M` the slope of
the secant from arm `M` to the target. -/
theorem eq_line (c : ℝ) (h : C.I c C.κ ≠ 0) :
    C.μ = C.G c - C.I c C.τ / C.I c C.κ * (C.S c - C.fpr) := by
  unfold G S; field_simp; ring

/-! ### Theorem 2 (i): homogeneity -/

/-- With a constant slope, every arm lies on one line through the target. -/
lemma G_line (β₀ : ℝ) (hβ : ∀ v, C.τ v = β₀ * C.κ v) (a : ℝ) :
    C.G a = C.μ + β₀ * (C.S a - C.fpr) := by
  have hI : C.I a C.τ = β₀ * C.I a C.κ := by
    unfold I; rw [Finset.mul_sum]
    refine Finset.sum_congr rfl (fun v _ => ?_)
    split_ifs
    · rw [hβ v]; ring
    · ring
  unfold G S; rw [hI]; ring

/-- **Theorem 2 (i).** If `β(v)` is constant, `E[g(Y(0),X)] = θ_{zz'}` for any two arms with
distinct flagged shares. -/
theorem thm2_i (β₀ : ℝ) (hβ : ∀ v, C.τ v = β₀ * C.κ v) (a a' : ℝ) (hne : C.S a ≠ C.S a') :
    C.μ = C.θ a a' := by
  have hd : C.S a - C.S a' ≠ 0 := sub_ne_zero.mpr hne
  unfold θ
  rw [C.G_line β₀ hβ a, C.G_line β₀ hβ a']
  field_simp
  ring

/-- `κ > 0` and a friction that stops someone give distinct flagged shares
(Assumption A4(iv)). -/
theorem S_strict (hκ : ∀ v, 0 < C.κ v) (a' a : ℝ) (h : a' ≤ a)
    (hm : ∃ v, a' < C.r v ∧ C.r v ≤ a ∧ 0 < C.p v) : C.S a' < C.S a := by
  have hpos : 0 < C.Ibetween a' a C.κ := by
    obtain ⟨v, hv1, hv2, hv3⟩ := hm
    unfold Ibetween
    refine Finset.sum_pos' (fun w _ => ?_) ⟨v, Finset.mem_univ v, ?_⟩
    · split_ifs
      · exact mul_nonneg (C.hp w) (hκ w).le
      · exact le_refl 0
    · rw [if_pos ⟨hv1, hv2⟩]; exact mul_pos hv3 (hκ v)
  have := C.I_sub a' a h C.κ
  unfold S; linarith

/-- The two-arm weights of the proof of Theorem 2 (i): with
`λ = (S̄_1 − FPR)/(S̄_0 − S̄_1)`, `θ_{01} = (1 + λ) Ḡ_1 − λ Ḡ_0`. -/
theorem theta_weights (a0 a1 : ℝ) :
    C.θ a0 a1 = (1 + (C.S a1 - C.fpr) / (C.S a0 - C.S a1)) * C.G a1
      - (C.S a1 - C.fpr) / (C.S a0 - C.S a1) * C.G a0 := by
  unfold θ; ring

/-! ### Theorem 2 (iii): monotone treatment response -/

/-- **Theorem 2 (iii).** If `τ` does not change sign, `τ(v) τ(v') ≥ 0`, then for arms
`a1 < a0` (arm 0 relaxed) `Ḡ_0 < Ḡ_1` implies `E[g(Y(0),X)] ≥ Ḡ_M` for every arm `M`, and
`Ḡ_0 > Ḡ_1` implies `E[g(Y(0),X)] ≤ Ḡ_M`. -/
theorem thm2_iii (hsign : ∀ v w, 0 ≤ C.τ v * C.τ w) (a1 a0 : ℝ) (h : a1 ≤ a0) (aM : ℝ) :
    (C.G a0 < C.G a1 → C.G aM ≤ C.μ) ∧ (C.G a1 < C.G a0 → C.μ ≤ C.G aM) := by
  have hdiff : C.G a0 - C.G a1 = C.Ibetween a1 a0 C.τ := by
    have := C.I_sub a1 a0 h C.τ; unfold G; linarith
  constructor
  · intro hlt
    -- some `τ v < 0`, so every `τ w ≤ 0`
    have hneg : ∃ v, C.τ v < 0 := by
      by_contra hcon
      push_neg at hcon
      have : 0 ≤ C.Ibetween a1 a0 C.τ := by
        unfold Ibetween
        exact Finset.sum_nonneg (fun v _ => by
          split_ifs
          · exact mul_nonneg (C.hp v) (hcon v)
          · exact le_refl 0)
      linarith
    obtain ⟨v, hv⟩ := hneg
    have hall : ∀ w, C.τ w ≤ 0 := fun w => by nlinarith [hsign v w]
    have : C.I aM C.τ ≤ 0 := by
      unfold I
      exact Finset.sum_nonpos (fun w _ => by
        split_ifs
        · exact mul_nonpos_of_nonneg_of_nonpos (C.hp w) (hall w)
        · exact le_refl 0)
    unfold G; linarith
  · intro hlt
    have hpos : ∃ v, 0 < C.τ v := by
      by_contra hcon
      push_neg at hcon
      have : C.Ibetween a1 a0 C.τ ≤ 0 := by
        unfold Ibetween
        exact Finset.sum_nonpos (fun v _ => by
          split_ifs
          · exact mul_nonpos_of_nonneg_of_nonpos (C.hp v) (hcon v)
          · exact le_refl 0)
      linarith
    obtain ⟨v, hv⟩ := hpos
    have hall : ∀ w, 0 ≤ C.τ w := fun w => by nlinarith [hsign v w]
    have : 0 ≤ C.I aM C.τ := by
      unfold I
      exact Finset.sum_nonneg (fun w _ => by
        split_ifs
        · exact mul_nonneg (C.hp w) (hall w)
        · exact le_refl 0)
    unfold G; linarith

/-! ### Theorem 2 (iv): monotone treatment selection -/

/-- Weighted averages: if every value carried by `w1` is at most every value carried by `w2`,
the `w1`-average of `b` is at most its `w2`-average. -/
lemma wavg_le {ι : Type*} [Fintype ι] (w1 w2 b : ι → ℝ) (h1 : ∀ v, 0 ≤ w1 v)
    (h2 : ∀ v, 0 ≤ w2 v) (hb : ∀ v u, 0 < w1 v → 0 < w2 u → b v ≤ b u)
    (hK1 : 0 < ∑ v, w1 v) (hK2 : 0 < ∑ v, w2 v) :
    (∑ v, w1 v * b v) / (∑ v, w1 v) ≤ (∑ v, w2 v * b v) / (∑ v, w2 v) := by
  rw [div_le_div_iff₀ hK1 hK2]
  have hdouble : (∑ v, w2 v * b v) * (∑ v, w1 v) - (∑ v, w1 v * b v) * (∑ v, w2 v)
      = ∑ v, ∑ u, w1 v * w2 u * (b u - b v) := by
    rw [Finset.sum_mul_sum, Finset.sum_mul_sum, Finset.sum_comm (f := fun x y => w2 x * b x * w1 y)]
    rw [← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl (fun v _ => ?_)
    rw [← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl (fun u _ => ?_)
    ring
  have hnn : 0 ≤ ∑ v, ∑ u, w1 v * w2 u * (b u - b v) := by
    refine Finset.sum_nonneg (fun v _ => Finset.sum_nonneg (fun u _ => ?_))
    rcases (h1 v).lt_or_eq with hv | hv
    · rcases (h2 u).lt_or_eq with hu | hu
      · have := hb v u hv hu
        exact mul_nonneg (mul_nonneg hv.le hu.le) (by linarith)
      · rw [← hu]; ring_nf; exact le_refl 0
    · rw [← hv]; ring_nf; exact le_refl 0
  linarith

/-- `κ`-weights on a set of resistance values. -/
def wt (A : Ω → Prop) [DecidablePred A] (v : Ω) : ℝ := if A v then C.p v * C.κ v else 0

lemma wt_nonneg (hκ : ∀ v, 0 < C.κ v) (A : Ω → Prop) [DecidablePred A] (v : Ω) :
    0 ≤ C.wt A v := by
  unfold wt; split_ifs
  · exact mul_nonneg (C.hp v) (hκ v).le
  · exact le_refl 0

/-- With `κ > 0`, the `κ`-weighted sum of `β` is the sum of `τ`. -/
lemma wt_beta (hκ : ∀ v, 0 < C.κ v) (A : Ω → Prop) [DecidablePred A] :
    ∑ v, C.wt A v * C.β v = ∑ v, if A v then C.p v * C.τ v else 0 := by
  refine Finset.sum_congr rfl (fun v _ => ?_)
  unfold wt β; split_ifs
  · have := (hκ v).ne'; field_simp
  · ring

/-- The secant slope over a set of resistance values is the `κ`-weighted average of `β(v)`. -/
lemma slope_le_slope (hκ : ∀ v, 0 < C.κ v) (A B : Ω → Prop) [DecidablePred A] [DecidablePred B]
    (hAB : ∀ v u, A v → B u → C.β v ≤ C.β u)
    (hA : 0 < ∑ v, C.wt A v) (hB : 0 < ∑ v, C.wt B v) :
    (∑ v, if A v then C.p v * C.τ v else 0) / (∑ v, C.wt A v)
      ≤ (∑ v, if B v then C.p v * C.τ v else 0) / (∑ v, C.wt B v) := by
  rw [← C.wt_beta hκ A, ← C.wt_beta hκ B]
  refine wavg_le _ _ _ (C.wt_nonneg hκ A) (C.wt_nonneg hκ B) (fun v u hv hu => ?_) hA hB
  have hAv : A v := by
    by_contra hn; unfold wt at hv; rw [if_neg hn] at hv; exact lt_irrefl 0 hv
  have hBu : B u := by
    by_contra hn; unfold wt at hu; rw [if_neg hn] at hu; exact lt_irrefl 0 hu
  exact hAB v u hAv hBu

/-- **Theorem 2 (iv).** Arms `M`, `M − 1`, `M − 2` have thresholds `c < b < a`, each friction
stops someone, and someone uses AI in arm `M`. If `β(v)` is monotone in `v`, then
`E[g(Y(0),X)] ≥ θ_{M−1,M}` if arm `M − 1` lies below the line through arms `M − 2` and `M`,
and `E[g(Y(0),X)] ≤ θ_{M−1,M}` if it lies above. -/
theorem thm2_iv (hκ : ∀ v, 0 < C.κ v)
    (hmono : (∀ v u, C.r v ≤ C.r u → C.β v ≤ C.β u) ∨ (∀ v u, C.r v ≤ C.r u → C.β u ≤ C.β v))
    (c b a : ℝ) (hcb : c < b) (hba : b < a)
    (m0 : 0 < ∑ v, C.wt (fun v => C.r v ≤ c) v)
    (m1 : 0 < ∑ v, C.wt (fun v => c < C.r v ∧ C.r v ≤ b) v)
    (m2 : 0 < ∑ v, C.wt (fun v => b < C.r v ∧ C.r v ≤ a) v) :
    (C.G b < C.G c + (C.G a - C.G c) * (C.S b - C.S c) / (C.S a - C.S c) → C.θ b c ≤ C.μ) ∧
    (C.G c + (C.G a - C.G c) * (C.S b - C.S c) / (C.S a - C.S c) < C.G b → C.μ ≤ C.θ b c) := by
  -- the three pieces of the curve
  set K0 := ∑ v, C.wt (fun v => C.r v ≤ c) v
  set K1 := ∑ v, C.wt (fun v => c < C.r v ∧ C.r v ≤ b) v
  set K2 := ∑ v, C.wt (fun v => b < C.r v ∧ C.r v ≤ a) v
  set T0 := ∑ v, if C.r v ≤ c then C.p v * C.τ v else 0
  set T1 := ∑ v, if c < C.r v ∧ C.r v ≤ b then C.p v * C.τ v else 0
  set T2 := ∑ v, if b < C.r v ∧ C.r v ≤ a then C.p v * C.τ v else 0
  have eK0 : C.S c - C.fpr = K0 := by unfold S I; simp only [K0, wt]; ring
  have eT0 : C.G c - C.μ = T0 := by unfold G I; simp only [T0]; ring
  have eK1 : C.S b - C.S c = K1 := by
    have := C.I_sub c b hcb.le C.κ; unfold S; simp only [K1, wt]; unfold Ibetween at this; linarith
  have eT1 : C.G b - C.G c = T1 := by
    have := C.I_sub c b hcb.le C.τ; unfold G; simp only [T1]; unfold Ibetween at this; linarith
  have eK2 : C.S a - C.S b = K2 := by
    have := C.I_sub b a hba.le C.κ; unfold S; simp only [K2, wt]; unfold Ibetween at this; linarith
  have eT2 : C.G a - C.G b = T2 := by
    have := C.I_sub b a hba.le C.τ; unfold G; simp only [T2]; unfold Ibetween at this; linarith
  -- arm M − 1 below (above) the line through arms M − 2 and M iff T1/K1 < T2/K2 (>)
  have hθ : C.θ b c = C.G c - T1 / K1 * K0 := by
    unfold θ; rw [eK0, eK1, eT1]; ring
  have hμ : C.μ = C.G c - T0 / K0 * K0 := by
    rw [div_mul_cancel₀ _ m0.ne']; linarith
  have hline : C.G c + (C.G a - C.G c) * (C.S b - C.S c) / (C.S a - C.S c)
      = C.G c + (T1 + T2) * K1 / (K1 + K2) := by
    rw [show C.G a - C.G c = T1 + T2 by linarith, eK1, show C.S a - C.S c = K1 + K2 by linarith]
  have hGb : C.G b = C.G c + T1 := by linarith
  have below_iff : C.G b < C.G c + (C.G a - C.G c) * (C.S b - C.S c) / (C.S a - C.S c)
      ↔ T1 / K1 < T2 / K2 := by
    rw [hline, hGb, add_lt_add_iff_left, lt_div_iff₀ (by linarith), div_lt_div_iff₀ m1 m2]
    constructor <;> intro h <;> nlinarith
  have above_iff : C.G c + (C.G a - C.G c) * (C.S b - C.S c) / (C.S a - C.S c) < C.G b
      ↔ T2 / K2 < T1 / K1 := by
    rw [hline, hGb, add_lt_add_iff_left, div_lt_iff₀ (by linarith), div_lt_div_iff₀ m2 m1]
    constructor <;> intro h <;> nlinarith
  have hK0 : 0 ≤ K0 := m0.le
  -- slopes of the pieces are ordered as the pieces when β is monotone
  have up01 : (∀ v u, C.r v ≤ C.r u → C.β v ≤ C.β u) → T0 / K0 ≤ T1 / K1 := fun hm =>
    C.slope_le_slope hκ _ _ (fun v u hv hu => hm v u (le_of_lt (lt_of_le_of_lt hv hu.1))) m0 m1
  have up12 : (∀ v u, C.r v ≤ C.r u → C.β v ≤ C.β u) → T1 / K1 ≤ T2 / K2 := fun hm =>
    C.slope_le_slope hκ _ _ (fun v u hv hu => hm v u (le_of_lt (lt_of_le_of_lt hv.2 hu.1))) m1 m2
  have dn01 : (∀ v u, C.r v ≤ C.r u → C.β u ≤ C.β v) → T1 / K1 ≤ T0 / K0 := fun hm =>
    C.slope_le_slope hκ _ _ (fun v u hv hu => hm u v (le_of_lt (lt_of_le_of_lt hu hv.1))) m1 m0
  have dn12 : (∀ v u, C.r v ≤ C.r u → C.β u ≤ C.β v) → T2 / K2 ≤ T1 / K1 := fun hm =>
    C.slope_le_slope hκ _ _ (fun v u hv hu => hm u v (le_of_lt (lt_of_le_of_lt hu.2 hv.1))) m2 m1
  constructor
  · intro hbelow
    have hs := below_iff.1 hbelow
    rcases hmono with hm | hm
    · have := up01 hm
      rw [hθ, hμ]; nlinarith
    · exact absurd hs (not_lt.2 (dn12 hm))
  · intro habove
    have hs := above_iff.1 habove
    rcases hmono with hm | hm
    · exact absurd hs (not_lt.2 (up12 hm))
    · have := dn01 hm
      rw [hθ, hμ]; nlinarith

end Curve

/-! ## Theorem 2 (ii) and Lemma `lem:setid`: participant level

`U i` is AI use in arm `z` (`W(z)`), `G0 G1 S0 S1` are `g(Y(0),X)`, `g(Y(1),X)`, `S(0)`, `S(1)`.
The detector condition of Appendix D enters only through four moments, which it implies:
AI answers of the arm's users are flagged at rate TPR, also after weighting by `g`, and human
answers of the others at rate FPR. -/

section SetId

variable {Ω : Type*} [Fintype Ω]

/-- The arm moments `S̄_z`, `Ḡ_z`, `H̄_z = E[g(Y^obs,X) S^obs | Z = z]`. -/
def armS (p : Ω → ℝ) (U : Ω → Bool) (S0 S1 : Ω → ℝ) : ℝ := E p (obsVal U S0 S1)
def armG (p : Ω → ℝ) (U : Ω → Bool) (G0 G1 : Ω → ℝ) : ℝ := E p (obsVal U G0 G1)
def armH (p : Ω → ℝ) (U : Ω → Bool) (G0 G1 S0 S1 : Ω → ℝ) : ℝ :=
  E p (fun i => obsVal U G0 G1 i * obsVal U S0 S1 i)

/-- The detector condition, in the four moments the proof uses. -/
structure DetectorRates (p : Ω → ℝ) (U : Ω → Bool) (G0 G1 S0 S1 : Ω → ℝ) (fpr tpr : ℝ) : Prop where
  s1 : EOn p (fun i => U i = true) S1 = tpr * P p (fun i => U i = true)
  s0 : EOn p (fun i => U i = false) S0 = fpr * P p (fun i => U i = false)
  h1 : EOn p (fun i => U i = true) (fun i => G1 i * S1 i) = tpr * EOn p (fun i => U i = true) G1
  h0 : EOn p (fun i => U i = false) (fun i => G0 i * S0 i) = fpr * EOn p (fun i => U i = false) G0

lemma E_split (p : Ω → ℝ) (U : Ω → Bool) (f : Ω → ℝ) :
    E p f = EOn p (fun i => U i = true) f + EOn p (fun i => U i = false) f := by
  unfold E EOn; rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rcases Bool.eq_false_or_eq_true (U i) with h | h <;> simp [h]

lemma E_obs_split (p : Ω → ℝ) (U : Ω → Bool) (A B : Ω → ℝ) :
    E p (obsVal U A B) = EOn p (fun i => U i = true) B + EOn p (fun i => U i = false) A := by
  unfold E EOn obsVal; rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rcases Bool.eq_false_or_eq_true (U i) with h | h <;> simp [h]

/-- **Equation (`eq:setmom`).** With `α = Pr{W(z) = 1}`, `A = E[g(Y(1),X) | W(z) = 1]`,
`B = E[g(Y(0),X) | W(z) = 1]` and `μ = E[g(Y(0),X)]`:
`S̄ = FPR + α (TPR − FPR)`, `Ḡ = μ + α (A − B)`, `H̄ = FPR (μ − α B) + TPR α A`. -/
theorem setmom {p : Ω → ℝ} (hp : ∀ i, 0 ≤ p i) (hsum : ∑ i, p i = 1) (U : Ω → Bool)
    (G0 G1 S0 S1 : Ω → ℝ) (fpr tpr : ℝ) (hd : DetectorRates p U G0 G1 S0 S1 fpr tpr) :
    let α := P p (fun i => U i = true)
    let A := condMean p (fun i => U i = true) G1
    let B := condMean p (fun i => U i = true) G0
    armS p U S0 S1 = fpr + α * (tpr - fpr) ∧
    armG p U G0 G1 = E p G0 + α * (A - B) ∧
    armH p U G0 G1 S0 S1 = fpr * (E p G0 - α * B) + tpr * α * A := by
  intro α A B
  have h01 := P_true_add_false p hsum U
  have eA := P_mul_condMean hp (fun i => U i = true) G1
  have eB := P_mul_condMean hp (fun i => U i = true) G0
  have hE := E_split p U G0
  refine ⟨?_, ?_, ?_⟩
  · unfold armS; rw [E_obs_split, hd.s1, hd.s0]
    have : P p (fun i => U i = false) = 1 - α := by simp only [α]; linarith
    rw [this]; ring
  · unfold armG; rw [E_obs_split, hE, ← eA, ← eB]; ring
  · unfold armH
    have : E p (fun i => obsVal U G0 G1 i * obsVal U S0 S1 i)
        = EOn p (fun i => U i = true) (fun i => G1 i * S1 i)
          + EOn p (fun i => U i = false) (fun i => G0 i * S0 i) := by
      unfold E EOn obsVal; rw [← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl (fun i _ => ?_)
      rcases Bool.eq_false_or_eq_true (U i) with h | h <;> simp [h]
    rw [this, hd.h1, hd.h0, ← eA]
    have : EOn p (fun i => U i = false) G0 = E p G0 - α * B := by
      simp only [α, B]; rw [eB]; linarith
    rw [this]; ring

/-- **Lemma `lem:setid`.** `α = (S̄ − FPR)/(TPR − FPR)` and `A = (H̄ − FPR Ḡ)/(S̄ − FPR)`;
TPR cancels in `A`. -/
theorem setid {p : Ω → ℝ} (hp : ∀ i, 0 ≤ p i) (hsum : ∑ i, p i = 1) (U : Ω → Bool)
    (G0 G1 S0 S1 : Ω → ℝ) (fpr tpr : ℝ) (hd : DetectorRates p U G0 G1 S0 S1 fpr tpr)
    (hrate : tpr ≠ fpr) (hα : P p (fun i => U i = true) ≠ 0) :
    P p (fun i => U i = true) = (armS p U S0 S1 - fpr) / (tpr - fpr) ∧
    condMean p (fun i => U i = true) G1
      = (armH p U G0 G1 S0 S1 - fpr * armG p U G0 G1) / (armS p U S0 S1 - fpr) := by
  obtain ⟨hS, hG, hH⟩ := setmom hp hsum U G0 G1 S0 S1 fpr tpr hd
  have hd' : tpr - fpr ≠ 0 := sub_ne_zero.mpr hrate
  constructor
  · rw [hS]; field_simp; ring
  · rw [hS, hG, hH]
    have : P p (fun i => U i = true) * (tpr - fpr) ≠ 0 := mul_ne_zero hα hd'
    field_simp
    ring

/-- `B ∈ [g_min, g_max]` when `g(Y(0),X)` is bounded on the arm's AI users. -/
lemma condMean_mem {p : Ω → ℝ} (hp : ∀ i, 0 ≤ p i) (A : Ω → Prop) [DecidablePred A]
    (f : Ω → ℝ) (lo hi : ℝ) (hf : ∀ i, A i → lo ≤ f i ∧ f i ≤ hi) (hA : 0 < P p A) :
    lo ≤ condMean p A f ∧ condMean p A f ≤ hi := by
  have key : lo * P p A ≤ EOn p A f ∧ EOn p A f ≤ hi * P p A := by
    unfold EOn P; rw [Finset.mul_sum, Finset.mul_sum]
    constructor
    · refine Finset.sum_le_sum (fun i _ => ?_)
      split_ifs with h
      · nlinarith [hp i, (hf i h).1]
      · simp
    · refine Finset.sum_le_sum (fun i _ => ?_)
      split_ifs with h
      · nlinarith [hp i, (hf i h).2]
      · simp
  unfold condMean
  constructor
  · rw [le_div_iff₀ hA]; linarith [key.1]
  · rw [div_le_iff₀ hA]; linarith [key.2]

/-- **Theorem 2 (ii).** If `g ∈ [g_min, g_max]`, then
`E[g(Y(0),X)] ∈ [Ḡ + α (g_min − A), Ḡ + α (g_max − A)]`, where `α` and `A` are identified by
Lemma `lem:setid`. (The nesting of the intervals across arms and the sharpness of the interval
of arm `M`, Appendix D, are not formalized.) -/
theorem thm2_ii {p : Ω → ℝ} (hp : ∀ i, 0 ≤ p i) (hsum : ∑ i, p i = 1) (U : Ω → Bool)
    (G0 G1 S0 S1 : Ω → ℝ) (fpr tpr gmin gmax : ℝ) (hd : DetectorRates p U G0 G1 S0 S1 fpr tpr)
    (hg : ∀ i, gmin ≤ G0 i ∧ G0 i ≤ gmax) (hα : 0 < P p (fun i => U i = true)) :
    let α := P p (fun i => U i = true)
    let A := condMean p (fun i => U i = true) G1
    armG p U G0 G1 + α * (gmin - A) ≤ E p G0 ∧ E p G0 ≤ armG p U G0 G1 + α * (gmax - A) := by
  intro α A
  obtain ⟨_, hG, _⟩ := setmom hp hsum U G0 G1 S0 S1 fpr tpr hd
  have hB := condMean_mem hp (fun i => U i = true) G0 gmin gmax (fun i _ => hg i) hα
  have hG' : armG p U G0 G1 = E p G0 + α * (A - condMean p (fun i => U i = true) G0) := hG
  constructor <;> nlinarith [hB.1, hB.2, hα]

/-- **Lemma `lem:setid`, adjacent arms.** With nested arms `U' ≤ U` (Assumption A4(iii)),
`(H̄_z − FPR Ḡ_z) − (H̄_{z+1} − FPR Ḡ_{z+1}) = (TPR − FPR) E[g(Y(1),X) 1{W(z)=1, W(z+1)=0}]`, so
`A_{z,z+1} = (dH̄ − FPR dḠ)/dS̄` once divided by `dS̄ = (TPR − FPR)(α_z − α_{z+1})`. -/
theorem setid_adjacent {p : Ω → ℝ} (hp : ∀ i, 0 ≤ p i) (hsum : ∑ i, p i = 1) (U U' : Ω → Bool)
    (hnest : ∀ i, U' i = true → U i = true) (G0 G1 S0 S1 : Ω → ℝ) (fpr tpr : ℝ)
    (hd : DetectorRates p U G0 G1 S0 S1 fpr tpr) (hd' : DetectorRates p U' G0 G1 S0 S1 fpr tpr) :
    (armH p U G0 G1 S0 S1 - fpr * armG p U G0 G1)
        - (armH p U' G0 G1 S0 S1 - fpr * armG p U' G0 G1)
      = (tpr - fpr) * EOn p (fun i => U i = true ∧ U' i = false) G1 := by
  obtain ⟨_, hG, hH⟩ := setmom hp hsum U G0 G1 S0 S1 fpr tpr hd
  obtain ⟨_, hG', hH'⟩ := setmom hp hsum U' G0 G1 S0 S1 fpr tpr hd'
  rw [hG, hH, hG', hH']
  have eA := P_mul_condMean hp (fun i => U i = true) G1
  have eA' := P_mul_condMean hp (fun i => U' i = true) G1
  have eB := P_mul_condMean hp (fun i => U i = true) G0
  have eB' := P_mul_condMean hp (fun i => U' i = true) G0
  have hdiff : EOn p (fun i => U i = true) G1 - EOn p (fun i => U' i = true) G1
      = EOn p (fun i => U i = true ∧ U' i = false) G1 := by
    unfold EOn; rw [← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    have hn := hnest i
    rcases Bool.eq_false_or_eq_true (U i) with h | h <;>
      rcases Bool.eq_false_or_eq_true (U' i) with h' | h' <;> simp_all
  rw [← hdiff, ← eA, ← eA']
  ring

end SetId

end AIC

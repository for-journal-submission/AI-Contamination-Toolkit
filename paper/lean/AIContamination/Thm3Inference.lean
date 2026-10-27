import AIContamination.Thm2Curve
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Inv

/-!
# Theorem `thm:inference` (Appendix E): the exact parts

Formalized: the moment function `M` (`ψ` in the paper), `M(θ₀) = 0` at the truth, its uniqueness
when the first stage is nonzero, linearity in `θ₀`, the gradient with respect to the five means,
the exact second-order remainder, the gradient of the estimator used in the delta method, and
the fact that the Anderson–Rubin set solves a quadratic inequality (bounded when its leading
coefficient is positive, unbounded when it is negative).

Not formalized (standard asymptotic results, cited in the paper): the central limit theorem,
the delta method, the consistency of `v̂`, weak-instrument asymptotics, the coverage of the
Anderson–Rubin set and its uniformity, and the split of the error when the admissible range of
the bounds is estimated.
-/

open Finset

namespace AIC

set_option linter.unusedSectionVars false

/-- `M(θ₀) = (θ₀ − Ȳ₁)(S̄₀ − S̄₁) − (S̄₁ − FPR)(Ȳ₁ − Ȳ₀)`. -/
def Mfun (θ Y1 Y0 S0 S1 F : ℝ) : ℝ := (θ - Y1) * (S0 - S1) - (S1 - F) * (Y1 - Y0)

/-- **`M(θ₀) = 0` at the truth** under Theorem 2 (i): arms `a0` (relaxed) and `a1`. -/
theorem M_zero_at_truth {Ω : Type*} [Fintype Ω] (C : Curve Ω) (β₀ : ℝ)
    (hβ : ∀ v, C.τ v = β₀ * C.κ v) (a0 a1 : ℝ) :
    Mfun C.μ (C.G a1) (C.G a0) (C.S a0) (C.S a1) C.fpr = 0 := by
  unfold Mfun; rw [C.G_line β₀ hβ a0, C.G_line β₀ hβ a1]; ring

/-- **The identifying equation of the bounds.** At the true secant slope `b = β_M` of
Equation (`eq:line`), `θ₀ − Ḡ_M + b (S̄_M − FPR) = 0` at `θ₀ = E[g(Y(0),X)]`; it is a
polynomial in the arm means and FPR, as the proof of Theorem `thm:inference` uses. -/
theorem bound_equation {Ω : Type*} [Fintype Ω] (C : Curve Ω) (c : ℝ) (h : C.I c C.κ ≠ 0) :
    C.μ - C.G c + C.I c C.τ / C.I c C.κ * (C.S c - C.fpr) = 0 := by
  have := C.eq_line c h; linarith

/-- `M` is linear in `θ₀` with slope equal to the first stage. -/
theorem M_linear (θ Y1 Y0 S0 S1 F : ℝ) :
    Mfun θ Y1 Y0 S0 S1 F = (S0 - S1) * θ - (Y1 * (S0 - S1) + (S1 - F) * (Y1 - Y0)) := by
  unfold Mfun; ring

/-- With a nonzero first stage, the only root of `M` is the estimator `θ_{01}` of Theorem 2 (i). -/
theorem M_root_iff (θ Y1 Y0 S0 S1 F : ℝ) (h : S0 - S1 ≠ 0) :
    Mfun θ Y1 Y0 S0 S1 F = 0 ↔ θ = Y1 + (S1 - F) / (S0 - S1) * (Y1 - Y0) := by
  unfold Mfun
  constructor
  · intro hM; field_simp; linarith
  · intro hθ; rw [hθ]; field_simp; ring

/-- An affine function `t ↦ a t + b` has derivative `a`. -/
lemma hasDerivAt_affine (f : ℝ → ℝ) (a b x : ℝ) (h : ∀ t, f t = a * t + b) :
    HasDerivAt f a x := by
  have : f = fun t => a * t + b := funext h
  rw [this]; simpa using ((hasDerivAt_id x).const_mul a).add_const b

/-- **Gradient of `M`** with respect to `(Ȳ₁, Ȳ₀, S̄₀, S̄₁, FPR)`:
`(−(S̄₀ − FPR), S̄₁ − FPR, θ₀ − Ȳ₁, −(θ₀ − Ȳ₀), Ȳ₁ − Ȳ₀)`. -/
theorem M_gradient (θ Y1 Y0 S0 S1 F : ℝ) :
    HasDerivAt (fun t => Mfun θ t Y0 S0 S1 F) (-(S0 - F)) Y1 ∧
    HasDerivAt (fun t => Mfun θ Y1 t S0 S1 F) (S1 - F) Y0 ∧
    HasDerivAt (fun t => Mfun θ Y1 Y0 t S1 F) (θ - Y1) S0 ∧
    HasDerivAt (fun t => Mfun θ Y1 Y0 S0 t F) (-(θ - Y0)) S1 ∧
    HasDerivAt (fun t => Mfun θ Y1 Y0 S0 S1 t) (Y1 - Y0) F := by
  refine ⟨hasDerivAt_affine _ _ (θ * (S0 - S1) + (S1 - F) * Y0) _ (fun t => by unfold Mfun; ring),
    hasDerivAt_affine _ _ ((θ - Y1) * (S0 - S1) - (S1 - F) * Y1) _ (fun t => by unfold Mfun; ring),
    hasDerivAt_affine _ _ (-(θ - Y1) * S1 - (S1 - F) * (Y1 - Y0)) _ (fun t => by unfold Mfun; ring),
    hasDerivAt_affine _ _ ((θ - Y1) * S0 + F * (Y1 - Y0)) _ (fun t => by unfold Mfun; ring),
    hasDerivAt_affine _ _ ((θ - Y1) * (S0 - S1) - S1 * (Y1 - Y0)) _ (fun t => by unfold Mfun; ring)⟩

/-- **Exact expansion.** `M` is a polynomial: its increment is the gradient term plus a remainder
that is a product of two increments (hence `O_p(1/N)`, i.e. `O_p(N^{-1/2})` after scaling by
`√N`). -/
theorem M_expansion (θ Y1 Y0 S0 S1 F d1 d0 e0 e1 f : ℝ) :
    Mfun θ (Y1 + d1) (Y0 + d0) (S0 + e0) (S1 + e1) (F + f) - Mfun θ Y1 Y0 S0 S1 F
      = (-(S0 - F)) * d1 + (S1 - F) * d0 + (θ - Y1) * e0 + (-(θ - Y0)) * e1 + (Y1 - Y0) * f
        + (-d1 * (e0 - e1) - (e1 - f) * (d1 - d0)) := by
  unfold Mfun; ring

/-- The estimator `θ̂ = Ȳ₁ + λ̂ (Ȳ₁ − Ȳ₀)`, `λ̂ = (S̄₁ − FPR)/(S̄₀ − S̄₁)`. -/
noncomputable def thetaHat (Y1 Y0 S0 S1 F : ℝ) : ℝ := Y1 + (S1 - F) / (S0 - S1) * (Y1 - Y0)

/-- **Delta-method coefficients of `θ̂`** (the interval of the IV estimator in Table 2):
`∂θ̂/∂(Ȳ₁, Ȳ₀, S̄₀, S̄₁, FPR) = (1 + λ, −λ, −cλ, c(1 + λ), −c)`,
`λ = (S̄₁ − FPR)/(S̄₀ − S̄₁)`, `c = (Ȳ₁ − Ȳ₀)/(S̄₀ − S̄₁)`. -/
theorem thetaHat_gradient (Y1 Y0 S0 S1 F : ℝ) (h : S0 - S1 ≠ 0) :
    let lam := (S1 - F) / (S0 - S1)
    let c := (Y1 - Y0) / (S0 - S1)
    HasDerivAt (fun t => thetaHat t Y0 S0 S1 F) (1 + lam) Y1 ∧
    HasDerivAt (fun t => thetaHat Y1 t S0 S1 F) (-lam) Y0 ∧
    HasDerivAt (fun t => thetaHat Y1 Y0 S0 S1 t) (-c) F ∧
    HasDerivAt (fun t => thetaHat Y1 Y0 t S1 F) (-(c * lam)) S0 ∧
    HasDerivAt (fun t => thetaHat Y1 Y0 S0 t F) (c * (1 + lam)) S1 := by
  intro lam c
  refine ⟨hasDerivAt_affine _ _ (-lam * Y0) _ (fun t => by unfold thetaHat; ring),
    hasDerivAt_affine _ _ (Y1 + lam * Y1) _ (fun t => by unfold thetaHat; ring),
    hasDerivAt_affine _ _ (Y1 + S1 / (S0 - S1) * (Y1 - Y0)) _
      (fun t => by unfold thetaHat; simp only [c]; ring), ?_, ?_⟩
  · have hd : HasDerivAt (fun t => t - S1) 1 S0 := by
      simpa using (hasDerivAt_id S0).sub_const S1
    have hq := ((hasDerivAt_const S0 (S1 - F)).div hd h).mul_const (Y1 - Y0)
    have hq2 := hq.const_add Y1
    unfold thetaHat
    convert hq2 using 1
    simp only [c, lam]; field_simp; ring
  · have hn : HasDerivAt (fun t => t - F) 1 S1 := by
      simpa using (hasDerivAt_id S1).sub_const F
    have hd : HasDerivAt (fun t => S0 - t) (-1) S1 := by
      simpa using (hasDerivAt_id S1).const_sub S0
    have hq := ((hn.div hd h).mul_const (Y1 - Y0)).const_add Y1
    unfold thetaHat
    convert hq using 1
    simp only [c, lam]; field_simp; ring

/-! ## The Anderson–Rubin set solves a quadratic inequality -/

section AR

variable {J : Type*} [Fintype J]

/-- Variance under a finite distribution `r`. -/
def Var (r : J → ℝ) (f : J → ℝ) : ℝ := E r (fun j => f j ^ 2) - E r f ^ 2
/-- Covariance under `r`. -/
def Cov (r : J → ℝ) (f g : J → ℝ) : ℝ := E r (fun j => f j * g j) - E r f * E r g

lemma E_lin (r f g : J → ℝ) (a b : ℝ) :
    E r (fun j => a * f j + b * g j) = a * E r f + b * E r g := by
  unfold E; rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl (fun j _ => by ring)

/-- `Var(aY + bS) = a² Var Y + 2ab Cov(Y,S) + b² Var S`. -/
theorem Var_lin (r Y S : J → ℝ) (a b : ℝ) :
    Var r (fun j => a * Y j + b * S j) = a ^ 2 * Var r Y + 2 * a * b * Cov r Y S + b ^ 2 * Var r S := by
  unfold Var Cov
  rw [E_lin]
  have : E r (fun j => (a * Y j + b * S j) ^ 2)
      = a ^ 2 * E r (fun j => Y j ^ 2) + (2 * a * b) * E r (fun j => Y j * S j)
        + b ^ 2 * E r (fun j => S j ^ 2) := by
    unfold E; simp only [Finset.mul_sum, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl (fun j _ => by ring)
  rw [this]; ring

/-- The variance `v(θ₀)` of the proof of Theorem `thm:inference` with plug-in moments: arm `z` has a finite
distribution `r_z` of `(Y^obs, S^obs)`. -/
noncomputable def vAR (r1 r0 Y1v S1v Y0v S0v : J → ℝ) (F ρ γ θ : ℝ) : ℝ :=
  Var r1 (fun j => (E r0 S0v - F) * Y1v j + (θ - E r0 Y0v) * S1v j) / ρ
  + Var r0 (fun j => (E r1 S1v - F) * Y0v j + (θ - E r1 Y1v) * S0v j) / (1 - ρ)
  + γ * (E r1 Y1v - E r0 Y0v) ^ 2 * (F * (1 - F))

/-- **The Anderson–Rubin set solves a quadratic inequality.** With `M̂` linear and `v̂`
quadratic in `θ₀`, `{θ₀ : N M̂(θ₀)² ≤ z² v̂(θ₀)} = {θ₀ : A θ₀² + B θ₀ + C ≤ 0}`, where
`A = N (S̄₀ − S̄₁)² − z² {Var(S | Z=1)/ρ + Var(S | Z=0)/(1−ρ)}`. -/
theorem AR_quadratic (r1 r0 Y1v S1v Y0v S0v : J → ℝ) (F ρ γ N z : ℝ) :
    ∃ B C : ℝ, ∀ θ : ℝ,
      N * Mfun θ (E r1 Y1v) (E r0 Y0v) (E r0 S0v) (E r1 S1v) F ^ 2
          - z ^ 2 * vAR r1 r0 Y1v S1v Y0v S0v F ρ γ θ
        = (N * (E r0 S0v - E r1 S1v) ^ 2 - z ^ 2 * (Var r1 S1v / ρ + Var r0 S0v / (1 - ρ)))
            * θ ^ 2 + B * θ + C := by
  set Y1 := E r1 Y1v; set Y0 := E r0 Y0v; set S1 := E r1 S1v; set S0 := E r0 S0v
  set a1 := S0 - F; set a0 := S1 - F
  set k := Y1 * (S0 - S1) + (S1 - F) * (Y1 - Y0)
  refine ⟨N * (-2 * (S0 - S1) * k)
      - z ^ 2 * ((2 * a1 * Cov r1 Y1v S1v - 2 * Y0 * Var r1 S1v) / ρ
        + (2 * a0 * Cov r0 Y0v S0v - 2 * Y1 * Var r0 S0v) / (1 - ρ)),
    N * k ^ 2 - z ^ 2 * ((a1 ^ 2 * Var r1 Y1v - 2 * a1 * Y0 * Cov r1 Y1v S1v
        + Y0 ^ 2 * Var r1 S1v) / ρ
      + (a0 ^ 2 * Var r0 Y0v - 2 * a0 * Y1 * Cov r0 Y0v S0v + Y1 ^ 2 * Var r0 S0v) / (1 - ρ)
      + γ * (Y1 - Y0) ^ 2 * (F * (1 - F))), fun θ => ?_⟩
  unfold vAR
  rw [M_linear, Var_lin, Var_lin]
  ring

/-- A quadratic set with a positive leading coefficient is bounded. -/
theorem quad_set_bounded (A B C : ℝ) (hA : 0 < A) :
    ∃ R, ∀ θ, A * θ ^ 2 + B * θ + C ≤ 0 → |θ| ≤ R := by
  refine ⟨(|B| + |C|) / A + 1, fun θ hθ => ?_⟩
  by_contra hcon0
  have hcon := lt_of_not_ge hcon0
  have hR1 : 1 ≤ (|B| + |C|) / A + 1 := by
    have : 0 ≤ (|B| + |C|) / A := by positivity
    linarith
  have hθ1 : 1 < |θ| := lt_of_le_of_lt hR1 hcon
  have hAR : |B| + |C| < A * (|θ| - 1) := by
    have := (div_lt_iff₀ hA).1 (by linarith : (|B| + |C|) / A < |θ| - 1)
    linarith
  have hsq : θ ^ 2 = |θ| ^ 2 := (sq_abs θ).symm
  have hB : -(B * θ) ≤ |B| * |θ| := by
    have := neg_abs_le (B * θ); rw [abs_mul] at this; linarith
  have hC : -C ≤ |C| * |θ| := by
    have := neg_abs_le C; nlinarith [abs_nonneg C]
  nlinarith [abs_nonneg B, abs_nonneg C]

/-- A quadratic set with a negative leading coefficient is unbounded: it contains every
`θ ≥ R`. -/
theorem quad_set_unbounded (A B C : ℝ) (hA : A < 0) :
    ∃ R, ∀ θ, R ≤ θ → A * θ ^ 2 + B * θ + C ≤ 0 := by
  refine ⟨(|B| + |C|) / (-A) + 1, fun θ hθ => ?_⟩
  have hnA : 0 < -A := by linarith
  have h0 : 0 ≤ (|B| + |C|) / (-A) := by positivity
  have hθ1 : 1 ≤ θ := by linarith
  have hk : |B| + |C| ≤ -A * (θ - 1) := by
    have := (div_le_iff₀ hnA).1 (by linarith : (|B| + |C|) / (-A) ≤ θ - 1); linarith
  have hB : B * θ ≤ |B| * θ := by
    have := le_abs_self B; nlinarith
  have hC : C ≤ |C| * θ := by
    have := le_abs_self C; nlinarith [abs_nonneg C]
  nlinarith [abs_nonneg B, abs_nonneg C]

end AR

end AIC

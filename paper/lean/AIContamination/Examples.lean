import AIContamination.Thm1Deletion
import AIContamination.Thm2Curve
import Mathlib.Data.Fin.VecNotation
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Tactic.FinCases

/-!
# Every number in the examples

* Table 1 (`tab:example`): 100 participants answer the bat-and-ball question; 50 would answer
  wrong, 25 of them let AI answer, and AI answers right.
* Figure 1 (`fig:setid`) and its example in Appendix D.
-/

open Finset

namespace AIC.Examples

noncomputable section

set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unnecessarySeqFocus false
set_option linter.unusedSimpArgs false

/-! ## Table 1 -/

/-- Types: 0 = wrong, own answer; 1 = would answer wrong, AI answers right; 2 = right. -/
def p1 : Fin 3 → ℝ := ![1/4, 1/4, 1/2]
def W1 : Fin 3 → Bool := ![false, true, false]
/-- `true` = wrong (10 cents). -/
def Y0t : Fin 3 → Bool := ![true, true, false]
def Yobst : Fin 3 → Bool := ![true, false, false]
/-- The poor detector flags the 50 who answer right themselves and misses the 25 AI users. -/
def Spoor : Fin 3 → Bool := ![false, false, true]
/-- `g(y) = y` with `y = 1` for a wrong answer. -/
def gD : Bool → ℝ := fun b => if b then 1 else 0

/-- Share reported wrong after deleting the answers flagged by `S`. -/
def reported (S : Fin 3 → Bool) : ℝ :=
  (∑ i, p1 i * (if S i then 0 else 1) * gD (Yobst i)) / (∑ i, p1 i * (if S i then 0 else 1))

/-- Table 1, last column: 25%, 33%, 50%. -/
theorem table1_reported :
    reported (fun _ => false) = 1/4 ∧ reported W1 = 1/3 ∧ reported Spoor = 1/2 := by
  refine ⟨?_, ?_, ?_⟩ <;>
  simp [reported, Fin.sum_univ_three, p1, W1, Spoor, Yobst, gD] <;> norm_num

/-- Table 1, people misclassified (out of 100): 25, 0, 75. -/
theorem table1_misclassified :
    100 * ∑ i, (if (false : Bool) ≠ W1 i then p1 i else 0) = 25 ∧
    100 * ∑ i, (if W1 i ≠ W1 i then p1 i else 0) = 0 ∧
    100 * ∑ i, (if Spoor i ≠ W1 i then p1 i else 0) = 75 := by
  refine ⟨?_, ?_, ?_⟩ <;> simp [Fin.sum_univ_three, p1, W1, Spoor] <;> norm_num

/-- Ideal weights of Lemma `lem:balance`: `ω*(1) = 2`, `ω*(0) = 2/3`. -/
theorem table1_omegaStar : omegaStar p1 Y0t Yobst true = 2 ∧ omegaStar p1 Y0t Yobst false = 2/3 := by
  refine ⟨?_, ?_⟩ <;> simp [omegaStar, mass, Fin.sum_univ_three, p1, Y0t, Yobst] <;> norm_num

/-- No correction: `ω = 1`. -/
def omNone : Fin 3 → ℝ := fun _ => 1
/-- A perfect detector: `ω = (1 − W)/0.75`. -/
def omPerfect : Fin 3 → ℝ := fun i => (if W1 i then 0 else 1) / (3/4)
/-- The poor detector: `ω = (1 − S^obs)/0.5`. -/
def omPoor : Fin 3 → ℝ := fun i => (if Spoor i then 0 else 1) / (1/2)

/-- Average weights: no correction 1; perfect detector `4/3` and `8/9`; poor detector `2` and
`2/3`, the ideal weights. -/
theorem table1_omegaBar :
    omegaBar p1 omNone Yobst true = 1 ∧
    omegaBar p1 omPerfect Yobst true = 4/3 ∧ omegaBar p1 omPerfect Yobst false = 8/9 ∧
    omegaBar p1 omPoor Yobst true = 2 ∧ omegaBar p1 omPoor Yobst false = 2/3 := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;>
  simp [omegaBar, wmass, mass, Fin.sum_univ_three, p1, Yobst, omNone, omPerfect, omPoor, W1,
    Spoor] <;> norm_num

/-- Biases: `−0.25`, `−1/6`, `0`. -/
theorem table1_bias :
    bias p1 omNone Y0t Yobst gD = -1/4 ∧ bias p1 omPerfect Y0t Yobst gD = -1/6 ∧
    bias p1 omPoor Y0t Yobst gD = 0 := by
  refine ⟨?_, ?_, ?_⟩ <;>
  simp [bias, E, Fin.sum_univ_three, p1, Y0t, Yobst, gD, omNone, omPerfect, omPoor, W1,
    Spoor] <;> norm_num

/-- The same biases from Lemma `lem:balance`: `0.25 {ω̄(1) − 2}`. -/
theorem table1_bias_via_thm1 :
    (1/4 : ℝ) * (1 - 2) = -1/4 ∧ (1/4 : ℝ) * (4/3 - 2) = -1/6 ∧ (1/4 : ℝ) * (2 - 2) = 0 := by
  norm_num

/-- `E[Y(0)] = 0.5`, `E[Y^obs] = 0.25`. -/
theorem table1_means : E p1 (fun i => gD (Y0t i)) = 1/2 ∧ E p1 (fun i => gD (Yobst i)) = 1/4 := by
  refine ⟨?_, ?_⟩ <;> simp [E, Fin.sum_univ_three, p1, Y0t, Yobst, gD] <;> norm_num

/-- Theorem 1 with a perfect detector: the bias is `α {E[g | W = 0] − E[g | W = 1]}
= 0.25 (1/3 − 1) = −1/6`. -/
theorem table1_perfect_detector :
    condMean p1 (fun i => W1 i = false) (obsVal W1 (fun i => gD (Y0t i)) (fun _ => 0))
      - E p1 (fun i => gD (Y0t i)) = -1/6 := by
  simp [condMean, EOn, P, E, obsVal, Fin.sum_univ_three, p1, W1, Y0t, gD]; norm_num

/-! ## Figure 1 and its example (Appendix D)

Resistance groups, in the order in which a friction stops them: 0 = the 5 who use AI in every
arm (wrong at 80%), 1 = the 5 whom only arm 2 stops (60%), 2 = the 20 compliers whom arm 1
stops (40%), 3 = the 70 never-takers (50%). AI answers right, so `τ = −(wrong share)` for the
groups that use AI; the never-takers' `τ` never enters an arm and is set to 0. `FPR = 0.1`,
`TPR = 0.9`, so `κ = 0.8`. Arms 2, 1, 0 have thresholds 0, 1, 2. -/

def fig : Curve (Fin 4) where
  p := ![1/20, 1/20, 1/5, 7/10]
  hp := by intro v; fin_cases v <;> norm_num
  r := ![0, 1, 2, 3]
  τ := ![-4/5, -3/5, -2/5, 0]
  κ := fun _ => 4/5
  μ := 1/2
  fpr := 1/10

/-- The arms: `(S̄_z, Ḡ_z) = (0.34, 0.35), (0.18, 0.43), (0.14, 0.46)`; `α_z = 0.30, 0.10, 0.05`. -/
theorem fig_arms :
    fig.S 2 = 0.34 ∧ fig.G 2 = 0.35 ∧ fig.S 1 = 0.18 ∧ fig.G 1 = 0.43 ∧
    fig.S 0 = 0.14 ∧ fig.G 0 = 0.46 ∧ fig.α 2 = 0.30 ∧ fig.α 1 = 0.10 ∧ fig.α 0 = 0.05 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
  simp [Curve.S, Curve.G, Curve.α, Curve.I, fig, Fin.sum_univ_four] <;> norm_num

/-- `θ_{01} = 0.47`, `θ_{12} = 0.49`; the truth is `0.5`. -/
theorem fig_theta : fig.θ 2 1 = 0.47 ∧ fig.θ 1 0 = 0.49 ∧ fig.μ = 0.5 := by
  refine ⟨?_, ?_, ?_⟩ <;>
  simp [Curve.θ, Curve.S, Curve.G, Curve.I, fig, Fin.sum_univ_four] <;> norm_num

/-- Slopes: `β_{01} = −0.5`, `β_1 = −0.875 = 1.75 β_{01}`, `β_{12} = −0.75`, `β_2 = −1`; the
misses `(β_1 − β_{01})(S̄_1 − FPR) = −0.03` and `(β_2 − β_{12})(S̄_2 − FPR) = −0.01`. -/
theorem fig_slopes :
    (fig.G 2 - fig.G 1) / (fig.S 2 - fig.S 1) = -0.5 ∧
    fig.I 1 fig.τ / fig.I 1 fig.κ = -0.875 ∧ (-0.875 : ℝ) = 1.75 * (-0.5) ∧
    (fig.G 1 - fig.G 0) / (fig.S 1 - fig.S 0) = -0.75 ∧
    fig.I 0 fig.τ / fig.I 0 fig.κ = -1 ∧
    (-0.875 - (-0.5) : ℝ) * (0.18 - 0.1) = -0.03 ∧ (-1 - (-0.75) : ℝ) * (0.14 - 0.1) = -0.01 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
  simp [Curve.S, Curve.G, Curve.I, fig, Fin.sum_univ_four] <;> norm_num

/-- Theorem 2 (ii) with `g ∈ [0, 1]` and `A_z = 0`: `[0.43, 0.53]` from arm 1 and
`[0.46, 0.51]` from arm 2; `α_z = (S̄_z − FPR)/(TPR − FPR)`. -/
theorem fig_manski :
    (fig.S 1 - 0.1) / (0.9 - 0.1) = 0.10 ∧ (fig.S 0 - 0.1) / (0.9 - 0.1) = 0.05 ∧
    fig.G 1 + 0.10 * (0 - 0) = 0.43 ∧ fig.G 1 + 0.10 * (1 - 0) = 0.53 ∧
    fig.G 0 + 0.05 * (0 - 0) = 0.46 ∧ fig.G 0 + 0.05 * (1 - 0) = 0.51 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
  simp [Curve.S, Curve.G, Curve.I, fig, Fin.sum_univ_four] <;> norm_num

/-- Theorem 2 (iv): the line through arms 0 and 2 reaches `0.438` at `S̄_1 = 0.18`, above
`Ḡ_1 = 0.43`, so arm 1 lies below it. -/
theorem fig_below :
    fig.G 0 + (fig.G 2 - fig.G 0) * (fig.S 1 - fig.S 0) / (fig.S 2 - fig.S 0) = 0.438 ∧
    fig.G 1 < 0.438 := by
  refine ⟨?_, ?_⟩ <;>
  simp [Curve.S, Curve.G, Curve.I, fig, Fin.sum_univ_four] <;> norm_num

/-- `β(v)` rises in `v` in this population (`−1, −0.75, −0.5, 0`), so Theorem 2 (iv) applies
and gives `E[g(Y(0),X)] ≥ θ_{12} = 0.49`; with Theorem 2 (ii) from arm 2, `[0.49, 0.51]`. -/
theorem fig_mts : fig.θ 1 0 ≤ fig.μ := by
  have hκ : ∀ v, 0 < fig.κ v := fun v => by simp [fig]
  have hmono : ∀ v u, fig.r v ≤ fig.r u → fig.β v ≤ fig.β u := by
    intro v u h
    fin_cases v <;> fin_cases u <;> simp [Curve.β, fig] at h ⊢ <;> (try norm_num at h) <;> norm_num
  have pos : ∀ (A : Fin 4 → Prop) [DecidablePred A] (v : Fin 4), A v → 0 < ∑ w, fig.wt A w := by
    intro A _ v hv
    refine Finset.sum_pos' (fun w _ => fig.wt_nonneg hκ A w) ⟨v, Finset.mem_univ v, ?_⟩
    unfold Curve.wt; rw [if_pos hv]
    fin_cases v <;> simp [fig] <;> norm_num
  have h := (fig.thm2_iv hκ (Or.inl hmono) 0 1 2 (by norm_num) (by norm_num)
    (pos _ 0 (by simp [fig])) (pos _ 1 (by simp [fig])) (pos _ 2 (by simp [fig]))).1
  apply h
  have := fig_below
  rw [this.1]; exact this.2

end

end AIC.Examples

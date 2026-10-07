/-
Modification notice for the LogTwo project.
Adapted from openai/math (Apache-2.0), revision adc7f1241b42e322a6451854ab7e4b4c146bf78a.
Changes: Adapt determinant-budget comparisons to the actual log-two minor and geometry.
See ../../../THIRD_PARTY_NOTICES.txt for provenance and the recorded changes.
-/

module

public import LogTwo.Analysis.AsymptoticUpper
public import LogTwo.Geometry.MatrixInterpolation

@[expose] public section
namespace LogTwo.Analysis
open OAI PiExponent
open LogTwo.Interpolation LogTwo.Arithmetic LogTwo.Parameters LogTwo.Geometry
open Filter Topology
noncomputable section

/-- Both bounds must use the same normalized determinant and mean row weight. -/
theorem normalized_bounds_inconsistent
    (ν θ x b ear ean err collision d : ℝ)
    (hν : 1 < ν) (hb0 : 0 ≤ b) (hb : b ≤ θ)
    (hgap : ear+ean+err < ν*(x-θ)-(1-θ))
    (hc : 1+ear+ean+err < collision)
    (hlower : -(1-b)-ear ≤ d)
    (hupper : d ≤ ean+err+max (-collision) (-ν*(x-b))) : False := by
  have hfirst : ean+err-collision < -(1-b)-ear := by linarith
  have hmono : ν*(x-θ)-(1-θ) ≤ ν*(x-b)-(1-b) := by nlinarith
  have hsecond : ean+err-ν*(x-b) < -(1-b)-ear := by linarith
  rcases le_total (-collision) (-ν*(x-b)) with h | h
  · rw [max_eq_right h] at hupper; linarith
  · rw [max_eq_left h] at hupper; linarith

/-- Once the two fixed numerical margins hold, no sufficiently large degree
can carry a nonzero full-row minor. This is uniform over all column choices. -/
theorem eventual_no_fullRowMinor {m : ℕ} (w : Weights m) {F : ℚ}
    (p : Fin m → ℤ) (q : Fin m → ℕ) (hK : 0 < w.K) (hF : 0 < F)
    {ν ws A η : ℝ} (hν : 1 < ν) (hws : 0 < ws) (hA : 0 < A) (hη : 0 ≤ η)
    (hq : ∀ k, 2 ≤ q k) (hwq : ∀ k, w.w k = ceilLogWeight (q k))
    (hw : ∀ k, ws ≤ (w.w k : ℝ))
    (happrox : ∀ k, |Real.log 2-(rationalPoint p q k : ℝ)| ≤ (q k : ℝ)^(-ν))
    (hgap : arithmeticError w F ws + fixedAnalyticError w ν (F : ℝ) ws <
      ν*(A*(1-η)-(w.theta : ℝ))-(1-(w.theta : ℝ)))
    (hcollision : 1+arithmeticError w F ws+fixedAnalyticError w ν (F : ℝ) ws < collisionLimit w A η) :
    ∀ᶠ H : ℚ in atTop, FullRowMinor w H (rationalPoint p q) (truncationOrders w F) → False := by
  have hsum : Tendsto (fun H : ℝ => arithmeticError w F ws + fixedAnalyticError w ν (F : ℝ) ws + analyticRemainder w H)
      atTop (𝓝 (arithmeticError w F ws+fixedAnalyticError w ν (F : ℝ) ws+0)) :=
    tendsto_const_nhds.add (tendsto_analyticRemainder w hK)
  have hsmall := (hsum.eventually_lt_const (by simpa using hgap)).ratCast_atTop
  have hdiff : Tendsto (fun H : ℝ => collisionRate w A η H -
      (1+arithmeticError w F ws+fixedAnalyticError w ν (F : ℝ) ws+analyticRemainder w H))
      atTop (𝓝 (collisionLimit w A η-(1+arithmeticError w F ws+fixedAnalyticError w ν (F : ℝ) ws+0))) :=
    (tendsto_collisionRate w hA η).sub (tendsto_const_nhds.add (tendsto_analyticRemainder w hK))
  have hlarge := (hdiff.eventually (Ioi_mem_nhds (show 0 < collisionLimit w A η-
      (1+arithmeticError w F ws+fixedAnalyticError w ν (F : ℝ) ws+0) by linarith))).ratCast_atTop
  filter_upwards [eventually_gt_atTop (0 : ℚ), hsmall, hlarge] with H hH hsmall hlarge
  intro minor
  have hl := fullRowMinor_bound_of_ceilLogWeights p q hq hwq hK hH hF.le ws hws hw minor
  have hu := actual_minor_log_bound_with_remainder (rationalPoint p q) q minor hK hH hF
    (by linarith : 0 ≤ ν) hws hA.le hη hq hwq hw happrox
  have hb := averageRowWeight_bounds hK hH minor
  exact normalized_bounds_inconsistent ν w.theta (A*(1-η)) (averageRowWeight minor)
    (arithmeticError w F ws) (fixedAnalyticError w ν (F : ℝ) ws) (analyticRemainder w H)
    (collisionRate w A η H) (Real.log |(minor.matrix.det : ℝ)|/((minor.size : ℝ)*(H : ℝ)))
    hν hb.1 hb.2.le hsmall (by linarith) hl hu

/-- The geometric minor is chosen above the analytic threshold. Neither the
minor's existence nor an analytic bound is an unproved input here. The two
fixed numerical margins remain explicit for the parameter-selection step. -/
theorem logTwo_contradiction_of_budgets
    (n : ℕ) (hn : 1 ≤ n) (m : ℕ) (p : Fin m → ℤ) (q : ℕ → ℕ) (hq : ∀ i, 2 ≤ q i)
    (hgrowth : ∀ i, i < m →
      denominatorSeparationFactor n m (chosenComparisonConstant n m)*
        (∏ j : Fin i, (ceilLogWeight (q j) : ℝ)) < (ceilLogWeight (q i) : ℝ)) :
    let w := chosenWeights n hn m (fun i => q i) (fun i => hq i)
    ∀ {F : ℚ} {ν ws A η : ℝ}, 1/w.theta < F → 1 < ν → 0 < ws → 0 < A → 0 ≤ η →
      (∀ k : Fin m, ws ≤ (w.w k : ℝ)) →
      (∀ k : Fin m, |Real.log 2-(rationalPoint p (fun i => q i) k : ℝ)| ≤ (q k : ℝ)^(-ν)) →
      arithmeticError w F ws+fixedAnalyticError w ν (F : ℝ) ws <
        ν*(A*(1-η)-(w.theta : ℝ))-(1-(w.theta : ℝ)) →
      1+arithmeticError w F ws+fixedAnalyticError w ν (F : ℝ) ws < collisionLimit w A η → False := by
  dsimp only
  intro F ν ws A η hF hν hws hA hη hw happrox hgap hcollision
  let w := chosenWeights n hn m (fun i => q i) (fun i => hq i)
  have hK : 0 < w.K := centerCount_pos (shape n hn).one_lt_c.le m
  have hFp : 0 < F := (div_pos (by norm_num) w.theta_pos).trans hF
  obtain ⟨B, hB⟩ := Filter.eventually_atTop.mp
    (eventual_no_fullRowMinor w p (fun i => q i) hK hFp hν hws hA hη
      (fun i => hq i) (fun _ => rfl) hw happrox hgap hcollision)
  obtain ⟨H, hH, ⟨minor⟩⟩ := MatrixCompactification.logTwo_cofinally_fullRowMinor
    n hn m q hq hgrowth (rationalPoint p (fun i => q i)) F hF B
  exact hB H hH.le minor

end
end LogTwo.Analysis

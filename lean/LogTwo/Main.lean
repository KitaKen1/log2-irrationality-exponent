module

public import LogTwo.FinalParameters
public import LogTwo.Approximation

@[expose] public section
namespace LogTwo
open Interpolation Arithmetic Parameters Analysis
noncomputable section

/-- No unbounded family of approximations exists at any exponent 2+1/n. -/
theorem not_unbounded_logTwo (n : ℕ) (hn : 1 ≤ n) :
    ¬ UnboundedApproximations (Real.log 2) (nu n : ℝ) := by
  intro hbad
  obtain ⟨m, p, q, hq, W, hm, hW, hw, hgrowth, happrox, herror, hcollision⟩ :=
    exists_small_total_parameters n hn hbad
  have hs := scalarConditions n hn
  let w := chosenWeights n hn m (fun i => q i) (fun i => hq i)
  have hF : 1/w.theta < truncationFactor n := by
    have hθ := hs.shape.theta_pos
    change 1/theta (delta n) < truncationFactor n
    have hl : (1 : ℚ)/theta (delta n) < 2/theta (delta n) := by
      exact div_lt_div_of_pos_right (by norm_num) hθ
    exact hl.trans hs.factor_gt
  have hν : (1 : ℝ) < nu n := by
    unfold nu
    push_cast
    have : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
    linarith [one_div_pos.mpr this]
  apply logTwo_contradiction_of_budgets n hn m (fun i => p i) q hq hgrowth
    hF hν hW (show (0 : ℝ) < a (delta n) by exact_mod_cast hs.shape.theta_pos.trans hs.shape.theta_lt_a)
    (show (0 : ℝ) ≤ eta n by exact_mod_cast hs.eta_pos.le) (fun i => hw i)
  · intro k
    simpa only [rationalPoint, Rat.cast_div, Rat.cast_intCast, Rat.cast_natCast] using happrox k
  · have hg : (epsilon n : ℝ) < (finalGap n : ℝ) := by exact_mod_cast hs.epsilon_lt_gap
    have hgap := herror.trans hg
    simpa only [finalGap, Rat.cast_sub, Rat.cast_mul, Rat.cast_one, chosenWeights] using hgap
  · have he : (epsilon n : ℝ) < (1 : ℝ)/2 := by
      have hh : (epsilon n : ℝ) < ((1/2 : ℚ) : ℝ) := Rat.cast_lt.mpr hs.epsilon_lt_half
      norm_num at hh ⊢
      exact hh
    linarith

theorem logTwo_sequentialLowerBound : SequentialLowerBound (Real.log 2) := by
  by_contra h
  obtain ⟨n, hn, hbad⟩ := exists_unbounded_of_not_sequential h
  apply not_unbounded_logTwo n hn
  simpa only [nu, Rat.cast_add, Rat.cast_ofNat, Rat.cast_div, Rat.cast_one, Rat.cast_natCast] using hbad

theorem logTwo_eventualLowerBound : LogTwoLowerBound :=
  (sequentialLowerBound_iff (Real.log 2)).mp logTwo_sequentialLowerBound

theorem logTwo_irrational : Irrational (Real.log 2) :=
  irrational_of_eventualLowerBound logTwo_eventualLowerBound

/-- Unconditional theorem for the irrationality exponent of the natural log. -/
theorem logTwo_exponent_eq_two : LogTwoExponentTwo :=
  logTwoExponentTwo_of_sequentialLowerBound logTwo_sequentialLowerBound

end
end LogTwo

module

public import LogTwo.Analysis.BudgetContradiction

@[expose] public section
namespace LogTwo
open Interpolation Arithmetic Parameters Analysis LogTwo.Geometry
open scoped BigOperators
noncomputable section

def remainingWeightCoefficient {m : ℕ} (w : Weights m) (ν : ℝ) : ℝ :=
  lcmConstant*m+(w.theta : ℝ)+Real.log 4+Real.log (w.K : ℝ)+ν+Real.log (200*(w.K : ℝ))

theorem totalError_le_uniform {m : ℕ} (w : Weights m) (F : ℚ) (ν W : ℝ)
    (hW : 0 < W) (hw : ∀ i, W ≤ (w.w i : ℝ)) :
    arithmeticError w F W+fixedAnalyticError w ν (F : ℝ) W ≤
      lcmConstant*(F : ℝ)*m/(w.v0 : ℝ)+100*(w.K : ℝ)/(w.w0 : ℝ)+
        2*Real.log 2/(w.v0 : ℝ)+ν/(F : ℝ)+remainingWeightCoefficient w ν/W := by
  calc
    _ ≤ (lcmConstant*(F : ℝ)*m/(w.v0 : ℝ)+(lcmConstant*m+(w.theta : ℝ))/W) +
        fixedAnalyticError w ν (F : ℝ) W := add_le_add (arithmeticError_le_uniform w F W hW hw) le_rfl
    _ = _ := by
      unfold fixedAnalyticError translationBudget holomorphicBudget remainingWeightCoefficient
      ring

theorem chosen_collisionLimit_eq (n : ℕ) (hn : 1 ≤ n) (m : ℕ)
    (q : Fin m → ℕ) (hq : ∀ i, 2 ≤ q i) :
    collisionLimit (chosenWeights n hn m q hq) (a (delta n)) (eta n) =
      (Real.log 2/8)*(eta n : ℝ)^2*
        (((b (delta n)/a (delta n) : ℚ) : ℝ)^m/((m : ℝ)+1)) := by
  have hs := shape n hn
  have hk : (centerCount (c (delta n)) m : ℝ) ≠ 0 := by
    exact_mod_cast (centerCount_pos hs.one_lt_c.le m).ne'
  have ht : (theta (delta n) : ℝ) ≠ 0 := by exact_mod_cast hs.theta_pos.ne'
  have ha : (a (delta n) : ℝ) ≠ 0 := by exact_mod_cast (hs.theta_pos.trans hs.theta_lt_a).ne'
  have hb : (b (delta n) : ℝ) ≠ 0 := by exact_mod_cast (hs.theta_pos.trans (hs.theta_lt_a.trans hs.a_lt_b)).ne'
  simp only [collisionLimit, chosenWeights, verticalWeight, horizontalWeight,
    Rat.cast_mul, Rat.cast_ofNat, Rat.cast_pow, Rat.cast_inv, Rat.cast_natCast, Rat.cast_div, div_pow]
  field_simp
  ring

theorem exists_dimension_total_budget (n : ℕ) (hn : 1 ≤ n) :
    ∃ m : ℕ, 1 ≤ m ∧
      100*(centerCount (c (delta n)) m : ℝ)/(horizontalWeight (b (delta n)) m : ℝ) < (epsilon n : ℝ)/8 ∧
      lcmConstant*(truncationFactor n : ℝ)*m/(verticalWeight (theta (delta n)) (b (delta n)) (c (delta n)) m : ℝ) < (epsilon n : ℝ)/8 ∧
      2*Real.log 2/(verticalWeight (theta (delta n)) (b (delta n)) (c (delta n)) m : ℝ) < (epsilon n : ℝ)/8 ∧
      2 < (Real.log 2/8)*(eta n : ℝ)^2*
        (((b (delta n)/a (delta n) : ℚ) : ℝ)^m/((m : ℝ)+1)) := by
  have hs := scalarConditions n hn
  have he : (0 : ℝ) < epsilon n := by exact_mod_cast hs.epsilon_pos
  have hη : (0 : ℝ) < eta n := by exact_mod_cast hs.eta_pos
  have hl : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  obtain ⟨m, hm, hc, har, hv, hcol⟩ := exists_dimension n hn ((epsilon n : ℝ)/800)
    (lcmConstant*(truncationFactor n : ℝ))
    (16*Real.log 2/(epsilon n : ℝ)) (16/(Real.log 2*(eta n : ℝ)^2)) (by positivity) 1
  have hθ := hs.shape.theta_pos
  have hB := hθ.trans (hs.shape.theta_lt_a.trans hs.shape.a_lt_b)
  have hvpos : (0 : ℝ) < verticalWeight (theta (delta n)) (b (delta n)) (c (delta n)) m := by
    exact_mod_cast verticalWeight_pos hθ hB hs.shape.one_lt_c.le m
  have hc' : (centerCount (c (delta n)) m : ℝ)/(horizontalWeight (b (delta n)) m : ℝ) < (epsilon n : ℝ)/800 := by
    simpa only [Rat.cast_div, Rat.cast_natCast] using hc
  refine ⟨m, hm, ?_, ?_, ?_, ?_⟩
  · rw [mul_div_assoc]
    linarith
  · have heq : lcmConstant*(truncationFactor n : ℝ)*m/(verticalWeight (theta (delta n)) (b (delta n)) (c (delta n)) m : ℝ) =
        (lcmConstant*(truncationFactor n : ℝ))*((m : ℝ)/(verticalWeight (theta (delta n)) (b (delta n)) (c (delta n)) m : ℝ)) := by ring
    rw [heq]; linarith
  · apply (div_lt_iff₀ hvpos).mpr
    have hh := (div_lt_iff₀ he).mp hv
    nlinarith
  · have hp : 0 < Real.log 2*(eta n : ℝ)^2 := by positivity
    have hh := (div_lt_iff₀ hp).mp hcol
    nlinarith

/-- The dimension is fixed first. The coefficient of 1/W then determines W,
and only then are the separated denominators chosen from the bad family. -/
theorem exists_small_total_parameters (n : ℕ) (hn : 1 ≤ n) {x : ℝ}
    (hbad : UnboundedApproximations x (nu n : ℝ)) :
    ∃ (m : ℕ) (p : ℕ → ℤ) (q : ℕ → ℕ) (hq : ∀ i, 2 ≤ q i) (W : ℝ),
      1 ≤ m ∧ 0 < W ∧
      (∀ i, W ≤ (ceilLogWeight (q i) : ℝ)) ∧
      (∀ i, i < m → denominatorSeparationFactor n m (chosenComparisonConstant n m)*
        (∏ j : Fin i, (ceilLogWeight (q j) : ℝ)) < (ceilLogWeight (q i) : ℝ)) ∧
      (∀ i, |x-(p i : ℝ)/q i| ≤ (q i : ℝ)^(-(nu n : ℝ))) ∧
      let w := chosenWeights n hn m (fun i => q i) (fun i => hq i)
      arithmeticError w (truncationFactor n) W+
        fixedAnalyticError w (nu n : ℝ) (truncationFactor n : ℝ) W < (epsilon n : ℝ) ∧
      2 < collisionLimit w (a (delta n)) (eta n) := by
  have hs := scalarConditions n hn
  have he : (0 : ℝ) < epsilon n := by exact_mod_cast hs.epsilon_pos
  have he8 : (0 : ℝ) < (epsilon n : ℝ)/8 := by positivity
  have hθ : (0 : ℝ) < theta (delta n) := by exact_mod_cast hs.shape.theta_pos
  have hν : (0 : ℝ) < nu n := by unfold nu; positivity
  obtain ⟨m, hm, hc, har, hv, hcol⟩ := exists_dimension_total_budget n hn
  let K := centerCount (c (delta n)) m
  have hK : (1 : ℝ) ≤ K := by
    exact_mod_cast (centerCount_pos hs.shape.one_lt_c.le m)
  have hlogK : 0 ≤ Real.log (K : ℝ) := Real.log_nonneg hK
  have hlog4 : (0 : ℝ) < Real.log 4 := Real.log_pos (by norm_num)
  have hlog200 : 0 ≤ Real.log (200*(K : ℝ)) := Real.log_nonneg (by linarith)
  let S : ℝ := lcmConstant*m+(theta (delta n) : ℝ)+Real.log 4+Real.log (K : ℝ)+
    (nu n : ℝ)+Real.log (200*(K : ℝ))
  have hS : 0 < S := by
    dsimp [S]
    have hl := lcmConstant_pos
    positivity
  let W : ℝ := S/((epsilon n : ℝ)/8)+1
  have hW : 0 < W := by dsimp [W]; positivity
  have hsmall : S/W < (epsilon n : ℝ)/8 := by
    apply (div_lt_iff₀ hW).mpr
    dsimp [W]
    rw [mul_add, mul_div_cancel₀ _ he8.ne', mul_one]
    linarith
  obtain ⟨p, q, hq⟩ := exists_sequential_approximations hbad
    (fun i previous => max W (denominatorSeparationFactor n m (chosenComparisonConstant n m)*
      (∏ j : Fin i, (ceilLogWeight (previous j) : ℝ))))
  have hq2 : ∀ i, 2 ≤ q i := fun i => (hq i).1
  have hw : ∀ i, W ≤ (ceilLogWeight (q i) : ℝ) := by
    intro i
    exact ((le_max_left _ _).trans_lt (hq i).2.1).le.trans (ceilLogWeight_bounds _).1
  have hgrowth : ∀ i, i < m → denominatorSeparationFactor n m (chosenComparisonConstant n m)*
      (∏ j : Fin i, (ceilLogWeight (q j) : ℝ)) < (ceilLogWeight (q i) : ℝ) := by
    intro i _
    exact ((le_max_right _ _).trans_lt (hq i).2.1).trans_le (ceilLogWeight_bounds _).1
  refine ⟨m, p, q, hq2, W, hm, hW, hw, hgrowth, (fun i => (hq i).2.2), ?_, ?_⟩
  · let w := chosenWeights n hn m (fun i => q i) (fun i => hq2 i)
    have hb := totalError_le_uniform w (truncationFactor n) (nu n : ℝ) W hW (fun i => hw i)
    change arithmeticError w (truncationFactor n) W+fixedAnalyticError w (nu n : ℝ) (truncationFactor n : ℝ) W ≤
      lcmConstant*(truncationFactor n : ℝ)*m/(verticalWeight (theta (delta n)) (b (delta n)) (c (delta n)) m : ℝ)+
        100*(centerCount (c (delta n)) m : ℝ)/(horizontalWeight (b (delta n)) m : ℝ)+
        2*Real.log 2/(verticalWeight (theta (delta n)) (b (delta n)) (c (delta n)) m : ℝ)+
        (nu n : ℝ)/(truncationFactor n : ℝ)+S/W at hb
    have hfactor : (nu n : ℝ)/(truncationFactor n : ℝ) = (epsilon n : ℝ)/4 := by
      exact_mod_cast nu_div_factor n hn
    change arithmeticError w (truncationFactor n) W+fixedAnalyticError w (nu n : ℝ) (truncationFactor n : ℝ) W < _
    linarith
  · rw [chosen_collisionLimit_eq n hn]
    exact hcol

end
end LogTwo

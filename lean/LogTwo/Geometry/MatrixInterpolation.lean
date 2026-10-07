module

public import LogTwo.Geometry.MatrixSectionPolynomial
public import OAI.NumberTheory.PiExponent.Approximation.FrameEquationFamily

@[expose] public section

/-! The geometric interpolation theorem for the actual log-two matrix.
The certificates have all rows, rational columns and a nonzero rational
minor. The analytic upper estimate and final irrationality-exponent theorem
are not consequences of interpolation alone. -/
namespace LogTwo.Geometry.MatrixCompactification
open OAI PiExponent PiExponentApprox
open LogTwo.Interpolation LogTwo.Parameters LogTwo.Arithmetic
noncomputable section

/-- All sufficiently large multiples of the common radius give a full-row minor. -/
theorem logTwo_eventual_fullRowMinor
    (n : ℕ) (hn : 1 ≤ n) (m : ℕ) (q : ℕ → ℕ) (hq : ∀ i, 2 ≤ q i)
    (hgrowth : ∀ i, i < m →
      denominatorSeparationFactor n m (chosenComparisonConstant n m) *
        (∏ j : Fin i, (ceilLogWeight (q j) : ℝ)) < (ceilLogWeight (q i) : ℝ))
    (r : Fin m → ℚ) :
    let w := chosenWeights n hn m (fun i => q i) (fun i => hq i)
    ∀ (F : ℚ), 1 / w.theta < F →
      ∃ N : ℕ, ∀ k : ℕ, N ≤ k → Nonempty
        (FullRowMinor w (k * (scale w).radius) r (truncationOrders w F)) := by
  dsimp only
  intro F hF
  let w := chosenWeights n hn m (fun i => q i) (fun i => hq i)
  obtain ⟨N, hN⟩ := MatrixBlowup.logTwo_eventual_jetRestriction_surjective n hn m q hq hgrowth r F hF
  obtain ⟨M, hM⟩ := eventual_supportBound w
  obtain ⟨e⟩ := frame_exists w
  refine ⟨max N M, fun k hk => ?_⟩
  apply fullRowMinor_of_formal_packets w (k * (scale w).radius) r (truncationOrders w F)
    (fun i => (truncation_weight_strict w F hF i).le) (sectionPolynomial w k e)
  · intro s
    apply (FrameEquationFamily.hasWeightedDegreeLE_iff_supportBound _ _ _).mpr
    have hd := hM k (le_trans (le_max_right N M) hk) e s
    rw [cast_rationalColumnWeight] at hd
    simpa only [Rat.cast_mul, Rat.cast_natCast] using hd
  · exact formalPackets_surjective_of_jetRestriction w (fun j => 2^j.val)
      (fun j => pow_ne_zero j.val (by norm_num))
      (complex_centerY_injective.comp Fin.val_injective) (fun j i => (j.val : ℂ) * (r i : ℂ))
      F hF k e (hN k (le_trans (le_max_left N M) hk))

/-- The degree cutoff can exceed any prescribed rational lower threshold. -/
theorem logTwo_cofinally_fullRowMinor
    (n : ℕ) (hn : 1 ≤ n) (m : ℕ) (q : ℕ → ℕ) (hq : ∀ i, 2 ≤ q i)
    (hgrowth : ∀ i, i < m →
      denominatorSeparationFactor n m (chosenComparisonConstant n m) *
        (∏ j : Fin i, (ceilLogWeight (q j) : ℝ)) < (ceilLogWeight (q i) : ℝ))
    (r : Fin m → ℚ) :
    let w := chosenWeights n hn m (fun i => q i) (fun i => hq i)
    ∀ (F : ℚ), 1 / w.theta < F → ∀ B : ℚ, ∃ H : ℚ,
      B < H ∧ Nonempty (FullRowMinor w H r (truncationOrders w F)) := by
  dsimp only
  intro F hF B
  let w := chosenWeights n hn m (fun i => q i) (fun i => hq i)
  obtain ⟨N, hN⟩ := logTwo_eventual_fullRowMinor n hn m q hq hgrowth r F hF
  obtain ⟨k, hk⟩ := exists_nat_gt (max (N : ℚ) (B / (scale w).radius))
  have hNk : N ≤ k := by exact_mod_cast (le_of_lt (lt_of_le_of_lt (le_max_left _ _) hk))
  refine ⟨k * (scale w).radius, ?_, hN k hNk⟩
  have hR : (0 : ℚ) < (scale w).radius := by exact_mod_cast (scale w).radius_pos
  exact (div_lt_iff₀ hR).mp (lt_of_le_of_lt (le_max_right _ _) hk)

end
end LogTwo.Geometry.MatrixCompactification

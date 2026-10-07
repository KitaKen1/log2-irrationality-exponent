module
public import LogTwo.IrrationalityExponent
public import LogTwo.Main

@[expose] public section

namespace LogTwo

/-- The independently stated reciprocal-denominator definition agrees with
the comparison library's negative-power definition. This is a proved bridge,
not an alias used as the public definition. -/
theorem approximationExponents_eq_comparison (x : ℝ) :
    {μ : ℝ | 0 < μ ∧ Set.Infinite
      {r : ℚ | 1 < r.den ∧ 0 < |x - (r : ℝ)| ∧
        |x - (r : ℝ)| < 1 / (r.den : ℝ) ^ μ}} = OAI.PiExponent.ApproximationExponents x := by
  have hsets (μ : ℝ) :
      {r : ℚ | 1 < r.den ∧ 0 < |x - (r : ℝ)| ∧
        |x - (r : ℝ)| < 1 / (r.den : ℝ) ^ μ} =
        OAI.PiExponent.GoodRationalApproximations x μ := by
    ext r
    simp [OAI.PiExponent.GoodRationalApproximations, Nat.lt_iff_add_one_le,
      Real.rpow_neg (Nat.cast_nonneg r.den), one_div]
  ext μ
  change (0 < μ ∧ _ ) ↔ (0 < μ ∧ _)
  rw [hsets μ]

theorem log_two_approximationExponents_bddAbove :
    BddAbove ({μ : ℝ | 0 < μ ∧ Set.Infinite
      {r : ℚ | 1 < r.den ∧ 0 < |Real.log 2 - (r : ℝ)| ∧
        |Real.log 2 - (r : ℝ)| < 1 / (r.den : ℝ) ^ μ}}) := by
  rw [approximationExponents_eq_comparison]
  refine ⟨2, ?_⟩
  intro μ hμ
  by_contra h
  exact (OAI.PiExponent.finite_goodRationalApproximations_of_eventualLowerBound
    logTwo_eventualLowerBound (by linarith : 2 < μ)).not_infinite hμ.2

theorem two_mem_log_two_approximationExponents :
    (2 : ℝ) ∈ {μ : ℝ | 0 < μ ∧ Set.Infinite
      {r : ℚ | 1 < r.den ∧ 0 < |Real.log 2 - (r : ℝ)| ∧
        |Real.log 2 - (r : ℝ)| < 1 / (r.den : ℝ) ^ μ}} := by
  rw [approximationExponents_eq_comparison]
  exact OAI.PiExponent.two_mem_approximationExponents logTwo_irrational

/-- Final public target: the project's own irrationality exponent of log 2 is 2. -/
theorem irrationalityExponent_log_two : irrationalityExponent (Real.log 2) = 2 := by
  rw [irrationalityExponent, approximationExponents_eq_comparison]
  exact logTwo_exponent_eq_two

end LogTwo

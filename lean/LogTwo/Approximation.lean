module

public import LogTwo.Statement
public import LogTwo.ApproximationSelection
public import OAI.NumberTheory.PiExponent.Approximation.Exponent

@[expose] public section

namespace LogTwo

open OAI.PiExponent

/-- It suffices to rule out approximation at the countable exponents `2 + 1/n`. -/
theorem sequentialLowerBound_iff (x : ℝ) :
    SequentialLowerBound x ↔ EventualLowerBound x := by
  constructor
  · intro h ν hν
    obtain ⟨k, hk⟩ := exists_nat_one_div_lt (by linarith : (0 : ℝ) < ν - 2)
    obtain ⟨Q, hQ, hb⟩ := h (k + 1) (by omega)
    refine ⟨Q, hQ, ?_⟩
    intro p q hq
    have hbase : (1 : ℝ) ≤ q := by exact_mod_cast (show 1 ≤ q by omega)
    have hexp : -(ν : ℝ) ≤ -(2 + 1 / ((k + 1 : ℕ) : ℝ)) := by
      push_cast
      linarith
    exact (Real.rpow_le_rpow_of_exponent_le hbase hexp).trans (hb p q hq)
  · intro h n hn
    have hnreal : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
    apply h
    linarith [one_div_pos.mpr hnreal]

/-- Failure of the target bound supplies the bad approximation family used by
the parameter construction. The integer n is fixed before its denominators. -/
theorem exists_unbounded_of_not_sequential {x : ℝ} (h : ¬ SequentialLowerBound x) :
    ∃ n : ℕ, 1 ≤ n ∧ UnboundedApproximations x (2 + 1 / (n : ℝ)) := by
  classical
  unfold SequentialLowerBound at h
  push Not at h
  obtain ⟨n, hn, h⟩ := h
  refine ⟨n, hn, ?_⟩
  intro Q
  obtain ⟨p, q, hq, herr⟩ := h (max 2 Q) (le_max_left _ _)
  exact ⟨p, q, (le_max_right _ _).trans hq, herr.le⟩

/-- The bound quantifies over unreduced fractions, so it also excludes exact rational values. -/
theorem irrational_of_eventualLowerBound {x : ℝ} (h : EventualLowerBound x) :
    Irrational x := by
  rintro ⟨r, rfl⟩
  obtain ⟨Q, hQ, hb⟩ := h 3 (by norm_num)
  have hk : (0 : ℝ) < (Q + 1 : ℕ) := by positivity
  have hq : Q ≤ r.den * (Q + 1) := by nlinarith [r.pos]
  have hfrac : ((r.num * (Q + 1 : ℕ) : ℤ) : ℝ) /
      ((r.den * (Q + 1) : ℕ) : ℝ) = (r : ℝ) := by
    push_cast
    rw [mul_div_mul_right _ _ (by positivity : (Q : ℝ) + 1 ≠ 0)]
    exact Rat.cast_def r |>.symm
  have hh := hb (r.num * (Q + 1 : ℕ)) (r.den * (Q + 1)) hq
  rw [hfrac, sub_self, abs_zero] at hh
  have hp : (0 : ℝ) < (r.den * (Q + 1) : ℕ) := by
    exact_mod_cast (Nat.mul_pos r.pos (Nat.succ_pos Q))
  exact (not_le_of_gt (Real.rpow_pos_of_pos hp (-3))) hh

/-- Conditional endgame: the difficult analytic lower bound is an explicit argument. -/
theorem exponent_eq_two_of_sequentialLowerBound {x : ℝ}
    (h : SequentialLowerBound x) : irrationalityExponent x = 2 := by
  have hb := (sequentialLowerBound_iff x).mp h
  exact irrationalityExponent_eq_two_of_eventualLowerBound
    (irrational_of_eventualLowerBound hb) hb

theorem logTwoExponentTwo_of_sequentialLowerBound
    (h : SequentialLowerBound (Real.log 2)) : LogTwoExponentTwo :=
  exponent_eq_two_of_sequentialLowerBound h

end LogTwo

module

public import LogTwo.LogarithmicBound
public import Mathlib.NumberTheory.Chebyshev

@[expose] public section

/-!
A deliberately weaker absolute constant than the manuscript's 4*log 2:
Mathlib directly proves the sufficient linear bound with log 4 + 4. Keeping this
choice explicit avoids silently claiming the sharper numerical estimate.
-/
namespace LogTwo.Arithmetic

open LogTwo.Interpolation
noncomputable section

def lcmConstant : ℝ := Real.log 4 + 4

theorem lcmConstant_pos : 0 < lcmConstant := by
  have := Real.log_pos (by norm_num : (1 : ℝ) < 4)
  dsimp [lcmConstant]
  linarith

theorem lcmBelow_dvd_lcmUpto (T : ℕ) : lcmBelow T ∣ Nat.lcmUpto T := by
  apply Finset.lcm_dvd
  intro k hk
  apply Finset.dvd_lcm (f := id)
  exact Finset.mem_Icc.mpr ⟨(Finset.mem_Ico.mp hk).1, (Finset.mem_Ico.mp hk).2.le⟩

theorem log_lcmBelow_le (T : ℕ) :
    Real.log (lcmBelow T : ℝ) ≤ lcmConstant * T := by
  calc
    _ ≤ Real.log (Nat.lcmUpto T : ℝ) := by
      apply Real.log_le_log (by exact_mod_cast lcmBelow_pos T)
      exact_mod_cast Nat.le_of_dvd (Nat.lcmUpto_pos T) (lcmBelow_dvd_lcmUpto T)
    _ ≤ _ := by
      rw [← Chebyshev.psi_eq_log_lcmUpto]
      exact Chebyshev.psi_le_const_mul_self (by positivity)

theorem denominatorBudget_le {m : ℕ} (w : Weights m) (H : ℚ) (hH : 0 ≤ H)
    (T : Fin m → ℕ) :
    denominatorBudget w H T ≤
      (H : ℝ) * lcmConstant * ∑ i, (T i : ℝ) / (w.w i : ℝ) := by
  unfold denominatorBudget
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro i _
  have hf : (⌊H / w.w i⌋₊ : ℝ) ≤ (H : ℝ) / (w.w i : ℝ) := by
    exact_mod_cast Nat.floor_le (div_nonneg hH (w.w_pos i).le)
  calc
    _ ≤ (⌊H / w.w i⌋₊ : ℝ) * (lcmConstant * T i) :=
      mul_le_mul_of_nonneg_left (log_lcmBelow_le (T i)) (Nat.cast_nonneg _)
    _ ≤ ((H : ℝ) / (w.w i : ℝ)) * (lcmConstant * T i) :=
      mul_le_mul_of_nonneg_right hf (mul_nonneg lcmConstant_pos.le (Nat.cast_nonneg _))
    _ = _ := by ring

def truncationOrders {m : ℕ} (w : Weights m) (F : ℚ) : Fin m → ℕ :=
  fun i => ⌈F * w.w i / w.v0⌉₊

/-- The same truncation orders used in the arithmetic matrix also satisfy the
weight threshold needed for the formal logarithmic change of variables. -/
theorem truncation_weight_lower {m : ℕ} (w : Weights m) (F : ℚ)
    (hF : 1 / w.theta ≤ F) (i : Fin m) :
    w.w i / w.theta ≤ (truncationOrders w F i : ℚ) * w.v0 := by
  calc
    w.w i / w.theta = (1 / w.theta) * w.w i := by ring
    _ ≤ F * w.w i := mul_le_mul_of_nonneg_right hF (w.w_pos i).le
    _ ≤ (truncationOrders w F i : ℚ) * w.v0 :=
      (div_le_iff₀ w.v0_pos).mp (Nat.le_ceil _)

theorem sum_truncation_div_le {m : ℕ} (w : Weights m) (F : ℚ) (hF : 0 ≤ F) :
    (∑ i, (truncationOrders w F i : ℝ) / (w.w i : ℝ)) ≤
      (F : ℝ) * m / (w.v0 : ℝ) + ∑ i, 1 / (w.w i : ℝ) := by
  calc
    _ ≤ ∑ i, (((F : ℝ) * (w.w i : ℝ) / (w.v0 : ℝ) + 1) / (w.w i : ℝ)) := by
      apply Finset.sum_le_sum
      intro i _
      apply div_le_div_of_nonneg_right _ (by exact_mod_cast (w.w_pos i).le)
      have hh := (Nat.ceil_lt_add_one (div_nonneg (mul_nonneg hF (w.w_pos i).le) w.v0_pos.le)).le
      exact_mod_cast hh
    _ = ∑ i, ((F : ℝ) / (w.v0 : ℝ) + 1 / (w.w i : ℝ)) := by
      apply Finset.sum_congr rfl
      intro i _
      field_simp [(show (w.w i : ℝ) ≠ 0 by exact_mod_cast (w.w_pos i).ne'),
        (show (w.v0 : ℝ) ≠ 0 by exact_mod_cast w.v0_pos.ne')]
    _ = _ := by simp [Finset.sum_add_distrib]; ring

theorem truncation_denominatorBudget_le {m : ℕ} (w : Weights m)
    (H F : ℚ) (hH : 0 ≤ H) (hF : 0 ≤ F) :
    denominatorBudget w H (truncationOrders w F) ≤
      (H : ℝ) * (lcmConstant * (F : ℝ) * m / (w.v0 : ℝ) +
        lcmConstant * ∑ i, 1 / (w.w i : ℝ)) := by
  calc
    _ ≤ (H : ℝ) * lcmConstant * ∑ i, (truncationOrders w F i : ℝ) / (w.w i : ℝ) :=
      denominatorBudget_le w H hH _
    _ ≤ (H : ℝ) * lcmConstant * ((F : ℝ) * m / (w.v0 : ℝ) + ∑ i, 1 / (w.w i : ℝ)) :=
      mul_le_mul_of_nonneg_left (sum_truncation_div_le w F hF)
        (mul_nonneg (by exact_mod_cast hH) lcmConstant_pos.le)
    _ = _ := by ring

end
end LogTwo.Arithmetic

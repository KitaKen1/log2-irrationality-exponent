module

public import LogTwo.Arithmetic
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Tactic.Linarith

@[expose] public section

namespace LogTwo.Arithmetic

open LogTwo.Interpolation
noncomputable section

def rowLogSaving {m : ℕ} (q : Fin m → ℕ) (r : Row m) : ℝ :=
  ∑ i, (r.beta i : ℝ) * Real.log (q i : ℝ)

def columnLogCost {m : ℕ} (q T : Fin m → ℕ) (c : Column m) : ℝ :=
  ∑ i, (c.alpha i : ℝ) * (Real.log (q i : ℝ) + Real.log (lcmBelow (T i) : ℝ))

theorem log_rowMultiplier {m : ℕ} (q : Fin m → ℕ) (hq : ∀ i, q i ≠ 0) (r : Row m) :
    Real.log (rowMultiplier q r : ℝ) = -rowLogSaving q r := by
  simp only [rowMultiplier, Rat.cast_prod, Rat.cast_pow, Rat.cast_inv, Rat.cast_natCast]
  rw [Real.log_prod (fun i _ => pow_ne_zero _ (inv_ne_zero (by exact_mod_cast hq i)))]
  simp [Real.log_pow, Real.log_inv, rowLogSaving, Finset.sum_neg_distrib]

theorem log_columnMultiplier {m : ℕ} (q T : Fin m → ℕ)
    (hq : ∀ i, q i ≠ 0) (c : Column m) :
    Real.log (columnMultiplier q T c : ℝ) = columnLogCost q T c := by
  simp only [columnMultiplier, Rat.cast_prod, Rat.cast_pow, Rat.cast_mul, Rat.cast_natCast]
  rw [Real.log_prod (fun i _ => pow_ne_zero _ (mul_ne_zero
    (by exact_mod_cast hq i) (by exact_mod_cast lcmBelow_ne_zero (T i))))]
  apply Finset.sum_congr rfl
  intro i _
  rw [Real.log_pow, Real.log_mul (by exact_mod_cast hq i)
    (by exact_mod_cast lcmBelow_ne_zero (T i))]

/-- Exact logarithmic lower bound for the same minor used by interpolation. -/
theorem fullRowMinor_logarithmic_bound {m : ℕ} {w : Weights m} {H : ℚ}
    (p : Fin m → ℤ) (q T : Fin m → ℕ) (hq : ∀ i, q i ≠ 0)
    (minor : FullRowMinor w H (rationalPoint p q) T) :
    (∑ i, rowLogSaving q (minor.rows i)) - (∑ j, columnLogCost q T (minor.columns j)) ≤
      Real.log |(minor.matrix.det : ℝ)| := by
  let R : ℚ := ∏ i, rowMultiplier q (minor.rows i)
  let C : ℚ := ∏ j, columnMultiplier q T (minor.columns j)
  have hr : 0 < R := Finset.prod_pos (fun i _ => rowMultiplier_pos q hq _)
  have hc : 0 < C := Finset.prod_pos (fun j _ => columnMultiplier_pos q T hq _)
  have hr' : (0 : ℝ) < R := by exact_mod_cast hr
  have hc' : (0 : ℝ) < C := by exact_mod_cast hc
  have hd : (0 : ℝ) < |(minor.matrix.det : ℝ)| := by
    apply abs_pos.mpr
    exact_mod_cast minor.matrix_det_ne_zero
  have hb := fullRowMinor_arithmetic_bound p q T hq minor
  have hb' : (1 : ℝ) ≤ |((R * C : ℚ) : ℝ) * (minor.matrix.det : ℝ)| := by
    exact_mod_cast hb
  rw [Rat.cast_mul, abs_mul, abs_of_pos (mul_pos hr' hc')] at hb'
  have hh := Real.log_le_log (by norm_num : (0 : ℝ) < 1) hb'
  rw [Real.log_one, Real.log_mul (mul_pos hr' hc').ne' hd.ne',
    Real.log_mul hr'.ne' hc'.ne'] at hh
  have hR : Real.log (R : ℝ) = -∑ i, rowLogSaving q (minor.rows i) := by
    dsimp [R]
    rw [Rat.cast_prod, Real.log_prod (fun i _ => by
      exact_mod_cast rowMultiplier_ne_zero q hq (minor.rows i))]
    simp only [log_rowMultiplier q hq, Finset.sum_neg_distrib]
  have hC : Real.log (C : ℝ) = ∑ j, columnLogCost q T (minor.columns j) := by
    dsimp [C]
    rw [Rat.cast_prod, Real.log_prod (fun j _ => by
      exact_mod_cast columnMultiplier_ne_zero q T hq (minor.columns j))]
    simp only [log_columnMultiplier q T hq]
  rw [hR, hC] at hh
  linarith

/-- Each weighted column has a coordinate bound needed for the uniform denominator D_H. -/
theorem alpha_le_floor {m : ℕ} (w : Weights m) (H : ℚ) (c : Column m)
    (hc : AdmissibleColumn w H c) (i : Fin m) : c.alpha i ≤ ⌊H / w.w i⌋₊ := by
  have hsum : w.w i * c.alpha i ≤ ∑ k, w.w k * c.alpha k :=
    Finset.single_le_sum (fun k _ => mul_nonneg (w.w_pos k).le (Nat.cast_nonneg _))
      (Finset.mem_univ i)
  have hh : w.w i * c.alpha i ≤ H := by
    have hzero : 0 ≤ w.w0 * c.h := mul_nonneg w.w0_pos.le (Nat.cast_nonneg _)
    dsimp [AdmissibleColumn] at hc
    linarith
  have hdiv : (c.alpha i : ℚ) ≤ H / w.w i := by
    apply (le_div_iff₀ (w.w_pos i)).mpr
    simpa only [mul_comm] using hh
  exact (Nat.le_floor_iff ((Nat.cast_nonneg _).trans hdiv)).mpr hdiv

def denominatorBudget {m : ℕ} (w : Weights m) (H : ℚ) (T : Fin m → ℕ) : ℝ :=
  ∑ i, (⌊H / w.w i⌋₊ : ℝ) * Real.log (lcmBelow (T i) : ℝ)

def columnQCost {m : ℕ} (q : Fin m → ℕ) (c : Column m) : ℝ :=
  ∑ i, (c.alpha i : ℝ) * Real.log (q i : ℝ)

theorem columnLogCost_le {m : ℕ} (w : Weights m) (H : ℚ) (q T : Fin m → ℕ)
    (c : Column m) (hc : AdmissibleColumn w H c) :
    columnLogCost q T c ≤ columnQCost q c + denominatorBudget w H T := by
  unfold columnLogCost columnQCost denominatorBudget
  simp_rw [mul_add]
  rw [Finset.sum_add_distrib]
  apply add_le_add le_rfl
  apply Finset.sum_le_sum
  intro i _
  apply mul_le_mul_of_nonneg_right
  · exact_mod_cast alpha_le_floor w H c hc i
  · apply Real.log_nonneg
    exact_mod_cast (Nat.one_le_iff_ne_zero.mpr (lcmBelow_ne_zero (T i)))

/-- The manuscript's uniform denominator version, before bounding log lcm. -/
theorem fullRowMinor_uniform_log_bound {m : ℕ} {w : Weights m} {H : ℚ}
    (p : Fin m → ℤ) (q T : Fin m → ℕ) (hq : ∀ i, q i ≠ 0)
    (minor : FullRowMinor w H (rationalPoint p q) T) :
    (∑ i, rowLogSaving q (minor.rows i)) -
      (∑ j, columnQCost q (minor.columns j)) -
      (minor.size : ℝ) * denominatorBudget w H T ≤ Real.log |(minor.matrix.det : ℝ)| := by
  have hcost : (∑ j, columnLogCost q T (minor.columns j)) ≤
      (∑ j, columnQCost q (minor.columns j)) + (minor.size : ℝ) * denominatorBudget w H T := by
    calc
      _ ≤ ∑ j, (columnQCost q (minor.columns j) + denominatorBudget w H T) :=
        Finset.sum_le_sum (fun j _ => columnLogCost_le w H q T _ (minor.column_valid j))
      _ = _ := by simp [Finset.sum_add_distrib]
  have hbound := fullRowMinor_logarithmic_bound p q T hq minor
  linarith

end
end LogTwo.Arithmetic

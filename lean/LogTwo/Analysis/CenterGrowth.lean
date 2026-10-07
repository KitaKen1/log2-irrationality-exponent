module

public import LogTwo.DimensionChoice
public import LogTwo.Matrix
public import Mathlib.Analysis.SpecialFunctions.Log.Basic

@[expose] public section

/-! The extra growth from the centers Y=2^j. These estimates control individual
positive factors and Leibniz products. They do not transfer a determinant bound
from the Y=1 matrix: its cancellations still require a separate analytic proof. -/
namespace LogTwo.Analysis
open LogTwo.Interpolation LogTwo.Parameters Filter
open scoped Topology
noncomputable section

def centerGrowth {m : ℕ} (w : Weights m) : ℝ :=
  Real.log 2 * ((w.K : ℝ) / (w.w0 : ℝ))

theorem column_y_degree_le {m : ℕ} (w : Weights m) (H : ℚ) (col : Column m)
    (hc : AdmissibleColumn w H col) : w.w0 * col.h ≤ H := by
  have hs : 0 ≤ ∑ i, w.w i * col.alpha i :=
    Finset.sum_nonneg (fun i _ => mul_nonneg (w.w_pos i).le (Nat.cast_nonneg _))
  exact (le_add_of_nonneg_right hs).trans hc

theorem log_center_factor_le {m : ℕ} (w : Weights m) (H : ℚ)
    (j : ℕ) (hj : j < w.K) (col : Column m) (hc : AdmissibleColumn w H col) :
    Real.log ((2 : ℝ) ^ (j * col.h)) ≤ centerGrowth w * (H : ℝ) := by
  have hw : (0 : ℝ) < w.w0 := by exact_mod_cast w.w0_pos
  have hh : (col.h : ℝ) ≤ (H : ℝ) / (w.w0 : ℝ) := by
    apply (le_div_iff₀ hw).mpr
    have hb : (w.w0 : ℝ) * (col.h : ℝ) ≤ H := by
      exact_mod_cast column_y_degree_le w H col hc
    simpa only [mul_comm] using hb
  have hj' : (j : ℝ) ≤ w.K := by exact_mod_cast hj.le
  have hp := mul_le_mul hj' hh (Nat.cast_nonneg col.h) (Nat.cast_nonneg w.K)
  have hl : 0 ≤ Real.log (2 : ℝ) := Real.log_nonneg (by norm_num)
  rw [Real.log_pow, Nat.cast_mul]
  calc
    _ ≤ ((w.K : ℝ) * ((H : ℝ) / (w.w0 : ℝ))) * Real.log 2 :=
      mul_le_mul_of_nonneg_right hp hl
    _ = _ := by unfold centerGrowth; ring

/-- Every determinant permutation uses at most this logarithmic growth budget.
This is not an estimate for the cancellation in the determinant sum. -/
theorem leibniz_center_growth_le {m : ℕ} {w : Weights m} {H : ℚ}
    {r : Fin m → ℚ} {T : Fin m → ℕ} (minor : FullRowMinor w H r T)
    (σ : Equiv.Perm (Fin minor.size)) :
    (∑ i : Fin minor.size,
      Real.log ((2 : ℝ) ^ ((minor.rows i).j * (minor.columns (σ i)).h))) ≤
      (minor.size : ℝ) * centerGrowth w * (H : ℝ) := by
  calc
    _ ≤ ∑ _i : Fin minor.size, centerGrowth w * (H : ℝ) := by
      apply Finset.sum_le_sum
      intro i _
      exact log_center_factor_le w H (minor.rows i).j (minor.row_valid i).1
        (minor.columns (σ i)) (minor.column_valid (σ i))
    _ = _ := by simp [mul_assoc]

theorem center_growth_tendsto {B C : ℚ} (hB : 0 < B) (hC : 1 ≤ C)
    (hCB : C * B < 1) :
    Tendsto (fun m : ℕ => Real.log 2 *
      (((centerCount C m : ℚ) / horizontalWeight B m : ℚ) : ℝ)) atTop (𝓝 0) := by
  simpa using (count_over_horizontal_tendsto hB hC hCB).const_mul (Real.log 2)

end
end LogTwo.Analysis

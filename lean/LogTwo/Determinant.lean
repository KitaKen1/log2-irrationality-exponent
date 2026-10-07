module

public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
public import Mathlib.Tactic.Ring

@[expose] public section

namespace LogTwo.Determinant

open scoped BigOperators

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

def scale (A : Matrix ι ι ℚ) (r c : ι → ℚ) : Matrix ι ι ℚ :=
  fun i j => r i * A i j * c j

theorem det_scale (A : Matrix ι ι ℚ) (r c : ι → ℚ) :
    (scale A r c).det = ((∏ i, r i) * (∏ i, c i)) * A.det := by
  have heq : scale A r c = Matrix.diagonal r * A * Matrix.diagonal c := by
    ext i j
    simp [scale]
  rw [heq, Matrix.det_mul, Matrix.det_mul, Matrix.det_diagonal, Matrix.det_diagonal]
  ring

/-- Clearing denominators in the very same minor gives a nonzero integer determinant. -/
theorem scaled_integer_det_ne_zero (A : Matrix ι ι ℚ) (r c : ι → ℚ)
    (Z : Matrix ι ι ℤ) (hA : A.det ≠ 0)
    (hr : ∀ i, r i ≠ 0) (hc : ∀ i, c i ≠ 0)
    (hZ : ∀ i j, (Z i j : ℚ) = scale A r c i j) : Z.det ≠ 0 := by
  have heq : (Z.det : ℚ) = (scale A r c).det := by
    rw [Int.cast_det]
    congr 1
    ext i j
    exact hZ i j
  have hn : (Z.det : ℚ) ≠ 0 := by
    rw [heq, det_scale]
    exact mul_ne_zero (mul_ne_zero (Finset.prod_ne_zero_iff.mpr (by simpa using hr))
      (Finset.prod_ne_zero_iff.mpr (by simpa using hc))) hA
  exact fun hz => hn (by simp [hz])

/-- The generic arithmetic lower bound; the concrete denominator estimates are separate. -/
theorem scaled_integer_lower_bound (A : Matrix ι ι ℚ) (r c : ι → ℚ)
    (Z : Matrix ι ι ℤ) (hA : A.det ≠ 0)
    (hr : ∀ i, r i ≠ 0) (hc : ∀ i, c i ≠ 0)
    (hZ : ∀ i j, (Z i j : ℚ) = scale A r c i j) :
    (1 : ℚ) ≤ |((∏ i, r i) * (∏ i, c i)) * A.det| := by
  have hn := scaled_integer_det_ne_zero A r c Z hA hr hc hZ
  have hi : (1 : ℤ) ≤ |Z.det| := by
    have := abs_pos.mpr hn
    omega
  have heq : (Z.det : ℚ) = ((∏ i, r i) * (∏ i, c i)) * A.det := by
    rw [← det_scale, Int.cast_det]
    congr 1
    ext i j
    exact hZ i j
  rw [← heq]
  exact_mod_cast hi

/-- An explicit compatibility check: both bounds must refer to the identical scaled minor. -/
theorem contradiction_of_scaled_upper_bound (A : Matrix ι ι ℚ) (r c : ι → ℚ)
    (Z : Matrix ι ι ℤ) (hA : A.det ≠ 0)
    (hr : ∀ i, r i ≠ 0) (hc : ∀ i, c i ≠ 0)
    (hZ : ∀ i j, (Z i j : ℚ) = scale A r c i j)
    (hanalytic : |((∏ i, r i) * (∏ i, c i)) * A.det| < 1) : False :=
  (not_lt_of_ge (scaled_integer_lower_bound A r c Z hA hr hc hZ)) hanalytic

end LogTwo.Determinant

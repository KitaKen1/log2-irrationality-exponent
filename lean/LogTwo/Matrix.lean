module

public import Mathlib.Algebra.MvPolynomial.Basic
public import Mathlib.Algebra.MvPolynomial.Coeff
public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
public import Mathlib.Data.Finsupp.Fintype

@[expose] public section

/-!
The rational coefficient matrix from equation (3.2) of the supplied manuscript.
`FullRowMinor` records the missing interpolation output; no instance or existence
theorem is postulated. In particular it requires every admissible row.
-/
namespace LogTwo.Interpolation

open MvPolynomial
noncomputable section

structure Row (m : ℕ) where
  j : ℕ
  s : ℕ
  beta : Fin m → ℕ
  deriving DecidableEq

structure Column (m : ℕ) where
  h : ℕ
  alpha : Fin m → ℕ
  deriving DecidableEq

def truncatedLog {m : ℕ} (T : ℕ) : MvPolynomial (Option (Fin m)) ℚ :=
  ∑ k ∈ Finset.Ico 1 T, C ((-1 : ℚ) ^ (k + 1) / (k : ℚ)) * X none ^ k

def rowExponent {m : ℕ} (r : Row m) : Option (Fin m) →₀ ℕ :=
  Finsupp.equivFunOnFinite.symm (fun i => match i with
    | none => r.s
    | some k => r.beta k)

def columnExpansion {m : ℕ} (r : Fin m → ℚ) (T : Fin m → ℕ)
    (j : ℕ) (col : Column m) : MvPolynomial (Option (Fin m)) ℚ :=
  C ((2 : ℚ) ^ (j * col.h)) * (1 + X none) ^ col.h *
    ∏ i, (C ((j : ℚ) * r i) + truncatedLog (T i) + X (some i)) ^ col.alpha i

def coefficientMatrix {m : ℕ} (r : Fin m → ℚ) (T : Fin m → ℕ) :
    Matrix (Row m) (Column m) ℚ :=
  fun row col => (columnExpansion r T row.j col).coeff (rowExponent row)

def valueRow (m j : ℕ) : Row m := ⟨j, 0, fun _ => 0⟩
def oneColumn (m : ℕ) : Column m := ⟨0, fun _ => 0⟩
def yColumn (m : ℕ) : Column m := ⟨1, fun _ => 0⟩

@[simp] theorem valueRow_exponent (m j : ℕ) : rowExponent (valueRow m j) = 0 := by
  ext i
  cases i <;> rfl

theorem coefficient_oneColumn {m : ℕ} (r : Fin m → ℚ) (T : Fin m → ℕ) (j : ℕ) :
    coefficientMatrix r T (valueRow m j) (oneColumn m) = 1 := by
  simp only [coefficientMatrix, valueRow_exponent]
  simp [columnExpansion, oneColumn, valueRow]

theorem coefficient_yColumn {m : ℕ} (r : Fin m → ℚ) (T : Fin m → ℕ) (j : ℕ) :
    coefficientMatrix r T (valueRow m j) (yColumn m) = 2 ^ j := by
  have he : columnExpansion r T j (yColumn m) = C ((2 : ℚ) ^ j) * (1 + X none) := by
    simp [columnExpansion, yColumn]
  simp only [coefficientMatrix, valueRow_exponent]
  change (columnExpansion r T j (yColumn m)).coeff 0 = 2 ^ j
  rw [he]
  rw [MvPolynomial.coeff_C_mul]
  simp

structure Weights (m : ℕ) where
  K : ℕ
  w0 : ℚ
  v0 : ℚ
  w : Fin m → ℚ
  theta : ℚ
  w0_pos : 0 < w0
  v0_pos : 0 < v0
  w_pos : ∀ i, 0 < w i
  theta_pos : 0 < theta
  theta_lt_one : theta < 1

def AdmissibleRow {m : ℕ} (w : Weights m) (H : ℚ) (r : Row m) : Prop :=
  r.j < w.K ∧ w.v0 * r.s + (∑ i, w.w i * r.beta i) / w.theta < H

def AdmissibleColumn {m : ℕ} (w : Weights m) (H : ℚ) (c : Column m) : Prop :=
  w.w0 * c.h + ∑ i, w.w i * c.alpha i ≤ H

/-- A single square minor, with all the rows required by the manuscript. -/
structure FullRowMinor {m : ℕ} (w : Weights m) (H : ℚ)
    (r : Fin m → ℚ) (T : Fin m → ℕ) where
  size : ℕ
  rows : Fin size → Row m
  columns : Fin size → Column m
  rows_injective : Function.Injective rows
  columns_injective : Function.Injective columns
  row_valid : ∀ k, AdmissibleRow w H (rows k)
  all_rows : ∀ row, AdmissibleRow w H row → ∃ k, rows k = row
  column_valid : ∀ k, AdmissibleColumn w H (columns k)
  det_ne_zero : (Matrix.of (fun i j => coefficientMatrix r T (rows i) (columns j))).det ≠ 0

def FullRowMinor.matrix {m : ℕ} {w : Weights m} {H : ℚ}
    {r : Fin m → ℚ} {T : Fin m → ℕ} (minor : FullRowMinor w H r T) :
    Matrix (Fin minor.size) (Fin minor.size) ℚ :=
  fun i j => coefficientMatrix r T (minor.rows i) (minor.columns j)

theorem FullRowMinor.matrix_det_ne_zero {m : ℕ} {w : Weights m} {H : ℚ}
    {r : Fin m → ℚ} {T : Fin m → ℕ} (minor : FullRowMinor w H r T) :
    minor.matrix.det ≠ 0 := minor.det_ne_zero

end
end LogTwo.Interpolation

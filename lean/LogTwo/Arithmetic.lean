module

public import LogTwo.Rescale
public import LogTwo.LogDenominator
public import LogTwo.Determinant
public import Mathlib.Tactic.FieldSimp

@[expose] public section

/-!
Concrete denominator clearing for the matrix (3.2). The row multiplier retains
the factor q_i^(-beta_i), which is essential in the manuscript's arithmetic bound.
-/
namespace LogTwo.Arithmetic

open MvPolynomial LogTwo.Interpolation LogTwo.Polynomial
noncomputable section

def rationalPoint {m : ℕ} (p : Fin m → ℤ) (q : Fin m → ℕ) : Fin m → ℚ :=
  fun i => (p i : ℚ) / (q i : ℚ)

def variableScale {m : ℕ} (q : Fin m → ℕ) : Option (Fin m) → ℚ
  | none => 1
  | some i => (q i : ℚ)⁻¹

def rowMultiplier {m : ℕ} (q : Fin m → ℕ) (r : Row m) : ℚ :=
  ∏ i, ((q i : ℚ)⁻¹) ^ r.beta i

def columnMultiplier {m : ℕ} (q T : Fin m → ℕ) (c : Column m) : ℚ :=
  ∏ i, ((q i : ℚ) * (lcmBelow (T i) : ℚ)) ^ c.alpha i

theorem rescale_truncatedLog {m : ℕ} (q : Fin m → ℕ) (T : ℕ) :
    rescale (variableScale q) (truncatedLog T) = truncatedLog T := by
  simp [truncatedLog, map_sum, variableScale]

theorem coeff_rescale_row {m : ℕ} (q : Fin m → ℕ)
    (P : MvPolynomial (Option (Fin m)) ℚ) (r : Row m) :
    (rescale (variableScale q) P).coeff (rowExponent r) =
      P.coeff (rowExponent r) * rowMultiplier q r := by
  rw [coeff_rescale]
  simp [rowMultiplier, rowExponent, variableScale, Fintype.prod_option]

def integerFactor {m : ℕ} (p : ℤ) (q T j : ℕ) (i : Fin m) :
    MvPolynomial (Option (Fin m)) ℤ :=
  C ((lcmBelow T : ℤ) * (j : ℤ) * p) + C (q : ℤ) * integerLog T +
    C (lcmBelow T : ℤ) * X (some i)

theorem map_integerFactor {m : ℕ} (p : Fin m → ℤ) (q T : Fin m → ℕ)
    (hq : ∀ i, q i ≠ 0) (j : ℕ) (i : Fin m) :
    MvPolynomial.map (Int.castRingHom ℚ) (integerFactor (p i) (q i) (T i) j i) =
      C ((q i : ℚ) * (lcmBelow (T i) : ℚ)) *
        rescale (variableScale q)
          (C ((j : ℚ) * rationalPoint p q i) + truncatedLog (T i) + X (some i)) := by
  have hqi : (q i : ℚ) ≠ 0 := by exact_mod_cast hq i
  simp only [integerFactor, map_add, map_mul, MvPolynomial.map_C, MvPolynomial.map_X,
    map_integerLog, rescale_C, rescale_truncatedLog, rescale_X, variableScale]
  change C (lcmBelow (T i) : ℚ) * C (j : ℚ) * C (p i : ℚ) +
      C (q i : ℚ) * (C (lcmBelow (T i) : ℚ) * truncatedLog (T i)) +
      C (lcmBelow (T i) : ℚ) * X (some i) = _
  simp only [← map_mul, rationalPoint]
  have hconst : (q i : ℚ) * lcmBelow (T i) * ((j : ℚ) * ((p i : ℚ) / q i)) =
      (lcmBelow (T i) : ℚ) * j * p i := by field_simp
  have hvar : (q i : ℚ) * lcmBelow (T i) * (q i : ℚ)⁻¹ = lcmBelow (T i) := by
    field_simp
  simp only [mul_add, ← mul_assoc, ← map_mul, hconst, hvar]

def integerColumnExpansion {m : ℕ} (p : Fin m → ℤ) (q T : Fin m → ℕ)
    (j : ℕ) (col : Column m) : MvPolynomial (Option (Fin m)) ℤ :=
  C ((2 : ℤ) ^ (j * col.h)) * (1 + X none) ^ col.h *
    ∏ i, (integerFactor (p i) (q i) (T i) j i) ^ col.alpha i

theorem map_integerColumnExpansion {m : ℕ} (p : Fin m → ℤ) (q T : Fin m → ℕ)
    (hq : ∀ i, q i ≠ 0) (j : ℕ) (col : Column m) :
    MvPolynomial.map (Int.castRingHom ℚ) (integerColumnExpansion p q T j col) =
      C (columnMultiplier q T col) *
        rescale (variableScale q) (columnExpansion (rationalPoint p q) T j col) := by
  simp only [integerColumnExpansion, map_mul, map_pow, map_prod,
    map_integerFactor p q T hq, columnMultiplier, columnExpansion]
  simp only [map_mul, map_add, map_one,
    MvPolynomial.map_X, rescale_C, rescale_X, variableScale, map_ofNat, one_mul,
    mul_pow, Finset.prod_mul_distrib]
  ring

def integerMatrix {m : ℕ} (p : Fin m → ℤ) (q T : Fin m → ℕ) :
    Matrix (Row m) (Column m) ℤ :=
  fun row col => (integerColumnExpansion p q T row.j col).coeff (rowExponent row)

/-- Exact integer clearing, including the denominator saving from the row multi-index. -/
theorem integerMatrix_cast {m : ℕ} (p : Fin m → ℤ) (q T : Fin m → ℕ)
    (hq : ∀ i, q i ≠ 0) (row : Row m) (col : Column m) :
    (integerMatrix p q T row col : ℚ) =
      rowMultiplier q row * coefficientMatrix (rationalPoint p q) T row col *
        columnMultiplier q T col := by
  have he := congrArg (fun P : MvPolynomial (Option (Fin m)) ℚ => P.coeff (rowExponent row))
    (map_integerColumnExpansion p q T hq row.j col)
  rw [MvPolynomial.coeff_map, MvPolynomial.coeff_C_mul, coeff_rescale_row] at he
  change (integerMatrix p q T row col : ℚ) =
    columnMultiplier q T col *
      (coefficientMatrix (rationalPoint p q) T row col * rowMultiplier q row) at he
  rw [he]
  ring

theorem rowMultiplier_ne_zero {m : ℕ} (q : Fin m → ℕ) (hq : ∀ i, q i ≠ 0) (r : Row m) :
    rowMultiplier q r ≠ 0 := by
  apply Finset.prod_ne_zero_iff.mpr
  intro i _
  exact pow_ne_zero _ (inv_ne_zero (by exact_mod_cast hq i))

theorem columnMultiplier_ne_zero {m : ℕ} (q T : Fin m → ℕ)
    (hq : ∀ i, q i ≠ 0) (c : Column m) : columnMultiplier q T c ≠ 0 := by
  apply Finset.prod_ne_zero_iff.mpr
  intro i _
  apply pow_ne_zero
  exact mul_ne_zero (by exact_mod_cast hq i) (by exact_mod_cast lcmBelow_ne_zero (T i))

theorem rowMultiplier_pos {m : ℕ} (q : Fin m → ℕ) (hq : ∀ i, q i ≠ 0) (r : Row m) :
    0 < rowMultiplier q r := by
  apply Finset.prod_pos
  intro i _
  apply pow_pos
  apply inv_pos.mpr
  exact_mod_cast Nat.pos_of_ne_zero (hq i)

theorem columnMultiplier_pos {m : ℕ} (q T : Fin m → ℕ)
    (hq : ∀ i, q i ≠ 0) (c : Column m) : 0 < columnMultiplier q T c := by
  apply Finset.prod_pos
  intro i _
  apply pow_pos
  exact mul_pos (by exact_mod_cast Nat.pos_of_ne_zero (hq i))
    (by exact_mod_cast lcmBelow_pos (T i))

def integerMinor {m : ℕ} {w : Weights m} {H : ℚ}
    (p : Fin m → ℤ) (q T : Fin m → ℕ)
    (minor : FullRowMinor w H (rationalPoint p q) T) :
    Matrix (Fin minor.size) (Fin minor.size) ℤ :=
  fun i j => integerMatrix p q T (minor.rows i) (minor.columns j)

/-- Arithmetic lower bound for the actual full-row minor, with no integrality hypothesis left. -/
theorem fullRowMinor_arithmetic_bound {m : ℕ} {w : Weights m} {H : ℚ}
    (p : Fin m → ℤ) (q T : Fin m → ℕ) (hq : ∀ i, q i ≠ 0)
    (minor : FullRowMinor w H (rationalPoint p q) T) :
    (1 : ℚ) ≤ |((∏ i, rowMultiplier q (minor.rows i)) *
      (∏ j, columnMultiplier q T (minor.columns j))) * minor.matrix.det| := by
  apply LogTwo.Determinant.scaled_integer_lower_bound minor.matrix
    (fun i => rowMultiplier q (minor.rows i))
    (fun j => columnMultiplier q T (minor.columns j)) (integerMinor p q T minor)
    minor.matrix_det_ne_zero
  · intro i; exact rowMultiplier_ne_zero q hq _
  · intro j; exact columnMultiplier_ne_zero q T hq _
  · intro i j
    exact integerMatrix_cast p q T hq (minor.rows i) (minor.columns j)

end
end LogTwo.Arithmetic

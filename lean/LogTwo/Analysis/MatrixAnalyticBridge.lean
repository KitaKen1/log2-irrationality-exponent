/-
Modification notice for the LogTwo project.
Adapted from leanprover-community/mathlib4 (Apache-2.0), revision d13f23b723b8a846827a245b89c10fc7d3f11612.
Changes: Adapt the optionEquivLeft coefficient proof strategy to optionEquivRight.
See ../../../THIRD_PARTY_NOTICES.txt for provenance and the recorded changes.
-/

module

public import LogTwo.Matrix
public import OAI.NumberTheory.PiExponent.Approximation.InterpolationMatrix
public import Mathlib.Algebra.MvPolynomial.Equiv

@[expose] public section
namespace LogTwo.Analysis
open MvPolynomial
open OAI.PiExponent
noncomputable section

/-- Splitting off the distinguished variable preserves the double coefficient. -/
theorem optionEquivRight_monomial {R σ : Type*} [CommSemiring R]
    (d : Option σ →₀ ℕ) (r : R) :
    MvPolynomial.optionEquivRight R σ (monomial d r) =
      monomial d.some (Polynomial.monomial (d none) r) := by
  rw [MvPolynomial.optionEquivRight_apply, aeval_monomial, Finsupp.prod_option_index]
  · rw [MvPolynomial.monomial_eq, ← Polynomial.C_mul_X_pow_eq_monomial]
    simp only [MvPolynomial.algebraMap_apply, Polynomial.algebraMap_eq,
      Option.elim_none, Option.elim_some, map_mul, map_pow, mul_assoc]
  · simp
  · intros; rw [pow_add]

theorem optionEquivRight_coeff_coeff {R σ : Type*} [CommSemiring R]
    (d : Option σ →₀ ℕ) (P : MvPolynomial (Option σ) R) :
    ((MvPolynomial.optionEquivRight R σ P).coeff d.some).coeff (d none) =
      P.coeff d := by
  induction P using MvPolynomial.induction_on' generalizing d with
  | monomial e r =>
    rw [optionEquivRight_monomial]
    classical
    by_cases he : e = d
    · subst e
      simp [MvPolynomial.coeff_monomial]
    · by_cases hs : e.some = d.some
      · have hn : e none ≠ d none := by
          intro hn
          apply he
          ext i
          cases i with
          | none => exact hn
          | some i => exact DFunLike.congr_fun hs i
        simp [MvPolynomial.coeff_monomial, Polynomial.coeff_monomial, he, hs, hn]
      · simp [MvPolynomial.coeff_monomial, he, hs]
  | add P Q hP hQ => simp only [map_add, AddMonoidAlgebra.coeff_add, Finsupp.add_apply,
      Polynomial.coeff_add, hP, hQ]

def splitRationalPolynomial (m : ℕ) :
    MvPolynomial (Option (Fin m)) ℚ →+* MvPolynomial (Fin m) (Polynomial ℂ) :=
  (MvPolynomial.optionEquivRight ℂ (Fin m)).toRingHom.comp
    (MvPolynomial.map (algebraMap ℚ ℂ))

@[simp] theorem splitRationalPolynomial_C (m : ℕ) (r : ℚ) :
    splitRationalPolynomial m (C r) = C (Polynomial.C (r : ℂ)) := by
  simp [splitRationalPolynomial]

@[simp] theorem splitRationalPolynomial_X (m : ℕ) (i : Option (Fin m)) :
    splitRationalPolynomial m (X i) = i.elim (C Polynomial.X) X := by
  cases i <;> simp [splitRationalPolynomial]

theorem splitRationalPolynomial_truncatedLog (m T : ℕ) :
    splitRationalPolynomial m (Interpolation.truncatedLog T) =
      C (InterpolationMatrix.truncatedLog T) := by
  induction T with
  | zero => simp [Interpolation.truncatedLog, InterpolationMatrix.truncatedLog]
  | succ T ih =>
    by_cases hT : T = 0
    · subst T
      simp [Interpolation.truncatedLog, InterpolationMatrix.truncatedLog,
        PowerSeries.trunc_succ, PowerSeries.coeff_log]
    · have hs : Interpolation.truncatedLog (m := m) (T+1) =
          Interpolation.truncatedLog T +
          C ((-1 : ℚ)^(T+1) / T) * X none ^ T :=
        Finset.sum_Ico_succ_top (Nat.one_le_iff_ne_zero.mpr hT) _
      rw [hs, map_add, map_mul, map_pow, splitRationalPolynomial_C,
        splitRationalPolynomial_X, ih]
      simp [InterpolationMatrix.truncatedLog, PowerSeries.trunc_succ,
        PowerSeries.coeff_log, hT, ← Polynomial.C_mul_X_pow_eq_monomial]

theorem splitRationalPolynomial_columnExpansion {m : ℕ}
    (r : Fin m → ℚ) (T : Fin m → ℕ) (j : ℕ) (col : Interpolation.Column m) :
    splitRationalPolynomial m (Interpolation.columnExpansion r T j col) =
      C (Polynomial.C ((2 : ℂ)^(j*col.h))) *
        InterpolationMatrix.monomialImage (fun i => (r i : ℂ))
          (fun i => InterpolationMatrix.truncatedLog (T i)) j col.h col.alpha := by
  simp [Interpolation.columnExpansion, InterpolationMatrix.monomialImage,
    map_prod, splitRationalPolynomial_truncatedLog, map_add, map_pow, mul_assoc]

/-- The scalar 2^(j*h) relates the actual rational entries to the generic
translation matrix. It is retained before any determinant expansion. -/
theorem coefficientMatrix_eq_scaled_entry {m : ℕ}
    (r : Fin m → ℚ) (T : Fin m → ℕ)
    (row : Interpolation.Row m) (col : Interpolation.Column m) :
    (Interpolation.coefficientMatrix r T row col : ℂ) =
      (2 : ℂ)^(row.j*col.h) * InterpolationMatrix.entry
        (fun i => (r i : ℂ)) (fun i => InterpolationMatrix.truncatedLog (T i))
        row.j row.s row.beta col.h col.alpha := by
  have hc := optionEquivRight_coeff_coeff (Interpolation.rowExponent row)
    (MvPolynomial.map (algebraMap ℚ ℂ) (Interpolation.columnExpansion r T row.j col))
  have hsome : (Interpolation.rowExponent row).some =
      InterpolationMatrix.exponentVector row.beta := by ext i; rfl
  have hnone : Interpolation.rowExponent row none = row.s := rfl
  change ((splitRationalPolynomial m (Interpolation.columnExpansion r T row.j col)).coeff
    (Interpolation.rowExponent row).some).coeff (Interpolation.rowExponent row none) = _ at hc
  rw [hsome, hnone, splitRationalPolynomial_columnExpansion,
    MvPolynomial.coeff_C_mul, Polynomial.coeff_C_mul, MvPolynomial.coeff_map] at hc
  exact hc.symm

end
end LogTwo.Analysis

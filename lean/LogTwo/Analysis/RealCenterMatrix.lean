/-
Modification notice for the LogTwo project.
Adapted from openai/math (Apache-2.0), revision adc7f1241b42e322a6451854ab7e4b4c146bf78a.
Changes: Adapt analytic matrix-translation interfaces, preserving the factor 2^(j*h).
See ../../../THIRD_PARTY_NOTICES.txt for provenance and the recorded changes.
-/

module

public import LogTwo.Analysis.MatrixAnalyticBridge
public import LogTwo.Analysis.RealCenterRows

@[expose] public section
namespace LogTwo.Analysis
open OAI PiExponent MatrixTranslation RowTranslation AnalyticCollision PeriodAnalytic
open LogTwo.Interpolation
noncomputable section

/-- A column-independent scalar for each translation choice in an actual row. -/
def actualRowScalar {m : ℕ} (r : Fin m → ℚ) (T : Fin m → ℕ)
    (row : Row m) (S : Finset (Fin m →₀ ℕ))
    (t : RowChoices S (InterpolationMatrix.exponentVector row.beta) row.s) : ℂ :=
  rowScalar (fun i => (row.j : ℂ)*((r i : ℂ)-(Real.log 2 : ℂ)))
    (fun i => tail (T i) (PowerSeries.log ℂ))
    (InterpolationMatrix.exponentVector row.beta) t.1.1 t.2.1 t.2.2

def actualAnalyticRow {m : ℕ} (row : Row m) (S : Finset (Fin m →₀ ℕ))
    (t : RowChoices S (InterpolationMatrix.exponentVector row.beta) row.s)
    (col : Column m) : ℂ :=
  rowTest (row.s-t.2.2) (fun z => columnFunction col.h col.alpha t.1.1
    ((row.j : ℂ)*(Real.log 2 : ℂ)+Complex.log (1+z)))

/-- Equation (4.1) for the original rational matrix, including 2^(j*h). -/
theorem coefficientMatrix_eq_analytic_rows {m : ℕ}
    (r : Fin m → ℚ) (T : Fin m → ℕ) (row : Row m) (col : Column m)
    (S : Finset (Fin m →₀ ℕ))
    (hp : (periodMonomial row.j (Real.log 2 : ℂ) col.h col.alpha).support ⊆ S) :
    (coefficientMatrix r T row col : ℂ) =
      ∑ t : RowChoices S (InterpolationMatrix.exponentVector row.beta) row.s,
        actualRowScalar r T row S t * actualAnalyticRow row S t col := by
  rw [coefficientMatrix_eq_scaled_entry,
    matrix_entry_translation_choices _ _ _ _ _ _ _ _ S hp, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro t _
  change _ = _ * rowTest _ _
  rw [← scaled_periodMonomial_coeff_eq_rowTest]
  unfold actualRowScalar
  ring

/-- Multilinear expansion of the same selected rational minor used by the
arithmetic lower bound. No determinant estimate is transferred. -/
theorem actual_minor_analytic_expansion {m : ℕ} {w : Weights m} {H : ℚ}
    {r : Fin m → ℚ} {T : Fin m → ℕ} (minor : FullRowMinor w H r T)
    (S : Finset (Fin m →₀ ℕ))
    (hp : ∀ i c, (periodMonomial (minor.rows i).j (Real.log 2 : ℂ)
      (minor.columns c).h (minor.columns c).alpha).support ⊆ S) :
    Matrix.det (fun i c => (minor.matrix i c : ℂ)) =
      ∑ f : (∀ i, RowChoices S (InterpolationMatrix.exponentVector (minor.rows i).beta)
        (minor.rows i).s),
        (∏ i, actualRowScalar r T (minor.rows i) S (f i)) *
          Matrix.det (fun i c => actualAnalyticRow (minor.rows i) S (f i) (minor.columns c)) := by
  have he : (fun i c => (minor.matrix i c : ℂ)) =
      (fun i c => ∑ t : RowChoices S
        (InterpolationMatrix.exponentVector (minor.rows i).beta) (minor.rows i).s,
        actualRowScalar r T (minor.rows i) S t *
          actualAnalyticRow (minor.rows i) S t (minor.columns c)) := by
    funext i c
    exact coefficientMatrix_eq_analytic_rows r T (minor.rows i) (minor.columns c) S (hp i c)
  rw [he]
  exact det_dependent_row_sum _ _

/-- Every admissible column uses the same finite transverse index set. -/
theorem actual_minor_support_subset {m : ℕ} {w : Weights m} {H : ℚ}
    {r : Fin m → ℚ} {T : Fin m → ℕ} (minor : FullRowMinor w H r T)
    (i c : Fin minor.size) :
    (periodMonomial (minor.rows i).j (Real.log 2 : ℂ)
      (minor.columns c).h (minor.columns c).alpha).support ⊆
      transverseIndices (fun k => (w.w k : ℝ)) (H : ℝ) := by
  apply periodMonomial_support_subset
  · intro k; exact_mod_cast w.w_pos k
  · have hc := minor.column_valid c
    have hn : (0 : ℚ) ≤ w.w0 * (minor.columns c).h :=
      mul_nonneg w.w0_pos.le (Nat.cast_nonneg _)
    have hb : ∑ k, w.w k * (minor.columns c).alpha k ≤ H :=
      le_trans (le_add_of_nonneg_left hn) hc
    exact_mod_cast hb

/-- Full expansion with the support hypothesis discharged by admissibility. -/
theorem actual_minor_analytic_expansion_weighted {m : ℕ} {w : Weights m} {H : ℚ}
    {r : Fin m → ℚ} {T : Fin m → ℕ} (minor : FullRowMinor w H r T) :
    let S := transverseIndices (fun k => (w.w k : ℝ)) (H : ℝ)
    Matrix.det (fun i c => (minor.matrix i c : ℂ)) =
      ∑ f : (∀ i, RowChoices S (InterpolationMatrix.exponentVector (minor.rows i).beta)
        (minor.rows i).s),
        (∏ i, actualRowScalar r T (minor.rows i) S (f i)) *
          Matrix.det (fun i c => actualAnalyticRow (minor.rows i) S (f i) (minor.columns c)) := by
  exact actual_minor_analytic_expansion minor _ (actual_minor_support_subset minor)

/-- Taylor expansion for each selected row/column of the same rational minor. -/
theorem actual_minor_row_hasSum {m : ℕ} {w : Weights m} {H : ℚ}
    {r : Fin m → ℚ} {T : Fin m → ℕ} (minor : FullRowMinor w H r T)
    (hH : 0 ≤ H) {wstar : ℝ} (hws : 0 < wstar)
    (hw : ∀ k, wstar ≤ (w.w k : ℝ))
    (S : Finset (Fin m →₀ ℕ)) (i c : Fin minor.size)
    (t : RowChoices S (InterpolationMatrix.exponentVector (minor.rows i).beta)
      (minor.rows i).s) :
    HasSum (fun d => rowTest ((minor.rows i).s-t.2.2) (fun z =>
      ((((minor.rows i).j : ℂ)*(Real.log 2 : ℂ)+Complex.log (1+z))/(100*(w.K : ℂ)))^d) *
      normalizedTaylorCoeff (columnFunction (minor.columns c).h (minor.columns c).alpha t.1.1)
        (100*(w.K : ℝ)) d)
      (actualAnalyticRow (minor.rows i) S t (minor.columns c)) := by
  apply hasSum_logTwo_column_row _ _ _ (fun k => (w.w k : ℝ))
    (H := (H : ℝ)) (w0 := (w.w0 : ℝ))
    (by exact_mod_cast hH) (by exact_mod_cast w.w0_pos) hws hw
  · exact_mod_cast minor.column_valid c
  · exact (minor.row_valid i).1

end
end LogTwo.Analysis

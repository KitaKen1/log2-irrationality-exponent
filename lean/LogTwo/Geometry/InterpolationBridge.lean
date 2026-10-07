/-
Modification notice for the LogTwo project.
Adapted from openai/math (Apache-2.0), revision adc7f1241b42e322a6451854ab7e4b4c146bf78a.
Changes: Adapt packet surjectivity to varying Y-centers and add rational determinant descent.
See ../../../THIRD_PARTY_NOTICES.txt for provenance and the recorded changes.
-/

module

public import LogTwo.Geometry.WeightedIndices

@[expose] public section

/-! Conditional bridge from weighted polynomial interpolation to the actual
rational full-row minor. The interpolation surjectivity is an explicit input. -/
namespace LogTwo.Geometry
open OAI PiExponentApprox LogTwo.Interpolation
open PiExponent PiExponent.FormalMatrixBridge PiExponent.JetGeometry
noncomputable section

def indexedMatrix {m : ℕ} (w : Weights m) (H : ℚ)
    (r : Fin m → ℚ) (T : Fin m → ℕ) :
    Matrix (RowIndex w H) (ColumnIndex w H) ℂ :=
  fun a b => (coefficientMatrix r T (rowOfIndex a) (columnOfIndex b) : ℂ)

theorem monomial_eq_C_mul_frameMonomial {m : ℕ} (a : Fin (m+1) → ℕ) (z : ℂ) :
    MvPolynomial.monomial (InterpolationMatrix.exponentVector a) z =
      MvPolynomial.C z * frameMonomial (a 0) (fun i => a i.succ) := by
  rw [MvPolynomial.monomial_eq,
    Finsupp.prod_fintype _ _ (fun _ => pow_zero _), Fin.prod_univ_succ]
  rfl

theorem indexedMatrix_mulVec_eq_coeff {m : ℕ} (w : Weights m) (H : ℚ)
    (r : Fin m → ℚ) (T : Fin m → ℕ) (x : ColumnIndex w H → ℂ)
    (a : RowIndex w H) :
    (indexedMatrix w H r T).mulVec x a =
      MvPowerSeries.coeff (InterpolationMatrix.exponentVector a.2.val)
        (truncatedJetAt ((2 : ℂ)^a.1.val) (fun i => (a.1.val : ℂ)*(r i : ℂ)) T
          (polynomialOfCoefficients (realWeightedSimplex (columnWeight w) (H : ℝ)) x)) := by
  classical
  change (∑ b, (coefficientMatrix r T (rowOfIndex a) (columnOfIndex b) : ℂ) * x b) = _
  simp only [coefficientMatrix_eq_truncatedJetAt, rowExponent_index]
  change _ = MvPowerSeries.coeff _ (truncatedJetAt _ _ T
    (∑ b : ColumnIndex w H, MvPolynomial.monomial
      (InterpolationMatrix.exponentVector b.val) (x b)))
  simp only [map_sum, monomial_eq_C_mul_frameMonomial, map_mul]
  apply Finset.sum_congr rfl
  intro b hb
  simp [rowOfIndex, columnOfIndex, MvPowerSeries.algebraMap_apply,
    mul_comm]

/-- The degree constraint applies to one global polynomial for all centers. -/
theorem indexedMatrix_surjective_of_truncated_packets {m : ℕ} {α : Type*}
    (w : Weights m) (H : ℚ) (r : Fin m → ℚ) (T : Fin m → ℕ)
    (P : α → FramePolynomial m)
    (hdegree : ∀ a, HasWeightedDegreeLE (columnWeight w) (H : ℝ) (P a))
    (hpacket : Function.Surjective (fun a => fun j : Fin w.K =>
      rationalCoefficientPacket (jetWeight w) H
        (truncatedJetAt ((2 : ℂ)^j.val) (fun i => (j.val : ℂ)*(r i : ℂ)) T (P a)))) :
    Function.Surjective (indexedMatrix w H r T).mulVecLin := by
  classical
  intro y
  let e := rationalJetIndexEquiv (jetWeight w) (jetWeight_pos w) H
  let z : Fin w.K → RationalCoefficientPacket (R := ℂ) (jetWeight w) H :=
    fun j d => y (j, e d)
  obtain ⟨a, ha⟩ := hpacket z
  let x : ColumnIndex w H → ℂ :=
    fun c => (P a).coeff (InterpolationMatrix.exponentVector c.val)
  refine ⟨x, ?_⟩
  funext ρ
  change (indexedMatrix w H r T).mulVec x ρ = y ρ
  rw [indexedMatrix_mulVec_eq_coeff]
  change MvPowerSeries.coeff _ (truncatedJetAt _ _ T
    (polynomialOfCoefficients _ (fun c => (P a).coeff
      (InterpolationMatrix.exponentVector c.val)))) = _
  rw [polynomialOfCoefficients_of_weighted _ (columnWeight_pos w) _ (P a) (hdegree a)]
  have hh := congrFun (congrFun ha ρ.1) (e.symm ρ.2)
  change MvPowerSeries.coeff (e.symm ρ.2).val
    (truncatedJetAt _ _ T (P a)) = z ρ.1 (e.symm ρ.2) at hh
  simpa only [e, rationalJetIndexEquiv_symm_val, z, Equiv.apply_symm_apply] using hh

theorem indexedMatrix_surjective_of_formal_packets {m : ℕ} {α : Type*}
    (w : Weights m) (H : ℚ) (r : Fin m → ℚ) (T : Fin m → ℕ)
    (hT : ∀ i, w.w i / w.theta ≤ (T i : ℚ) * w.v0)
    (P : α → FramePolynomial m)
    (hdegree : ∀ a, HasWeightedDegreeLE (columnWeight w) (H : ℝ) (P a))
    (hpacket : Function.Surjective (fun a => fun j : Fin w.K =>
      rationalCoefficientPacket (jetWeight w) H
        (formalJetAt ((2 : ℂ)^j.val) (fun i => (j.val : ℂ)*(r i : ℂ)) (P a)))) :
    Function.Surjective (indexedMatrix w H r T).mulVecLin := by
  apply indexedMatrix_surjective_of_truncated_packets w H r T P hdegree
  exact (formalJetAt_surjective_iff_truncated (jetWeight w)
    (fun i => (jetWeight_pos w i).le) H T hT
    (fun j : Fin w.K => (2 : ℂ)^j.val)
    (fun j i => (j.val : ℂ)*(r i : ℂ)) P).mp hpacket

/-- Complex surjectivity selects rational columns with a nonzero rational determinant.
The certificate enumerates every admissible row, including when the row set is empty. -/
theorem fullRowMinor_of_indexedMatrix_surjective {m : ℕ}
    (w : Weights m) (H : ℚ) (r : Fin m → ℚ) (T : Fin m → ℕ)
    (hsurj : Function.Surjective (indexedMatrix w H r T).mulVecLin) :
    Nonempty (FullRowMinor w H r T) := by
  classical
  obtain ⟨select, hselect, hdet⟩ :=
    InterpolationMatrix.exists_full_row_minor_of_surjective (indexedMatrix w H r T) hsurj
  let e := (Fintype.equivFin (RowIndex w H)).symm
  refine ⟨{
    size := Fintype.card (RowIndex w H)
    rows := fun i => rowOfIndex (e i)
    columns := fun i => columnOfIndex (select (e i))
    rows_injective := (rowOfIndex_injective w H).comp e.injective
    columns_injective := (columnOfIndex_injective w H).comp (hselect.comp e.injective)
    row_valid := fun i => rowOfIndex_valid (e i)
    all_rows := ?_
    column_valid := fun i => columnOfIndex_valid (select (e i))
    det_ne_zero := ?_ }⟩
  · intro row hrow
    obtain ⟨a, ha⟩ := exists_rowIndex w H row hrow
    exact ⟨e.symm a, by simpa using ha⟩
  · have hd : (((indexedMatrix w H r T).submatrix id select).submatrix e e).det ≠ 0 := by
      rwa [Matrix.det_submatrix_equiv_self]
    intro hz
    apply hd
    let A : Matrix (Fin (Fintype.card (RowIndex w H))) _ ℚ :=
      fun i j => coefficientMatrix r T (rowOfIndex (e i)) (columnOfIndex (select (e j)))
    change (A.map (fun q : ℚ => (q : ℂ))).det = 0
    rw [← Rat.cast_det]
    have hA : A.det = 0 := hz
    rw [hA]
    norm_num

/-- The remaining geometric obligation is exactly the displayed packet surjectivity. -/
theorem fullRowMinor_of_formal_packets {m : ℕ} {α : Type*}
    (w : Weights m) (H : ℚ) (r : Fin m → ℚ) (T : Fin m → ℕ)
    (hT : ∀ i, w.w i / w.theta ≤ (T i : ℚ) * w.v0)
    (P : α → FramePolynomial m)
    (hdegree : ∀ a, HasWeightedDegreeLE (columnWeight w) (H : ℝ) (P a))
    (hpacket : Function.Surjective (fun a => fun j : Fin w.K =>
      rationalCoefficientPacket (jetWeight w) H
        (formalJetAt ((2 : ℂ)^j.val) (fun i => (j.val : ℂ)*(r i : ℂ)) (P a)))) :
    Nonempty (FullRowMinor w H r T) :=
  fullRowMinor_of_indexedMatrix_surjective w H r T
    (indexedMatrix_surjective_of_formal_packets w H r T hT P hdegree hpacket)

end
end LogTwo.Geometry

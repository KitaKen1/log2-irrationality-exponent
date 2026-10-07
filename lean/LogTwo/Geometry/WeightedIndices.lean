module

public import LogTwo.Geometry.JetMatrix
public import OAI.NumberTheory.PiExponent.Jets.FormalJetIndices

@[expose] public section

/-! Finite weighted indices for the manuscript's actual rational matrix. -/
namespace LogTwo.Geometry
open OAI PiExponentApprox LogTwo.Interpolation
open PiExponent
noncomputable section

def columnWeight {m : ℕ} (w : Weights m) : Fin (m+1) → ℝ :=
  InterpolationMatrix.columnWeights w.w0 (fun i => w.w i)

def jetWeight {m : ℕ} (w : Weights m) : Fin (m+1) → ℚ :=
  Fin.cases w.v0 (fun i => w.w i / w.theta)

theorem columnWeight_pos {m : ℕ} (w : Weights m) : ∀ i, 0 < columnWeight w i := by
  intro i
  refine Fin.cases ?_ (fun j => ?_) i
  · change (0 : ℝ) < w.w0
    exact_mod_cast w.w0_pos
  · change (0 : ℝ) < w.w j
    exact_mod_cast w.w_pos j

theorem jetWeight_pos {m : ℕ} (w : Weights m) : ∀ i, 0 < jetWeight w i :=
  fun i => Fin.cases w.v0_pos (fun j => div_pos (w.w_pos j) w.theta_pos) i

theorem cast_jetWeight {m : ℕ} (w : Weights m) :
    (fun i => (jetWeight w i : ℝ)) =
      InterpolationMatrix.rowWeights w.v0 w.theta (fun i => w.w i) := by
  funext i
  refine Fin.cases ?_ (fun j => ?_) i <;>
    simp [jetWeight, InterpolationMatrix.rowWeights]

abbrev ColumnIndex {m : ℕ} (w : Weights m) (H : ℚ) :=
  ↥(realWeightedSimplex (columnWeight w) (H : ℝ))

abbrev RowIndex {m : ℕ} (w : Weights m) (H : ℚ) :=
  Fin w.K × ↥(strictWeightedSimplex (fun i => (jetWeight w i : ℝ)) (H : ℝ))

def columnOfIndex {m : ℕ} {w : Weights m} {H : ℚ} (c : ColumnIndex w H) :
    LogTwo.Interpolation.Column m := ⟨c.val 0, fun i => c.val i.succ⟩

def rowOfIndex {m : ℕ} {w : Weights m} {H : ℚ} (r : RowIndex w H) :
    LogTwo.Interpolation.Row m := ⟨r.1.val, r.2.val 0, fun i => r.2.val i.succ⟩

theorem columnOfIndex_valid {m : ℕ} {w : Weights m} {H : ℚ} (c : ColumnIndex w H) :
    AdmissibleColumn w H (columnOfIndex c) := by
  have hc := (InterpolationMatrix.column_mem_iff
    (show (0 : ℝ) < w.w0 by exact_mod_cast w.w0_pos)
    (fun i => show (0 : ℝ) < w.w i by exact_mod_cast w.w_pos i) c.val).mp c.property
  unfold AdmissibleColumn columnOfIndex
  exact_mod_cast hc

theorem rowOfIndex_valid {m : ℕ} {w : Weights m} {H : ℚ} (r : RowIndex w H) :
    AdmissibleRow w H (rowOfIndex r) := by
  refine ⟨r.1.isLt, ?_⟩
  have hr : r.2.val ∈ strictWeightedSimplex
      (InterpolationMatrix.rowWeights w.v0 w.theta (fun i => w.w i)) (H : ℝ) := by
    simpa only [← cast_jetWeight] using r.2.property
  have hb := (InterpolationMatrix.row_mem_iff
    (show (0 : ℝ) < w.v0 by exact_mod_cast w.v0_pos)
    (show (0 : ℝ) < w.theta by exact_mod_cast w.theta_pos)
    (fun i => show (0 : ℝ) < w.w i by exact_mod_cast w.w_pos i) r.2.val).mp hr
  change w.v0 * (r.2.val 0 : ℚ) + (∑ i, w.w i * (r.2.val i.succ : ℚ)) / w.theta < H
  exact_mod_cast hb

theorem columnOfIndex_injective {m : ℕ} (w : Weights m) (H : ℚ) :
    Function.Injective (@columnOfIndex m w H) := by
  intro a b hab
  apply Subtype.ext
  funext i
  refine Fin.cases ?_ (fun j => ?_) i
  · exact congrArg LogTwo.Interpolation.Column.h hab
  · exact congrFun (congrArg LogTwo.Interpolation.Column.alpha hab) j

theorem rowOfIndex_injective {m : ℕ} (w : Weights m) (H : ℚ) :
    Function.Injective (@rowOfIndex m w H) := by
  intro a b hab
  apply Prod.ext
  · exact Fin.ext (congrArg LogTwo.Interpolation.Row.j hab)
  · apply Subtype.ext
    funext i
    refine Fin.cases ?_ (fun j => ?_) i
    · exact congrArg LogTwo.Interpolation.Row.s hab
    · exact congrFun (congrArg LogTwo.Interpolation.Row.beta hab) j

theorem exists_rowIndex {m : ℕ} (w : Weights m) (H : ℚ)
    (r : LogTwo.Interpolation.Row m) (hr : AdmissibleRow w H r) :
    ∃ a : RowIndex w H, rowOfIndex a = r := by
  let b : Fin (m+1) → ℕ := Fin.cases r.s r.beta
  have hb : b ∈ strictWeightedSimplex (fun i => (jetWeight w i : ℝ)) (H : ℝ) := by
    rw [cast_jetWeight]
    apply (InterpolationMatrix.row_mem_iff
      (by exact_mod_cast w.v0_pos) (by exact_mod_cast w.theta_pos)
      (fun i => by exact_mod_cast w.w_pos i) b).mpr
    change (w.v0 : ℝ) * r.s + (∑ i, (w.w i : ℝ) * r.beta i) / w.theta < H
    exact_mod_cast hr.2
  exact ⟨(⟨r.j, hr.1⟩, ⟨b, hb⟩), rfl⟩

theorem rowExponent_index {m : ℕ} {w : Weights m} {H : ℚ} (r : RowIndex w H) :
    (rowExponent (rowOfIndex r)).mapDomain (_root_.finSuccEquiv m).symm =
      InterpolationMatrix.exponentVector r.2.val := by
  ext i
  rw [Finsupp.mapDomain_equiv_apply]
  refine Fin.cases ?_ (fun j => ?_) i <;>
    simp [rowExponent, rowOfIndex, InterpolationMatrix.exponentVector]

end
end LogTwo.Geometry

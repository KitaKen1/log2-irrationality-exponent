/-
Modification notice for the LogTwo project.
Derived from openai/math (Apache-2.0), revision adc7f1241b42e322a6451854ab7e4b4c146bf78a.
Original source: lean/OAI/NumberTheory/PiExponent/Ampleness/CurveNormalizationPolarization.lean
Changes: Convert module/import declarations to the Lean 4.34 public module format.
See ../../../../../THIRD_PARTY_NOTICES.txt for provenance and the recorded changes.
-/

module

public import OAI.NumberTheory.PiExponent.Ampleness.FinitePullbackAmple
public import OAI.NumberTheory.PiExponent.Ampleness.ProjectiveO1Ample
public import OAI.NumberTheory.PiExponent.Cohomology.CurveNormalizationCohomology
public import OAI.NumberTheory.PiExponent.Geometry.CurveDegreeAdditivity
public import OAI.NumberTheory.PiExponent.Geometry.CurveNormalizationNonaffine
public import OAI.NumberTheory.PiExponent.Geometry.ProjectiveFinitePencil

@[expose] public section

namespace OAI

noncomputable section
namespace PiExponent.CurveNormalizationModel
open AlgebraicGeometry CategoryTheory
open PiExponentSeshadri.Geometry
variable {E : Type} [Field E] [Algebra ℂ E]
variable (f : E) (hf : Transcendental ℂ f)
variable [FiniteDimensional (IntermediateField.adjoin ℂ {f}) E]

def parameterCurvePolarization : LineBundle (parameterCurve f hf) :=
  (ProjectiveO1.lineBundle (R := ℂ) (σ := Bool)).pullback (parameterCurveProjection f hf)

theorem parameterCurvePolarization_ample : (parameterCurvePolarization f hf).IsAmple := by
  let : CompactSpace (ProjectiveO1.projectiveSpace ℂ Bool) :=
    QuasiCompact.compactSpace_of_compactSpace (polynomialProjectiveProjection ℂ Bool)
  exact LineBundle.IsAmple.pullback_finite _ ProjectiveO1.lineBundle_ample
    (parameterCurveProjection f hf)

theorem parameterCurve_finiteLineCohomology :
    CurveDegree.FiniteLineCohomology (parameterCurveStructureMap f hf) := by
  intro L n hn
  have h0 := ProjectivePencil.H0_finite_complex (parameterCurveProjection f hf)
    (parameterCurve_not_isAffine f hf) L
  have h1 := ProjectivePencil.H1_finite_complex (parameterCurveProjection f hf) L
  rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hn with rfl | rfl
  · exact h0
  · exact h1

theorem parameterCurve_lineCohomologyTwoZero :
    CurveDegree.LineCohomologyTwoZero (parameterCurve f hf) := by
  intro L
  apply subsingleton_of_forall_eq 0
  intro x
  exact parameterCurve_lineBundle_ext_zero f hf L 2 (by omega) x

theorem parameterCurve_tensor_euler_add (L M : LineBundle (parameterCurve f hf)) :
    eulerCharacteristic (parameterCurveStructureMap f hf) 1 (L.tensor M).sheaf -
      eulerCharacteristic (parameterCurveStructureMap f hf) 1 M.sheaf =
    eulerCharacteristic (parameterCurveStructureMap f hf) 1 L.sheaf -
      eulerCharacteristic (parameterCurveStructureMap f hf) 1
        (structureSheaf (parameterCurve f hf)) :=
  CurveDegree.tensor_euler_add _ (parameterCurve_dimension_le_one f hf)
    (parameterCurvePolarization f hf) (parameterCurvePolarization_ample f hf)
    (parameterCurve_finiteLineCohomology f hf) (parameterCurve_lineCohomologyTwoZero f hf) L M

theorem parameterCurve_power_euler (L : LineBundle (parameterCurve f hf)) (n : ℕ) :
    eulerCharacteristic (parameterCurveStructureMap f hf) 1 (L.pow n).sheaf -
      eulerCharacteristic (parameterCurveStructureMap f hf) 1
        (structureSheaf (parameterCurve f hf)) =
    (n : ℤ) * (eulerCharacteristic (parameterCurveStructureMap f hf) 1 L.sheaf -
      eulerCharacteristic (parameterCurveStructureMap f hf) 1
        (structureSheaf (parameterCurve f hf))) :=
  CurveDegree.power_euler _ (parameterCurve_dimension_le_one f hf)
    (parameterCurvePolarization f hf) (parameterCurvePolarization_ample f hf)
    (parameterCurve_finiteLineCohomology f hf) (parameterCurve_lineCohomologyTwoZero f hf) L n

end PiExponent.CurveNormalizationModel

end

end OAI

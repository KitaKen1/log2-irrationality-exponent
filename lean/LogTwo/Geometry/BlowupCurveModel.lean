/-
Modification notice for the LogTwo project.
Adapted from openai/math (Apache-2.0), revision adc7f1241b42e322a6451854ab7e4b4c146bf78a.
Changes: Adapt curve-model constructions to the varying-center blowup.
See ../../../THIRD_PARTY_NOTICES.txt for provenance and the recorded changes.
-/

module

public import LogTwo.Geometry.BlowupCurveCoordinates
public import LogTwo.Geometry.IntrinsicContactBound
public import OAI.NumberTheory.PiExponent.Geometry.CurveNormalizationMorphism

@[expose] public section

/-! Actual varying-center curve models, adapted from the corresponding
AdmissibleCurve*.lean wrappers in pinned openai/math (Apache-2.0).
Only scheme-generic APIs are imported; no fixed-Y contact bound is used. -/
namespace LogTwo.Geometry.MatrixBlowup.CurveModel
open OAI PiExponent AlgebraicGeometry CategoryTheory TopologicalSpace
noncomputable section
open LogTwo.Geometry.MatrixBlowup CurveNormalizationModel
variable {m K : ℕ} (w : LogTwo.Interpolation.Weights m)
variable (y : Fin K → ℂ) (a : Fin K → Fin m → ℂ) (T : Fin m → ℕ)

structure ModelData (C : NumericalAmpleness.IntegralCurve (space w y a T)) where
  E : Type
  [field : Field E]
  [algebra : Algebra ℂ E]
  [essFiniteType : Algebra.EssFiniteType ℂ E]
  coordinates : Fin (m+1) → E
  coordinates_generate : IntermediateField.adjoin ℂ (Set.range coordinates) = ⊤
  trdeg_one : Algebra.trdeg ℂ E = 1
  parameter : E
  parameter_transcendental : Transcendental ℂ parameter
  [parameterFinite : FiniteDimensional (IntermediateField.adjoin ℂ {parameter}) E]
  normalization : parameterCurve parameter parameter_transcendental ⟶ C.scheme
  [normalizationFinite : IsFinite normalization]
  normalization_over : normalization ≫ C.embedding ≫ structureMap w y a T =
    parameterCurveStructureMap parameter parameter_transcendental
  chart : C.scheme.Opens
  chart_nonempty : chart ≠ ⊥
  [chartIso : IsIso (normalization ∣_ chart)]
  generic_coordinates : parameterCurveGenericPoint parameter parameter_transcendental ≫
      (normalization ≫ C.embedding ≫ projection w y a T) =
    Spec.map (CommRingCat.ofHom (MvPolynomial.aeval coordinates).toRingHom) ≫
      MatrixCompactification.affineChart w

theorem existsModelData (C : NumericalAmpleness.IntegralCurve (space w y a T))
    (hn : ¬ ∃ t : MatrixCompactification.space w, Set.range (C.embedding ≫ projection w y a T) ⊆ {t})
    (hm : ∃ c : C.scheme, (C.embedding ≫ projection w y a T) c ∈ (MatrixCompactification.affineChart w).opensRange) :
    Nonempty (ModelData w y a T C) := by
  let := LogTwo.Geometry.MatrixBlowup.Coordinates.sourceAlgebra w y a T C
  have hp := LogTwo.Geometry.MatrixBlowup.Coordinates.field_properties w y a T C hn hm
  let := hp.1
  let z := LogTwo.Geometry.MatrixBlowup.Coordinates.coordinates w y a T C hn hm
  have hfinite := CurveParameterFinite.finite_over_every_parameter ℂ C.scheme.functionField hp.2.1
  obtain ⟨i,hi⟩ := LogTwo.Geometry.nonconstant_coordinates_of_trdeg_one z hp.2.2 hp.2.1
  let f := z i
  have hf : Transcendental ℂ f := hi
  let := hfinite f hf
  obtain ⟨g,hg,hgeneric,hgfinite,W,hW,hWiso⟩ :=
    CurveNormalizationMorphism.exists_intrinsic_normalization_morphism
      (C.embedding ≫ structureMap w y a T) C.dimension f hf
  let := hgfinite
  let := hWiso
  have hWne : W ≠ ⊥ := by
    intro he
    simp only [he, Opens.mem_bot] at hW
  have hc : parameterCurveGenericPoint f hf ≫ (g ≫ C.embedding ≫ projection w y a T) =
      Spec.map (CommRingCat.ofHom (MvPolynomial.aeval z).toRingHom) ≫
      MatrixCompactification.affineChart w := by
    rw [← Category.assoc, ← Category.assoc, hgeneric]
    exact (LogTwo.Geometry.MatrixBlowup.Coordinates.coordinates_generic_map w y a T C hn hm).symm
  exact ⟨{ E := C.scheme.functionField
           field := inferInstance
           algebra := inferInstance
           essFiniteType := hp.1
           coordinates := z
           coordinates_generate := hp.2.2
           trdeg_one := hp.2.1
           parameter := f
           parameter_transcendental := hf
           parameterFinite := inferInstance
           normalization := g
           normalizationFinite := hgfinite
           normalization_over := hg
           chart := W
           chart_nonempty := hWne
           chartIso := hWiso
           generic_coordinates := hc }⟩

end
end LogTwo.Geometry.MatrixBlowup.CurveModel

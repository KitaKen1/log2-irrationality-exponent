/-
Modification notice for the LogTwo project.
Adapted from openai/math (Apache-2.0), revision adc7f1241b42e322a6451854ab7e4b4c146bf78a.
Changes: Adapt curve-coordinate constructions to the varying-center blowup.
See ../../../THIRD_PARTY_NOTICES.txt for provenance and the recorded changes.
-/

module

public import LogTwo.Geometry.BlowupCurveImage
public import OAI.NumberTheory.PiExponent.Geometry.CurveImageAffineChart

@[expose] public section

/-! Actual varying-center curve models, adapted from the corresponding
AdmissibleCurve*.lean wrappers in pinned openai/math (Apache-2.0).
Only scheme-generic APIs are imported; no fixed-Y contact bound is used. -/
namespace LogTwo.Geometry.MatrixBlowup.Coordinates
open OAI PiExponent AlgebraicGeometry CategoryTheory TopologicalSpace
noncomputable section
open LogTwo.Geometry.MatrixBlowup
open CurveImageAffineCoordinates
variable {m K : ℕ} (w : LogTwo.Interpolation.Weights m)
variable (y : Fin K → ℂ) (a : Fin K → Fin m → ℂ) (T : Fin m → ℕ)
variable (C : NumericalAmpleness.IntegralCurve (space w y a T))
variable (hn : ¬ ∃ x : MatrixCompactification.space w, Set.range (C.embedding ≫ projection w y a T) ⊆ {x})

abbrev imageCurve := LogTwo.Geometry.MatrixBlowup.Image.imageCurve w y a T C hn
abbrev sourceStructure := C.embedding ≫ structureMap w y a T
abbrev imageStructure := (imageCurve w y a T C hn).embedding ≫ MatrixCompactification.structureMap w
@[instance_reducible] def sourceAlgebra : Algebra ℂ C.scheme.functionField :=
  IntegralAffineOpenDimension.functionFieldAlgebra (sourceStructure w y a T C)
@[instance_reducible] def imageAlgebra :
    Algebra ℂ (imageCurve w y a T C hn).scheme.functionField :=
  IntegralAffineOpenDimension.functionFieldAlgebra (imageStructure w y a T C hn)

def fieldEquiv :
    letI := imageAlgebra w y a T C hn
    letI := sourceAlgebra w y a T C
    (imageCurve w y a T C hn).scheme.functionField ≃ₐ[ℂ] C.scheme.functionField :=
  fieldAlgEquiv (imageStructure w y a T C hn) (sourceStructure w y a T C)
    (LogTwo.Geometry.MatrixBlowup.Image.functionFieldIso w y a T C hn) (by
      simpa only [imageStructure, sourceStructure, MatrixBlowup.structureMap, Category.assoc] using
        congrArg (fun f => f ≫ MatrixCompactification.structureMap w)
          (LogTwo.Geometry.MatrixBlowup.Image.functionFieldIso_generic w y a T C hn))

abbrev chart := affinePart (imageCurve w y a T C hn).embedding (MatrixCompactification.affineChart w)
abbrev chartPresentation := affinePresentation (imageCurve w y a T C hn).embedding (MatrixCompactification.affineChart w)

variable (hm : ∃ c : C.scheme, (C.embedding ≫ projection w y a T) c ∈ (MatrixCompactification.affineChart w).opensRange)

include hm in
theorem chart_nonempty : Nonempty (chart w y a T C hn).1 :=
  affinePart_nonempty _ _ (LogTwo.Geometry.MatrixBlowup.Image.image_meets_chart w y a T C hn hm)

def imageCoordinates : Fin (m+1) → (imageCurve w y a T C hn).scheme.functionField :=
  letI := chart_nonempty w y a T C hn hm
  CurveImageAffineCoordinates.coordinates (chart w y a T C hn) (chartPresentation w y a T C hn)

def coordinates : Fin (m+1) → C.scheme.functionField :=
  letI := imageAlgebra w y a T C hn
  letI := sourceAlgebra w y a T C
  fieldEquiv w y a T C hn ∘ imageCoordinates w y a T C hn hm

theorem field_properties :
    letI := sourceAlgebra w y a T C
    Algebra.EssFiniteType ℂ C.scheme.functionField ∧
      Algebra.trdeg ℂ C.scheme.functionField = 1 ∧
      IntermediateField.adjoin ℂ (Set.range (coordinates w y a T C hn hm)) = ⊤ := by
  let := sourceAlgebra w y a T C
  let := imageAlgebra w y a T C hn
  let := chart_nonempty w y a T C hn hm
  obtain ⟨ht,hd,hg⟩ := CurveImageAffineCoordinates.field_properties
    (imageStructure w y a T C hn) (imageCurve w y a T C hn).dimension
    (chart w y a T C hn) (chartPresentation w y a T C hn)
    (affinePresentation_over (MatrixCompactification.structureMap w) _ _ (MatrixCompactification.affineChart_over w))
  let := ht
  exact transport_field_properties (fieldEquiv w y a T C hn)
    (imageCoordinates w y a T C hn hm) hd hg

theorem coordinates_generic_map :
    letI := sourceAlgebra w y a T C
    Spec.map (CommRingCat.ofHom (MvPolynomial.aeval (R := ℂ) (coordinates w y a T C hn hm)).toRingHom) ≫
      MatrixCompactification.affineChart w = C.scheme.fromSpecStalk (genericPoint C.scheme) ≫
        C.embedding ≫ projection w y a T := by
  let := sourceAlgebra w y a T C
  let := imageAlgebra w y a T C hn
  let := chart_nonempty w y a T C hn hm
  have himage := CurveImageAffineCoordinates.coordinates_generic_map
    (imageStructure w y a T C hn) (chart w y a T C hn) (chartPresentation w y a T C hn)
    (affinePresentation_over (MatrixCompactification.structureMap w) _ _ (MatrixCompactification.affineChart_over w))
    (MatrixCompactification.affineChart w) (imageCurve w y a T C hn).embedding (affinePresentation_comp _ _)
  have he : (MvPolynomial.aeval (R := ℂ) (coordinates w y a T C hn hm)).toRingHom =
      (LogTwo.Geometry.MatrixBlowup.Image.functionFieldIso w y a T C hn).hom.hom.comp
        (MvPolynomial.aeval (R := ℂ) (imageCoordinates w y a T C hn hm)).toRingHom := by
    apply congrArg AlgHom.toRingHom
      (show MvPolynomial.aeval (R := ℂ) (coordinates w y a T C hn hm) =
        (fieldEquiv w y a T C hn).toAlgHom.comp
          (MvPolynomial.aeval (R := ℂ) (imageCoordinates w y a T C hn hm)) from ?_)
    apply MvPolynomial.algHom_ext
    intro i
    simp only [MvPolynomial.aeval_X, AlgHom.comp_apply]
    rfl
  rw [he, CommRingCat.ofHom_comp, CommRingCat.ofHom_hom, Spec.map_comp, Category.assoc]
  rw [show Spec.map (CommRingCat.ofHom
      (MvPolynomial.aeval (R := ℂ) (imageCoordinates w y a T C hn hm)).toRingHom) ≫ MatrixCompactification.affineChart w =
      (imageCurve w y a T C hn).scheme.fromSpecStalk (genericPoint (imageCurve w y a T C hn).scheme) ≫
        (imageCurve w y a T C hn).embedding from himage]
  exact LogTwo.Geometry.MatrixBlowup.Image.functionFieldIso_generic w y a T C hn

end
end LogTwo.Geometry.MatrixBlowup.Coordinates

/-
Modification notice for the LogTwo project.
Derived from openai/math (Apache-2.0), revision adc7f1241b42e322a6451854ab7e4b4c146bf78a.
Original source: lean/OAI/NumberTheory/PiExponent/Geometry/CurvePlaceCenterStalk.lean
Changes: Convert module/import declarations to the Lean 4.34 public module format.
See ../../../../../THIRD_PARTY_NOTICES.txt for provenance and the recorded changes.
-/

module

public import OAI.NumberTheory.PiExponent.Geometry.BirationalValuationStalk
public import OAI.NumberTheory.PiExponent.Geometry.CurveModelLocalOrder
public import OAI.NumberTheory.PiExponent.Geometry.CurvePlaceCenter

@[expose] public section

namespace OAI

noncomputable section
namespace PiExponent.CurvePlaceCenter
open CategoryTheory AlgebraicGeometry
open CurveZeroPole CurveValuationCenter CurveNormalizationModel CurveModelPlaces
universe u
variable {F E : Type u} [Field F] [CharZero F] [Field E] [Algebra F E]
variable (f : E) (hf : Transcendental F f)
variable [FiniteDimensional (IntermediateField.adjoin F {f}) E]
variable (p : NormalizedPlace F E)

instance centerMorphism_stalkMap_isIso :
    IsIso ((centerMorphism f hf p).stalkMap (IsLocalRing.closedPoint (PlaceValuationRing.ring p))) := by
  have hx : centerMorphism f hf p (IsLocalRing.closedPoint (PlaceValuationRing.ring p)) ≠
      genericPoint (parameterCurve f hf) := by
    rw [centerMorphism_closedPoint]
    exact placePoint_ne_genericPoint f hf p
  let := parameterCurve_stalkDVR f hf _ hx
  exact BirationalValuationStalk.stalkMap_isIso (centerMorphism f hf p)
    (parameterCurveFunctionFieldEquiv f hf) (centerMorphism_generic f hf p)

instance centerMorphism_stalkClosedPointTo_isIso :
    IsIso (Scheme.stalkClosedPointTo (centerMorphism f hf p)) := by
  unfold Scheme.stalkClosedPointTo
  infer_instance

def centerStalkIso :
    (parameterCurve f hf).presheaf.stalk (placePoint f hf p) ≅
      CommRingCat.of (PlaceValuationRing.ring p) :=
  (parameterCurve f hf).presheaf.stalkCongr
      (.of_eq (centerMorphism_closedPoint f hf p).symm) ≪≫
    asIso (Scheme.stalkClosedPointTo (centerMorphism f hf p))

@[reassoc]
theorem centerStalkIso_hom_eq :
    (centerStalkIso f hf p).hom =
      ((parameterCurve f hf).presheaf.stalkCongr
        (.of_eq (centerMorphism_closedPoint f hf p).symm)).hom ≫
      (centerMorphism f hf p).stalkMap (IsLocalRing.closedPoint (PlaceValuationRing.ring p)) ≫
      (stalkClosedPointIso (.of (PlaceValuationRing.ring p))).hom := rfl

omit [CharZero F] in
theorem centerMorphism_stalkClosedPointTo_field :
    (algebraMap (PlaceValuationRing.ring p) E).comp
        (Scheme.stalkClosedPointTo (centerMorphism f hf p)).hom =
      (parameterCurveFunctionFieldEquiv f hf).toRingHom.comp
        (algebraMap ((parameterCurve f hf).presheaf.stalk
          (centerMorphism f hf p (IsLocalRing.closedPoint (PlaceValuationRing.ring p))))
          (parameterCurve f hf).functionField) :=
  BirationalValuationStalk.stalkClosedPointTo_field_compatibility (centerMorphism f hf p)
    (parameterCurveFunctionFieldEquiv f hf) (centerMorphism_generic f hf p)

end PiExponent.CurvePlaceCenter

end

end OAI

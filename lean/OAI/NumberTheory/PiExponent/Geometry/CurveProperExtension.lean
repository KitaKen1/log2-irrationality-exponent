/-
Modification notice for the LogTwo project.
Derived from openai/math (Apache-2.0), revision adc7f1241b42e322a6451854ab7e4b4c146bf78a.
Original source: lean/OAI/NumberTheory/PiExponent/Geometry/CurveProperExtension.lean
Changes: Convert module/import declarations to the Lean 4.34 public module format.
See ../../../../../THIRD_PARTY_NOTICES.txt for provenance and the recorded changes.
-/

module

public import Mathlib.AlgebraicGeometry.ValuativeCriterion
public import OAI.NumberTheory.PiExponent.Geometry.CurveNormalizationLocalRing

@[expose] public section

namespace OAI

noncomputable section
universe u
namespace PiExponent.CurveProperExtension
open AlgebraicGeometry CategoryTheory

theorem fractionMap_fromSpecStalk
    (X : Scheme.{u}) [IsIntegral X] (x : X) :
    Spec.map (CommRingCat.ofHom (algebraMap (X.presheaf.stalk x) X.functionField)) ≫
      X.fromSpecStalk x = X.fromSpecStalk (genericPoint X) := by
  change Spec.map (X.presheaf.stalkSpecializes ((genericPoint_spec X).specializes trivial)) ≫
    X.fromSpecStalk x = _
  exact Scheme.SpecMap_stalkSpecializes_fromSpecStalk _

theorem exists_stalk_map
    {X Y S : Scheme.{u}} [IsIntegral X]
    (sX : X ⟶ S) (sY : Y ⟶ S) [IsProper sY]
    (hDVR : ∀ x : X, x ≠ genericPoint X → IsDiscreteValuationRing (X.presheaf.stalk x))
    (η : Spec X.functionField ⟶ Y)
    (hη : η ≫ sY = X.fromSpecStalk (genericPoint X) ≫ sX) (x : X) :
    ∃ φ : Spec (X.presheaf.stalk x) ⟶ Y,
      φ ≫ sY = X.fromSpecStalk x ≫ sX ∧
      Spec.map (CommRingCat.ofHom (algebraMap (X.presheaf.stalk x) X.functionField)) ≫ φ = η := by
  by_cases hx : x = genericPoint X
  · subst x
    refine ⟨η, hη, ?_⟩
    change Spec.map (X.presheaf.stalkSpecializes ((genericPoint_spec X).specializes trivial)) ≫ η = η
    simp
  · let := hDVR x hx
    have hval : ValuativeCriterion sY := by
      have h : IsProper sY := inferInstance
      rw [IsProper.eq_valuativeCriterion] at h
      exact h.1.1.1
    let sq : ValuativeCommSq sY :=
      { R := X.presheaf.stalk x
        commRing := inferInstanceAs (CommRing (X.presheaf.stalk x))
        domain := inferInstanceAs (IsDomain (X.presheaf.stalk x))
        valuationRing := inferInstanceAs (ValuationRing (X.presheaf.stalk x))
        K := X.functionField
        field := inferInstanceAs (Field X.functionField)
        algebra := inferInstanceAs (Algebra (X.presheaf.stalk x) X.functionField)
        isFractionRing := inferInstanceAs (IsFractionRing (X.presheaf.stalk x) X.functionField)
        i₁ := η
        i₂ := X.fromSpecStalk x ≫ sX
        commSq := ⟨by
          rw [hη]
          exact (congrArg (fun g => g ≫ sX) (fractionMap_fromSpecStalk X x)).symm.trans
            (Category.assoc _ _ _)⟩ }
    obtain ⟨φ, hφ, hbase⟩ := (hval.existence sq).exists_lift
    exact ⟨φ, hbase, hφ⟩

theorem parameterCurve_exists_stalk_map
    {F E : Type u} [Field F] [CharZero F] [Field E] [Algebra F E]
    (f : E) (hf : Transcendental F f)
    [FiniteDimensional (IntermediateField.adjoin F {f}) E]
    {Y S : Scheme.{u}}
    (sX : CurveNormalizationModel.parameterCurve f hf ⟶ S) (sY : Y ⟶ S) [IsProper sY]
    (η : Spec (CurveNormalizationModel.parameterCurve f hf).functionField ⟶ Y)
    (hη : η ≫ sY = (CurveNormalizationModel.parameterCurve f hf).fromSpecStalk
      (genericPoint (CurveNormalizationModel.parameterCurve f hf)) ≫ sX)
    (x : CurveNormalizationModel.parameterCurve f hf) :
    ∃ φ : Spec ((CurveNormalizationModel.parameterCurve f hf).presheaf.stalk x) ⟶ Y,
      φ ≫ sY = (CurveNormalizationModel.parameterCurve f hf).fromSpecStalk x ≫ sX ∧
      Spec.map (CommRingCat.ofHom (algebraMap
        ((CurveNormalizationModel.parameterCurve f hf).presheaf.stalk x)
        (CurveNormalizationModel.parameterCurve f hf).functionField)) ≫ φ = η :=
  exists_stalk_map sX sY (CurveNormalizationModel.parameterCurve_stalkDVR f hf) η hη x

end PiExponent.CurveProperExtension

end

end OAI

/-
Modification notice for the LogTwo project.
Derived from openai/math (Apache-2.0), revision adc7f1241b42e322a6451854ab7e4b4c146bf78a.
Original source: lean/OAI/NumberTheory/PiExponent/Geometry/CurveNormalizationNonaffine.lean
Changes: Convert module/import declarations to the Lean 4.34 public module format.
See ../../../../../THIRD_PARTY_NOTICES.txt for provenance and the recorded changes.
-/

module

public import Mathlib.AlgebraicGeometry.Artinian
public import OAI.NumberTheory.PiExponent.Geometry.CurveNormalizationDimension
public import OAI.NumberTheory.PiExponent.Geometry.CurveNormalizationProper

@[expose] public section

namespace OAI

noncomputable section
namespace PiExponent.CurveNormalizationModel
open AlgebraicGeometry CategoryTheory TopologicalSpace
open PiExponent.CurveZeroPole
universe u
variable {F E : Type u} [Field F] [Field E] [Algebra F E]
variable (f : E) (hf : Transcendental F f)
variable [CharZero F] [FiniteDimensional (IntermediateField.adjoin F {f}) E]

theorem parameterCurve_not_isAffine : ¬ IsAffine (parameterCurve f hf) := by
  intro haff
  let X := parameterCurve f hf
  let p := parameterCurveStructureMap f hf
  have : IsAffine X := haff
  have : IsFinite p := IsFinite.iff_isProper_and_isAffineHom.mpr
    ⟨inferInstance, inferInstance⟩
  let : Algebra F Γ(X,⊤) :=
    (p.appTop.hom.comp (Scheme.ΓSpecIso (CommRingCat.of F)).inv.hom).toAlgebra
  have : Module.Finite F Γ(X,⊤) :=
    p.finite_appTop.comp (RingHom.Finite.of_surjective
      (Scheme.ΓSpecIso (CommRingCat.of F)).inv.hom
      (Scheme.ΓSpecIso (CommRingCat.of F)).symm.commRingCatIsoToRingEquiv.surjective)
  have : IsArtinianRing Γ(X,⊤) := IsArtinianRing.of_finite F Γ(X,⊤)
  have : IsLocallyArtinian (Spec Γ(X,⊤)) :=
    Scheme.isLocallyArtinianScheme_Spec.mpr inferInstance
  have : T1Space (Spec Γ(X,⊤)) := inferInstance
  have : T1Space X := X.isoSpec.hom.isEmbedding.t1Space
  exact (parameterCurve_isClosed_iff_ne_generic f hf
    (genericPoint (parameterCurve f hf))).mp isClosed_singleton rfl

end PiExponent.CurveNormalizationModel

end

end OAI

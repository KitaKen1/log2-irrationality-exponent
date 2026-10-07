/-
Modification notice for the LogTwo project.
Derived from openai/math (Apache-2.0), revision adc7f1241b42e322a6451854ab7e4b4c146bf78a.
Original source: lean/OAI/NumberTheory/PiExponent/Geometry/CurveNormalizationLocalRing.lean
Changes: Convert module/import declarations to the Lean 4.34 public module format.
See ../../../../../THIRD_PARTY_NOTICES.txt for provenance and the recorded changes.
-/

module

public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import OAI.NumberTheory.PiExponent.Geometry.CurveNormalizationModel

@[expose] public section

namespace OAI

noncomputable section

namespace PiExponent.CurveNormalizationModel
open scoped Polynomial
open AlgebraicGeometry CategoryTheory
open PiExponent.CurveZeroPole

universe u
variable {F E : Type u} [Field F] [Field E] [Algebra F E]
variable (f : E) (hf : Transcendental F f)

def parameterChartProjection : Spec (.of (parameterChart f hf)) ⟶ Spec (.of F[X]) :=
  letI := parameterPolynomialAlgebra f hf
  Spec.map (CommRingCat.ofHom (algebraMap F[X] (parameterChart f hf)))

instance parameterChartProjection_isFinite [CharZero F]
    [FiniteDimensional (IntermediateField.adjoin F {f}) E] :
    IsFinite (parameterChartProjection f hf) := by
  let := parameterAlgebra f hf
  let := parameterPolynomialAlgebra f hf
  let := parameter_scalarTower f hf
  let := parameter_finite f hf
  rw [parameterChartProjection, IsFinite.SpecMap_iff]
  change (algebraMap F[X] (parameterChart f hf)).Finite
  rw [RingHom.finite_algebraMap]
  infer_instance

theorem parameterChart_localDVR [CharZero F]
    [FiniteDimensional (IntermediateField.adjoin F {f}) E]
    (q : PrimeSpectrum (parameterChart f hf)) (hq : q.asIdeal ≠ ⊥) :
    IsDiscreteValuationRing (Localization.AtPrime q.asIdeal) := by
  let := parameterAlgebra f hf
  let := parameterPolynomialAlgebra f hf
  let := parameter_scalarTower f hf
  let := parameter_finite f hf
  exact IsLocalization.AtPrime.isDiscreteValuationRing_of_dedekind_domain
    (parameterChart f hf) hq (Localization.AtPrime q.asIdeal)

theorem zeroChart_stalkDVR [CharZero F]
    [FiniteDimensional (IntermediateField.adjoin F {f}) E]
    (q : PrimeSpectrum (parameterChart f hf)) (hq : q.asIdeal ≠ ⊥) :
    IsDiscreteValuationRing
      ((parameterCurve f hf).presheaf.stalk (zeroChartInclusion f hf q)) := by
  let := parameterChart_localDVR f hf q hq
  exact IsDiscreteValuationRing.RingEquivClass.isDiscreteValuationRing
    (zeroChartStalkIso f hf q).commRingCatIsoToRingEquiv.symm

theorem infinityChart_stalkDVR [CharZero F]
    [FiniteDimensional (IntermediateField.adjoin F {f}) E]
    (q : PrimeSpectrum (parameterChart f⁻¹ (transcendental_inverse f hf)))
    (hq : q.asIdeal ≠ ⊥) :
    IsDiscreteValuationRing
      ((parameterCurve f hf).presheaf.stalk (infinityChartInclusion f hf q)) := by
  let : FiniteDimensional (IntermediateField.adjoin F {f⁻¹}) E :=
    (adjoin_inverse_eq (F := F) f).symm ▸ inferInstance
  let := parameterChart_localDVR f⁻¹ (transcendental_inverse f hf) q hq
  exact IsDiscreteValuationRing.RingEquivClass.isDiscreteValuationRing
    (infinityChartStalkIso f hf q).commRingCatIsoToRingEquiv.symm

theorem parameterCurve_stalkDVR [CharZero F]
    [FiniteDimensional (IntermediateField.adjoin F {f}) E]
    (x : parameterCurve f hf) (hx : x ≠ genericPoint (parameterCurve f hf)) :
    IsDiscreteValuationRing ((parameterCurve f hf).presheaf.stalk x) := by
  rcases parameterCurve_twoChartCover f hf x with ⟨q, rfl⟩ | ⟨q, rfl⟩
  · apply zeroChart_stalkDVR f hf q
    intro hq
    have heq : q = genericPoint (Spec (.of (parameterChart f hf))) := by
      rw [genericPoint_eq_bot_of_affine]
      exact PrimeSpectrum.ext hq
    apply hx
    rw [heq]
    exact genericPoint_eq_of_isOpenImmersion (zeroChartInclusion f hf)
  · apply infinityChart_stalkDVR f hf q
    intro hq
    have heq : q = genericPoint
        (Spec (.of (parameterChart f⁻¹ (transcendental_inverse f hf)))) := by
      rw [genericPoint_eq_bot_of_affine]
      exact PrimeSpectrum.ext hq
    apply hx
    rw [heq]
    exact genericPoint_eq_of_isOpenImmersion (infinityChartInclusion f hf)

theorem parameterCurve_stalkIntegrallyClosed [CharZero F]
    [FiniteDimensional (IntermediateField.adjoin F {f}) E]
    (x : parameterCurve f hf) :
    IsIntegrallyClosed ((parameterCurve f hf).presheaf.stalk x) := by
  by_cases hx : x = genericPoint (parameterCurve f hf)
  · subst x
    change IsIntegrallyClosed (parameterCurve f hf).functionField
    infer_instance
  · let := parameterCurve_stalkDVR f hf x hx
    infer_instance

end PiExponent.CurveNormalizationModel

end

end OAI

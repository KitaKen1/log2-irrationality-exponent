/-
Modification notice for the LogTwo project.
Derived from openai/math (Apache-2.0), revision adc7f1241b42e322a6451854ab7e4b4c146bf78a.
Original source: lean/OAI/NumberTheory/PiExponent/Geometry/CurveModelFieldEmbedding.lean
Changes: Convert module/import declarations to the Lean 4.34 public module format.
See ../../../../../THIRD_PARTY_NOTICES.txt for provenance and the recorded changes.
-/

module

public import OAI.NumberTheory.PiExponent.Geometry.CurveChartFunctionField
public import OAI.NumberTheory.PiExponent.Geometry.CurveNormalizationOverlap

@[expose] public section

namespace OAI

noncomputable section
namespace PiExponent.CurveNormalizationModel
open CategoryTheory AlgebraicGeometry
open scoped Polynomial nonZeroDivisors
open PiExponent.CurveZeroPole
universe u
variable {F E : Type u} [Field F] [Field E] [Algebra F E]
variable (f : E) (hf : Transcendental F f)
variable [FiniteDimensional (IntermediateField.adjoin F {f}) E]

abbrev parameterChartFractionRing : IsFractionRing (parameterChart f hf) E :=
  let := parameterAlgebra f hf
  let := parameterPolynomialAlgebra f hf
  let := parameter_scalarTower f hf
  let := parameter_finite f hf
  inferInstance

abbrev parameterChartLocalAlgebra (q : PrimeSpectrum (parameterChart f hf)) :
    Algebra (Localization.AtPrime q.asIdeal) E :=
  let := parameterChartFractionRing f hf
  IsLocalization.localizationAlgebraOfSubmonoidLe (Localization.AtPrime q.asIdeal) E
    q.asIdeal.primeCompl (nonZeroDivisors (parameterChart f hf))
    q.asIdeal.primeCompl_le_nonZeroDivisors

theorem parameterChartLocal_scalarTower (q : PrimeSpectrum (parameterChart f hf)) :
    letI := parameterChartLocalAlgebra f hf q
    IsScalarTower (parameterChart f hf) (Localization.AtPrime q.asIdeal) E := by
  let := parameterChartFractionRing f hf
  exact IsLocalization.localization_isScalarTower_of_submonoid_le
    (Localization.AtPrime q.asIdeal) E q.asIdeal.primeCompl
    (nonZeroDivisors (parameterChart f hf)) q.asIdeal.primeCompl_le_nonZeroDivisors

theorem parameterLaurentChartFractionRing : IsFractionRing (parameterLaurentChart f hf) E := by
  let := parameterChartFractionRing f hf
  let : Algebra (parameterChart f hf) (parameterLaurentChart f hf) :=
    (parameterChartOverlapHom f hf).toAlgebra
  have : IsScalarTower (parameterChart f hf) (parameterLaurentChart f hf) E :=
    IsScalarTower.of_algebraMap_eq' rfl
  exact isFractionRing_of_intermediate_domain (parameterChart f hf) E
    (parameterLaurentChart f hf) Subtype.val_injective

theorem parameterCurveFunctionFieldEquiv_eq_infinity :
    letI : FiniteDimensional (IntermediateField.adjoin F {f⁻¹}) E :=
      (adjoin_inverse_eq (F := F) f).symm ▸ inferInstance
    letI := parameterChartFractionRing f⁻¹ (transcendental_inverse f hf)
    (parameterCurveFunctionFieldEquiv f hf).toRingHom =
      affineChartFunctionFieldMap (parameterChart f⁻¹ (transcendental_inverse f hf)) E
        (infinityChartInclusion f hf) := by
  let : FiniteDimensional (IntermediateField.adjoin F {f⁻¹}) E :=
    (adjoin_inverse_eq (F := F) f).symm ▸ inferInstance
  let := parameterChartFractionRing f hf
  let := parameterChartFractionRing f⁻¹ (transcendental_inverse f hf)
  let := parameterLaurentChartFractionRing f hf
  let : Algebra (parameterChart f hf) (parameterLaurentChart f hf) :=
    (parameterChartOverlapHom f hf).toAlgebra
  let : Algebra (parameterChart f⁻¹ (transcendental_inverse f hf))
      (parameterLaurentChart f hf) :=
    ((reciprocalLaurentChartEquiv f hf).symm.toRingHom.comp
      (parameterChartOverlapHom f⁻¹ (transcendental_inverse f hf))).toAlgebra
  have : IsScalarTower (parameterChart f hf) (parameterLaurentChart f hf) E :=
    IsScalarTower.of_algebraMap_eq' rfl
  have : IsScalarTower (parameterChart f⁻¹ (transcendental_inverse f hf))
      (parameterLaurentChart f hf) E := IsScalarTower.of_algebraMap_eq' rfl
  have : IsOpenImmersion (Spec.map (CommRingCat.ofHom
      (algebraMap (parameterChart f hf) (parameterLaurentChart f hf)))) :=
    zeroOverlap_isOpenImmersion f hf
  have : IsOpenImmersion (Spec.map (CommRingCat.ofHom
      (algebraMap (parameterChart f⁻¹ (transcendental_inverse f hf))
        (parameterLaurentChart f hf)))) := infinityOverlap_isOpenImmersion f hf
  change affineChartFunctionFieldMap (parameterChart f hf) E (zeroChartInclusion f hf) = _
  exact affineChartFunctionFieldMap_eq_of_overlap (parameterChart f hf) E
    (parameterChart f⁻¹ (transcendental_inverse f hf)) (parameterLaurentChart f hf)
    (zeroChartInclusion f hf) (infinityChartInclusion f hf)
    (parameterCurve_overlap_compatibility f hf)

theorem zeroChartStalk_functionField_compatibility
    (q : PrimeSpectrum (parameterChart f hf))
    (a : (parameterCurve f hf).presheaf.stalk (zeroChartInclusion f hf q)) :
    letI := parameterChartLocalAlgebra f hf q
    parameterCurveFunctionFieldEquiv f hf
      (algebraMap ((parameterCurve f hf).presheaf.stalk (zeroChartInclusion f hf q))
        (parameterCurve f hf).functionField a) =
      algebraMap (Localization.AtPrime q.asIdeal) E ((zeroChartStalkIso f hf q).hom a) := by
  let := parameterChartFractionRing f hf
  let := parameterChartLocalAlgebra f hf q
  let := parameterChartLocal_scalarTower f hf q
  exact affineChartFunctionFieldMap_stalk (parameterChart f hf) E
    (zeroChartInclusion f hf) q a

theorem infinityChartStalk_functionField_compatibility
    (q : PrimeSpectrum (parameterChart f⁻¹ (transcendental_inverse f hf)))
    (a : (parameterCurve f hf).presheaf.stalk (infinityChartInclusion f hf q)) :
    letI : FiniteDimensional (IntermediateField.adjoin F {f⁻¹}) E :=
      (adjoin_inverse_eq (F := F) f).symm ▸ inferInstance
    letI := parameterChartLocalAlgebra f⁻¹ (transcendental_inverse f hf) q
    parameterCurveFunctionFieldEquiv f hf
      (algebraMap ((parameterCurve f hf).presheaf.stalk (infinityChartInclusion f hf q))
        (parameterCurve f hf).functionField a) =
      algebraMap (Localization.AtPrime q.asIdeal) E ((infinityChartStalkIso f hf q).hom a) := by
  let : FiniteDimensional (IntermediateField.adjoin F {f⁻¹}) E :=
    (adjoin_inverse_eq (F := F) f).symm ▸ inferInstance
  let := parameterChartFractionRing f⁻¹ (transcendental_inverse f hf)
  let := parameterChartLocalAlgebra f⁻¹ (transcendental_inverse f hf) q
  let := parameterChartLocal_scalarTower f⁻¹ (transcendental_inverse f hf) q
  change (parameterCurveFunctionFieldEquiv f hf).toRingHom _ = _
  rw [parameterCurveFunctionFieldEquiv_eq_infinity]
  exact affineChartFunctionFieldMap_stalk (parameterChart f⁻¹ (transcendental_inverse f hf)) E
    (infinityChartInclusion f hf) q a

end PiExponent.CurveNormalizationModel

end

end OAI

/-
Modification notice for the LogTwo project.
Derived from openai/math (Apache-2.0), revision adc7f1241b42e322a6451854ab7e4b4c146bf78a.
Original source: lean/OAI/NumberTheory/PiExponent/LocalAlgebra/QuotientLocalizedLength.lean
Changes: Convert module/import declarations to the Lean 4.34 public module format.
See ../../../../../THIRD_PARTY_NOTICES.txt for provenance and the recorded changes.
-/

module

public import Mathlib.RingTheory.Length
public import OAI.NumberTheory.PiExponent.LocalAlgebra.LocalizationQuotientParameters
public import OAI.NumberTheory.PiExponent.LocalAlgebra.QuotientLengthEquivalence

@[expose] public section

namespace OAI

noncomputable section
namespace PiExponentSiegel.W23

theorem intrinsic_length_eq_of_ringEquiv {R S : Type*} [CommRing R] [CommRing S]
    (e : R ≃+* S) : Module.length R R = Module.length S S := by
  let : RingHomSurjective e.toRingHom := ⟨e.surjective⟩
  let f : R →ₛₗ[e.toRingHom] S :=
    { toFun := e
      map_add' := e.map_add'
      map_smul' := by
        intro r x
        exact e.map_mul' r x }
  exact PiExponentJets.W22.length_eq_of_semilinear_bijective
    e.toRingHom f e.bijective

theorem quotient_module_length_eq_intrinsic {R : Type*} [CommRing R] (I : Ideal R) :
    Module.length R (R ⧸ I) = Module.length (R ⧸ I) (R ⧸ I) := by
  have hq : Function.Surjective (algebraMap R (R ⧸ I)) := Ideal.Quotient.mk_surjective
  exact Module.length_eq_of_surjective (M := R ⧸ I) hq

variable {A : Type*} [CommRing A] (I P : Ideal A) [P.IsPrime] (hI : I ≤ P)

theorem parameterLocalizationMap_surjective :
    Function.Surjective (parameterLocalizationMap I P hI) := by
  intro y
  obtain ⟨x, hx⟩ := (localizationQuotientParametersEquiv I P hI).surjective y
  obtain ⟨z, rfl⟩ := Ideal.Quotient.mk_surjective x
  exact ⟨z, hx⟩

theorem quotient_localized_length_eq :
    Module.length (Localization.AtPrime P)
      (Localization.AtPrime P ⧸ parameterLocalizedIdeal I P) =
    Module.length (Localization.AtPrime (quotientParameterPrime I P hI))
      (Localization.AtPrime (quotientParameterPrime I P hI)) := by
  calc
    Module.length (Localization.AtPrime P)
        (Localization.AtPrime P ⧸ parameterLocalizedIdeal I P) =
      Module.length (Localization.AtPrime P ⧸ parameterLocalizedIdeal I P)
        (Localization.AtPrime P ⧸ parameterLocalizedIdeal I P) :=
      quotient_module_length_eq_intrinsic (parameterLocalizedIdeal I P)
    _ = Module.length (Localization.AtPrime (quotientParameterPrime I P hI))
        (Localization.AtPrime (quotientParameterPrime I P hI)) :=
      intrinsic_length_eq_of_ringEquiv (localizationQuotientParametersEquiv I P hI)

theorem quotient_localized_length_eq_explicit :
    Module.length (Localization.AtPrime P)
      (Localization.AtPrime P ⧸ I.map (algebraMap A (Localization.AtPrime P))) =
    Module.length (Localization.AtPrime (quotientParameterPrime I P hI))
      (Localization.AtPrime (quotientParameterPrime I P hI)) :=
  quotient_localized_length_eq I P hI

end PiExponentSiegel.W23

end

end OAI

/-
Modification notice for the LogTwo project.
Derived from openai/math (Apache-2.0), revision adc7f1241b42e322a6451854ab7e4b4c146bf78a.
Original source: lean/OAI/NumberTheory/PiExponent/Geometry/CurveLocalMultiplicity.lean
Changes: Convert module/import declarations to the Lean 4.34 public module format.
See ../../../../../THIRD_PARTY_NOTICES.txt for provenance and the recorded changes.
-/

module

public import OAI.NumberTheory.PiExponent.Geometry.CurveComponentMultiplicity
public import OAI.NumberTheory.PiExponent.Geometry.CurveComponentStalks
public import OAI.NumberTheory.PiExponent.Geometry.FromSpecStalkLocalIso
public import OAI.NumberTheory.PiExponent.Geometry.SectionZeroStalk

@[expose] public section

namespace OAI

namespace PiExponent.CurveCycle
noncomputable section
open AlgebraicGeometry CategoryTheory TopologicalSpace

theorem componentMultiplicity_cast {X : Scheme.{0}} [IsLocallyNoetherian X]
    (C : irreducibleComponents X) :
    (componentMultiplicity X C : ℕ∞) =
      Module.length (X.presheaf.stalk (genericPoints.ofComponent C).val)
        (X.presheaf.stalk (genericPoints.ofComponent C).val) := by
  let x := (genericPoints.ofComponent C).val
  let : IsArtinianRing (X.presheaf.stalk x) :=
    generic_stalk_isArtinian x (genericPoints.ofComponent C).property
  exact ENat.natCast_toNat Module.length_ne_top

def localMinimalPrimeGenericStalkIso (X : Scheme.{0}) (x : X)
    (P : minimalPrimes (X.presheaf.stalk x)) :
    letI : P.val.IsPrime := P.property.1.1
    X.presheaf.stalk (genericPoints.ofComponent
      (stalkMinimalPrimesEquivComponentsThrough X x P).val).val ≅
      CommRingCat.of (Localization.AtPrime P.val) := by
  let y : Spec (X.presheaf.stalk x) := ⟨P.val,P.property.1.1⟩
  let e := (PiExponent.fromSpecStalkStalkIso X x y) ≪≫
    (Spec.stalkIso (X.presheaf.stalk x) y)
  simpa only [y,stalkMinimalPrimesEquivComponentsThrough_point] using e

theorem localMinimalPrime_length_eq_componentMultiplicity
    {X : Scheme.{0}} [IsLocallyNoetherian X] (x : X)
    (P : minimalPrimes (X.presheaf.stalk x)) :
    letI : P.val.IsPrime := P.property.1.1
    Module.length (Localization.AtPrime P.val) (Localization.AtPrime P.val) =
      (componentMultiplicity X (stalkMinimalPrimesEquivComponentsThrough X x P).val : ℕ∞) := by
  let : P.val.IsPrime := P.property.1.1
  rw [componentMultiplicity_cast]
  exact (SectionZeroStalk.intrinsic_length_eq_of_ringEquiv
    (localMinimalPrimeGenericStalkIso X x P).commRingCatIsoToRingEquiv).symm

end
end PiExponent.CurveCycle

end OAI

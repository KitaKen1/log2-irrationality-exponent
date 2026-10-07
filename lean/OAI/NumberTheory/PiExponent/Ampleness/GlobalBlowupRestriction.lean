/-
Modification notice for the LogTwo project.
Derived from openai/math (Apache-2.0), revision adc7f1241b42e322a6451854ab7e4b4c146bf78a.
Original source: lean/OAI/NumberTheory/PiExponent/Ampleness/GlobalBlowupRestriction.lean
Changes: Convert module/import declarations to the Lean 4.34 public module format.
See ../../../../../THIRD_PARTY_NOTICES.txt for provenance and the recorded changes.
-/

module

public import OAI.NumberTheory.PiExponent.Ampleness.GlobalBlowupGluing

@[expose] public section

namespace OAI

noncomputable section
namespace PiExponentSeshadri.BlowupGluing
open CategoryTheory AlgebraicGeometry PiExponentSeshadri.Geometry
variable {X : Scheme.{0}} (I : X.IdealSheafData)

def exceptionalLineBundle : LineBundle (scheme I) := (projection_invertible I).choose

def exceptionalInclusion : (exceptionalLineBundle I).sheaf ⟶ structureSheaf (scheme I) :=
  (projection_invertible I).choose_spec.choose

theorem exceptional_presents :
    PresentsPullbackIdeal I (projection I) (exceptionalLineBundle I) (exceptionalInclusion I) :=
  (projection_invertible I).choose_spec.choose_spec

def restrictionIso (U : X.Opens) :
    ((projection I) ⁻¹ᵁ U).toScheme ≅ scheme (I.comap U.ι) :=
  ((isBlowup I).morphismRestrict U).iso (isBlowup (I.comap U.ι))

@[reassoc (attr := simp)]
theorem restrictionIso_hom_projection (U : X.Opens) :
    (restrictionIso I U).hom ≫ projection (I.comap U.ι) = (projection I) ∣_ U :=
  ((isBlowup I).morphismRestrict U).iso_hom_comp (isBlowup (I.comap U.ι))

def affineRestrictionIso (U : X.affineOpens) :
    ((projection I) ⁻¹ᵁ U.1).toScheme ≅ AffineBlowup.scheme (I.comap U.1.ι) :=
  ((isBlowup I).morphismRestrict U.1).iso (AffineBlowup.isBlowup (I.comap U.1.ι))

@[reassoc (attr := simp)]
theorem affineRestrictionIso_hom_projection (U : X.affineOpens) :
    (affineRestrictionIso I U).hom ≫ AffineBlowup.projection (I.comap U.1.ι) =
      (projection I) ∣_ U.1 :=
  ((isBlowup I).morphismRestrict U.1).iso_hom_comp
    (AffineBlowup.isBlowup (I.comap U.1.ι))

end PiExponentSeshadri.BlowupGluing

end

end OAI

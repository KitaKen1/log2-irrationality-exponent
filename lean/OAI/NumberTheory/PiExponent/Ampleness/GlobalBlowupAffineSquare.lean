/-
Modification notice for the LogTwo project.
Derived from openai/math (Apache-2.0), revision adc7f1241b42e322a6451854ab7e4b4c146bf78a.
Original source: lean/OAI/NumberTheory/PiExponent/Ampleness/GlobalBlowupAffineSquare.lean
Changes: Convert module/import declarations to the Lean 4.34 public module format.
See ../../../../../THIRD_PARTY_NOTICES.txt for provenance and the recorded changes.
-/

module

public import OAI.NumberTheory.PiExponent.Ampleness.GlobalExceptionalComparison

@[expose] public section

namespace OAI

namespace PiExponentSeshadri.BlowupGluing
noncomputable section
open AlgebraicGeometry CategoryTheory TopologicalSpace
variable {X : Scheme.{0}} (I : X.IdealSheafData) (U : X.affineOpens)

def baseChart : Spec (CommRingCat.of Γ(U.1.toScheme, ⊤)) ⟶ X :=
  U.1.toScheme.isoSpec.inv ≫ U.1.ι

def totalChart : ReesGrading.affineBlowup (affineCenterIdeal I U) ⟶ scheme I :=
  (affineRestrictionIso I U).inv ≫ ((projection I) ⁻¹ᵁ U.1).ι

instance baseChart_isOpenImmersion : IsOpenImmersion (baseChart (X := X) U) := by
  dsimp [baseChart]
  infer_instance

instance totalChart_isOpenImmersion : IsOpenImmersion (totalChart I U) := by
  dsimp [totalChart]
  infer_instance

@[reassoc (attr := simp)] theorem totalChart_projection :
    totalChart I U ≫ projection I =
      ReesGrading.projection (affineCenterIdeal I U) ≫ baseChart U := by
  have he : (affineRestrictionIso I U).inv ≫ ((projection I) ∣_ U.1) =
      ReesGrading.projection (affineCenterIdeal I U) ≫ U.1.toScheme.isoSpec.inv := by
    apply (cancel_mono U.1.toScheme.isoSpec.hom).mp
    rw [Category.assoc, Category.assoc, Iso.inv_hom_id, Category.comp_id,
      ← affineRestrictionIso_hom_reesProjection I U, Iso.inv_hom_id_assoc]
  rw [totalChart, Category.assoc, ← morphismRestrict_ι, ← Category.assoc, he,
    Category.assoc]
  rfl

@[simp] theorem baseChart_opensRange : (baseChart (X := X) U).opensRange = U.1 := by
  change (U.1.toScheme.isoSpec.inv ≫ U.1.ι).opensRange = U.1
  rw [Scheme.Hom.opensRange_comp_of_isIso, Scheme.Opens.opensRange_ι]

@[simp] theorem totalChart_opensRange :
    (totalChart I U).opensRange = projection I ⁻¹ᵁ U.1 := by
  change ((affineRestrictionIso I U).inv ≫ ((projection I) ⁻¹ᵁ U.1).ι).opensRange = _
  rw [Scheme.Hom.opensRange_comp_of_isIso, Scheme.Opens.opensRange_ι]

@[simp] theorem center_comap_baseChart :
    I.comap (baseChart U) = IdealPullback.specIdeal (affineCenterIdeal I U) := by
  rw [baseChart, Scheme.IdealSheafData.comap_comp, IdealPullback.comap_isoSpec_inv]

end
end PiExponentSeshadri.BlowupGluing

end OAI

/-
Modification notice for the LogTwo project.
Derived from openai/math (Apache-2.0), revision adc7f1241b42e322a6451854ab7e4b4c146bf78a.
Original source: lean/OAI/NumberTheory/PiExponent/Ampleness/BlowupPresentationRestriction.lean
Changes: Convert module/import declarations to the Lean 4.34 public module format.
See ../../../../../THIRD_PARTY_NOTICES.txt for provenance and the recorded changes.
-/

module

public import OAI.NumberTheory.PiExponent.Ampleness.GlobalBlowupRestriction
public import OAI.NumberTheory.PiExponent.Cohomology.PencilCohomologySections

@[expose] public section

namespace OAI

namespace PiExponentSeshadri.Geometry
noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace
open PiExponentSeshadri.Frames
variable {X B : Scheme.{0}} {I : X.IdealSheafData} {π : B ⟶ X}

lemma presents_post_toSpec [IsAffine X] (J : LineBundle B)
    (ι : J.sheaf ⟶ O B) (hJ : PresentsPullbackIdeal I π J ι) :
    PresentsPullbackIdeal (IdealPullback.specIdeal (I.ideal ⟨⊤,isAffineOpen_top X⟩))
      (π ≫ X.isoSpec.hom) J ι := by
  refine ⟨hJ.1,?_⟩
  intro U V e
  rw [InvertibleLocal.image_eq_comap I π J ι hJ U,
    ← IdealPullback.comap_ideal _ (π ≫ X.isoSpec.hom) U V e,
      Scheme.IdealSheafData.comap_comp]
  rw [show (IdealPullback.specIdeal (I.ideal ⟨⊤,isAffineOpen_top X⟩)).comap
    X.isoSpec.hom = I from IdealPullback.specIdeal_comap_toSpec I]

lemma presents_morphismRestrict (J : LineBundle B) (ι : J.sheaf ⟶ O B)
    (hJ : PresentsPullbackIdeal I π J ι) (U : X.affineOpens) :
    PresentsPullbackIdeal (I.comap U.1.ι) (π ∣_ U.1)
      (J.restrict (π ⁻¹ᵁ U.1).ι) (InvertibleLocal.restrictedInclusion J ι (π ⁻¹ᵁ U.1).ι) := by
  refine ⟨@InvertibleLocal.restrictedInclusion_mono _ _ J ι
    (π ⁻¹ᵁ U.1).ι inferInstance hJ.1, ?_⟩
  intro V W hVW
  change ((InvertibleLocal.restrictedInclusion J ι (π ⁻¹ᵁ U.1).ι).val.app
    (Opposite.op V.1)).hom.range = _
  rw [InvertibleLocal.restricted_image_on_chart J ι hJ (π ⁻¹ᵁ U.1).ι V U (by
    rintro _ ⟨x,hx,rfl⟩; exact x.property),
    ← Scheme.IdealSheafData.comap_comp,← morphismRestrict_ι π U.1,
      Scheme.IdealSheafData.comap_comp]
  exact IdealPullback.comap_ideal _ (π ∣_ U.1) V W hVW

end
end PiExponentSeshadri.Geometry

end OAI

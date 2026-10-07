/-
Modification notice for the LogTwo project.
Derived from openai/math (Apache-2.0), revision adc7f1241b42e322a6451854ab7e4b4c146bf78a.
Original source: lean/OAI/NumberTheory/PiExponent/Geometry/ProjectiveO1Morphism.lean
Changes: Convert module/import declarations to the Lean 4.34 public module format.
See ../../../../../THIRD_PARTY_NOTICES.txt for provenance and the recorded changes.
-/

module

public import OAI.NumberTheory.PiExponent.Geometry.ProjectiveO1LocalIdentity
public import OAI.NumberTheory.PiExponent.Geometry.ProjectiveSectionsPullback

@[expose] public section

namespace OAI

noncomputable section

namespace PiExponent.ProjectiveO1

open AlgebraicGeometry CategoryTheory TopologicalSpace
open PiExponentSeshadri.Projective PiExponentSeshadri.Frames PiExponentSeshadri.LineBundleGluing

variable {R σ : Type} [CommRing R]

def coordinateOpenFrame (i : σ) :
    (lineBundle (R := R) (σ := σ)).sheaf.restrict (coordinateOpen i).ι ≅
      O (coordinateOpen (R := R) i).toScheme :=
  openFrame (coordinateCocycle (R := R) (σ := σ)) i (coordinateOpen i) le_rfl

lemma coordinateOpenFrame_normalized (i : σ) :
    coefficient (coordinateOpenFrame (R := R) i)
      (restrictSection (coordinateOpen i).ι (coordinateSection i)) = 1 :=
  coordinateSection_normalized i (coordinateOpen i) le_rfl

lemma coordinateOpenFrame_localMap (i : σ) :
    coordinatesMap (coordinateOpen (R := R) i).toScheme
      ((coordinateOpen i).ι.appTop.hom.comp (scalars (R := R) (σ := σ)))
      (fun j => coefficient (coordinateOpenFrame i)
        (restrictSection (coordinateOpen i).ι (coordinateSection j))) i
      (coordinateOpenFrame_normalized i) = (coordinateOpen i).ι :=
  coordinateSection_localMap i

attribute [local irreducible] coordinateSection lineBundle coordinateCocycle scalars coordinateOpenFrame
  sectionsMorphism CoordinateAtlas.morphism atlasOfFramedSections

theorem coordinate_sectionsMorphism_identity :
    sectionsMorphism (M := (lineBundle (R := R) (σ := σ)).sheaf)
      (scalars (R := R) (σ := σ)) (coordinateSection (R := R) (σ := σ))
      (coordinateSection_cover (R := R) (σ := σ)) = 𝟙 (projectiveSpace R σ) := by
  apply ((projectiveSpace R σ).openCoverOfIsOpenCover
    (coordinateOpen (R := R)) standardChart_cover).hom_ext
  intro i
  change (coordinateOpen (R := R) i).ι ≫ sectionsMorphism _ _ _ =
    (coordinateOpen i).ι ≫ 𝟙 _
  rw [Category.comp_id]
  have hι : IsOpenImmersion (coordinateOpen (R := R) i).ι :=
    IsOpenImmersion.ofRestrict (projectiveSpace R σ) (coordinateOpen (R := R) i).isOpenEmbedding
  exact (@sectionsMorphism_frame R σ _ (projectiveSpace R σ)
    (coordinateOpen (R := R) i).toScheme (lineBundle (R := R) (σ := σ)).sheaf
    (scalars (R := R) (σ := σ)) (coordinateSection (R := R) (σ := σ))
    (coordinateSection_cover (R := R) (σ := σ)) (coordinateOpen i).ι hι
    (coordinateOpenFrame i) i (coordinateOpenFrame_normalized i)).trans
      (coordinateOpenFrame_localMap i)

end PiExponent.ProjectiveO1

end

end OAI

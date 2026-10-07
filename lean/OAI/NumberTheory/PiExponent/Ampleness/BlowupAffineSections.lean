/-
Modification notice for the LogTwo project.
Derived from openai/math (Apache-2.0), revision adc7f1241b42e322a6451854ab7e4b4c146bf78a.
Original source: lean/OAI/NumberTheory/PiExponent/Ampleness/BlowupAffineSections.lean
Changes: Convert module/import declarations to the Lean 4.34 public module format.
See ../../../../../THIRD_PARTY_NOTICES.txt for provenance and the recorded changes.
-/

module

public import OAI.NumberTheory.PiExponent.Ampleness.BlowupPresentationRestriction
public import OAI.NumberTheory.PiExponent.Ampleness.BlowupUniversalBaseChange
public import OAI.NumberTheory.PiExponent.Ampleness.ReesRelativeSections

@[expose] public section

namespace OAI

namespace PiExponentSeshadri.Geometry
noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace
open PiExponentSeshadri.Frames
variable {X B : Scheme.{0}} {I : X.IdealSheafData} {π : B ⟶ X}

theorem IsBlowup.affine_section_cover [IsAffine X] (hπ : IsBlowup I π)
    (J : LineBundle B) (ι : J.sheaf ⟶ O B) (hJ : PresentsPullbackIdeal I π J ι) :
    ∃ (α : Type) (s : α → (O B ⟶ J.sheaf)),
      (⨆ a, SectionOpens.isoOpen (s a)) = ⊤ ∧
      ∀ a, IsAffineOpen (SectionOpens.isoOpen (s a)) := by
  let A := I.ideal ⟨⊤,isAffineOpen_top X⟩
  have hp := hπ.postIso X.isoSpec (IdealPullback.specIdeal A)
    (IdealPullback.specIdeal_comap_toSpec I)
  obtain ⟨s,hs,ha⟩ := ReesGrading.relative_affine_section_cover A
    (π ≫ X.isoSpec.hom) J ι (presents_post_toSpec J ι hJ) hp
  exact ⟨A,s,hs,ha⟩

end
end PiExponentSeshadri.Geometry

end OAI

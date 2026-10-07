/-
Modification notice for the LogTwo project.
Derived from openai/math (Apache-2.0), revision adc7f1241b42e322a6451854ab7e4b4c146bf78a.
Original source: lean/OAI/NumberTheory/PiExponent/Approximation/SectionZeroSupport.lean
Changes: Convert module/import declarations to the Lean 4.34 public module format.
See ../../../../../THIRD_PARTY_NOTICES.txt for provenance and the recorded changes.
-/

module

public import OAI.NumberTheory.PiExponent.Approximation.SectionImageSupport
public import OAI.NumberTheory.PiExponent.LocalAlgebra.SectionZeroIdeal

@[expose] public section

namespace OAI

namespace PiExponent.SectionZeroIdeal
noncomputable section
open AlgebraicGeometry CategoryTheory TopologicalSpace
open PiExponentSeshadri.Geometry PiExponentSeshadri.Frames
open PiExponent.InverseFrames PiExponent.SectionImageSupport
variable {X : Scheme.{0}}

theorem dualSection_isoOpen (L : LineBundle X) (s : GlobalSections X L.sheaf) :
    PiExponentSeshadri.SectionOpens.isoOpen (L.dualSection s) = sectionOpen X s := by
  ext x
  obtain ⟨U,hx,⟨e⟩⟩ := L.locallyRankOne x
  change (⟨x,hx⟩ : U.toScheme) ∈ U.ι ⁻¹ᵁ PiExponentSeshadri.SectionOpens.isoOpen (L.dualSection s) ↔
    (⟨x,hx⟩ : U.toScheme) ∈ U.ι ⁻¹ᵁ PiExponentSeshadri.SectionOpens.isoOpen s
  erw [isoOpen_preimage_on_frame (L.dualSection s) U
    (inverseOpenFrame (lineTensorInverseIso L) U e), dualSection_restrict_coefficient,
    preimage_isoOpen s U.ι e]

theorem zeroIdeal_support (L : LineBundle X) (s : GlobalSections X L.sheaf) :
    ((zeroIdeal L s).support : Set X) = (sectionOpen X s : Set X)ᶜ := by
  let := PiExponent.GeometrySupport.LineBundleCoherent.lineBundle_isFinitePresentation L.inverse
  let : SheafOfModules.IsQuasicoherent L.inverse.sheaf :=
    (SheafOfModules.IsFinitePresentation.exists_quasicoherentData L.inverse.sheaf).choose.isQuasicoherent
  change ((PiExponent.SectionImageIdeal.imageIdealSheaf (L.dualSection s)).support : Set X) = _
  rw [imageIdealSheaf_support, dualSection_isoOpen]

end
end PiExponent.SectionZeroIdeal

end OAI

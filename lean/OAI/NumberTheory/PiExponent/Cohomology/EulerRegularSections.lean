/-
Modification notice for the LogTwo project.
Derived from openai/math (Apache-2.0), revision adc7f1241b42e322a6451854ab7e4b4c146bf78a.
Original source: lean/OAI/NumberTheory/PiExponent/Cohomology/EulerRegularSections.lean
Changes: Convert module/import declarations to the Lean 4.34 public module format.
See ../../../../../THIRD_PARTY_NOTICES.txt for provenance and the recorded changes.
-/

module

public import OAI.NumberTheory.PiExponent.Approximation.GeneratorsSectionCover
public import OAI.NumberTheory.PiExponent.Approximation.RegularSectionChoice
public import OAI.NumberTheory.PiExponent.Cohomology.EulerRegularTwists

@[expose] public section

namespace OAI

namespace PiExponent.NumericalAmpleness
noncomputable section
open AlgebraicGeometry CategoryTheory
open PiExponentSeshadri.Geometry
variable {X : Scheme.{0}}

theorem exists_mono_section_of_generators [IsNoetherian X]
    (p : X ⟶ Spec (CommRingCat.of ℂ)) (L : LineBundle X)
    (G : L.sheaf.GeneratingSections) [G.IsFiniteType] :
    ∃ s : GlobalSections X L.sheaf, Mono s := by
  obtain ⟨k, s, hs⟩ := PiExponent.GeneratorsSectionCover.exists_fin_section_cover L G
  exact exists_mono_section_of_finite_cover p L s hs

theorem exists_regular_twist_pair [IsNoetherian X]
    (p : X ⟶ Spec (CommRingCat.of ℂ)) (H L : LineBundle X) (hH : H.IsAmple) :
    ∃ B : LineBundle X, ∃ s : GlobalSections X (L.tensor B).sheaf,
      ∃ t : GlobalSections X B.sheaf, Mono s ∧ Mono t := by
  obtain ⟨n, G, hG, G', hG'⟩ := exists_common_tensor_generators H L hH
  let : G.IsFiniteType := hG
  let : G'.IsFiniteType := hG'
  obtain ⟨s, hs⟩ := exists_mono_section_of_generators p (L.tensor (H.pow n)) G'
  obtain ⟨t, ht⟩ := exists_mono_section_of_generators p (H.pow n) G
  exact ⟨H.pow n, s, t, hs, ht⟩

end
end PiExponent.NumericalAmpleness

end OAI

/-
Modification notice for the LogTwo project.
Derived from openai/math (Apache-2.0), revision adc7f1241b42e322a6451854ab7e4b4c146bf78a.
Original source: lean/OAI/NumberTheory/PiExponent/Ampleness/AmpleFiniteProjectiveEmbedding.lean
Changes: Convert module/import declarations to the Lean 4.34 public module format.
See ../../../../../THIRD_PARTY_NOTICES.txt for provenance and the recorded changes.
-/

module

public import OAI.NumberTheory.PiExponent.Ampleness.NoetherianAmpleProjectiveSections
public import OAI.NumberTheory.PiExponent.Cohomology.AmpleCohomologyFinite
public import OAI.NumberTheory.PiExponent.Geometry.ProjectiveSectionReindex

@[expose] public section

namespace OAI

namespace PiExponent.NumericalAmpleness
noncomputable section
open AlgebraicGeometry CategoryTheory TopologicalSpace
open PiExponentSeshadri.Geometry PiExponentSeshadri.Projective
open PiExponent.ProjectiveO1
variable {X : Scheme.{0}}

theorem ample_finite_projective_embedding [Nonempty X]
    (p : X ⟶ Spec (CommRingCat.of ℂ)) [IsProper p]
    (H : LineBundle X) (hH : H.IsAmple) :
    ∃ r : ℕ, ∃ i : X ⟶ projectiveSpace ℂ (Fin (r+1)),
      IsClosedImmersion i ∧ i ≫ polynomialProjectiveProjection ℂ (Fin (r+1)) = p := by
  classical
  let : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian p
  let : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace p
  let : IsNoetherian X := {}
  obtain ⟨n, _, σ, hσ, s, hs, hc⟩ := H.ample_projective_sections_noetherian p hH
  let : Fintype σ := hσ
  have hne : Nonempty σ := by
    obtain ⟨x⟩ : Nonempty X := inferInstance
    have hx : x ∈ ⨆ i, PiExponentSeshadri.SectionOpens.isoOpen (s i) := by
      rw [hs]
      trivial
    obtain ⟨i, _⟩ := Opens.mem_iSup.mp hx
    exact ⟨i⟩
  have hpos : 0 < Fintype.card σ := Fintype.card_pos_iff.mpr hne
  obtain ⟨r, hr⟩ := Nat.exists_eq_succ_of_ne_zero (ne_of_gt hpos)
  let e : Fin (r+1) ≃ σ := ((Fintype.equivFin σ).trans (finCongr hr)).symm
  let t : Fin (r+1) → GlobalSections X (modulePow X H.sheaf n) := s ∘ e
  have ht : (⨆ i, PiExponentSeshadri.SectionOpens.isoOpen (t i)) = ⊤ :=
    (e.iSup_comp (g := fun j => PiExponentSeshadri.SectionOpens.isoOpen (s j))).trans hs
  let k := baseScalars p
  let : IsClosedImmersion (sectionsMorphism k s hs) := hc
  let i : X ⟶ projectiveSpace ℂ (Fin (r+1)) := sectionsMorphism k t ht
  have hclosed : IsClosedImmersion i := sectionsMorphism_reindex_closed k s hs e ht
  refine ⟨r, i, hclosed, ?_⟩
  rw [← AmpleCohomologyFinite.projectiveBase_eq_polynomialProjectiveProjection]
  exact (sectionsMorphism_over k t ht).trans (toSpec_scalarMap p)

end
end PiExponent.NumericalAmpleness

end OAI

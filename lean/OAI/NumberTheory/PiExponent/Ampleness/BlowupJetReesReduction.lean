/-
Modification notice for the LogTwo project.
Derived from openai/math (Apache-2.0), revision adc7f1241b42e322a6451854ab7e4b4c146bf78a.
Original source: lean/OAI/NumberTheory/PiExponent/Ampleness/BlowupJetReesReduction.lean
Changes: Convert module/import declarations to the Lean 4.34 public module format.
See ../../../../../THIRD_PARTY_NOTICES.txt for provenance and the recorded changes.
-/

module

public import OAI.NumberTheory.PiExponent.Ampleness.FiniteReesComparison
public import OAI.NumberTheory.PiExponent.Ampleness.GlobalBlowupJetSurjectivity

@[expose] public section

namespace OAI

namespace PiExponent.BlowupJetSurjectivity
noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace
open PiExponentSeshadri.Geometry
open PiExponent.GeometrySupport
variable {X : Scheme.{0}} {R : Type} [CommRing R] [IsNoetherianRing R]

theorem eventual_blowup_jetRestriction_surjective_of_affine_recovery
    (p : X ⟶ Spec (CommRingCat.of R)) [IsProper p] [IsLocallyNoetherian X]
    (I : X.IdealSheafData) (A : LineBundle X)
    (hample : LineBundle.IsAmple _ (blowupBundle I A))
    (hrecover : ∀ U : X.affineOpens, ∃ N, ∀ n, N ≤ n → Function.Bijective
      ((ExceptionalRecoveryMap.ordinaryMap (PiExponentSeshadri.BlowupGluing.projection I)
        I (PiExponentSeshadri.BlowupGluing.exceptionalLineBundle I)
        (PiExponentSeshadri.BlowupGluing.exceptionalInclusion I)
        (PiExponentSeshadri.BlowupGluing.exceptional_presents I) n).app U.1)) :
    ∃ N, ∀ n, N ≤ n → Function.Surjective (jetRestriction I A n) := by
  let : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian p
  let : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace p
  let : X.IsSeparated := ⟨by
    have h : IsSeparated (p ≫ terminal.from (Spec (CommRingCat.of R))) := inferInstance
    simpa only [terminal.comp_from] using h⟩
  obtain ⟨k,U,hcover,N,hN⟩ :=
    ExceptionalRecoveryMap.eventual_comparison_of_affine_recovery
      (PiExponentSeshadri.BlowupGluing.projection I) I
      (PiExponentSeshadri.BlowupGluing.exceptionalLineBundle I)
      (PiExponentSeshadri.BlowupGluing.exceptionalInclusion I)
      (PiExponentSeshadri.BlowupGluing.exceptional_presents I) A hrecover
  exact eventual_blowup_jetRestriction_surjective_of_section_comparison
    p I A hample (fun i => (U i).1) (fun i => (U i).2) hcover ⟨N,hN⟩

end
end PiExponent.BlowupJetSurjectivity

end OAI

/-
Modification notice for the LogTwo project.
Derived from openai/math (Apache-2.0), revision adc7f1241b42e322a6451854ab7e4b4c146bf78a.
Original source: lean/OAI/NumberTheory/PiExponent/Ampleness/BlowupJetSurjectivityComplete.lean
Changes: Convert module/import declarations to the Lean 4.34 public module format.
See ../../../../../THIRD_PARTY_NOTICES.txt for provenance and the recorded changes.
-/

module

public import OAI.NumberTheory.PiExponent.Ampleness.BlowupJetReesReduction
public import OAI.NumberTheory.PiExponent.Ampleness.GlobalReesCanonicalRecovery

@[expose] public section

namespace OAI

namespace PiExponent.BlowupJetSurjectivity
noncomputable section
open AlgebraicGeometry CategoryTheory TopologicalSpace
open PiExponentSeshadri.Geometry
variable {X : Scheme.{0}} {R : Type} [CommRing R] [IsNoetherianRing R]

theorem eventual_blowup_jetRestriction_surjective
    (p : X ⟶ Spec (CommRingCat.of R)) [IsProper p]
    (I : X.IdealSheafData) (A : LineBundle X)
    (hample : LineBundle.IsAmple _ (blowupBundle I A)) :
    ∃ N, ∀ n, N ≤ n → Function.Surjective (jetRestriction I A n) := by
  let : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian p
  exact eventual_blowup_jetRestriction_surjective_of_affine_recovery p I A hample
    (fun U => GlobalReesRecoveryComparison.eventually_ordinaryMap_app_bijective I U)

end
end PiExponent.BlowupJetSurjectivity

end OAI

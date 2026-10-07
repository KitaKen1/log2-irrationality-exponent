/-
Modification notice for the LogTwo project.
Derived from openai/math (Apache-2.0), revision adc7f1241b42e322a6451854ab7e4b4c146bf78a.
Original source: lean/OAI/NumberTheory/PiExponent/Ampleness/GlobalReesCanonicalRecovery.lean
Changes: Convert module/import declarations to the Lean 4.34 public module format.
See ../../../../../THIRD_PARTY_NOTICES.txt for provenance and the recorded changes.
-/

module

public import OAI.NumberTheory.PiExponent.Ampleness.AffineReesCanonicalRecovery
public import OAI.NumberTheory.PiExponent.Ampleness.GlobalReesRecoveryComparison

@[expose] public section

namespace OAI

noncomputable section
namespace PiExponent.GlobalReesRecoveryComparison
open AlgebraicGeometry CategoryTheory
open PiExponentSeshadri.Geometry PiExponentSeshadri.BlowupGluing
open CanonicalRecoveryProperties

theorem eventually_ordinaryMap_app_bijective {X : Scheme.{0}} [IsLocallyNoetherian X]
    (I : X.IdealSheafData) (U : X.affineOpens) :
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
      OrdinaryBijective (projection I) I (exceptionalLineBundle I)
        (exceptionalInclusion I) (exceptional_presents I) n U.1 := by
  let : IsAffine U.1.toScheme := U.2
  let : IsNoetherianRing Γ(U.1.toScheme,⊤) :=
    IsLocallyNoetherian.component_noetherian ⟨⊤, isAffineOpen_top U.1.toScheme⟩
  obtain ⟨N,hN⟩ := AffineReesCanonicalRecovery.eventually_comap_bijective (affineCenterIdeal I U)
  exact ⟨N, fun n hn => (ordinary_iff_comap (projection I) I
    (exceptionalLineBundle I) (exceptionalInclusion I) (exceptional_presents I) n U.1).mpr
      ((comap_app_bijective_iff_affine I U n).mpr (hN n hn))⟩

end PiExponent.GlobalReesRecoveryComparison

end

end OAI

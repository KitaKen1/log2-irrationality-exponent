/-
Modification notice for the LogTwo project.
Derived from openai/math (Apache-2.0), revision adc7f1241b42e322a6451854ab7e4b4c146bf78a.
Original source: lean/OAI/NumberTheory/PiExponent/Ampleness/AffineReesCanonicalRecovery.lean
Changes: Convert module/import declarations to the Lean 4.34 public module format.
See ../../../../../THIRD_PARTY_NOTICES.txt for provenance and the recorded changes.
-/

module

public import OAI.NumberTheory.PiExponent.Ampleness.ReesSheafCanonicalValue
public import OAI.NumberTheory.PiExponent.Approximation.CanonicalAffineRecovery
public import OAI.NumberTheory.PiExponent.LocalAlgebra.IdealFiniteGenerators

@[expose] public section

namespace OAI

noncomputable section
namespace PiExponent.AffineReesCanonicalRecovery
open AlgebraicGeometry CategoryTheory
open PiExponentSeshadri.Geometry PiExponentSeshadri.ReesGrading PiExponentSeshadri.IdealPullback
open CanonicalRecoveryProperties
attribute [local irreducible] affineBlowup projection exceptionalLineBundle exceptionalInclusion
  ReesSheafCechRecovery.ordinaryGlobalSection

theorem eventually_comap_bijective {R : Type} [CommRing R] [IsNoetherianRing R]
    (I : Ideal R) :
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
      ComapBijective (projection I) (specIdeal (I^n)) ⊤ := by
  classical
  obtain ⟨m,a,ha⟩ := IdealFiniteGenerators.exists_generators I
  obtain ⟨N,hN⟩ := ReesSheafCechRecovery.eventually_recovery_and_cohomology I a ha
  refine ⟨N, ?_⟩
  intro n hn
  exact (CanonicalAffineRecovery.power_bijective_iff_comap I (projection I)
    (exceptionalLineBundle I) (exceptionalInclusion I) (exceptional_presents I) n
    (ReesSheafCechRecovery.ordinaryGlobalSection I a ha n)
    (ReesSheafCechRecovery.ordinaryGlobalSection_inclusion I a ha n)).mp (hN n hn).1

end PiExponent.AffineReesCanonicalRecovery

end

end OAI

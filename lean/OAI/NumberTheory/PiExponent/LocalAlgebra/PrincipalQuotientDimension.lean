/-
Modification notice for the LogTwo project.
Derived from openai/math (Apache-2.0), revision adc7f1241b42e322a6451854ab7e4b4c146bf78a.
Original source: lean/OAI/NumberTheory/PiExponent/LocalAlgebra/PrincipalQuotientDimension.lean
Changes: Convert module/import declarations to the Lean 4.34 public module format.
See ../../../../../THIRD_PARTY_NOTICES.txt for provenance and the recorded changes.
-/

module

public import Mathlib.RingTheory.Ideal.KrullsHeightTheorem
public import Mathlib.RingTheory.KrullDimension.NonZeroDivisors
public import OAI.NumberTheory.PiExponent.LocalAlgebra.ClosedPointLocalDimension

@[expose] public section

namespace OAI

namespace PiExponent.GeometrySupport.PrincipalQuotientDimension

variable (k R : Type*) [Field k] [CommRing R] [IsDomain R]
  [Algebra k R] [Algebra.FiniteType k R]

include k

theorem le_quotient_succ (a : R) (hu : ¬ IsUnit a) :
    ringKrullDim R ≤ ringKrullDim (R ⧸ Ideal.span {a}) + 1 := by
  let : IsNoetherianRing R := Algebra.FiniteType.isNoetherianRing k R
  obtain ⟨m, hm, ham⟩ := Ideal.exists_le_maximal (Ideal.span {a})
    (Ideal.span_singleton_ne_top hu)
  let : m.IsMaximal := hm
  rw [← PiExponentJets.W29.affineDomain_maximal_height k R m]
  exact Ideal.height_le_ringKrullDim_quotient_add_one
    (ham (Ideal.subset_span (by simp)))

theorem quotient_succ_eq (a : R) (ha : a ≠ 0) (hu : ¬ IsUnit a) :
    ringKrullDim (R ⧸ Ideal.span {a}) + 1 = ringKrullDim R := by
  exact le_antisymm
    (ringKrullDim_quotient_succ_le_of_nonZeroDivisor
      (mem_nonZeroDivisors_of_ne_zero ha))
    (le_quotient_succ k R a hu)

end PiExponent.GeometrySupport.PrincipalQuotientDimension

end OAI

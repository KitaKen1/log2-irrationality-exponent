/-
Modification notice for the LogTwo project.
Derived from openai/math (Apache-2.0), revision adc7f1241b42e322a6451854ab7e4b4c146bf78a.
Original source: lean/OAI/NumberTheory/PiExponent/LocalAlgebra/RegularSequenceHomZero.lean
Changes: Convert module/import declarations to the Lean 4.34 public module format.
See ../../../../../THIRD_PARTY_NOTICES.txt for provenance and the recorded changes.
-/

module

public import Mathlib.LinearAlgebra.Dual.Defs
public import Mathlib.RingTheory.Regular.RegularSequence

@[expose] public section

namespace OAI

namespace PiExponentSiegelAux.W30
open Module
variable {R : Type*} [CommRing R]

theorem quotient_dual_eq_zero_of_regular (I : Ideal R) (r : R) (hrI : r ∈ I)
    (hr : IsSMulRegular R r) (φ : Dual R (R ⧸ I)) : φ = 0 := by
  apply LinearMap.ext
  intro x
  apply hr
  change r • φ x = r • (0 : R)
  rw [smul_zero, ← φ.map_smul]
  have hx : r • x = 0 := by
    obtain ⟨a, rfl⟩ := Submodule.mkQ_surjective I x
    change r • (Submodule.Quotient.mk a : R ⧸ I) = 0
    rw [← Submodule.Quotient.mk_smul I]
    apply (Submodule.Quotient.mk_eq_zero I).mpr
    simpa only [smul_eq_mul, mul_comm] using I.smul_mem a hrI
  rw [hx, map_zero]

theorem regularSequenceQuotient_dual_subsingleton (rs : List R)
    (hreg : RingTheory.Sequence.IsRegular R rs) (hne : rs ≠ []) :
    Subsingleton (Dual R (R ⧸ Ideal.ofList rs)) := by
  cases rs with
  | nil => exact (hne rfl).elim
  | cons r rs =>
    apply subsingleton_of_forall_eq 0
    intro φ
    apply quotient_dual_eq_zero_of_regular (Ideal.ofList (r :: rs)) r
    · exact Ideal.subset_span (by simp)
    · exact ((RingTheory.Sequence.isRegular_cons_iff R r rs).mp hreg).1

end PiExponentSiegelAux.W30

end OAI

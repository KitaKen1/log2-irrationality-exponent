/-
Modification notice for the LogTwo project.
Derived from openai/math (Apache-2.0), revision adc7f1241b42e322a6451854ab7e4b4c146bf78a.
Original source: lean/OAI/NumberTheory/PiExponent/LocalAlgebra/LocalIntersectionDimensionOne.lean
Changes: Convert module/import declarations to the Lean 4.34 public module format.
See ../../../../../THIRD_PARTY_NOTICES.txt for provenance and the recorded changes.
-/

module

public import Mathlib.RingTheory.KrullDimension.LocalRing
public import OAI.NumberTheory.PiExponent.LocalAlgebra.LocalIntersectionPrimeFactors

@[expose] public section

namespace OAI

namespace PiExponentJets.W28.LocalIntersection

variable {A : Type*} [CommRing A]

theorem maximal_factor_cut_eq_colon (P : Ideal A) [P.IsMaximal] (x : A) :
    Module.length A (A ⧸ (P ⊔ Ideal.span {x})) =
      Module.length A ((P.colon {x}) ⧸ P.submoduleOf (P.colon {x})) := by
  let : IsSimpleModule A (A ⧸ P) :=
    isSimpleModule_iff_isCoatom.mpr (Ideal.isMaximal_def.mp inferInstance)
  apply finite_length_cut_eq_colon P x
  apply Module.length_ne_top_iff.mp
  rw [Module.length_eq_one A (A ⧸ P)]
  exact ENat.one_ne_top

theorem regular_not_mem_minimalPrime (x : A) (hx : x ∈ nonZeroDivisors A)
    (P : Ideal A) (hP : P ∈ minimalPrimes A) : x ∉ P := by
  exact fun hxP => Set.disjoint_left.mp
    (Ideal.disjoint_nonZeroDivisors_of_mem_minimalPrimes hP) hxP hx

theorem dimension_one_prime_factor_dichotomy
    [Ring.KrullDimLE 1 A] [IsLocalRing A]
    (x : A) (hx : x ∈ nonZeroDivisors A)
    (P : Ideal A) [P.IsPrime] :
    (P ∈ minimalPrimes A ∧ Function.Injective (quotientMul P x)) ∨
    (P = IsLocalRing.maximalIdeal A ∧
      Module.length A (A ⧸ (P ⊔ Ideal.span {x})) =
        Module.length A ((P.colon {x}) ⧸ P.submoduleOf (P.colon {x}))) := by
  rcases (Ring.krullDimLE_one_iff.mp inferInstance) P inferInstance with hP | hP
  · exact Or.inl ⟨hP,
      prime_quotientMul_injective P x (regular_not_mem_minimalPrime x hx P hP)⟩
  · let : P.IsMaximal := hP
    exact Or.inr ⟨IsLocalRing.eq_maximalIdeal hP, maximal_factor_cut_eq_colon P x⟩

end PiExponentJets.W28.LocalIntersection

end OAI

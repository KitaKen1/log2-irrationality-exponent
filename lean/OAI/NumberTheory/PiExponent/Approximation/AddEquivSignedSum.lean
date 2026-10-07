/-
Modification notice for the LogTwo project.
Derived from openai/math (Apache-2.0), revision adc7f1241b42e322a6451854ab7e4b4c146bf78a.
Original source: lean/OAI/NumberTheory/PiExponent/Approximation/AddEquivSignedSum.lean
Changes: Convert module/import declarations to the Lean 4.34 public module format.
See ../../../../../THIRD_PARTY_NOTICES.txt for provenance and the recorded changes.
-/

module

public import Mathlib

@[expose] public section

namespace OAI

namespace PiExponent.AddEquivSignedSum
open scoped BigOperators

theorem map_signed_sum {A B : Type*} [AddCommGroup A] [AddCommGroup B]
    (E : A ≃+ B) (q : ℕ) (f : Fin (q+2) → A) :
    E (∑ k, (-1 : ℤ)^k.val • f k) = ∑ k, (-1 : ℤ)^k.val • E (f k) := by
  simp only [map_sum, map_zsmul]

theorem map_signed_sum_eq {A B : Type*} [AddCommGroup A] [AddCommGroup B]
    (E : A ≃+ B) (q : ℕ) (f : Fin (q+2) → A) (g : Fin (q+2) → B)
    (h : ∀ k, E (f k) = g k) :
    E (∑ k, (-1 : ℤ)^k.val • f k) = ∑ k, (-1 : ℤ)^k.val • g k := by
  rw [map_signed_sum]
  exact Finset.sum_congr rfl (fun k _ => congrArg (fun z => (-1 : ℤ)^k.val • z) (h k))

end PiExponent.AddEquivSignedSum

end OAI

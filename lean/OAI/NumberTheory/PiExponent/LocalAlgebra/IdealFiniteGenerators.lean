/-
Modification notice for the LogTwo project.
Derived from openai/math (Apache-2.0), revision adc7f1241b42e322a6451854ab7e4b4c146bf78a.
Original source: lean/OAI/NumberTheory/PiExponent/LocalAlgebra/IdealFiniteGenerators.lean
Changes: Convert module/import declarations to the Lean 4.34 public module format.
See ../../../../../THIRD_PARTY_NOTICES.txt for provenance and the recorded changes.
-/

module

public import Mathlib

@[expose] public section

namespace OAI

namespace PiExponent.IdealFiniteGenerators

theorem exists_generators {R : Type*} [CommRing R] [IsNoetherianRing R]
    (I : Ideal R) : ∃ m : ℕ, ∃ a : Fin m → I,
      Ideal.span (Set.range fun j => (a j).val) = I := by
  obtain ⟨m,b,hb⟩ := Submodule.fg_iff_exists_fin_generating_family.mp
    (IsNoetherian.noetherian I)
  let a : Fin m → I := fun j => ⟨b j, by
    rw [← hb]
    exact Submodule.subset_span ⟨j,rfl⟩⟩
  exact ⟨m,a,hb⟩

end PiExponent.IdealFiniteGenerators

end OAI

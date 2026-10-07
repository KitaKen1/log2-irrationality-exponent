/-
Modification notice for the LogTwo project.
Derived from openai/math (Apache-2.0), revision adc7f1241b42e322a6451854ab7e4b4c146bf78a.
Original source: lean/OAI/NumberTheory/PiExponent/Jets/DifferentialConstant.lean
Changes: Convert module/import declarations to the Lean 4.34 public module format.
See ../../../../../THIRD_PARTY_NOTICES.txt for provenance and the recorded changes.
-/

module

public import OAI.NumberTheory.PiExponent.Analysis.AlgebraicLogarithmicObstruction

@[expose] public section

namespace OAI

namespace PiExponent

open KaehlerDifferential

theorem isAlgebraic_of_differential_eq_zero
    {C E : Type*} [Field C] [CharZero C] [Field E] [Algebra C E]
    [Algebra.EssFiniteType C E] (x : E) (hx : D C E x = 0) : IsAlgebraic C x :=
  isAlgebraic_of_logarithmic_differential (0 : E) x (by simp [hx])

theorem constant_of_differential_eq_zero
    {C E : Type*} [Field C] [CharZero C] [IsAlgClosed C] [Field E] [Algebra C E]
    [Algebra.EssFiniteType C E] (x : E) (hx : D C E x = 0) :
    ∃ c : C, algebraMap C E c = x :=
  constant_of_logarithmic_differential (0 : E) x (by simp [hx])

end PiExponent

end OAI

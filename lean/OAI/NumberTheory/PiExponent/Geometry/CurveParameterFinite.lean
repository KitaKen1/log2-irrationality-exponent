/-
Modification notice for the LogTwo project.
Derived from openai/math (Apache-2.0), revision adc7f1241b42e322a6451854ab7e4b4c146bf78a.
Original source: lean/OAI/NumberTheory/PiExponent/Geometry/CurveParameterFinite.lean
Changes: Convert module/import declarations to the Lean 4.34 public module format.
See ../../../../../THIRD_PARTY_NOTICES.txt for provenance and the recorded changes.
-/

module

public import Mathlib.FieldTheory.IntermediateField.Adjoin.Algebra
public import Mathlib.RingTheory.AlgebraicIndependent.TranscendenceBasis

@[expose] public section

namespace OAI

namespace PiExponent.CurveParameterFinite

theorem finiteDimensional_adjoin_singleton
    (F E : Type*) [Field F] [Field E] [Algebra F E]
    [Algebra.EssFiniteType F E] (htrdeg : Algebra.trdeg F E ≤ 1)
    {g : E} (hg : Transcendental F g) :
    FiniteDimensional (IntermediateField.adjoin F {g}) E := by
  have hind : AlgebraicIndependent F (fun z : ({g} : Set E) => (z : E)) := by
    rw [algebraicIndependent_singleton_iff ⟨g, rfl⟩]
    exact hg
  have hb := hind.isTranscendenceBasis_of_trdeg_le_of_finite (by simpa using htrdeg)
  have hrange : Set.range (fun z : ({g} : Set E) => (z : E)) = {g} :=
    Subtype.range_coe
  let : Algebra.IsAlgebraic (IntermediateField.adjoin F {g}) E := by
    have ha := hb.isAlgebraic_field
    rw [hrange] at ha
    exact ha
  let : Algebra.EssFiniteType (IntermediateField.adjoin F {g}) E :=
    Algebra.EssFiniteType.of_comp F (IntermediateField.adjoin F {g}) E
  exact Algebra.finite_of_essFiniteType_of_isAlgebraic

theorem finite_over_every_parameter
    (F E : Type*) [Field F] [Field E] [Algebra F E]
    [Algebra.EssFiniteType F E] (htrdeg : Algebra.trdeg F E = 1) :
    ∀ g : E, Transcendental F g →
      FiniteDimensional (IntermediateField.adjoin F {g}) E :=
  fun _ hg => finiteDimensional_adjoin_singleton F E htrdeg.le hg

end PiExponent.CurveParameterFinite

end OAI

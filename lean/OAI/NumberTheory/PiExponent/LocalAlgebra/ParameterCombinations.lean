/-
Modification notice for the LogTwo project.
Derived from openai/math (Apache-2.0), revision adc7f1241b42e322a6451854ab7e4b4c146bf78a.
Original source: lean/OAI/NumberTheory/PiExponent/LocalAlgebra/ParameterCombinations.lean
Changes: Convert module/import declarations to the Lean 4.34 public module format.
See ../../../../../THIRD_PARTY_NOTICES.txt for provenance and the recorded changes.
-/

module

public import Mathlib.Algebra.MvPolynomial.Degrees
public import Mathlib.RingTheory.Ideal.Span

@[expose] public section

namespace OAI

namespace PiExponentJets.W22

open scoped BigOperators

variable {k σ ι : Type*} [CommRing k]

noncomputable def parameterCombination (s : Finset ι) (c : ι → k)
    (f : ι → MvPolynomial σ k) : MvPolynomial σ k :=
  ∑ i ∈ s, MvPolynomial.C (c i) * f i

theorem parameterCombination_totalDegree_le (s : Finset ι) (c : ι → k)
    (f : ι → MvPolynomial σ k) {d : ℕ}
    (hf : ∀ i ∈ s, (f i).totalDegree ≤ d) :
    (parameterCombination s c f).totalDegree ≤ d := by
  apply MvPolynomial.totalDegree_finsetSum_le
  intro i hi
  calc
    (MvPolynomial.C (c i) * f i).totalDegree ≤
        (MvPolynomial.C (c i) : MvPolynomial σ k).totalDegree + (f i).totalDegree :=
      MvPolynomial.totalDegree_mul _ _
    _ = (f i).totalDegree := by rw [MvPolynomial.totalDegree_C, zero_add]
    _ ≤ d := hf i hi

theorem parameterCombination_mem (s : Finset ι) (c : ι → k)
    (f : ι → MvPolynomial σ k) (J : Ideal (MvPolynomial σ k))
    (hf : ∀ i ∈ s, f i ∈ J) : parameterCombination s c f ∈ J := by
  apply J.sum_mem
  intro i hi
  exact J.mul_mem_left _ (hf i hi)

theorem parameterCandidates_span_le {κ : Type*} (s : Finset ι) (c : κ → ι → k)
    (f : ι → MvPolynomial σ k) (J : Ideal (MvPolynomial σ k))
    (hf : ∀ i ∈ s, f i ∈ J) :
    Ideal.span (Set.range (fun j => parameterCombination s (c j) f)) ≤ J := by
  apply Ideal.span_le.mpr
  rintro p ⟨j, rfl⟩
  exact parameterCombination_mem s (c j) f J hf

end PiExponentJets.W22

end OAI

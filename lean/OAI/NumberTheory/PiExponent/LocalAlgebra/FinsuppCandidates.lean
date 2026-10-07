/-
Modification notice for the LogTwo project.
Derived from openai/math (Apache-2.0), revision adc7f1241b42e322a6451854ab7e4b4c146bf78a.
Original source: lean/OAI/NumberTheory/PiExponent/LocalAlgebra/FinsuppCandidates.lean
Changes: Convert module/import declarations to the Lean 4.34 public module format.
See ../../../../../THIRD_PARTY_NOTICES.txt for provenance and the recorded changes.
-/

module

public import Mathlib.LinearAlgebra.Finsupp.LinearCombination
public import OAI.NumberTheory.PiExponent.LocalAlgebra.ParameterCombinations

@[expose] public section

namespace OAI

namespace PiExponentJets.W22

variable {k σ ι : Type*} [CommRing k]

theorem linearCombination_eq_parameterCombination (f : ι → MvPolynomial σ k) (c : ι →₀ k) :
    Finsupp.linearCombination k f c = parameterCombination c.support c f := by
  simp only [Finsupp.linearCombination_apply, Finsupp.sum, parameterCombination,
    MvPolynomial.C_mul']

theorem linearCombination_totalDegree_le (f : ι → MvPolynomial σ k) (c : ι →₀ k)
    {d : ℕ} (hf : ∀ i, (f i).totalDegree ≤ d) :
    (Finsupp.linearCombination k f c).totalDegree ≤ d := by
  rw [linearCombination_eq_parameterCombination]
  exact parameterCombination_totalDegree_le c.support c f (fun i _ => hf i)

theorem linearCombination_mem_ideal (f : ι → MvPolynomial σ k) (c : ι →₀ k)
    (J : Ideal (MvPolynomial σ k)) (hf : ∀ i, f i ∈ J) :
    Finsupp.linearCombination k f c ∈ J := by
  rw [linearCombination_eq_parameterCombination]
  exact parameterCombination_mem c.support c f J (fun i _ => hf i)

end PiExponentJets.W22

end OAI

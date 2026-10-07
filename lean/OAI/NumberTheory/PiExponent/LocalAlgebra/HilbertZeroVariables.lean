/-
Modification notice for the LogTwo project.
Derived from openai/math (Apache-2.0), revision adc7f1241b42e322a6451854ab7e4b4c146bf78a.
Original source: lean/OAI/NumberTheory/PiExponent/LocalAlgebra/HilbertZeroVariables.lean
Changes: Convert module/import declarations to the Lean 4.34 public module format.
See ../../../../../THIRD_PARTY_NOTICES.txt for provenance and the recorded changes.
-/

module

public import OAI.NumberTheory.PiExponent.Polynomials.HilbertPolynomialBase

@[expose] public section

namespace OAI

namespace PiExponentJets.W64

variable {k σ : Type*} [Field k] [Fintype σ]

theorem quotientSection_finrank_zero_of_no_variables
    (hσ : Fintype.card σ = 0) (I : Ideal (MvPolynomial σ k)) (n : ℕ) :
    Module.finrank k (quotientSection I (n+1)) = 0 := by
  have h := Submodule.finrank_map_le (Ideal.Quotient.mkₐ k I).toLinearMap
    (MvPolynomial.homogeneousSubmodule σ k (n+1))
  rw [homogeneousSection_finrank, card_exponents_degree, hσ,
    Nat.multichoose_zero_succ] at h
  exact Nat.eq_zero_of_le_zero h

theorem sectionHilbertSeries_no_variables
    (hσ : Fintype.card σ = 0) (I : Ideal (MvPolynomial σ k)) :
    sectionHilbertSeries I = PowerSeries.C (Module.finrank k (quotientSection I 0) : ℤ) := by
  ext n
  cases n with
  | zero => simp
  | succ n =>
    rw [coeff_sectionHilbertSeries, quotientSection_finrank_zero_of_no_variables hσ I n]
    simp only [PowerSeries.coeff_C, Nat.succ_ne_zero, ite_false, Nat.cast_zero]

theorem exists_hilbert_numerator_no_variables
    (hσ : Fintype.card σ = 0) (I : Ideal (MvPolynomial σ k)) :
    ∃ P : Polynomial ℤ, sectionHilbertSeries I =
      (P : PowerSeries ℤ) * (PowerSeries.invOneSubPow ℤ (Fintype.card σ)).val := by
  refine ⟨Polynomial.C (Module.finrank k (quotientSection I 0) : ℤ), ?_⟩
  simpa only [hσ, PowerSeries.invOneSubPow_zero, Units.val_one, mul_one,
    Polynomial.coe_C] using sectionHilbertSeries_no_variables hσ I

end PiExponentJets.W64

end OAI

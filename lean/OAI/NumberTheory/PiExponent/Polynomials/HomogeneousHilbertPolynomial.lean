/-
Modification notice for the LogTwo project.
Derived from openai/math (Apache-2.0), revision adc7f1241b42e322a6451854ab7e4b4c146bf78a.
Original source: lean/OAI/NumberTheory/PiExponent/Polynomials/HomogeneousHilbertPolynomial.lean
Changes: Convert module/import declarations to the Lean 4.34 public module format.
See ../../../../../THIRD_PARTY_NOTICES.txt for provenance and the recorded changes.
-/

module

public import OAI.NumberTheory.PiExponent.LocalAlgebra.PositiveDimensionalHilbert
public import OAI.NumberTheory.PiExponent.Polynomials.HomogeneousHilbertExistence

@[expose] public section

namespace OAI

namespace PiExponentJets.W64

universe u v
attribute [local instance] MvPolynomial.gradedAlgebra
variable {k : Type v} [Field k]

theorem rational_hilbert_numerator {σ : Type u} [Fintype σ]
    (I : Ideal (MvPolynomial σ k)) (P : Polynomial ℤ)
    (hP : sectionHilbertSeries I =
      (P : PowerSeries ℤ) * (PowerSeries.invOneSubPow ℤ (Fintype.card σ)).val) :
    rationalSectionHilbertSeries I =
      ((P.map (Int.castRingHom ℚ)) : PowerSeries ℚ) *
        (PowerSeries.invOneSubPow ℚ (Fintype.card σ)).val := by
  rw [rationalSectionHilbertSeries, hP, map_mul, map_int_invOneSubPow,
    ← Polynomial.polynomial_map_coe]

theorem exists_homogeneous_hilbert_polynomial
    (σ : Type u) [Fintype σ] (I : Ideal (MvPolynomial σ k))
    (hI : I.IsHomogeneous (MvPolynomial.homogeneousSubmodule σ k)) :
    ∃ p : Polynomial ℚ, ∃ N : ℕ, ∀ n : ℕ, N < n →
      (Module.finrank k (quotientSection I n) : ℚ) = p.eval (n : ℚ) := by
  obtain ⟨P, hP⟩ := exists_homogeneous_hilbert_numerator σ I hI
  refine ⟨Polynomial.hilbertPoly (P.map (Int.castRingHom ℚ)) (Fintype.card σ),
    (P.map (Int.castRingHom ℚ)).natDegree, ?_⟩
  intro n hn
  rw [← coeff_rationalSectionHilbertSeries, rational_hilbert_numerator I P hP]
  exact Polynomial.coeff_mul_invOneSubPow_eq_hilbertPoly_eval _ hn

theorem exists_homogeneous_hilbert_polynomial_degree_le
    (σ : Type u) [Fintype σ] (hσ : 0 < Fintype.card σ)
    (I : Ideal (MvPolynomial σ k))
    (hI : I.IsHomogeneous (MvPolynomial.homogeneousSubmodule σ k)) :
    ∃ p : Polynomial ℚ,
      (∃ N : ℕ, ∀ n : ℕ, N < n →
        (Module.finrank k (quotientSection I n) : ℚ) = p.eval (n : ℚ)) ∧
      p.natDegree ≤ Fintype.card σ - 1 := by
  obtain ⟨P, hP⟩ := exists_homogeneous_hilbert_numerator σ I hI
  refine ⟨Polynomial.hilbertPoly (P.map (Int.castRingHom ℚ)) (Fintype.card σ),
    ⟨(P.map (Int.castRingHom ℚ)).natDegree, ?_⟩,
    hilbertPolynomial_natDegree_le _ _ hσ⟩
  intro n hn
  rw [← coeff_rationalSectionHilbertSeries, rational_hilbert_numerator I P hP]
  exact Polynomial.coeff_mul_invOneSubPow_eq_hilbertPoly_eval _ hn

end PiExponentJets.W64

end OAI

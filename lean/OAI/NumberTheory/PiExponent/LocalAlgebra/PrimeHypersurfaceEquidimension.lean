/-
Modification notice for the LogTwo project.
Derived from openai/math (Apache-2.0), revision adc7f1241b42e322a6451854ab7e4b4c146bf78a.
Original source: lean/OAI/NumberTheory/PiExponent/LocalAlgebra/PrimeHypersurfaceEquidimension.lean
Changes: Convert module/import declarations to the Lean 4.34 public module format.
See ../../../../../THIRD_PARTY_NOTICES.txt for provenance and the recorded changes.
-/

module

public import OAI.NumberTheory.PiExponent.LocalAlgebra.PrimeHypersurfaceDimension
public import OAI.NumberTheory.PiExponent.Polynomials.PolynomialPrimeDimension

@[expose] public section

namespace OAI

namespace PiExponentJets.W24

variable (k σ : Type*) [Field k] [Finite σ]

theorem minimal_prime_hypersurface_dimension
    (P Q : Ideal (MvPolynomial σ k)) [P.IsPrime]
    (f : MvPolynomial σ k) (hfP : f ∉ P)
    (hQ : Q ∈ (P ⊔ Ideal.span {f}).minimalPrimes)
    (s : ℕ)
    (hdim : ringKrullDim (MvPolynomial σ k ⧸ P) = ((s + 2 : ℕ) : WithBot ℕ∞)) :
    ringKrullDim (MvPolynomial σ k ⧸ Q) = ((s + 1 : ℕ) : WithBot ℕ∞) := by
  let : Q.IsPrime := hQ.1.1
  have hd := polynomial_prime_pair_dimension k σ P Q (le_sup_left.trans hQ.1.2)
  rw [proper_prime_cut_relative_height_eq_one P Q f hfP hQ] at hd
  have he : ringKrullDim (MvPolynomial σ k ⧸ Q) + 1 =
      ((s + 1 : ℕ) : WithBot ℕ∞) + 1 := by
    calc
      ringKrullDim (MvPolynomial σ k ⧸ Q) + 1 =
          1 + ringKrullDim (MvPolynomial σ k ⧸ Q) := add_comm _ _
      _ = ringKrullDim (MvPolynomial σ k ⧸ P) := hd
      _ = ((s + 2 : ℕ) : WithBot ℕ∞) := hdim
      _ = ((s + 1 : ℕ) : WithBot ℕ∞) + 1 := by
        rw [show s + 2 = (s + 1) + 1 by omega, Nat.cast_add, Nat.cast_one]
  exact ENat.WithBot.add_one_cancel.mp he

end PiExponentJets.W24

end OAI

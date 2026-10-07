/-
Modification notice for the LogTwo project.
Derived from openai/math (Apache-2.0), revision adc7f1241b42e322a6451854ab7e4b4c146bf78a.
Original source: lean/OAI/NumberTheory/PiExponent/Polynomials/HomogeneousSections.lean
Changes: Convert module/import declarations to the Lean 4.34 public module format.
See ../../../../../THIRD_PARTY_NOTICES.txt for provenance and the recorded changes.
-/

module

public import Mathlib.Data.Finsupp.Weight
public import Mathlib.LinearAlgebra.Dimension.Constructions
public import Mathlib.LinearAlgebra.Dimension.DivisionRing
public import Mathlib.LinearAlgebra.Dimension.RankNullity
public import Mathlib.LinearAlgebra.Finsupp.Supported
public import Mathlib.RingTheory.MvPolynomial.Homogeneous

@[expose] public section

namespace OAI

namespace PiExponentJets.W64

variable {k σ : Type*} [Field k] [Finite σ]

private theorem finite_exponents_of_degree (n : ℕ) :
    {d : σ →₀ ℕ | d.degree = n}.Finite :=
  (Finsupp.finite_of_degree_le n).subset (fun _ h => le_of_eq h)

noncomputable instance homogeneousSection_finite (n : ℕ) :
    Module.Finite k (MvPolynomial.homogeneousSubmodule σ k n) := by
  rw [MvPolynomial.homogeneousSubmodule_eq_finsupp_supported]
  let : Fintype {d : σ →₀ ℕ | d.degree = n} :=
    (finite_exponents_of_degree n).fintype
  exact Module.Finite.equiv
    (AddMonoidAlgebra.supportedEquivFinsupp (R := k) (S := k)
      {d : σ →₀ ℕ | d.degree = n}).symm

theorem homogeneousSection_finrank (n : ℕ) :
    Module.finrank k (MvPolynomial.homogeneousSubmodule σ k n) =
      Nat.card {d : σ →₀ ℕ | d.degree = n} := by
  rw [MvPolynomial.homogeneousSubmodule_eq_finsupp_supported]
  let : Fintype {d : σ →₀ ℕ | d.degree = n} :=
    (finite_exponents_of_degree n).fintype
  calc
    _ = Module.finrank k ({d : σ →₀ ℕ | d.degree = n} →₀ k) :=
      (AddMonoidAlgebra.supportedEquivFinsupp (R := k) (S := k)
        {d : σ →₀ ℕ | d.degree = n}).finrank_eq
    _ = Nat.card {d : σ →₀ ℕ | d.degree = n} := by
      simp only [Module.finrank_finsupp_self, Nat.card_eq_fintype_card]

noncomputable def homogeneousMultiply {d : ℕ} (f : MvPolynomial σ k)
    (hf : f.IsHomogeneous d) (n : ℕ) :
    MvPolynomial.homogeneousSubmodule σ k n →ₗ[k]
      MvPolynomial.homogeneousSubmodule σ k (n + d) where
  toFun x := ⟨x.1 * f, x.2.mul hf⟩
  map_add' x y := by apply Subtype.ext; exact add_mul _ _ _
  map_smul' c x := by apply Subtype.ext; exact smul_mul_assoc _ _ _

omit [Finite σ] in
theorem homogeneousMultiply_injective {d : ℕ} (f : MvPolynomial σ k)
    (hf : f.IsHomogeneous d) (hf0 : f ≠ 0) (n : ℕ) :
    Function.Injective (homogeneousMultiply f hf n) := by
  intro x y h
  apply Subtype.ext
  exact mul_right_cancel₀ hf0 (congrArg Subtype.val h)

theorem homogeneousCokernel_finrank_add {d : ℕ} (f : MvPolynomial σ k)
    (hf : f.IsHomogeneous d) (hf0 : f ≠ 0) (n : ℕ) :
    Module.finrank k
        (MvPolynomial.homogeneousSubmodule σ k (n + d) ⧸
          LinearMap.range (homogeneousMultiply f hf n)) +
      Module.finrank k (MvPolynomial.homogeneousSubmodule σ k n) =
      Module.finrank k (MvPolynomial.homogeneousSubmodule σ k (n + d)) := by
  have hi := homogeneousMultiply_injective f hf hf0 n
  simpa only [LinearMap.finrank_range_of_inj hi] using
    (LinearMap.range (homogeneousMultiply f hf n)).finrank_quotient_add_finrank

end PiExponentJets.W64

end OAI

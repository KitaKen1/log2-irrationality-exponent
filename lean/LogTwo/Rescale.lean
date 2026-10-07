module

public import Mathlib.Algebra.MvPolynomial.Eval
public import Mathlib.Data.Fintype.BigOperators

@[expose] public section

/-! Diagonal variable substitution, with an exact coefficient formula. -/
namespace LogTwo.Polynomial

open MvPolynomial
noncomputable section

variable {σ : Type*}

def rescale (a : σ → ℚ) : MvPolynomial σ ℚ →+* MvPolynomial σ ℚ :=
  eval₂Hom C (fun i => C (a i) * X i)

@[simp] theorem rescale_C (a : σ → ℚ) (b : ℚ) : rescale a (C b) = C b := by
  simp [rescale]

@[simp] theorem rescale_X (a : σ → ℚ) (i : σ) : rescale a (X i) = C (a i) * X i := by
  simp [rescale]

variable [Fintype σ]

theorem rescale_monomial (a : σ → ℚ) (d : σ →₀ ℕ) (b : ℚ) :
    rescale a (monomial d b) = monomial d (b * ∏ i, a i ^ d i) := by
  rw [rescale, eval₂Hom_monomial, monomial_eq]
  rw [Finsupp.prod_fintype d (fun i k => (C (a i) * X i) ^ k) (by intro i; simp)]
  rw [Finsupp.prod_fintype d (fun i k => (X i : MvPolynomial σ ℚ) ^ k) (by intro i; simp)]
  simp only [mul_pow, ← map_pow,
    Finset.prod_mul_distrib, ← map_prod, map_mul, mul_assoc]

theorem coeff_rescale (a : σ → ℚ) (P : MvPolynomial σ ℚ) (d : σ →₀ ℕ) :
    (rescale a P).coeff d = P.coeff d * ∏ i, a i ^ d i := by
  classical
  induction P using MvPolynomial.induction_on' with
  | add p q hp hq => simp [map_add, hp, hq, add_mul]
  | monomial e b =>
    rw [rescale_monomial]
    by_cases he : e = d
    · subst e; simp
    · simp [MvPolynomial.coeff_monomial, he]

end
end LogTwo.Polynomial

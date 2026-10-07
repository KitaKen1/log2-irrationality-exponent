/-
Copyright 2026 Kenta Kitamura (KitaKen1).
-/
module

public import FormalConjecturesUtil

/-!
# The irrationality exponent of the natural logarithm of 2

Determine the irrationality exponent of $\log 2$, where $\log$ is the natural
logarithm. Marcovecchio [Ma09] obtained the upper bound $3.574\ldots$.
Bugeaud and Kim [BK26, Section 1] record its exact value as unknown.
The statement below gives the value $2$, with a Lean formalization by
Kenta Kitamura [Ki26].

*References:*
- [Ma09] R. Marcovecchio, *The Rhin–Viola method for log 2* (2009),
  [institutional record](https://ricerca.unich.it/handle/11564/648605).
- [BK26] Y. Bugeaud and D. H. Kim, *On the b-ary expansion of a real number whose
  irrationality exponent is close to 2*,
  [arXiv:2510.02059v2](https://arxiv.org/abs/2510.02059v2) (2026), Section 1.
- [Ki26] Kenta Kitamura, *log2-irrationality-exponent*, Lean 4 formalization (2026),
  [GitHub repository](https://github.com/KitaKen1/log2-irrationality-exponent).
-/

@[expose] public section

namespace LogTwo

/-- The supremum of positive $\mu$ for which infinitely many reduced rationals
$p/q$, with $q > 1$, satisfy $0 < |x-p/q| < 1/q^\mu$.
This real-valued definition represents the irrationality exponent when the
set of such exponents is nonempty and bounded above. -/
noncomputable def irrationalityExponent (x : ℝ) : ℝ :=
  sSup {μ : ℝ | 0 < μ ∧ Set.Infinite
    {r : ℚ | 1 < r.den ∧ 0 < |x - (r : ℝ)| ∧
      |x - (r : ℝ)| < 1 / (r.den : ℝ) ^ μ}}

/-- What is the irrationality exponent of the natural logarithm of $2$?
The answer is $2$ [Ki26]; see [BK26, Section 1] for the historical question. -/
@[category research solved, AMS 11]
theorem irrationalityExponent_log_two :
    irrationalityExponent (Real.log 2) = answer(2) := by
  sorry

end LogTwo

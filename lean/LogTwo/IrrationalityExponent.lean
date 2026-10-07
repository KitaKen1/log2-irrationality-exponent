/- Copyright 2026 Kenta Kitamura. Licensed under Apache-2.0. -/
module
public import Mathlib

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

end LogTwo

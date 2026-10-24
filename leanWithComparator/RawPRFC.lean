-- Generated from the pinned PR; mathematical namespace body is verbatim.
import Mathlib
import FormalConjecturesUtil.Answer
import FormalConjecturesUtil.Attributes.Basic

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
Its exact value is listed as unknown in [BK26, Section 1]. The answer is $2$ [Ki26]. -/
@[category research solved, AMS 11,
    formal_proof using lean4 at "https://github.com/KitaKen1/log2-irrationality-exponent/blob/93a66a6c6b69e5e2f7775d791fd4943f4b1cf671/lean/LogTwo/Target.lean#L45-L48"]
theorem irrationalityExponent_log_two :
    irrationalityExponent (Real.log 2) = answer(2) := by
  sorry

end LogTwo

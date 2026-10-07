module

public import Mathlib.Analysis.SpecialFunctions.Complex.Log
public import Mathlib.Tactic

@[expose] public section

/-! Exact analytic identity retaining the factor 2^(j*h) inside each column
function. It is a prospective input to the Taylor/collision argument, not a
determinant upper bound or a transfer of a bound for the fixed-Y matrix. -/
namespace LogTwo.Analysis
noncomputable section

/-- At a non-periodic center the exponential factor must be retained. -/
theorem scaled_log_monomial_identity (b center : ℂ) (h d : ℕ)
    {z : ℂ} (hz : 1+z ≠ 0) :
    b * Complex.exp center ^ h * (1+z)^h * (center+Complex.log (1+z))^d =
      b * Complex.exp ((h : ℂ)*(center+Complex.log (1+z))) *
        (center+Complex.log (1+z))^d := by
  rw [Complex.exp_nat_mul, Complex.exp_add, Complex.exp_log hz, mul_pow]
  ring

theorem exp_logTwo_center (j : ℕ) :
    Complex.exp ((j : ℂ)*(Real.log 2 : ℂ)) = (2 : ℂ)^j := by
  rw [Complex.exp_nat_mul, ← Complex.ofReal_exp, Real.exp_log (by norm_num : (0 : ℝ) < 2)]
  norm_num

/-- The j-dependent matrix factor is exactly the exponential at j*log(2).
This preserves the common entire column function needed for cancellation. -/
theorem logTwo_scaled_log_monomial_identity (b : ℂ) (j h d : ℕ)
    {z : ℂ} (hz : 1+z ≠ 0) :
    b * (2 : ℂ)^(j*h) * (1+z)^h *
        ((j : ℂ)*(Real.log 2 : ℂ)+Complex.log (1+z))^d =
      b * Complex.exp ((h : ℂ)*((j : ℂ)*(Real.log 2 : ℂ)+Complex.log (1+z))) *
        ((j : ℂ)*(Real.log 2 : ℂ)+Complex.log (1+z))^d := by
  have hidentity := scaled_log_monomial_identity b ((j : ℂ)*(Real.log 2 : ℂ)) h d hz
  rw [exp_logTwo_center, ← pow_mul] at hidentity
  exact hidentity

end
end LogTwo.Analysis

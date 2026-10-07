module

public import LogTwo.Parameters
public import Mathlib.Analysis.SpecificLimits.Normed

@[expose] public section

/-! Growth estimates used by the ceiling-based dimension and denominator choices. -/
namespace LogTwo.Parameters

open Filter
open scoped Topology

theorem geometric_over_succ_tendsto {r : ℝ} (hr : 1 < r) :
    Tendsto (fun m : ℕ => r ^ m / ((m : ℝ) + 1)) atTop atTop := by
  have hz : Tendsto (fun m : ℕ => ((m : ℝ) + 1) / r ^ m) atTop (𝓝 0) := by
    have h1 := tendsto_pow_const_div_const_pow_of_one_lt 1 hr
    have h0 := tendsto_pow_const_div_const_pow_of_one_lt 0 hr
    simpa only [pow_one, pow_zero, zero_add, add_div] using h1.add h0
  have hp : ∀ m : ℕ, (0 : ℝ) < ((m : ℝ) + 1) / r ^ m := by
    intro m
    have : 0 < r := by linarith
    positivity
  have hz' : Tendsto (fun m : ℕ => ((m : ℝ) + 1) / r ^ m) atTop (𝓝[>] 0) :=
    tendsto_nhdsWithin_iff.mpr ⟨hz, Filter.Eventually.of_forall hp⟩
  have hinv := hz'.inv_tendsto_nhdsGT_zero
  change Tendsto (fun m : ℕ => (((m : ℝ) + 1) / r ^ m)⁻¹) atTop atTop at hinv
  simpa only [inv_div] using hinv

/-- Three growth/decay facts supplied by the explicit scalar choices. -/
theorem dimension_growth (n : ℕ) (hn : 1 ≤ n) :
    Tendsto (fun m : ℕ => ((c (delta n) * b (delta n) : ℚ) : ℝ) ^ m)
      atTop (𝓝 0) ∧
    Tendsto (fun m : ℕ => ((c (delta n) * theta (delta n) / b (delta n) : ℚ) : ℝ) ^ m)
      atTop atTop ∧
    Tendsto (fun m : ℕ => ((b (delta n) / a (delta n) : ℚ) : ℝ) ^ m / ((m : ℝ) + 1))
      atTop atTop := by
  have hs := shape n hn
  have hr := growth_ratios n hn
  have hb : 0 < b (delta n) := hs.theta_pos.trans (hs.theta_lt_a.trans hs.a_lt_b)
  have hc : 0 < c (delta n) := by linarith [hs.one_lt_c]
  refine ⟨?_, ?_, ?_⟩
  · apply tendsto_pow_atTop_nhds_zero_of_lt_one
    · exact_mod_cast (mul_pos hc hb).le
    · exact_mod_cast hs.cb_lt_one
  · apply tendsto_pow_atTop_atTop_of_one_lt
    exact_mod_cast hr.1
  · apply geometric_over_succ_tendsto
    exact_mod_cast hr.2

/-- Choosing v0 by this formula fixes the volume ratio at one half. -/
theorem volume_ratio_half {K w0 θ : ℚ} (hK : K ≠ 0) (hw : w0 ≠ 0)
    (hθ : θ ≠ 0) (m : ℕ) :
    K * (w0 / (2 * K * θ ^ m * w0)) * θ ^ m = 1 / 2 := by
  field_simp

end LogTwo.Parameters

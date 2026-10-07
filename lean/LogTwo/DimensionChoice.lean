module

public import LogTwo.Dimension
public import Mathlib.Algebra.Order.Floor.Ring

@[expose] public section

/-! Ceiling-based choices avoid a separate eventual lower bound for the floor. -/
namespace LogTwo.Parameters

open Filter
open scoped Topology

def centerCount (C : ℚ) (m : ℕ) : ℕ := ⌈C ^ m⌉₊
def horizontalWeight (B : ℚ) (m : ℕ) : ℚ := (B ^ m)⁻¹
def verticalWeight (θ B C : ℚ) (m : ℕ) : ℚ :=
  2 * (centerCount C m : ℚ) * θ ^ m * horizontalWeight B m

theorem centerCount_bounds {C : ℚ} (hC : 1 ≤ C) (m : ℕ) :
    C ^ m ≤ (centerCount C m : ℚ) ∧ (centerCount C m : ℚ) ≤ 2 * C ^ m := by
  have hp : 1 ≤ C ^ m := one_le_pow₀ hC
  refine ⟨Nat.le_ceil _, ?_⟩
  have ht := Nat.ceil_lt_add_one (show 0 ≤ C ^ m by linarith)
  dsimp [centerCount]
  linarith

theorem centerCount_pos {C : ℚ} (hC : 1 ≤ C) (m : ℕ) : 0 < centerCount C m := by
  have hb := (centerCount_bounds hC m).1
  have hp : 1 ≤ C ^ m := one_le_pow₀ hC
  have : (0 : ℚ) < centerCount C m := by linarith
  exact_mod_cast this

theorem horizontalWeight_pos {B : ℚ} (hB : 0 < B) (m : ℕ) :
    0 < horizontalWeight B m := by unfold horizontalWeight; positivity

theorem verticalWeight_pos {θ B C : ℚ} (hθ : 0 < θ) (hB : 0 < B)
    (hC : 1 ≤ C) (m : ℕ) : 0 < verticalWeight θ B C m := by
  have hK := centerCount_pos hC m
  have hw := horizontalWeight_pos hB m
  unfold verticalWeight
  positivity

theorem count_over_horizontal_le {B C : ℚ} (hB : 0 < B) (hC : 1 ≤ C) (m : ℕ) :
    (centerCount C m : ℚ) / horizontalWeight B m ≤ 2 * (C * B) ^ m := by
  have hb := mul_le_mul_of_nonneg_right (centerCount_bounds hC m).2
    (pow_nonneg hB.le m)
  simpa [horizontalWeight, div_inv_eq_mul, mul_pow, mul_assoc] using hb

theorem verticalWeight_lower {θ B C : ℚ} (hθ : 0 < θ) (hB : 0 < B)
    (hC : 1 ≤ C) (m : ℕ) :
    2 * (C * θ / B) ^ m ≤ verticalWeight θ B C m := by
  have hb := mul_le_mul_of_nonneg_right (centerCount_bounds hC m).1
    (show 0 ≤ 2 * θ ^ m * (B ^ m)⁻¹ by positivity)
  simpa [verticalWeight, horizontalWeight, div_pow, mul_pow, div_eq_mul_inv,
    mul_comm, mul_left_comm, mul_assoc] using hb

theorem count_over_horizontal_tendsto {B C : ℚ} (hB : 0 < B) (hC : 1 ≤ C)
    (hCB : C * B < 1) :
    Tendsto (fun m => ((centerCount C m : ℚ) / horizontalWeight B m : ℚ) : ℕ → ℝ)
      atTop (𝓝 0) := by
  have hz : Tendsto (fun m : ℕ => 2 * ((C * B : ℚ) : ℝ) ^ m) atTop (𝓝 0) := by
    have hh := tendsto_pow_atTop_nhds_zero_of_lt_one
      (show (0 : ℝ) ≤ ((C * B : ℚ) : ℝ) by exact_mod_cast mul_nonneg (by linarith) hB.le)
      (show ((C * B : ℚ) : ℝ) < 1 by exact_mod_cast hCB)
    simpa using hh.const_mul 2
  apply squeeze_zero _ _ hz
  · intro m
    exact_mod_cast (div_nonneg (Nat.cast_nonneg _) (horizontalWeight_pos hB m).le)
  · intro m
    exact_mod_cast count_over_horizontal_le hB hC m

theorem verticalWeight_tendsto {θ B C : ℚ} (hθ : 0 < θ) (hB : 0 < B)
    (hC : 1 ≤ C) (hr : 1 < C * θ / B) :
    Tendsto (fun m => (verticalWeight θ B C m : ℝ)) atTop atTop := by
  have hp := tendsto_pow_atTop_atTop_of_one_lt
    (show (1 : ℝ) < ((C * θ / B : ℚ) : ℝ) by exact_mod_cast hr)
  apply tendsto_atTop_mono _ hp
  intro m
  have hlow := verticalWeight_lower hθ hB hC m
  have hpos : 0 ≤ (C * θ / B) ^ m := pow_nonneg (by linarith) m
  exact_mod_cast (show (C * θ / B) ^ m ≤ verticalWeight θ B C m by linarith)

theorem dimension_over_vertical_tendsto {θ B C : ℚ} (hθ : 0 < θ) (hB : 0 < B)
    (hC : 1 ≤ C) (hr : 1 < C * θ / B) :
    Tendsto (fun m : ℕ => (m : ℝ) / (verticalWeight θ B C m : ℝ)) atTop (𝓝 0) := by
  have hz := tendsto_pow_const_div_const_pow_of_one_lt 1
    (show (1 : ℝ) < ((C * θ / B : ℚ) : ℝ) by exact_mod_cast hr)
  simp only [pow_one] at hz
  apply squeeze_zero _ _ hz
  · intro m
    have hv : (0 : ℝ) < (verticalWeight θ B C m : ℝ) := by
      exact_mod_cast verticalWeight_pos hθ hB hC m
    positivity
  · intro m
    have hp : (0 : ℝ) < ((C * θ / B : ℚ) : ℝ) ^ m := by
      have : (0 : ℝ) < ((C * θ / B : ℚ) : ℝ) := by exact_mod_cast (show 0 < C * θ / B by linarith)
      positivity
    apply div_le_div_of_nonneg_left (Nat.cast_nonneg _) hp
    have hl := verticalWeight_lower hθ hB hC m
    have hq : 0 ≤ (C * θ / B) ^ m := pow_nonneg (by linarith) m
    exact_mod_cast (show (C * θ / B) ^ m ≤ verticalWeight θ B C m by linarith)

/-- All dimension requirements can be imposed at once, including any fixed
multiple of the arithmetic term `m/v₀`. The constants are chosen before `m`. -/
theorem exists_dimension (n : ℕ) (hn : 1 ≤ n) (ε A D R : ℝ) (hε : 0 < ε)
    (m₀ : ℕ) : ∃ m : ℕ, m₀ ≤ m ∧
      ((centerCount (c (delta n)) m : ℚ) / horizontalWeight (b (delta n)) m : ℝ) < ε ∧
      A * ((m : ℝ) / (verticalWeight (theta (delta n)) (b (delta n)) (c (delta n)) m : ℝ)) < ε ∧
      D < (verticalWeight (theta (delta n)) (b (delta n)) (c (delta n)) m : ℝ) ∧
      R < ((b (delta n) / a (delta n) : ℚ) : ℝ) ^ m / ((m : ℝ) + 1) := by
  have hs := shape n hn
  have hb := hs.theta_pos.trans (hs.theta_lt_a.trans hs.a_lt_b)
  have hr := (growth_ratios n hn).1
  have hc := count_over_horizontal_tendsto hb hs.one_lt_c.le hs.cb_lt_one
  have hm := dimension_over_vertical_tendsto hs.theta_pos hb hs.one_lt_c.le hr
  have hv := verticalWeight_tendsto hs.theta_pos hb hs.one_lt_c.le hr
  have hA : Tendsto (fun m : ℕ => A * ((m : ℝ) /
      (verticalWeight (theta (delta n)) (b (delta n)) (c (delta n)) m : ℝ)))
      atTop (𝓝 0) := by simpa using hm.const_mul A
  have he := (hc.eventually_lt_const hε).and (hA.eventually_lt_const hε)
  have he' := he.and ((hv.eventually (eventually_gt_atTop D)).and
    ((dimension_growth n hn).2.2.eventually (eventually_gt_atTop R)))
  obtain ⟨m, hm₀, ⟨hmc, hmA⟩, hmD, hmR⟩ :=
    ((eventually_ge_atTop m₀).and he').exists
  exact ⟨m, hm₀, by exact_mod_cast hmc, hmA, hmD, hmR⟩

theorem chosen_volume_ratio {θ B C : ℚ} (hθ : 0 < θ) (hB : 0 < B)
    (hC : 1 ≤ C) (m : ℕ) :
    (centerCount C m : ℚ) * (horizontalWeight B m / verticalWeight θ B C m) * θ ^ m =
      1 / 2 := by
  apply volume_ratio_half
  · exact_mod_cast (centerCount_pos hC m).ne'
  · exact (horizontalWeight_pos hB m).ne'
  · exact hθ.ne'

end LogTwo.Parameters

module

public import LogTwo.DimensionChoice
public import LogTwo.ApproximationSelection
public import LogTwo.ArithmeticEstimate

@[expose] public section

/-! Construct the actual weights used by the matrix and make the arithmetic
error small. Interpolation and the analytic upper bound are still separate goals. -/
namespace LogTwo

open Parameters Arithmetic Interpolation
noncomputable section

theorem ceilLogWeight_pos {q : ℕ} (hq : 2 ≤ q) : 0 < ceilLogWeight q := by
  have hlog : 0 < Real.log (q : ℝ) :=
    Real.log_pos (by exact_mod_cast (show 1 < q by omega))
  exact_mod_cast hlog.trans_le (ceilLogWeight_bounds q).1

def chosenWeights (n : ℕ) (hn : 1 ≤ n) (m : ℕ) (q : Fin m → ℕ)
    (hq : ∀ i, 2 ≤ q i) : Weights m where
  K := centerCount (c (delta n)) m
  w0 := horizontalWeight (b (delta n)) m
  v0 := verticalWeight (theta (delta n)) (b (delta n)) (c (delta n)) m
  w := fun i => ceilLogWeight (q i)
  theta := theta (delta n)
  w0_pos := horizontalWeight_pos
    ((shape n hn).theta_pos.trans ((shape n hn).theta_lt_a.trans (shape n hn).a_lt_b)) m
  v0_pos := verticalWeight_pos (shape n hn).theta_pos
    ((shape n hn).theta_pos.trans ((shape n hn).theta_lt_a.trans (shape n hn).a_lt_b))
    (shape n hn).one_lt_c.le m
  w_pos := fun i => ceilLogWeight_pos (hq i)
  theta_pos := (shape n hn).theta_pos
  theta_lt_one := (shape n hn).theta_lt_a.trans
    ((shape n hn).a_lt_b.trans (shape n hn).b_lt_one)

theorem arithmeticError_le_uniform {m : ℕ} (w : Weights m) (F : ℚ) (W : ℝ)
    (hW : 0 < W) (hw : ∀ i, W ≤ (w.w i : ℝ)) :
    arithmeticError w F W ≤ lcmConstant * (F : ℝ) * m / (w.v0 : ℝ) +
      (lcmConstant * m + (w.theta : ℝ)) / W := by
  have hs : (∑ i, 1 / (w.w i : ℝ)) ≤ (m : ℝ) / W := by
    calc
      _ ≤ ∑ _i : Fin m, (1 : ℝ) / W := Finset.sum_le_sum
        (fun i _ => one_div_le_one_div_of_le hW (hw i))
      _ = _ := by simp [div_eq_mul_inv]
  have hh := mul_le_mul_of_nonneg_left hs lcmConstant_pos.le
  unfold arithmeticError
  calc
    _ ≤ lcmConstant * (F : ℝ) * m / (w.v0 : ℝ) +
        lcmConstant * ((m : ℝ) / W) + (w.theta : ℝ) / W := by linarith
    _ = _ := by ring

/-- For any bad approximation family, make the actual arithmetic error less
than ε. The extra threshold may depend on m and every previous denominator.
This does not construct a nonzero minor or an analytic estimate. -/
theorem exists_small_arithmetic_parameters (n : ℕ) (hn : 1 ≤ n) {x ν : ℝ}
    (hbad : UnboundedApproximations x ν) (ε : ℝ) (hε : 0 < ε)
    (threshold : (m i : ℕ) → (Fin i → ℕ) → ℝ) :
    ∃ (m : ℕ) (p : ℕ → ℤ) (q : ℕ → ℕ) (hq : ∀ i, 2 ≤ q i) (W : ℝ),
      1 ≤ m ∧ 0 < W ∧
      (∀ i, W ≤ (ceilLogWeight (q i) : ℝ)) ∧
      (∀ i, threshold m i (fun j => q j) < Real.log (q i)) ∧
      (∀ i, |x - (p i : ℝ) / q i| ≤ (q i : ℝ) ^ (-ν)) ∧
      arithmeticError (chosenWeights n hn m (fun i => q i) (fun i => hq i))
        (truncationFactor n) W < ε := by
  have he : 0 < ε / 2 := by positivity
  obtain ⟨m, hm, _, hdim, _, _⟩ := exists_dimension n hn (ε / 2)
    (lcmConstant * (truncationFactor n : ℝ)) 0 0 he 1
  let S : ℝ := lcmConstant * m + (theta (delta n) : ℝ)
  have hS : 0 < S := by
    have hθ : (0 : ℝ) < (theta (delta n) : ℝ) := by exact_mod_cast (shape n hn).theta_pos
    dsimp [S]
    exact add_pos_of_nonneg_of_pos (mul_nonneg lcmConstant_pos.le (Nat.cast_nonneg _)) hθ
  let W : ℝ := S / (ε / 2) + 1
  have hW : 0 < W := by dsimp [W]; positivity
  have hsmall : S / W < ε / 2 := by
    apply (div_lt_iff₀ hW).mpr
    dsimp [W]
    rw [mul_add, mul_div_cancel₀ _ he.ne', mul_one]
    linarith
  obtain ⟨p, q, hq⟩ := exists_sequential_approximations hbad
    (fun i previous => max W (threshold m i previous))
  have hq2 : ∀ i, 2 ≤ q i := fun i => (hq i).1
  have hweights : ∀ i, W ≤ (ceilLogWeight (q i) : ℝ) := by
    intro i
    exact ((le_max_left _ _).trans_lt (hq i).2.1).le.trans (ceilLogWeight_bounds _).1
  refine ⟨m, p, q, hq2, W, hm, hW, hweights,
    (fun i => (le_max_right _ _).trans_lt (hq i).2.1), (fun i => (hq i).2.2), ?_⟩
  have hb := arithmeticError_le_uniform
    (chosenWeights n hn m (fun i => q i) (fun i => hq2 i))
    (truncationFactor n) W hW (fun i => hweights i)
  change arithmeticError _ _ W ≤ lcmConstant * (truncationFactor n : ℝ) * m /
    (verticalWeight (theta (delta n)) (b (delta n)) (c (delta n)) m : ℝ) + S / W at hb
  have heq : lcmConstant * (truncationFactor n : ℝ) * m /
    (verticalWeight (theta (delta n)) (b (delta n)) (c (delta n)) m : ℝ) =
    (lcmConstant * (truncationFactor n : ℝ)) * ((m : ℝ) /
    (verticalWeight (theta (delta n)) (b (delta n)) (c (delta n)) m : ℝ)) := by ring
  rw [heq] at hb
  linarith

end
end LogTwo

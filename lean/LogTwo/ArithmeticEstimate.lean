module

public import LogTwo.LcmBound

@[expose] public section

/-! Normalized arithmetic estimate, with the row saving preserved. -/
namespace LogTwo.Arithmetic

open LogTwo.Interpolation
noncomputable section

def ceilLogWeight (q : ℕ) : ℚ := (⌈Real.log (q : ℝ)⌉₊ : ℚ)

theorem ceilLogWeight_bounds (q : ℕ) :
    Real.log (q : ℝ) ≤ (ceilLogWeight q : ℝ) ∧
    (ceilLogWeight q : ℝ) - 1 ≤ Real.log (q : ℝ) := by
  simp only [ceilLogWeight, Rat.cast_natCast]
  exact ⟨Nat.le_ceil _, by linarith [Nat.ceil_lt_add_one (Real.log_natCast_nonneg q)]⟩

def rowWeight {m : ℕ} (w : Weights m) (r : Row m) : ℝ :=
  ∑ i, (w.w i : ℝ) * (r.beta i : ℝ)

theorem rowWeight_lt {m : ℕ} (w : Weights m) (H : ℚ) (r : Row m)
    (hr : AdmissibleRow w H r) : rowWeight w r < (w.theta : ℝ) * (H : ℝ) := by
  have hz : (0 : ℚ) ≤ w.v0 * r.s := mul_nonneg w.v0_pos.le (Nat.cast_nonneg _)
  have hh : (∑ i, w.w i * r.beta i) / w.theta < H := by
    have := hr.2
    linarith
  have hh' := (div_lt_iff₀ w.theta_pos).mp hh
  simpa only [rowWeight, Rat.cast_sum, Rat.cast_mul, Rat.cast_natCast, mul_comm] using
    (show ((∑ i, w.w i * r.beta i : ℚ) : ℝ) < ((H * w.theta : ℚ) : ℝ) by exact_mod_cast hh')

theorem columnQCost_le_height {m : ℕ} (w : Weights m) (H : ℚ) (q : Fin m → ℕ)
    (hlog : ∀ i, Real.log (q i : ℝ) ≤ (w.w i : ℝ))
    (c : Column m) (hc : AdmissibleColumn w H c) : columnQCost q c ≤ (H : ℝ) := by
  have hh : (∑ i, w.w i * c.alpha i) ≤ H := by
    have hz : (0 : ℚ) ≤ w.w0 * c.h := mul_nonneg w.w0_pos.le (Nat.cast_nonneg _)
    dsimp [AdmissibleColumn] at hc
    linarith
  calc
    _ ≤ ∑ i, (c.alpha i : ℝ) * (w.w i : ℝ) :=
      Finset.sum_le_sum (fun i _ => mul_le_mul_of_nonneg_left (hlog i) (Nat.cast_nonneg _))
    _ ≤ _ := by
      simpa only [Rat.cast_sum, Rat.cast_mul, Rat.cast_natCast, mul_comm] using
        (show ((∑ i, w.w i * c.alpha i : ℚ) : ℝ) ≤ (H : ℝ) by exact_mod_cast hh)

theorem rowLogSaving_lower {m : ℕ} (w : Weights m) (H : ℚ) (q : Fin m → ℕ)
    (hlog : ∀ i, (w.w i : ℝ) - 1 ≤ Real.log (q i : ℝ))
    (wmin : ℝ) (hmin : 0 < wmin) (hweights : ∀ i, wmin ≤ (w.w i : ℝ))
    (r : Row m) (hr : AdmissibleRow w H r) :
    rowWeight w r - (w.theta : ℝ) * (H : ℝ) / wmin ≤ rowLogSaving q r := by
  have hcount : wmin * ∑ i, (r.beta i : ℝ) ≤ rowWeight w r := by
    rw [Finset.mul_sum]
    exact Finset.sum_le_sum (fun i _ => mul_le_mul_of_nonneg_right (hweights i) (Nat.cast_nonneg _))
  have hcount' : (∑ i, (r.beta i : ℝ)) ≤ (w.theta : ℝ) * (H : ℝ) / wmin := by
    apply (le_div_iff₀ hmin).mpr
    rw [mul_comm]
    exact hcount.trans (rowWeight_lt w H r hr).le
  have hsave : rowWeight w r - (∑ i, (r.beta i : ℝ)) ≤ rowLogSaving q r := by
    calc
      _ = ∑ i, (r.beta i : ℝ) * ((w.w i : ℝ) - 1) := by
        simp [rowWeight, mul_sub, Finset.sum_sub_distrib, mul_comm]
      _ ≤ _ := Finset.sum_le_sum (fun i _ =>
        mul_le_mul_of_nonneg_left (hlog i) (Nat.cast_nonneg _))
  linarith

theorem fullRowMinor_size_pos {m : ℕ} {w : Weights m} {H : ℚ}
    {r : Fin m → ℚ} {T : Fin m → ℕ} (hK : 0 < w.K) (hH : 0 < H)
    (minor : FullRowMinor w H r T) : 0 < minor.size := by
  have hrow : AdmissibleRow w H (valueRow m 0) := by
    refine ⟨hK, ?_⟩
    simpa [valueRow] using hH
  obtain ⟨i, _⟩ := minor.all_rows (valueRow m 0) hrow
  exact Nat.zero_lt_of_lt i.isLt

def averageRowWeight {m : ℕ} {w : Weights m} {H : ℚ}
    {r : Fin m → ℚ} {T : Fin m → ℕ} (minor : FullRowMinor w H r T) : ℝ :=
  (∑ i, rowWeight w (minor.rows i)) / ((minor.size : ℝ) * (H : ℝ))

theorem averageRowWeight_bounds {m : ℕ} {w : Weights m} {H : ℚ}
    {r : Fin m → ℚ} {T : Fin m → ℕ} (hK : 0 < w.K) (hH : 0 < H)
    (minor : FullRowMinor w H r T) :
    0 ≤ averageRowWeight minor ∧ averageRowWeight minor < (w.theta : ℝ) := by
  have hsize := fullRowMinor_size_pos hK hH minor
  have hM : (0 : ℝ) < minor.size := by exact_mod_cast hsize
  have hH' : (0 : ℝ) < H := by exact_mod_cast hH
  constructor
  · apply div_nonneg _ (mul_pos hM hH').le
    apply Finset.sum_nonneg
    intro i _
    apply Finset.sum_nonneg
    intro k _
    exact mul_nonneg (by exact_mod_cast (w.w_pos k).le) (Nat.cast_nonneg _)
  · apply (div_lt_iff₀ (mul_pos hM hH')).mpr
    calc
      _ < ∑ _i : Fin minor.size, (w.theta : ℝ) * (H : ℝ) := by
        apply Finset.sum_lt_sum
        · intro i _; exact (rowWeight_lt w H _ (minor.row_valid i)).le
        · exact ⟨⟨0, hsize⟩, Finset.mem_univ _, rowWeight_lt w H _ (minor.row_valid _)⟩
      _ = _ := by simp; ring

def arithmeticError {m : ℕ} (w : Weights m) (F : ℚ) (wmin : ℝ) : ℝ :=
  lcmConstant * (F : ℝ) * m / (w.v0 : ℝ) +
    lcmConstant * ∑ i, 1 / (w.w i : ℝ) + (w.theta : ℝ) / wmin

/-- Variant of (3.5), using the explicit Mathlib constant log 4 + 4. -/
theorem fullRowMinor_normalized_arithmetic_bound {m : ℕ} {w : Weights m} {H F : ℚ}
    (p : Fin m → ℤ) (q : Fin m → ℕ) (hq : ∀ i, q i ≠ 0)
    (hK : 0 < w.K) (hH : 0 < H) (hF : 0 ≤ F)
    (hlog : ∀ i, Real.log (q i : ℝ) ≤ (w.w i : ℝ))
    (hlog' : ∀ i, (w.w i : ℝ) - 1 ≤ Real.log (q i : ℝ))
    (wmin : ℝ) (hmin : 0 < wmin) (hweights : ∀ i, wmin ≤ (w.w i : ℝ))
    (minor : FullRowMinor w H (rationalPoint p q) (truncationOrders w F)) :
    -(1 - averageRowWeight minor) - arithmeticError w F wmin ≤
      Real.log |(minor.matrix.det : ℝ)| / ((minor.size : ℝ) * (H : ℝ)) := by
  have hM : (0 : ℝ) < minor.size := by exact_mod_cast fullRowMinor_size_pos hK hH minor
  have hH' : (0 : ℝ) < H := by exact_mod_cast hH
  have hs : (∑ i, rowWeight w (minor.rows i)) -
      (minor.size : ℝ) * ((w.theta : ℝ) * (H : ℝ) / wmin) ≤
      ∑ i, rowLogSaving q (minor.rows i) := by
    calc
      _ = ∑ i, (rowWeight w (minor.rows i) - (w.theta : ℝ) * (H : ℝ) / wmin) := by
        simp [Finset.sum_sub_distrib]
      _ ≤ _ := Finset.sum_le_sum (fun i _ =>
        rowLogSaving_lower w H q hlog' wmin hmin hweights _ (minor.row_valid i))
  have hc : (∑ j, columnQCost q (minor.columns j)) ≤ (minor.size : ℝ) * (H : ℝ) := by
    calc
      _ ≤ ∑ j : Fin minor.size, (H : ℝ) := Finset.sum_le_sum
        (fun j _ => columnQCost_le_height w H q hlog _ (minor.column_valid j))
      _ = _ := by simp
  have hd := mul_le_mul_of_nonneg_left
    (truncation_denominatorBudget_le w H F hH.le hF) hM.le
  have hb := fullRowMinor_uniform_log_bound p q (truncationOrders w F) hq minor
  apply (le_div_iff₀ (mul_pos hM hH')).mpr
  dsimp [averageRowWeight, arithmeticError]
  rw [sub_mul, neg_mul, sub_mul, one_mul, div_mul_cancel₀ _ (mul_pos hM hH').ne']
  have halg : (minor.size : ℝ) * ((w.theta : ℝ) * (H : ℝ) / wmin) =
      ((w.theta : ℝ) / wmin) * ((minor.size : ℝ) * (H : ℝ)) := by ring
  rw [halg] at hs
  nlinarith only [hs, hc, hd, hb]

/-- The concrete ceil(log q_i) specialization needs no separate logarithmic weight assumptions. -/
theorem fullRowMinor_bound_of_ceilLogWeights {m : ℕ} {w : Weights m} {H F : ℚ}
    (p : Fin m → ℤ) (q : Fin m → ℕ) (hq : ∀ i, 2 ≤ q i)
    (hw : ∀ i, w.w i = ceilLogWeight (q i))
    (hK : 0 < w.K) (hH : 0 < H) (hF : 0 ≤ F)
    (wmin : ℝ) (hmin : 0 < wmin) (hweights : ∀ i, wmin ≤ (w.w i : ℝ))
    (minor : FullRowMinor w H (rationalPoint p q) (truncationOrders w F)) :
    -(1 - averageRowWeight minor) - arithmeticError w F wmin ≤
      Real.log |(minor.matrix.det : ℝ)| / ((minor.size : ℝ) * (H : ℝ)) := by
  apply fullRowMinor_normalized_arithmetic_bound p q (fun i => by have := hq i; omega)
    hK hH hF _ _ wmin hmin hweights minor
  · intro i; rw [hw i]; exact (ceilLogWeight_bounds (q i)).1
  · intro i; rw [hw i]; exact (ceilLogWeight_bounds (q i)).2

end
end LogTwo.Arithmetic

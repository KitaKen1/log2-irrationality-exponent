module

public import LogTwo.Analysis.AnalyticSummand
public import LogTwo.ArithmeticEstimate

@[expose] public section
namespace LogTwo.Analysis
open OAI PiExponent MatrixTranslation RowTranslation AnalyticCollision PeriodAnalytic
open LogTwo.Interpolation LogTwo.Arithmetic
noncomputable section

abbrev analyticIndices {m : ℕ} (w : Weights m) (H : ℚ) :=
  transverseIndices (fun k => (w.w k : ℝ)) (H : ℝ)

abbrev MinorChoice {m : ℕ} {w : Weights m} {H : ℚ} {r : Fin m → ℚ}
    {T : Fin m → ℕ} (minor : FullRowMinor w H r T) :=
  ∀ i, RowChoices (analyticIndices w H)
    (InterpolationMatrix.exponentVector (minor.rows i).beta) (minor.rows i).s

def indexWeight {m : ℕ} (w : Weights m) (a : Fin m →₀ ℕ) : ℝ :=
  ∑ k, (w.w k : ℝ)*(a k : ℝ)

def translationBudget {m : ℕ} (w : Weights m) (C ν F ws : ℝ) : ℝ :=
  ν/F + Real.log 2/(w.v0 : ℝ) + (Real.log 4+C)/ws

def holomorphicBudget {m : ℕ} (w : Weights m) (ws : ℝ) : ℝ :=
  100*(w.K : ℝ)/(w.w0 : ℝ)+Real.log (200*(w.K : ℝ))/ws+Real.log 2/(w.v0 : ℝ)

def choiceScalar {m : ℕ} {w : Weights m} {H : ℚ} {r : Fin m → ℚ}
    {T : Fin m → ℕ} (minor : FullRowMinor w H r T) (f : MinorChoice minor) : ℂ :=
  ∏ i, actualRowScalar r T (minor.rows i) (analyticIndices w H) (f i)

/-- The logarithm-two center error has no periodicity factor. -/
theorem norm_logTwo_center_error_exp {r : ℚ} {q j K : ℕ} {ν : ℝ}
    (hK : 1 ≤ K) (hj : j ≤ K) (hν : 0 ≤ ν) (hq : 1 ≤ q)
    (happrox : |Real.log 2-(r : ℝ)| ≤ (q : ℝ)^(-ν)) :
    ‖(j : ℂ)*((r : ℂ)-(Real.log 2 : ℂ))‖ ≤
      Real.exp ((Real.log (K : ℝ)+ν)-ν*(ceilLogWeight q : ℝ)) := by
  have he : (r : ℂ)-(Real.log 2 : ℂ) = (((r : ℝ)-Real.log 2 : ℝ) : ℂ) := by
    push_cast
    rfl
  rw [norm_mul, he, Complex.norm_natCast, Complex.norm_real, Real.norm_eq_abs, abs_sub_comm]
  have hjR : (j : ℝ) ≤ K := by exact_mod_cast hj
  have hKpos : (0 : ℝ) < K := by exact_mod_cast (show 0 < K by omega)
  calc
    _ ≤ (K : ℝ)*(q : ℝ)^(-ν) :=
      mul_le_mul hjR happrox (abs_nonneg _) (Nat.cast_nonneg _)
    _ ≤ (K : ℝ)*(Real.exp ν * Real.exp (-ν*(⌈Real.log (q : ℝ)⌉₊ : ℝ))) :=
      mul_le_mul_of_nonneg_left (rpow_neg_le_exp_ceil_log ν hν hq) (Nat.cast_nonneg _)
    _ = _ := by
      simp only [ceilLogWeight, Rat.cast_natCast]
      rw [sub_eq_add_neg, Real.exp_add, Real.exp_add, Real.exp_log hKpos]
      simp only [neg_mul]
      ring

theorem truncationOrders_analytic_budget {m : ℕ} (w : Weights m) {F : ℚ}
    (hF : 0 < F) :
    (∀ k, 1 ≤ truncationOrders w F k) ∧
      (∀ k, (F : ℝ)*(w.w k : ℝ) ≤ (w.v0 : ℝ)*(truncationOrders w F k : ℝ)) := by
  constructor
  · intro k
    have hp : (0 : ℚ) < F*w.w k/w.v0 := div_pos (mul_pos hF (w.w_pos k)) w.v0_pos
    exact Nat.one_le_iff_ne_zero.mpr (Nat.ceil_pos.mpr hp).ne'
  · intro k
    have hb : F*w.w k ≤ (truncationOrders w F k : ℚ)*w.v0 :=
      (div_le_iff₀ w.v0_pos).mp (Nat.le_ceil _)
    exact_mod_cast (by simpa only [mul_comm] using hb)

theorem actual_row_order_le {m : ℕ} {w : Weights m} {H : ℚ} {row : Row m}
    (hr : AdmissibleRow w H row) : (row.s : ℝ) ≤ (H : ℝ)/(w.v0 : ℝ) := by
  have hb : (0 : ℚ) ≤ (∑ k, w.w k*row.beta k)/w.theta :=
    div_nonneg (Finset.sum_nonneg (fun k _ => mul_nonneg (w.w_pos k).le (Nat.cast_nonneg _)))
      w.theta_pos.le
  have hs : w.v0*row.s ≤ H := (le_add_of_nonneg_right hb).trans hr.2.le
  apply (le_div_iff₀ (by exact_mod_cast w.v0_pos)).mpr
  have hsR : (w.v0 : ℝ)*(row.s : ℝ) ≤ (H : ℝ) := by exact_mod_cast hs
  simpa only [mul_comm] using hsR

/-- Tail orders and approximation errors are the explicit inputs. -/
theorem norm_actualRowScalar_le {m : ℕ} {w : Weights m} {H : ℚ}
    (r : Fin m → ℚ) (T : Fin m → ℕ) {C ν F ws : ℝ}
    (hC : 0 ≤ C) (hν : 0 ≤ ν) (hF : 0 < F) (hws : 0 < ws)
    (hw : ∀ k, ws ≤ (w.w k : ℝ))
    (hT : ∀ k, 1 ≤ T k) (hTw : ∀ k, F*(w.w k : ℝ) ≤ (w.v0 : ℝ)*T k)
    (row : Row m) (hr : AdmissibleRow w H row)
    (he : ∀ k, ‖(row.j : ℂ)*((r k : ℂ)-(Real.log 2 : ℂ))‖ ≤
      Real.exp (C-ν*(w.w k : ℝ)))
    (t : RowChoices (analyticIndices w H) (InterpolationMatrix.exponentVector row.beta) row.s) :
    ‖actualRowScalar r T row (analyticIndices w H) t‖ ≤
      Real.exp (-ν*(indexWeight w t.1.1-rowWeight w row) +
        (H : ℝ)*translationBudget w C ν F ws) := by
  apply MatrixTranslationBounds.norm_rowScalar_exp_weight_difference
    _ T _ t.1.1 t.2.1 t.2.2 (fun k => (w.w k : ℝ)) C ν (H : ℝ) ws (w.v0 : ℝ) F
    hC hν hws (by exact_mod_cast w.v0_pos) hF hw
  · exact (mem_transverseIndices _ _ (fun k => by exact_mod_cast w.w_pos k) t.1.1).mp t.1.2
  · have hk : ((t.2.2 : ℕ) : ℝ) ≤ row.s := by
      exact_mod_cast (Nat.le_of_lt_succ t.2.2.isLt)
    exact hk.trans (actual_row_order_le hr)
  · exact hT
  · exact hTw
  · exact he

theorem actualRowScalar_ne_zero_beta_le {m : ℕ} {w : Weights m} {H : ℚ}
    (r : Fin m → ℚ) (T : Fin m → ℕ) (row : Row m)
    (t : RowChoices (analyticIndices w H) (InterpolationMatrix.exponentVector row.beta) row.s)
    (ht : actualRowScalar r T row (analyticIndices w H) t ≠ 0) :
    ∀ k, row.beta k ≤ t.1.1 k := by
  exact rowScalar_ne_zero_le _ _ _ _ _ _ ht

/-- The product retains the exact average row saving used by the arithmetic bound. -/
theorem norm_choiceScalar_le {m : ℕ} {w : Weights m} {H : ℚ}
    {r : Fin m → ℚ} {T : Fin m → ℕ} (minor : FullRowMinor w H r T)
    (hK : 0 < w.K) (hH : 0 < H) {C ν F ws : ℝ}
    (hC : 0 ≤ C) (hν : 0 ≤ ν) (hF : 0 < F) (hws : 0 < ws)
    (hw : ∀ k, ws ≤ (w.w k : ℝ))
    (hT : ∀ k, 1 ≤ T k) (hTw : ∀ k, F*(w.w k : ℝ) ≤ (w.v0 : ℝ)*T k)
    (he : ∀ i k, ‖((minor.rows i).j : ℂ)*((r k : ℂ)-(Real.log 2 : ℂ))‖ ≤
      Real.exp (C-ν*(w.w k : ℝ))) (f : MinorChoice minor) :
    ‖choiceScalar minor f‖ ≤
      Real.exp (-ν*((∑ i, indexWeight w (f i).1.1) -
        (minor.size : ℝ)*(H : ℝ)*averageRowWeight minor) +
          (minor.size : ℝ)*(H : ℝ)*translationBudget w C ν F ws) := by
  have hM : (minor.size : ℝ) ≠ 0 := by exact_mod_cast (fullRowMinor_size_pos hK hH minor).ne'
  have hH0 : (H : ℝ) ≠ 0 := by exact_mod_cast hH.ne'
  have hsave : (minor.size : ℝ)*(H : ℝ)*averageRowWeight minor =
      ∑ i, rowWeight w (minor.rows i) := by
    unfold averageRowWeight
    field_simp
  calc
    _ ≤ ∏ i, Real.exp (-ν*(indexWeight w (f i).1.1-rowWeight w (minor.rows i)) +
        (H : ℝ)*translationBudget w C ν F ws) := by
      rw [choiceScalar, norm_prod]
      apply Finset.prod_le_prod₀ (fun i _ => norm_nonneg _)
      intro i _
      exact norm_actualRowScalar_le r T hC hν hF hws hw hT hTw
        (minor.rows i) (minor.row_valid i) (he i) (f i)
    _ = _ := by
      rw [← Real.exp_sum, hsave]
      congr 1
      simp only [Finset.sum_add_distrib, mul_sub, Finset.sum_sub_distrib,
        ← Finset.mul_sum, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
      ring

end
end LogTwo.Analysis

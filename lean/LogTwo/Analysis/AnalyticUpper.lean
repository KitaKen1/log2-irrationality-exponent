/-
Modification notice for the LogTwo project.
Adapted from openai/math (Apache-2.0), revision adc7f1241b42e322a6451854ab7e4b4c146bf78a.
Changes: Adapt the low-index injection and finite-choice aggregation arguments to log-two data.
See ../../../THIRD_PARTY_NOTICES.txt for provenance and the recorded changes.
-/

module

public import LogTwo.Analysis.TranslationScalar

@[expose] public section
namespace LogTwo.Analysis
open OAI PiExponent MatrixTranslation RowTranslation AnalyticCollision PeriodAnalytic
open LogTwo.Interpolation LogTwo.Arithmetic
noncomputable section

def lowIndexCount {m : ℕ} (w : Weights m) (H : ℚ) (A : ℝ) : ℕ :=
  (transverseIndices (fun k => (w.w k : ℝ)) (A*(H : ℝ))).card

def analyticSummand {m : ℕ} {w : Weights m} {H : ℚ} {r : Fin m → ℚ}
    {T : Fin m → ℕ} (minor : FullRowMinor w H r T) (f : MinorChoice minor) : ℂ :=
  choiceScalar minor f * Matrix.det (fun i c =>
    actualAnalyticRow (minor.rows i) (analyticIndices w H) (f i) (minor.columns c))

def combinedAnalyticBudget {m : ℕ} {w : Weights m} {H : ℚ} {r : Fin m → ℚ}
    {T : Fin m → ℕ} (minor : FullRowMinor w H r T) (C ν F ws A η : ℝ) : ℝ :=
  translationBudget w C ν F ws + holomorphicBudget w ws +
    Collision.collisionRemainder minor.size (H : ℝ) +
      max (-(Real.log 2/4)*η^2*(minor.size : ℝ)/((H : ℝ)*lowIndexCount w H A))
        (-ν*(A*(1-η)-averageRowWeight minor))

def rowChoiceCount {m : ℕ} (w : Weights m) (H : ℚ) : ℕ :=
  (⌊(H : ℝ)⌋₊+1)^(2*m) * (⌊(H : ℝ)/(w.v0 : ℝ)⌋₊+1)

theorem lowIndexCount_pos {m : ℕ} (w : Weights m) {H : ℚ} {A : ℝ}
    (hH : 0 < H) (hA : 0 ≤ A) : 0 < lowIndexCount w H A := by
  apply Finset.card_pos.mpr
  refine ⟨0, ?_⟩
  apply (mem_transverseIndices _ _ (fun k => by exact_mod_cast w.w_pos k) 0).mpr
  simpa using mul_nonneg hA (show (0 : ℝ) ≤ H by exact_mod_cast hH.le)

theorem low_transverse_capacity {m : ℕ} (w : Weights m) (H : ℚ) (A : ℝ) :
    (((Finset.univ : Finset (analyticIndices w H)).filter
      (fun a => indexWeight w a.1 ≤ A*(H : ℝ))).card : ℝ) ≤ lowIndexCount w H A := by
  classical
  let f : {a : analyticIndices w H // indexWeight w a.1 ≤ A*(H : ℝ)} →
      ↥(transverseIndices (fun k => (w.w k : ℝ)) (A*(H : ℝ))) :=
    fun a => ⟨a.1.1, (mem_transverseIndices _ _ (fun k => by exact_mod_cast w.w_pos k) _).mpr a.2⟩
  have hinj : Function.Injective f := by
    intro a b h
    apply Subtype.ext
    apply Subtype.ext
    have he := congrArg Subtype.val h
    simpa only [f] using he
  have hb := Fintype.card_le_of_injective f hinj
  rw [Fintype.card_subtype, Fintype.card_coe] at hb
  unfold lowIndexCount
  exact_mod_cast hb

theorem choiceScalar_ne_zero_weight_sum {m : ℕ} {w : Weights m} {H : ℚ}
    {r : Fin m → ℚ} {T : Fin m → ℕ} (minor : FullRowMinor w H r T)
    (hK : 0 < w.K) (hH : 0 < H) (f : MinorChoice minor)
    (hf : choiceScalar minor f ≠ 0) :
    (minor.size : ℝ)*(H : ℝ)*averageRowWeight minor ≤ ∑ i, indexWeight w (f i).1.1 := by
  have hM : (minor.size : ℝ) ≠ 0 := by exact_mod_cast (fullRowMinor_size_pos hK hH minor).ne'
  have hH0 : (H : ℝ) ≠ 0 := by exact_mod_cast hH.ne'
  have heq : (minor.size : ℝ)*(H : ℝ)*averageRowWeight minor =
      ∑ i, rowWeight w (minor.rows i) := by unfold averageRowWeight; field_simp
  rw [heq]
  apply Finset.sum_le_sum
  intro i _
  have hi : actualRowScalar r T (minor.rows i) (analyticIndices w H) (f i) ≠ 0 :=
    Finset.prod_ne_zero_iff.mp hf i (Finset.mem_univ i)
  have hb := actualRowScalar_ne_zero_beta_le r T (minor.rows i) (f i) hi
  apply Finset.sum_le_sum
  intro k _
  exact mul_le_mul_of_nonneg_left (by exact_mod_cast hb k)
    (show (0 : ℝ) ≤ w.w k by exact_mod_cast (w.w_pos k).le)

/-- The two-alternative collision estimate is applied to the actual scalar
and determinant, retaining the arithmetic mean row weight. -/
theorem norm_analyticSummand_le {m : ℕ} {w : Weights m} {H : ℚ}
    {r : Fin m → ℚ} {T : Fin m → ℕ} (minor : FullRowMinor w H r T)
    (hK : 0 < w.K) (hH : 0 < H) {C ν F ws A η : ℝ}
    (hC : 0 ≤ C) (hν : 0 ≤ ν) (hF : 0 < F) (hws : 0 < ws)
    (hA : 0 ≤ A) (hη : 0 ≤ η) (hw : ∀ k, ws ≤ (w.w k : ℝ))
    (hT : ∀ k, 1 ≤ T k) (hTw : ∀ k, F*(w.w k : ℝ) ≤ (w.v0 : ℝ)*T k)
    (he : ∀ i k, ‖((minor.rows i).j : ℂ)*((r k : ℂ)-(Real.log 2 : ℂ))‖ ≤
      Real.exp (C-ν*(w.w k : ℝ))) (f : MinorChoice minor) :
    ‖analyticSummand minor f‖ ≤
      Real.exp ((minor.size : ℝ)*(H : ℝ)*combinedAnalyticBudget minor C ν F ws A η) := by
  classical
  by_cases hz : choiceScalar minor f = 0
  · simp [analyticSummand, hz, Real.exp_nonneg]
  have hweight : ∀ a : analyticIndices w H, 0 ≤ indexWeight w a.1 := by
    intro a
    exact Finset.sum_nonneg (fun k _ => mul_nonneg
      (show (0 : ℝ) ≤ (w.w k : ℝ) by exact_mod_cast (w.w_pos k).le)
      (Nat.cast_nonneg (a.1 k)))
  have hb := DeterminantAnalyticBound.translated_summand_bound
    (H := (H : ℝ)) (A := A) (eta := η) (nu := ν) (c := Real.log 2/4)
    (N := (lowIndexCount w H A : ℝ)) (bbar := averageRowWeight minor)
    (Etr := translationBudget w C ν F ws) (Ehol := holomorphicBudget w ws)
    (rho := Collision.collisionRemainder minor.size (H : ℝ))
    (fun i => (f i).1) (fun a : analyticIndices w H => indexWeight w a.1)
    (choiceScalar minor f)
    (Matrix.det (fun i c => actualAnalyticRow (minor.rows i) (analyticIndices w H)
      (f i) (minor.columns c)))
    (by exact_mod_cast hH) hA hη hν
    (div_nonneg (Real.log_nonneg (by norm_num : (1 : ℝ) ≤ 2)) (by norm_num))
    (by exact_mod_cast lowIndexCount_pos w hH hA)
    hweight
    (by simpa only [Fintype.card_fin] using choiceScalar_ne_zero_weight_sum minor hK hH f hz)
    (low_transverse_capacity w H A)
    (by simpa only [Fintype.card_fin] using norm_choiceScalar_le minor hK hH hC hν hF hws hw hT hTw he f)
    (by simpa only [Fintype.card_fin, holomorphicBudget] using
      actual_analytic_summand_exp_bound minor hK hH hws hw f)
  simpa only [analyticSummand, combinedAnalyticBudget, holomorphicBudget, Fintype.card_fin] using hb

theorem card_minorChoice_le {m : ℕ} {w : Weights m} {H : ℚ}
    {r : Fin m → ℚ} {T : Fin m → ℕ} (minor : FullRowMinor w H r T)
    (hw : ∀ k, 1 ≤ (w.w k : ℝ)) :
    Fintype.card (MinorChoice minor) ≤ (rowChoiceCount w H)^minor.size := by
  classical
  rw [Fintype.card_pi]
  calc
    _ ≤ ∏ _i : Fin minor.size, rowChoiceCount w H := by
      apply Finset.prod_le_prod
      intro i _
      exact row_term_count (fun k => (w.w k : ℝ)) (H : ℝ) (w.v0 : ℝ) hw
        _ (minor.rows i).s (actual_row_order_le (minor.row_valid i))
    _ = _ := by simp

theorem actual_minor_complex_det {m : ℕ} {w : Weights m} {H : ℚ}
    {r : Fin m → ℚ} {T : Fin m → ℕ} (minor : FullRowMinor w H r T) :
    Matrix.det (fun i c => (minor.matrix i c : ℂ)) = (minor.matrix.det : ℂ) := by
  exact (Rat.cast_det minor.matrix).symm

/-- Explicit normalized analytic upper bound for the very same rational minor.
Asymptotic control of lowIndexCount and collisionRemainder is still a separate step. -/
theorem actual_minor_log_analytic_bound {m : ℕ} {w : Weights m} {H : ℚ}
    {r : Fin m → ℚ} {T : Fin m → ℕ} (minor : FullRowMinor w H r T)
    (hK : 0 < w.K) (hH : 0 < H) {C ν F ws A η : ℝ}
    (hC : 0 ≤ C) (hν : 0 ≤ ν) (hF : 0 < F) (hws : 0 < ws)
    (hA : 0 ≤ A) (hη : 0 ≤ η) (hw : ∀ k, ws ≤ (w.w k : ℝ))
    (hw1 : ∀ k, 1 ≤ (w.w k : ℝ))
    (hT : ∀ k, 1 ≤ T k) (hTw : ∀ k, F*(w.w k : ℝ) ≤ (w.v0 : ℝ)*T k)
    (he : ∀ i k, ‖((minor.rows i).j : ℂ)*((r k : ℂ)-(Real.log 2 : ℂ))‖ ≤
      Real.exp (C-ν*(w.w k : ℝ))) :
    Real.log |(minor.matrix.det : ℝ)| / ((minor.size : ℝ)*(H : ℝ)) ≤
      combinedAnalyticBudget minor C ν F ws A η + Real.log (rowChoiceCount w H : ℝ)/(H : ℝ) := by
  classical
  have hq : (0 : ℝ) < rowChoiceCount w H := by
    unfold rowChoiceCount
    positivity
  have hd : Matrix.det (fun i c => (minor.matrix i c : ℂ)) ≠ 0 := by
    rw [actual_minor_complex_det]
    exact_mod_cast minor.matrix_det_ne_zero
  have hb := DeterminantAnalyticBound.log_norm_sum_le (analyticSummand minor)
    (Matrix.det (fun i c => (minor.matrix i c : ℂ)))
    (fullRowMinor_size_pos hK hH minor) (by exact_mod_cast hH) hq
    (by exact_mod_cast card_minorChoice_le minor hw1)
    (actual_minor_analytic_expansion_weighted minor) hd
    (fun f => norm_analyticSummand_le minor hK hH hC hν hF hws hA hη hw hT hTw he f)
  rw [actual_minor_complex_det] at hb
  have hn : ‖(minor.matrix.det : ℂ)‖ = |(minor.matrix.det : ℝ)| := by
    rw [← Complex.ofReal_ratCast, Complex.norm_real, Real.norm_eq_abs]
  rwa [hn] at hb

/-- All analytic entry hypotheses are discharged by the actual logarithm-two
approximations and the same ceil-log weights / truncation orders as arithmetic. -/
theorem actual_minor_log_bound_of_approximations {m : ℕ} {w : Weights m} {H F : ℚ}
    (r : Fin m → ℚ) (q : Fin m → ℕ)
    (minor : FullRowMinor w H r (truncationOrders w F))
    (hK : 0 < w.K) (hH : 0 < H) (hF : 0 < F) {ν ws A η : ℝ}
    (hν : 0 ≤ ν) (hws : 0 < ws) (hA : 0 ≤ A) (hη : 0 ≤ η)
    (hq : ∀ k, 2 ≤ q k) (hwq : ∀ k, w.w k = ceilLogWeight (q k))
    (hw : ∀ k, ws ≤ (w.w k : ℝ))
    (happrox : ∀ k, |Real.log 2-(r k : ℝ)| ≤ (q k : ℝ)^(-ν)) :
    Real.log |(minor.matrix.det : ℝ)| / ((minor.size : ℝ)*(H : ℝ)) ≤
      combinedAnalyticBudget minor (Real.log (w.K : ℝ)+ν) ν (F : ℝ) ws A η +
        Real.log (rowChoiceCount w H : ℝ)/(H : ℝ) := by
  have hK1 : (1 : ℝ) ≤ w.K := by exact_mod_cast hK
  have hweights : ∀ k, 1 ≤ (w.w k : ℝ) := by
    intro k
    rw [hwq k]
    have hqR : (1 : ℝ) < q k := by exact_mod_cast (show 1 < q k by have := hq k; omega)
    have hc : 1 ≤ ⌈Real.log (q k : ℝ)⌉₊ := Nat.succ_le_of_lt (Nat.ceil_pos.mpr (Real.log_pos hqR))
    simpa only [ceilLogWeight, Rat.cast_natCast] using (show (1 : ℝ) ≤ (⌈Real.log (q k : ℝ)⌉₊ : ℝ) by exact_mod_cast hc)
  apply actual_minor_log_analytic_bound minor hK hH
    (add_nonneg (Real.log_nonneg hK1) hν) hν (by exact_mod_cast hF) hws hA hη hw hweights
    (truncationOrders_analytic_budget w hF).1 (truncationOrders_analytic_budget w hF).2
  intro i k
  rw [hwq k]
  exact norm_logTwo_center_error_exp (by omega : 1 ≤ w.K) (minor.row_valid i).1.le hν
    (by have := hq k; omega) (happrox k)

end
end LogTwo.Analysis

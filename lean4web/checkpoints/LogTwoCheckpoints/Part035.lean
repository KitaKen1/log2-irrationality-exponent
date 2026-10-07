/- Generated rc4 checkpoint for LogTwo.
Modified from the reduced edition: new imports, separate module compilation,
and synchronous elaboration. Original source blocks and notices are retained.
See ../../../THIRD_PARTY_NOTICES.txt and ../../reduction.json.
-/
module
public import LogTwoCheckpoints.Part000
public import LogTwoCheckpoints.Part001
public import LogTwoCheckpoints.Part002
public import LogTwoCheckpoints.Part003
public import LogTwoCheckpoints.Part004
public import LogTwoCheckpoints.Part011
public import LogTwoCheckpoints.Part012
public import LogTwoCheckpoints.Part013
public import LogTwoCheckpoints.Part014
public import LogTwoCheckpoints.Part015
public import LogTwoCheckpoints.Part019
public import LogTwoCheckpoints.Part020
public import LogTwoCheckpoints.Part021
public import LogTwoCheckpoints.Part022
public import LogTwoCheckpoints.Part024
public import LogTwoCheckpoints.Part025
public import LogTwoCheckpoints.Part029
public import LogTwoCheckpoints.Part033
public import LogTwoCheckpoints.Part034
public import Mathlib.Analysis.Complex.Polynomial.Basic
public import Mathlib.NumberTheory.Real.Irrational
@[expose] public section
set_option Elab.async false

-- Source: LogTwo/Analysis/AnalyticUpper.lean
section Source0875
/-
Modification notice for the LogTwo project.
Adapted from openai/math (Apache-2.0), revision adc7f1241b42e322a6451854ab7e4b4c146bf78a.
Changes: Adapt the low-index injection and finite-choice aggregation arguments to log-two data.
See ../THIRD_PARTY_NOTICES.txt for provenance and the recorded changes.
-/

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
end Source0875

-- Source: OAI/NumberTheory/PiExponent/Analysis/TranslationCountLimit.lean
section Source0876
-- Modified in this edition: unused plain lemmas removed; see reduction.json.
/-
Modification notice for the LogTwo project.
Derived from openai/math (Apache-2.0), revision adc7f1241b42e322a6451854ab7e4b4c146bf78a.
Original source: lean/OAI/NumberTheory/PiExponent/Analysis/TranslationCountLimit.lean
Changes: Convert module/import declarations to the Lean 4.34 public module format.
See ../THIRD_PARTY_NOTICES.txt for provenance and the recorded changes.
-/

namespace OAI

open Filter Topology

namespace PiExponent

noncomputable def translationTermCount (m : ℕ) (v H : ℝ) : ℕ :=
  (⌊H⌋₊ + 1) ^ (2 * m) * (⌊H / v⌋₊ + 1)

theorem tendsto_natFloor_mul_add_one_div {a : ℝ} (ha : 0 < a) :
    Tendsto (fun H : ℝ => ((⌊a * H⌋₊ + 1 : ℕ) : ℝ) / H) atTop (𝓝 a) := by
  have h := (tendsto_natFloor_affine_div ha 0).add (tendsto_id.const_div_atTop (1 : ℝ))
  simpa only [add_zero, id_eq, Nat.cast_add, Nat.cast_one, add_div] using h

theorem tendsto_translationTermCount_normalized (m : ℕ) {v : ℝ} (hv : 0 < v) :
    Tendsto (fun H : ℝ => (translationTermCount m v H : ℝ) / H ^ (2 * m + 1))
      atTop (𝓝 (1 / v)) := by
  have h₁ : Tendsto (fun H : ℝ => ((⌊H⌋₊ + 1 : ℕ) : ℝ) / H) atTop (𝓝 1) := by
    simpa only [one_mul] using tendsto_natFloor_mul_add_one_div (show (0 : ℝ) < 1 by norm_num)
  have h₂ : Tendsto (fun H : ℝ => ((⌊H / v⌋₊ + 1 : ℕ) : ℝ) / H)
      atTop (𝓝 (1 / v)) := by
    simpa only [one_div, div_eq_mul_inv, mul_comm, mul_one, one_mul] using
      tendsto_natFloor_mul_add_one_div (div_pos zero_lt_one hv)
  have h := (h₁.pow (2 * m)).mul h₂
  simp only [one_pow, one_mul] at h
  convert h using 1
  ext H
  simp only [translationTermCount, Nat.cast_mul, Nat.cast_pow, div_pow, div_mul_div_comm,
    pow_succ]

theorem tendsto_log_translationTermCount_div (m : ℕ) {v : ℝ} (hv : 0 < v) :
    Tendsto (fun H : ℝ => Real.log (translationTermCount m v H : ℝ) / H)
      atTop (𝓝 0) :=
  tendsto_log_div_of_normalized_pow (tendsto_translationTermCount_normalized m hv)
    (div_pos zero_lt_one hv)

end PiExponent

end OAI
end Source0876

-- Source: LogTwo/Analysis/Counting.lean
section Source0877
/-
Modification notice for the LogTwo project.
Adapted from openai/math (Apache-2.0), revision adc7f1241b42e322a6451854ab7e4b4c146bf78a.
Changes: Generalize the matrix-counting strategy to arbitrary rational weights.
See ../THIRD_PARTY_NOTICES.txt for provenance and the recorded changes.
-/

namespace LogTwo.Analysis
open OAI PiExponent MatrixTranslation
open LogTwo.Interpolation LogTwo.Geometry
open Filter Topology
noncomputable section

/-- The full row count is independent of the columns selected by interpolation. -/
def rowCount {m : ℕ} (w : Weights m) (H : ℝ) : ℕ :=
  w.K * (strictWeightedSimplex (fun i => (jetWeight w i : ℝ)) H).card

def rowDensity {m : ℕ} (w : Weights m) : ℝ :=
  (w.K : ℝ)*(w.theta : ℝ)^m /
    (((m+1).factorial : ℝ)*(w.v0 : ℝ)*∏ i, (w.w i : ℝ))

def lowDensity {m : ℕ} (w : Weights m) (A : ℝ) : ℝ :=
  A^m / ((m.factorial : ℝ)*∏ i, (w.w i : ℝ))

def lowCountReal {m : ℕ} (w : Weights m) (A H : ℝ) : ℕ :=
  (transverseIndices (fun i => (w.w i : ℝ)) (A*H)).card

def collisionLimit {m : ℕ} (w : Weights m) (A η : ℝ) : ℝ :=
  (Real.log 2/4)*η^2*(w.K : ℝ)*(w.theta : ℝ)^m /
    (((m : ℝ)+1)*(w.v0 : ℝ)*A^m)

theorem fullRowMinor_size_eq_card {m : ℕ} {w : Weights m} {H : ℚ}
    {r : Fin m → ℚ} {T : Fin m → ℕ} (minor : FullRowMinor w H r T) :
    minor.size = Fintype.card (RowIndex w H) := by
  classical
  let f : Fin minor.size → RowIndex w H := fun i =>
    (exists_rowIndex w H (minor.rows i) (minor.row_valid i)).choose
  have hf (i) : rowOfIndex (f i) = minor.rows i :=
    (exists_rowIndex w H (minor.rows i) (minor.row_valid i)).choose_spec
  have hinj : Function.Injective f := by
    intro i j hij
    apply minor.rows_injective
    rw [← hf i, ← hf j, hij]
  have hsurj : Function.Surjective f := by
    intro a
    obtain ⟨i, hi⟩ := minor.all_rows (rowOfIndex a) (rowOfIndex_valid a)
    exact ⟨i, (rowOfIndex_injective w H) ((hf i).trans hi)⟩
  simpa only [Fintype.card_fin] using Fintype.card_congr (Equiv.ofBijective f ⟨hinj, hsurj⟩)

theorem fullRowMinor_size_eq_rowCount {m : ℕ} {w : Weights m} {H : ℚ}
    {r : Fin m → ℚ} {T : Fin m → ℕ} (minor : FullRowMinor w H r T) :
    minor.size = rowCount w (H : ℝ) := by
  rw [fullRowMinor_size_eq_card minor]
  simp only [RowIndex, rowCount, Fintype.card_prod, Fintype.card_fin, Fintype.card_coe]

theorem rowDensity_pos {m : ℕ} (w : Weights m) (hK : 0 < w.K) :
    0 < rowDensity w := by
  have hv : (0 : ℝ) < w.v0 := by exact_mod_cast w.v0_pos
  have ht : (0 : ℝ) < w.theta := by exact_mod_cast w.theta_pos
  have hk : (0 : ℝ) < w.K := by exact_mod_cast hK
  have hp : 0 < ∏ i, (w.w i : ℝ) := Finset.prod_pos (fun i _ => by exact_mod_cast w.w_pos i)
  unfold rowDensity
  positivity

theorem lowDensity_pos {m : ℕ} (w : Weights m) {A : ℝ} (hA : 0 < A) :
    0 < lowDensity w A := by
  have hp : 0 < ∏ i, (w.w i : ℝ) := Finset.prod_pos (fun i _ => by exact_mod_cast w.w_pos i)
  unfold lowDensity
  positivity

theorem tendsto_rowCount_normalized {m : ℕ} (w : Weights m) :
    Tendsto (fun H : ℝ => (rowCount w H : ℝ)/H^(m+1)) atTop (𝓝 (rowDensity w)) := by
  have ht := (tendsto_card_strictWeightedSimplex_rational (jetWeight w) (jetWeight_pos w)).const_mul (w.K : ℝ)
  have hp : ∏ i, (jetWeight w i : ℝ) =
      (w.v0 : ℝ)*(∏ i, (w.w i : ℝ))/(w.theta : ℝ)^m := by
    rw [Fin.prod_univ_succ]
    simp [jetWeight, Finset.prod_div_distrib, mul_div_assoc]
  have he : (w.K : ℝ)*(1/(((m+1).factorial : ℝ)*∏ i, (jetWeight w i : ℝ))) = rowDensity w := by
    rw [hp]
    unfold rowDensity
    have ht0 : (w.theta : ℝ) ≠ 0 := by exact_mod_cast w.theta_pos.ne'
    field_simp
  rw [he] at ht
  apply ht.congr'
  exact Eventually.of_forall (fun H => by simp only [rowCount, Nat.cast_mul]; ring)

theorem tendsto_lowCount_normalized {m : ℕ} (w : Weights m) {A : ℝ} (hA : 0 < A) :
    Tendsto (fun H : ℝ => (lowCountReal w A H : ℝ)/H^m) atTop (𝓝 (lowDensity w A)) := by
  have hscale : Tendsto (fun H : ℝ => A*H) atTop atTop :=
    Tendsto.const_mul_atTop hA tendsto_id
  have ht := ((tendsto_card_realWeightedSimplex_rational w.w w.w_pos).comp hscale).mul_const (A^m)
  have he : 1/((m.factorial : ℝ)*∏ i, (w.w i : ℝ))*A^m = lowDensity w A := by
    unfold lowDensity; ring
  rw [he] at ht
  apply ht.congr'
  exact Eventually.of_forall (fun H => by
    simp only [Function.comp_apply, lowCountReal, card_transverseIndices, mul_pow]
    field_simp)

theorem tendsto_collisionRate {m : ℕ} (w : Weights m) {A : ℝ} (hA : 0 < A) (η : ℝ) :
    Tendsto (fun H : ℝ => (Real.log 2/4)*η^2*(rowCount w H : ℝ)/(H*lowCountReal w A H))
      atTop (𝓝 (collisionLimit w A η)) := by
  have ht := ((tendsto_rowCount_normalized w).div (tendsto_lowCount_normalized w hA)
    (lowDensity_pos w hA).ne').const_mul ((Real.log 2/4)*η^2)
  have he : (Real.log 2/4)*η^2*(rowDensity w/lowDensity w A) = collisionLimit w A η := by
    unfold rowDensity lowDensity collisionLimit
    simp only [Nat.factorial_succ, Nat.cast_mul, Nat.cast_add, Nat.cast_one]
    have hp : (∏ i, (w.w i : ℝ)) ≠ 0 := (Finset.prod_pos (fun i _ => by exact_mod_cast w.w_pos i)).ne'
    have hv : (w.v0 : ℝ) ≠ 0 := by exact_mod_cast w.v0_pos.ne'
    field_simp
  rw [he] at ht
  apply ht.congr'
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with H hH
  change (Real.log 2/4)*η^2*(((rowCount w H : ℝ)/H^(m+1))/((lowCountReal w A H : ℝ)/H^m)) = _
  by_cases hn : lowCountReal w A H = 0
  · simp [hn]
  · have hnR : (lowCountReal w A H : ℝ) ≠ 0 := by exact_mod_cast hn
    simp only [pow_succ]
    field_simp

/-- Both terms depend only on the full row set, so the estimate is uniform
in the columns selected by interpolation. -/
def analyticRemainder {m : ℕ} (w : Weights m) (H : ℝ) : ℝ :=
  Collision.collisionRemainder (rowCount w H) H +
    Real.log (translationTermCount m (w.v0 : ℝ) H : ℝ)/H

theorem tendsto_analyticRemainder {m : ℕ} (w : Weights m) (hK : 0 < w.K) :
    Tendsto (analyticRemainder w) atTop (𝓝 0) := by
  have hr := tendsto_collisionRemainder_of_normalized_pow (tendsto_rowCount_normalized w) (rowDensity_pos w hK)
  have hq := tendsto_log_translationTermCount_div m (show (0 : ℝ) < w.v0 by exact_mod_cast w.v0_pos)
  change Tendsto (fun H : ℝ => Collision.collisionRemainder (rowCount w H) H +
    Real.log (translationTermCount m (w.v0 : ℝ) H : ℝ)/H) atTop (𝓝 0)
  simpa only [add_zero] using hr.add hq

end
end LogTwo.Analysis
end Source0877

-- Source: LogTwo/Analysis/AsymptoticUpper.lean
section Source0878
-- Modified in this edition: unused plain lemmas removed; see reduction.json.
/-
Modification notice for the LogTwo project.
Adapted from openai/math (Apache-2.0), revision adc7f1241b42e322a6451854ab7e4b4c146bf78a.
Changes: Adapt asymptotic bounds to the actual log-two minor and geometry.
See ../THIRD_PARTY_NOTICES.txt for provenance and the recorded changes.
-/

namespace LogTwo.Analysis
open OAI PiExponent MatrixTranslation
open LogTwo.Interpolation LogTwo.Arithmetic
open Filter Topology
noncomputable section

def fixedAnalyticError {m : ℕ} (w : Weights m) (ν F ws : ℝ) : ℝ :=
  translationBudget w (Real.log (w.K : ℝ)+ν) ν F ws + holomorphicBudget w ws

def collisionRate {m : ℕ} (w : Weights m) (A η H : ℝ) : ℝ :=
  (Real.log 2/4)*η^2*(rowCount w H : ℝ)/(H*lowCountReal w A H)

theorem combinedAnalyticBudget_eq {m : ℕ} {w : Weights m} {H : ℚ}
    {r : Fin m → ℚ} {T : Fin m → ℕ} (minor : FullRowMinor w H r T) (ν F ws A η : ℝ) :
    combinedAnalyticBudget minor (Real.log (w.K : ℝ)+ν) ν F ws A η +
      Real.log (rowChoiceCount w H : ℝ)/(H : ℝ) =
    fixedAnalyticError w ν F ws + analyticRemainder w (H : ℝ) +
      max (-collisionRate w A η (H : ℝ)) (-ν*(A*(1-η)-averageRowWeight minor)) := by
  unfold combinedAnalyticBudget fixedAnalyticError analyticRemainder collisionRate
  rw [← fullRowMinor_size_eq_rowCount minor]
  change _ = _ + (Collision.collisionRemainder minor.size (H : ℝ) +
    Real.log (rowChoiceCount w H : ℝ)/(H : ℝ)) +
    max (-((Real.log 2/4)*η^2*(minor.size : ℝ)/((H : ℝ)*lowIndexCount w H A))) _
  simp only [neg_mul, neg_div]
  ring

/-- The remainder and collision rate are uniform in the chosen columns. -/
theorem actual_minor_log_bound_with_remainder {m : ℕ} {w : Weights m} {H F : ℚ}
    (r : Fin m → ℚ) (q : Fin m → ℕ)
    (minor : FullRowMinor w H r (truncationOrders w F))
    (hK : 0 < w.K) (hH : 0 < H) (hF : 0 < F) {ν ws A η : ℝ}
    (hν : 0 ≤ ν) (hws : 0 < ws) (hA : 0 ≤ A) (hη : 0 ≤ η)
    (hq : ∀ k, 2 ≤ q k) (hwq : ∀ k, w.w k = ceilLogWeight (q k))
    (hw : ∀ k, ws ≤ (w.w k : ℝ))
    (happrox : ∀ k, |Real.log 2-(r k : ℝ)| ≤ (q k : ℝ)^(-ν)) :
    Real.log |(minor.matrix.det : ℝ)|/((minor.size : ℝ)*(H : ℝ)) ≤
      fixedAnalyticError w ν (F : ℝ) ws + analyticRemainder w (H : ℝ) +
        max (-collisionRate w A η (H : ℝ)) (-ν*(A*(1-η)-averageRowWeight minor)) := by
  rw [← combinedAnalyticBudget_eq minor]
  exact actual_minor_log_bound_of_approximations r q minor hK hH hF hν hws hA hη hq hwq hw happrox

end
end LogTwo.Analysis
end Source0878

-- Source: LogTwo/Analysis/BudgetContradiction.lean
section Source0879
/-
Modification notice for the LogTwo project.
Adapted from openai/math (Apache-2.0), revision adc7f1241b42e322a6451854ab7e4b4c146bf78a.
Changes: Adapt determinant-budget comparisons to the actual log-two minor and geometry.
See ../THIRD_PARTY_NOTICES.txt for provenance and the recorded changes.
-/

namespace LogTwo.Analysis
open OAI PiExponent
open LogTwo.Interpolation LogTwo.Arithmetic LogTwo.Parameters LogTwo.Geometry
open Filter Topology
noncomputable section

/-- Both bounds must use the same normalized determinant and mean row weight. -/
theorem normalized_bounds_inconsistent
    (ν θ x b ear ean err collision d : ℝ)
    (hν : 1 < ν) (hb0 : 0 ≤ b) (hb : b ≤ θ)
    (hgap : ear+ean+err < ν*(x-θ)-(1-θ))
    (hc : 1+ear+ean+err < collision)
    (hlower : -(1-b)-ear ≤ d)
    (hupper : d ≤ ean+err+max (-collision) (-ν*(x-b))) : False := by
  have hfirst : ean+err-collision < -(1-b)-ear := by linarith
  have hmono : ν*(x-θ)-(1-θ) ≤ ν*(x-b)-(1-b) := by nlinarith
  have hsecond : ean+err-ν*(x-b) < -(1-b)-ear := by linarith
  rcases le_total (-collision) (-ν*(x-b)) with h | h
  · rw [max_eq_right h] at hupper; linarith
  · rw [max_eq_left h] at hupper; linarith

/-- Once the two fixed numerical margins hold, no sufficiently large degree
can carry a nonzero full-row minor. This is uniform over all column choices. -/
theorem eventual_no_fullRowMinor {m : ℕ} (w : Weights m) {F : ℚ}
    (p : Fin m → ℤ) (q : Fin m → ℕ) (hK : 0 < w.K) (hF : 0 < F)
    {ν ws A η : ℝ} (hν : 1 < ν) (hws : 0 < ws) (hA : 0 < A) (hη : 0 ≤ η)
    (hq : ∀ k, 2 ≤ q k) (hwq : ∀ k, w.w k = ceilLogWeight (q k))
    (hw : ∀ k, ws ≤ (w.w k : ℝ))
    (happrox : ∀ k, |Real.log 2-(rationalPoint p q k : ℝ)| ≤ (q k : ℝ)^(-ν))
    (hgap : arithmeticError w F ws + fixedAnalyticError w ν (F : ℝ) ws <
      ν*(A*(1-η)-(w.theta : ℝ))-(1-(w.theta : ℝ)))
    (hcollision : 1+arithmeticError w F ws+fixedAnalyticError w ν (F : ℝ) ws < collisionLimit w A η) :
    ∀ᶠ H : ℚ in atTop, FullRowMinor w H (rationalPoint p q) (truncationOrders w F) → False := by
  have hsum : Tendsto (fun H : ℝ => arithmeticError w F ws + fixedAnalyticError w ν (F : ℝ) ws + analyticRemainder w H)
      atTop (𝓝 (arithmeticError w F ws+fixedAnalyticError w ν (F : ℝ) ws+0)) :=
    tendsto_const_nhds.add (tendsto_analyticRemainder w hK)
  have hsmall := (hsum.eventually_lt_const (by simpa using hgap)).ratCast_atTop
  have hdiff : Tendsto (fun H : ℝ => collisionRate w A η H -
      (1+arithmeticError w F ws+fixedAnalyticError w ν (F : ℝ) ws+analyticRemainder w H))
      atTop (𝓝 (collisionLimit w A η-(1+arithmeticError w F ws+fixedAnalyticError w ν (F : ℝ) ws+0))) :=
    (tendsto_collisionRate w hA η).sub (tendsto_const_nhds.add (tendsto_analyticRemainder w hK))
  have hlarge := (hdiff.eventually (Ioi_mem_nhds (show 0 < collisionLimit w A η-
      (1+arithmeticError w F ws+fixedAnalyticError w ν (F : ℝ) ws+0) by linarith))).ratCast_atTop
  filter_upwards [eventually_gt_atTop (0 : ℚ), hsmall, hlarge] with H hH hsmall hlarge
  intro minor
  have hl := fullRowMinor_bound_of_ceilLogWeights p q hq hwq hK hH hF.le ws hws hw minor
  have hu := actual_minor_log_bound_with_remainder (rationalPoint p q) q minor hK hH hF
    (by linarith : 0 ≤ ν) hws hA.le hη hq hwq hw happrox
  have hb := averageRowWeight_bounds hK hH minor
  exact normalized_bounds_inconsistent ν w.theta (A*(1-η)) (averageRowWeight minor)
    (arithmeticError w F ws) (fixedAnalyticError w ν (F : ℝ) ws) (analyticRemainder w H)
    (collisionRate w A η H) (Real.log |(minor.matrix.det : ℝ)|/((minor.size : ℝ)*(H : ℝ)))
    hν hb.1 hb.2.le hsmall (by linarith) hl hu

/-- The geometric minor is chosen above the analytic threshold. Neither the
minor's existence nor an analytic bound is an unproved input here. The two
fixed numerical margins remain explicit for the parameter-selection step. -/
theorem logTwo_contradiction_of_budgets
    (n : ℕ) (hn : 1 ≤ n) (m : ℕ) (p : Fin m → ℤ) (q : ℕ → ℕ) (hq : ∀ i, 2 ≤ q i)
    (hgrowth : ∀ i, i < m →
      denominatorSeparationFactor n m (chosenComparisonConstant n m)*
        (∏ j : Fin i, (ceilLogWeight (q j) : ℝ)) < (ceilLogWeight (q i) : ℝ)) :
    let w := chosenWeights n hn m (fun i => q i) (fun i => hq i)
    ∀ {F : ℚ} {ν ws A η : ℝ}, 1/w.theta < F → 1 < ν → 0 < ws → 0 < A → 0 ≤ η →
      (∀ k : Fin m, ws ≤ (w.w k : ℝ)) →
      (∀ k : Fin m, |Real.log 2-(rationalPoint p (fun i => q i) k : ℝ)| ≤ (q k : ℝ)^(-ν)) →
      arithmeticError w F ws+fixedAnalyticError w ν (F : ℝ) ws <
        ν*(A*(1-η)-(w.theta : ℝ))-(1-(w.theta : ℝ)) →
      1+arithmeticError w F ws+fixedAnalyticError w ν (F : ℝ) ws < collisionLimit w A η → False := by
  dsimp only
  intro F ν ws A η hF hν hws hA hη hw happrox hgap hcollision
  let w := chosenWeights n hn m (fun i => q i) (fun i => hq i)
  have hK : 0 < w.K := centerCount_pos (shape n hn).one_lt_c.le m
  have hFp : 0 < F := (div_pos (by norm_num) w.theta_pos).trans hF
  obtain ⟨B, hB⟩ := Filter.eventually_atTop.mp
    (eventual_no_fullRowMinor w p (fun i => q i) hK hFp hν hws hA hη
      (fun i => hq i) (fun _ => rfl) hw happrox hgap hcollision)
  obtain ⟨H, hH, ⟨minor⟩⟩ := MatrixCompactification.logTwo_cofinally_fullRowMinor
    n hn m q hq hgrowth (rationalPoint p (fun i => q i)) F hF B
  exact hB H hH.le minor

end
end LogTwo.Analysis
end Source0879

-- Source: LogTwo/FinalParameters.lean
section Source0880
namespace LogTwo
open Interpolation Arithmetic Parameters Analysis LogTwo.Geometry
open scoped BigOperators
noncomputable section

def remainingWeightCoefficient {m : ℕ} (w : Weights m) (ν : ℝ) : ℝ :=
  lcmConstant*m+(w.theta : ℝ)+Real.log 4+Real.log (w.K : ℝ)+ν+Real.log (200*(w.K : ℝ))

theorem totalError_le_uniform {m : ℕ} (w : Weights m) (F : ℚ) (ν W : ℝ)
    (hW : 0 < W) (hw : ∀ i, W ≤ (w.w i : ℝ)) :
    arithmeticError w F W+fixedAnalyticError w ν (F : ℝ) W ≤
      lcmConstant*(F : ℝ)*m/(w.v0 : ℝ)+100*(w.K : ℝ)/(w.w0 : ℝ)+
        2*Real.log 2/(w.v0 : ℝ)+ν/(F : ℝ)+remainingWeightCoefficient w ν/W := by
  calc
    _ ≤ (lcmConstant*(F : ℝ)*m/(w.v0 : ℝ)+(lcmConstant*m+(w.theta : ℝ))/W) +
        fixedAnalyticError w ν (F : ℝ) W := add_le_add (arithmeticError_le_uniform w F W hW hw) le_rfl
    _ = _ := by
      unfold fixedAnalyticError translationBudget holomorphicBudget remainingWeightCoefficient
      ring

theorem chosen_collisionLimit_eq (n : ℕ) (hn : 1 ≤ n) (m : ℕ)
    (q : Fin m → ℕ) (hq : ∀ i, 2 ≤ q i) :
    collisionLimit (chosenWeights n hn m q hq) (a (delta n)) (eta n) =
      (Real.log 2/8)*(eta n : ℝ)^2*
        (((b (delta n)/a (delta n) : ℚ) : ℝ)^m/((m : ℝ)+1)) := by
  have hs := shape n hn
  have hk : (centerCount (c (delta n)) m : ℝ) ≠ 0 := by
    exact_mod_cast (centerCount_pos hs.one_lt_c.le m).ne'
  have ht : (theta (delta n) : ℝ) ≠ 0 := by exact_mod_cast hs.theta_pos.ne'
  have ha : (a (delta n) : ℝ) ≠ 0 := by exact_mod_cast (hs.theta_pos.trans hs.theta_lt_a).ne'
  have hb : (b (delta n) : ℝ) ≠ 0 := by exact_mod_cast (hs.theta_pos.trans (hs.theta_lt_a.trans hs.a_lt_b)).ne'
  simp only [collisionLimit, chosenWeights, verticalWeight, horizontalWeight,
    Rat.cast_mul, Rat.cast_ofNat, Rat.cast_pow, Rat.cast_inv, Rat.cast_natCast, Rat.cast_div, div_pow]
  field_simp
  ring

theorem exists_dimension_total_budget (n : ℕ) (hn : 1 ≤ n) :
    ∃ m : ℕ, 1 ≤ m ∧
      100*(centerCount (c (delta n)) m : ℝ)/(horizontalWeight (b (delta n)) m : ℝ) < (epsilon n : ℝ)/8 ∧
      lcmConstant*(truncationFactor n : ℝ)*m/(verticalWeight (theta (delta n)) (b (delta n)) (c (delta n)) m : ℝ) < (epsilon n : ℝ)/8 ∧
      2*Real.log 2/(verticalWeight (theta (delta n)) (b (delta n)) (c (delta n)) m : ℝ) < (epsilon n : ℝ)/8 ∧
      2 < (Real.log 2/8)*(eta n : ℝ)^2*
        (((b (delta n)/a (delta n) : ℚ) : ℝ)^m/((m : ℝ)+1)) := by
  have hs := scalarConditions n hn
  have he : (0 : ℝ) < epsilon n := by exact_mod_cast hs.epsilon_pos
  have hη : (0 : ℝ) < eta n := by exact_mod_cast hs.eta_pos
  have hl : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  obtain ⟨m, hm, hc, har, hv, hcol⟩ := exists_dimension n hn ((epsilon n : ℝ)/800)
    (lcmConstant*(truncationFactor n : ℝ))
    (16*Real.log 2/(epsilon n : ℝ)) (16/(Real.log 2*(eta n : ℝ)^2)) (by positivity) 1
  have hθ := hs.shape.theta_pos
  have hB := hθ.trans (hs.shape.theta_lt_a.trans hs.shape.a_lt_b)
  have hvpos : (0 : ℝ) < verticalWeight (theta (delta n)) (b (delta n)) (c (delta n)) m := by
    exact_mod_cast verticalWeight_pos hθ hB hs.shape.one_lt_c.le m
  have hc' : (centerCount (c (delta n)) m : ℝ)/(horizontalWeight (b (delta n)) m : ℝ) < (epsilon n : ℝ)/800 := by
    simpa only [Rat.cast_div, Rat.cast_natCast] using hc
  refine ⟨m, hm, ?_, ?_, ?_, ?_⟩
  · rw [mul_div_assoc]
    linarith
  · have heq : lcmConstant*(truncationFactor n : ℝ)*m/(verticalWeight (theta (delta n)) (b (delta n)) (c (delta n)) m : ℝ) =
        (lcmConstant*(truncationFactor n : ℝ))*((m : ℝ)/(verticalWeight (theta (delta n)) (b (delta n)) (c (delta n)) m : ℝ)) := by ring
    rw [heq]; linarith
  · apply (div_lt_iff₀ hvpos).mpr
    have hh := (div_lt_iff₀ he).mp hv
    nlinarith
  · have hp : 0 < Real.log 2*(eta n : ℝ)^2 := by positivity
    have hh := (div_lt_iff₀ hp).mp hcol
    nlinarith

/-- The dimension is fixed first. The coefficient of 1/W then determines W,
and only then are the separated denominators chosen from the bad family. -/
theorem exists_small_total_parameters (n : ℕ) (hn : 1 ≤ n) {x : ℝ}
    (hbad : UnboundedApproximations x (nu n : ℝ)) :
    ∃ (m : ℕ) (p : ℕ → ℤ) (q : ℕ → ℕ) (hq : ∀ i, 2 ≤ q i) (W : ℝ),
      1 ≤ m ∧ 0 < W ∧
      (∀ i, W ≤ (ceilLogWeight (q i) : ℝ)) ∧
      (∀ i, i < m → denominatorSeparationFactor n m (chosenComparisonConstant n m)*
        (∏ j : Fin i, (ceilLogWeight (q j) : ℝ)) < (ceilLogWeight (q i) : ℝ)) ∧
      (∀ i, |x-(p i : ℝ)/q i| ≤ (q i : ℝ)^(-(nu n : ℝ))) ∧
      let w := chosenWeights n hn m (fun i => q i) (fun i => hq i)
      arithmeticError w (truncationFactor n) W+
        fixedAnalyticError w (nu n : ℝ) (truncationFactor n : ℝ) W < (epsilon n : ℝ) ∧
      2 < collisionLimit w (a (delta n)) (eta n) := by
  have hs := scalarConditions n hn
  have he : (0 : ℝ) < epsilon n := by exact_mod_cast hs.epsilon_pos
  have he8 : (0 : ℝ) < (epsilon n : ℝ)/8 := by positivity
  have hθ : (0 : ℝ) < theta (delta n) := by exact_mod_cast hs.shape.theta_pos
  have hν : (0 : ℝ) < nu n := by unfold nu; positivity
  obtain ⟨m, hm, hc, har, hv, hcol⟩ := exists_dimension_total_budget n hn
  let K := centerCount (c (delta n)) m
  have hK : (1 : ℝ) ≤ K := by
    exact_mod_cast (centerCount_pos hs.shape.one_lt_c.le m)
  have hlogK : 0 ≤ Real.log (K : ℝ) := Real.log_nonneg hK
  have hlog4 : (0 : ℝ) < Real.log 4 := Real.log_pos (by norm_num)
  have hlog200 : 0 ≤ Real.log (200*(K : ℝ)) := Real.log_nonneg (by linarith)
  let S : ℝ := lcmConstant*m+(theta (delta n) : ℝ)+Real.log 4+Real.log (K : ℝ)+
    (nu n : ℝ)+Real.log (200*(K : ℝ))
  have hS : 0 < S := by
    dsimp [S]
    have hl := lcmConstant_pos
    positivity
  let W : ℝ := S/((epsilon n : ℝ)/8)+1
  have hW : 0 < W := by dsimp [W]; positivity
  have hsmall : S/W < (epsilon n : ℝ)/8 := by
    apply (div_lt_iff₀ hW).mpr
    dsimp [W]
    rw [mul_add, mul_div_cancel₀ _ he8.ne', mul_one]
    linarith
  obtain ⟨p, q, hq⟩ := exists_sequential_approximations hbad
    (fun i previous => max W (denominatorSeparationFactor n m (chosenComparisonConstant n m)*
      (∏ j : Fin i, (ceilLogWeight (previous j) : ℝ))))
  have hq2 : ∀ i, 2 ≤ q i := fun i => (hq i).1
  have hw : ∀ i, W ≤ (ceilLogWeight (q i) : ℝ) := by
    intro i
    exact ((le_max_left _ _).trans_lt (hq i).2.1).le.trans (ceilLogWeight_bounds _).1
  have hgrowth : ∀ i, i < m → denominatorSeparationFactor n m (chosenComparisonConstant n m)*
      (∏ j : Fin i, (ceilLogWeight (q j) : ℝ)) < (ceilLogWeight (q i) : ℝ) := by
    intro i _
    exact ((le_max_right _ _).trans_lt (hq i).2.1).trans_le (ceilLogWeight_bounds _).1
  refine ⟨m, p, q, hq2, W, hm, hW, hw, hgrowth, (fun i => (hq i).2.2), ?_, ?_⟩
  · let w := chosenWeights n hn m (fun i => q i) (fun i => hq2 i)
    have hb := totalError_le_uniform w (truncationFactor n) (nu n : ℝ) W hW (fun i => hw i)
    change arithmeticError w (truncationFactor n) W+fixedAnalyticError w (nu n : ℝ) (truncationFactor n : ℝ) W ≤
      lcmConstant*(truncationFactor n : ℝ)*m/(verticalWeight (theta (delta n)) (b (delta n)) (c (delta n)) m : ℝ)+
        100*(centerCount (c (delta n)) m : ℝ)/(horizontalWeight (b (delta n)) m : ℝ)+
        2*Real.log 2/(verticalWeight (theta (delta n)) (b (delta n)) (c (delta n)) m : ℝ)+
        (nu n : ℝ)/(truncationFactor n : ℝ)+S/W at hb
    have hfactor : (nu n : ℝ)/(truncationFactor n : ℝ) = (epsilon n : ℝ)/4 := by
      exact_mod_cast nu_div_factor n hn
    change arithmeticError w (truncationFactor n) W+fixedAnalyticError w (nu n : ℝ) (truncationFactor n : ℝ) W < _
    linarith
  · rw [chosen_collisionLimit_eq n hn]
    exact hcol

end
end LogTwo
end Source0880

-- Source: LogTwo/Main.lean
section Source0881
-- Modified in this edition: unused plain lemmas removed; see reduction.json.
namespace LogTwo
open Interpolation Arithmetic Parameters Analysis
noncomputable section

/-- No unbounded family of approximations exists at any exponent 2+1/n. -/
theorem not_unbounded_logTwo (n : ℕ) (hn : 1 ≤ n) :
    ¬ UnboundedApproximations (Real.log 2) (nu n : ℝ) := by
  intro hbad
  obtain ⟨m, p, q, hq, W, hm, hW, hw, hgrowth, happrox, herror, hcollision⟩ :=
    exists_small_total_parameters n hn hbad
  have hs := scalarConditions n hn
  let w := chosenWeights n hn m (fun i => q i) (fun i => hq i)
  have hF : 1/w.theta < truncationFactor n := by
    have hθ := hs.shape.theta_pos
    change 1/theta (delta n) < truncationFactor n
    have hl : (1 : ℚ)/theta (delta n) < 2/theta (delta n) := by
      exact div_lt_div_of_pos_right (by norm_num) hθ
    exact hl.trans hs.factor_gt
  have hν : (1 : ℝ) < nu n := by
    unfold nu
    push_cast
    have : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
    linarith [one_div_pos.mpr this]
  apply logTwo_contradiction_of_budgets n hn m (fun i => p i) q hq hgrowth
    hF hν hW (show (0 : ℝ) < a (delta n) by exact_mod_cast hs.shape.theta_pos.trans hs.shape.theta_lt_a)
    (show (0 : ℝ) ≤ eta n by exact_mod_cast hs.eta_pos.le) (fun i => hw i)
  · intro k
    simpa only [rationalPoint, Rat.cast_div, Rat.cast_intCast, Rat.cast_natCast] using happrox k
  · have hg : (epsilon n : ℝ) < (finalGap n : ℝ) := by exact_mod_cast hs.epsilon_lt_gap
    have hgap := herror.trans hg
    simpa only [finalGap, Rat.cast_sub, Rat.cast_mul, Rat.cast_one, chosenWeights] using hgap
  · have he : (epsilon n : ℝ) < (1 : ℝ)/2 := by
      have hh : (epsilon n : ℝ) < ((1/2 : ℚ) : ℝ) := Rat.cast_lt.mpr hs.epsilon_lt_half
      norm_num at hh ⊢
      exact hh
    linarith

theorem logTwo_sequentialLowerBound : SequentialLowerBound (Real.log 2) := by
  by_contra h
  obtain ⟨n, hn, hbad⟩ := exists_unbounded_of_not_sequential h
  apply not_unbounded_logTwo n hn
  simpa only [nu, Rat.cast_add, Rat.cast_ofNat, Rat.cast_div, Rat.cast_one, Rat.cast_natCast] using hbad

/-- Unconditional theorem for the irrationality exponent of the natural log. -/
theorem logTwo_exponent_eq_two : LogTwoExponentTwo :=
  logTwoExponentTwo_of_sequentialLowerBound logTwo_sequentialLowerBound

end
end LogTwo
end Source0881

-- Source: LogTwo/IrrationalityExponent.lean
section Source0882
/- Copyright 2026 Kenta Kitamura. Licensed under Apache-2.0. -/

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
end Source0882

-- Source: LogTwo/Target.lean
section Source0883
-- Modified in this edition: unused plain lemmas removed; see reduction.json.
namespace LogTwo

/-- The independently stated reciprocal-denominator definition agrees with
the comparison library's negative-power definition. This is a proved bridge,
not an alias used as the public definition. -/
theorem approximationExponents_eq_comparison (x : ℝ) :
    {μ : ℝ | 0 < μ ∧ Set.Infinite
      {r : ℚ | 1 < r.den ∧ 0 < |x - (r : ℝ)| ∧
        |x - (r : ℝ)| < 1 / (r.den : ℝ) ^ μ}} = OAI.PiExponent.ApproximationExponents x := by
  have hsets (μ : ℝ) :
      {r : ℚ | 1 < r.den ∧ 0 < |x - (r : ℝ)| ∧
        |x - (r : ℝ)| < 1 / (r.den : ℝ) ^ μ} =
        OAI.PiExponent.GoodRationalApproximations x μ := by
    ext r
    simp [OAI.PiExponent.GoodRationalApproximations, Nat.lt_iff_add_one_le,
      Real.rpow_neg (Nat.cast_nonneg r.den), one_div]
  ext μ
  change (0 < μ ∧ _ ) ↔ (0 < μ ∧ _)
  rw [hsets μ]

/-- Final public target: the project's own irrationality exponent of log 2 is 2. -/
theorem irrationalityExponent_log_two : irrationalityExponent (Real.log 2) = 2 := by
  rw [irrationalityExponent, approximationExponents_eq_comparison]
  exact logTwo_exponent_eq_two

end LogTwo
end Source0883

-- Source: LogTwo.lean
section Source0884

end Source0884

/-
Modification notice for the LogTwo project.
Adapted from openai/math (Apache-2.0), revision adc7f1241b42e322a6451854ab7e4b4c146bf78a.
Changes: Generalize the matrix-counting strategy to arbitrary rational weights.
See ../../../THIRD_PARTY_NOTICES.txt for provenance and the recorded changes.
-/

module

public import LogTwo.Analysis.AnalyticUpper
public import LogTwo.Geometry.WeightedIndices
public import OAI.NumberTheory.PiExponent.Analysis.TranslationCountLimit

@[expose] public section
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

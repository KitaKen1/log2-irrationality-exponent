module
public import LogTwo.Analysis.RealCenterMatrix
public import OAI.NumberTheory.PiExponent.Analysis.AnalyticDeterminantCollision
public import OAI.NumberTheory.PiExponent.Analysis.DeterminantAnalyticBound
public import OAI.NumberTheory.PiExponent.Approximation.MatrixTranslationBounds
@[expose] public section
namespace LogTwo.Analysis
open OAI PiExponent MatrixTranslation RowTranslation AnalyticCollision PeriodAnalytic
open LogTwo.Interpolation
noncomputable section

-- Apply the generic arbitrary-center collision theorem.
-- This is only the analytic determinant for one translation choice family.
-- Bounds on actualRowScalar and summation over choice families remain separate.
theorem actual_analytic_summand_exp_bound {m : ℕ} {w : Weights m} {H : ℚ}
    {r : Fin m → ℚ} {T : Fin m → ℕ} (minor : FullRowMinor w H r T)
    (hK : 0 < w.K) (hH : 0 < H) {wstar : ℝ} (hws : 0 < wstar)
    (hw : ∀ k, wstar ≤ (w.w k : ℝ))
    (f : ∀ i, RowChoices (transverseIndices (fun k => (w.w k : ℝ)) (H : ℝ))
      (InterpolationMatrix.exponentVector (minor.rows i).beta) (minor.rows i).s) :
    let S := transverseIndices (fun k => (w.w k : ℝ)) (H : ℝ)
    ‖Matrix.det (fun i c => actualAnalyticRow (minor.rows i) S (f i) (minor.columns c))‖ ≤
      Real.exp (-(Real.log 2 / 4) *
        (∑ a : S, (Collision.multiplicity Finset.univ (fun i => (f i).1) a : ℝ)^2) +
        (minor.size : ℝ) * (H : ℝ) *
          (100*(w.K : ℝ)/(w.w0 : ℝ) + Real.log (200*(w.K : ℝ))/wstar +
            Real.log 2/(w.v0 : ℝ) + Collision.collisionRemainder minor.size (H : ℝ))) := by
  classical
  let S := transverseIndices (fun k => (w.w k : ℝ)) (H : ℝ)
  let R : NNReal := ⟨100*(w.K : ℝ), by positivity⟩
  have hR : 0 < R := by change (0 : ℝ) < 100*(w.K : ℝ); positivity
  have horder (i : Fin minor.size) : ((minor.rows i).s : ℝ) ≤ (H : ℝ)/(w.v0 : ℝ) := by
    have hr := (minor.row_valid i).2
    have hb : (0 : ℚ) ≤ (∑ k, w.w k*(minor.rows i).beta k)/w.theta :=
      div_nonneg (Finset.sum_nonneg (fun k _ => mul_nonneg (w.w_pos k).le (Nat.cast_nonneg _)))
        w.theta_pos.le
    have hs : w.v0*(minor.rows i).s ≤ H := (le_add_of_nonneg_right hb).trans hr.le
    apply (le_div_iff₀ (by exact_mod_cast w.v0_pos)).mpr
    exact_mod_cast (by simpa only [mul_comm] using hs)
  have hell : ((∑ i, ((minor.rows i).s-(f i).2.2) : ℕ) : ℝ) ≤
      (Fintype.card (Fin minor.size) : ℝ)*(H : ℝ)/(w.v0 : ℝ) := by
    simp only [Nat.cast_sum]
    calc
      _ ≤ ∑ i : Fin minor.size, (H : ℝ)/(w.v0 : ℝ) := by
        apply Finset.sum_le_sum
        intro i _
        have hsub : (((minor.rows i).s-(f i).2.2 : ℕ) : ℝ) ≤ (minor.rows i).s := by
          exact_mod_cast Nat.sub_le (minor.rows i).s (f i).2.2
        exact hsub.trans (horder i)
      _ = _ := by simp; ring
  have hR1 : (1 : ℝ) ≤ R := by
    have hk : (1 : ℝ) ≤ w.K := by exact_mod_cast hK
    change 1 ≤ 100*(w.K : ℝ)
    linarith
  have hbound := translated_row_determinant_exp_bound
    (fun i => (f i).1)
    (fun (a : S) c => columnFunction (minor.columns c).h (minor.columns c).alpha a.1)
    (fun i => ((minor.rows i).j : ℂ)*(Real.log 2 : ℂ))
    (fun i => (minor.rows i).s-(f i).2.2) R hR
    (H := (H : ℝ)) (A := (R : ℝ)/(w.w0 : ℝ)+Real.log (2*(R : ℝ))/wstar)
    (v := (w.v0 : ℝ)) (by exact_mod_cast hH)
    (fun a c => differentiable_columnFunction _ _ _)
    (fun a c z hz => norm_columnFunction_le (minor.columns c).h (minor.columns c).alpha a.1
      (fun k => (w.w k : ℝ)) (H := (H : ℝ)) (w0 := (w.w0 : ℝ)) hR1
      (by exact_mod_cast hH.le) (by exact_mod_cast w.w0_pos) hws hw
      (by exact_mod_cast minor.column_valid c)
      (by simpa only [Metric.mem_sphere, dist_zero_right] using hz.le))
    (fun i => logTwo_center_radius (minor.row_valid i).1) hell
  have hRv : (R : ℝ) = 100*(w.K : ℝ) := rfl
  rw [hRv, show (2 : ℝ)*(100*(w.K : ℝ)) = 200*(w.K : ℝ) by ring] at hbound
  simpa only [actualAnalyticRow, Fintype.card_fin] using hbound

end
end LogTwo.Analysis

/-
Modification notice for the LogTwo project.
Adapted from openai/math (Apache-2.0), revision adc7f1241b42e322a6451854ab7e4b4c146bf78a.
Changes: Adapt analytic row-series interfaces to the nonperiodic centers j * log(2).
See ../../../THIRD_PARTY_NOTICES.txt for provenance and the recorded changes.
-/

module

public import LogTwo.Analysis.RealCenterIdentity
public import OAI.NumberTheory.PiExponent.Analysis.PeriodAnalytic
public import OAI.NumberTheory.PiExponent.Analysis.AnalyticRowSeries

@[expose] public section
namespace LogTwo.Analysis
open OAI PiExponent AnalyticCollision PeriodAnalytic
noncomputable section

theorem rowTest_logTwo_exponentialMonomial_eq_coeff (b : ℂ) (j h d ell : ℕ) :
    rowTest ell (fun t => exponentialMonomial b (h : ℂ) d
      ((j : ℂ) * (Real.log 2 : ℂ) + Complex.log (1+t))) =
      PowerSeries.coeff ell
        (periodSeries (b * (2 : ℂ)^(j*h)) ((j : ℂ) * (Real.log 2 : ℂ)) h d) := by
  rw [← rowTest_periodFunction_eq_coeff]
  apply rowTest_congr_sphere
  intro t ht
  have hn : ‖t‖ = (1/2 : ℝ) := by
    simpa only [Metric.mem_sphere, dist_zero_right] using ht
  have ht0 : 1+t ≠ 0 := by
    intro heq
    have heq' : t = -1 := by linear_combination heq
    simp [heq'] at hn
  symm
  exact logTwo_scaled_log_monomial_identity b j h d ht0

/-- The nonperiodic scalar is absorbed into the entire column function. -/
theorem scaled_periodMonomial_coeff_eq_rowTest {m : ℕ} (j h ell : ℕ)
    (a : Fin m → ℕ) (A : Fin m →₀ ℕ) :
    (2 : ℂ)^(j*h) * PowerSeries.coeff ell
      ((MatrixTranslation.periodMonomial j (Real.log 2 : ℂ) h a).coeff A) =
      rowTest ell (fun t => columnFunction h a A
        ((j : ℂ)*(Real.log 2 : ℂ) + Complex.log (1+t))) := by
  unfold columnFunction
  rw [rowTest_logTwo_exponentialMonomial_eq_coeff,
    MatrixTranslation.periodMonomial_coeff]
  have he : periodSeries
      (((∏ i, (a i).choose (A i) : ℕ) : ℂ) * (2 : ℂ)^(j*h))
      ((j : ℂ)*(Real.log 2 : ℂ)) h (∑ i, (a i - A i)) =
      PowerSeries.C ((2 : ℂ)^(j*h)) *
        (((∏ i, (a i).choose (A i) : ℕ) : PowerSeries ℂ) *
          (1+PowerSeries.X)^h *
            (MatrixTranslation.periodCoordinate j (Real.log 2 : ℂ))^(∑ i, (a i - A i))) := by
    simp only [periodSeries, MatrixTranslation.periodCoordinate, map_mul, map_natCast]
    ring
  rw [he, PowerSeries.coeff_C_mul]

/-- Radius 100*K contains every actual row center with the margin needed
for the uniform translated Taylor series. -/
theorem logTwo_center_radius {j K : ℕ} (hj : j < K) :
    ‖(j : ℂ)*(Real.log 2 : ℂ)‖ + 3/4 ≤ (100*(K : ℝ))/2 := by
  have hlog : 0 ≤ Real.log (2 : ℝ) := Real.log_nonneg (by norm_num)
  have hlog1 : Real.log (2 : ℝ) ≤ 1 := by
    have h := Real.log_lt_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)
      (by norm_num : (2 : ℝ) ≠ 1)
    linarith
  have hjK : (j : ℝ)+1 ≤ K := by exact_mod_cast hj
  rw [norm_mul, Complex.norm_natCast, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg hlog]
  have hm := mul_le_mul_of_nonneg_left hlog1 (Nat.cast_nonneg j : (0 : ℝ) ≤ j)
  nlinarith

/-- An actual-center analytic row is the sum of its normalized Taylor terms.
The coefficient sequence depends only on the transverse index and the column. -/
theorem hasSum_logTwo_column_row {m : ℕ} (h : ℕ) (a : Fin m → ℕ)
    (A : Fin m →₀ ℕ) (w : Fin m → ℝ) {H w0 wstar : ℝ}
    (hH : 0 ≤ H) (hw0 : 0 < w0) (hws : 0 < wstar)
    (hw : ∀ i, wstar ≤ w i) (hcol : w0*h + ∑ i, w i*a i ≤ H)
    {j K : ℕ} (hj : j < K) (ell : ℕ) :
    HasSum (fun d => rowTest ell (fun t =>
      (((j : ℂ)*(Real.log 2 : ℂ)+Complex.log (1+t))/(100*(K : ℂ)))^d) *
      normalizedTaylorCoeff (columnFunction h a A) (100*(K : ℝ)) d)
      (rowTest ell (fun t => columnFunction h a A
        ((j : ℂ)*(Real.log 2 : ℂ)+Complex.log (1+t)))) := by
  have hK : (1 : ℝ) ≤ K := by
    have hk : 1 ≤ K := by omega
    exact_mod_cast hk
  let R : NNReal := ⟨100*(K : ℝ), by positivity⟩
  have hR : 0 < R := by change (0 : ℝ) < 100*(K : ℝ); positivity
  have hbound : ∀ z ∈ Metric.sphere (0 : ℂ) (R : ℝ),
      ‖columnFunction h a A z‖ ≤
        Real.exp (H*((R : ℝ)/w0+Real.log (2*(R : ℝ))/wstar)) := by
    intro z hz
    apply norm_columnFunction_le h a A w (by change 1 ≤ 100*(K : ℝ); linarith)
      hH hw0 hws hw hcol
    simpa only [Metric.mem_sphere, dist_zero_right] using (Metric.mem_sphere.mp hz).le
  have hs := hasSum_translated_row (differentiable_columnFunction h a A) hR
    (Real.exp_pos _).le hbound (logTwo_center_radius hj) ell
  change HasSum (fun d => rowTest ell (fun t =>
      (((j : ℂ)*(Real.log 2 : ℂ)+Complex.log (1+t))/((100*(K : ℝ) : ℝ) : ℂ))^d) *
      normalizedTaylorCoeff (columnFunction h a A) (100*(K : ℝ)) d) _ at hs
  simpa only [Complex.ofReal_mul, Complex.ofReal_natCast, Complex.ofReal_ofNat] using hs

/-- The test factor in each Taylor term decays geometrically. -/
theorem norm_logTwo_rowTest_power_le {j K : ℕ} (hj : j < K) (ell d : ℕ) :
    ‖rowTest ell (fun t =>
      (((j : ℂ)*(Real.log 2 : ℂ)+Complex.log (1+t))/(100*(K : ℂ)))^d)‖ ≤
        (2 : ℝ)^ell * (1/2 : ℝ)^d := by
  have hK : (0 : ℝ) < K := by exact_mod_cast (show 0 < K by omega)
  simpa only [Complex.ofReal_mul, Complex.ofReal_ofNat, Complex.ofReal_natCast] using
    norm_rowTest_shifted_power_le (by positivity : (0 : ℝ) < 100*(K : ℝ))
      (logTwo_center_radius hj) ell d

/-- Collision of the transverse index and Taylor degree gives identical
coefficient rows, independently of the original center j. -/
theorem actual_taylor_coefficient_collision {ι : Type*} [Fintype ι] [DecidableEq ι]
    {m : ℕ} (h : ι → ℕ) (a : ι → Fin m → ℕ) (R : ℝ)
    (group : ι → Fin m →₀ ℕ) (degree : ι → ℕ)
    {i j : ι} (hij : i ≠ j) (hg : group i = group j) (hd : degree i = degree j) :
    Matrix.det (fun r c => normalizedTaylorCoeff
      (columnFunction (h c) (a c) (group r)) R (degree r)) = 0 := by
  exact coefficient_det_eq_zero_of_collision
    (fun A d c => normalizedTaylorCoeff (columnFunction (h c) (a c) A) R d)
    group degree hij hg hd

end
end LogTwo.Analysis

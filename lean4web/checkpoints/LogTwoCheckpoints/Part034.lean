/- Generated rc4 checkpoint for LogTwo.
Modified from the reduced edition: new imports, separate module compilation,
and synchronous elaboration. Original source blocks and notices are retained.
See ../../../THIRD_PARTY_NOTICES.txt and ../../reduction.json.
-/
module
public import LogTwoCheckpoints.Part000
public import LogTwoCheckpoints.Part002
public import LogTwoCheckpoints.Part003
public import LogTwoCheckpoints.Part004
public import LogTwoCheckpoints.Part011
public import LogTwoCheckpoints.Part012
public import LogTwoCheckpoints.Part013
public import LogTwoCheckpoints.Part014
public import LogTwoCheckpoints.Part020
public import LogTwoCheckpoints.Part030
public import LogTwoCheckpoints.Part033
public import Mathlib.AlgebraicGeometry.IdealSheaf.Basic
public import Mathlib.Analysis.Complex.Polynomial.Basic
public import Mathlib.Analysis.Real.Pi.Bounds
public import Mathlib.Analysis.SpecialFunctions.Complex.Analytic
public import Mathlib.Analysis.SpecialFunctions.Complex.LogBounds
public import Mathlib.Data.FunLike.Basic
public import Mathlib.RingTheory.PowerSeries.Log
@[expose] public section
set_option Elab.async false

-- Source: LogTwo/Geometry/MatrixSectionPolynomial.lean
section Source0850
/-
Modification notice for the LogTwo project.
Adapted from openai/math (Apache-2.0), revision adc7f1241b42e322a6451854ab7e4b4c146bf78a.
Changes: Adapt the section-polynomial strategy to the varying Y-centers.
See ../THIRD_PARTY_NOTICES.txt for provenance and the recorded changes.
-/

/-! Global sections give bounded polynomials and, eventually, all formal packets.
The Y centers vary, and all bounds use the actual matrix weights. -/
namespace LogTwo.Geometry.MatrixCompactification
open OAI PiExponent AlgebraicGeometry CategoryTheory
open LogTwo.Interpolation LogTwo.Parameters LogTwo.Arithmetic
open AffineJetCoefficientInterface BlowupJetSurjectivity
noncomputable section
variable {m : ℕ} (w : Weights m)

abbrev sectionPolynomial (k : ℕ) (e : Frame (affineChart w) (MatrixBlowup.hyperplane w)) :=
  coefficient (affineChart w) (MatrixBlowup.hyperplane w) k e

theorem frame_exists : Nonempty (Frame (affineChart w) (MatrixBlowup.hyperplane w)) :=
  WeightedAffineFrame.affineFrame_nonempty (exponents w) (constantIndex w)
    ((scale w).exponents_constant (rationalColumnWeight_pos w)) (coordinateIndex w)
    ((scale w).exponents_coordinate (rationalColumnWeight_pos w))

theorem exponent_budget (j : Index w) :
    Finsupp.weight (fun i => (rationalColumnWeight w i : ℝ)) (exponents w j) ≤
      ((scale w).radius : ℝ) := by
  have hr : (∑ i, (rationalColumnWeight w i : ℝ) * (exponents w j i : ℝ)) ≤
      ((scale w).radius : ℝ) := by exact_mod_cast monomial_budget w j
  simpa only [Finsupp.weight_eq_sum, nsmul_eq_mul, mul_comm] using hr

theorem eventual_supportBound :
    ProjectiveCoefficientBound.EventualBound (affineChart w) (MatrixBlowup.hyperplane w)
      (fun i => (rationalColumnWeight w i : ℝ)) ((scale w).radius : ℝ) :=
  WeightedGlobalSectionBound.eventual_supportBound (exponents w) (constantIndex w)
    ((scale w).exponents_constant (rationalColumnWeight_pos w)) (coordinateIndex w)
    ((scale w).exponents_coordinate (rationalColumnWeight_pos w)) _ _ (exponent_budget w)

theorem formalPackets_surjective_of_jetRestriction
    (y : Fin w.K → ℂ) (hy0 : ∀ j, y j ≠ 0) (hy : Function.Injective y)
    (a : Fin w.K → Fin m → ℂ) (F : ℚ) (hF : 1 / w.theta < F) (k : ℕ)
    (e : Frame (affineChart w) (MatrixBlowup.hyperplane w))
    (hjet : Function.Surjective
      (jetRestriction (centerIdeal w y a (truncationOrders w F)) (MatrixBlowup.hyperplane w) k)) :
    Function.Surjective (fun s j => JetGeometry.rationalCoefficientPacket (jetWeight w)
      (k * (scale w).radius) (formalJetAt (y j) (a j) (sectionPolynomial w k e s))) := by
  have he : ∀ i, (scale w).radius ≤ ((scale w).jetPowers i : ℚ) * jetWeight w i := by
    intro i
    rw [mul_comm, jet_balance]
  have hs : (((centerIdeal w y a (truncationOrders w F))^k).support : Set (space w)) ⊆
      (affineChart w).opensRange := by
    cases k with
    | zero => simp
    | succ k => simpa using centerIdeal_support_subset_chart w y a (truncationOrders w F)
  apply formalJetAt_packets_surjective_of_quotient y hy0 hy a (truncationOrders w F)
    (scale w).jetPowers (scale w).jetPowers_pos (jetWeight w) (jetWeight_pos w)
    (fun i => (truncation_weight_strict w F hF i).le) (scale w).radius he k (sectionPolynomial w k e)
  exact AffineJetPolynomial.polynomialQuotient_surjective_of_jetRestriction
    (centerIdeal w y a (truncationOrders w F)) (MatrixBlowup.hyperplane w) k (affineChart w) e
    (jetProductIdeal y a (truncationOrders w F) (scale w).jetPowers)
    (centerIdeal_restrict w y a (truncationOrders w F)) hs hjet

end
end LogTwo.Geometry.MatrixCompactification
end Source0850

-- Source: LogTwo/Geometry/MatrixInterpolation.lean
section Source0851
/-! The geometric interpolation theorem for the actual log-two matrix.
The certificates have all rows, rational columns and a nonzero rational
minor. The analytic upper estimate and final irrationality-exponent theorem
are not consequences of interpolation alone. -/
namespace LogTwo.Geometry.MatrixCompactification
open OAI PiExponent PiExponentApprox
open LogTwo.Interpolation LogTwo.Parameters LogTwo.Arithmetic
noncomputable section

/-- All sufficiently large multiples of the common radius give a full-row minor. -/
theorem logTwo_eventual_fullRowMinor
    (n : ℕ) (hn : 1 ≤ n) (m : ℕ) (q : ℕ → ℕ) (hq : ∀ i, 2 ≤ q i)
    (hgrowth : ∀ i, i < m →
      denominatorSeparationFactor n m (chosenComparisonConstant n m) *
        (∏ j : Fin i, (ceilLogWeight (q j) : ℝ)) < (ceilLogWeight (q i) : ℝ))
    (r : Fin m → ℚ) :
    let w := chosenWeights n hn m (fun i => q i) (fun i => hq i)
    ∀ (F : ℚ), 1 / w.theta < F →
      ∃ N : ℕ, ∀ k : ℕ, N ≤ k → Nonempty
        (FullRowMinor w (k * (scale w).radius) r (truncationOrders w F)) := by
  dsimp only
  intro F hF
  let w := chosenWeights n hn m (fun i => q i) (fun i => hq i)
  obtain ⟨N, hN⟩ := MatrixBlowup.logTwo_eventual_jetRestriction_surjective n hn m q hq hgrowth r F hF
  obtain ⟨M, hM⟩ := eventual_supportBound w
  obtain ⟨e⟩ := frame_exists w
  refine ⟨max N M, fun k hk => ?_⟩
  apply fullRowMinor_of_formal_packets w (k * (scale w).radius) r (truncationOrders w F)
    (fun i => (truncation_weight_strict w F hF i).le) (sectionPolynomial w k e)
  · intro s
    apply (FrameEquationFamily.hasWeightedDegreeLE_iff_supportBound _ _ _).mpr
    have hd := hM k (le_trans (le_max_right N M) hk) e s
    rw [cast_rationalColumnWeight] at hd
    simpa only [Rat.cast_mul, Rat.cast_natCast] using hd
  · exact formalPackets_surjective_of_jetRestriction w (fun j => 2^j.val)
      (fun j => pow_ne_zero j.val (by norm_num))
      (complex_centerY_injective.comp Fin.val_injective) (fun j i => (j.val : ℂ) * (r i : ℂ))
      F hF k e (hN k (le_trans (le_max_left N M) hk))

/-- The degree cutoff can exceed any prescribed rational lower threshold. -/
theorem logTwo_cofinally_fullRowMinor
    (n : ℕ) (hn : 1 ≤ n) (m : ℕ) (q : ℕ → ℕ) (hq : ∀ i, 2 ≤ q i)
    (hgrowth : ∀ i, i < m →
      denominatorSeparationFactor n m (chosenComparisonConstant n m) *
        (∏ j : Fin i, (ceilLogWeight (q j) : ℝ)) < (ceilLogWeight (q i) : ℝ))
    (r : Fin m → ℚ) :
    let w := chosenWeights n hn m (fun i => q i) (fun i => hq i)
    ∀ (F : ℚ), 1 / w.theta < F → ∀ B : ℚ, ∃ H : ℚ,
      B < H ∧ Nonempty (FullRowMinor w H r (truncationOrders w F)) := by
  dsimp only
  intro F hF B
  let w := chosenWeights n hn m (fun i => q i) (fun i => hq i)
  obtain ⟨N, hN⟩ := logTwo_eventual_fullRowMinor n hn m q hq hgrowth r F hF
  obtain ⟨k, hk⟩ := exists_nat_gt (max (N : ℚ) (B / (scale w).radius))
  have hNk : N ≤ k := by exact_mod_cast (le_of_lt (lt_of_le_of_lt (le_max_left _ _) hk))
  refine ⟨k * (scale w).radius, ?_, hN k hNk⟩
  have hR : (0 : ℚ) < (scale w).radius := by exact_mod_cast (scale w).radius_pos
  exact (div_lt_iff₀ hR).mp (lt_of_le_of_lt (le_max_right _ _) hk)

end
end LogTwo.Geometry.MatrixCompactification
end Source0851

-- Source: OAI/NumberTheory/PiExponent/Analysis/AnalyticCollision.lean
section Source0852
-- Modified in this edition: unused plain lemmas removed; see reduction.json.
/-
Modification notice for the LogTwo project.
Derived from openai/math (Apache-2.0), revision adc7f1241b42e322a6451854ab7e4b4c146bf78a.
Original source: lean/OAI/NumberTheory/PiExponent/Analysis/AnalyticCollision.lean
Changes: Convert module/import declarations to the Lean 4.34 public module format.
See ../THIRD_PARTY_NOTICES.txt for provenance and the recorded changes.
-/

namespace OAI

open scoped BigOperators
open Complex Finset

namespace PiExponent.AnalyticCollision

noncomputable def exponentialMonomial (b h : ℂ) (d : ℕ) (z : ℂ) : ℂ :=
  b * Complex.exp (h * z) * z ^ d

theorem differentiable_exponentialMonomial (b h : ℂ) (d : ℕ) :
    Differentiable ℂ (exponentialMonomial b h d) := by
  exact ((Complex.differentiable_exp.comp (differentiable_id.const_mul h)).const_mul b).mul
    (differentiable_id.pow d)

theorem norm_exponentialMonomial_le (b h : ℂ) (d : ℕ) {z : ℂ} {R : ℝ}
    (hR : 0 ≤ R) (hz : ‖z‖ ≤ R) :
    ‖exponentialMonomial b h d z‖ ≤ ‖b‖ * Real.exp (‖h‖ * R) * R ^ d := by
  unfold exponentialMonomial
  simp only [norm_mul, norm_pow]
  apply mul_le_mul_of_nonneg
  · apply mul_le_mul_of_nonneg_left _ (norm_nonneg b)
    exact (Complex.norm_exp_le_exp_norm _).trans
      (Real.exp_le_exp.mpr (by simpa only [norm_mul] using mul_le_mul_of_nonneg_left hz (norm_nonneg h)))
  · exact pow_le_pow_left₀ (norm_nonneg z) hz d
  · positivity
  · exact pow_nonneg hR d

noncomputable def normalizedTaylorCoeff (f : ℂ → ℂ) (R : ℝ) (d : ℕ) : ℂ :=
  cauchyPowerSeries f 0 R d (fun _ => (R : ℂ))

theorem norm_normalizedTaylorCoeff_le {f : ℂ → ℂ} {R D : ℝ} (hR : 0 < R)
    (hD : ∀ z ∈ Metric.sphere (0 : ℂ) R, ‖f z‖ ≤ D) (d : ℕ) :
    ‖normalizedTaylorCoeff f R d‖ ≤ D := by
  unfold normalizedTaylorCoeff
  rw [cauchyPowerSeries_apply]
  calc
    _ ≤ R * (R⁻¹ * D) := by
      apply circleIntegral.norm_two_pi_i_inv_smul_integral_le_of_norm_le_const hR.le
      intro z hz
      have hzR : ‖z‖ = R := by simpa only [Metric.mem_sphere, dist_zero_right] using hz
      simp only [sub_zero, norm_smul, norm_pow, norm_div, Complex.norm_real,
        Real.norm_eq_abs, abs_of_pos hR, norm_inv, hzR, div_self (ne_of_gt hR),
        one_pow, one_mul]
      exact mul_le_mul_of_nonneg_left (hD z hz) (inv_nonneg.mpr hR.le)
    _ = D := by field_simp

theorem hasSum_normalizedTaylorCoeff {f : ℂ → ℂ} (hf : Differentiable ℂ f)
    {R : NNReal} (hR : 0 < R) (z : ℂ) :
    HasSum (fun d => normalizedTaylorCoeff f R d * (z / (R : ℂ)) ^ d) (f z) := by
  convert! (hf.hasFPowerSeriesOnBall 0 hR).hasSum (y := z) (by simp) using 1
  · funext d
    simp only [normalizedTaylorCoeff, cauchyPowerSeries,
      ContinuousMultilinearMap.mkPiRing_apply, Fin.prod_const, smul_eq_mul]
    have hr : (R : ℂ) ≠ 0 := by exact_mod_cast ne_of_gt hR
    rw [div_pow]
    field_simp
  · simp

theorem norm_det_le_factorial_mul_pow {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A : Matrix ι ι ℂ) {D : ℝ} (hD : 0 ≤ D) (hA : ∀ i j, ‖A i j‖ ≤ D) :
    ‖A.det‖ ≤ (Fintype.card ι).factorial * D ^ Fintype.card ι := by
  rw [Matrix.det_apply]
  calc
    _ ≤ ∑ σ : Equiv.Perm ι, ‖σ.sign • ∏ i, A (σ i) i‖ := norm_sum_le _ _
    _ = ∑ σ : Equiv.Perm ι, ∏ i, ‖A (σ i) i‖ := by
      apply Finset.sum_congr rfl
      intro σ _
      rcases Int.units_eq_one_or σ.sign with hs | hs <;> simp [hs, norm_prod]
    _ ≤ ∑ _σ : Equiv.Perm ι, D ^ Fintype.card ι := by
      apply Finset.sum_le_sum
      intro σ _
      calc
        _ ≤ ∏ _index : ι, |D| := Finset.prod_le_prod₀
          (fun index _ => norm_nonneg _) (fun index _ => (hA (σ index) index).trans (le_abs_self D))
        _ = D ^ Fintype.card ι := by simp [abs_of_nonneg hD]
    _ = _ := by simp [Fintype.card_perm]

noncomputable def rowTest (ell : ℕ) (f : ℂ → ℂ) : ℂ :=
  cauchyPowerSeries f 0 (1 / 2) ell (fun _ => 1)

theorem norm_rowTest_le {f : ℂ → ℂ} {D : ℝ}
    (hD : ∀ t ∈ Metric.sphere (0 : ℂ) (1 / 2), ‖f t‖ ≤ D) (ell : ℕ) :
    ‖rowTest ell f‖ ≤ (2 : ℝ) ^ ell * D := by
  unfold rowTest
  rw [cauchyPowerSeries_apply]
  calc
    _ ≤ (1 / 2 : ℝ) * (2 ^ ell * (2 * D)) := by
      apply circleIntegral.norm_two_pi_i_inv_smul_integral_le_of_norm_le_const (by norm_num)
      intro z hz
      have hzR : ‖z‖ = (1 / 2 : ℝ) := by
        simpa only [Metric.mem_sphere, dist_zero_right] using hz
      simp only [sub_zero, norm_smul, norm_pow, norm_div, norm_one, norm_inv, hzR]
      norm_num only [one_div, inv_div, div_one]
      exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left (hD z hz) (by norm_num))
        (by positivity)
    _ = _ := by ring

theorem norm_shifted_log_div_le_half {center t : ℂ} {R : ℝ} (hR : 0 < R)
    (hc : ‖center‖ + 3 / 4 ≤ R / 2) (ht : ‖t‖ ≤ 1 / 2) :
    ‖(center + Complex.log (1 + t)) / (R : ℂ)‖ ≤ 1 / 2 := by
  rw [norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hR]
  apply (div_le_iff₀ hR).mpr
  have hlog := Complex.norm_log_one_add_half_le_self ht
  have htri := norm_add_le center (Complex.log (1 + t))
  nlinarith

theorem norm_rowTest_shifted_power_le {center : ℂ} {R : ℝ} (hR : 0 < R)
    (hc : ‖center‖ + 3 / 4 ≤ R / 2) (ell d : ℕ) :
    ‖rowTest ell (fun t => ((center + Complex.log (1 + t)) / (R : ℂ)) ^ d)‖ ≤
      (2 : ℝ) ^ ell * (1 / 2 : ℝ) ^ d := by
  apply norm_rowTest_le
  intro t ht
  rw [norm_pow]
  apply pow_le_pow_left₀ (norm_nonneg _) (norm_shifted_log_div_le_half hR hc _)
  simpa only [Metric.mem_sphere, dist_zero_right] using ht.le

theorem norm_exponentialMonomial_le_exp_budget (b h : ℂ) (d A : ℕ)
    {z : ℂ} {R H w0 wstar : ℝ} (hR : 1 ≤ R) (hH : 0 ≤ H)
    (hw0 : 0 < w0) (hws : 0 < wstar) (hz : ‖z‖ ≤ R)
    (hb : ‖b‖ ≤ (2 : ℝ) ^ A) (hh : ‖h‖ ≤ H / w0)
    (hd : d ≤ A) (hA : (A : ℝ) ≤ H / wstar) :
    ‖exponentialMonomial b h d z‖ ≤
      Real.exp (H * (R / w0 + Real.log (2 * R) / wstar)) := by
  have hR0 : 0 ≤ R := le_trans zero_le_one hR
  have h2R : 0 < 2 * R := by positivity
  have hlog : 0 ≤ Real.log (2 * R) := Real.log_nonneg (by linarith)
  calc
    _ ≤ ‖b‖ * Real.exp (‖h‖ * R) * R ^ d := norm_exponentialMonomial_le b h d hR0 hz
    _ ≤ (2 : ℝ) ^ A * Real.exp ((H / w0) * R) * R ^ A := by
      apply mul_le_mul
      · exact mul_le_mul hb (Real.exp_le_exp.mpr
          (mul_le_mul hh le_rfl hR0 (div_nonneg hH hw0.le)))
          (Real.exp_pos _).le (by positivity)
      · exact pow_le_pow_right₀ hR hd
      · positivity
      · positivity
    _ = Real.exp ((H / w0) * R + (A : ℝ) * Real.log (2 * R)) := by
      rw [Real.exp_add, Real.exp_nat_mul, Real.exp_log h2R, mul_pow]
      ring
    _ ≤ _ := by
      apply Real.exp_le_exp.mpr
      have ha := mul_le_mul hA (le_refl _) hlog (div_nonneg hH hws.le)
      calc
        _ ≤ (H / w0) * R + (H / wstar) * Real.log (2 * R) := add_le_add le_rfl ha
        _ = _ := by ring

end PiExponent.AnalyticCollision

end OAI
end Source0852

-- Source: OAI/NumberTheory/PiExponent/Approximation/RowTranslation.lean
section Source0853
-- Modified in this edition: unused plain lemmas removed; see reduction.json.
/-
Modification notice for the LogTwo project.
Derived from openai/math (Apache-2.0), revision adc7f1241b42e322a6451854ab7e4b4c146bf78a.
Original source: lean/OAI/NumberTheory/PiExponent/Approximation/RowTranslation.lean
Changes: Convert module/import declarations to the Lean 4.34 public module format.
See ../THIRD_PARTY_NOTICES.txt for provenance and the recorded changes.
-/

namespace OAI

namespace PiExponent.RowTranslation

open scoped BigOperators
open MvPolynomial

section PolynomialShift
variable {σ R : Type*} [CommSemiring R]

noncomputable def shift (c : σ → R) : MvPolynomial σ R →+* MvPolynomial σ R :=
  eval₂Hom C (fun i => X i + C (c i))

@[simp] theorem shift_C (c : σ → R) (r : R) : shift c (C r) = C r := by
  simp [shift]

@[simp] theorem shift_X (c : σ → R) (i : σ) : shift c (X i) = X i + C (c i) := by
  simp [shift]

@[simp] theorem shift_zero (p : MvPolynomial σ R) : shift (fun _ => 0) p = p := by
  have h : shift (fun _ : σ => (0 : R)) = RingHom.id _ := by
    ext r i <;> simp
  exact DFunLike.congr_fun h p

noncomputable def shiftCoefficient (c : σ → R) (β a : σ →₀ ℕ) : R :=
  (shift c (monomial a 1)).coeff β

theorem coeff_shift (c : σ → R) (p : MvPolynomial σ R) (β : σ →₀ ℕ) :
    (shift c p).coeff β =
      ∑ a ∈ p.support, p.coeff a * shiftCoefficient c β a := by
  classical
  conv_lhs => rw [p.as_sum]
  simp only [map_sum, coeff_sum]
  apply Finset.sum_congr rfl
  intro a ha
  rw [show monomial a (p.coeff a) = C (p.coeff a) * monomial a 1 by simp [C_mul_monomial]]
  simp [shiftCoefficient, coeff_C_mul]

theorem coeff_shift_over (c : σ → R) (p : MvPolynomial σ R) (β : σ →₀ ℕ)
    (S : Finset (σ →₀ ℕ)) (hp : p.support ⊆ S) :
    (shift c p).coeff β = ∑ a ∈ S, p.coeff a * shiftCoefficient c β a := by
  classical
  rw [coeff_shift]
  apply Finset.sum_subset hp
  intro a ha hnot
  simp [MvPolynomial.notMem_support_iff.mp hnot]

end PolynomialShift

section FiniteExpansion
variable {σ R : Type*} [Fintype σ] [DecidableEq σ] [CommSemiring R]

noncomputable def multiIndex (a : σ → ℕ) : σ →₀ ℕ := Finsupp.equivFunOnFinite.symm a

omit [DecidableEq σ] in
@[simp] theorem multiIndex_apply (a : σ → ℕ) (i : σ) : multiIndex a i = a i := by
  simp [multiIndex]

omit [Fintype σ] [DecidableEq σ] in
theorem shifted_X_pow (c : σ → R) (i : σ) (n : ℕ) :
    (X i + C (c i)) ^ n =
      ∑ b : Fin (n + 1), C ((n.choose b : R) * c i ^ (n - b)) * X i ^ (b : ℕ) := by
  rw [add_pow, ← Fin.sum_univ_eq_sum_range]
  apply Finset.sum_congr rfl
  intro b hb
  simp only [map_mul, map_pow, map_natCast]
  ring

theorem shifted_product_expansion (c : σ → R) (a : σ → ℕ) :
    (∏ i, (X i + C (c i)) ^ a i) =
      ∑ b : (∀ i, Fin (a i + 1)),
        C (∏ i, ((a i).choose (b i) : R) * c i ^ (a i - b i)) *
          monomial (multiIndex (fun i => (b i : ℕ))) 1 := by
  simp_rw [shifted_X_pow]
  rw [Fintype.prod_sum]
  apply Finset.sum_congr rfl
  intro b hb
  rw [Finset.prod_mul_distrib, ← map_prod, prod_X_pow]
  have hidx : Finsupp.indicator Finset.univ (fun i _ => (b i : ℕ)) =
      multiIndex (fun i => (b i : ℕ)) := by
    ext i
    simp [Finsupp.indicator]
  rw [hidx]

omit [DecidableEq σ] in
theorem shift_monomial_one (c : σ → R) (a : σ →₀ ℕ) :
    shift c (monomial a 1) = ∏ i, (X i + C (c i)) ^ a i := by
  simp only [shift, eval₂Hom_monomial, map_one, one_mul]
  exact a.prod_fintype _ (fun i => pow_zero _)

theorem shiftCoefficient_eq (c : σ → R) (β a : σ →₀ ℕ) :
    shiftCoefficient c β a = ∏ i, ((a i).choose (β i) : R) * c i ^ (a i - β i) := by
  classical
  rw [shiftCoefficient, shift_monomial_one, shifted_product_expansion, coeff_sum]
  simp only [coeff_C_mul, coeff_monomial]
  by_cases h : ∀ i, β i ≤ a i
  · let b₀ : ∀ i, Fin (a i + 1) := fun i => ⟨β i, Nat.lt_succ_of_le (h i)⟩
    have hidx : multiIndex (fun i => (b₀ i : ℕ)) = β := by ext i; simp [b₀]
    rw [Finset.sum_eq_single b₀]
    · simp [hidx, b₀]
    · intro b hb hne
      have hidx' : multiIndex (fun i => (b i : ℕ)) ≠ β := by
        intro he
        apply hne
        funext i
        apply Fin.ext
        have hi := congrArg (fun d : σ →₀ ℕ => d i) he
        simpa [b₀] using hi
      simp [hidx']
    · simp
  · push Not at h
    obtain ⟨i, hi⟩ := h
    have hright : (∏ j, ((a j).choose (β j) : R) * c j ^ (a j - β j)) = 0 := by
      apply Finset.prod_eq_zero (Finset.mem_univ i)
      simp [Nat.choose_eq_zero_of_lt hi]
    rw [hright]
    apply Finset.sum_eq_zero
    intro b hb
    have hidx : multiIndex (fun j => (b j : ℕ)) ≠ β := by
      intro he
      have hi' := congrArg (fun d : σ →₀ ℕ => d i) he
      have hbi : (b i : ℕ) = β i := by simpa using hi'
      have hlt := (b i).isLt
      omega
    simp [hidx]

theorem product_add_expansion (ε τ : σ → R) (n : σ → ℕ) :
    (∏ i, (ε i + τ i) ^ n i) =
      ∑ d : (∀ i, Fin (n i + 1)),
        (∏ i, (n i).choose (d i) : ℕ) *
          (∏ i, ε i ^ (n i - d i)) * ∏ i, τ i ^ (d i : ℕ) := by
  have h (i : σ) : (ε i + τ i) ^ n i =
      ∑ d : Fin (n i + 1), ((n i).choose d : R) * ε i ^ (n i - d) * τ i ^ (d : ℕ) := by
    rw [add_comm, add_pow, ← Fin.sum_univ_eq_sum_range]
    apply Finset.sum_congr rfl
    intro d hd
    ring
  simp_rw [h]
  rw [Fintype.prod_sum]
  apply Finset.sum_congr rfl
  intro d hd
  simp only [Finset.prod_mul_distrib, Nat.cast_prod]

end FiniteExpansion

section FormalSeriesRow
variable {σ R : Type*} [Fintype σ] [DecidableEq σ] [CommRing R]

omit [Fintype σ] [DecidableEq σ] in
theorem row_coefficient_identity (c : σ → PowerSeries R)
    (p : MvPolynomial σ (PowerSeries R)) (β : σ →₀ ℕ)
    (S : Finset (σ →₀ ℕ)) (hp : p.support ⊆ S) (s : ℕ) :
    PowerSeries.coeff s ((shift c p).coeff β) =
      ∑ a ∈ S, ∑ kl ∈ Finset.HasAntidiagonal.antidiagonal s,
        PowerSeries.coeff kl.1 (shiftCoefficient c β a) *
          PowerSeries.coeff kl.2 (p.coeff a) := by
  rw [coeff_shift_over c p β S hp]
  simp only [map_sum]
  apply Finset.sum_congr rfl
  intro a ha
  rw [mul_comm, PowerSeries.coeff_mul]

theorem coefficient_error_tail (ε : σ → R) (τ : σ → PowerSeries R)
    (n : σ → ℕ) (k : ℕ) :
    PowerSeries.coeff k (∏ i, (PowerSeries.C (ε i) + τ i) ^ n i) =
      ∑ d : (∀ i, Fin (n i + 1)),
        ((∏ i, (n i).choose (d i) : ℕ) : R) *
          (∏ i, ε i ^ (n i - d i)) *
            PowerSeries.coeff k (∏ i, τ i ^ (d i : ℕ)) := by
  rw [product_add_expansion]
  simp only [map_sum]
  apply Finset.sum_congr rfl
  intro d hd
  simp only [← map_pow, ← map_prod]
  rw [show ((∏ i, (n i).choose (d i) : ℕ) : PowerSeries R) =
      PowerSeries.C (((∏ i, (n i).choose (d i) : ℕ) : R)) by simp]
  rw [← map_mul, PowerSeries.coeff_C_mul]

noncomputable def rowScalar (ε : σ → R) (τ : σ → PowerSeries R)
    (β a : σ →₀ ℕ) (d : ∀ i, Fin (a i - β i + 1)) (k : ℕ) : R :=
  ((∏ i, (a i).choose (β i) * (a i - β i).choose (d i) : ℕ) : R) *
    (∏ i, ε i ^ (a i - β i - d i)) *
      PowerSeries.coeff k (∏ i, τ i ^ (d i : ℕ))

omit [DecidableEq σ] in
theorem rowScalar_ne_zero_le (ε : σ → R) (τ : σ → PowerSeries R)
    (β a : σ →₀ ℕ) (d : ∀ i, Fin (a i - β i + 1)) (k : ℕ)
    (h : rowScalar ε τ β a d k ≠ 0) : β ≤ a := by
  intro i
  by_contra hn
  have hi : a i < β i := by omega
  have hp : (∏ j, (a j).choose (β j) * (a j - β j).choose (d j) : ℕ) = 0 := by
    apply Finset.prod_eq_zero (Finset.mem_univ i)
    simp [Nat.choose_eq_zero_of_lt hi]
  exact h (by simp [rowScalar, hp])

theorem coeff_shiftCoefficient_error_tail (ε : σ → R) (τ : σ → PowerSeries R)
    (β a : σ →₀ ℕ) (k : ℕ) :
    PowerSeries.coeff k (shiftCoefficient (fun i => PowerSeries.C (ε i) + τ i) β a) =
      ∑ d : (∀ i, Fin (a i - β i + 1)), rowScalar ε τ β a d k := by
  rw [shiftCoefficient_eq, Finset.prod_mul_distrib]
  have hcast : (∏ i, ((a i).choose (β i) : PowerSeries R)) =
      PowerSeries.C ((∏ i, (a i).choose (β i) : ℕ) : R) := by simp
  rw [hcast, PowerSeries.coeff_C_mul, coefficient_error_tail, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro d hd
  simp only [rowScalar, Finset.prod_mul_distrib, Nat.cast_mul]
  ring

theorem exact_row_identity (ε : σ → R) (τ : σ → PowerSeries R)
    (p : MvPolynomial σ (PowerSeries R)) (β : σ →₀ ℕ)
    (S : Finset (σ →₀ ℕ)) (hp : p.support ⊆ S) (s : ℕ) :
    PowerSeries.coeff s ((shift (fun i => PowerSeries.C (ε i) + τ i) p).coeff β) =
      ∑ a ∈ S, ∑ d : (∀ i, Fin (a i - β i + 1)),
        ∑ kl ∈ Finset.HasAntidiagonal.antidiagonal s,
          rowScalar ε τ β a d kl.1 * PowerSeries.coeff kl.2 (p.coeff a) := by
  rw [row_coefficient_identity _ p β S hp s]
  apply Finset.sum_congr rfl
  intro a ha
  simp only [coeff_shiftCoefficient_error_tail, Finset.sum_mul]
  rw [Finset.sum_comm]

end FormalSeriesRow

section FiniteExpansion
variable {σ : Type*} [Fintype σ] [DecidableEq σ]

theorem choose_product_le_four_pow (a β d : ℕ) :
    a.choose β * (a - β).choose d ≤ 4 ^ a := by
  calc
    a.choose β * (a - β).choose d ≤ 2 ^ a * 2 ^ (a - β) :=
      Nat.mul_le_mul (Nat.choose_le_two_pow _ _) (Nat.choose_le_two_pow _ _)
    _ ≤ 2 ^ a * 2 ^ a := Nat.mul_le_mul_left _ (Nat.pow_le_pow_right (by decide) (Nat.sub_le _ _))
    _ = 4 ^ a := by rw [← mul_pow]; norm_num

omit [DecidableEq σ] in
theorem multi_choose_product_le_four_pow (a β d : σ → ℕ) :
    (∏ i, (a i).choose (β i) * (a i - β i).choose (d i)) ≤
      4 ^ (∑ i, a i) := by
  calc
    _ ≤ ∏ i, 4 ^ a i := Finset.prod_le_prod (fun i hi => choose_product_le_four_pow _ _ _)
    _ = _ := Finset.prod_pow_eq_pow_sum _ _ _

theorem card_bounded_indices_le (a : σ → ℕ) (H : ℕ) (ha : ∀ i, a i ≤ H) :
    Fintype.card (∀ i, Fin (a i + 1)) ≤ (H + 1) ^ Fintype.card σ := by
  rw [Fintype.card_pi]
  simp only [Fintype.card_fin]
  calc
    _ ≤ ∏ _i : σ, (H + 1) := Finset.prod_le_prod (fun i hi => Nat.add_le_add_right (ha i) 1)
    _ = _ := by simp

abbrev RowChoices (S : Finset (σ →₀ ℕ)) (β : σ →₀ ℕ) (s : ℕ) :=
  Σ a : S, (∀ i, Fin (a.1 i - β i + 1)) × Fin (s + 1)

theorem card_rowChoices_le (S : Finset (σ →₀ ℕ)) (β : σ →₀ ℕ) (s H : ℕ)
    (ha : ∀ a ∈ S, ∀ i, a i ≤ H) :
    Fintype.card (RowChoices S β s) ≤ S.card * (H + 1) ^ Fintype.card σ * (s + 1) := by
  classical
  rw [Fintype.card_sigma]
  simp only [Fintype.card_prod, Fintype.card_fin]
  calc
    _ ≤ ∑ _a : S, (H + 1) ^ Fintype.card σ * (s + 1) := by
      apply Finset.sum_le_sum
      intro a ha'
      apply Nat.mul_le_mul_right
      exact card_bounded_indices_le _ H (fun i => (Nat.sub_le _ _).trans (ha a.1 a.2 i))
    _ = _ := by simp [Nat.mul_assoc]

theorem card_rowChoices_box_le (S : Finset (σ →₀ ℕ)) (β : σ →₀ ℕ) (s H : ℕ)
    (ha : ∀ a ∈ S, ∀ i, a i ≤ H)
    (hS : S.card ≤ (H + 1) ^ Fintype.card σ) :
    Fintype.card (RowChoices S β s) ≤ (H + 1) ^ (2 * Fintype.card σ) * (s + 1) := by
  calc
    _ ≤ S.card * (H + 1) ^ Fintype.card σ * (s + 1) := card_rowChoices_le S β s H ha
    _ ≤ (H + 1) ^ Fintype.card σ * (H + 1) ^ Fintype.card σ * (s + 1) :=
      Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _ hS)
    _ = _ := by rw [← pow_add]; congr 2; omega

omit [DecidableEq σ] in
theorem norm_rowScalar_le (ε : σ → ℂ) (τ : σ → PowerSeries ℂ)
    (β a : σ →₀ ℕ) (d : ∀ i, Fin (a i - β i + 1)) (k : ℕ) (B : ℝ)
    (hτ : ‖PowerSeries.coeff k (∏ i, τ i ^ (d i : ℕ))‖ ≤ B) :
    ‖rowScalar ε τ β a d k‖ ≤
      (4 : ℝ) ^ (∑ i, a i) * (∏ i, ‖ε i‖ ^ (a i - β i - d i)) * B := by
  have hbin : ((∏ i, (a i).choose (β i) * (a i - β i).choose (d i) : ℕ) : ℝ) ≤
      (4 : ℝ) ^ (∑ i, a i) := by
    exact_mod_cast multi_choose_product_le_four_pow (fun i => a i) (fun i => β i) (fun i => (d i : ℕ))
  simp only [rowScalar, norm_mul, norm_prod, norm_pow, Complex.norm_natCast]
  exact mul_le_mul (mul_le_mul_of_nonneg_right hbin (by positivity)) hτ
    (norm_nonneg _) (by positivity)

end FiniteExpansion

variable {R : Type*} [CommRing R]

noncomputable def tail (T : ℕ) (f : PowerSeries R) : PowerSeries R :=
  (PowerSeries.trunc T f : PowerSeries R) - f

@[simp] theorem coeff_tail_of_lt (T k : ℕ) (f : PowerSeries R) (hk : k < T) :
    PowerSeries.coeff k (tail T f) = 0 := by
  simp [tail, PowerSeries.coeff_trunc, hk]

theorem order_tail (T : ℕ) (f : PowerSeries R) :
    (T : ℕ∞) ≤ (tail T f).order := by
  apply PowerSeries.nat_le_order
  exact fun k hk => coeff_tail_of_lt T k f hk

theorem order_tail_prod {ι : Type*} (s : Finset ι) (T d : ι → ℕ)
    (f : ι → PowerSeries R) :
    ((∑ i ∈ s, d i * T i : ℕ) : ℕ∞) ≤
      (∏ i ∈ s, tail (T i) (f i) ^ d i).order := by
  calc
    ((∑ i ∈ s, d i * T i : ℕ) : ℕ∞) = ∑ i ∈ s, d i • (T i : ℕ∞) := by
      simp [nsmul_eq_mul]
    _ ≤ ∑ i ∈ s, d i • (tail (T i) (f i)).order := by
      exact Finset.sum_le_sum (fun i hi => nsmul_le_nsmul_right (order_tail _ _) _)
    _ ≤ ∑ i ∈ s, (tail (T i) (f i) ^ d i).order := by
      exact Finset.sum_le_sum (fun i hi => PowerSeries.le_order_pow _ _)
    _ ≤ (∏ i ∈ s, tail (T i) (f i) ^ d i).order := PowerSeries.le_order_prod _ _

theorem tail_budget_nat {ι : Type*} (s : Finset ι) (T d : ι → ℕ)
    (f : ι → PowerSeries R) (k : ℕ)
    (hk : PowerSeries.coeff k (∏ i ∈ s, tail (T i) (f i) ^ d i) ≠ 0) :
    ∑ i ∈ s, d i * T i ≤ k := by
  exact_mod_cast (order_tail_prod s T d f).trans (PowerSeries.order_le k hk)

theorem tail_weight_budget {ι : Type*} (s : Finset ι) (T d : ι → ℕ)
    (f : ι → PowerSeries R) (k : ℕ) (w : ι → ℝ) (v F : ℝ)
    (hv : 0 ≤ v) (hF : 0 < F)
    (hT : ∀ i ∈ s, F * w i ≤ v * T i)
    (hk : PowerSeries.coeff k (∏ i ∈ s, tail (T i) (f i) ^ d i) ≠ 0) :
    ∑ i ∈ s, (d i : ℝ) * w i ≤ v * k / F := by
  apply (le_div_iff₀ hF).2
  calc
    (∑ i ∈ s, (d i : ℝ) * w i) * F =
        ∑ i ∈ s, (d i : ℝ) * (F * w i) := by rw [Finset.sum_mul]; congr 1; ext i; ring
    _ ≤ ∑ i ∈ s, (d i : ℝ) * (v * T i) :=
      Finset.sum_le_sum (fun i hi => mul_le_mul_of_nonneg_left (hT i hi) (Nat.cast_nonneg _))
    _ = v * (∑ i ∈ s, (d i * T i : ℕ) : ℕ) := by
      simp only [Nat.cast_sum, Nat.cast_mul, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i hi
      ring
    _ ≤ v * k := mul_le_mul_of_nonneg_left (by exact_mod_cast tail_budget_nat s T d f k hk) hv

end PiExponent.RowTranslation

end OAI
end Source0853

-- Source: OAI/NumberTheory/PiExponent/Analysis/LogTailAnalytic.lean
section Source0854
-- Modified in this edition: unused plain lemmas removed; see reduction.json.
/-
Modification notice for the LogTwo project.
Derived from openai/math (Apache-2.0), revision adc7f1241b42e322a6451854ab7e4b4c146bf78a.
Original source: lean/OAI/NumberTheory/PiExponent/Analysis/LogTailAnalytic.lean
Changes: Convert module/import declarations to the Lean 4.34 public module format.
See ../THIRD_PARTY_NOTICES.txt for provenance and the recorded changes.
-/

namespace OAI

open scoped BigOperators

namespace PiExponent.LogTailAnalytic

noncomputable def logTail (T : ℕ) (z : ℂ) : ℂ :=
  Complex.logTaylor T z - Complex.log (1 + z)

theorem eval_trunc_log (T : ℕ) (z : ℂ) :
    (PowerSeries.trunc T (PowerSeries.log ℂ)).eval z = Complex.logTaylor T z := by
  change (PowerSeries.trunc T (PowerSeries.log ℂ)).eval₂ (RingHom.id ℂ) z = _
  rw [PowerSeries.eval₂_trunc_eq_sum_range]
  unfold Complex.logTaylor
  apply Finset.sum_congr rfl
  intro n hn
  simp only [RingHom.id_apply, PowerSeries.coeff_log]
  by_cases h : n = 0
  · simp [h]
  · simp [h, map_div₀, map_pow]
    ring

theorem analyticAt_logTail (T : ℕ) {z : ℂ} (hz : ‖z‖ < 1) :
    AnalyticAt ℂ (logTail T) z := by
  unfold logTail Complex.logTaylor
  apply AnalyticAt.sub
  · apply Finset.analyticAt_fun_sum
    intro n hn
    fun_prop
  · exact (analyticAt_const.add analyticAt_id).clog (Complex.mem_slitPlane_of_norm_lt_one hz)

 theorem norm_logTail_le (T : ℕ) (hT : 1 ≤ T) {z : ℂ} (hz : ‖z‖ < 1) :
    ‖logTail T z‖ ≤ ‖z‖ ^ T * (1 - ‖z‖)⁻¹ / T := by
  obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : T ≠ 0)
  unfold logTail
  rw [norm_sub_rev]
  simpa only [Nat.succ_eq_add_one, Nat.cast_add, Nat.cast_one] using
    Complex.norm_log_sub_logTaylor_le n hz

theorem norm_logTail_le_one (T : ℕ) (hT : 1 ≤ T) {z : ℂ} (hz : ‖z‖ ≤ 1 / 2) :
    ‖logTail T z‖ ≤ 1 := by
  have hz1 : ‖z‖ < 1 := by linarith
  have hpow : ‖z‖ ^ T ≤ 1 / 2 := by
    obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : T ≠ 0)
    rw [pow_succ]
    have hh : ‖z‖ ^ n ≤ 1 := pow_le_one₀ (norm_nonneg z) hz1.le
    nlinarith [norm_nonneg z]
  have hinv : (1 - ‖z‖)⁻¹ ≤ 2 := by
    rw [inv_le_comm₀ (by linarith : 0 < 1 - ‖z‖) (by norm_num : (0 : ℝ) < 2)]
    linarith
  have hTreal : (1 : ℝ) ≤ T := by exact_mod_cast hT
  calc
    ‖logTail T z‖ ≤ ‖z‖ ^ T * (1 - ‖z‖)⁻¹ / T := norm_logTail_le T hT hz1
    _ ≤ (1 / 2 : ℝ) * 2 / T := by gcongr
    _ ≤ 1 := by rw [div_le_iff₀ (by positivity : (0 : ℝ) < T)]; nlinarith

theorem norm_prod_logTail_le_one {ι : Type*} (s : Finset ι) (T d : ι → ℕ)
    (hT : ∀ i ∈ s, 1 ≤ T i) {z : ℂ} (hz : ‖z‖ ≤ 1 / 2) :
    ‖∏ i ∈ s, logTail (T i) z ^ d i‖ ≤ 1 := by
  rw [norm_prod]
  apply Finset.prod_le_one₀
  · intro i hi
    positivity
  · intro i hi
    rw [norm_pow]
    exact pow_le_one₀ (norm_nonneg _) (norm_logTail_le_one (T i) (hT i hi) hz)

theorem analyticAt_prod_logTail {ι : Type*} (s : Finset ι) (T d : ι → ℕ)
    {z : ℂ} (hz : ‖z‖ < 1) :
    AnalyticAt ℂ (fun t => ∏ i ∈ s, logTail (T i) t ^ d i) z := by
  apply Finset.analyticAt_fun_prod
  intro i hi
  exact (analyticAt_logTail (T i) hz).pow (d i)

theorem norm_rowTest_prod_logTail_le {ι : Type*} (s : Finset ι) (T d : ι → ℕ)
    (hT : ∀ i ∈ s, 1 ≤ T i) (k : ℕ) :
    ‖AnalyticCollision.rowTest k (fun z => ∏ i ∈ s, logTail (T i) z ^ d i)‖ ≤
      (2 : ℝ) ^ k := by
  have h := AnalyticCollision.norm_rowTest_le
    (f := fun z => ∏ i ∈ s, logTail (T i) z ^ d i) (D := 1) ?_ k
  · simpa only [mul_one] using h
  intro z hz
  apply norm_prod_logTail_le_one s T d hT
  exact (by simpa only [Metric.mem_sphere, dist_zero_right] using hz : ‖z‖ = 1 / 2).le

theorem hasSum_formal_log {z : ℂ} (hz : ‖z‖ < 1) :
    HasSum (fun n => PowerSeries.coeff n (PowerSeries.log ℂ) * z ^ n)
      (Complex.log (1 + z)) := by
  convert Complex.hasSum_taylorSeries_log hz using 1
  funext n
  by_cases hn : n = 0
  · simp [hn]
  · simp [PowerSeries.coeff_log, hn, map_div₀, map_pow]
    ring

theorem hasSum_trunc_log (T : ℕ) (z : ℂ) :
    HasSum (fun n => PowerSeries.coeff n
      (PowerSeries.trunc T (PowerSeries.log ℂ) : PowerSeries ℂ) * z ^ n)
      (Complex.logTaylor T z) := by
  have h := hasSum_sum_of_ne_finset_zero (L := SummationFilter.unconditional ℕ)
    (s := Finset.range T)
    (f := fun n => PowerSeries.coeff n
      (PowerSeries.trunc T (PowerSeries.log ℂ) : PowerSeries ℂ) * z ^ n) ?_
  · convert h using 1
    rw [← eval_trunc_log]
    change (PowerSeries.trunc T (PowerSeries.log ℂ)).eval₂ (RingHom.id ℂ) z = _
    rw [PowerSeries.eval₂_trunc_eq_sum_range]
    apply Finset.sum_congr rfl
    intro n hn
    simp [PowerSeries.coeff_trunc, Finset.mem_range.mp hn]
  · intro n hn
    have hn' : ¬ n < T := by simpa only [Finset.mem_range] using hn
    simp [PowerSeries.coeff_trunc, hn']

theorem hasSum_formal_logTail (T : ℕ) {z : ℂ} (hz : ‖z‖ < 1) :
    HasSum (fun n => PowerSeries.coeff n
      (RowTranslation.tail T (PowerSeries.log ℂ)) * z ^ n) (logTail T z) := by
  convert (hasSum_trunc_log T z).sub (hasSum_formal_log hz) using 1
  · funext n
    simp only [RowTranslation.tail, map_sub, sub_mul]
  · rfl

theorem hasSum_coeff_mul {f g : PowerSeries ℂ} {x y z : ℂ}
    (hf : HasSum (fun n => PowerSeries.coeff n f * z ^ n) x)
    (hg : HasSum (fun n => PowerSeries.coeff n g * z ^ n) y) :
    HasSum (fun n => PowerSeries.coeff n (f * g) * z ^ n) (x * y) := by
  have hfn := hf.summable.norm
  have hgn := hg.summable.norm
  have hs := (summable_norm_sum_mul_antidiagonal_of_summable_norm hfn hgn).of_norm.hasSum
  have heq := tsum_mul_tsum_eq_tsum_sum_antidiagonal_of_summable_norm hfn hgn
  rw [hf.tsum_eq, hg.tsum_eq] at heq
  rw [← heq] at hs
  convert hs using 1
  funext n
  rw [PowerSeries.coeff_mul, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro a ha
  have he : a.1 + a.2 = n := Finset.HasAntidiagonal.mem_antidiagonal.mp ha
  rw [← he, pow_add]
  ring

theorem hasSum_coeff_one (z : ℂ) :
    HasSum (fun n => PowerSeries.coeff n (1 : PowerSeries ℂ) * z ^ n) 1 := by
  convert hasSum_ite_eq 0 (1 : ℂ) using 1
  funext n
  by_cases hn : n = 0 <;> simp [PowerSeries.coeff_one, hn]

 theorem hasSum_coeff_pow {f : PowerSeries ℂ} {x z : ℂ}
    (hf : HasSum (fun n => PowerSeries.coeff n f * z ^ n) x) (d : ℕ) :
    HasSum (fun n => PowerSeries.coeff n (f ^ d) * z ^ n) (x ^ d) := by
  induction d with
  | zero => simpa only [pow_zero] using hasSum_coeff_one z
  | succ d hd => simpa only [pow_succ] using hasSum_coeff_mul hd hf

theorem hasSum_formal_prod_logTail {ι : Type*} (s : Finset ι) (T d : ι → ℕ)
    {z : ℂ} (hz : ‖z‖ < 1) :
    HasSum (fun n => PowerSeries.coeff n
      (∏ i ∈ s, RowTranslation.tail (T i) (PowerSeries.log ℂ) ^ d i) * z ^ n)
      (∏ i ∈ s, logTail (T i) z ^ d i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa only [Finset.prod_empty] using hasSum_coeff_one z
  | @insert i s hi hs =>
    simpa only [Finset.prod_insert hi] using
      hasSum_coeff_mul (hasSum_coeff_pow (hasSum_formal_logTail (T i) hz) (d i)) hs

theorem hasFPowerSeriesAt_prod_logTail {ι : Type*} (s : Finset ι) (T d : ι → ℕ) :
    HasFPowerSeriesAt (fun z => ∏ i ∈ s, logTail (T i) z ^ d i)
      (FormalMultilinearSeries.ofScalars ℂ
        (fun n => PowerSeries.coeff n
          (∏ i ∈ s, RowTranslation.tail (T i) (PowerSeries.log ℂ) ^ d i))) 0 := by
  rw [hasFPowerSeriesAt_iff]
  filter_upwards [Metric.ball_mem_nhds (0 : ℂ) (by norm_num : (0 : ℝ) < 1)] with z hz
  have hn : ‖z‖ < 1 := by simpa only [Metric.mem_ball, dist_zero_right] using hz
  simpa only [FormalMultilinearSeries.coeff_ofScalars, zero_add, smul_eq_mul, mul_comm] using
    hasSum_formal_prod_logTail s T d hn

theorem rowTest_prod_logTail_eq_coeff {ι : Type*} (s : Finset ι) (T d : ι → ℕ) (k : ℕ) :
    AnalyticCollision.rowTest k (fun z => ∏ i ∈ s, logTail (T i) z ^ d i) =
      PowerSeries.coeff k (∏ i ∈ s, RowTranslation.tail (T i) (PowerSeries.log ℂ) ^ d i) := by
  have hd : DifferentiableOn ℂ (fun z => ∏ i ∈ s, logTail (T i) z ^ d i)
      (Metric.closedBall 0 (1 / 2)) := by
    intro z hz
    apply (analyticAt_prod_logTail s T d ?_).differentiableAt.differentiableWithinAt
    have hz' : ‖z‖ ≤ 1 / 2 := by simpa only [Metric.mem_closedBall, dist_zero_right] using hz
    linarith
  have hp := hd.hasFPowerSeriesOnBall (R := (1 / 2 : NNReal)) (by norm_num)
  have he := hp.hasFPowerSeriesAt.eq_formalMultilinearSeries
    (hasFPowerSeriesAt_prod_logTail s T d)
  have hh := congrArg (fun p : FormalMultilinearSeries ℂ ℂ ℂ => p k (fun _ => 1)) he
  simpa only [AnalyticCollision.rowTest, FormalMultilinearSeries.apply_eq_prod_smul_coeff,
    Finset.prod_const_one, one_smul, FormalMultilinearSeries.coeff_ofScalars,
    NNReal.coe_div, NNReal.coe_one, NNReal.coe_ofNat] using hh

theorem norm_coeff_prod_formal_logTail_le {ι : Type*} (s : Finset ι) (T d : ι → ℕ)
    (hT : ∀ i ∈ s, 1 ≤ T i) (k : ℕ) :
    ‖PowerSeries.coeff k (∏ i ∈ s, RowTranslation.tail (T i) (PowerSeries.log ℂ) ^ d i)‖ ≤
      (2 : ℝ) ^ k := by
  rw [← rowTest_prod_logTail_eq_coeff]
  exact norm_rowTest_prod_logTail_le s T d hT k

end PiExponent.LogTailAnalytic

end OAI
end Source0854

-- Source: OAI/NumberTheory/PiExponent/Approximation/MatrixTranslation.lean
section Source0855
-- Modified in this edition: unused plain lemmas removed; see reduction.json.
/-
Modification notice for the LogTwo project.
Derived from openai/math (Apache-2.0), revision adc7f1241b42e322a6451854ab7e4b4c146bf78a.
Original source: lean/OAI/NumberTheory/PiExponent/Approximation/MatrixTranslation.lean
Changes: Convert module/import declarations to the Lean 4.34 public module format.
See ../THIRD_PARTY_NOTICES.txt for provenance and the recorded changes.
-/

namespace OAI

namespace PiExponent.MatrixTranslation

open scoped BigOperators
open MvPolynomial
open RowTranslation

noncomputable def periodCoordinate (j : ℕ) (ω : ℂ) : PowerSeries ℂ :=
  PowerSeries.C ((j : ℂ) * ω) + PowerSeries.log ℂ

noncomputable def periodMonomial {m : ℕ} (j : ℕ) (ω : ℂ) (h : ℕ)
    (a : Fin m → ℕ) : MvPolynomial (Fin m) (PowerSeries ℂ) :=
  C ((1 + PowerSeries.X) ^ h) *
    ∏ i, (C (periodCoordinate j ω) + X i) ^ a i

theorem periodMonomial_as_shift {m : ℕ} (j : ℕ) (ω : ℂ) (h : ℕ)
    (a : Fin m → ℕ) :
    periodMonomial j ω h a = C ((1 + PowerSeries.X) ^ h) *
      shift (fun _ => periodCoordinate j ω) (monomial (InterpolationMatrix.exponentVector a) 1) := by
  rw [periodMonomial, shift_monomial_one]
  simp [add_comm]

theorem periodMonomial_coeff {m : ℕ} (j : ℕ) (ω : ℂ) (h : ℕ)
    (a : Fin m → ℕ) (A : Fin m →₀ ℕ) :
    (periodMonomial j ω h a).coeff A =
      ((∏ i, (a i).choose (A i) : ℕ) : PowerSeries ℂ) *
        (1 + PowerSeries.X) ^ h * periodCoordinate j ω ^ (∑ i : Fin m, (a i - A i)) := by
  rw [periodMonomial_as_shift, coeff_C_mul]
  change _ * shiftCoefficient _ _ _ = _
  rw [shiftCoefficient_eq, Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum]
  simp only [InterpolationMatrix.exponentVector_apply, Nat.cast_prod]
  ring

theorem periodMonomial_support_le {m : ℕ} (j : ℕ) (ω : ℂ) (h : ℕ)
    (a : Fin m → ℕ) {A : Fin m →₀ ℕ}
    (hA : A ∈ (periodMonomial j ω h a).support) : ∀ i, A i ≤ a i := by
  intro i
  by_contra hn
  have hi : a i < A i := by omega
  have hzero : (∏ k, (a k).choose (A k) : ℕ) = 0 := by
    apply Finset.prod_eq_zero (Finset.mem_univ i)
    exact Nat.choose_eq_zero_of_lt hi
  have hz : (periodMonomial j ω h a).coeff A = 0 := by
    rw [periodMonomial_coeff, hzero]
    simp
  exact (MvPolynomial.mem_support_iff.mp hA) hz

theorem periodMonomial_support_weight {m : ℕ} (j : ℕ) (ω : ℂ) (h : ℕ)
    (a : Fin m → ℕ) (w : Fin m → ℝ) (H : ℝ) (hw : ∀ i, 0 ≤ w i)
    (ha : ∑ i, w i * a i ≤ H) {A : Fin m →₀ ℕ}
    (hA : A ∈ (periodMonomial j ω h a).support) :
    ∑ i, w i * A i ≤ H := by
  apply le_trans _ ha
  apply Finset.sum_le_sum
  intro i hi
  apply mul_le_mul_of_nonneg_left _ (hw i)
  exact_mod_cast periodMonomial_support_le j ω h a hA i

noncomputable def transverseIndices {m : ℕ} (w : Fin m → ℝ) (H : ℝ) :
    Finset (Fin m →₀ ℕ) :=
  (PiExponent.realWeightedSimplex w H).map Finsupp.equivFunOnFinite.symm.toEmbedding

@[simp] theorem mem_transverseIndices {m : ℕ} (w : Fin m → ℝ) (H : ℝ)
    (hw : ∀ i, 0 < w i) (A : Fin m →₀ ℕ) :
    A ∈ transverseIndices w H ↔ ∑ i, w i * A i ≤ H := by
  classical
  simp only [transverseIndices, Finset.mem_map_equiv, PiExponent.mem_realWeightedSimplex hw]
  rfl

@[simp] theorem card_transverseIndices {m : ℕ} (w : Fin m → ℝ) (H : ℝ) :
    (transverseIndices w H).card = (PiExponent.realWeightedSimplex w H).card := by
  simp [transverseIndices]

theorem periodMonomial_support_subset {m : ℕ} (j : ℕ) (ω : ℂ) (h : ℕ)
    (a : Fin m → ℕ) (w : Fin m → ℝ) (H : ℝ) (hw : ∀ i, 0 < w i)
    (ha : ∑ i, w i * a i ≤ H) :
    (periodMonomial j ω h a).support ⊆ transverseIndices w H := by
  intro A hA
  apply (mem_transverseIndices w H hw A).2
  exact periodMonomial_support_weight j ω h a w H (fun i => (hw i).le) ha hA

theorem transverseIndices_coordinate_le {m : ℕ} (w : Fin m → ℝ) (H : ℝ)
    (hw : ∀ i, 1 ≤ w i) {A : Fin m →₀ ℕ} (hA : A ∈ transverseIndices w H) (i : Fin m) :
    A i ≤ ⌊H⌋₊ := by
  have hwpos : ∀ i, 0 < w i := fun i => lt_of_lt_of_le zero_lt_one (hw i)
  have ha := (mem_transverseIndices w H hwpos A).mp hA
  apply Nat.le_floor
  calc
    (A i : ℝ) ≤ w i * A i := by nlinarith [show (0 : ℝ) ≤ (A i : ℝ) by positivity, hw i]
    _ ≤ ∑ k, w k * A k := Finset.single_le_sum
      (fun k hk => mul_nonneg (hwpos k).le (Nat.cast_nonneg _)) (Finset.mem_univ i)
    _ ≤ H := ha

theorem transverseIndices_card_le {m : ℕ} (w : Fin m → ℝ) (H : ℝ)
    (hw : ∀ i, 1 ≤ w i) :
    (transverseIndices w H).card ≤ (⌊H⌋₊ + 1) ^ m := by
  classical
  let box : Finset (Fin m → ℕ) := Fintype.piFinset (fun _ => Finset.range (⌊H⌋₊ + 1))
  have hcard : (transverseIndices w H).card ≤ box.card := by
    apply Finset.card_le_card_of_injOn (fun A : Fin m →₀ ℕ => fun i => A i)
    · intro A hA
      apply Fintype.mem_piFinset.mpr
      intro i
      exact Finset.mem_range.mpr (Nat.lt_succ_of_le (transverseIndices_coordinate_le w H hw hA i))
    · intro A hA B hB he
      exact Finsupp.ext (fun i => congrFun he i)
  simpa [box, Fintype.card_piFinset] using hcard

theorem row_term_count {m : ℕ} (w : Fin m → ℝ) (H v : ℝ)
    (hw : ∀ i, 1 ≤ w i) (β : Fin m →₀ ℕ) (s : ℕ) (hs : (s : ℝ) ≤ H / v) :
    Fintype.card (RowChoices (transverseIndices w H) β s) ≤
      (⌊H⌋₊ + 1) ^ (2 * m) * (⌊H / v⌋₊ + 1) := by
  have h := card_rowChoices_box_le (transverseIndices w H) β s ⌊H⌋₊
    (fun A hA i => transverseIndices_coordinate_le w H hw hA i)
    (by simpa using transverseIndices_card_le w H hw)
  simp only [Fintype.card_fin] at h
  exact h.trans (Nat.mul_le_mul_left _ (Nat.add_le_add_right (Nat.le_floor hs) 1))

noncomputable def formalMonomialImage {m : ℕ} (r : Fin m → ℂ)
    (T : Fin m → ℕ) (j h : ℕ) (a : Fin m → ℕ) :
    MvPolynomial (Fin m) (PowerSeries ℂ) :=
  MvPolynomial.map Polynomial.coeToPowerSeries.ringHom
    (InterpolationMatrix.monomialImage r (fun i => InterpolationMatrix.truncatedLog (T i)) j h a)

theorem coordinate_translation (j : ℕ) (ω r : ℂ) (T : ℕ) :
    periodCoordinate j ω + (PowerSeries.C ((j : ℂ) * (r - ω)) +
      tail T (PowerSeries.log ℂ)) =
      PowerSeries.C ((j : ℂ) * r) + (InterpolationMatrix.truncatedLog T : PowerSeries ℂ) := by
  unfold periodCoordinate tail InterpolationMatrix.truncatedLog
  calc
    _ = PowerSeries.C ((j : ℂ) * ω) + PowerSeries.C ((j : ℂ) * (r - ω)) +
        (PowerSeries.trunc T (PowerSeries.log ℂ) : PowerSeries ℂ) := by ring
    _ = _ := by rw [← map_add]; congr 1; congr 1; ring

theorem periodMonomial_shift {m : ℕ} (r : Fin m → ℂ) (T : Fin m → ℕ)
    (j : ℕ) (ω : ℂ) (h : ℕ) (a : Fin m → ℕ) :
    shift (fun i => PowerSeries.C ((j : ℂ) * (r i - ω)) + tail (T i) (PowerSeries.log ℂ))
      (periodMonomial j ω h a) = formalMonomialImage r T j h a := by
  simp only [periodMonomial, formalMonomialImage, InterpolationMatrix.monomialImage,
    map_mul, map_prod, map_pow, map_add, shift_C, shift_X, MvPolynomial.map_C,
    MvPolynomial.map_X, Polynomial.coeToPowerSeries.ringHom_apply,
    Polynomial.coe_C, Polynomial.coe_one, Polynomial.coe_X]
  congr 1
  apply Finset.prod_congr rfl
  intro i hi
  congr 1
  calc
    _ = C (periodCoordinate j ω + (PowerSeries.C ((j : ℂ) * (r i - ω)) +
        tail (T i) (PowerSeries.log ℂ))) + X i := by simp only [map_add, map_mul]; ring
    _ = _ := by rw [coordinate_translation]; simp [map_add]

theorem formalMonomialImage_coeff {m : ℕ} (r : Fin m → ℂ) (T : Fin m → ℕ)
    (j s : ℕ) (b : Fin m → ℕ) (h : ℕ) (a : Fin m → ℕ) :
    PowerSeries.coeff s ((formalMonomialImage r T j h a).coeff
      (InterpolationMatrix.exponentVector b)) =
      InterpolationMatrix.entry r (fun i => InterpolationMatrix.truncatedLog (T i)) j s b h a := by
  simp [formalMonomialImage, MvPolynomial.coeff_map, InterpolationMatrix.entry]

theorem matrix_entry_translation {m : ℕ} (r : Fin m → ℂ) (T : Fin m → ℕ)
    (j s : ℕ) (ω : ℂ) (b : Fin m → ℕ) (h : ℕ) (a : Fin m → ℕ)
    (S : Finset (Fin m →₀ ℕ)) (hp : (periodMonomial j ω h a).support ⊆ S) :
    InterpolationMatrix.entry r (fun i => InterpolationMatrix.truncatedLog (T i)) j s b h a =
      ∑ A ∈ S, ∑ d : (∀ i, Fin (A i - (InterpolationMatrix.exponentVector b) i + 1)),
        ∑ kl ∈ Finset.HasAntidiagonal.antidiagonal s,
          rowScalar (fun i => (j : ℂ) * (r i - ω))
            (fun i => tail (T i) (PowerSeries.log ℂ))
            (InterpolationMatrix.exponentVector b) A d kl.1 *
            PowerSeries.coeff kl.2 ((periodMonomial j ω h a).coeff A) := by
  rw [← formalMonomialImage_coeff r T j s b h a, ← periodMonomial_shift r T j ω h a]
  exact exact_row_identity _ _ _ _ S hp s

theorem matrix_entry_translation_choices {m : ℕ} (r : Fin m → ℂ) (T : Fin m → ℕ)
    (j s : ℕ) (ω : ℂ) (b : Fin m → ℕ) (h : ℕ) (a : Fin m → ℕ)
    (S : Finset (Fin m →₀ ℕ)) (hp : (periodMonomial j ω h a).support ⊆ S) :
    InterpolationMatrix.entry r (fun i => InterpolationMatrix.truncatedLog (T i)) j s b h a =
      ∑ t : RowChoices S (InterpolationMatrix.exponentVector b) s,
        rowScalar (fun i => (j : ℂ) * (r i - ω))
          (fun i => tail (T i) (PowerSeries.log ℂ))
          (InterpolationMatrix.exponentVector b) t.1.1 t.2.1 t.2.2 *
          PowerSeries.coeff (s - t.2.2) ((periodMonomial j ω h a).coeff t.1.1) := by
  classical
  rw [matrix_entry_translation r T j s ω b h a S hp, Fintype.sum_sigma]
  simp only [Fintype.sum_prod_type]
  rw [← Finset.sum_coe_sort]
  apply Finset.sum_congr rfl
  intro A hA
  apply Finset.sum_congr rfl
  intro d hd
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk, ← Fin.sum_univ_eq_sum_range]

theorem det_dependent_row_sum {ι : Type*} [Fintype ι] [DecidableEq ι]
    {δ : ι → Type*} [∀ i, Fintype (δ i)]
    (B : ∀ i, δ i → ℂ) (C : ∀ i, δ i → ι → ℂ) :
    Matrix.det (fun i j => ∑ t, B i t * C i t j) =
      ∑ f : (∀ i, δ i), (∏ i, B i (f i)) * Matrix.det (fun i j => C i (f i) j) := by
  classical
  have hm := (Matrix.detRowAlternating : (ι → ℂ) [⋀^ι]→ₗ[ℂ] ℂ).toMultilinearMap.map_sum
    (fun i t => B i t • C i t)
  calc
    _ = Matrix.det (fun i => ∑ t, B i t • C i t) := by
      congr 1
      funext i j
      simp
    _ = ∑ f : (∀ i, δ i), Matrix.det (fun i => B i (f i) • C i (f i)) := hm
    _ = _ := by
      apply Finset.sum_congr rfl
      intro f hf
      exact Matrix.det_mul_column (fun i => B i (f i)) (fun i j => C i (f i) j)

end PiExponent.MatrixTranslation

end OAI
end Source0855

-- Source: OAI/NumberTheory/PiExponent/Analysis/PeriodAnalytic.lean
section Source0856
-- Modified in this edition: unused plain lemmas removed; see reduction.json.
/-
Modification notice for the LogTwo project.
Derived from openai/math (Apache-2.0), revision adc7f1241b42e322a6451854ab7e4b4c146bf78a.
Original source: lean/OAI/NumberTheory/PiExponent/Analysis/PeriodAnalytic.lean
Changes: Convert module/import declarations to the Lean 4.34 public module format.
See ../THIRD_PARTY_NOTICES.txt for provenance and the recorded changes.
-/

namespace OAI

open scoped BigOperators
open PiExponent.AnalyticCollision PiExponent.LogTailAnalytic

namespace PiExponent.PeriodAnalytic

noncomputable def periodSeries (b center : ℂ) (h d : ℕ) : PowerSeries ℂ :=
  PowerSeries.C b * (1 + PowerSeries.X) ^ h *
    (PowerSeries.C center + PowerSeries.log ℂ) ^ d

noncomputable def periodFunction (b center : ℂ) (h d : ℕ) (t : ℂ) : ℂ :=
  b * (1 + t) ^ h * (center + Complex.log (1 + t)) ^ d

theorem hasSum_coeff_C (b z : ℂ) :
    HasSum (fun n => PowerSeries.coeff n (PowerSeries.C b) * z ^ n) b := by
  convert hasSum_ite_eq 0 b using 1
  funext n
  by_cases hn : n = 0 <;> simp [PowerSeries.coeff_C, hn]

theorem hasSum_coeff_X (z : ℂ) :
    HasSum (fun n => PowerSeries.coeff n (PowerSeries.X : PowerSeries ℂ) * z ^ n) z := by
  convert hasSum_ite_eq 1 z using 1
  funext n
  by_cases hn : n = 1 <;> simp [PowerSeries.coeff_X, hn]

theorem hasSum_coeff_add {f g : PowerSeries ℂ} {x y z : ℂ}
    (hf : HasSum (fun n => PowerSeries.coeff n f * z ^ n) x)
    (hg : HasSum (fun n => PowerSeries.coeff n g * z ^ n) y) :
    HasSum (fun n => PowerSeries.coeff n (f + g) * z ^ n) (x + y) := by
  simpa only [map_add, add_mul] using hf.add hg

theorem hasSum_periodSeries (b center : ℂ) (h d : ℕ) {z : ℂ} (hz : ‖z‖ < 1) :
    HasSum (fun n => PowerSeries.coeff n (periodSeries b center h d) * z ^ n)
      (periodFunction b center h d z) := by
  exact hasSum_coeff_mul
    (hasSum_coeff_mul (hasSum_coeff_C b z)
      (hasSum_coeff_pow (hasSum_coeff_add (hasSum_coeff_one z) (hasSum_coeff_X z)) h))
    (hasSum_coeff_pow (hasSum_coeff_add (hasSum_coeff_C center z) (hasSum_formal_log hz)) d)

theorem analyticAt_periodFunction (b center : ℂ) (h d : ℕ) {z : ℂ} (hz : ‖z‖ < 1) :
    AnalyticAt ℂ (periodFunction b center h d) z := by
  unfold periodFunction
  apply AnalyticAt.mul
  · fun_prop
  · exact (analyticAt_const.add ((analyticAt_const.add analyticAt_id).clog
      (Complex.mem_slitPlane_of_norm_lt_one hz))).pow d

theorem hasFPowerSeriesAt_periodFunction (b center : ℂ) (h d : ℕ) :
    HasFPowerSeriesAt (periodFunction b center h d)
      (FormalMultilinearSeries.ofScalars ℂ (fun n => PowerSeries.coeff n
        (periodSeries b center h d))) 0 := by
  rw [hasFPowerSeriesAt_iff]
  filter_upwards [Metric.ball_mem_nhds (0 : ℂ) (by norm_num : (0 : ℝ) < 1)] with z hz
  have hn : ‖z‖ < 1 := by simpa only [Metric.mem_ball, dist_zero_right] using hz
  simpa only [FormalMultilinearSeries.coeff_ofScalars, zero_add, smul_eq_mul, mul_comm] using
    hasSum_periodSeries b center h d hn

theorem rowTest_periodFunction_eq_coeff (b center : ℂ) (h d ell : ℕ) :
    rowTest ell (periodFunction b center h d) =
      PowerSeries.coeff ell (periodSeries b center h d) := by
  have hd : DifferentiableOn ℂ (periodFunction b center h d)
      (Metric.closedBall 0 (1 / 2)) := by
    intro z hz
    apply (analyticAt_periodFunction b center h d ?_).differentiableAt.differentiableWithinAt
    have hz' : ‖z‖ ≤ 1 / 2 := by simpa only [Metric.mem_closedBall, dist_zero_right] using hz
    linarith
  have hp := hd.hasFPowerSeriesOnBall (R := (1 / 2 : NNReal)) (by norm_num)
  have he := hp.hasFPowerSeriesAt.eq_formalMultilinearSeries
    (hasFPowerSeriesAt_periodFunction b center h d)
  have hh := congrArg (fun p : FormalMultilinearSeries ℂ ℂ ℂ => p ell (fun _ => 1)) he
  simpa only [rowTest, FormalMultilinearSeries.apply_eq_prod_smul_coeff,
    Finset.prod_const_one, one_smul, FormalMultilinearSeries.coeff_ofScalars,
    NNReal.coe_div, NNReal.coe_one, NNReal.coe_ofNat] using hh

theorem rowTest_congr_sphere {f g : ℂ → ℂ}
    (hfg : ∀ z ∈ Metric.sphere (0 : ℂ) (1 / 2), f z = g z) (ell : ℕ) :
    rowTest ell f = rowTest ell g := by
  simp only [rowTest, cauchyPowerSeries_apply]
  congr 1
  apply circleIntegral.integral_congr (by norm_num)
  intro z hz
  change (1 / (z - 0)) ^ ell • (z - 0)⁻¹ • f z =
    (1 / (z - 0)) ^ ell • (z - 0)⁻¹ • g z
  rw [hfg z hz]

theorem norm_binomial_product_le {m : ℕ} (a : Fin m → ℕ) (A : Fin m →₀ ℕ) :
    ‖((∏ i, (a i).choose (A i) : ℕ) : ℂ)‖ ≤ (2 : ℝ) ^ (∑ i, a i) := by
  rw [Complex.norm_natCast]
  have h : (∏ i, (a i).choose (A i) : ℕ) ≤ 2 ^ (∑ i, a i) := by
    calc
      _ ≤ ∏ i, 2 ^ a i := Finset.prod_le_prod (fun i _ => Nat.choose_le_two_pow _ _)
      _ = _ := Finset.prod_pow_eq_pow_sum _ _ _
  exact_mod_cast h

noncomputable def columnFunction {m : ℕ} (h : ℕ) (a : Fin m → ℕ)
    (A : Fin m →₀ ℕ) : ℂ → ℂ :=
  exponentialMonomial ((∏ i, (a i).choose (A i) : ℕ) : ℂ) (h : ℂ)
    (∑ i : Fin m, (a i - A i))

theorem differentiable_columnFunction {m : ℕ} (h : ℕ) (a : Fin m → ℕ)
    (A : Fin m →₀ ℕ) : Differentiable ℂ (columnFunction h a A) :=
  differentiable_exponentialMonomial _ _ _

theorem norm_columnFunction_le {m : ℕ} (h : ℕ) (a : Fin m → ℕ)
    (A : Fin m →₀ ℕ) (w : Fin m → ℝ) {R H w0 wstar : ℝ}
    (hR : 1 ≤ R) (hH : 0 ≤ H) (hw0 : 0 < w0) (hws : 0 < wstar)
    (hw : ∀ i, wstar ≤ w i) (hcol : w0 * h + ∑ i, w i * a i ≤ H)
    {z : ℂ} (hz : ‖z‖ ≤ R) :
    ‖columnFunction h a A z‖ ≤
      Real.exp (H * (R / w0 + Real.log (2 * R) / wstar)) := by
  have hwpos (i) : 0 ≤ w i := hws.le.trans (hw i)
  have hsum0 : 0 ≤ ∑ i, w i * a i := Finset.sum_nonneg fun i _ => mul_nonneg (hwpos i) (Nat.cast_nonneg _)
  have hh : ‖(h : ℂ)‖ ≤ H / w0 := by
    rw [Complex.norm_natCast, le_div_iff₀ hw0]
    nlinarith
  have htot : (((∑ i, a i : ℕ) : ℝ)) ≤ H / wstar := by
    rw [le_div_iff₀ hws]
    have hs : wstar * ∑ i, (a i : ℝ) ≤ ∑ i, w i * a i := by
      rw [Finset.mul_sum]
      exact Finset.sum_le_sum fun i _ => mul_le_mul_of_nonneg_right (hw i) (Nat.cast_nonneg _)
    have hcast : ((∑ i, a i : ℕ) : ℝ) = ∑ i, (a i : ℝ) := by push_cast; rfl
    rw [hcast]
    nlinarith
  exact norm_exponentialMonomial_le_exp_budget _ _ _ _ hR hH hw0 hws hz
    (norm_binomial_product_le a A) hh
    (Finset.sum_le_sum fun i _ => Nat.sub_le _ _) htot

end PiExponent.PeriodAnalytic

end OAI
end Source0856

-- Source: OAI/NumberTheory/PiExponent/Analysis/AnalyticRowSeries.lean
section Source0857
/-
Modification notice for the LogTwo project.
Derived from openai/math (Apache-2.0), revision adc7f1241b42e322a6451854ab7e4b4c146bf78a.
Original source: lean/OAI/NumberTheory/PiExponent/Analysis/AnalyticRowSeries.lean
Changes: Convert module/import declarations to the Lean 4.34 public module format.
See ../THIRD_PARTY_NOTICES.txt for provenance and the recorded changes.
-/

namespace OAI

open scoped BigOperators
open Complex Finset MeasureTheory Filter

namespace PiExponent.AnalyticCollision

theorem hasSum_rowTest {F : ℕ → ℂ → ℂ} {f : ℂ → ℂ} {bound : ℕ → ℝ}
    (hF : ∀ n, Measurable (F n))
    (hbound : ∀ n z, z ∈ Metric.sphere (0 : ℂ) (1 / 2) → ‖F n z‖ ≤ bound n)
    (hsum : Summable bound)
    (hpoint : ∀ z ∈ Metric.sphere (0 : ℂ) (1 / 2), HasSum (fun n => F n z) (f z))
    (ell : ℕ) : HasSum (fun n => rowTest ell (F n)) (rowTest ell f) := by
  simp only [rowTest, cauchyPowerSeries_apply]
  apply HasSum.const_smul
  change HasSum (fun n => ∫ θ in (0 : ℝ)..2 * Real.pi,
      deriv (circleMap 0 (1 / 2)) θ •
        ((1 / (circleMap 0 (1 / 2) θ - 0)) ^ ell •
          (circleMap 0 (1 / 2) θ - 0)⁻¹ • F n (circleMap 0 (1 / 2) θ)))
    (∫ θ in (0 : ℝ)..2 * Real.pi,
      deriv (circleMap 0 (1 / 2)) θ •
        ((1 / (circleMap 0 (1 / 2) θ - 0)) ^ ell •
          (circleMap 0 (1 / 2) θ - 0)⁻¹ • f (circleMap 0 (1 / 2) θ)))
  apply intervalIntegral.hasSum_integral_of_dominated_convergence
    (fun n _ => (2 : ℝ) ^ ell * bound n)
  · intro n
    apply Measurable.aestronglyMeasurable
    simp only [deriv_circleMap]
    exact (by fun_prop)
  · intro n
    apply Eventually.of_forall
    intro θ _
    have hb := hbound n (circleMap 0 (1 / 2) θ) (circleMap_mem_sphere 0 (by norm_num) θ)
    simp only [deriv_circleMap, norm_smul, norm_mul, norm_I, mul_one, sub_zero,
      norm_pow, norm_div, norm_one, norm_inv, norm_circleMap_zero]
    norm_num only [abs_of_pos (by norm_num : (0 : ℝ) < 1 / 2), one_div, inv_div, div_one]
    calc
      _ = (2 : ℝ) ^ ell * ‖F n (circleMap 0 (1 / 2) θ)‖ := by ring
      _ ≤ (2 : ℝ) ^ ell * bound n := mul_le_mul_of_nonneg_left hb (by positivity)
  · exact Eventually.of_forall fun _ _ => hsum.mul_left _
  · simpa only [tsum_mul_left] using
      (intervalIntegrable_const : IntervalIntegrable (fun _ : ℝ => (2 : ℝ) ^ ell * ∑' n, bound n)
        volume 0 (2 * Real.pi))
  · apply Eventually.of_forall
    intro θ _
    exact (((hpoint _ (circleMap_mem_sphere 0 (by norm_num) θ)).const_smul _).const_smul _).const_smul _

theorem rowTest_const_mul (ell : ℕ) (c : ℂ) (f : ℂ → ℂ) :
    rowTest ell (fun t => c * f t) = c * rowTest ell f := by
  simp only [rowTest, cauchyPowerSeries_apply, smul_eq_mul]
  have heq : (fun z : ℂ => (1 / (z - 0)) ^ ell * ((z - 0)⁻¹ * (c * f z))) =
      (fun z : ℂ => c * ((1 / (z - 0)) ^ ell * ((z - 0)⁻¹ * f z))) := by
    funext z
    ring
  rw [heq, circleIntegral.integral_const_mul]
  ring

theorem hasSum_translated_row {f : ℂ → ℂ} (hf : Differentiable ℂ f)
    {R : NNReal} (hR : 0 < R) {D : ℝ} (hD : 0 ≤ D)
    (hfD : ∀ z ∈ Metric.sphere (0 : ℂ) (R : ℝ), ‖f z‖ ≤ D)
    {center : ℂ} (hc : ‖center‖ + 3 / 4 ≤ (R : ℝ) / 2) (ell : ℕ) :
    HasSum (fun d => rowTest ell (fun t => ((center + Complex.log (1 + t)) / (R : ℂ)) ^ d) *
      normalizedTaylorCoeff f R d)
      (rowTest ell (fun t => f (center + Complex.log (1 + t)))) := by
  have h := hasSum_rowTest
    (F := fun d t => normalizedTaylorCoeff f R d *
      ((center + Complex.log (1 + t)) / (R : ℂ)) ^ d)
    (f := fun t => f (center + Complex.log (1 + t)))
    (bound := fun d => D * (1 / 2 : ℝ) ^ d)
    (by intro d; fun_prop) ?_ ?_ ?_ ell
  · convert! h using 1
    funext d
    rw [rowTest_const_mul, mul_comm]
  · intro d t ht
    rw [norm_mul, norm_pow]
    apply mul_le_mul (norm_normalizedTaylorCoeff_le hR hfD d)
    · apply pow_le_pow_left₀ (norm_nonneg _) (norm_shifted_log_div_le_half hR hc _)
      simpa only [Metric.mem_sphere, dist_zero_right] using ht.le
    · positivity
    · exact hD
  · exact (summable_geometric_of_lt_one (by norm_num : (0 : ℝ) ≤ 1 / 2)
      (by norm_num : (1 / 2 : ℝ) < 1)).mul_left D
  · intro t _
    exact hasSum_normalizedTaylorCoeff hf hR _

end PiExponent.AnalyticCollision

end OAI
end Source0857

-- Source: LogTwo/Analysis/RealCenterRows.lean
section Source0858
-- Modified in this edition: unused plain lemmas removed; see reduction.json.
/-
Modification notice for the LogTwo project.
Adapted from openai/math (Apache-2.0), revision adc7f1241b42e322a6451854ab7e4b4c146bf78a.
Changes: Adapt analytic row-series interfaces to the nonperiodic centers j * log(2).
See ../THIRD_PARTY_NOTICES.txt for provenance and the recorded changes.
-/

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

end
end LogTwo.Analysis
end Source0858

-- Source: LogTwo/Analysis/MatrixAnalyticBridge.lean
section Source0859
/-
Modification notice for the LogTwo project.
Adapted from leanprover-community/mathlib4 (Apache-2.0), revision d13f23b723b8a846827a245b89c10fc7d3f11612.
Changes: Adapt the optionEquivLeft coefficient proof strategy to optionEquivRight.
See ../THIRD_PARTY_NOTICES.txt for provenance and the recorded changes.
-/

namespace LogTwo.Analysis
open MvPolynomial
open OAI.PiExponent
noncomputable section

/-- Splitting off the distinguished variable preserves the double coefficient. -/
theorem optionEquivRight_monomial {R σ : Type*} [CommSemiring R]
    (d : Option σ →₀ ℕ) (r : R) :
    MvPolynomial.optionEquivRight R σ (monomial d r) =
      monomial d.some (Polynomial.monomial (d none) r) := by
  rw [MvPolynomial.optionEquivRight_apply, aeval_monomial, Finsupp.prod_option_index]
  · rw [MvPolynomial.monomial_eq, ← Polynomial.C_mul_X_pow_eq_monomial]
    simp only [MvPolynomial.algebraMap_apply, Polynomial.algebraMap_eq,
      Option.elim_none, Option.elim_some, map_mul, map_pow, mul_assoc]
  · simp
  · intros; rw [pow_add]

theorem optionEquivRight_coeff_coeff {R σ : Type*} [CommSemiring R]
    (d : Option σ →₀ ℕ) (P : MvPolynomial (Option σ) R) :
    ((MvPolynomial.optionEquivRight R σ P).coeff d.some).coeff (d none) =
      P.coeff d := by
  induction P using MvPolynomial.induction_on' generalizing d with
  | monomial e r =>
    rw [optionEquivRight_monomial]
    classical
    by_cases he : e = d
    · subst e
      simp [MvPolynomial.coeff_monomial]
    · by_cases hs : e.some = d.some
      · have hn : e none ≠ d none := by
          intro hn
          apply he
          ext i
          cases i with
          | none => exact hn
          | some i => exact DFunLike.congr_fun hs i
        simp [MvPolynomial.coeff_monomial, Polynomial.coeff_monomial, he, hs, hn]
      · simp [MvPolynomial.coeff_monomial, he, hs]
  | add P Q hP hQ => simp only [map_add, AddMonoidAlgebra.coeff_add, Finsupp.add_apply,
      Polynomial.coeff_add, hP, hQ]

def splitRationalPolynomial (m : ℕ) :
    MvPolynomial (Option (Fin m)) ℚ →+* MvPolynomial (Fin m) (Polynomial ℂ) :=
  (MvPolynomial.optionEquivRight ℂ (Fin m)).toRingHom.comp
    (MvPolynomial.map (algebraMap ℚ ℂ))

@[simp] theorem splitRationalPolynomial_C (m : ℕ) (r : ℚ) :
    splitRationalPolynomial m (C r) = C (Polynomial.C (r : ℂ)) := by
  simp [splitRationalPolynomial]

@[simp] theorem splitRationalPolynomial_X (m : ℕ) (i : Option (Fin m)) :
    splitRationalPolynomial m (X i) = i.elim (C Polynomial.X) X := by
  cases i <;> simp [splitRationalPolynomial]

theorem splitRationalPolynomial_truncatedLog (m T : ℕ) :
    splitRationalPolynomial m (Interpolation.truncatedLog T) =
      C (InterpolationMatrix.truncatedLog T) := by
  induction T with
  | zero => simp [Interpolation.truncatedLog, InterpolationMatrix.truncatedLog]
  | succ T ih =>
    by_cases hT : T = 0
    · subst T
      simp [Interpolation.truncatedLog, InterpolationMatrix.truncatedLog,
        PowerSeries.trunc_succ, PowerSeries.coeff_log]
    · have hs : Interpolation.truncatedLog (m := m) (T+1) =
          Interpolation.truncatedLog T +
          C ((-1 : ℚ)^(T+1) / T) * X none ^ T :=
        Finset.sum_Ico_succ_top (Nat.one_le_iff_ne_zero.mpr hT) _
      rw [hs, map_add, map_mul, map_pow, splitRationalPolynomial_C,
        splitRationalPolynomial_X, ih]
      simp [InterpolationMatrix.truncatedLog, PowerSeries.trunc_succ,
        PowerSeries.coeff_log, hT, ← Polynomial.C_mul_X_pow_eq_monomial]

theorem splitRationalPolynomial_columnExpansion {m : ℕ}
    (r : Fin m → ℚ) (T : Fin m → ℕ) (j : ℕ) (col : Interpolation.Column m) :
    splitRationalPolynomial m (Interpolation.columnExpansion r T j col) =
      C (Polynomial.C ((2 : ℂ)^(j*col.h))) *
        InterpolationMatrix.monomialImage (fun i => (r i : ℂ))
          (fun i => InterpolationMatrix.truncatedLog (T i)) j col.h col.alpha := by
  simp [Interpolation.columnExpansion, InterpolationMatrix.monomialImage,
    map_prod, splitRationalPolynomial_truncatedLog, map_add, map_pow, mul_assoc]

/-- The scalar 2^(j*h) relates the actual rational entries to the generic
translation matrix. It is retained before any determinant expansion. -/
theorem coefficientMatrix_eq_scaled_entry {m : ℕ}
    (r : Fin m → ℚ) (T : Fin m → ℕ)
    (row : Interpolation.Row m) (col : Interpolation.Column m) :
    (Interpolation.coefficientMatrix r T row col : ℂ) =
      (2 : ℂ)^(row.j*col.h) * InterpolationMatrix.entry
        (fun i => (r i : ℂ)) (fun i => InterpolationMatrix.truncatedLog (T i))
        row.j row.s row.beta col.h col.alpha := by
  have hc := optionEquivRight_coeff_coeff (Interpolation.rowExponent row)
    (MvPolynomial.map (algebraMap ℚ ℂ) (Interpolation.columnExpansion r T row.j col))
  have hsome : (Interpolation.rowExponent row).some =
      InterpolationMatrix.exponentVector row.beta := by ext i; rfl
  have hnone : Interpolation.rowExponent row none = row.s := rfl
  change ((splitRationalPolynomial m (Interpolation.columnExpansion r T row.j col)).coeff
    (Interpolation.rowExponent row).some).coeff (Interpolation.rowExponent row none) = _ at hc
  rw [hsome, hnone, splitRationalPolynomial_columnExpansion,
    MvPolynomial.coeff_C_mul, Polynomial.coeff_C_mul, MvPolynomial.coeff_map] at hc
  exact hc.symm

end
end LogTwo.Analysis
end Source0859

-- Source: LogTwo/Analysis/RealCenterMatrix.lean
section Source0860
-- Modified in this edition: unused plain lemmas removed; see reduction.json.
/-
Modification notice for the LogTwo project.
Adapted from openai/math (Apache-2.0), revision adc7f1241b42e322a6451854ab7e4b4c146bf78a.
Changes: Adapt analytic matrix-translation interfaces, preserving the factor 2^(j*h).
See ../THIRD_PARTY_NOTICES.txt for provenance and the recorded changes.
-/

namespace LogTwo.Analysis
open OAI PiExponent MatrixTranslation RowTranslation AnalyticCollision PeriodAnalytic
open LogTwo.Interpolation
noncomputable section

/-- A column-independent scalar for each translation choice in an actual row. -/
def actualRowScalar {m : ℕ} (r : Fin m → ℚ) (T : Fin m → ℕ)
    (row : Row m) (S : Finset (Fin m →₀ ℕ))
    (t : RowChoices S (InterpolationMatrix.exponentVector row.beta) row.s) : ℂ :=
  rowScalar (fun i => (row.j : ℂ)*((r i : ℂ)-(Real.log 2 : ℂ)))
    (fun i => tail (T i) (PowerSeries.log ℂ))
    (InterpolationMatrix.exponentVector row.beta) t.1.1 t.2.1 t.2.2

def actualAnalyticRow {m : ℕ} (row : Row m) (S : Finset (Fin m →₀ ℕ))
    (t : RowChoices S (InterpolationMatrix.exponentVector row.beta) row.s)
    (col : Column m) : ℂ :=
  rowTest (row.s-t.2.2) (fun z => columnFunction col.h col.alpha t.1.1
    ((row.j : ℂ)*(Real.log 2 : ℂ)+Complex.log (1+z)))

/-- Equation (4.1) for the original rational matrix, including 2^(j*h). -/
theorem coefficientMatrix_eq_analytic_rows {m : ℕ}
    (r : Fin m → ℚ) (T : Fin m → ℕ) (row : Row m) (col : Column m)
    (S : Finset (Fin m →₀ ℕ))
    (hp : (periodMonomial row.j (Real.log 2 : ℂ) col.h col.alpha).support ⊆ S) :
    (coefficientMatrix r T row col : ℂ) =
      ∑ t : RowChoices S (InterpolationMatrix.exponentVector row.beta) row.s,
        actualRowScalar r T row S t * actualAnalyticRow row S t col := by
  rw [coefficientMatrix_eq_scaled_entry,
    matrix_entry_translation_choices _ _ _ _ _ _ _ _ S hp, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro t _
  change _ = _ * rowTest _ _
  rw [← scaled_periodMonomial_coeff_eq_rowTest]
  unfold actualRowScalar
  ring

/-- Multilinear expansion of the same selected rational minor used by the
arithmetic lower bound. No determinant estimate is transferred. -/
theorem actual_minor_analytic_expansion {m : ℕ} {w : Weights m} {H : ℚ}
    {r : Fin m → ℚ} {T : Fin m → ℕ} (minor : FullRowMinor w H r T)
    (S : Finset (Fin m →₀ ℕ))
    (hp : ∀ i c, (periodMonomial (minor.rows i).j (Real.log 2 : ℂ)
      (minor.columns c).h (minor.columns c).alpha).support ⊆ S) :
    Matrix.det (fun i c => (minor.matrix i c : ℂ)) =
      ∑ f : (∀ i, RowChoices S (InterpolationMatrix.exponentVector (minor.rows i).beta)
        (minor.rows i).s),
        (∏ i, actualRowScalar r T (minor.rows i) S (f i)) *
          Matrix.det (fun i c => actualAnalyticRow (minor.rows i) S (f i) (minor.columns c)) := by
  have he : (fun i c => (minor.matrix i c : ℂ)) =
      (fun i c => ∑ t : RowChoices S
        (InterpolationMatrix.exponentVector (minor.rows i).beta) (minor.rows i).s,
        actualRowScalar r T (minor.rows i) S t *
          actualAnalyticRow (minor.rows i) S t (minor.columns c)) := by
    funext i c
    exact coefficientMatrix_eq_analytic_rows r T (minor.rows i) (minor.columns c) S (hp i c)
  rw [he]
  exact det_dependent_row_sum _ _

/-- Every admissible column uses the same finite transverse index set. -/
theorem actual_minor_support_subset {m : ℕ} {w : Weights m} {H : ℚ}
    {r : Fin m → ℚ} {T : Fin m → ℕ} (minor : FullRowMinor w H r T)
    (i c : Fin minor.size) :
    (periodMonomial (minor.rows i).j (Real.log 2 : ℂ)
      (minor.columns c).h (minor.columns c).alpha).support ⊆
      transverseIndices (fun k => (w.w k : ℝ)) (H : ℝ) := by
  apply periodMonomial_support_subset
  · intro k; exact_mod_cast w.w_pos k
  · have hc := minor.column_valid c
    have hn : (0 : ℚ) ≤ w.w0 * (minor.columns c).h :=
      mul_nonneg w.w0_pos.le (Nat.cast_nonneg _)
    have hb : ∑ k, w.w k * (minor.columns c).alpha k ≤ H :=
      le_trans (le_add_of_nonneg_left hn) hc
    exact_mod_cast hb

/-- Full expansion with the support hypothesis discharged by admissibility. -/
theorem actual_minor_analytic_expansion_weighted {m : ℕ} {w : Weights m} {H : ℚ}
    {r : Fin m → ℚ} {T : Fin m → ℕ} (minor : FullRowMinor w H r T) :
    let S := transverseIndices (fun k => (w.w k : ℝ)) (H : ℝ)
    Matrix.det (fun i c => (minor.matrix i c : ℂ)) =
      ∑ f : (∀ i, RowChoices S (InterpolationMatrix.exponentVector (minor.rows i).beta)
        (minor.rows i).s),
        (∏ i, actualRowScalar r T (minor.rows i) S (f i)) *
          Matrix.det (fun i c => actualAnalyticRow (minor.rows i) S (f i) (minor.columns c)) := by
  exact actual_minor_analytic_expansion minor _ (actual_minor_support_subset minor)

end
end LogTwo.Analysis
end Source0860

-- Source: OAI/NumberTheory/PiExponent/Analysis/CollisionCombinatorics.lean
section Source0861
-- Modified in this edition: unused plain lemmas removed; see reduction.json.
/-
Modification notice for the LogTwo project.
Derived from openai/math (Apache-2.0), revision adc7f1241b42e322a6451854ab7e4b4c146bf78a.
Original source: lean/OAI/NumberTheory/PiExponent/Analysis/CollisionCombinatorics.lean
Changes: Convert module/import declarations to the Lean 4.34 public module format.
See ../THIRD_PARTY_NOTICES.txt for provenance and the recorded changes.
-/

namespace OAI

open scoped BigOperators

namespace PiExponent.Collision

theorem choose_card_le_sum (s : Finset ℕ) :
    s.card.choose 2 ≤ ∑ d ∈ s, d := by
  induction s using Finset.induction_on_max with
  | empty => simp
  | insert a s hmax ih =>
    have ha : a ∉ s := by
      intro h
      exact (lt_irrefl a) (hmax a h)
    have hsub : s ⊆ Finset.range a := by
      intro x hx
      exact Finset.mem_range.mpr (hmax x hx)
    have hcard : s.card ≤ a := by
      simpa using Finset.card_le_card hsub
    rw [Finset.card_insert_of_notMem ha, Finset.sum_insert ha]
    rw [show s.card + 1 = s.card.succ from rfl,
      Nat.choose_succ_succ s.card 1, Nat.choose_one_right]
    exact Nat.add_le_add hcard ih

theorem choose_card_le_sum_of_injOn {ι : Type*} (s : Finset ι)
    (degree : ι → ℕ) (hinj : Set.InjOn degree (s : Set ι)) :
    s.card.choose 2 ≤ ∑ i ∈ s, degree i := by
  have h := choose_card_le_sum (s.image degree)
  rw [Finset.card_image_of_injOn hinj, Finset.sum_image hinj] at h
  exact h

def multiplicity {ι κ : Type*} [DecidableEq κ]
    (rows : Finset ι) (group : ι → κ) (a : κ) : ℕ :=
  (rows.filter fun i => group i = a).card

theorem sum_multiplicity {ι κ : Type*} [DecidableEq κ]
    (rows : Finset ι) (groups : Finset κ) (group : ι → κ)
    (hgroups : ∀ i ∈ rows, group i ∈ groups) :
    ∑ a ∈ groups, multiplicity rows group a = rows.card := by
  simpa only [multiplicity, Finset.sum_const, smul_eq_mul, mul_one]
    using Finset.sum_fiberwise_of_maps_to hgroups (fun _ => (1 : ℕ))

theorem sum_choose_multiplicity_le_sum_degree {ι κ : Type*} [DecidableEq κ]
    (rows : Finset ι) (groups : Finset κ) (group : ι → κ) (degree : ι → ℕ)
    (hgroups : ∀ i ∈ rows, group i ∈ groups)
    (hinj : Set.InjOn (fun i => (group i, degree i)) (rows : Set ι)) :
    (∑ a ∈ groups, (multiplicity rows group a).choose 2) ≤
      ∑ i ∈ rows, degree i := by
  calc
    (∑ a ∈ groups, (multiplicity rows group a).choose 2) ≤
        ∑ a ∈ groups, ∑ i ∈ rows.filter (fun i => group i = a), degree i := by
      apply Finset.sum_le_sum
      intro a _
      apply choose_card_le_sum_of_injOn
      intro i hi j hj hdegree
      have hi' := Finset.mem_filter.mp hi
      have hj' := Finset.mem_filter.mp hj
      apply hinj hi'.1 hj'.1
      exact Prod.ext (hi'.2.trans hj'.2.symm) hdegree
    _ = ∑ i ∈ rows, degree i :=
      Finset.sum_fiberwise_of_maps_to hgroups degree

theorem sum_choose_multiplicity_le_sum_degree_univ
    {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq κ]
    (group : ι → κ) (degree : ι → ℕ)
    (hinj : Function.Injective (fun i => (group i, degree i))) :
    (∑ a, (multiplicity Finset.univ group a).choose 2) ≤ ∑ i, degree i := by
  exact sum_choose_multiplicity_le_sum_degree Finset.univ Finset.univ group degree
    (by simp) hinj.injOn

theorem sum_multiplicity_univ
    {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq κ]
    (group : ι → κ) :
    ∑ a, multiplicity Finset.univ group a = Fintype.card ι := by
  exact sum_multiplicity Finset.univ Finset.univ group (by simp)

theorem sum_multiplicity_eq_card_filter {ι κ : Type*} [DecidableEq κ]
    (rows : Finset ι) (groups : Finset κ) (group : ι → κ) :
    ∑ a ∈ groups, multiplicity rows group a =
      (rows.filter fun i => group i ∈ groups).card := by
  exact Finset.sum_card_fiberwise_eq_card_filter rows groups group

theorem cutoff_mul_high_count_le_sum {ι : Type*}
    (rows : Finset ι) (weight : ι → ℝ) (cutoff : ℝ)
    (hnonneg : ∀ i ∈ rows, 0 ≤ weight i) :
    cutoff * ((rows.filter fun i => ¬ weight i ≤ cutoff).card : ℝ) ≤
      ∑ i ∈ rows, weight i := by
  classical
  calc
    _ = ∑ i ∈ rows.filter (fun i => ¬ weight i ≤ cutoff), cutoff := by
      simp [mul_comm]
    _ ≤ ∑ i ∈ rows.filter (fun i => ¬ weight i ≤ cutoff), weight i := by
      apply Finset.sum_le_sum
      intro i hi
      exact le_of_lt (lt_of_not_ge (Finset.mem_filter.mp hi).2)
    _ ≤ ∑ i ∈ rows, weight i := by
      apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ rows)
      intro i hi _
      exact hnonneg i hi

theorem sum_weight_ge_of_low_count_le {ι : Type*}
    (rows : Finset ι) (weight : ι → ℝ) {cutoff η : ℝ}
    (hcutoff : 0 ≤ cutoff) (hnonneg : ∀ i ∈ rows, 0 ≤ weight i)
    (hlow : ((rows.filter fun i => weight i ≤ cutoff).card : ℝ) ≤
      η * rows.card) :
    cutoff * (1 - η) * rows.card ≤ ∑ i ∈ rows, weight i := by
  classical
  have hcard : ((rows.filter fun i => weight i ≤ cutoff).card : ℝ) +
      ((rows.filter fun i => ¬ weight i ≤ cutoff).card : ℝ) = rows.card := by
    exact_mod_cast (Finset.card_filter_add_card_filter_not (s := rows)
      (fun i => weight i ≤ cutoff))
  have hhigh : (1 - η) * rows.card ≤
      ((rows.filter fun i => ¬ weight i ≤ cutoff).card : ℝ) := by nlinarith
  calc
    _ = cutoff * ((1 - η) * rows.card) := by ring
    _ ≤ cutoff * ((rows.filter fun i => ¬ weight i ≤ cutoff).card : ℝ) :=
      mul_le_mul_of_nonneg_left hhigh hcutoff
    _ ≤ ∑ i ∈ rows, weight i := cutoff_mul_high_count_le_sum rows weight cutoff hnonneg

end PiExponent.Collision

end OAI
end Source0861

-- Source: OAI/NumberTheory/PiExponent/Analysis/CollisionExponential.lean
section Source0862
/-
Modification notice for the LogTwo project.
Derived from openai/math (Apache-2.0), revision adc7f1241b42e322a6451854ab7e4b4c146bf78a.
Original source: lean/OAI/NumberTheory/PiExponent/Analysis/CollisionExponential.lean
Changes: Convert module/import declarations to the Lean 4.34 public module format.
See ../THIRD_PARTY_NOTICES.txt for provenance and the recorded changes.
-/

namespace OAI

open scoped BigOperators

namespace PiExponent.Collision

noncomputable def collisionRatio : ℝ := Real.exp (-Real.log 2 / 2)

theorem collisionRatio_pos : 0 < collisionRatio := Real.exp_pos _

theorem collisionRatio_lt_one : collisionRatio < 1 := by
  apply Real.exp_lt_one_iff.mpr
  have h : 0 < Real.log 2 := Real.log_pos (by norm_num)
  linarith

theorem collisionRatio_mul_self : collisionRatio * collisionRatio = 1 / 2 := by
  unfold collisionRatio
  rw [← Real.exp_add]
  have heq : -Real.log 2 / 2 + -Real.log 2 / 2 = -Real.log 2 := by ring
  rw [heq, Real.exp_neg, Real.exp_log (by norm_num)]
  simp only [one_div]

theorem factorial_le_exp_card_log (M : ℕ) :
    (M.factorial : ℝ) ≤ Real.exp ((M : ℝ) * Real.log M) := by
  by_cases hM : M = 0
  · subst M
    norm_num
  · rw [Real.exp_nat_mul, Real.exp_log (by exact_mod_cast Nat.pos_of_ne_zero hM)]
    exact_mod_cast Nat.factorial_le_pow M

theorem twice_collision_count_eq
    {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq κ] (group : ι → κ) :
    2 * ((∑ a, (multiplicity Finset.univ group a).choose 2 : ℕ) : ℝ) =
      (∑ a, (multiplicity Finset.univ group a : ℝ) ^ 2) - Fintype.card ι := by
  have hsum : (∑ a, (multiplicity Finset.univ group a : ℝ)) = Fintype.card ι := by
    exact_mod_cast sum_multiplicity_univ group
  push_cast
  rw [Finset.mul_sum]
  calc
    _ = ∑ a, ((multiplicity Finset.univ group a : ℝ) ^ 2 -
        (multiplicity Finset.univ group a : ℝ)) := by
      apply Finset.sum_congr rfl
      intro a _
      rw [Nat.cast_choose_two]
      ring
    _ = _ := by rw [Finset.sum_sub_distrib, hsum]

theorem collision_factor_le_exp (M C ell : ℕ) {H A v S : ℝ}
    (hell : (ell : ℝ) ≤ (M : ℝ) * H / v)
    (hC : 2 * (C : ℝ) = S - M) :
    ((M.factorial : ℝ) * (Real.exp (H * A)) ^ M * (2 : ℝ) ^ ell) *
      collisionRatio ^ C * ((1 - collisionRatio)⁻¹) ^ M ≤
    Real.exp (-(Real.log 2 / 4) * S + (M : ℝ) * H * (A + Real.log 2 / v) +
      (M : ℝ) * (Real.log M + Real.log 2 / 4 - Real.log (1 - collisionRatio))) := by
  have hlog2 : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
  have hr : 0 < 1 - collisionRatio := sub_pos.mpr collisionRatio_lt_one
  have ht : (2 : ℝ) ^ ell ≤ Real.exp ((M : ℝ) * H / v * Real.log 2) := by
    calc
      _ = Real.exp ((ell : ℝ) * Real.log 2) := by
        rw [Real.exp_nat_mul, Real.exp_log (by norm_num)]
      _ ≤ _ := Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right hell hlog2)
  calc
    _ ≤ (Real.exp ((M : ℝ) * Real.log M) * (Real.exp (H * A)) ^ M *
        Real.exp ((M : ℝ) * H / v * Real.log 2)) *
        collisionRatio ^ C * ((1 - collisionRatio)⁻¹) ^ M := by
      apply mul_le_mul_of_nonneg_right _ (pow_nonneg (inv_nonneg.mpr hr.le) M)
      apply mul_le_mul_of_nonneg_right _ (pow_nonneg collisionRatio_pos.le C)
      apply mul_le_mul _ ht (by positivity) (by positivity)
      exact mul_le_mul_of_nonneg_right (factorial_le_exp_card_log M) (by positivity)
    _ = _ := by
      rw [← Real.exp_nat_mul, collisionRatio, ← Real.exp_nat_mul]
      have hi : (1 - Real.exp (-Real.log 2 / 2))⁻¹ =
          Real.exp (-Real.log (1 - collisionRatio)) := by
        rw [Real.exp_neg, Real.exp_log hr]
        rfl
      rw [hi, ← Real.exp_nat_mul]
      simp only [← Real.exp_add]
      congr 1
      have hc : (C : ℝ) = (S - M) / 2 := by linarith
      rw [hc]
      unfold collisionRatio
      ring

noncomputable def collisionRemainder (M : ℕ) (H : ℝ) : ℝ :=
  (Real.log M + Real.log 2 / 4 - Real.log (1 - collisionRatio)) / H

theorem collision_factor_le_exp_normalized (M C ell : ℕ) {H A v S : ℝ}
    (hH : 0 < H) (hell : (ell : ℝ) ≤ (M : ℝ) * H / v)
    (hC : 2 * (C : ℝ) = S - M) :
    ((M.factorial : ℝ) * (Real.exp (H * A)) ^ M * (2 : ℝ) ^ ell) *
      collisionRatio ^ C * ((1 - collisionRatio)⁻¹) ^ M ≤
    Real.exp (-(Real.log 2 / 4) * S + (M : ℝ) * H *
      (A + Real.log 2 / v + collisionRemainder M H)) := by
  convert collision_factor_le_exp M C ell hell hC using 1
  congr 1
  unfold collisionRemainder
  field_simp
  ring

end PiExponent.Collision

end OAI
end Source0862

-- Source: OAI/NumberTheory/PiExponent/Analysis/CollisionGeometricSum.lean
section Source0863
/-
Modification notice for the LogTwo project.
Derived from openai/math (Apache-2.0), revision adc7f1241b42e322a6451854ab7e4b4c146bf78a.
Original source: lean/OAI/NumberTheory/PiExponent/Analysis/CollisionGeometricSum.lean
Changes: Convert module/import declarations to the Lean 4.34 public module format.
See ../THIRD_PARTY_NOTICES.txt for provenance and the recorded changes.
-/

namespace OAI

open scoped BigOperators

namespace PiExponent.Collision

theorem sum_pow_fin_le_inv_one_sub {s : ℝ} (hs0 : 0 ≤ s) (hs1 : s < 1)
    (N : ℕ) : (∑ k : Fin N, s ^ (k : ℕ)) ≤ (1 - s)⁻¹ := by
  rw [Fin.sum_univ_eq_sum_range (fun k : ℕ => s ^ k), ← one_div]
  apply (le_div_iff₀ (sub_pos.mpr hs1)).2
  rw [geom_sum_mul_neg]
  exact sub_le_self 1 (pow_nonneg hs0 N)

theorem sum_pow_degree_assignments_eq {ι : Type*} [Fintype ι] [DecidableEq ι]
    (s : ℝ) (N : ℕ) :
    (∑ f : ι → Fin N, s ^ (∑ i, (f i : ℕ))) =
      (∑ k : Fin N, s ^ (k : ℕ)) ^ Fintype.card ι := by
  classical
  simp_rw [← Finset.prod_pow_eq_pow_sum]
  rw [← Fintype.prod_sum (fun (_ : ι) (k : Fin N) => s ^ (k : ℕ))]
  simp

theorem sum_pow_degree_assignments_le {ι : Type*} [Fintype ι] [DecidableEq ι]
    {s : ℝ} (hs0 : 0 ≤ s) (hs1 : s < 1) (N : ℕ) :
    (∑ f : ι → Fin N, s ^ (∑ i, (f i : ℕ))) ≤
      ((1 - s)⁻¹) ^ Fintype.card ι := by
  rw [sum_pow_degree_assignments_eq]
  exact pow_le_pow_left₀ (Finset.sum_nonneg fun k _ => pow_nonneg hs0 _)
    (sum_pow_fin_le_inv_one_sub hs0 hs1 N) _

theorem collision_geometric_sum_le
    {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
    (group : ι → κ) {s : ℝ} (hs0 : 0 ≤ s) (hs1 : s < 1) (N : ℕ) :
    (∑ f ∈ (Finset.univ : Finset (ι → Fin N)).filter
        (fun f => Function.Injective (fun i => (group i, (f i : ℕ)))),
      (s * s) ^ (∑ i, (f i : ℕ))) ≤
      s ^ (∑ a, (multiplicity Finset.univ group a).choose 2) *
        ((1 - s)⁻¹) ^ Fintype.card ι := by
  classical
  let good := (Finset.univ : Finset (ι → Fin N)).filter
    (fun f => Function.Injective (fun i => (group i, (f i : ℕ))))
  let C := ∑ a, (multiplicity Finset.univ group a).choose 2
  have hpoint : ∀ f ∈ good,
      (s * s) ^ (∑ i, (f i : ℕ)) ≤ s ^ C * s ^ (∑ i, (f i : ℕ)) := by
    intro f hf
    have hinj := (Finset.mem_filter.mp hf).2
    have hdeg : C ≤ ∑ i, (f i : ℕ) :=
      sum_choose_multiplicity_le_sum_degree_univ group (fun i => (f i : ℕ)) hinj
    rw [mul_pow]
    exact mul_le_mul_of_nonneg_right (pow_le_pow_of_le_one hs0 hs1.le hdeg)
      (pow_nonneg hs0 _)
  calc
    _ ≤ ∑ f ∈ good, s ^ C * s ^ (∑ i, (f i : ℕ)) :=
      Finset.sum_le_sum hpoint
    _ = s ^ C * ∑ f ∈ good, s ^ (∑ i, (f i : ℕ)) := by rw [Finset.mul_sum]
    _ ≤ s ^ C * ∑ f : ι → Fin N, s ^ (∑ i, (f i : ℕ)) := by
      apply mul_le_mul_of_nonneg_left _ (pow_nonneg hs0 C)
      apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
      intro f _ _
      exact pow_nonneg hs0 _
    _ ≤ _ := mul_le_mul_of_nonneg_left (sum_pow_degree_assignments_le hs0 hs1 N)
      (pow_nonneg hs0 C)

end PiExponent.Collision

end OAI
end Source0863

-- Source: OAI/NumberTheory/PiExponent/Analysis/FiniteDeterminantCollision.lean
section Source0864
/-
Modification notice for the LogTwo project.
Derived from openai/math (Apache-2.0), revision adc7f1241b42e322a6451854ab7e4b4c146bf78a.
Original source: lean/OAI/NumberTheory/PiExponent/Analysis/FiniteDeterminantCollision.lean
Changes: Convert module/import declarations to the Lean 4.34 public module format.
See ../THIRD_PARTY_NOTICES.txt for provenance and the recorded changes.
-/

namespace OAI

open scoped BigOperators

namespace PiExponent.FiniteDeterminantCollision

theorem det_finite_row_sum {ι κ δ : Type*} [Fintype ι] [DecidableEq ι]
    [Fintype δ] (group : ι → κ) (B : ι → δ → ℂ) (C : κ → δ → ι → ℂ) :
    Matrix.det (fun i j => ∑ d, B i d * C (group i) d j) =
      ∑ f : ι → δ, (∏ i, B i (f i)) *
        Matrix.det (fun i j => C (group i) (f i) j) := by
  classical
  have hm := (Matrix.detRowAlternating : (ι → ℂ) [⋀^ι]→ₗ[ℂ] ℂ).toMultilinearMap.map_sum
    (fun i d => B i d • C (group i) d)
  calc
    _ = Matrix.det (fun i => ∑ d, B i d • C (group i) d) := by
      congr 1
      funext i j
      simp
    _ = ∑ f : ι → δ, Matrix.det (fun i => B i (f i) • C (group i) (f i)) := hm
    _ = _ := by
      apply Finset.sum_congr rfl
      intro f _
      exact Matrix.det_mul_column (fun i => B i (f i)) (fun i j => C (group i) (f i) j)

theorem norm_det_le_factorial_mul_pow {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A : Matrix ι ι ℂ) {D : ℝ} (hD : 0 ≤ D) (hA : ∀ i j, ‖A i j‖ ≤ D) :
    ‖A.det‖ ≤ (Fintype.card ι).factorial * D ^ Fintype.card ι := by
  rw [Matrix.det_apply]
  calc
    _ ≤ ∑ σ : Equiv.Perm ι, ‖σ.sign • ∏ i, A (σ i) i‖ := norm_sum_le _ _
    _ = ∑ σ : Equiv.Perm ι, ∏ i, ‖A (σ i) i‖ := by
      apply Finset.sum_congr rfl
      intro σ _
      rcases Int.units_eq_one_or σ.sign with hs | hs <;> simp [hs, norm_prod]
    _ ≤ ∑ _σ : Equiv.Perm ι, D ^ Fintype.card ι := by
      apply Finset.sum_le_sum
      intro σ _
      calc
        _ ≤ ∏ _index : ι, |D| := Finset.prod_le_prod₀
          (fun index _ => norm_nonneg _)
          (fun index _ => (hA (σ index) index).trans (le_abs_self D))
        _ = D ^ Fintype.card ι := by simp [abs_of_nonneg hD]
    _ = _ := by simp [Fintype.card_perm]

theorem finite_collision_bound
    {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
    (group : ι → κ) (B : ι → ℕ → ℂ) (C : κ → ℕ → ι → ℂ)
    (D s : ℝ) (L : ι → ℝ) (hD : 0 ≤ D) (hs0 : 0 ≤ s) (hs1 : s < 1)
    (hL : ∀ i, 0 ≤ L i)
    (hC : ∀ a d j, ‖C a d j‖ ≤ D)
    (hB : ∀ i d, ‖B i d‖ ≤ L i * (s * s) ^ d) (N : ℕ) :
    ‖Matrix.det (fun i j => ∑ d : Fin N, B i d * C (group i) d j)‖ ≤
      ((Fintype.card ι).factorial * D ^ Fintype.card ι * (∏ i, L i)) *
        s ^ (∑ a, (Collision.multiplicity Finset.univ group a).choose 2) *
          ((1 - s)⁻¹) ^ Fintype.card ι := by
  classical
  let good := (Finset.univ : Finset (ι → Fin N)).filter
    (fun f => Function.Injective (fun i => (group i, (f i : ℕ))))
  let Q := (Fintype.card ι).factorial * D ^ Fintype.card ι * (∏ i, L i)
  have hQ : 0 ≤ Q :=
    mul_nonneg (mul_nonneg (Nat.cast_nonneg _) (pow_nonneg hD _))
      (Finset.prod_nonneg fun i _ => hL i)
  have hexpand : Matrix.det (fun i j => ∑ d : Fin N, B i d * C (group i) d j) =
      ∑ f ∈ good, (∏ i, B i (f i)) * Matrix.det (fun i j => C (group i) (f i) j) := by
    rw [det_finite_row_sum group (fun i (d : Fin N) => B i d)
      (fun a (d : Fin N) j => C a d j)]
    symm
    apply Finset.sum_subset (Finset.filter_subset _ _)
    intro f _ hf
    have hn : ¬ Function.Injective (fun i => (group i, (f i : ℕ))) := by
      simpa [good] using hf
    obtain ⟨i, j, hij, hne⟩ := Function.not_injective_iff.mp hn
    have hg : group i = group j := congrArg Prod.fst hij
    have hd : (f i : ℕ) = (f j : ℕ) := congrArg Prod.snd hij
    have hz : Matrix.det (fun r c => C (group r) (f r) c) = 0 := by
      apply Matrix.det_zero_of_row_eq hne
      funext c
      simp only [hg, hd]
    simp [hz]
  have hterm (f : ι → Fin N) :
      ‖(∏ i, B i (f i)) * Matrix.det (fun i j => C (group i) (f i) j)‖ ≤
        Q * (s * s) ^ (∑ i, (f i : ℕ)) := by
    have hbp : (∏ i, ‖B i (f i)‖) ≤ ∏ i, L i * (s * s) ^ (f i : ℕ) :=
      Finset.prod_le_prod₀ (fun i _ => norm_nonneg _) (fun i _ => hB i (f i))
    have hcp := norm_det_le_factorial_mul_pow
      (fun i j => C (group i) (f i) j) hD (fun i j => hC _ _ _)
    rw [norm_mul, norm_prod]
    calc
      _ ≤ (∏ i, L i * (s * s) ^ (f i : ℕ)) *
          ((Fintype.card ι).factorial * D ^ Fintype.card ι) :=
        mul_le_mul hbp hcp (norm_nonneg _) (Finset.prod_nonneg fun i _ =>
          mul_nonneg (hL i) (pow_nonneg (mul_self_nonneg s) _))
      _ = _ := by
        rw [Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum]
        dsimp [Q]
        ring
  rw [hexpand]
  calc
    _ ≤ ∑ f ∈ good,
        ‖(∏ i, B i (f i)) * Matrix.det (fun i j => C (group i) (f i) j)‖ :=
      norm_sum_le _ _
    _ ≤ ∑ f ∈ good, Q * (s * s) ^ (∑ i, (f i : ℕ)) :=
      Finset.sum_le_sum (fun f _ => hterm f)
    _ = Q * ∑ f ∈ good, (s * s) ^ (∑ i, (f i : ℕ)) := by rw [Finset.mul_sum]
    _ ≤ Q * (s ^ (∑ a, (Collision.multiplicity Finset.univ group a).choose 2) *
        ((1 - s)⁻¹) ^ Fintype.card ι) :=
      mul_le_mul_of_nonneg_left (Collision.collision_geometric_sum_le group hs0 hs1 N) hQ
    _ = _ := by dsimp [Q]; ring

end PiExponent.FiniteDeterminantCollision

end OAI
end Source0864

-- Source: OAI/NumberTheory/PiExponent/Analysis/CollisionLimit.lean
section Source0865
/-
Modification notice for the LogTwo project.
Derived from openai/math (Apache-2.0), revision adc7f1241b42e322a6451854ab7e4b4c146bf78a.
Original source: lean/OAI/NumberTheory/PiExponent/Analysis/CollisionLimit.lean
Changes: Convert module/import declarations to the Lean 4.34 public module format.
See ../THIRD_PARTY_NOTICES.txt for provenance and the recorded changes.
-/

namespace OAI

open scoped BigOperators Topology
open Filter

namespace PiExponent.Collision

theorem norm_det_le_of_entrywise_limit {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A : ℕ → Matrix ι ι ℂ) (T : Matrix ι ι ℂ) {B : ℝ}
    (hlim : ∀ i j, Tendsto (fun N => A N i j) atTop (𝓝 (T i j)))
    (hbound : ∀ N, ‖(A N).det‖ ≤ B) : ‖T.det‖ ≤ B := by
  have hmatrix : Tendsto A atTop (𝓝 T) := by
    apply tendsto_pi_nhds.mpr
    intro i
    exact tendsto_pi_nhds.mpr (hlim i)
  have hdet : Tendsto (fun N => (A N).det) atTop (𝓝 T.det) :=
    (continuous_id.matrix_det.tendsto T).comp hmatrix
  exact le_of_tendsto' hdet.norm hbound

theorem norm_det_le_of_entrywise_hasSum {ι : Type*} [Fintype ι] [DecidableEq ι]
    (C : ι → ℕ → ι → ℂ) (T : Matrix ι ι ℂ) {B : ℝ}
    (hsum : ∀ i j, HasSum (fun d => C i d j) (T i j))
    (hbound : ∀ N, ‖Matrix.det (fun i j => ∑ d ∈ Finset.range N, C i d j)‖ ≤ B) :
    ‖T.det‖ ≤ B := by
  exact norm_det_le_of_entrywise_limit
    (fun N i j => ∑ d ∈ Finset.range N, C i d j) T
    (fun i j => (hsum i j).tendsto_sum_nat) hbound

theorem norm_det_le_of_tested_series_hasSum
    {ι κ : Type*} [Fintype ι] [DecidableEq ι]
    (group : ι → κ) (coeff : κ → ℕ → ι → ℂ) (test : ι → ℕ → ℂ)
    (T : Matrix ι ι ℂ) {B : ℝ}
    (hsum : ∀ i j, HasSum (fun d => test i d * coeff (group i) d j) (T i j))
    (hbound : ∀ N,
      ‖Matrix.det (fun i j => ∑ d ∈ Finset.range N, test i d * coeff (group i) d j)‖ ≤ B) :
    ‖T.det‖ ≤ B := by
  exact norm_det_le_of_entrywise_hasSum
    (fun i d j => test i d * coeff (group i) d j) T hsum hbound

theorem infinite_collision_bound
    {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
    (group : ι → κ) (B : ι → ℕ → ℂ) (C : κ → ℕ → ι → ℂ)
    (D s : ℝ) (L : ι → ℝ) (hD : 0 ≤ D) (hs0 : 0 ≤ s) (hs1 : s < 1)
    (hL : ∀ i, 0 ≤ L i)
    (hC : ∀ a d j, ‖C a d j‖ ≤ D)
    (hB : ∀ i d, ‖B i d‖ ≤ L i * (s * s) ^ d)
    (T : Matrix ι ι ℂ)
    (hsum : ∀ i j, HasSum (fun d => B i d * C (group i) d j) (T i j)) :
    ‖T.det‖ ≤
      ((Fintype.card ι).factorial * D ^ Fintype.card ι * (∏ i, L i)) *
        s ^ (∑ a, (multiplicity Finset.univ group a).choose 2) *
          ((1 - s)⁻¹) ^ Fintype.card ι := by
  apply norm_det_le_of_tested_series_hasSum group C B T hsum
  intro N
  have hmatrix : (fun i j => ∑ d ∈ Finset.range N, B i d * C (group i) d j) =
      (fun i j => ∑ d : Fin N, B i d * C (group i) d j) := by
    funext i j
    exact (Fin.sum_univ_eq_sum_range (fun d : ℕ => B i d * C (group i) d j) N).symm
  rw [hmatrix]
  exact FiniteDeterminantCollision.finite_collision_bound group B C D s L hD hs0 hs1
    hL hC hB N

end PiExponent.Collision

end OAI
end Source0865

-- Source: OAI/NumberTheory/PiExponent/Analysis/AnalyticDeterminantCollision.lean
section Source0866
/-
Modification notice for the LogTwo project.
Derived from openai/math (Apache-2.0), revision adc7f1241b42e322a6451854ab7e4b4c146bf78a.
Original source: lean/OAI/NumberTheory/PiExponent/Analysis/AnalyticDeterminantCollision.lean
Changes: Convert module/import declarations to the Lean 4.34 public module format.
See ../THIRD_PARTY_NOTICES.txt for provenance and the recorded changes.
-/

namespace OAI

open scoped BigOperators

namespace PiExponent.AnalyticCollision

theorem translated_row_determinant_bound
    {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
    (group : ι → κ) (f : κ → ι → ℂ → ℂ)
    (center : ι → ℂ) (ell : ι → ℕ)
    (R : NNReal) (hR : 0 < R) (D s : ℝ) (hD : 0 ≤ D)
    (hs0 : 0 ≤ s) (hs1 : s < 1) (hss : s * s = 1 / 2)
    (hf : ∀ a j, Differentiable ℂ (f a j))
    (hfD : ∀ a j z, z ∈ Metric.sphere (0 : ℂ) (R : ℝ) → ‖f a j z‖ ≤ D)
    (hc : ∀ i, ‖center i‖ + 3 / 4 ≤ (R : ℝ) / 2) :
    ‖Matrix.det (fun i j => rowTest (ell i)
        (fun t => f (group i) j (center i + Complex.log (1 + t))))‖ ≤
      ((Fintype.card ι).factorial * D ^ Fintype.card ι * (∏ i, (2 : ℝ) ^ ell i)) *
        s ^ (∑ a, (Collision.multiplicity Finset.univ group a).choose 2) *
          ((1 - s)⁻¹) ^ Fintype.card ι := by
  let B : ι → ℕ → ℂ := fun i d => rowTest (ell i)
    (fun t => ((center i + Complex.log (1 + t)) / (R : ℂ)) ^ d)
  let C : κ → ℕ → ι → ℂ := fun a d j => normalizedTaylorCoeff (f a j) R d
  apply Collision.infinite_collision_bound group B C D s (fun i => (2 : ℝ) ^ ell i)
    hD hs0 hs1 (fun _ => by positivity)
  · intro a d j
    exact norm_normalizedTaylorCoeff_le (by exact_mod_cast hR) (hfD a j) d
  · intro i d
    dsimp [B]
    rw [hss]
    exact norm_rowTest_shifted_power_le (by exact_mod_cast hR) (hc i) (ell i) d
  · intro i j
    exact hasSum_translated_row (hf (group i) j) hR hD (hfD (group i) j) (hc i) (ell i)

theorem translated_row_determinant_bound_sum_order
    {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
    (group : ι → κ) (f : κ → ι → ℂ → ℂ)
    (center : ι → ℂ) (ell : ι → ℕ)
    (R : NNReal) (hR : 0 < R) (D s : ℝ) (hD : 0 ≤ D)
    (hs0 : 0 ≤ s) (hs1 : s < 1) (hss : s * s = 1 / 2)
    (hf : ∀ a j, Differentiable ℂ (f a j))
    (hfD : ∀ a j z, z ∈ Metric.sphere (0 : ℂ) (R : ℝ) → ‖f a j z‖ ≤ D)
    (hc : ∀ i, ‖center i‖ + 3 / 4 ≤ (R : ℝ) / 2) :
    ‖Matrix.det (fun i j => rowTest (ell i)
        (fun t => f (group i) j (center i + Complex.log (1 + t))))‖ ≤
      ((Fintype.card ι).factorial * D ^ Fintype.card ι * (2 : ℝ) ^ (∑ i, ell i)) *
        s ^ (∑ a, (Collision.multiplicity Finset.univ group a).choose 2) *
          ((1 - s)⁻¹) ^ Fintype.card ι := by
  simpa only [Finset.prod_pow_eq_pow_sum] using
    translated_row_determinant_bound group f center ell R hR D s hD hs0 hs1 hss hf hfD hc

theorem translated_row_determinant_exp_bound
    {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
    (group : ι → κ) (f : κ → ι → ℂ → ℂ)
    (center : ι → ℂ) (ell : ι → ℕ)
    (R : NNReal) (hR : 0 < R) {H A v : ℝ} (hH : 0 < H)
    (hf : ∀ a j, Differentiable ℂ (f a j))
    (hfD : ∀ a j z, z ∈ Metric.sphere (0 : ℂ) (R : ℝ) →
      ‖f a j z‖ ≤ Real.exp (H * A))
    (hc : ∀ i, ‖center i‖ + 3 / 4 ≤ (R : ℝ) / 2)
    (hell : ((∑ i, ell i : ℕ) : ℝ) ≤ (Fintype.card ι : ℝ) * H / v) :
    ‖Matrix.det (fun i j => rowTest (ell i)
        (fun t => f (group i) j (center i + Complex.log (1 + t))))‖ ≤
      Real.exp (-(Real.log 2 / 4) *
        (∑ a, (Collision.multiplicity Finset.univ group a : ℝ) ^ 2) +
        (Fintype.card ι : ℝ) * H *
          (A + Real.log 2 / v + Collision.collisionRemainder (Fintype.card ι) H)) := by
  have hfinite := translated_row_determinant_bound_sum_order group f center ell R hR
    (Real.exp (H * A)) Collision.collisionRatio (Real.exp_pos _).le
    Collision.collisionRatio_pos.le Collision.collisionRatio_lt_one
    Collision.collisionRatio_mul_self hf hfD hc
  exact hfinite.trans (Collision.collision_factor_le_exp_normalized (Fintype.card ι)
    (∑ a, (Collision.multiplicity Finset.univ group a).choose 2) (∑ i, ell i)
    hH hell (Collision.twice_collision_count_eq group))

end PiExponent.AnalyticCollision

end OAI
end Source0866

-- Source: OAI/NumberTheory/PiExponent/Polynomials/SimplexLog.lean
section Source0867
-- Modified in this edition: unused plain lemmas removed; see reduction.json.
/-
Modification notice for the LogTwo project.
Derived from openai/math (Apache-2.0), revision adc7f1241b42e322a6451854ab7e4b4c146bf78a.
Original source: lean/OAI/NumberTheory/PiExponent/Polynomials/SimplexLog.lean
Changes: Convert module/import declarations to the Lean 4.34 public module format.
See ../THIRD_PARTY_NOTICES.txt for provenance and the recorded changes.
-/

namespace OAI

open Filter Topology
open scoped BigOperators

namespace PiExponent

theorem tendsto_log_div_of_normalized_pow {f : ℝ → ℝ} {d : ℕ} {L : ℝ}
    (hf : Tendsto (fun H : ℝ => f H / H ^ d) atTop (𝓝 L)) (hL : 0 < L) :
    Tendsto (fun H : ℝ => Real.log (f H) / H) atTop (𝓝 0) := by
  have hlog : Tendsto (fun H : ℝ => Real.log (f H / H ^ d)) atTop (𝓝 (Real.log L)) :=
    (Real.continuousAt_log hL.ne').tendsto.comp hf
  have hslow : Tendsto (fun H : ℝ => Real.log H / H) atTop (𝓝 0) :=
    Real.isLittleO_log_id_atTop.tendsto_div_nhds_zero
  have h := (hlog.div_atTop tendsto_id).add (hslow.const_mul (d : ℝ))
  simp only [mul_zero, add_zero] at h
  apply h.congr'
  filter_upwards [eventually_gt_atTop (0 : ℝ),
    hf.eventually (eventually_ne_nhds hL.ne')] with H hH hn
  have hfne : f H ≠ 0 := by
    intro hz
    apply hn
    simp [hz]
  rw [Real.log_div hfne (pow_ne_zero _ hH.ne'), Real.log_pow]
  simp only [id_eq]
  ring

theorem tendsto_log_add_div_of_normalized_pow {f : ℝ → ℝ} {d : ℕ} {L : ℝ}
    (hf : Tendsto (fun H : ℝ => f H / H ^ d) atTop (𝓝 L)) (hL : 0 < L) (C : ℝ) :
    Tendsto (fun H : ℝ => (Real.log (f H) + C) / H) atTop (𝓝 0) := by
  have h := (tendsto_log_div_of_normalized_pow hf hL).add
    (tendsto_id.const_div_atTop C)
  simpa only [add_zero, add_div, id_eq] using h

end PiExponent

end OAI
end Source0867

-- Source: OAI/NumberTheory/PiExponent/Analysis/Collision.lean
section Source0868
-- Modified in this edition: unused plain lemmas removed; see reduction.json.
/-
Modification notice for the LogTwo project.
Derived from openai/math (Apache-2.0), revision adc7f1241b42e322a6451854ab7e4b4c146bf78a.
Original source: lean/OAI/NumberTheory/PiExponent/Analysis/Collision.lean
Changes: Convert module/import declarations to the Lean 4.34 public module format.
See ../THIRD_PARTY_NOTICES.txt for provenance and the recorded changes.
-/

namespace OAI

open scoped BigOperators Topology
open Filter

namespace PiExponent

noncomputable def holomorphicError (K : ℕ) (w0 v0 wstar : ℝ) : ℝ :=
  100 * K / w0 + Real.log 2 / v0 + Real.log (200 * K) / wstar

theorem tendsto_collisionRemainder_of_normalized_pow {M : ℝ → ℕ} {d : ℕ} {L : ℝ}
    (hM : Tendsto (fun H : ℝ => (M H : ℝ) / H ^ d) atTop (𝓝 L)) (hL : 0 < L) :
    Tendsto (fun H => Collision.collisionRemainder (M H) H) atTop (𝓝 0) := by
  convert tendsto_log_add_div_of_normalized_pow hM hL
    (Real.log 2 / 4 - Real.log (1 - Collision.collisionRatio)) using 1
  funext H
  unfold Collision.collisionRemainder
  congr 1
  ring

end PiExponent

end OAI
end Source0868

-- Source: OAI/NumberTheory/PiExponent/Analysis/CollisionOccupancy.lean
section Source0869
-- Modified in this edition: unused plain lemmas removed; see reduction.json.
/-
Modification notice for the LogTwo project.
Derived from openai/math (Apache-2.0), revision adc7f1241b42e322a6451854ab7e4b4c146bf78a.
Original source: lean/OAI/NumberTheory/PiExponent/Analysis/CollisionOccupancy.lean
Changes: Convert module/import declarations to the Lean 4.34 public module format.
See ../THIRD_PARTY_NOTICES.txt for provenance and the recorded changes.
-/

namespace OAI

namespace PiExponent.Collision

open scoped BigOperators

variable {G : Type*}

theorem sum_sq_le_card_mul_sum_sq (S : Finset G) (n : G → ℝ) :
    (∑ a ∈ S, n a) ^ 2 ≤ (S.card : ℝ) * ∑ a ∈ S, n a ^ 2 := by
  simpa using Finset.sum_mul_sq_le_sq_mul_sq S (fun _ : G => (1 : ℝ)) n

theorem sum_sq_le_card_mul_total_sq (S U : Finset G) (hSU : S ⊆ U)
    (n : G → ℝ) :
    (∑ a ∈ S, n a) ^ 2 ≤ (S.card : ℝ) * ∑ a ∈ U, n a ^ 2 := by
  apply (sum_sq_le_card_mul_sum_sq S n).trans
  apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg _)
  exact Finset.sum_le_sum_of_subset_of_nonneg hSU (fun a _ _ => sq_nonneg (n a))

variable [Fintype G]

theorem sum_sq_le_card_mul_univ_sq (S : Finset G) (n : G → ℝ) :
    (∑ a ∈ S, n a) ^ 2 ≤ (S.card : ℝ) * ∑ a, n a ^ 2 := by
  exact sum_sq_le_card_mul_total_sq S Finset.univ (Finset.subset_univ S) n

end PiExponent.Collision

end OAI
end Source0869

-- Source: OAI/NumberTheory/PiExponent/Analysis/DeterminantAnalyticBound.lean
section Source0870
/-
Modification notice for the LogTwo project.
Derived from openai/math (Apache-2.0), revision adc7f1241b42e322a6451854ab7e4b4c146bf78a.
Original source: lean/OAI/NumberTheory/PiExponent/Analysis/DeterminantAnalyticBound.lean
Changes: Convert module/import declarations to the Lean 4.34 public module format.
See ../THIRD_PARTY_NOTICES.txt for provenance and the recorded changes.
-/

namespace OAI

open scoped BigOperators

namespace PiExponent.DeterminantAnalyticBound

theorem two_alternative_exponent
    {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
    (group : ι → κ) (weight : κ → ℝ)
    {H A eta nu c N bbar E : ℝ}
    (hH : 0 < H) (hA : 0 ≤ A) (heta : 0 ≤ eta) (hnu : 0 ≤ nu)
    (hc : 0 ≤ c) (hN : 0 < N) (hw : ∀ a, 0 ≤ weight a)
    (hbeta : (Fintype.card ι : ℝ) * H * bbar ≤ ∑ i, weight (group i))
    (hcap : (((Finset.univ : Finset κ).filter (fun a => weight a ≤ A * H)).card : ℝ) ≤ N) :
    -nu * ((∑ i, weight (group i)) - (Fintype.card ι : ℝ) * H * bbar) -
      c * (∑ a, (Collision.multiplicity Finset.univ group a : ℝ) ^ 2) +
      (Fintype.card ι : ℝ) * H * E ≤
    (Fintype.card ι : ℝ) * H *
      (E + max (-c * eta ^ 2 * (Fintype.card ι : ℝ) / (H * N))
        (-nu * (A * (1 - eta) - bbar))) := by
  classical
  let S := (Finset.univ : Finset κ).filter (fun a => weight a ≤ A * H)
  let M : ℝ := Fintype.card ι
  let Z : ℝ := ∑ a, (Collision.multiplicity Finset.univ group a : ℝ) ^ 2
  have hM : 0 ≤ M := Nat.cast_nonneg _
  have hZ : 0 ≤ Z := Finset.sum_nonneg fun _ _ => sq_nonneg _
  have hmass : (∑ a ∈ S, (Collision.multiplicity Finset.univ group a : ℝ)) =
      (((Finset.univ : Finset ι).filter (fun i => weight (group i) ≤ A * H)).card : ℝ) := by
    have hn := Collision.sum_multiplicity_eq_card_filter (Finset.univ : Finset ι) S group
    have hn' : (∑ a ∈ S, Collision.multiplicity Finset.univ group a) =
        ((Finset.univ : Finset ι).filter (fun i => weight (group i) ≤ A * H)).card := by
      simpa only [S, Finset.mem_filter, Finset.mem_univ, true_and] using hn
    exact_mod_cast hn'
  by_cases hlow : eta * M ≤ ∑ a ∈ S, (Collision.multiplicity Finset.univ group a : ℝ)
  · have hsq : eta ^ 2 * M ^ 2 ≤ N * Z := by
      calc
        _ = (eta * M) ^ 2 := by ring
        _ ≤ (∑ a ∈ S, (Collision.multiplicity Finset.univ group a : ℝ)) ^ 2 :=
          pow_le_pow_left₀ (mul_nonneg heta hM) hlow 2
        _ ≤ (S.card : ℝ) * Z := Collision.sum_sq_le_card_mul_univ_sq S _
        _ ≤ N * Z := mul_le_mul_of_nonneg_right hcap hZ
    have hcollision : -c * Z ≤ M * H * (-c * eta ^ 2 * M / (H * N)) := by
      have hz : eta ^ 2 * M ^ 2 / N ≤ Z := (div_le_iff₀ hN).mpr (by nlinarith [hsq])
      have hh := mul_le_mul_of_nonneg_left hz hc
      have he : M * H * (-c * eta ^ 2 * M / (H * N)) = -c * (eta ^ 2 * M ^ 2 / N) := by
        field_simp
      rw [he]
      nlinarith [hh]
    have hscalar : -nu * ((∑ i, weight (group i)) - M * H * bbar) ≤ 0 := by
      have hp := mul_nonneg hnu (sub_nonneg.mpr hbeta)
      nlinarith [hp]
    have hmax := mul_le_mul_of_nonneg_left
      (le_max_left (-c * eta ^ 2 * M / (H * N)) (-nu * (A * (1 - eta) - bbar)))
      (mul_nonneg hM hH.le)
    change -nu * ((∑ i, weight (group i)) - M * H * bbar) - c * Z + M * H * E ≤ _
    change _ ≤ M * H * (E + max (-c * eta ^ 2 * M / (H * N)) (-nu * (A * (1 - eta) - bbar)))
    nlinarith
  · have hl : (((Finset.univ : Finset ι).filter (fun i => weight (group i) ≤ A * H)).card : ℝ) ≤
        eta * (Finset.univ : Finset ι).card := by
      rw [← hmass]
      exact (le_of_not_ge hlow)
    have hwgt := Collision.sum_weight_ge_of_low_count_le (Finset.univ : Finset ι)
      (fun i => weight (group i)) (mul_nonneg hA hH.le) (fun i _ => hw _) hl
    have hwgt' : A * H * (1 - eta) * M ≤ ∑ i, weight (group i) := by
      simpa only [Finset.card_univ, M] using hwgt
    have hmul := mul_le_mul_of_nonneg_left hwgt' hnu
    have hscalar : -nu * ((∑ i, weight (group i)) - M * H * bbar) ≤
        M * H * (-nu * (A * (1 - eta) - bbar)) := by nlinarith [hmul]
    have hcollision : -c * Z ≤ 0 := by nlinarith [mul_nonneg hc hZ]
    have hmax := mul_le_mul_of_nonneg_left
      (le_max_right (-c * eta ^ 2 * M / (H * N)) (-nu * (A * (1 - eta) - bbar)))
      (mul_nonneg hM hH.le)
    change -nu * ((∑ i, weight (group i)) - M * H * bbar) - c * Z + M * H * E ≤ _
    change _ ≤ M * H * (E + max (-c * eta ^ 2 * M / (H * N)) (-nu * (A * (1 - eta) - bbar)))
    nlinarith

theorem translated_summand_bound
    {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
    (group : ι → κ) (weight : κ → ℝ) (scalar determinant : ℂ)
    {H A eta nu c N bbar Etr Ehol rho : ℝ}
    (hH : 0 < H) (hA : 0 ≤ A) (heta : 0 ≤ eta) (hnu : 0 ≤ nu)
    (hc : 0 ≤ c) (hN : 0 < N) (hw : ∀ a, 0 ≤ weight a)
    (hbeta : (Fintype.card ι : ℝ) * H * bbar ≤ ∑ i, weight (group i))
    (hcap : (((Finset.univ : Finset κ).filter (fun a => weight a ≤ A * H)).card : ℝ) ≤ N)
    (hscalar : ‖scalar‖ ≤ Real.exp
      (-nu * ((∑ i, weight (group i)) - (Fintype.card ι : ℝ) * H * bbar) +
        (Fintype.card ι : ℝ) * H * Etr))
    (hdet : ‖determinant‖ ≤ Real.exp
      (-c * (∑ a, (Collision.multiplicity Finset.univ group a : ℝ) ^ 2) +
        (Fintype.card ι : ℝ) * H * (Ehol + rho))) :
    ‖scalar * determinant‖ ≤ Real.exp ((Fintype.card ι : ℝ) * H *
      (Etr + Ehol + rho + max (-c * eta ^ 2 * (Fintype.card ι : ℝ) / (H * N))
        (-nu * (A * (1 - eta) - bbar)))) := by
  rw [norm_mul]
  apply (mul_le_mul hscalar hdet (norm_nonneg _) (Real.exp_pos _).le).trans
  rw [← Real.exp_add]
  apply Real.exp_le_exp.mpr
  have h := two_alternative_exponent group weight hH hA heta hnu hc hN hw hbeta hcap
    (E := Etr + Ehol + rho)
  nlinarith [h]

theorem log_norm_sum_le {Ω : Type*} [Fintype Ω]
    (term : Ω → ℂ) (delta : ℂ) {M : ℕ} {H Q E : ℝ}
    (hM : 0 < M) (hH : 0 < H) (hQ : 0 < Q)
    (hcard : (Fintype.card Ω : ℝ) ≤ Q ^ M)
    (hexpansion : delta = ∑ x, term x) (hne : delta ≠ 0)
    (hterm : ∀ x, ‖term x‖ ≤ Real.exp ((M : ℝ) * H * E)) :
    Real.log ‖delta‖ / ((M : ℝ) * H) ≤ E + Real.log Q / H := by
  have hbound : ‖delta‖ ≤ Real.exp ((M : ℝ) * H * (E + Real.log Q / H)) := by
    calc
      _ = ‖∑ x, term x‖ := by rw [hexpansion]
      _ ≤ ∑ x, ‖term x‖ := norm_sum_le _ _
      _ ≤ ∑ _x : Ω, Real.exp ((M : ℝ) * H * E) := Finset.sum_le_sum fun x _ => hterm x
      _ = (Fintype.card Ω : ℝ) * Real.exp ((M : ℝ) * H * E) := by simp
      _ ≤ Q ^ M * Real.exp ((M : ℝ) * H * E) :=
        mul_le_mul_of_nonneg_right hcard (Real.exp_pos _).le
      _ = _ := by
        have he : Q ^ M = Real.exp ((M : ℝ) * Real.log Q) := by
          rw [Real.exp_nat_mul, Real.exp_log hQ]
        rw [he, ← Real.exp_add]
        congr 1
        field_simp
        ring
  have hlog := Real.log_le_log (norm_pos_iff.mpr hne) hbound
  rw [Real.log_exp] at hlog
  apply (div_le_iff₀ (mul_pos (by exact_mod_cast hM) hH)).mpr
  nlinarith [hlog]

end PiExponent.DeterminantAnalyticBound

end OAI
end Source0870

-- Source: OAI/NumberTheory/PiExponent/Approximation/ApproximationCenters.lean
section Source0871
-- Modified in this edition: unused plain lemmas removed; see reduction.json.
/-
Modification notice for the LogTwo project.
Derived from openai/math (Apache-2.0), revision adc7f1241b42e322a6451854ab7e4b4c146bf78a.
Original source: lean/OAI/NumberTheory/PiExponent/Approximation/ApproximationCenters.lean
Changes: Convert module/import declarations to the Lean 4.34 public module format.
See ../THIRD_PARTY_NOTICES.txt for provenance and the recorded changes.
-/

namespace OAI

namespace PiExponent

noncomputable def approximatePeriod (p : ℤ) (q : ℕ) : ℂ :=
  2 * Complex.I * (p : ℂ) / (q : ℂ)

noncomputable def logarithmicPeriod : ℂ := 2 * (Real.pi : ℂ) * Complex.I

theorem ceil_log_bounds {q : ℕ} (hq : 1 ≤ q) :
    0 ≤ (⌈Real.log q⌉₊ : ℝ) - Real.log q ∧
      (⌈Real.log q⌉₊ : ℝ) - Real.log q < 1 := by
  have hlog : 0 ≤ Real.log (q : ℝ) := Real.log_nonneg (by exact_mod_cast hq)
  constructor
  · exact sub_nonneg.mpr (Nat.le_ceil _)
  · have := Nat.ceil_lt_add_one hlog
    linarith

theorem rpow_neg_le_exp_ceil_log (nu : ℝ) {q : ℕ} (hnu : 0 ≤ nu) (hq : 1 ≤ q) :
    (q : ℝ) ^ (-nu) ≤
      Real.exp nu * Real.exp (-nu * (⌈Real.log q⌉₊ : ℝ)) := by
  have hqpos : (0 : ℝ) < q := by exact_mod_cast (by omega : 0 < q)
  rw [Real.rpow_def_of_pos hqpos, ← Real.exp_add]
  apply Real.exp_le_exp.mpr
  have hw := (ceil_log_bounds hq).2
  nlinarith

end PiExponent

end OAI
end Source0871

-- Source: OAI/NumberTheory/PiExponent/Approximation/MatrixTranslationBounds.lean
section Source0872
-- Modified in this edition: unused plain lemmas removed; see reduction.json.
/-
Modification notice for the LogTwo project.
Derived from openai/math (Apache-2.0), revision adc7f1241b42e322a6451854ab7e4b4c146bf78a.
Original source: lean/OAI/NumberTheory/PiExponent/Approximation/MatrixTranslationBounds.lean
Changes: Convert module/import declarations to the Lean 4.34 public module format.
See ../THIRD_PARTY_NOTICES.txt for provenance and the recorded changes.
-/

namespace OAI

namespace PiExponent.MatrixTranslationBounds

open scoped BigOperators
open RowTranslation

noncomputable def weight {σ : Type*} [Fintype σ] (w : σ → ℝ) (a : σ → ℕ) : ℝ :=
  ∑ i, w i * a i

theorem error_power_product_le {σ : Type*} [Fintype σ]
    (ε : σ → ℂ) (e : σ → ℕ) (w : σ → ℝ) (C ν : ℝ)
    (hε : ∀ i, ‖ε i‖ ≤ Real.exp (C - ν * w i)) :
    (∏ i, ‖ε i‖ ^ e i) ≤ Real.exp (∑ i, (e i : ℝ) * (C - ν * w i)) := by
  rw [Real.exp_sum]
  apply Finset.prod_le_prod₀ (fun i hi => by positivity)
  intro i hi
  rw [Real.exp_nat_mul]
  exact pow_le_pow_left₀ (norm_nonneg _) (hε i) _

theorem norm_rowScalar_exp_basic {σ : Type*} [Fintype σ] [DecidableEq σ]
    (ε : σ → ℂ) (T : σ → ℕ) (β a : σ →₀ ℕ)
    (d : ∀ i, Fin (a i - β i + 1)) (k : ℕ) (w : σ → ℝ) (C ν : ℝ)
    (hT : ∀ i, 1 ≤ T i) (hε : ∀ i, ‖ε i‖ ≤ Real.exp (C - ν * w i)) :
    ‖rowScalar ε (fun i => tail (T i) (PowerSeries.log ℂ)) β a d k‖ ≤
      Real.exp ((∑ i, a i : ℕ) * Real.log 4 +
        (∑ i, ((a i - β i - d i : ℕ) : ℝ) * (C - ν * w i)) +
          (k : ℝ) * Real.log 2) := by
  have hτ := LogTailAnalytic.norm_coeff_prod_formal_logTail_le Finset.univ T
    (fun i => (d i : ℕ)) (fun i hi => hT i) k
  apply (norm_rowScalar_le ε _ β a d k ((2 : ℝ) ^ k) hτ).trans
  calc
    _ ≤ (4 : ℝ) ^ (∑ i, a i) *
        Real.exp (∑ i, ((a i - β i - d i : ℕ) : ℝ) * (C - ν * w i)) * (2 : ℝ) ^ k :=
      mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left (error_power_product_le ε _ w C ν hε) (by positivity))
        (by positivity)
    _ = _ := by
      rw [Real.exp_add, Real.exp_add, Real.exp_nat_mul, Real.exp_nat_mul,
        Real.exp_log (by norm_num : (0 : ℝ) < 4), Real.exp_log (by norm_num : (0 : ℝ) < 2)]

theorem sum_exponents_le {σ : Type*} [Fintype σ] (w : σ → ℝ) (a : σ → ℕ)
    (H ws : ℝ) (hws : 0 < ws) (hw : ∀ i, ws ≤ w i) (ha : weight w a ≤ H) :
    ((∑ i, a i : ℕ) : ℝ) ≤ H / ws := by
  apply (le_div_iff₀ hws).2
  calc
    ((∑ i, a i : ℕ) : ℝ) * ws = ∑ i, ws * (a i : ℝ) := by
      simp only [Nat.cast_sum, Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro i hi
      ring_nf
    _ ≤ weight w a := Finset.sum_le_sum (fun i hi =>
      mul_le_mul_of_nonneg_right (hw i) (Nat.cast_nonneg _))
    _ ≤ H := ha

theorem residual_exponent_identity {σ : Type*} [Fintype σ]
    (a β : σ →₀ ℕ) (d : ∀ i, Fin (a i - β i + 1)) (w : σ → ℝ) (C ν : ℝ) :
    (∑ i, ((a i - β i - d i : ℕ) : ℝ) * (C - ν * w i)) =
      C * ((∑ i, (a i - β i - d i) : ℕ) : ℝ) -
        ν * weight w (fun i => a i - β i) + ν * weight w (fun i => (d i : ℕ)) := by
  simp only [weight, Nat.cast_sum, Finset.mul_sum, ← Finset.sum_sub_distrib,
    ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i hi
  rw [Nat.cast_sub (Nat.le_of_lt_succ (d i).isLt)]
  ring_nf

theorem norm_rowScalar_exp_weighted {σ : Type*} [Fintype σ] [DecidableEq σ]
    (ε : σ → ℂ) (T : σ → ℕ) (β a : σ →₀ ℕ)
    (d : ∀ i, Fin (a i - β i + 1)) (k : ℕ) (w : σ → ℝ)
    (C ν H ws v F : ℝ) (hC : 0 ≤ C) (hν : 0 ≤ ν)
    (hws : 0 < ws) (hv : 0 < v) (hF : 0 < F)
    (hw : ∀ i, ws ≤ w i) (ha : weight w (fun i => a i) ≤ H)
    (hk : (k : ℝ) ≤ H / v) (hT : ∀ i, 1 ≤ T i)
    (hTw : ∀ i, F * w i ≤ v * T i)
    (hε : ∀ i, ‖ε i‖ ≤ Real.exp (C - ν * w i)) :
    ‖rowScalar ε (fun i => tail (T i) (PowerSeries.log ℂ)) β a d k‖ ≤
      Real.exp (-ν * weight w (fun i => a i - β i) +
        H * (ν / F + Real.log 2 / v + (Real.log 4 + C) / ws)) := by
  by_cases hz : PowerSeries.coeff k (∏ i, tail (T i) (PowerSeries.log ℂ) ^ (d i : ℕ)) = 0
  · simp [rowScalar, hz, Real.exp_nonneg]
  have hbudget : weight w (fun i => (d i : ℕ)) ≤ H / F := by
    have hb := tail_weight_budget Finset.univ T (fun i => (d i : ℕ))
      (fun _ => PowerSeries.log ℂ) k w v F hv.le hF (fun i hi => hTw i) hz
    have hkv : v * (k : ℝ) ≤ H := by nlinarith [(le_div_iff₀ hv).mp hk]
    have hb' : weight w (fun i => (d i : ℕ)) ≤ v * k / F := by
      simpa [weight, mul_comm] using hb
    exact hb'.trans (div_le_div_of_nonneg_right hkv hF.le)
  have hsize := sum_exponents_le w (fun i => a i) H ws hws hw ha
  have hcount : ((∑ i, (a i - β i - d i) : ℕ) : ℝ) ≤ ((∑ i, a i : ℕ) : ℝ) := by
    exact_mod_cast Finset.sum_le_sum (fun i hi => (Nat.sub_le _ _).trans (Nat.sub_le _ _))
  have hlog2 : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
  have hlog4 : 0 ≤ Real.log 4 := Real.log_nonneg (by norm_num)
  apply (norm_rowScalar_exp_basic ε T β a d k w C ν hT hε).trans
  apply Real.exp_le_exp.mpr
  rw [residual_exponent_identity]
  calc
    _ ≤ (Real.log 4 + C) * ((∑ i, a i : ℕ) : ℝ) -
        ν * weight w (fun i => a i - β i) + ν * (H / F) + (H / v) * Real.log 2 := by
      nlinarith [mul_le_mul_of_nonneg_left hcount hC,
        mul_le_mul_of_nonneg_left hbudget hν,
        mul_le_mul_of_nonneg_right hk hlog2]
    _ ≤ (Real.log 4 + C) * (H / ws) -
        ν * weight w (fun i => a i - β i) + ν * (H / F) + (H / v) * Real.log 2 := by
      nlinarith [mul_le_mul_of_nonneg_left hsize (add_nonneg hlog4 hC)]
    _ = _ := by ring_nf

theorem weight_sub_le_weight_tsub {σ : Type*} [Fintype σ]
    (w : σ → ℝ) (a β : σ → ℕ) (hw : ∀ i, 0 ≤ w i) :
    weight w a - weight w β ≤ weight w (fun i => a i - β i) := by
  simp only [weight, ← Finset.sum_sub_distrib]
  apply Finset.sum_le_sum
  intro i hi
  rw [← mul_sub]
  apply mul_le_mul_of_nonneg_left _ (hw i)
  by_cases h : β i ≤ a i
  · rw [Nat.cast_sub h]
  · have hle : a i ≤ β i := by omega
    rw [Nat.sub_eq_zero_of_le hle, Nat.cast_zero]
    exact sub_nonpos.mpr (by exact_mod_cast hle)

theorem norm_rowScalar_exp_weight_difference {σ : Type*} [Fintype σ] [DecidableEq σ]
    (ε : σ → ℂ) (T : σ → ℕ) (β a : σ →₀ ℕ)
    (d : ∀ i, Fin (a i - β i + 1)) (k : ℕ) (w : σ → ℝ)
    (C ν H ws v F : ℝ) (hC : 0 ≤ C) (hν : 0 ≤ ν)
    (hws : 0 < ws) (hv : 0 < v) (hF : 0 < F)
    (hw : ∀ i, ws ≤ w i) (ha : weight w (fun i => a i) ≤ H)
    (hk : (k : ℝ) ≤ H / v) (hT : ∀ i, 1 ≤ T i)
    (hTw : ∀ i, F * w i ≤ v * T i)
    (hε : ∀ i, ‖ε i‖ ≤ Real.exp (C - ν * w i)) :
    ‖rowScalar ε (fun i => tail (T i) (PowerSeries.log ℂ)) β a d k‖ ≤
      Real.exp (-ν * (weight w (fun i => a i) - weight w (fun i => β i)) +
        H * (ν / F + Real.log 2 / v + (Real.log 4 + C) / ws)) := by
  apply (norm_rowScalar_exp_weighted ε T β a d k w C ν H ws v F
    hC hν hws hv hF hw ha hk hT hTw hε).trans
  apply Real.exp_le_exp.mpr
  have h := weight_sub_le_weight_tsub w (fun i => a i) (fun i => β i)
    (fun i => hws.le.trans (hw i))
  nlinarith [mul_le_mul_of_nonneg_left h hν]

noncomputable def truncationOrder (F v w : ℝ) : ℕ := ⌈F * w / v⌉₊

end PiExponent.MatrixTranslationBounds

end OAI
end Source0872

-- Source: LogTwo/Analysis/AnalyticSummand.lean
section Source0873
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
end Source0873

-- Source: LogTwo/Analysis/TranslationScalar.lean
section Source0874
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
end Source0874

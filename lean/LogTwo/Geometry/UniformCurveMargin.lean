/-
Modification notice for the LogTwo project.
Adapted from openai/math (Apache-2.0), revision adc7f1241b42e322a6451854ab7e4b4c146bf78a.
Changes: Adapt the three-case curve argument to the verified varying-center degree inequality.
See ../../../THIRD_PARTY_NOTICES.txt for provenance and the recorded changes.
-/

module

public import LogTwo.Geometry.IntegralCurveDegree
public import LogTwo.Geometry.CurveMarginLemmas

@[expose] public section

/-! A single positive margin for every integral curve on the actual blowup.
The exponent and margin are chosen before the curve. Contracted curves and
curves missing the affine chart are handled geometrically; the remaining
case uses the proved varying-center contact bound and degree transfer. -/
namespace LogTwo.Geometry.MatrixBlowup
open OAI PiExponent AlgebraicGeometry CategoryTheory
open PiExponentSeshadri.Geometry NumericalAmpleness
open LogTwo.Interpolation LogTwo.Parameters LogTwo.Arithmetic
noncomputable section

variable {m K : ℕ} (w : Weights m) (y : Fin K → ℂ)
variable (hy0 : ∀ j, y j ≠ 0) (a : Fin K → Fin m → ℂ) (T : Fin m → ℕ)

def interpolationBundle : LineBundle (space w y a T) :=
  (A w y a T).tensor (J w y a T)

def degreeMargin : ℝ :=
  CurveMarginLemmas.marginCoefficient (ampleExponent w y hy0 a T) (curveSigma w.theta m)

theorem degreeMargin_pos : 0 < degreeMargin w y hy0 a T := by
  apply CurveMarginLemmas.marginCoefficient_pos (ampleExponent_gt_one w y hy0 a T)
  exact_mod_cast curveSigma_pos w.theta_pos w.theta_lt_one m

theorem contracted_curve_margin (C : IntegralCurve (space w y a T))
    (x : MatrixCompactification.space w)
    (hc : Set.range (C.embedding ≫ projection w y a T) ⊆ {x}) :
    degreeMargin w y hy0 a T * (curveDegree (structureMap w y a T) (H w y hy0 a T) C : ℝ) ≤
      (curveDegree (structureMap w y a T) (interpolationBundle w y a T) C : ℝ) := by
  exact CurveMarginLemmas.margin_of_contracted (structureMap w y a T)
    (projection w y a T) (hyperplane w) (J w y a T)
    (ampleExponent w y hy0 a T) (ampleExponent_gt_one w y hy0 a T)
    (H_ample w y hy0 a T) (curveSigma w.theta m)
    (by exact_mod_cast curveSigma_pos w.theta_pos w.theta_lt_one m) C x hc

theorem outside_chart_curve_margin (C : IntegralCurve (space w y a T))
    (hm : ∀ c : C.scheme,
      (C.embedding ≫ projection w y a T) c ∉ (MatrixCompactification.affineChart w).opensRange) :
    degreeMargin w y hy0 a T * (curveDegree (structureMap w y a T) (H w y hy0 a T) C : ℝ) ≤
      (curveDegree (structureMap w y a T) (interpolationBundle w y a T) C : ℝ) := by
  exact CurveMarginLemmas.margin_of_image_outside_chart (structureMap w y a T)
    (MatrixCompactification.centerIdeal w y a T) (projection w y a T)
    (A w y a T) (J w y a T) (exceptionalInclusion w y a T) (exceptional_presents w y a T)
    (ampleExponent w y hy0 a T) (ampleExponent_gt_one w y hy0 a T)
    (H_ample w y hy0 a T) (curveSigma w.theta m)
    (by exact_mod_cast curveSigma_pos w.theta_pos w.theta_lt_one m) C
    (MatrixCompactification.affineChart w).opensRange
    (MatrixCompactification.centerIdeal_support_subset_chart w y a T) hm

/-- All three curve cases, with the same positive coefficient independent of C. -/
theorem chosenWeights_uniform_curve_margin
    (n : ℕ) (hn : 1 ≤ n) (m : ℕ) (q : ℕ → ℕ) (hq : ∀ i, 2 ≤ q i)
    (hgrowth : ∀ i, i < m →
      denominatorSeparationFactor n m (chosenComparisonConstant n m) *
        (∏ j : Fin i, (ceilLogWeight (q j) : ℝ)) < (ceilLogWeight (q i) : ℝ)) :
    let w := chosenWeights n hn m (fun i => q i) (fun i => hq i)
    ∀ (y : Fin w.K → ℂ) (hy0 : ∀ j, y j ≠ 0), Function.Injective y →
      ∀ (a : Fin w.K → Fin m → ℂ) (F : ℚ), 1 / w.theta < F →
      ∀ C : IntegralCurve (space w y a (truncationOrders w F)),
      degreeMargin w y hy0 a (truncationOrders w F) *
          (curveDegree (structureMap w y a (truncationOrders w F))
            (H w y hy0 a (truncationOrders w F)) C : ℝ) ≤
        (curveDegree (structureMap w y a (truncationOrders w F))
          (interpolationBundle w y a (truncationOrders w F)) C : ℝ) := by
  classical
  dsimp only
  intro y hy0 hy a F hF C
  let w := chosenWeights n hn m (fun i => q i) (fun i => hq i)
  by_cases hc : ∃ x : MatrixCompactification.space w,
      Set.range (C.embedding ≫ projection w y a (truncationOrders w F)) ⊆ {x}
  · obtain ⟨x, hx⟩ := hc
    exact contracted_curve_margin w y hy0 a (truncationOrders w F) C x hx
  · by_cases hm : ∃ c : C.scheme,
        (C.embedding ≫ projection w y a (truncationOrders w F)) c ∈
          (MatrixCompactification.affineChart w).opensRange
    · exact CurveMarginLemmas.margin_of_nonnegative_degree
        (structureMap w y a (truncationOrders w F))
        (A w y a (truncationOrders w F)) (J w y a (truncationOrders w F))
        (ampleExponent w y hy0 a (truncationOrders w F))
        (ampleExponent_gt_one w y hy0 a (truncationOrders w F))
        (H_ample w y hy0 a (truncationOrders w F)) (curveSigma w.theta m)
        (by exact_mod_cast curveSigma_pos w.theta_pos w.theta_lt_one m) C
        (chosenWeights_integralCurve_degree_nonnegative n hn m q hq hgrowth
          y hy0 hy a F hF C hc hm)
    · exact outside_chart_curve_margin w y hy0 a (truncationOrders w F) C
        (fun c hh => hm ⟨c, hh⟩)

/-- Existential packaging fixes epsilon before quantifying over all curves. -/
theorem logTwo_exists_positive_uniform_curve_margin
    (n : ℕ) (hn : 1 ≤ n) (m : ℕ) (q : ℕ → ℕ) (hq : ∀ i, 2 ≤ q i)
    (hgrowth : ∀ i, i < m →
      denominatorSeparationFactor n m (chosenComparisonConstant n m) *
        (∏ j : Fin i, (ceilLogWeight (q j) : ℝ)) < (ceilLogWeight (q i) : ℝ))
    (r : Fin m → ℚ) :
    let w := chosenWeights n hn m (fun i => q i) (fun i => hq i)
    let y : Fin w.K → ℂ := fun j => 2^j.val
    let a : Fin w.K → Fin m → ℂ := fun j i => (j.val : ℂ) * (r i : ℂ)
    ∀ (F : ℚ), 1 / w.theta < F →
      ∃ ε : ℝ, 0 < ε ∧ ∀ C : IntegralCurve (space w y a (truncationOrders w F)),
        ε * (curveDegree (structureMap w y a (truncationOrders w F))
          (H w y (fun j => pow_ne_zero j.val (by norm_num)) a (truncationOrders w F)) C : ℝ) ≤
          (curveDegree (structureMap w y a (truncationOrders w F))
            (interpolationBundle w y a (truncationOrders w F)) C : ℝ) := by
  dsimp only
  intro F hF
  let w := chosenWeights n hn m (fun i => q i) (fun i => hq i)
  let y : Fin w.K → ℂ := fun j => 2^j.val
  let a : Fin w.K → Fin m → ℂ := fun j i => (j.val : ℂ) * (r i : ℂ)
  have hy0 : ∀ j, y j ≠ 0 := fun j => pow_ne_zero j.val (by norm_num)
  exact ⟨degreeMargin w y hy0 a (truncationOrders w F),
    degreeMargin_pos w y hy0 a (truncationOrders w F),
    chosenWeights_uniform_curve_margin n hn m q hq hgrowth y hy0
      (complex_centerY_injective.comp Fin.val_injective) a F hF⟩

end
end LogTwo.Geometry.MatrixBlowup

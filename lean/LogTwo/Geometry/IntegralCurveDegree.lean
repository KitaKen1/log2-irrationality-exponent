module

public import LogTwo.Geometry.BlowupPolarization
public import LogTwo.Geometry.BlowupCurveModel
public import LogTwo.Geometry.CurveDegreeMargin
public import OAI.NumberTheory.PiExponent.Geometry.CurveNormalizedDegreeTransfer

@[expose] public section

/-! Actual curve degrees on the blowup. The noncontracted curve meeting the
affine chart supplies its own function field, generating coordinates and
normalization; none is postulated. Contracted and outside-chart curves and
the ampleness of A tensor J are separate later steps. -/
namespace LogTwo.Geometry.MatrixBlowup
open OAI PiExponent AlgebraicGeometry CategoryTheory
open PiExponentSeshadri.Geometry NumericalAmpleness
open LogTwo.Interpolation LogTwo.Parameters LogTwo.Arithmetic
noncomputable section

/-- Finite birational normalization preserves the actual curve degree. -/
theorem curveDegree_eq_modelDegree {m K : ℕ} (w : Weights m) (y : Fin K → ℂ)
    (hy0 : ∀ j, y j ≠ 0) (a : Fin K → Fin m → ℂ) (T : Fin m → ℕ)
    (C : IntegralCurve (space w y a T)) (r : CurveModel.ModelData w y a T C)
    (L : LineBundle (space w y a T)) :
    letI := r.field
    letI := r.algebra
    letI := r.parameterFinite
    (curveDegree (structureMap w y a T) L C : ℝ) =
      normalizationDegree r.parameter r.parameter_transcendental
        (r.normalization ≫ C.embedding) L := by
  let := r.field
  let := r.algebra
  let := r.parameterFinite
  let := r.normalizationFinite
  let := r.chartIso
  unfold normalizationDegree
  exact congrArg (fun d : ℤ => (d : ℝ)) <|
    CurveNormalizedDegreeTransfer.curveDegree_eq_normalized
    (structureMap w y a T) (H w y hy0 a T) (H_ample w y hy0 a T) C
    r.parameter r.parameter_transcendental r.normalization r.normalization_over
    r.chart r.chart_nonempty L

/-- The degree inequality on every noncontracted integral curve meeting the
actual affine chart, with its normalization data constructed internally. -/
theorem chosenWeights_integralCurve_degree_nonnegative
    (n : ℕ) (hn : 1 ≤ n) (m : ℕ) (q : ℕ → ℕ) (hq : ∀ i, 2 ≤ q i)
    (hgrowth : ∀ i, i < m →
      denominatorSeparationFactor n m (chosenComparisonConstant n m) *
        (∏ j : Fin i, (ceilLogWeight (q j) : ℝ)) < (ceilLogWeight (q i) : ℝ)) :
    let w := chosenWeights n hn m (fun i => q i) (fun i => hq i)
    ∀ (y : Fin w.K → ℂ), (∀ j, y j ≠ 0) → Function.Injective y →
      ∀ (a : Fin w.K → Fin m → ℂ) (F : ℚ), 1 / w.theta < F →
      ∀ (C : IntegralCurve (space w y a (truncationOrders w F))),
      (¬ ∃ x : MatrixCompactification.space w,
        Set.range (C.embedding ≫ projection w y a (truncationOrders w F)) ⊆ {x}) →
      (∃ p : C.scheme, (C.embedding ≫ projection w y a (truncationOrders w F)) p ∈
        (MatrixCompactification.affineChart w).opensRange) →
      0 ≤ (curveDegree (structureMap w y a (truncationOrders w F))
          (A w y a (truncationOrders w F)) C : ℝ) +
        (1 + (curveSigma w.theta m : ℝ)) *
          (curveDegree (structureMap w y a (truncationOrders w F))
            (J w y a (truncationOrders w F)) C : ℝ) := by
  dsimp only
  intro y hy0 hy a F hF C hnc hm
  let w := chosenWeights n hn m (fun i => q i) (fun i => hq i)
  obtain ⟨r⟩ := CurveModel.existsModelData w y a (truncationOrders w F) C hnc hm
  let := r.field
  let := r.algebra
  let := r.essFiniteType
  let := r.parameterFinite
  rw [curveDegree_eq_modelDegree w y hy0 a _ C r (A w y a _),
    curveDegree_eq_modelDegree w y hy0 a _ C r (J w y a _)]
  exact chosenWeights_degree_nonnegative r.parameter r.parameter_transcendental
    n hn m q hq hgrowth r.coordinates r.coordinates_generate r.trdeg_one y hy0 hy a F hF
    (r.normalization ≫ C.embedding) (by simpa only [Category.assoc] using r.generic_coordinates)

/-- Precisely the original matrix centers (2^j,j*r_i). -/
theorem logTwo_integralCurve_degree_nonnegative
    (n : ℕ) (hn : 1 ≤ n) (m : ℕ) (q : ℕ → ℕ) (hq : ∀ i, 2 ≤ q i)
    (hgrowth : ∀ i, i < m →
      denominatorSeparationFactor n m (chosenComparisonConstant n m) *
        (∏ j : Fin i, (ceilLogWeight (q j) : ℝ)) < (ceilLogWeight (q i) : ℝ))
    (r : Fin m → ℚ) :
    let w := chosenWeights n hn m (fun i => q i) (fun i => hq i)
    let y : Fin w.K → ℂ := fun j => 2^j.val
    let a : Fin w.K → Fin m → ℂ := fun j i => (j.val : ℂ) * (r i : ℂ)
    ∀ (F : ℚ), 1 / w.theta < F →
      ∀ (C : IntegralCurve (space w y a (truncationOrders w F))),
      (¬ ∃ x : MatrixCompactification.space w,
        Set.range (C.embedding ≫ projection w y a (truncationOrders w F)) ⊆ {x}) →
      (∃ p : C.scheme, (C.embedding ≫ projection w y a (truncationOrders w F)) p ∈
        (MatrixCompactification.affineChart w).opensRange) →
      0 ≤ (curveDegree (structureMap w y a (truncationOrders w F))
          (A w y a (truncationOrders w F)) C : ℝ) +
        (1 + (curveSigma w.theta m : ℝ)) *
          (curveDegree (structureMap w y a (truncationOrders w F))
            (J w y a (truncationOrders w F)) C : ℝ) := by
  dsimp only
  exact chosenWeights_integralCurve_degree_nonnegative n hn m q hq hgrowth
    (fun j => 2^j.val) (fun j => pow_ne_zero j.val (by norm_num))
    (complex_centerY_injective.comp Fin.val_injective) (fun j i => (j.val : ℂ) * (r i : ℂ))

end
end LogTwo.Geometry.MatrixBlowup

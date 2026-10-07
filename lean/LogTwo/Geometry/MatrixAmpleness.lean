module

public import LogTwo.Geometry.UniformCurveMargin
public import OAI.NumberTheory.PiExponent.Ampleness.NumericalAmplenessTheorem

@[expose] public section

/-! Ampleness of the actual interpolation bundle A tensor J follows from
the constructed auxiliary ample bundle and the proved uniform curve margin.
Bounded-degree jet surjectivity and the determinant estimate remain later steps. -/
namespace LogTwo.Geometry.MatrixBlowup
open OAI PiExponent AlgebraicGeometry CategoryTheory
open PiExponentSeshadri.Geometry NumericalAmpleness
open LogTwo.Interpolation LogTwo.Parameters LogTwo.Arithmetic
noncomputable section

theorem chosenWeights_interpolationBundle_ample
    (n : ℕ) (hn : 1 ≤ n) (m : ℕ) (q : ℕ → ℕ) (hq : ∀ i, 2 ≤ q i)
    (hgrowth : ∀ i, i < m →
      denominatorSeparationFactor n m (chosenComparisonConstant n m) *
        (∏ j : Fin i, (ceilLogWeight (q j) : ℝ)) < (ceilLogWeight (q i) : ℝ)) :
    let w := chosenWeights n hn m (fun i => q i) (fun i => hq i)
    ∀ (y : Fin w.K → ℂ), (∀ j, y j ≠ 0) → Function.Injective y →
      ∀ (a : Fin w.K → Fin m → ℂ) (F : ℚ), 1 / w.theta < F →
      (interpolationBundle w y a (truncationOrders w F)).IsAmple := by
  dsimp only
  intro y hy0 hy a F hF
  let w := chosenWeights n hn m (fun i => q i) (fun i => hq i)
  exact isAmple_of_uniform_curve_margin (structureMap w y a (truncationOrders w F))
    (H w y hy0 a (truncationOrders w F)) (interpolationBundle w y a (truncationOrders w F))
    (H_ample w y hy0 a (truncationOrders w F)) (degreeMargin w y hy0 a (truncationOrders w F))
    (degreeMargin_pos w y hy0 a (truncationOrders w F))
    (chosenWeights_uniform_curve_margin n hn m q hq hgrowth y hy0 hy a F hF)

/-- The target line bundle at exactly the matrix centers (2^j,j*r_i) is ample. -/
theorem logTwo_interpolationBundle_ample
    (n : ℕ) (hn : 1 ≤ n) (m : ℕ) (q : ℕ → ℕ) (hq : ∀ i, 2 ≤ q i)
    (hgrowth : ∀ i, i < m →
      denominatorSeparationFactor n m (chosenComparisonConstant n m) *
        (∏ j : Fin i, (ceilLogWeight (q j) : ℝ)) < (ceilLogWeight (q i) : ℝ))
    (r : Fin m → ℚ) :
    let w := chosenWeights n hn m (fun i => q i) (fun i => hq i)
    let y : Fin w.K → ℂ := fun j => 2^j.val
    let a : Fin w.K → Fin m → ℂ := fun j i => (j.val : ℂ) * (r i : ℂ)
    ∀ (F : ℚ), 1 / w.theta < F →
      (interpolationBundle w y a (truncationOrders w F)).IsAmple := by
  dsimp only
  exact chosenWeights_interpolationBundle_ample n hn m q hq hgrowth
    (fun j => 2^j.val) (fun j => pow_ne_zero j.val (by norm_num))
    (complex_centerY_injective.comp Fin.val_injective) (fun j i => (j.val : ℂ) * (r i : ℂ))

end
end LogTwo.Geometry.MatrixBlowup

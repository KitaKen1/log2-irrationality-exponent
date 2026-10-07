/-
Modification notice for the LogTwo project.
Adapted from openai/math (Apache-2.0), revision adc7f1241b42e322a6451854ab7e4b4c146bf78a.
Changes: Adapt the blowup/affine-jet strategy to the varying Y-centers.
See ../../../THIRD_PARTY_NOTICES.txt for provenance and the recorded changes.
-/

module

public import LogTwo.Geometry.MatrixAmpleness
public import OAI.NumberTheory.PiExponent.Ampleness.BlowupJetSurjectivityComplete

@[expose] public section

/-! Eventual sheaf-jet surjectivity on the actual weighted compactification.
The ampleness input is discharged by the preceding uniform curve argument.
The polynomial degree bound and the determinant estimate are separate steps. -/
namespace LogTwo.Geometry.MatrixBlowup
open OAI PiExponent AlgebraicGeometry CategoryTheory
open PiExponentSeshadri.Geometry BlowupJetSurjectivity
open LogTwo.Interpolation LogTwo.Parameters LogTwo.Arithmetic
noncomputable section

/-- Tensor commutativity matches the proved bundle to the generic blowup API. -/
theorem blowupBundle_ample_of_interpolationBundle
    {m K : ℕ} (w : Weights m) (y : Fin K → ℂ)
    (a : Fin K → Fin m → ℂ) (T : Fin m → ℕ)
    (h : (interpolationBundle w y a T).IsAmple) :
    (blowupBundle (MatrixCompactification.centerIdeal w y a T) (hyperplane w)).IsAmple := by
  exact AmpleIso.isAmple_of_sheaf_iso (interpolationBundle w y a T)
    (blowupBundle (MatrixCompactification.centerIdeal w y a T) (hyperplane w))
    (moduleTensorComm (A w y a T).sheaf (J w y a T).sheaf) h

theorem chosenWeights_eventual_jetRestriction_surjective
    (n : ℕ) (hn : 1 ≤ n) (m : ℕ) (q : ℕ → ℕ) (hq : ∀ i, 2 ≤ q i)
    (hgrowth : ∀ i, i < m →
      denominatorSeparationFactor n m (chosenComparisonConstant n m) *
        (∏ j : Fin i, (ceilLogWeight (q j) : ℝ)) < (ceilLogWeight (q i) : ℝ)) :
    let w := chosenWeights n hn m (fun i => q i) (fun i => hq i)
    ∀ (y : Fin w.K → ℂ), (∀ j, y j ≠ 0) → Function.Injective y →
      ∀ (a : Fin w.K → Fin m → ℂ) (F : ℚ), 1 / w.theta < F →
      ∃ N, ∀ k, N ≤ k → Function.Surjective
        (jetRestriction (MatrixCompactification.centerIdeal w y a (truncationOrders w F))
          (hyperplane w) k) := by
  dsimp only
  intro y hy0 hy a F hF
  let w := chosenWeights n hn m (fun i => q i) (fun i => hq i)
  exact eventual_blowup_jetRestriction_surjective (MatrixCompactification.structureMap w)
    (MatrixCompactification.centerIdeal w y a (truncationOrders w F)) (hyperplane w)
    (blowupBundle_ample_of_interpolationBundle w y a _
      (chosenWeights_interpolationBundle_ample n hn m q hq hgrowth y hy0 hy a F hF))

/-- The centers are exactly (2^j,j*r_i), without any surjectivity hypothesis. -/
theorem logTwo_eventual_jetRestriction_surjective
    (n : ℕ) (hn : 1 ≤ n) (m : ℕ) (q : ℕ → ℕ) (hq : ∀ i, 2 ≤ q i)
    (hgrowth : ∀ i, i < m →
      denominatorSeparationFactor n m (chosenComparisonConstant n m) *
        (∏ j : Fin i, (ceilLogWeight (q j) : ℝ)) < (ceilLogWeight (q i) : ℝ))
    (r : Fin m → ℚ) :
    let w := chosenWeights n hn m (fun i => q i) (fun i => hq i)
    ∀ (F : ℚ), 1 / w.theta < F →
      ∃ N, ∀ k, N ≤ k → Function.Surjective
        (jetRestriction (MatrixCompactification.logTwoIdeal w r (truncationOrders w F))
          (hyperplane w) k) := by
  dsimp only
  exact chosenWeights_eventual_jetRestriction_surjective n hn m q hq hgrowth
    (fun j => 2^j.val) (fun j => pow_ne_zero j.val (by norm_num))
    (complex_centerY_injective.comp Fin.val_injective) (fun j i => (j.val : ℂ) * (r i : ℂ))

end
end LogTwo.Geometry.MatrixBlowup

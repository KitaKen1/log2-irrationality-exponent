/-
Modification notice for the LogTwo project.
Adapted from openai/math (Apache-2.0), revision adc7f1241b42e322a6451854ab7e4b4c146bf78a.
Changes: Adapt the section-polynomial strategy to the varying Y-centers.
See ../../../THIRD_PARTY_NOTICES.txt for provenance and the recorded changes.
-/

module

public import LogTwo.Geometry.MatrixJetSurjectivity
public import LogTwo.Geometry.WeightedAffineFrame
public import LogTwo.Geometry.WeightedGlobalSectionBound
public import LogTwo.Geometry.JetPacketSurjectivity
public import LogTwo.Geometry.InterpolationBridge

@[expose] public section

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

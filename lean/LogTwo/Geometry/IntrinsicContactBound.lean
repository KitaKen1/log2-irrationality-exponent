/-
Modification notice for the LogTwo project.
Adapted from openai/math (Apache-2.0), revision adc7f1241b42e322a6451854ab7e4b4c146bf78a.
Changes: Adapt the nonconstant-coordinate argument and discharge the local field hypotheses.
See ../../../THIRD_PARTY_NOTICES.txt for provenance and the recorded changes.
-/

module

public import LogTwo.Geometry.GlobalContactBound
public import LogTwo.Geometry.Centers
public import OAI.NumberTheory.PiExponent.Geometry.PlaceLocalRing

@[expose] public section

/-! Intrinsic function-field formulation for varying nonzero Y-centers.
The residue and finite-extension inputs follow from finite type and trdeg = 1.
This is a curve inequality, not a proof of interpolation surjectivity. -/
namespace LogTwo.Geometry
open OAI PiExponent CurveValuationCenter PlaceValuationRing
open LogTwo.Interpolation LogTwo.Parameters LogTwo.Arithmetic
noncomputable section
variable {E : Type*} [Field E] [Algebra ℂ E]

theorem nonconstant_coordinates_of_trdeg_one {d : ℕ} (z : Fin d → E)
    (hgen : IntermediateField.adjoin ℂ (Set.range z) = ⊤)
    (htrdeg : Algebra.trdeg ℂ E = 1) : ∃ i, Transcendental ℂ (z i) := by
  let : Algebra.Transcendental ℂ E := trdeg_ne_zero_iff.mp (by rw [htrdeg]; exact one_ne_zero)
  exact CurveCenters.exists_transcendental_coordinate z hgen
    (Algebra.Transcendental.transcendental (R := ℂ) (A := E))

variable [Algebra.EssFiniteType ℂ E]

/-- The actual chosen matrix weights satisfy the full contact inequality on a
curve function field. No normal-comparison or local-residue hypothesis remains. -/
theorem chosenWeights_intrinsic_contact_bound
    (n : ℕ) (hn : 1 ≤ n) (m : ℕ) (q : ℕ → ℕ) (hq : ∀ i, 2 ≤ q i)
    (hgrowth : ∀ i, i < m →
      denominatorSeparationFactor n m (chosenComparisonConstant n m)*
        (∏ j : Fin i, (ceilLogWeight (q j) : ℝ)) < (ceilLogWeight (q i) : ℝ))
    (z : Fin (m+1) → E)
    (hgen : IntermediateField.adjoin ℂ (Set.range z) = ⊤)
    (htrdeg : Algebra.trdeg ℂ E = 1) :
    let hres := PlaceLocalRing.residue_integral htrdeg.le
    let hfinite := CurveParameterFinite.finite_over_every_parameter ℂ E htrdeg
    let hz := nonconstant_coordinates_of_trdeg_one z hgen htrdeg
    let w := chosenWeights n hn m (fun i => q i) (fun i => hq i)
    let hK : 0 < w.K := centerCount_pos (shape n hn).one_lt_c.le m
    ∀ (y : Fin w.K → ℂ) (hy : ∀ j, y j ≠ 0), Function.Injective y →
      ∀ (c : Fin w.K → Fin m → ℂ),
      (1+(curveSigma w.theta m : ℝ))*∑ p ∈ ContactFamilyAt.places hfinite z y c hz,
        (ContactFamilyAt.contact hres hfinite z y hy c hz hK (jetWeight w) p : ℝ) ≤
          CurveContactSum.weightedDegree hfinite z (rationalColumnWeight w) := by
  exact chosenWeights_contact_bound (PlaceLocalRing.residue_integral htrdeg.le)
    (CurveParameterFinite.finite_over_every_parameter ℂ E htrdeg)
    n hn m q hq hgrowth z (nonconstant_coordinates_of_trdeg_one z hgen htrdeg)

/-- Specialization to precisely the matrix centers (2^j, j*r_i). -/
theorem logTwo_intrinsic_contact_bound
    (n : ℕ) (hn : 1 ≤ n) (m : ℕ) (q : ℕ → ℕ) (hq : ∀ i, 2 ≤ q i)
    (hgrowth : ∀ i, i < m →
      denominatorSeparationFactor n m (chosenComparisonConstant n m)*
        (∏ j : Fin i, (ceilLogWeight (q j) : ℝ)) < (ceilLogWeight (q i) : ℝ))
    (z : Fin (m+1) → E)
    (hgen : IntermediateField.adjoin ℂ (Set.range z) = ⊤)
    (htrdeg : Algebra.trdeg ℂ E = 1) (r : Fin m → ℚ) :
    let hres := PlaceLocalRing.residue_integral htrdeg.le
    let hfinite := CurveParameterFinite.finite_over_every_parameter ℂ E htrdeg
    let hz := nonconstant_coordinates_of_trdeg_one z hgen htrdeg
    let w := chosenWeights n hn m (fun i => q i) (fun i => hq i)
    let hK : 0 < w.K := centerCount_pos (shape n hn).one_lt_c.le m
    let y : Fin w.K → ℂ := fun j => 2^j.val
    let hy : ∀ j, y j ≠ 0 := fun j => pow_ne_zero j.val (by norm_num)
    let c : Fin w.K → Fin m → ℂ := fun j i => (j.val : ℂ)*(r i : ℂ)
    (1+(curveSigma w.theta m : ℝ))*∑ p ∈ ContactFamilyAt.places hfinite z y c hz,
      (ContactFamilyAt.contact hres hfinite z y hy c hz hK (jetWeight w) p : ℝ) ≤
        CurveContactSum.weightedDegree hfinite z (rationalColumnWeight w) := by
  dsimp only
  apply chosenWeights_intrinsic_contact_bound n hn m q hq hgrowth z hgen htrdeg
  exact complex_centerY_injective.comp Fin.val_injective

end
end LogTwo.Geometry

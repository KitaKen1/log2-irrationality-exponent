module

public import LogTwo.Geometry.ContactBound
public import LogTwo.Geometry.SeparationAssembly

@[expose] public section

/-! Specialize the conditional curve inequality to the actual arithmetic matrix
weights. Volume, contact margin, and product separation are discharged here.
This component exposes the normal comparison; GlobalContactBound supplies it. -/
namespace LogTwo.Geometry
open OAI PiExponent PiExponentApprox CurveValuationCenter PlaceValuationRing
open LogTwo.Interpolation LogTwo.Parameters LogTwo.Arithmetic
noncomputable section
variable {E : Type*} [Field E] [Algebra ℂ E]

theorem chosenWeights_contact_bound_of_comparison
    (hres : ∀ p : NormalizedPlace ℂ E,
      Algebra.IsIntegral ℂ (IsLocalRing.ResidueField (ring p)))
    (hfinite : ∀ f : E, Transcendental ℂ f →
      FiniteDimensional (IntermediateField.adjoin ℂ {f}) E)
    (n : ℕ) (hn : 1 ≤ n) (m : ℕ) (q : ℕ → ℕ) (hq : ∀ i, 2 ≤ q i)
    (M : ℝ) (hM : 0 < M)
    (hgrowth : ∀ i, i < m →
      denominatorSeparationFactor n m M*(∏ j : Fin i, (ceilLogWeight (q j) : ℝ)) <
        (ceilLogWeight (q i) : ℝ))
    (z : Fin (m+1) → E) (hz : ∃ i, Transcendental ℂ (z i)) :
    let w := chosenWeights n hn m (fun i => q i) (fun i => hq i)
    let hK : 0 < w.K := centerCount_pos (shape n hn).one_lt_c.le m
    ∀ (y : Fin w.K → ℂ) (hy : ∀ j, y j ≠ 0) (hinj : Function.Injective y)
      (c : Fin w.K → Fin m → ℂ),
      EventualKernelComparison z (columnWeight w) (fun i => (jetWeight w i : ℝ))
        M (curveSigma w.theta m) →
      (1+(curveSigma w.theta m : ℝ))*∑ p ∈ ContactFamilyAt.places hfinite z y c hz,
        (ContactFamilyAt.contact hres hfinite z y hy c hz hK (jetWeight w) p : ℝ) ≤
          CurveContactSum.weightedDegree hfinite z (rationalColumnWeight w) := by
  dsimp only
  intro y hy hinj c hcomp
  let w := chosenWeights n hn m (fun i => q i) (fun i => hq i)
  have hK : 0 < w.K := centerCount_pos (shape n hn).one_lt_c.le m
  have hm := chosenWeights_geometric_margins n hn m (fun i => q i) (fun i => hq i)
  have hratio : ∀ i : Fin m, rationalColumnWeight w i.succ = w.theta*jetWeight w i.succ := by
    intro i
    dsimp [rationalColumnWeight, jetWeight]
    field_simp [w.theta_pos.ne']
  have hsep : SeparatedProducts (fun i => (rationalColumnWeight w i : ℝ))
      (fun i => (jetWeight w i : ℝ)) M := by
    simpa only [cast_rationalColumnWeight] using
      chosenWeights_separatedProducts n hn m q hq M hM hgrowth
  have hc : EventualKernelComparison z (fun i => (rationalColumnWeight w i : ℝ))
      (fun i => (jetWeight w i : ℝ)) M (curveSigma w.theta m) := by
    simpa only [cast_rationalColumnWeight] using hcomp
  exact contact_bound_of_comparison hres hfinite z y hy c hz hK hinj
    (rationalColumnWeight w) (jetWeight w) (rationalColumnWeight_pos w) (jetWeight_pos w)
    w.theta w.theta_pos.le hratio (curveSigma w.theta m) hm.1
    (curveSigma_contact_margin w.theta_pos w.theta_lt_one m).le hm.2.2 M hsep hc

end
end LogTwo.Geometry

module

public import LogTwo.Geometry.NormalComparison
public import LogTwo.Geometry.ChosenContactBound

@[expose] public section

/-! Contact bounds with the normal comparison proved internally. The field and
residue hypotheses are retained explicitly; geometric interpolation is separate. -/
namespace LogTwo.Geometry
open OAI PiExponent PiExponentApprox CurveValuationCenter PlaceValuationRing
open LogTwo.Interpolation LogTwo.Parameters LogTwo.Arithmetic
noncomputable section
variable {E : Type*} [Field E] [Algebra ℂ E]

theorem contact_bound {m K : ℕ}
    (hres : ∀ p : NormalizedPlace ℂ E,
      Algebra.IsIntegral ℂ (IsLocalRing.ResidueField (ring p)))
    (hfinite : ∀ f : E, Transcendental ℂ f →
      FiniteDimensional (IntermediateField.adjoin ℂ {f}) E)
    (z : Fin (m+1) → E) (y : Fin K → ℂ) (hy : ∀ j, y j ≠ 0)
    (c : Fin K → Fin m → ℂ) (hz : ∃ i, Transcendental ℂ (z i)) (hK : 0 < K)
    (hinj : Function.Injective y)
    (w v : Fin (m+1) → ℚ) (hw : ∀ i, 0 < w i) (hv : ∀ i, 0 < v i)
    (theta : ℚ) (htheta : 0 ≤ theta)
    (hratio : ∀ i : Fin m, w i.succ = theta*v i.succ)
    (sigma : ℚ) (hsigma : 0 < sigma) (hmargin : (1+sigma)*theta ≤ 1)
    (hvol : (K : ℝ)*(1+3*(sigma : ℝ))^(m+1)*(∏ i, (w i : ℝ))/(∏ i, (v i : ℝ)) < 1)
    (hseparated : SeparatedProducts (fun i => (w i : ℝ)) (fun i => (v i : ℝ))
      (rigidityComparisonConstant m sigma)) :
    (1+(sigma : ℝ))*∑ p ∈ ContactFamilyAt.places hfinite z y c hz,
      (ContactFamilyAt.contact hres hfinite z y hy c hz hK v p : ℝ) ≤
        CurveContactSum.weightedDegree hfinite z w := by
  exact contact_bound_of_comparison hres hfinite z y hy c hz hK hinj w v hw hv
    theta htheta hratio sigma hsigma hmargin hvol _ hseparated
    (eventualKernelComparison z w hw (fun i => (v i : ℝ))
      (fun i => by exact_mod_cast hv i) sigma (by exact_mod_cast hsigma))

/-- This constant is fixed after n and m, before choosing any denominator. -/
def chosenComparisonConstant (n m : ℕ) : ℝ :=
  rigidityComparisonConstant m (curveSigma (theta (delta n)) m)

theorem chosenComparisonConstant_pos (n : ℕ) (hn : 1 ≤ n) (m : ℕ) :
    0 < chosenComparisonConstant n m := by
  apply rigidityComparisonConstant_pos
  exact_mod_cast curveSigma_pos (shape n hn).theta_pos
    ((shape n hn).theta_lt_a.trans ((shape n hn).a_lt_b.trans (shape n hn).b_lt_one)) m

/-- For the matrix weights, volume and normal comparison are no longer inputs.
The displayed prefix-growth condition can be supplied by denominator selection. -/
theorem chosenWeights_contact_bound
    (hres : ∀ p : NormalizedPlace ℂ E,
      Algebra.IsIntegral ℂ (IsLocalRing.ResidueField (ring p)))
    (hfinite : ∀ f : E, Transcendental ℂ f →
      FiniteDimensional (IntermediateField.adjoin ℂ {f}) E)
    (n : ℕ) (hn : 1 ≤ n) (m : ℕ) (q : ℕ → ℕ) (hq : ∀ i, 2 ≤ q i)
    (hgrowth : ∀ i, i < m →
      denominatorSeparationFactor n m (chosenComparisonConstant n m)*
        (∏ j : Fin i, (ceilLogWeight (q j) : ℝ)) < (ceilLogWeight (q i) : ℝ))
    (z : Fin (m+1) → E) (hz : ∃ i, Transcendental ℂ (z i)) :
    let w := chosenWeights n hn m (fun i => q i) (fun i => hq i)
    let hK : 0 < w.K := centerCount_pos (shape n hn).one_lt_c.le m
    ∀ (y : Fin w.K → ℂ) (hy : ∀ j, y j ≠ 0), Function.Injective y →
      ∀ (c : Fin w.K → Fin m → ℂ),
      (1+(curveSigma w.theta m : ℝ))*∑ p ∈ ContactFamilyAt.places hfinite z y c hz,
        (ContactFamilyAt.contact hres hfinite z y hy c hz hK (jetWeight w) p : ℝ) ≤
          CurveContactSum.weightedDegree hfinite z (rationalColumnWeight w) := by
  dsimp only
  intro y hy hinj c
  let w := chosenWeights n hn m (fun i => q i) (fun i => hq i)
  apply chosenWeights_contact_bound_of_comparison hres hfinite n hn m q hq
    (chosenComparisonConstant n m) (chosenComparisonConstant_pos n hn m) hgrowth z hz
    y hy hinj c
  have hs : (0 : ℝ) < (curveSigma w.theta m : ℝ) := by
    exact_mod_cast curveSigma_pos w.theta_pos w.theta_lt_one m
  simpa only [cast_rationalColumnWeight, chosenComparisonConstant, w, chosenWeights] using
    eventualKernelComparison z (rationalColumnWeight w) (rationalColumnWeight_pos w)
      (fun i => (jetWeight w i : ℝ)) (fun i => by exact_mod_cast jetWeight_pos w i)
      (curveSigma w.theta m) hs

end
end LogTwo.Geometry

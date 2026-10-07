module

public import LogTwo.Geometry.ContactFamilyAt
public import LogTwo.Geometry.GeometricParameters

@[expose] public section

/-! Assemble the actual finite contact family with the explicit geometric margins.
The separated-weight rigidity theorem, forcing constant Y, remains separate. -/
namespace LogTwo.Geometry.ContactFamilyAt
open OAI PiExponent PiExponentApprox
open CurveValuationCenter CurveCenters PlaceValuationRing
open Filter Topology
noncomputable section
variable {E : Type*} [Field E] [Algebra ℂ E] {m K : ℕ}
variable
    (hres : ∀ p : NormalizedPlace ℂ E,
      Algebra.IsIntegral ℂ (IsLocalRing.ResidueField (ring p)))
    (hfinite : ∀ f : E, Transcendental ℂ f →
      FiniteDimensional (IntermediateField.adjoin ℂ {f}) E)
    (z : Fin (m+1) → E) (y : Fin K → ℂ) (hy : ∀ j, y j ≠ 0)
    (c : Fin K → Fin m → ℂ) (hz : ∃ i, Transcendental ℂ (z i)) (hK : 0 < K)

/-- The complete contact family on a constant Y fiber obeys the theta bound. -/
theorem contact_sum_le_of_constantY (hinj : Function.Injective y)
    (w v : Fin (m+1) → ℚ) (hw : ∀ i, 0 < w i) (hv : ∀ i, 0 < v i)
    (theta : ℚ) (htheta : 0 ≤ theta)
    (hratio : ∀ i : Fin m, w i.succ = theta*v i.succ)
    (a : ℂ) (ha : z 0 = algebraMap ℂ E a) :
    (∑ p ∈ places hfinite z y c hz, (contact hres hfinite z y hy c hz hK v p : ℝ)) ≤
      (theta : ℝ)*CurveContactSum.weightedDegree hfinite z w := by
  let x := fun i : Fin m => z i.succ
  have hx : (Fin.cases (algebraMap ℂ E a) x : Fin (m+1) → E) = z := by
    funext i
    exact Fin.cases ha.symm (fun _ => rfl) i
  have hc : ∀ p ∈ places hfinite z y c hz,
      Centered (Fin.cases (algebraMap ℂ E a) x)
        (centerPoint (y (center hfinite z y c hz hK p)) (c (center hfinite z y c hz hK p))) p := by
    simpa only [hx] using centered hfinite z y c hz hK
  have hnc : ∀ j, ∃ i : Fin (m+1),
      (Fin.cases (algebraMap ℂ E a) x : Fin (m+1) → E) i ≠
        algebraMap ℂ E (centerPoint (y j) (c j) i) := by
    simpa only [hx] using fun j => nonconstant z (y j) (c j) hz
  have hb := constant_fiber_family_contact_sum_le hfinite a x y hinj hy c w v hw hv
    theta htheta hratio (places hfinite z y c hz) (center hfinite z y c hz hK)
    hc (fun p _ => hres p) hnc
    (fun p => (contact hres hfinite z y hy c hz hK v p : ℝ)) (by
      intro p hp
      let := hres p
      simpa only [hx] using congrArg (fun q : ℚ => (q : ℝ))
        (contact_eq hres hfinite z y hy c hz hK v p hp))
  simpa only [hx] using hb

theorem no_excess_of_constantY (hinj : Function.Injective y)
    (w v : Fin (m+1) → ℚ) (hw : ∀ i, 0 < w i) (hv : ∀ i, 0 < v i)
    (theta : ℚ) (htheta : 0 ≤ theta)
    (hratio : ∀ i : Fin m, w i.succ = theta*v i.succ)
    (sigma : ℚ) (hsigma : 0 ≤ sigma) (hmargin : (1+sigma)*theta ≤ 1)
    (a : ℂ) (ha : z 0 = algebraMap ℂ E a) :
    (1+(sigma : ℝ)) *
      (∑ p ∈ places hfinite z y c hz, (contact hres hfinite z y hy c hz hK v p : ℝ)) ≤
        CurveContactSum.weightedDegree hfinite z w := by
  have hb := contact_sum_le_of_constantY hres hfinite z y hy c hz hK hinj
    w v hw hv theta htheta hratio a ha
  have hsigR : (0 : ℝ) ≤ sigma := by exact_mod_cast hsigma
  calc
    _ ≤ (1+(sigma : ℝ))*((theta : ℝ)*CurveContactSum.weightedDegree hfinite z w) :=
      mul_le_mul_of_nonneg_left hb (by positivity)
    _ = ((1+(sigma : ℝ))*theta)*CurveContactSum.weightedDegree hfinite z w := by ring
    _ ≤ 1*CurveContactSum.weightedDegree hfinite z w :=
      mul_le_mul_of_nonneg_right (by exact_mod_cast hmargin)
        (CurveContactSum.weightedDegree_nonneg hfinite z w)
    _ = _ := one_mul _

end
end LogTwo.Geometry.ContactFamilyAt

namespace LogTwo.Geometry
open OAI PiExponent PiExponentApprox
open CurveValuationCenter PlaceValuationRing Filter Topology
noncomputable section
variable {E : Type*} [Field E] [Algebra ℂ E]

theorem weights_no_excess_of_constantY {m : ℕ}
    (hres : ∀ p : NormalizedPlace ℂ E,
      Algebra.IsIntegral ℂ (IsLocalRing.ResidueField (ring p)))
    (hfinite : ∀ f : E, Transcendental ℂ f →
      FiniteDimensional (IntermediateField.adjoin ℂ {f}) E)
    (w : LogTwo.Interpolation.Weights m) (hK : 0 < w.K)
    (z : Fin (m+1) → E) (hz : ∃ i, Transcendental ℂ (z i))
    (y : Fin w.K → ℂ) (hy : ∀ j, y j ≠ 0) (hinj : Function.Injective y)
    (c : Fin w.K → Fin m → ℂ) (a : ℂ) (ha : z 0 = algebraMap ℂ E a) :
    (1+(curveSigma w.theta m : ℝ)) *
      (∑ p ∈ ContactFamilyAt.places hfinite z y c hz,
        (ContactFamilyAt.contact hres hfinite z y hy c hz hK (jetWeight w) p : ℝ)) ≤
      CurveContactSum.weightedDegree hfinite z (rationalColumnWeight w) := by
  apply ContactFamilyAt.no_excess_of_constantY hres hfinite z y hy c hz hK hinj
    (rationalColumnWeight w) (jetWeight w) (rationalColumnWeight_pos w) (jetWeight_pos w)
    w.theta w.theta_pos.le ?_ (curveSigma w.theta m)
    (curveSigma_pos w.theta_pos w.theta_lt_one m).le
    (curveSigma_contact_margin w.theta_pos w.theta_lt_one m).le a ha
  intro i
  dsimp [rationalColumnWeight, jetWeight]
  field_simp [w.theta_pos.ne']

/-- The scalar geometric inputs are discharged for the actual arithmetic weights.
Only excess of the actual contact sum is hypothesized in this annihilator step. -/
theorem chosenWeights_annihilator_of_excess
    (hres : ∀ p : NormalizedPlace ℂ E,
      Algebra.IsIntegral ℂ (IsLocalRing.ResidueField (ring p)))
    (hfinite : ∀ f : E, Transcendental ℂ f →
      FiniteDimensional (IntermediateField.adjoin ℂ {f}) E)
    (n : ℕ) (hn : 1 ≤ n) (m : ℕ) (q : Fin m → ℕ) (hq : ∀ i, 2 ≤ q i)
    (z : Fin (m+1) → E) (hz : ∃ i, Transcendental ℂ (z i)) :
    let w := LogTwo.chosenWeights n hn m q hq
    let sigma := curveSigma w.theta m
    let hK : 0 < w.K := Parameters.centerCount_pos (Parameters.shape n hn).one_lt_c.le m
    ∀ (y : Fin w.K → ℂ) (hy : ∀ j, y j ≠ 0) (c : Fin w.K → Fin m → ℂ),
      CurveContactSum.weightedDegree hfinite z (rationalColumnWeight w) <
        (1+(sigma : ℝ)) * ∑ p ∈ ContactFamilyAt.places hfinite z y c hz,
          (ContactFamilyAt.contact hres hfinite z y hy c hz hK (jetWeight w) p : ℝ) →
      ∀ᶠ N : ℕ in atTop, ∃ F : FramePolynomial m, F ≠ 0 ∧
        HasWeightedDegreeLE (columnWeight w) N F ∧
        ∀ word : List (Fin (m+1)), (word.map (jetWeight w)).sum ≤ sigma*N →
          MvPolynomial.aeval z (polynomialFrameWord m word F) = 0 := by
  dsimp only
  intro y hy c hexcess
  let w := LogTwo.chosenWeights n hn m q hq
  have hK : 0 < w.K := Parameters.centerCount_pos (Parameters.shape n hn).one_lt_c.le m
  have hm := chosenWeights_geometric_margins n hn m q hq
  have h := ContactFamilyAt.eventually_exists_annihilator_of_excess hres hfinite z y hy c hz hK
    (rationalColumnWeight w) (jetWeight w) (rationalColumnWeight_pos w) (jetWeight_pos w)
    (curveSigma w.theta m) hm.1 hm.2.2 hexcess
  simpa only [cast_rationalColumnWeight] using h

end
end LogTwo.Geometry

module

public import LogTwo.Geometry.PersistentRigidity

@[expose] public section

/-! Component contact bounds with an explicit normal comparison input.
NormalComparison supplies this input; GlobalContactBound applies that proof. -/
namespace LogTwo.Geometry
open OAI PiExponent PiExponentApprox CurveValuationCenter PlaceValuationRing
open Filter Topology
noncomputable section
variable {E : Type*} [Field E] [Algebra ℂ E]

/-- The comparison input, restricted to the actual coordinate kernel.
It is a proposition; NormalComparison.lean proves it for positive weights. -/
def EventualKernelComparison {m : ℕ} (z : Fin (m+1) → E)
    (w cost : Fin (m+1) → ℝ) (M sigma : ℝ) : Prop :=
  ∀ᶠ N : ℕ in atTop, ∀ F : FramePolynomial m, F ≠ 0 →
    HasWeightedDegreeLE w N F →
    ∀ hY : MvPolynomial.X (0 : Fin (m+1)) ∉ coordinateKernel z,
      CurveComponentRigidity.PersistentNormalComparison w cost M
        ((sigma/((m : ℝ)+2))*N) F (coordinateKernel z) hY

variable {m K : ℕ}
variable
    (hres : ∀ p : NormalizedPlace ℂ E,
      Algebra.IsIntegral ℂ (IsLocalRing.ResidueField (ring p)))
    (hfinite : ∀ f : E, Transcendental ℂ f →
      FiniteDimensional (IntermediateField.adjoin ℂ {f}) E)
    (z : Fin (m+1) → E) (y : Fin K → ℂ) (hy : ∀ j, y j ≠ 0)
    (c : Fin K → Fin m → ℂ) (hz : ∃ i, Transcendental ℂ (z i)) (hK : 0 < K)

theorem constantY_of_excess_of_comparison
    (w v : Fin (m+1) → ℚ) (hw : ∀ i, 0 < w i) (hv : ∀ i, 0 < v i)
    (sigma : ℚ) (hsigma : 0 < sigma)
    (hvol : (K : ℝ)*(1+3*(sigma : ℝ))^(m+1)*(∏ i, (w i : ℝ))/(∏ i, (v i : ℝ)) < 1)
    (M : ℝ)
    (hseparated : SeparatedProducts (fun i => (w i : ℝ)) (fun i => (v i : ℝ)) M)
    (hcomparison : EventualKernelComparison z (fun i => (w i : ℝ))
      (fun i => (v i : ℝ)) M sigma)
    (hexcess : CurveContactSum.weightedDegree hfinite z w <
      (1+(sigma : ℝ))*∑ p ∈ ContactFamilyAt.places hfinite z y c hz,
        (ContactFamilyAt.contact hres hfinite z y hy c hz hK v p : ℝ)) :
    ∃ a : ℂ, z 0 = algebraMap ℂ E a := by
  obtain ⟨hheight,hY,hann⟩ := rigidity_data_of_excess hres hfinite z y hy c hz hK
    w v hw hv sigma hsigma hvol hexcess
  obtain ⟨N,hF,hcomp⟩ := (hann.and hcomparison).exists
  obtain ⟨F,hF0,hdegree,hwords⟩ := hF
  exact coordinate_constant_of_persistent_comparison z hheight hY
    (fun i => (w i : ℝ)) (fun i => (v i : ℝ)) M sigma N
    (fun i => by exact_mod_cast (hv i).le) (by exact_mod_cast hsigma.le)
    (Nat.cast_nonneg N) F hF0 hwords (hcomp F hF0 hdegree hY) hseparated

/-- The full finite contact sum obeys the desired inequality once the normal
comparison and weight separation have been supplied. -/
theorem contact_bound_of_comparison (hinj : Function.Injective y)
    (w v : Fin (m+1) → ℚ) (hw : ∀ i, 0 < w i) (hv : ∀ i, 0 < v i)
    (theta : ℚ) (htheta : 0 ≤ theta)
    (hratio : ∀ i : Fin m, w i.succ = theta*v i.succ)
    (sigma : ℚ) (hsigma : 0 < sigma) (hmargin : (1+sigma)*theta ≤ 1)
    (hvol : (K : ℝ)*(1+3*(sigma : ℝ))^(m+1)*(∏ i, (w i : ℝ))/(∏ i, (v i : ℝ)) < 1)
    (M : ℝ)
    (hseparated : SeparatedProducts (fun i => (w i : ℝ)) (fun i => (v i : ℝ)) M)
    (hcomparison : EventualKernelComparison z (fun i => (w i : ℝ))
      (fun i => (v i : ℝ)) M sigma) :
    (1+(sigma : ℝ))*∑ p ∈ ContactFamilyAt.places hfinite z y c hz,
      (ContactFamilyAt.contact hres hfinite z y hy c hz hK v p : ℝ) ≤
        CurveContactSum.weightedDegree hfinite z w := by
  by_contra h
  obtain ⟨a,ha⟩ := constantY_of_excess_of_comparison hres hfinite z y hy c hz hK
    w v hw hv sigma hsigma hvol M hseparated hcomparison (lt_of_not_ge h)
  exact h (ContactFamilyAt.no_excess_of_constantY hres hfinite z y hy c hz hK hinj
    w v hw hv theta htheta hratio sigma hsigma.le hmargin a ha)

end
end LogTwo.Geometry

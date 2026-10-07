module

public import LogTwo.Geometry.CurveCertificate
public import LogTwo.Geometry.CoordinateKernel

@[expose] public section

/-! The verified field-level inputs to the remaining separated-weight rigidity
argument. No rigidity implication or interpolation surjectivity is postulated. -/
namespace LogTwo.Geometry
open OAI PiExponent PiExponentApprox
open CurveValuationCenter CurveCenters PlaceValuationRing
open Filter Topology
noncomputable section
variable {E : Type*} [Field E] [Algebra ℂ E]

theorem cast_word_cost {ι : Type*} (v : ι → ℚ) (word : List ι) :
    (((word.map v).sum : ℚ) : ℝ) = (word.map (fun i => (v i : ℝ))).sum := by
  induction word with
  | nil => simp
  | cons i word ih => simp [ih]

/-- Excess of the constructed complete contact sum supplies the prime-kernel
height bound, the nonvanishing Y coordinate, and, for every sufficiently large N,
a nonzero polynomial of weighted degree at most N whose low-cost derivative
words lie in that kernel. -/
theorem rigidity_data_of_excess {m K : ℕ}
    (hres : ∀ p : NormalizedPlace ℂ E,
      Algebra.IsIntegral ℂ (IsLocalRing.ResidueField (ring p)))
    (hfinite : ∀ f : E, Transcendental ℂ f →
      FiniteDimensional (IntermediateField.adjoin ℂ {f}) E)
    (z : Fin (m+1) → E) (y : Fin K → ℂ) (hy : ∀ j, y j ≠ 0)
    (c : Fin K → Fin m → ℂ) (hz : ∃ i, Transcendental ℂ (z i)) (hK : 0 < K)
    (w v : Fin (m+1) → ℚ) (hw : ∀ i, 0 < w i) (hv : ∀ i, 0 < v i)
    (sigma : ℚ) (hsigma : 0 < sigma)
    (hvol : (K : ℝ)*(1+3*(sigma : ℝ))^(m+1)*(∏ i, (w i : ℝ))/(∏ i, (v i : ℝ)) < 1)
    (hexcess : CurveContactSum.weightedDegree hfinite z w <
      (1+(sigma : ℝ)) * ∑ p ∈ ContactFamilyAt.places hfinite z y c hz,
        (ContactFamilyAt.contact hres hfinite z y hy c hz hK v p : ℝ)) :
    (coordinateKernel z).height ≤ (m : ℕ∞) ∧
      MvPolynomial.X (0 : Fin (m+1)) ∉ coordinateKernel z ∧
      ∀ᶠ N : ℕ in atTop, ∃ F : FramePolynomial m, F ≠ 0 ∧
        HasWeightedDegreeLE (fun i => (w i : ℝ)) N F ∧
        ∀ word : List (Fin (m+1)),
          (word.map (fun i => (v i : ℝ))).sum ≤ (sigma : ℝ)*N →
            polynomialFrameWord m word F ∈ coordinateKernel z := by
  classical
  have hS : (ContactFamilyAt.places hfinite z y c hz).Nonempty := by
    by_contra hn
    rw [Finset.not_nonempty_iff_eq_empty.mp hn, Finset.sum_empty, mul_zero] at hexcess
    exact (not_lt_of_ge (CurveContactSum.weightedDegree_nonneg hfinite z w)) hexcess
  obtain ⟨p, hp⟩ := hS
  let := hres p
  let j := ContactFamilyAt.center hfinite z y c hz hK p
  have hc := ContactFamilyAt.centered hfinite z y c hz hK p hp
  refine ⟨coordinateKernel_height_le p z (centerPoint (y j) (c j)) hc
    (ContactFamilyAt.nonconstant z _ _ hz),
    coordinateKernel_X_zero_not_mem p z (centerPoint (y j) (c j)) hc (hy j), ?_⟩
  filter_upwards [ContactFamilyAt.eventually_exists_annihilator_of_excess hres hfinite
    z y hy c hz hK w v hw hv sigma hsigma hvol hexcess] with N hN
  obtain ⟨F, hF0, hF, hwords⟩ := hN
  refine ⟨F, hF0, hF, ?_⟩
  intro word hword
  apply hwords word
  rw [← cast_word_cost] at hword
  exact_mod_cast hword

end
end LogTwo.Geometry

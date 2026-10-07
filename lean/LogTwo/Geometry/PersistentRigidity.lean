/-
Modification notice for the LogTwo project.
Adapted from openai/math (Apache-2.0), revision adc7f1241b42e322a6451854ab7e4b4c146bf78a.
Changes: Adapt the logarithmic rigidity and cutoff arguments to log-two data.
See ../../../THIRD_PARTY_NOTICES.txt for provenance and the recorded changes.
-/

module

public import LogTwo.Geometry.RigidityInput
public import LogTwo.Geometry.SeparatedWeights
public import OAI.NumberTheory.PiExponent.Geometry.CurveComponentRigidity
public import OAI.NumberTheory.PiExponent.Approximation.RectangularVolume

@[expose] public section

/-! The algebraic rigidity implication, with the persistent normal-product
comparison exposed as an input here and proved in NormalComparison.lean. The implication adapts the
logarithmic part of Geometry/CurveFieldRigidity.lean (openai/math, Apache-2.0).
It applies at every nonzero Y center, not only Y=1. -/
namespace LogTwo.Geometry
open OAI PiExponent PiExponentApprox CurveValuationCenter CurveCenters
open Filter Topology
noncomputable section
variable {E : Type*} [Field E] [Algebra ℂ E]

/-- The same numerical constant as the comparison theorem, defined without its
large intersection-theory import closure. -/
def rigidityComparisonConstant (m : ℕ) (sigma : ℝ) : ℝ :=
  2*((m : ℝ)+2)^(m+2)*(1+((m : ℝ)+2)/sigma)^(m+2)

theorem rigidityComparisonConstant_pos (m : ℕ) {sigma : ℝ} (hsigma : 0 < sigma) :
    0 < rigidityComparisonConstant m sigma := by
  unfold rigidityComparisonConstant
  positivity

def UniformRectangles (n : ℕ) (cost : Fin n → ℝ) (epsilon N : ℝ) : Prop :=
  ∀ k : ℕ, 0 < k → k ≤ n → ∀ B : Fin k → Fin n, ∀ i,
    2 ≤ rectangularCutoff (fun j => cost (B j)) (epsilon*N) i

/-- Rectangular cutoffs are achieved after fixing all costs. No uniformity in
future choices of centers or denominators is asserted. -/
theorem eventually_uniformRectangles_nat (n : ℕ) (cost : Fin n → ℝ)
    (hcost : ∀ i, 0 < cost i) (epsilon : ℝ) (hepsilon : 0 < epsilon) :
    ∀ᶠ N : ℕ in atTop, UniformRectangles n cost epsilon N := by
  have ht : Tendsto (fun N : ℕ => epsilon*(N : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.const_mul_atTop hepsilon
  have hb : ∀ᶠ N : ℕ in atTop, ∀ j : Fin n,
      (n : ℝ)*cost j < epsilon*N :=
    Filter.eventually_all.mpr (fun j => ht.eventually (eventually_gt_atTop _))
  filter_upwards [hb] with N hN
  intro k hk hkn B i
  apply two_le_rectangularCutoff hk (fun j => cost (B j)) (fun j => hcost _) i
  exact (mul_le_mul_of_nonneg_right (Nat.cast_le.mpr hkn) (hcost _).le).trans_lt (hN (B i))

theorem coordinate_constant_of_persistent_comparison {m : ℕ}
    (z : Fin (m+1) → E) (hheight : (coordinateKernel z).height ≤ m)
    (hY : MvPolynomial.X (0 : Fin (m+1)) ∉ coordinateKernel z)
    (w cost : Fin (m+1) → ℝ) (M sigma N : ℝ)
    (hcost : ∀ i, 0 ≤ cost i) (hsigma : 0 ≤ sigma) (hN : 0 ≤ N)
    (F : FramePolynomial m) (hF0 : F ≠ 0)
    (hvanish : ∀ word : List (Fin (m+1)), frameWordCost cost word ≤ sigma*N →
      polynomialFrameWord m word F ∈ coordinateKernel z)
    (hcomparison : CurveComponentRigidity.PersistentNormalComparison w cost M
      ((sigma/((m : ℝ)+2))*N) F (coordinateKernel z) hY)
    (hseparated : SeparatedProducts w cost M) :
    ∃ a : ℂ, z 0 = algebraMap ℂ E a := by
  have hbound : ((m : ℝ)+2)*((sigma/((m : ℝ)+2))*N) = sigma*N := by
    have hm : (m : ℝ)+2 ≠ 0 := by positivity
    field_simp
  obtain ⟨a, ha⟩ := CurveComponentRigidity.coordinate_constant_of_persistent_comparison
    w cost M ((sigma/((m : ℝ)+2))*N) hcost (by positivity) F hF0
    (coordinateKernel z) inferInstance hheight hY
    (fun word hword => hvanish word (by simpa only [hbound] using hword))
    hcomparison hseparated
  exact ⟨a, by simpa only [mem_coordinateKernel, map_sub, MvPolynomial.aeval_X,
    MvPolynomial.aeval_C, sub_eq_zero] using ha⟩

theorem coordinate_eq_center_of_persistent_comparison {m : ℕ}
    (z : Fin (m+1) → E) (a : Fin (m+1) → ℂ) (ha : a 0 ≠ 0)
    (p : NormalizedPlace ℂ E) (hp : Centered z a p)
    (hheight : (coordinateKernel z).height ≤ m)
    (w cost : Fin (m+1) → ℝ) (M sigma N : ℝ)
    (hcost : ∀ i, 0 ≤ cost i) (hsigma : 0 ≤ sigma) (hN : 0 ≤ N)
    (F : FramePolynomial m) (hF0 : F ≠ 0)
    (hvanish : ∀ word : List (Fin (m+1)), frameWordCost cost word ≤ sigma*N →
      polynomialFrameWord m word F ∈ coordinateKernel z)
    (hcomparison : CurveComponentRigidity.PersistentNormalComparison w cost M
      ((sigma/((m : ℝ)+2))*N) F (coordinateKernel z)
      (coordinateKernel_X_zero_not_mem p z a hp ha))
    (hseparated : SeparatedProducts w cost M) :
    z 0 = algebraMap ℂ E (a 0) := by
  obtain ⟨b, hb⟩ := coordinate_constant_of_persistent_comparison z hheight
    (coordinateKernel_X_zero_not_mem p z a hp ha) w cost M sigma N
    hcost hsigma hN F hF0 hvanish hcomparison hseparated
  exact hb.trans (congrArg (algebraMap ℂ E) (hp.constant_coordinate 0 b hb))

end
end LogTwo.Geometry

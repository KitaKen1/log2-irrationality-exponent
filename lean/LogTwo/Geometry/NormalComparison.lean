/-
Modification notice for the LogTwo project.
Adapted from openai/math (Apache-2.0), revision adc7f1241b42e322a6451854ab7e4b4c146bf78a.
Changes: Adapt the logarithmic persistent weight comparison to log-two data.
See ../../../THIRD_PARTY_NOTICES.txt for provenance and the recorded changes.
-/

module

public import LogTwo.Geometry.ContactBound
public import OAI.NumberTheory.PiExponent.Approximation.FrameEquationFamily
public import OAI.NumberTheory.PiExponent.Jets.TransverseSliceComparison

@[expose] public section

/-! The logarithmic normal comparison, adapted from the logarithmic part of
Approximation/PersistentWeightComparison.lean in pinned openai/math (Apache-2.0).
This discharges EventualKernelComparison using the proved local length bounds.
The ordinary-coordinate comparison is not imported. -/
namespace LogTwo.Geometry
open scoped BigOperators
open OAI PiExponent PiExponentApprox NormalBasisRigidity NormalBasisProducts
open Filter Topology
noncomputable section

theorem logarithmic_normal_comparison {m : ℕ}
    (rho : Fin (m + 1) → ℚ) (hrho : ∀ i, 0 < rho i)
    (cost : Fin (m + 1) → ℝ) (hcost : ∀ i, 0 < cost i)
    (sigma N : ℝ) (hsigma : 0 < sigma) (hN : 0 < N)
    (hrect : UniformRectangles (m + 1) cost (sigma / ((m : ℝ) + 2)) N)
    (F : FramePolynomial m) (hF : HasWeightedDegreeLE (fun i => (rho i : ℝ)) N F)
    (bound : ℝ) (Q : Ideal (FramePolynomial m)) [Q.IsPrime]
    (hY : MvPolynomial.X (0 : Fin (m + 1)) ∉ Q)
    (hQ : Q ∈ (frameDerivativeIdeal cost bound F).minimalPrimes)
    (hvanish : ∀ p ∈ frameDerivativeIdeal cost bound F,
      ∀ word : List (Fin (m + 1)),
        frameWordCost cost word ≤ (sigma / ((m : ℝ) + 2)) * N →
          polynomialFrameWord m word p ∈ Q) :
    CurveComponentRigidity.NormalProductComparison Q hY
      (fun i => (rho i : ℝ)) cost (rigidityComparisonConstant m sigma) := by
  intro A B hA hB
  have hcard : A.card = B.card := hA.card_eq.trans hB.card_eq.symm
  by_cases hk0 : A.card = 0
  · have hA0 : A = ∅ := Finset.card_eq_zero.mp hk0
    have hB0 : B = ∅ := Finset.card_eq_zero.mp (hcard.symm.trans hk0)
    have hc := rectangular_factor_le_constant m 0 sigma hsigma (by omega)
    simpa [hA0, hB0, rigidityComparisonConstant] using hc
  have hk : 0 < A.card := Nat.pos_of_ne_zero hk0
  have hka : A.card ≤ m + 1 := by simpa using Finset.card_le_univ A
  have hepsilon : 0 < sigma / ((m : ℝ) + 2) := by positivity
  have hrhoR (i : Fin (m + 1)) : (0 : ℝ) < rho i := by exact_mod_cast hrho i
  have hdegree : ∀ j, ∀ d ∈ (FrameEquationFamily.equations cost bound F j).support,
      (∑ i ∈ d.support, (d i : ℝ) * (rho i : ℝ)) ≤ N := by
    intro j
    have h := FrameEquationFamily.equation_supportBound cost (fun i => (rho i : ℝ))
      bound N F hF (fun i => (hrhoR i).le) j
    simpa only [WeightedSliceDegree.SupportBound, Finsupp.weight_apply, Finsupp.sum,
      nsmul_eq_mul] using h
  have hcomp := TransverseSliceComparison.comparison_of_normal_basis Q
    (CurveComponentRigidity.residueY_ne_zero Q hY) A hk hA
    (enumeration A B hcard) (enumeration_linearIndependent A B hcard hB)
    (FrameEquationFamily.equations cost bound F)
    (by simpa only [FrameEquationFamily.span_equations] using hQ)
    rho hrho cost hcost (sigma / ((m : ℝ) + 2)) N hepsilon hN hdegree
    (hrect A.card hk hka (enumeration A B hcard))
    (by simpa only [FrameEquationFamily.span_equations] using hvanish)
  exact hcomp.trans (by
    have hc := rectangular_comparison_le_constant (m := m) (k := A.card)
      (by omega) (fun i => cost (enumeration A B hcard i)) sigma hsigma
      (fun i => (hcost _).le)
    simpa only [prod_enumeration A B hcard cost, rigidityComparisonConstant] using hc)

theorem logarithmic_persistent_comparison {m : ℕ}
    (rho : Fin (m + 1) → ℚ) (hrho : ∀ i, 0 < rho i)
    (cost : Fin (m + 1) → ℝ) (hcost : ∀ i, 0 < cost i)
    (sigma N : ℝ) (hsigma : 0 < sigma) (hN : 0 < N)
    (hrect : UniformRectangles (m + 1) cost (sigma / ((m : ℝ) + 2)) N)
    (F : FramePolynomial m) (hF : HasWeightedDegreeLE (fun i => (rho i : ℝ)) N F)
    (P : Ideal (FramePolynomial m)) (hY : MvPolynomial.X (0 : Fin (m + 1)) ∉ P) :
    CurveComponentRigidity.PersistentNormalComparison (fun i => (rho i : ℝ)) cost
      (rigidityComparisonConstant m sigma) ((sigma / ((m : ℝ) + 2)) * N) F P hY := by
  intro r hr Q hQ hQP hQr hQnext hQlo hQhi hvanish
  let := hQ
  exact logarithmic_normal_comparison rho hrho cost hcost sigma N hsigma hN hrect
    F hF _ Q (fun h => hY (hQP h)) hQr hvanish


/-- The former geometric comparison input is supplied for all positive rational
degree weights and positive real derivative costs. The cutoff is chosen after
these data, independently of the field coordinates. -/
theorem eventualKernelComparison {E : Type*} [Field E] [Algebra ℂ E] {m : ℕ}
    (z : Fin (m+1) → E) (rho : Fin (m+1) → ℚ) (hrho : ∀ i, 0 < rho i)
    (cost : Fin (m+1) → ℝ) (hcost : ∀ i, 0 < cost i)
    (sigma : ℝ) (hsigma : 0 < sigma) :
    EventualKernelComparison z (fun i => (rho i : ℝ)) cost
      (rigidityComparisonConstant m sigma) sigma := by
  have hepsilon : 0 < sigma/((m : ℝ)+2) := by positivity
  filter_upwards [eventually_uniformRectangles_nat (m+1) cost hcost _ hepsilon,
    eventually_gt_atTop (0 : ℕ)] with N hrect hN
  intro F _ hF hY
  exact logarithmic_persistent_comparison rho hrho cost hcost sigma N hsigma
    (by exact_mod_cast hN) hrect F hF (coordinateKernel z) hY

end
end LogTwo.Geometry

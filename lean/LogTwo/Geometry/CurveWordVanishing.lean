/-
Modification notice for the LogTwo project.
Adapted from openai/math (Apache-2.0), revision adc7f1241b42e322a6451854ab7e4b4c146bf78a.
Changes: Adapt logarithmic word vanishing to nonzero Y-centers and normalized contacts.
See ../../../THIRD_PARTY_NOTICES.txt for provenance and the recorded changes.
-/

module

public import LogTwo.Geometry.AuxiliaryAtCenters
public import LogTwo.Geometry.ConstantFiber

@[expose] public section

/-! Adapted from openai/math, commit adc7f1241b42e322a6451854ab7e4b4c146bf78a,
Cohomology/CurveDerivativeVanishing.lean (Apache-2.0). This version uses arbitrary
nonzero Y-centers and any finite family of actual normalized contacts. It does
not import the global rigidity theorem. See THIRD_PARTY_NOTICES.txt. -/
namespace LogTwo.Geometry
open OAI PiExponentApprox PiExponent
open CurveValuationCenter CurveCenters PlaceValuationRing WeightedPolynomialPole
open Filter Topology
noncomputable section
variable {E : Type*} [Field E] [Algebra ℂ E]

/-- Excess actual contact forces low-cost derivative words to vanish identically
on the curve. Local order bounds are proved from jets, rather than assumed. -/
theorem curve_words_vanish_of_excess {m K : ℕ}
    (hfinite : ∀ f : E, Transcendental ℂ f →
      FiniteDimensional (IntermediateField.adjoin ℂ {f}) E)
    (z : Fin (m+1) → E) (y : Fin K → ℂ) (hy : ∀ j, y j ≠ 0)
    (c : Fin K → Fin m → ℂ)
    (hnc : ∀ j, ∃ i, z i ≠ algebraMap ℂ E (centerPoint (y j) (c j) i))
    (w v : Fin (m+1) → ℚ) (hw : ∀ i, 0 < w i) (hv : ∀ i, 0 < v i)
    (S : Finset (NormalizedPlace ℂ E)) (center : NormalizedPlace ℂ E → Fin K)
    (hc : ∀ p ∈ S, Centered z (centerPoint (y (center p)) (c (center p))) p)
    (hres : ∀ p ∈ S, Algebra.IsIntegral ℂ (IsLocalRing.ResidueField (ring p)))
    (μ : NormalizedPlace ℂ E → ℝ)
    (hμ : ∀ p (hp : p ∈ S), letI := hres p hp;
      μ p = (logContactAt p (y (center p)) (hy (center p)) z (c (center p))
        (hc p hp) (hnc (center p)) v : ℝ))
    (sigma : ℚ) (hsigma : 0 < sigma) (N : ℕ) (hN : 0 < N)
    (F : FramePolynomial m)
    (hF : HasWeightedDegreeLE (fun i => (w i : ℝ)) N F)
    (hjet : ∀ j, formalJetAt (y j) (c j) F ∈
      JetGeometry.rationalWeightedIdeal v (fun i => (hv i).le) ((1+3*sigma)*N))
    (hexcess : CurveContactSum.weightedDegree hfinite z w <
      (1+(sigma : ℝ)) * ∑ p ∈ S, μ p) :
    ∀ word : List (Fin (m+1)), (word.map v).sum ≤ sigma*N →
      MvPolynomial.aeval z (polynomialFrameWord m word F) = 0 := by
  intro word hword
  have hNR : (0 : ℝ) < N := by exact_mod_cast hN
  have hsigR : (0 : ℝ) < sigma := by exact_mod_cast hsigma
  have hdegree : ∀ d ∈ (polynomialFrameWord m word F).support,
      Finsupp.weight (fun i => (w i : ℝ)) d ≤ (N : ℝ) := by
    have hd := hF.polynomialFrameWord (fun i => by exact_mod_cast (hw i).le) word
    intro d hdmem
    simpa only [Finsupp.weight_eq_sum, nsmul_eq_mul, monomialWeight] using hd d hdmem
  have hsum : 0 ≤ ∑ p ∈ S, μ p := by
    apply Finset.sum_nonneg
    intro p hp
    letI := hres p hp
    rw [hμ p hp]
    exact_mod_cast (logContactAt_pos p (y (center p)) (hy (center p)) z
      (c (center p)) (hc p hp) (hnc (center p)) v hv).le
  apply CurveContactSum.polynomial_eq_zero_of_excess_contact hfinite z w hw
    (N : ℝ) ((1+2*(sigma : ℝ))*N) hNR.le (polynomialFrameWord m word F) hdegree S μ
  · intro hne p hp
    letI := hres p hp
    have hret : (1+2*sigma)*(N : ℚ) ≤ (1+3*sigma)*N - (word.map v).sum := by
      nlinarith
    have hlocal := logWord_order_lower_at p (y (center p)) (hy (center p)) z
      (c (center p)) (hc p hp) (hnc (center p)) v hv ((1+3*sigma)*N)
      F (hjet (center p)) word hne
    have hpos := (logContactAt_pos p (y (center p)) (hy (center p)) z
      (c (center p)) (hc p hp) (hnc (center p)) v hv).le
    have hq := (mul_le_mul_of_nonneg_left hret hpos).trans hlocal
    have hr : (logContactAt p (y (center p)) (hy (center p)) z (c (center p))
        (hc p hp) (hnc (center p)) v : ℝ) * ((1+2*(sigma : ℝ))*N) ≤
        (coordinateOrder p.valuation (MvPolynomial.aeval z (polynomialFrameWord m word F)) : ℝ) := by
      exact_mod_cast hq
    simpa only [← hμ p hp, mul_comm] using hr
  · calc
      (N : ℝ) * CurveContactSum.weightedDegree hfinite z w <
          N * ((1+(sigma : ℝ)) * ∑ p ∈ S, μ p) := mul_lt_mul_of_pos_left hexcess hNR
      _ = (1+(sigma : ℝ)) * (N * ∑ p ∈ S, μ p) := by ring
      _ ≤ (1+2*(sigma : ℝ)) * (N * ∑ p ∈ S, μ p) :=
        mul_le_mul_of_nonneg_right (by linarith) (mul_nonneg hNR.le hsum)
      _ = _ := by ring

end
end LogTwo.Geometry

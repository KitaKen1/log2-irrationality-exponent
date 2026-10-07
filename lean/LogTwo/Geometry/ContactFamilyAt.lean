/-
Modification notice for the LogTwo project.
Adapted from openai/math (Apache-2.0), revision adc7f1241b42e322a6451854ab7e4b4c146bf78a.
Changes: Adapt local contact families to varying Y-centers and a total center choice.
See ../../../THIRD_PARTY_NOTICES.txt for provenance and the recorded changes.
-/

module

public import LogTwo.Geometry.CurveWordVanishing

@[expose] public section

/-! Adapted from openai/math, commit adc7f1241b42e322a6451854ab7e4b4c146bf78a,
Geometry/CurveContactFamily.lean (Apache-2.0), to varying nonzero Y-centers.
All centered normalized places are included, not a selected subset.
See THIRD_PARTY_NOTICES.txt. -/
namespace LogTwo.Geometry.ContactFamilyAt
open OAI PiExponent PiExponentApprox
open CurveValuationCenter CurveCenters PlaceValuationRing
open Filter Topology
noncomputable section
variable {E : Type*} [Field E] [Algebra ℂ E] {m K : ℕ}

def places
    (hfinite : ∀ f : E, Transcendental ℂ f →
      FiniteDimensional (IntermediateField.adjoin ℂ {f}) E)
    (z : Fin (m+1) → E) (y : Fin K → ℂ) (c : Fin K → Fin m → ℂ)
    (hz : ∃ i, Transcendental ℂ (z i)) : Finset (NormalizedPlace ℂ E) :=
  centerPlaces z (fun j => centerPoint (y j) (c j)) hz hfinite

theorem mem_places
    (hfinite : ∀ f : E, Transcendental ℂ f →
      FiniteDimensional (IntermediateField.adjoin ℂ {f}) E)
    (z : Fin (m+1) → E) (y : Fin K → ℂ) (c : Fin K → Fin m → ℂ)
    (hz : ∃ i, Transcendental ℂ (z i)) (p : NormalizedPlace ℂ E) :
    p ∈ places hfinite z y c hz ↔ ∃ j, Centered z (centerPoint (y j) (c j)) p :=
  mem_centerPlaces z (fun j => centerPoint (y j) (c j)) hz hfinite p

/-- The value off the finite set is arbitrary and never contributes to contact. -/
def center
    (hfinite : ∀ f : E, Transcendental ℂ f →
      FiniteDimensional (IntermediateField.adjoin ℂ {f}) E)
    (z : Fin (m+1) → E) (y : Fin K → ℂ) (c : Fin K → Fin m → ℂ)
    (hz : ∃ i, Transcendental ℂ (z i)) (hK : 0 < K) (p : NormalizedPlace ℂ E) : Fin K := by
  classical
  exact if hp : p ∈ places hfinite z y c hz then
    Classical.choose ((mem_places hfinite z y c hz p).mp hp) else ⟨0, hK⟩

theorem centered
    (hfinite : ∀ f : E, Transcendental ℂ f →
      FiniteDimensional (IntermediateField.adjoin ℂ {f}) E)
    (z : Fin (m+1) → E) (y : Fin K → ℂ) (c : Fin K → Fin m → ℂ)
    (hz : ∃ i, Transcendental ℂ (z i)) (hK : 0 < K)
    (p : NormalizedPlace ℂ E) (hp : p ∈ places hfinite z y c hz) :
    Centered z (centerPoint (y (center hfinite z y c hz hK p))
      (c (center hfinite z y c hz hK p))) p := by
  simpa only [center, dite_eq_left hp] using
    Classical.choose_spec ((mem_places hfinite z y c hz p).mp hp)

theorem nonconstant (z : Fin (m+1) → E) (y : ℂ) (c : Fin m → ℂ)
    (hz : ∃ i, Transcendental ℂ (z i)) :
    ∃ i, z i ≠ algebraMap ℂ E (centerPoint y c i) :=
  Centered.exists_nonzero_difference z (centerPoint y c) hz

variable
    (hres : ∀ p : NormalizedPlace ℂ E,
      Algebra.IsIntegral ℂ (IsLocalRing.ResidueField (ring p)))
    (hfinite : ∀ f : E, Transcendental ℂ f →
      FiniteDimensional (IntermediateField.adjoin ℂ {f}) E)
    (z : Fin (m+1) → E) (y : Fin K → ℂ) (hy : ∀ j, y j ≠ 0)
    (c : Fin K → Fin m → ℂ) (hz : ∃ i, Transcendental ℂ (z i)) (hK : 0 < K)

def contact (v : Fin (m+1) → ℚ) (p : NormalizedPlace ℂ E) : ℚ := by
  classical
  let := hres p
  let j := center hfinite z y c hz hK p
  exact if hp : p ∈ places hfinite z y c hz then
    logContactAt p (y j) (hy j) z (c j)
      (centered hfinite z y c hz hK p hp) (nonconstant z (y j) (c j) hz) v
  else 0

theorem contact_eq (v : Fin (m+1) → ℚ) (p : NormalizedPlace ℂ E)
    (hp : p ∈ places hfinite z y c hz) :
    letI := hres p
    contact hres hfinite z y hy c hz hK v p =
      logContactAt p (y (center hfinite z y c hz hK p))
        (hy (center hfinite z y c hz hK p)) z (c (center hfinite z y c hz hK p))
        (centered hfinite z y c hz hK p hp)
        (nonconstant z _ _ hz) v := by
  simp only [contact, dite_eq_left hp]

theorem contact_pos (v : Fin (m+1) → ℚ) (hv : ∀ i, 0 < v i)
    (p : NormalizedPlace ℂ E) (hp : p ∈ places hfinite z y c hz) :
    0 < contact hres hfinite z y hy c hz hK v p := by
  let := hres p
  rw [contact_eq hres hfinite z y hy c hz hK v p hp]
  exact logContactAt_pos p _ _ _ _ _ _ v hv

theorem contact_nonneg (v : Fin (m+1) → ℚ) (hv : ∀ i, 0 < v i)
    (p : NormalizedPlace ℂ E) : 0 ≤ contact hres hfinite z y hy c hz hK v p := by
  by_cases hp : p ∈ places hfinite z y c hz
  · exact (contact_pos hres hfinite z y hy c hz hK v hv p hp).le
  · simp only [contact, dite_eq_right hp, le_refl]

/-- No per-place order inequalities are inputs: the actual contacts and all places
are supplied by the preceding constructions. -/
theorem words_vanish_of_excess
    (w v : Fin (m+1) → ℚ) (hw : ∀ i, 0 < w i) (hv : ∀ i, 0 < v i)
    (sigma : ℚ) (hsigma : 0 < sigma) (N : ℕ) (hN : 0 < N)
    (F : FramePolynomial m) (hF : HasWeightedDegreeLE (fun i => (w i : ℝ)) N F)
    (hjet : ∀ j, formalJetAt (y j) (c j) F ∈
      JetGeometry.rationalWeightedIdeal v (fun i => (hv i).le) ((1+3*sigma)*N))
    (hexcess : CurveContactSum.weightedDegree hfinite z w <
      (1+(sigma : ℝ)) * ∑ p ∈ places hfinite z y c hz,
        (contact hres hfinite z y hy c hz hK v p : ℝ)) :
    ∀ word : List (Fin (m+1)), (word.map v).sum ≤ sigma*N →
      MvPolynomial.aeval z (polynomialFrameWord m word F) = 0 := by
  apply curve_words_vanish_of_excess hfinite z y hy c
    (fun j => nonconstant z (y j) (c j) hz) w v hw hv
    (places hfinite z y c hz) (center hfinite z y c hz hK)
    (centered hfinite z y c hz hK) (fun p _ => hres p)
    (fun p => (contact hres hfinite z y hy c hz hK v p : ℝ))
    ?_ sigma hsigma N hN F hF hjet hexcess
  intro p hp
  let := hres p
  exact congrArg (fun q : ℚ => (q : ℝ)) (contact_eq hres hfinite z y hy c hz hK v p hp)

/-- A nonzero global polynomial with all low-cost words in the curve kernel,
for every sufficiently large natural N, assuming excess contact and volume. -/
theorem eventually_exists_annihilator_of_excess
    (w v : Fin (m+1) → ℚ) (hw : ∀ i, 0 < w i) (hv : ∀ i, 0 < v i)
    (sigma : ℚ) (hsigma : 0 < sigma)
    (hvol : (K : ℝ) * (1+3*(sigma : ℝ))^(m+1) *
      (∏ i, (w i : ℝ)) / (∏ i, (v i : ℝ)) < 1)
    (hexcess : CurveContactSum.weightedDegree hfinite z w <
      (1+(sigma : ℝ)) * ∑ p ∈ places hfinite z y c hz,
        (contact hres hfinite z y hy c hz hK v p : ℝ)) :
    ∀ᶠ N : ℕ in atTop, ∃ F : FramePolynomial m, F ≠ 0 ∧
      HasWeightedDegreeLE (fun i => (w i : ℝ)) N F ∧
      ∀ word : List (Fin (m+1)), (word.map v).sum ≤ sigma*N →
        MvPolynomial.aeval z (polynomialFrameWord m word F) = 0 := by
  have haux := eventually_exists_auxiliary_at_centers_nat w v hw hv K
    (a := 1+3*sigma) (by positivity) (by simpa using hvol) y c
  filter_upwards [haux, eventually_gt_atTop (0 : ℕ)] with N hauxN hN
  obtain ⟨F, hF0, hF, hjet⟩ := hauxN
  exact ⟨F, hF0, hF, words_vanish_of_excess hres hfinite z y hy c hz hK
    w v hw hv sigma hsigma N hN F hF hjet hexcess⟩

end
end LogTwo.Geometry.ContactFamilyAt

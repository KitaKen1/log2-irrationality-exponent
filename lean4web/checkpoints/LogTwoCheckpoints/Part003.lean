/- Generated rc4 checkpoint for LogTwo.
Modified from the reduced edition: new imports, separate module compilation,
and synchronous elaboration. Original source blocks and notices are retained.
See ../../../THIRD_PARTY_NOTICES.txt and ../../reduction.json.
-/
module
public import LogTwoCheckpoints.Part000
public import LogTwoCheckpoints.Part001
public import LogTwoCheckpoints.Part002
public import Mathlib.Analysis.Complex.Polynomial.Basic
public import Mathlib.RingTheory.Etale.Field
public import Mathlib.RingTheory.KrullDimension.Field
public import Mathlib.RingTheory.KrullDimension.Polynomial
public import Mathlib.RingTheory.LaurentSeries
public import Mathlib.RingTheory.RegularLocalRing.Polynomial
public import Mathlib.Tactic
@[expose] public section
set_option Elab.async false

-- Source: LogTwo/Geometry/ContactFamilyAt.lean
section Source0075
-- Modified in this edition: unused plain lemmas removed; see reduction.json.
/-
Modification notice for the LogTwo project.
Adapted from openai/math (Apache-2.0), revision adc7f1241b42e322a6451854ab7e4b4c146bf78a.
Changes: Adapt local contact families to varying Y-centers and a total center choice.
See ../THIRD_PARTY_NOTICES.txt for provenance and the recorded changes.
-/

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
end Source0075

-- Source: LogTwo/Geometry/GeometricParameters.lean
section Source0076
/-! An explicit rational margin meets the two scalar geometric requirements.
No new analytic estimate or limiting argument is needed. -/
namespace LogTwo.Geometry
open LogTwo.Interpolation LogTwo.Parameters
noncomputable section

def rationalColumnWeight {m : ℕ} (w : Weights m) : Fin (m+1) → ℚ :=
  Fin.cases w.w0 w.w

theorem rationalColumnWeight_pos {m : ℕ} (w : Weights m) :
    ∀ i, 0 < rationalColumnWeight w i :=
  fun i => Fin.cases w.w0_pos w.w_pos i

theorem cast_rationalColumnWeight {m : ℕ} (w : Weights m) :
    (fun i => (rationalColumnWeight w i : ℝ)) = columnWeight w := by
  funext i
  refine Fin.cases rfl (fun _ => rfl) i

theorem weighted_volume_ratio {m : ℕ} (w : Weights m) :
    (w.K : ℚ) * (∏ i, rationalColumnWeight w i) / (∏ i, jetWeight w i) =
      (w.K : ℚ) * (w.w0 / w.v0) * w.theta^m := by
  have hp : (∏ i, w.w i) ≠ 0 := (Finset.prod_pos (fun i _ => w.w_pos i)).ne'
  simp only [Fin.prod_univ_succ, rationalColumnWeight, jetWeight,
    Fin.cases_zero, Fin.cases_succ, Finset.prod_div_distrib, Finset.prod_const,
    Finset.card_univ, Fintype.card_fin]
  field_simp

def curveSigma (theta : ℚ) (m : ℕ) : ℚ :=
  min ((1-theta)/(2*theta)) (1/(12*((m : ℚ)+1)))

theorem curveSigma_pos {theta : ℚ} (htheta : 0 < theta) (hlt : theta < 1) (m : ℕ) :
    0 < curveSigma theta m := by
  unfold curveSigma
  apply lt_min
  · exact div_pos (sub_pos.mpr hlt) (by positivity)
  · positivity

theorem curveSigma_contact_margin {theta : ℚ}
    (htheta : 0 < theta) (hlt : theta < 1) (m : ℕ) :
    (1+curveSigma theta m)*theta < 1 := by
  have hb : curveSigma theta m * (2*theta) ≤ 1-theta :=
    (le_div_iff₀ (by positivity)).mp (min_le_left _ _)
  nlinarith

/-- An elementary reciprocal form of Bernoulli's bound, proved without division.
It is useful only when 1-n*x is positive, but the statement holds for every n. -/
theorem pow_mul_one_sub_mul_le_one {x : ℚ} (hx : 0 ≤ x) (n : ℕ) :
    (1+x)^n * (1-(n : ℚ)*x) ≤ 1 := by
  induction n with
  | zero => simp
  | succ n ih =>
    have hstep : (1+x)*(1-((n : ℚ)+1)*x) ≤ 1-(n : ℚ)*x := by
      have hnx : 0 ≤ (n : ℚ)*x^2 := mul_nonneg (Nat.cast_nonneg _) (sq_nonneg x)
      nlinarith [sq_nonneg x]
    calc
      _ = (1+x)^n * ((1+x)*(1-((n : ℚ)+1)*x)) := by
        rw [pow_succ, Nat.cast_succ]
        ring
      _ ≤ (1+x)^n * (1-(n : ℚ)*x) :=
        mul_le_mul_of_nonneg_left hstep (pow_nonneg (by linarith) n)
      _ ≤ 1 := ih

theorem curveSigma_power_bound {theta : ℚ}
    (htheta : 0 < theta) (hlt : theta < 1) (m : ℕ) :
    (1+3*curveSigma theta m)^(m+1) ≤ 4/3 := by
  have hs := curveSigma_pos htheta hlt m
  have hb : curveSigma theta m * (12*((m : ℚ)+1)) ≤ 1 :=
    (le_div_iff₀ (by positivity)).mp (min_le_right _ _)
  have h := pow_mul_one_sub_mul_le_one (show 0 ≤ 3*curveSigma theta m by positivity) (m+1)
  have hp : 0 ≤ (1+3*curveSigma theta m)^(m+1) := by positivity
  have hsmall : (3/4 : ℚ) ≤ 1-((m : ℚ)+1)*(3*curveSigma theta m) := by
    nlinarith
  have hh := mul_le_mul_of_nonneg_left hsmall hp
  norm_num only [Nat.cast_add, Nat.cast_one] at h
  nlinarith

/-- The enlarged jet volume stays below one whenever the unscaled volume is 1/2. -/
theorem curveSigma_volume_lt_one {m : ℕ} (w : Weights m)
    (hhalf : (w.K : ℚ)*(w.w0/w.v0)*w.theta^m = 1/2) :
    (w.K : ℝ) * (1+3*(curveSigma w.theta m : ℝ))^(m+1) *
      (∏ i, (rationalColumnWeight w i : ℝ)) / (∏ i, (jetWeight w i : ℝ)) < 1 := by
  have hbase : (w.K : ℚ)*(∏ i, rationalColumnWeight w i)/(∏ i, jetWeight w i) = 1/2 :=
    (weighted_volume_ratio w).trans hhalf
  have hpow := curveSigma_power_bound w.theta_pos w.theta_lt_one m
  have hscaled : (w.K : ℚ)*(1+3*curveSigma w.theta m)^(m+1)*
      (∏ i, rationalColumnWeight w i)/(∏ i, jetWeight w i) < 1 := by
    calc
      _ = (1+3*curveSigma w.theta m)^(m+1) *
          ((w.K : ℚ)*(∏ i, rationalColumnWeight w i)/(∏ i, jetWeight w i)) := by ring
      _ = (1+3*curveSigma w.theta m)^(m+1) * (1/2) := by rw [hbase]
      _ < 1 := by linarith
  exact_mod_cast hscaled

/-- The actual arithmetic weights already have the required volume 1/2. -/
theorem chosenWeights_half_volume (n : ℕ) (hn : 1 ≤ n) (m : ℕ)
    (q : Fin m → ℕ) (hq : ∀ i, 2 ≤ q i) :
    let w := LogTwo.chosenWeights n hn m q hq
    (w.K : ℚ)*(w.w0/w.v0)*w.theta^m = 1/2 := by
  exact chosen_volume_ratio (shape n hn).theta_pos
    ((shape n hn).theta_pos.trans ((shape n hn).theta_lt_a.trans (shape n hn).a_lt_b))
    (shape n hn).one_lt_c.le m

theorem chosenWeights_geometric_margins (n : ℕ) (hn : 1 ≤ n) (m : ℕ)
    (q : Fin m → ℕ) (hq : ∀ i, 2 ≤ q i) :
    let w := LogTwo.chosenWeights n hn m q hq
    let sigma := curveSigma w.theta m
    0 < sigma ∧ (1+sigma)*w.theta < 1 ∧
      (w.K : ℝ)*(1+3*(sigma : ℝ))^(m+1)*(∏ i, (rationalColumnWeight w i : ℝ))/
        (∏ i, (jetWeight w i : ℝ)) < 1 := by
  dsimp only
  let w := LogTwo.chosenWeights n hn m q hq
  exact ⟨curveSigma_pos w.theta_pos w.theta_lt_one m,
    curveSigma_contact_margin w.theta_pos w.theta_lt_one m,
    curveSigma_volume_lt_one w (chosenWeights_half_volume n hn m q hq)⟩

end
end LogTwo.Geometry
end Source0076

-- Source: LogTwo/Geometry/CurveCertificate.lean
section Source0077
-- Modified in this edition: unused plain lemmas removed; see reduction.json.
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

end
end LogTwo.Geometry
end Source0077

-- Source: LogTwo/Geometry/CoordinateKernel.lean
section Source0078
/-! A short height bound suffices for rigidity. The curve kernel lies strictly
inside the kernel of evaluation at a centered point; prime-chain length then
gives height <= m. No exact dimension formula for a curve quotient is required. -/
namespace LogTwo.Geometry
open OAI PiExponent PiExponentApprox
open CurveValuationCenter CurveCenters PlaceValuationRing PlaceCenteredBranch
noncomputable section
variable {E : Type*} [Field E] [Algebra ℂ E]

def coordinateKernel {n : ℕ} (z : Fin n → E) : Ideal (MvPolynomial (Fin n) ℂ) :=
  RingHom.ker (MvPolynomial.aeval z).toRingHom

instance coordinateKernel_isPrime {n : ℕ} (z : Fin n → E) : (coordinateKernel z).IsPrime :=
  RingHom.ker_isPrime _

@[simp] theorem mem_coordinateKernel {n : ℕ} (z : Fin n → E)
    (F : MvPolynomial (Fin n) ℂ) : F ∈ coordinateKernel z ↔ MvPolynomial.aeval z F = 0 :=
  Iff.rfl

/-- Evaluation at a centered point is the residue of evaluation in its valuation ring. -/
theorem eval_center_eq_zero_of_aeval_eq_zero {n : ℕ}
    (p : NormalizedPlace ℂ E)
    [Algebra.IsIntegral ℂ (IsLocalRing.ResidueField (ring p))]
    (z : Fin n → E) (a : Fin n → ℂ) (hc : Centered z a p)
    (F : MvPolynomial (Fin n) ℂ) (hF : MvPolynomial.aeval z F = 0) :
    MvPolynomial.aeval a F = 0 := by
  have hl : MvPolynomial.aeval (lift p z a hc) F = 0 := by
    apply IsFractionRing.injective (ring p) E
    rw [map_zero, lift_aeval]
    exact hF
  let φ : ring p →ₐ[ℂ] ℂ :=
    { toRingHom := CurveLocalOrder.residueAugmentation ℂ (ring p)
      commutes' := CurveLocalOrder.residueAugmentation_algebraMap ℂ (ring p) }
  have he := MvPolynomial.comp_aeval_apply (f := lift p z a hc) φ F
  have hφ : ∀ i, φ (lift p z a hc i) = a i := lift_residue p z a hc
  simpa only [hφ, hl, map_zero] using he.symm

theorem coordinateKernel_lt_pointKernel {n : ℕ}
    (p : NormalizedPlace ℂ E)
    [Algebra.IsIntegral ℂ (IsLocalRing.ResidueField (ring p))]
    (z : Fin n → E) (a : Fin n → ℂ) (hc : Centered z a p)
    (hnc : ∃ i, z i ≠ algebraMap ℂ E (a i)) :
    coordinateKernel z < coordinateKernel a := by
  apply lt_of_le_of_ne
  · intro F hF
    exact eval_center_eq_zero_of_aeval_eq_zero p z a hc F hF
  · intro he
    obtain ⟨i, hi⟩ := hnc
    have hmem : MvPolynomial.X i - MvPolynomial.C (a i) ∈ coordinateKernel a := by
      simp
    rw [← he] at hmem
    apply hi
    simpa only [mem_coordinateKernel, map_sub, MvPolynomial.aeval_X,
      MvPolynomial.aeval_C, sub_eq_zero] using hmem

/-- The upper bound needed by rigidity follows from one centered nonconstant branch. -/
theorem coordinateKernel_height_le {m : ℕ}
    (p : NormalizedPlace ℂ E)
    [Algebra.IsIntegral ℂ (IsLocalRing.ResidueField (ring p))]
    (z : Fin (m+1) → E) (a : Fin (m+1) → ℂ) (hc : Centered z a p)
    (hnc : ∃ i, z i ≠ algebraMap ℂ E (a i)) :
    (coordinateKernel z).height ≤ (m : ℕ∞) := by
  have hstep := Ideal.height_add_one_le_of_lt_of_isPrime
    (coordinateKernel_lt_pointKernel p z a hc hnc)
  have hdim := Ideal.height_le_ringKrullDim_of_isPrime (I := coordinateKernel a)
  have hpoint : (coordinateKernel a).height ≤ ((m : ℕ∞)+1) := by
    apply WithBot.coe_le_coe.mp
    simpa only [MvPolynomial.ringKrullDim_of_isNoetherianRing,
      ringKrullDim_eq_zero_of_field, zero_add, ENat.card_eq_coe_natCard,
      Nat.card_fin, Nat.cast_add, Nat.cast_one, WithBot.coe_add, WithBot.coe_one,
      WithBot.coe_natCast] using hdim
  exact (ENat.add_le_add_iff_right (by simp : (1 : ℕ∞) ≠ ⊤)).mp (hstep.trans hpoint)

theorem coordinateKernel_X_zero_not_mem {m : ℕ}
    (p : NormalizedPlace ℂ E) (z : Fin (m+1) → E) (a : Fin (m+1) → ℂ)
    (hc : Centered z a p) (ha : a 0 ≠ 0) :
    MvPolynomial.X (0 : Fin (m+1)) ∉ coordinateKernel z := by
  intro hmem
  have hz : z 0 = 0 := by simpa only [mem_coordinateKernel, MvPolynomial.aeval_X] using hmem
  have he := hc.constant_coordinate 0 0 (by simpa using hz)
  exact ha he.symm

end
end LogTwo.Geometry
end Source0078

-- Source: LogTwo/Geometry/RigidityInput.lean
section Source0079
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
end Source0079

-- Source: OAI/NumberTheory/PiExponent/Approximation/WeightSeparationProducts.lean
section Source0080
/-
Modification notice for the LogTwo project.
Derived from openai/math (Apache-2.0), revision adc7f1241b42e322a6451854ab7e4b4c146bf78a.
Original source: lean/OAI/NumberTheory/PiExponent/Approximation/WeightSeparationProducts.lean
Changes: Convert module/import declarations to the Lean 4.34 public module format.
See ../THIRD_PARTY_NOTICES.txt for provenance and the recorded changes.
-/

namespace OAI

namespace PiExponent

theorem product_dominance_of_lower_indices
    (x : ℕ → ℝ) (D : ℝ) (hx : ∀ j, 1 ≤ x j) (hD : 0 < D)
    (A B : Finset ℕ) (i : ℕ) (hiA : i ∈ A)
    (hB : ∀ j ∈ B, j < i)
    (hgrowth : D * (∏ j ∈ Finset.range i, x j) < x i) :
    D * (∏ j ∈ B, x j) < ∏ j ∈ A, x j := by
  have hxnonneg : ∀ j, 0 ≤ x j := fun j => le_trans zero_le_one (hx j)
  have hsub : B ⊆ Finset.range i := by
    intro j hj
    exact Finset.mem_range.mpr (hB j hj)
  have hprodB : (∏ j ∈ B, x j) ≤ ∏ j ∈ Finset.range i, x j :=
    Finset.prod_le_prod_of_subset_of_one_le₀ hsub
      (fun j _ => hxnonneg j) (fun j _ _ => hx j)
  have hprodA : x i ≤ ∏ j ∈ A, x j := by
    have hsubA : ({i} : Finset ℕ) ⊆ A := Finset.singleton_subset_iff.mpr hiA
    simpa only [Finset.prod_singleton] using
      (Finset.prod_le_prod_of_subset_of_one_le₀ hsubA
        (fun j _ => hxnonneg j) (fun j _ _ => hx j))
  exact lt_of_lt_of_le
    (lt_of_le_of_lt (mul_le_mul_of_nonneg_left hprodB hD.le) hgrowth) hprodA

theorem normalized_products_separated
    (x : ℕ → ℝ) (D : ℝ) (hx : ∀ j, 1 ≤ x j) (hD : 0 < D)
    (A B : Finset ℕ) (i : ℕ) (hiA : i ∈ A) (hiB : i ∉ B)
    (hB : ∀ j ∈ B \ A, j < i)
    (hgrowth : D * (∏ j ∈ Finset.range i, x j) < x i) :
    D * (∏ j ∈ B, x j) < ∏ j ∈ A, x j := by
  have hdiff : D * (∏ j ∈ B \ A, x j) < ∏ j ∈ A \ B, x j :=
    product_dominance_of_lower_indices x D hx hD (A \ B) (B \ A) i
      (Finset.mem_sdiff.mpr ⟨hiA, hiB⟩) hB hgrowth
  have hcommon : 0 < ∏ j ∈ A ∩ B, x j :=
    Finset.prod_pos (fun j _ => lt_of_lt_of_le zero_lt_one (hx j))
  calc
    D * (∏ j ∈ B, x j)
        = (∏ j ∈ A ∩ B, x j) * (D * (∏ j ∈ B \ A, x j)) := by
            rw [← Finset.prod_inter_mul_prod_sdiff B A x, Finset.inter_comm B A]
            ac_rfl
    _ < (∏ j ∈ A ∩ B, x j) * (∏ j ∈ A \ B, x j) :=
      mul_lt_mul_of_pos_left hdiff hcommon
    _ = ∏ j ∈ A, x j := Finset.prod_inter_mul_prod_sdiff A B x

end PiExponent

end OAI
end Source0080

-- Source: OAI/NumberTheory/PiExponent/Approximation/WeightSeparation.lean
section Source0081
/-
Modification notice for the LogTwo project.
Derived from openai/math (Apache-2.0), revision adc7f1241b42e322a6451854ab7e4b4c146bf78a.
Original source: lean/OAI/NumberTheory/PiExponent/Approximation/WeightSeparation.lean
Changes: Convert module/import declarations to the Lean 4.34 public module format.
See ../THIRD_PARTY_NOTICES.txt for provenance and the recorded changes.
-/

namespace OAI

namespace PiExponentApprox

noncomputable section

def geometricDegreeWeight (w0 : ℝ) (x : ℕ → ℝ) (i : ℕ) : ℝ :=
  if i = 0 then w0 else x i

def geometricJetWeight (v0 theta : ℝ) (x : ℕ → ℝ) (i : ℕ) : ℝ :=
  if i = 0 then v0 else x i / theta

def weightSeparationFactor (m : ℕ) (C w0 v0 theta : ℝ) : ℝ :=
  C * (max 1 (max v0 (1 / theta) / min w0 1)) ^ (m + 1)

theorem weightSeparationFactor_pos
    (m : ℕ) (C w0 v0 theta : ℝ) (hC : 0 < C) :
    0 < weightSeparationFactor m C w0 v0 theta := by
  unfold weightSeparationFactor
  have hbase : 0 < max 1 (max v0 (1 / theta) / min w0 1) :=
    lt_of_lt_of_le zero_lt_one (le_max_left _ _)
  exact mul_pos hC (pow_pos hbase _)

theorem geometric_weight_products_of_normalized
    (m : ℕ) (C w0 v0 theta : ℝ) (x : ℕ → ℝ)
    (hC : 0 < C) (hw0 : 0 < w0) (hv0 : 0 < v0) (htheta : 0 < theta)
    (hx0 : x 0 = 1) (hx : ∀ i, 1 ≤ x i)
    (A B : Finset ℕ) (hcard : A.card = B.card) (hbound : B.card ≤ m + 1)
    (hsep : weightSeparationFactor m C w0 v0 theta * (∏ i ∈ B, x i) <
      ∏ i ∈ A, x i) :
    C * (∏ i ∈ B, geometricJetWeight v0 theta x i) <
      ∏ i ∈ A, geometricDegreeWeight w0 x i := by
  let L : ℝ := min w0 1
  let R : ℝ := max v0 (1 / theta)
  let T : ℝ := max 1 (R / L)
  have hL : 0 < L := lt_min hw0 zero_lt_one
  have hR : 0 < R := lt_of_lt_of_le hv0 (le_max_left _ _)
  have hT : 1 ≤ T := le_max_left _ _
  have hxpos : ∀ i, 0 < x i := fun i => lt_of_lt_of_le zero_lt_one (hx i)
  have hdeg (i : ℕ) : L * x i ≤ geometricDegreeWeight w0 x i := by
    by_cases hi : i = 0
    · subst i
      simp only [geometricDegreeWeight, hx0, mul_one]
      exact min_le_left _ _
    · simp only [geometricDegreeWeight, ite_eq_right hi]
      exact mul_le_of_le_one_left (le_of_lt (hxpos i)) (min_le_right _ _)
  have hjet (i : ℕ) : geometricJetWeight v0 theta x i ≤ R * x i := by
    by_cases hi : i = 0
    · subst i
      simp only [geometricJetWeight, hx0, mul_one]
      exact le_max_left _ _
    · simp only [geometricJetWeight, ite_eq_right hi]
      calc
        x i / theta = (1 / theta) * x i := by ring
        _ ≤ R * x i := mul_le_mul_of_nonneg_right (le_max_right _ _)
          (le_of_lt (hxpos i))
  have hdegprod : L ^ A.card * (∏ i ∈ A, x i) ≤
      ∏ i ∈ A, geometricDegreeWeight w0 x i := by
    calc
      _ = ∏ i ∈ A, (L * x i) := by
        rw [Finset.prod_mul_distrib, Finset.prod_const]
      _ ≤ _ := Finset.prod_le_prod₀ (fun i _ => mul_nonneg (le_of_lt hL)
        (le_of_lt (hxpos i))) (fun i _ => hdeg i)
  have hjetnonneg (i : ℕ) : 0 ≤ geometricJetWeight v0 theta x i := by
    unfold geometricJetWeight
    split
    · exact le_of_lt hv0
    · exact div_nonneg (le_of_lt (hxpos i)) (le_of_lt htheta)
  have hjetprod : (∏ i ∈ B, geometricJetWeight v0 theta x i) ≤
      R ^ B.card * (∏ i ∈ B, x i) := by
    calc
      _ ≤ ∏ i ∈ B, (R * x i) := Finset.prod_le_prod₀
        (fun i _ => hjetnonneg i) (fun i _ => hjet i)
      _ = _ := by rw [Finset.prod_mul_distrib, Finset.prod_const]
  have hRle : R ≤ T * L := (div_le_iff₀ hL).mp (le_max_right _ _)
  have hpowers : R ^ B.card ≤ T ^ (m + 1) * L ^ B.card := by
    calc
      R ^ B.card ≤ (T * L) ^ B.card := pow_le_pow_left₀ (le_of_lt hR) hRle _
      _ = T ^ B.card * L ^ B.card := mul_pow _ _ _
      _ ≤ T ^ (m + 1) * L ^ B.card := mul_le_mul_of_nonneg_right
        (pow_le_pow_right₀ hT hbound) (pow_nonneg (le_of_lt hL) _)
  have hprodB : 0 ≤ ∏ i ∈ B, x i := Finset.prod_nonneg fun i _ => le_of_lt (hxpos i)
  calc
    C * (∏ i ∈ B, geometricJetWeight v0 theta x i) ≤
        C * (R ^ B.card * (∏ i ∈ B, x i)) :=
      mul_le_mul_of_nonneg_left hjetprod (le_of_lt hC)
    _ ≤ C * ((T ^ (m + 1) * L ^ B.card) * (∏ i ∈ B, x i)) :=
      mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_right hpowers hprodB) (le_of_lt hC)
    _ = L ^ A.card * (weightSeparationFactor m C w0 v0 theta *
          (∏ i ∈ B, x i)) := by
      rw [hcard]
      change C * ((T ^ (m + 1) * L ^ B.card) * (∏ i ∈ B, x i)) =
        L ^ B.card * ((C * T ^ (m + 1)) * (∏ i ∈ B, x i))
      ring
    _ < L ^ A.card * (∏ i ∈ A, x i) :=
      mul_lt_mul_of_pos_left hsep (pow_pos hL _)
    _ ≤ _ := hdegprod

def SeparatedWeightGrowth (m : ℕ) (D : ℝ) (x : ℕ → ℝ) : Prop :=
  ∀ i, 0 < i → i ≤ m → D * (∏ j ∈ Finset.range i, x j) < x i

theorem geometric_weight_products_separated
    (m : ℕ) (C w0 v0 theta : ℝ) (x : ℕ → ℝ)
    (hC : 0 < C) (hw0 : 0 < w0) (hv0 : 0 < v0) (htheta : 0 < theta)
    (hx0 : x 0 = 1) (hx : ∀ i, 1 ≤ x i)
    (hgrowth : SeparatedWeightGrowth m (weightSeparationFactor m C w0 v0 theta) x)
    (A B : Finset ℕ) (hcard : A.card = B.card)
    (hA : A ⊆ Finset.range (m + 1)) (hB : B ⊆ Finset.range (m + 1))
    (i : ℕ) (hi : 0 < i) (hiA : i ∈ A) (hiB : i ∉ B)
    (hbelow : ∀ j ∈ B \ A, j < i) :
    C * (∏ j ∈ B, geometricJetWeight v0 theta x j) <
      ∏ j ∈ A, geometricDegreeWeight w0 x j := by
  have hibound : i ≤ m := Nat.le_of_lt_succ (Finset.mem_range.mp (hA hiA))
  have hcardbound : B.card ≤ m + 1 := by
    simpa only [Finset.card_range] using Finset.card_le_card hB
  apply geometric_weight_products_of_normalized m C w0 v0 theta x
    hC hw0 hv0 htheta hx0 hx A B hcard hcardbound
  exact PiExponent.normalized_products_separated x
    (weightSeparationFactor m C w0 v0 theta) hx
    (weightSeparationFactor_pos m C w0 v0 theta hC)
    A B i hiA hiB hbelow (hgrowth i hi hibound)

end
end PiExponentApprox

end OAI
end Source0081

-- Source: LogTwo/Geometry/SeparatedWeights.lean
section Source0082
/-
Modification notice for the LogTwo project.
Adapted from openai/math (Apache-2.0), revision adc7f1241b42e322a6451854ab7e4b4c146bf78a.
Changes: Adapt the finite-index conversion to the log-two separated weights.
See ../THIRD_PARTY_NOTICES.txt for provenance and the recorded changes.
-/

/-! Product separation for the actual matrix weights. The finite-index conversion
adapts Geometry/AdmissibleCurveWeights.lean from pinned openai/math (Apache-2.0).
The growth condition depends only on earlier denominators. -/
namespace LogTwo.Geometry
open OAI PiExponent PiExponentApprox LogTwo.Interpolation
noncomputable section

def SeparatedProducts {m : ℕ} (w cost : Fin (m+1) → ℝ) (M : ℝ) : Prop :=
  ∀ A B : Finset (Fin (m+1)), A.card = B.card →
    ∀ i, i ≠ 0 → i ∈ A → i ∉ B →
    (∀ j, i < j → (j ∈ A ↔ j ∈ B)) →
    M * (∏ j ∈ B, cost j) < ∏ j ∈ A, w j

theorem separatedProducts_of_growth {m : ℕ} (w : Weights m) (M : ℝ) (hM : 0 < M)
    (x : ℕ → ℝ) (hx0 : x 0 = 1) (hx : ∀ i, 1 ≤ x i)
    (hmatch : ∀ i : Fin m, x (i.val+1) = (w.w i : ℝ))
    (hgrowth : SeparatedWeightGrowth m
      (weightSeparationFactor m M w.w0 w.v0 w.theta) x) :
    SeparatedProducts (columnWeight w) (fun i => (jetWeight w i : ℝ)) M := by
  classical
  intro A B hcard i hi hiA hiB hhigh
  let e : Fin (m+1) ↪ ℕ := ⟨Fin.val, Fin.val_injective⟩
  have hbound (S : Finset (Fin (m+1))) : S.map e ⊆ Finset.range (m+1) := by
    intro j hj
    obtain ⟨k, hk, rfl⟩ := Finset.mem_map.mp hj
    exact Finset.mem_range.mpr k.isLt
  have hbelow : ∀ j ∈ B.map e \ A.map e, j < i.val := by
    intro j hj
    obtain ⟨hjB, hjA⟩ := Finset.mem_sdiff.mp hj
    obtain ⟨k, hkB, rfl⟩ := Finset.mem_map.mp hjB
    by_contra hnot
    have hik : i ≤ k := Fin.le_iff_val_le_val.mpr (Nat.le_of_not_gt hnot)
    have hne : i ≠ k := fun h => hiB (h.symm ▸ hkB)
    have hkA := (hhigh k (lt_of_le_of_ne hik hne)).mpr hkB
    exact hjA (Finset.mem_map.mpr ⟨k, hkA, rfl⟩)
  have hn : 0 < i.val := Nat.pos_of_ne_zero (fun h => hi (Fin.ext h))
  have h := geometric_weight_products_separated m M w.w0 w.v0 w.theta x hM
    (by exact_mod_cast w.w0_pos) (by exact_mod_cast w.v0_pos)
    (by exact_mod_cast w.theta_pos) hx0 hx hgrowth (A.map e) (B.map e)
    (by simpa using hcard) (hbound A) (hbound B) i.val hn
    (Finset.mem_map.mpr ⟨i, hiA, rfl⟩)
    (by
      intro hmem
      obtain ⟨a, haB, hai⟩ := Finset.mem_map.mp hmem
      exact hiB ((Fin.ext hai : a = i) ▸ haB)) hbelow
  have hw (j : Fin (m+1)) :
      geometricDegreeWeight w.w0 x j.val = columnWeight w j := by
    refine Fin.cases ?_ (fun k => ?_) j
    · simp [geometricDegreeWeight, columnWeight, InterpolationMatrix.columnWeights]
    · simp [geometricDegreeWeight, columnWeight, InterpolationMatrix.columnWeights, hmatch]
  have hv (j : Fin (m+1)) :
      geometricJetWeight w.v0 w.theta x j.val = (jetWeight w j : ℝ) := by
    refine Fin.cases ?_ (fun k => ?_) j
    · simp [geometricJetWeight, jetWeight]
    · simp [geometricJetWeight, jetWeight, hmatch]
  simpa only [Finset.prod_map, e, Function.Embedding.coeFn_mk, hw, hv] using h

/-- Index zero is the normalized horizontal coordinate; denominator i is at i+1. -/
def normalizedLogWeights (q : ℕ → ℕ) : ℕ → ℝ :=
  fun i => Nat.casesOn i 1 (fun j => (Arithmetic.ceilLogWeight (q j) : ℝ))

theorem normalizedLogWeights_one_le (q : ℕ → ℕ) (hq : ∀ i, 2 ≤ q i) :
    ∀ i, 1 ≤ normalizedLogWeights q i := by
  intro i
  cases i with
  | zero => exact le_rfl
  | succ i =>
    have h := ceilLogWeight_pos (hq i)
    change (0 : ℚ) < (⌈Real.log (q i : ℝ)⌉₊ : ℚ) at h
    have hn : 1 ≤ ⌈Real.log (q i : ℝ)⌉₊ := by exact_mod_cast h
    change (1 : ℝ) ≤ ((⌈Real.log (q i : ℝ)⌉₊ : ℚ) : ℝ)
    exact_mod_cast hn

theorem normalizedLogWeights_prod (q : ℕ → ℕ) (i : ℕ) :
    (∏ j ∈ Finset.range (i+1), normalizedLogWeights q j) =
      ∏ j : Fin i, (Arithmetic.ceilLogWeight (q j) : ℝ) := by
  rw [Finset.prod_range_succ']
  simp [normalizedLogWeights]
  exact (Fin.prod_univ_eq_prod_range _ _).symm

end
end LogTwo.Geometry
end Source0082

-- Source: OAI/NumberTheory/PiExponent/Analysis/LogarithmicObstruction.lean
section Source0083
-- Modified in this edition: unused plain lemmas removed; see reduction.json.
/-
Modification notice for the LogTwo project.
Derived from openai/math (Apache-2.0), revision adc7f1241b42e322a6451854ab7e4b4c146bf78a.
Original source: lean/OAI/NumberTheory/PiExponent/Analysis/LogarithmicObstruction.lean
Changes: Convert module/import declarations to the Lean 4.34 public module format.
See ../THIRD_PARTY_NOTICES.txt for provenance and the recorded changes.
-/

namespace OAI

noncomputable section

namespace PiExponent

open scoped LaurentSeries Matrix

open Polynomial

theorem polynomial_logarithmic_equation_impossible {K : Type*} [Field K] [CharZero K]
    (P Q : K[X]) (hQ : Q ≠ 0) (hcop : IsCoprime P Q) {c : K} (hc : c ≠ 0) :
    X * (derivative P * Q - P * derivative Q) ≠ C c * Q ^ 2 := by
  intro heq
  obtain ⟨U, hfactor, hU⟩ := Q.exists_eq_pow_rootMultiplicity_mul_and_not_dvd hQ 0
  simp only [map_zero, sub_zero] at hfactor hU
  have hU0 : U.coeff 0 ≠ 0 := fun h => hU (X_dvd_iff.mpr h)
  cases hn : Q.rootMultiplicity 0 with
  | zero =>
      have hQ0 : Q.coeff 0 ≠ 0 := by
        rw [hfactor, hn]
        simpa using hU0
      have hconst := congrArg (fun f : K[X] => f.coeff 0) heq
      have hz : c * (Q.coeff 0) ^ 2 = 0 := by simpa [pow_two] using hconst.symm
      exact (mul_ne_zero hc (pow_ne_zero _ hQ0)) hz
  | succ n =>
      have hQfactor : Q = X ^ (n + 1) * U := by simpa [hn] using hfactor
      have hQ0 : Q.coeff 0 = 0 := by simp [hQfactor]
      have hP0 : P.coeff 0 ≠ 0 := by
        intro hp
        obtain ⟨A, B, hab⟩ := hcop
        have hconst := congrArg (fun f : K[X] => f.coeff 0) hab
        simp [hp, hQ0] at hconst
      have hcancel :
          X * derivative P * U - P * (C (n + 1 : K) * U + X * derivative U) =
            C c * X ^ (n + 1) * U ^ 2 := by
        apply mul_left_cancel₀ (pow_ne_zero (n + 1) (X_ne_zero (R := K)))
        calc
          X ^ (n + 1) *
              (X * derivative P * U - P * (C (n + 1 : K) * U + X * derivative U)) =
              X * (derivative P * Q - P * derivative Q) := by
                rw [hQfactor, derivative_mul, derivative_X_pow_succ]
                ring
          _ = C c * Q ^ 2 := heq
          _ = X ^ (n + 1) * (C c * X ^ (n + 1) * U ^ 2) := by rw [hQfactor]; ring
      have hconst := congrArg (fun f : K[X] => f.coeff 0) hcancel
      have hz : P.coeff 0 * ((n + 1 : K) * U.coeff 0) = 0 := by
        simpa using hconst
      exact (mul_ne_zero hP0 (mul_ne_zero (Nat.cast_add_one_ne_zero n) hU0)) hz

theorem ratFunc_derivation_polynomial {K : Type*} [Field K]
    (D : Derivation K (RatFunc K) (RatFunc K))
    (hDX : D RatFunc.X = 1) (p : K[X]) :
    D (algebraMap K[X] (RatFunc K) p) =
      algebraMap K[X] (RatFunc K) (derivative p) := by
  simpa [RatFunc.aeval_X_left_eq_algebraMap, hDX] using D.comp_aeval_eq RatFunc.X p

theorem ratFunc_derivation_ne_simple_pole {K : Type*} [Field K] [CharZero K]
    (D : Derivation K (RatFunc K) (RatFunc K))
    (hDX : D RatFunc.X = 1) (r : RatFunc K) {c : K} (hc : c ≠ 0) :
    D r ≠ RatFunc.C c / RatFunc.X := by
  intro heq
  have hquot := D.leibniz_div (algebraMap K[X] (RatFunc K) r.num)
    (algebraMap K[X] (RatFunc K) r.denom)
  rw [RatFunc.num_div_denom, ratFunc_derivation_polynomial D hDX,
    ratFunc_derivation_polynomial D hDX] at hquot
  have hder : D r =
      algebraMap K[X] (RatFunc K) (derivative r.num * r.denom - r.num * derivative r.denom) /
        (algebraMap K[X] (RatFunc K) r.denom) ^ 2 := by
    rw [hquot]
    simp only [smul_eq_mul, map_sub, map_mul, div_eq_mul_inv, inv_pow]
    ring
  have hden : algebraMap K[X] (RatFunc K) r.denom ≠ 0 :=
    RatFunc.algebraMap_ne_zero r.denom_ne_zero
  have hx : (RatFunc.X : RatFunc K) ≠ 0 := by
    rw [← RatFunc.algebraMap_X]
    exact RatFunc.algebraMap_ne_zero X_ne_zero
  have hcross := (div_eq_div_iff (pow_ne_zero 2 hden) hx).mp (hder.symm.trans heq)
  apply polynomial_logarithmic_equation_impossible r.num r.denom r.denom_ne_zero
    r.isCoprime_num_denom hc
  apply RatFunc.algebraMap_injective K
  simpa only [map_mul, map_pow, RatFunc.algebraMap_X, RatFunc.algebraMap_C, mul_comm] using hcross

theorem derivation_intermediate_smul
    {k F E : Type*} [Field k] [Field F] [Field E]
    [Algebra k F] [Algebra k E] [Algebra F E] [IsScalarTower k F E]
    (d : Derivation k F F) (D : Derivation k E E)
    (hcompat : ∀ a : F, D (algebraMap F E a) = algebraMap F E (d a))
    (a : F) (z : E) : D (a • z) = d a • z + a • D z := by
  rw [Algebra.smul_def, D.leibniz, hcompat]
  simp only [smul_eq_mul, Algebra.smul_def]
  ring

theorem derivation_basis_coordinates
    {k F E ι : Type*} [Field k] [Field F] [Field E] [Fintype ι]
    [Algebra k F] [Algebra k E] [Algebra F E] [IsScalarTower k F E]
    (d : Derivation k F F) (D : Derivation k E E)
    (hcompat : ∀ a : F, D (algebraMap F E a) = algebraMap F E (d a))
    (b : Module.Basis ι F E) (z : E) (i : ι) :
    b.repr (D z) i = d (b.repr z i) +
      ∑ j, b.repr z j * b.repr (D (b j)) i := by
  classical
  conv_lhs => rw [← b.sum_repr z]
  simp only [map_sum, derivation_intermediate_smul d D hcompat, map_add,
    map_smul, Finset.sum_add_distrib, Finsupp.coe_add, Pi.add_apply,
    Finsupp.coe_finsetSum, Finset.sum_apply, Finsupp.coe_smul, Pi.smul_apply, smul_eq_mul]
  simp [Finsupp.single_apply, eq_comm]

theorem derivation_trace_of_basis
    {k F E ι : Type*} [Field k] [Field F] [Field E] [Fintype ι]
    [Algebra k F] [Algebra k E] [Algebra F E] [IsScalarTower k F E]
    (d : Derivation k F F) (D : Derivation k E E)
    (hcompat : ∀ a : F, D (algebraMap F E a) = algebraMap F E (d a))
    (b : Module.Basis ι F E) (x : E) :
    d (Algebra.trace F E x) = Algebra.trace F E (D x) := by
  classical
  let M := Algebra.leftMulMatrix b x
  let N : Matrix ι ι F := fun i j => b.repr (D (b j)) i
  have hentry (i j : ι) :
      Algebra.leftMulMatrix b (D x) i j + (M * N) i j =
        d (M i j) + (N * M) i j := by
    have hMN : (M * N) i j = ∑ t, M i t * N t j := rfl
    have hNM : (N * M) i j = ∑ t, N i t * M t j := rfl
    have hz := derivation_basis_coordinates d D hcompat b (x * b j) i
    have hm := congrFun (Algebra.leftMulMatrix_mulVec_repr b x (D (b j))) i
    have hl : b.repr (D (x * b j)) i =
        Algebra.leftMulMatrix b (D x) i j + (M * N) i j := by
      rw [hMN, D.leibniz]
      simp only [smul_eq_mul, map_add, Finsupp.add_apply]
      rw [← hm]
      simp only [M, N, Algebra.leftMulMatrix_eq_repr_mul,
        Matrix.mulVec, dotProduct, mul_comm, add_comm]
    rw [hl] at hz
    simpa only [hNM, M, N, Algebra.leftMulMatrix_eq_repr_mul, mul_comm] using hz
  have hs := Finset.sum_congr rfl (fun i (_ : i ∈ Finset.univ) => hentry i i)
  have ht : Matrix.trace (Algebra.leftMulMatrix b (D x)) + Matrix.trace (M * N) =
      d (Matrix.trace M) + Matrix.trace (N * M) := by
    simpa only [Matrix.trace, Matrix.diag_apply, Finset.sum_add_distrib, map_sum] using hs
  rw [Matrix.trace_mul_comm M N] at ht
  have ht' := add_right_cancel ht
  simpa only [Algebra.trace_eq_matrix_trace b, M] using ht'.symm

theorem finite_extension_derivation_ne_simple_pole
    {K E : Type*} [Field K] [CharZero K] [Field E]
    [Algebra K E] [Algebra (RatFunc K) E] [IsScalarTower K (RatFunc K) E]
    [FiniteDimensional (RatFunc K) E]
    (d : Derivation K (RatFunc K) (RatFunc K)) (D : Derivation K E E)
    (hdX : d RatFunc.X = 1)
    (hcompat : ∀ a : RatFunc K,
      D (algebraMap (RatFunc K) E a) = algebraMap (RatFunc K) E (d a))
    (x : E) {c : K} (hc : c ≠ 0) :
    D x ≠ algebraMap (RatFunc K) E (RatFunc.C c / RatFunc.X) := by
  intro hx
  have ht := derivation_trace_of_basis d D hcompat
    (Module.finBasis (RatFunc K) E) x
  rw [hx, Algebra.trace_algebraMap] at ht
  have hdegree : (Module.finrank (RatFunc K) E : K) ≠ 0 := by
    exact Nat.cast_ne_zero.mpr (ne_of_gt (Module.finrank_pos (R := RatFunc K) (M := E)))
  apply ratFunc_derivation_ne_simple_pole d hdX (Algebra.trace (RatFunc K) E x)
    (mul_ne_zero hdegree hc)
  calc
    d (Algebra.trace (RatFunc K) E x) =
        Module.finrank (RatFunc K) E • (RatFunc.C c / RatFunc.X) := ht
    _ = RatFunc.C ((Module.finrank (RatFunc K) E : K) * c) / RatFunc.X := by
      simp only [map_mul, map_natCast, nsmul_eq_mul, mul_div_assoc]

end PiExponent

end

end OAI
end Source0083

-- Source: OAI/NumberTheory/PiExponent/LocalAlgebra/TranscendenceBasisReduction.lean
section Source0084
/-
Modification notice for the LogTwo project.
Derived from openai/math (Apache-2.0), revision adc7f1241b42e322a6451854ab7e4b4c146bf78a.
Original source: lean/OAI/NumberTheory/PiExponent/LocalAlgebra/TranscendenceBasisReduction.lean
Changes: Convert module/import declarations to the Lean 4.34 public module format.
See ../THIRD_PARTY_NOTICES.txt for provenance and the recorded changes.
-/

namespace OAI

noncomputable section

namespace PiExponent

open scoped IntermediateField.algebraAdjoinAdjoin

theorem exists_intermediateField_finite_over_simple
    (C E : Type*) [Field C] [Field E] [Algebra C E]
    [Algebra.EssFiniteType C E] {Y : E} (hY : Transcendental C Y) :
    ∃ K : IntermediateField C E,
      Transcendental K Y ∧ FiniteDimensional (IntermediateField.adjoin K {Y}) E := by
  classical
  have hsingle : AlgebraicIndepOn C id ({Y} : Set E) := by
    change AlgebraicIndependent C (fun z : ({Y} : Set E) => (z : E))
    rw [algebraicIndependent_singleton_iff ⟨Y, rfl⟩]
    exact hY
  obtain ⟨t, hsub, ht⟩ := exists_isTranscendenceBasis_superset hsingle
  have hYt : Y ∈ t := hsub (Set.mem_singleton Y)
  let s : Set E := t \ {Y}
  let K : IntermediateField C E := IntermediateField.adjoin C s
  have hts : insert Y s = t := by
    ext x
    simp only [s, Set.mem_insert_iff, Set.mem_sdiff, Set.mem_singleton_iff]
    constructor
    · rintro (rfl | ⟨hx, _⟩)
      · exact hYt
      · exact hx
    · intro hx
      by_cases heq : x = Y
      · exact Or.inl heq
      · exact Or.inr ⟨hx, heq⟩
  have hind : AlgebraicIndepOn C id (insert Y s) := by
    rw [hts]
    exact ht.1
  have htr : Transcendental (Algebra.adjoin C s) Y := by
    have hnot : Y ∉ s := by simp [s]
    have hh := (AlgebraicIndepOn.insert_iff hnot).mp hind
    have heq : id '' s = s := Set.image_id s
    rw [heq] at hh
    exact hh.2
  have htrK : Transcendental K Y := by
    intro h
    exact htr (h.restrictScalars (Algebra.adjoin C s))
  refine ⟨K, htrK, ?_⟩
  let L := IntermediateField.adjoin K ({Y} : Set E)
  have hL : L.restrictScalars C = IntermediateField.adjoin C t := by
    dsimp [L, K]
    rw [IntermediateField.adjoin_adjoin_left]
    congr 1
    rw [Set.union_comm, Set.singleton_union, hts]
  have halg : Algebra.IsAlgebraic L E := by
    change Algebra.IsAlgebraic (L.restrictScalars C) E
    rw [hL]
    have hh := ht.isAlgebraic_field
    have heq : Set.range ((↑) : t → E) = t := Subtype.range_coe
    rw [heq] at hh
    exact hh
  let : Algebra.IsAlgebraic L E := halg
  let : IsScalarTower C L E := IsScalarTower.of_algebraMap_eq (fun x => rfl)
  let : Algebra.EssFiniteType L E := Algebra.EssFiniteType.of_comp C L E
  exact Algebra.finite_of_essFiniteType_of_isAlgebraic

end PiExponent

end

end OAI
end Source0084

-- Source: OAI/NumberTheory/PiExponent/Analysis/AlgebraicLogarithmicObstruction.lean
section Source0085
/-
Modification notice for the LogTwo project.
Derived from openai/math (Apache-2.0), revision adc7f1241b42e322a6451854ab7e4b4c146bf78a.
Original source: lean/OAI/NumberTheory/PiExponent/Analysis/AlgebraicLogarithmicObstruction.lean
Changes: Convert module/import declarations to the Lean 4.34 public module format.
See ../THIRD_PARTY_NOTICES.txt for provenance and the recorded changes.
-/

namespace OAI

noncomputable section

namespace PiExponent

open KaehlerDifferential
open scoped TensorProduct Polynomial nonZeroDivisors IntermediateField

def extendDerivation
    {R S T : Type*} [CommRing R] [CommRing S] [CommRing T]
    [Algebra R S] [Algebra R T] [Algebra S T] [IsScalarTower R S T]
    [Algebra.FormallyEtale S T]
    (d : Derivation R S S) : Derivation R T T :=
  ((LinearMap.liftBaseChange T ((Algebra.linearMap S T).comp d.liftKaehlerDifferential)).comp
    (tensorKaehlerEquivOfFormallyEtale R S T).symm.toLinearMap).compDer (D R T)

theorem extendDerivation_algebraMap
    {R S T : Type*} [CommRing R] [CommRing S] [CommRing T]
    [Algebra R S] [Algebra R T] [Algebra S T] [IsScalarTower R S T]
    [Algebra.FormallyEtale S T]
    (d : Derivation R S S) (s : S) :
    extendDerivation (T := T) d (algebraMap S T s) = algebraMap S T (d s) := by
  simp [extendDerivation, LinearMap.compDer,
    tensorKaehlerEquivOfFormallyEtale_symm_D_algebraMap,
    Derivation.liftKaehlerDifferential_comp_D]

def ratFuncDerivative {K : Type*} [Field K] : Derivation K (RatFunc K) (RatFunc K) := by
  letI : Algebra.FormallyEtale K[X] (RatFunc K) :=
    Algebra.FormallyEtale.of_isLocalization (K[X]⁰)
  exact extendDerivation Polynomial.derivative'

@[simp]
theorem ratFuncDerivative_X {K : Type*} [Field K] :
    ratFuncDerivative (RatFunc.X : RatFunc K) = 1 := by
  let : Algebra.FormallyEtale K[X] (RatFunc K) :=
    Algebra.FormallyEtale.of_isLocalization (K[X]⁰)
  change extendDerivation Polynomial.derivative' (RatFunc.X : RatFunc K) = 1
  rw [← RatFunc.algebraMap_X, extendDerivation_algebraMap]
  simp [Polynomial.derivative']

theorem finite_extension_no_logarithmic_differential
    {K E : Type*} [Field K] [CharZero K] [Field E]
    [Algebra K E] [Algebra (RatFunc K) E] [IsScalarTower K (RatFunc K) E]
    [FiniteDimensional (RatFunc K) E] (x : E) :
    D K E x ≠ (algebraMap (RatFunc K) E RatFunc.X)⁻¹ •
      D K E (algebraMap (RatFunc K) E RatFunc.X) := by
  let : Algebra.FormallyEtale (RatFunc K) E :=
    Algebra.FormallyEtale.of_isSeparable (RatFunc K) E
  let delta : Derivation K E E := extendDerivation ratFuncDerivative
  have hcompat (a : RatFunc K) :
      delta (algebraMap (RatFunc K) E a) =
        algebraMap (RatFunc K) E (ratFuncDerivative a) :=
    extendDerivation_algebraMap ratFuncDerivative a
  intro heq
  have hd := congrArg delta.liftKaehlerDifferential heq
  simp only [Derivation.liftKaehlerDifferential_comp_D, map_smul, hcompat,
    ratFuncDerivative_X, map_one, smul_eq_mul, mul_one] at hd
  apply finite_extension_derivation_ne_simple_pole ratFuncDerivative delta
    ratFuncDerivative_X hcompat x (c := (1 : K)) one_ne_zero
  simpa only [map_div₀, map_one, one_div, map_inv₀] using hd

theorem adjoin_finite_no_logarithmic_differential
    {K E : Type*} [Field K] [CharZero K] [Field E] [Algebra K E]
    (y : E) (hy : Transcendental K y) [FiniteDimensional K⟮y⟯ E] (x : E) :
    D K E x ≠ y⁻¹ • D K E y := by
  let F := K⟮y⟯
  let e : RatFunc K ≃ₐ[K] F := RatFunc.algEquivOfTranscendental y hy
  let : Algebra (RatFunc K) F := e.toRingHom.toAlgebra
  let : Algebra (RatFunc K) E :=
    ((algebraMap F E).comp e.toRingHom).toAlgebra
  let : IsScalarTower (RatFunc K) F E := IsScalarTower.of_algebraMap_eq' rfl
  let : IsScalarTower K (RatFunc K) E := IsScalarTower.of_algebraMap_eq fun a => by
    change algebraMap K E a = algebraMap F E (e (algebraMap K (RatFunc K) a))
    rw [e.commutes]
    exact IsScalarTower.algebraMap_apply K F E a
  have : Module.Finite (RatFunc K) F :=
    Module.Finite.of_surjective (Algebra.linearMap (RatFunc K) F) e.surjective
  have : Module.Finite (RatFunc K) E := Module.Finite.trans F E
  have hX : algebraMap (RatFunc K) E RatFunc.X = y := by
    change ((RatFunc.algEquivOfTranscendental y hy) RatFunc.X : E) = y
    exact RatFunc.algEquivOfTranscendental_X y hy
  simpa only [hX] using finite_extension_no_logarithmic_differential (K := K) x

theorem logarithmic_differential_base_change
    {C K E : Type*} [Field C] [Field K] [Field E]
    [Algebra C K] [Algebra C E] [Algebra K E] [IsScalarTower C K E]
    {x y : E} (h : D C E x = y⁻¹ • D C E y) :
    D K E x = y⁻¹ • D K E y := by
  have hm := congrArg (KaehlerDifferential.map C K E E) h
  simpa only [map_D, map_smul, Algebra.algebraMap_self, RingHom.id_apply] using hm

theorem no_logarithmic_differential_over_intermediateField
    {C E : Type*} [Field C] [CharZero C] [Field E] [Algebra C E]
    (K : IntermediateField C E) (y : E) (hy : Transcendental K y)
    [FiniteDimensional K⟮y⟯ E] (x : E) :
    D C E x ≠ y⁻¹ • D C E y := by
  intro h
  exact adjoin_finite_no_logarithmic_differential y hy x
    (logarithmic_differential_base_change (K := K) h)

theorem isAlgebraic_of_logarithmic_differential
    {C E : Type*} [Field C] [CharZero C] [Field E] [Algebra C E]
    [Algebra.EssFiniteType C E] (x y : E)
    (h : D C E x = y⁻¹ • D C E y) : IsAlgebraic C y := by
  by_contra hy
  obtain ⟨K, hKy, hfinite⟩ := exists_intermediateField_finite_over_simple C E hy
  have : FiniteDimensional K⟮y⟯ E := hfinite
  exact no_logarithmic_differential_over_intermediateField K y hKy x h

theorem constant_of_logarithmic_differential
    {C E : Type*} [Field C] [CharZero C] [IsAlgClosed C] [Field E] [Algebra C E]
    [Algebra.EssFiniteType C E] (x y : E)
    (h : D C E x = y⁻¹ • D C E y) : ∃ c : C, algebraMap C E c = y := by
  have hy := isAlgebraic_of_logarithmic_differential x y h
  have hmem : y ∈ algebraicClosure C E := mem_algebraicClosure_iff.mpr hy
  rw [IntermediateField.eq_bot_of_isAlgClosed_of_isAlgebraic (algebraicClosure C E)] at hmem
  exact IntermediateField.mem_bot.mp hmem

end PiExponent

end

end OAI
end Source0085

-- Source: OAI/NumberTheory/PiExponent/Jets/DifferentialConstant.lean
section Source0086
-- Modified in this edition: unused plain lemmas removed; see reduction.json.
/-
Modification notice for the LogTwo project.
Derived from openai/math (Apache-2.0), revision adc7f1241b42e322a6451854ab7e4b4c146bf78a.
Original source: lean/OAI/NumberTheory/PiExponent/Jets/DifferentialConstant.lean
Changes: Convert module/import declarations to the Lean 4.34 public module format.
See ../THIRD_PARTY_NOTICES.txt for provenance and the recorded changes.
-/

namespace OAI

namespace PiExponent

open KaehlerDifferential

theorem constant_of_differential_eq_zero
    {C E : Type*} [Field C] [CharZero C] [IsAlgClosed C] [Field E] [Algebra C E]
    [Algebra.EssFiniteType C E] (x : E) (hx : D C E x = 0) :
    ∃ c : C, algebraMap C E c = x :=
  constant_of_logarithmic_differential (0 : E) x (by simp [hx])

end PiExponent

end OAI
end Source0086

-- Source: OAI/NumberTheory/PiExponent/Jets/NormalBasisRigidity.lean
section Source0087
-- Modified in this edition: unused plain lemmas removed; see reduction.json.
/-
Modification notice for the LogTwo project.
Derived from openai/math (Apache-2.0), revision adc7f1241b42e322a6451854ab7e4b4c146bf78a.
Original source: lean/OAI/NumberTheory/PiExponent/Jets/NormalBasisRigidity.lean
Changes: Convert module/import declarations to the Lean 4.34 public module format.
See ../THIRD_PARTY_NOTICES.txt for provenance and the recorded changes.
-/

namespace OAI

noncomputable section

namespace PiExponent.NormalBasisRigidity

open Set Submodule Module

variable {K V ι : Type*} [Field K] [AddCommGroup V] [Module K V]

def IsNormalBasis (v : ι → V) (A : Finset ι) : Prop :=
  LinearIndepOn K v (A : Set ι) ∧ span K (v '' (A : Set ι)) = ⊤

lemma exists_normalBasis_subset [Fintype ι] (v : ι → V) (S : Set ι)
    (hS : span K (v '' S) = ⊤) :
    ∃ A : Finset ι, (A : Set ι) ⊆ S ∧ IsNormalBasis (K := K) v A := by
  classical
  let h := linearIndepOn_empty K v
  let A := h.extend (Set.empty_subset S)
  refine ⟨A.toFinset, ?_, ?_, ?_⟩
  · simpa only [Set.coe_toFinset] using h.extend_subset (Set.empty_subset S)
  · simpa only [Set.coe_toFinset] using h.linearIndepOn_extend (Set.empty_subset S)
  · simpa only [Set.coe_toFinset, A] using
      (h.span_image_extend_eq_span_image (Set.empty_subset S)).trans hS

lemma exists_normalBasis_containing [Fintype ι] (v : ι → V)
    (hv : span K (Set.range v) = ⊤) (i : ι) (hi : v i ≠ 0) :
    ∃ A : Finset ι, i ∈ A ∧ IsNormalBasis (K := K) v A := by
  classical
  have h : LinearIndepOn K v ({i} : Set ι) := by
    exact LinearIndepOn.singleton hi
  let A := h.extend (Set.subset_univ _)
  refine ⟨A.toFinset, ?_, ?_, ?_⟩
  · exact Set.mem_toFinset.mpr (h.subset_extend (Set.subset_univ _) (Set.mem_singleton i))
  · simpa only [Set.coe_toFinset] using h.linearIndepOn_extend (Set.subset_univ _)
  · simpa only [Set.coe_toFinset, Set.image_univ, A] using
      (h.span_image_extend_eq_span_image (Set.subset_univ _)).trans (by simpa using hv)

lemma IsNormalBasis.ne_zero [DecidableEq ι] {v : ι → V} {A : Finset ι}
    (hA : IsNormalBasis (K := K) v A) {i : ι} (hi : i ∈ A) : v i ≠ 0 :=
  hA.1.ne_zero hi

lemma exists_normalBasis_omitting [Fintype ι] (v : ι → V) (i : ι)
    (h : span K (v '' {j | j ≠ i}) = ⊤) :
    ∃ A : Finset ι, i ∉ A ∧ IsNormalBasis (K := K) v A := by
  obtain ⟨A, hA, hB⟩ := exists_normalBasis_subset v {j | j ≠ i} h
  exact ⟨A, fun hi => hA hi rfl, hB⟩

lemma mandatory_not_mem_span [Fintype ι] (v : ι → V)
    (hv : span K (Set.range v) = ⊤) (i : ι)
    (hi : ∀ A, IsNormalBasis (K := K) v A → i ∈ A) :
    v i ∉ span K (v '' {j | j ≠ i}) := by
  intro hmem
  have hspan : span K (v '' {j | j ≠ i}) = ⊤ := by
    apply top_unique
    rw [← hv]
    apply span_le.mpr
    rintro _ ⟨j, rfl⟩
    by_cases hj : j = i
    · subst j
      exact hmem
    · exact subset_span ⟨j, hj, rfl⟩
  obtain ⟨A, hAi, hA⟩ := exists_normalBasis_omitting v i hspan
  exact hAi (hi A hA)

lemma IsNormalBasis.card_eq {v : ι → V} {A : Finset ι}
    (hA : IsNormalBasis (K := K) v A) : A.card = Module.finrank K V := by
  classical
  have hli : LinearIndependent K (fun i : A => v i) := hA.1
  let b : Basis A K V := Basis.mk hli (by
    have hr : Set.range (fun i : A => v i) = v '' (A : Set ι) := by
      ext x
      simp
    rw [hr, hA.2])
  exact (Module.finrank_eq_card_finset_basis b).symm

variable {W : Type*} [AddCommGroup W] [Module K W]

lemma mandatory_coordinate_eq_zero [Fintype ι] (b : Basis ι K V) (q : V →ₗ[K] W)
    (hq : span K (Set.range (fun j => q (b j))) = ⊤) (i : ι)
    (hi : ∀ A, IsNormalBasis (K := K) (fun j => q (b j)) A → i ∈ A)
    (t : V) (ht : q t = 0) : b.repr t i = 0 := by
  classical
  by_contra hti
  let S : Submodule K W := span K ((fun j => q (b j)) '' {j | j ≠ i})
  have hsum : (∑ j ∈ Finset.univ.erase i, b.repr t j • q (b j)) ∈ S := by
    apply S.sum_mem
    intro j hj
    exact S.smul_mem _ (subset_span ⟨j, (Finset.mem_erase.mp hj).1, rfl⟩)
  have hall : (∑ j, b.repr t j • q (b j)) = 0 := by
    calc
      _ = q (∑ j, b.repr t j • b j) := by simp only [map_sum, map_smul]
      _ = 0 := by rw [b.sum_repr, ht]
  rw [← Finset.sum_erase_add _ _ (Finset.mem_univ i)] at hall
  have hterm : b.repr t i • q (b i) ∈ S := by
    have heq : b.repr t i • q (b i) = -(∑ j ∈ Finset.univ.erase i,
        b.repr t j • q (b j)) := eq_neg_of_add_eq_zero_left (by simpa only [add_comm] using hall)
    rw [heq]
    exact S.neg_mem hsum
  exact mandatory_not_mem_span (fun j => q (b j)) hq i hi
    ((S.smul_mem_iff hti).mp hterm)

lemma largest_nontangent_mandatory {m : ℕ}
    (u v : Fin (m + 1) → V) (hu : span K (Set.range u) = ⊤)
    (hvu : ∀ i, i ≠ 0 → v i = u i)
    (hexclude : ∀ A B : Finset (Fin (m + 1)),
      IsNormalBasis (K := K) u A → IsNormalBasis (K := K) v B →
      ∀ i, i ≠ 0 → i ∈ A → i ∉ B →
      (∀ j, i < j → (j ∈ A ↔ j ∈ B)) → False)
    (i : Fin (m + 1)) (hi0 : i ≠ 0) (hi : u i ≠ 0)
    (hlarge : ∀ j, i < j → u j = 0)
    (B : Finset (Fin (m + 1))) (hB : IsNormalBasis (K := K) v B) : i ∈ B := by
  classical
  obtain ⟨A, hiA, hA⟩ := exists_normalBasis_containing u hu i hi
  by_contra hiB
  apply hexclude A B hA hB i hi0 hiA hiB
  intro j hj
  have hj0 : j ≠ 0 := by
    intro h
    subst j
    exact (not_lt_of_ge (Fin.zero_le _)) hj
  have hjA : j ∉ A := fun h => hA.ne_zero h (hlarge j hj)
  have hjB : j ∉ B := fun h => hB.ne_zero h ((hvu j hj0).trans (hlarge j hj))
  simp only [hjA, hjB]

lemma weighted_normalBasis_exclusion {m : ℕ}
    (u v : Fin (m + 1) → V) (w cost : Fin (m + 1) → ℝ) (C : ℝ)
    (hcomparison : ∀ A B, IsNormalBasis (K := K) u A →
      IsNormalBasis (K := K) v B → (∏ j ∈ A, w j) ≤ C * ∏ j ∈ B, cost j)
    (hseparated : ∀ A B : Finset (Fin (m + 1)), A.card = B.card →
      ∀ i, i ≠ 0 → i ∈ A → i ∉ B →
      (∀ j, i < j → (j ∈ A ↔ j ∈ B)) →
      C * (∏ j ∈ B, cost j) < ∏ j ∈ A, w j)
    (A B : Finset (Fin (m + 1)))
    (hA : IsNormalBasis (K := K) u A) (hB : IsNormalBasis (K := K) v B)
    (i : Fin (m + 1)) (hi0 : i ≠ 0) (hiA : i ∈ A) (hiB : i ∉ B)
    (hlarge : ∀ j, i < j → (j ∈ A ↔ j ∈ B)) : False := by
  exact (not_lt_of_ge (hcomparison A B hA hB))
    (hseparated A B (hA.card_eq.trans hB.card_eq.symm) i hi0 hiA hiB hlarge)

end PiExponent.NormalBasisRigidity

end

end OAI
end Source0087

-- Source: OAI/NumberTheory/PiExponent/Jets/NormalFrameBasis.lean
section Source0088
/-
Modification notice for the LogTwo project.
Derived from openai/math (Apache-2.0), revision adc7f1241b42e322a6451854ab7e4b4c146bf78a.
Original source: lean/OAI/NumberTheory/PiExponent/Jets/NormalFrameBasis.lean
Changes: Convert module/import declarations to the Lean 4.34 public module format.
See ../THIRD_PARTY_NOTICES.txt for provenance and the recorded changes.
-/

namespace OAI

noncomputable section
namespace PiExponent.NormalBasisRigidity
open Module

variable {K : Type*} [Field K] (m : ℕ) (y : K) (hy : y ≠ 0)

def frameEquiv : (Fin (m + 1) → K) ≃ₗ[K] (Fin (m + 1) → K) where
  toFun c := Fin.cases (y * c 0) (fun i => c i.succ + c 0)
  invFun t := Fin.cases (t 0 / y) (fun i => t i.succ - t 0 / y)
  left_inv c := by
    funext i
    refine Fin.cases ?_ (fun j => ?_) i
    · simp [hy]
    · simp [hy]
  right_inv t := by
    funext i
    refine Fin.cases ?_ (fun j => ?_) i
    · change y * (t 0 / y) = t 0
      field_simp
    · simp
  map_add' c d := by
    funext i
    refine Fin.cases ?_ (fun j => ?_) i
    · simp [mul_add]
    · simp only [Pi.add_apply, Fin.cases_succ]
      ring
  map_smul' a c := by
    funext i
    refine Fin.cases ?_ (fun j => ?_) i
    · simp only [Pi.smul_apply, Fin.cases_zero, smul_eq_mul, RingHom.id_apply]
      ring
    · simp [mul_add]

def frameBasis : Basis (Fin (m + 1)) K (Fin (m + 1) → K) :=
  (Pi.basisFun K _).map (frameEquiv m y hy)

@[simp] lemma frameBasis_repr_zero (t : Fin (m + 1) → K) :
    (frameBasis m y hy).repr t 0 = t 0 / y := by
  change (Pi.basisFun K _).repr ((frameEquiv m y hy).symm t) 0 = _
  rw [Pi.basisFun_repr]
  rfl

@[simp] lemma frameBasis_repr_succ (t : Fin (m + 1) → K) (i : Fin m) :
    (frameBasis m y hy).repr t i.succ = t i.succ - t 0 / y := by
  change (Pi.basisFun K _).repr ((frameEquiv m y hy).symm t) i.succ = _
  rw [Pi.basisFun_repr]
  rfl

@[simp] lemma frameBasis_succ (i : Fin m) :
    frameBasis m y hy i.succ = Pi.basisFun K _ i.succ := by
  ext j
  refine Fin.cases ?_ (fun k => ?_) j
  · simp [frameBasis, frameEquiv, Pi.basisFun_apply]
  · simp [frameBasis, frameEquiv, Pi.basisFun_apply, Pi.single_apply]

@[simp] lemma frameBasis_zero_zero : frameBasis m y hy 0 0 = y := by
  simp [frameBasis, frameEquiv, Pi.basisFun_apply]

@[simp] lemma frameBasis_zero_succ (i : Fin m) : frameBasis m y hy 0 i.succ = 1 := by
  simp [frameBasis, frameEquiv, Pi.basisFun_apply]

variable {V : Type*} [AddCommGroup V] [Module K V]

lemma mandatory_logarithmic_differential (q : (Fin (m + 1) → K) →ₗ[K] V)
    (hq : Submodule.span K (Set.range (fun j => q (frameBasis m y hy j))) = ⊤)
    (i : Fin m)
    (hi : ∀ A, IsNormalBasis (K := K) (fun j => q (frameBasis m y hy j)) A → i.succ ∈ A)
    (t : Fin (m + 1) → K) (ht : q t = 0) : t i.succ = t 0 / y := by
  have h := mandatory_coordinate_eq_zero (frameBasis m y hy) q hq i.succ hi t ht
  rw [frameBasis_repr_succ] at h
  exact sub_eq_zero.mp h

lemma span_mapped_basis_eq_top {ι U : Type*} [Fintype ι]
    [AddCommGroup U] [Module K U] (b : Basis ι K U) (q : U →ₗ[K] V)
    (hq : Function.Surjective q) :
    Submodule.span K (Set.range (fun j => q (b j))) = ⊤ := by
  apply top_unique
  intro x _
  obtain ⟨t, rfl⟩ := hq x
  rw [← b.sum_repr t, map_sum]
  apply Submodule.sum_mem
  intro i _
  rw [map_smul]
  exact Submodule.smul_mem _ _ (Submodule.subset_span (Set.mem_range_self i))

theorem normal_basis_differential_dichotomy
    (q : (Fin (m + 1) → K) →ₗ[K] V) (hq : Function.Surjective q) (hq0 : q ≠ 0)
    (hexclude : ∀ A B : Finset (Fin (m + 1)),
      IsNormalBasis (K := K) (fun j => q (Pi.basisFun K _ j)) A →
      IsNormalBasis (K := K) (fun j => q (frameBasis m y hy j)) B →
      ∀ i, i ≠ 0 → i ∈ A → i ∉ B →
      (∀ j, i < j → (j ∈ A ↔ j ∈ B)) → False) :
    (∀ t, q t = 0 → t 0 = 0) ∨
      ∃ i : Fin m, ∀ t, q t = 0 → t i.succ = t 0 / y := by
  classical
  let b := Pi.basisFun K (Fin (m + 1))
  let S := Finset.univ.filter (fun i : Fin (m + 1) => i ≠ 0 ∧ q (b i) ≠ 0)
  by_cases hS : S.Nonempty
  · let i := S.max' hS
    have hiS : i ∈ S := Finset.max'_mem _ _
    have hi := (Finset.mem_filter.mp hiS).2
    have hlarge : ∀ j, i < j → q (b j) = 0 := by
      intro j hj
      by_contra hjq
      have hj0 : j ≠ 0 := by
        intro hz
        subst j
        exact (not_lt_of_ge (Fin.zero_le _)) hj
      have hjS : j ∈ S := Finset.mem_filter.mpr ⟨Finset.mem_univ _, hj0, hjq⟩
      exact (not_lt_of_ge (Finset.le_max' _ _ hjS)) hj
    have hvu : ∀ j : Fin (m + 1), j ≠ 0 → q (frameBasis m y hy j) = q (b j) := by
      intro j
      refine Fin.cases ?_ (fun k _ => ?_) j
      · intro hz
        exact (hz rfl).elim
      · rw [frameBasis_succ]
    have hmand : ∀ B, IsNormalBasis (K := K) (fun j => q (frameBasis m y hy j)) B → i ∈ B :=
      largest_nontangent_mandatory (fun j => q (b j))
        (fun j => q (frameBasis m y hy j)) (span_mapped_basis_eq_top b q hq)
        hvu hexclude i hi.1 hi.2 hlarge
    rcases Fin.eq_zero_or_eq_succ i with hz | ⟨j, hj⟩
    · exact (hi.1 hz).elim
    · right
      refine ⟨j, ?_⟩
      intro t ht
      apply mandatory_logarithmic_differential m y hy q
        (span_mapped_basis_eq_top (frameBasis m y hy) q hq) j ?_ t ht
      intro B hB
      rw [← hj]
      exact hmand B hB
  · have hpos : ∀ j : Fin m, q (b j.succ) = 0 := by
      intro j
      by_contra hj
      exact hS ⟨j.succ, Finset.mem_filter.mpr ⟨Finset.mem_univ _, Fin.succ_ne_zero _, hj⟩⟩
    have he0 : q (b 0) ≠ 0 := by
      intro he
      apply hq0
      apply b.ext
      intro j
      refine Fin.cases ?_ (fun k => ?_) j
      · exact he
      · exact hpos k
    have hqform (t : Fin (m + 1) → K) : q t = t 0 • q (b 0) := by
      calc
        q t = q (∑ j, b.repr t j • b j) := congrArg q (b.sum_repr t).symm
        _ = ∑ j, b.repr t j • q (b j) := by simp only [map_sum, map_smul]
        _ = t 0 • q (b 0) := by
          rw [Fin.sum_univ_succ]
          simp only [hpos, smul_zero, Finset.sum_const_zero, add_zero]
          simp only [b, Pi.basisFun_repr]
    left
    intro t ht
    rw [hqform] at ht
    exact (smul_eq_zero.mp ht).resolve_right he0

end PiExponent.NormalBasisRigidity

end

end OAI
end Source0088

-- Source: OAI/NumberTheory/PiExponent/Jets/PolynomialTangentDifferential.lean
section Source0089
-- Modified in this edition: unused plain lemmas removed; see reduction.json.
/-
Modification notice for the LogTwo project.
Derived from openai/math (Apache-2.0), revision adc7f1241b42e322a6451854ab7e4b4c146bf78a.
Original source: lean/OAI/NumberTheory/PiExponent/Jets/PolynomialTangentDifferential.lean
Changes: Convert module/import declarations to the Lean 4.34 public module format.
See ../THIRD_PARTY_NOTICES.txt for provenance and the recorded changes.
-/

namespace OAI

noncomputable section

namespace PiExponent

open MvPolynomial KaehlerDifferential

section PolynomialMap
variable {C E ι : Type*} [Field C] [Field E] [Algebra C E] [Fintype ι]

theorem derivation_polynomial_map (φ : MvPolynomial ι C →ₐ[C] E)
    (d : Derivation C E E) (p : MvPolynomial ι C) :
    d (φ p) = ∑ i, φ (pderiv i p) * d (φ (X i)) := by
  classical
  induction p using MvPolynomial.induction_on with
  | C a => simp
  | add p q hp hq => simp [hp, hq, add_mul, Finset.sum_add_distrib]
  | mul_X p j hp =>
    simp only [map_mul, Derivation.leibniz, smul_eq_mul, hp,
      map_add, pderiv_X, Finset.sum_add_distrib, add_mul, mul_assoc]
    simp only [← Finset.mul_sum]
    simp [Pi.single_apply, mul_comm]

def polynomialJacobian (φ : MvPolynomial ι C →ₐ[C] E)
    (Q : Ideal (MvPolynomial ι C)) : (ι → E) →ₗ[E] (Q → E) where
  toFun t p := ∑ i, φ (pderiv i p.1) * t i
  map_add' t u := by ext p; simp [mul_add, Finset.sum_add_distrib]
  map_smul' a t := by ext p; simp [Finset.mul_sum, mul_left_comm]

def polynomialTangent (φ : MvPolynomial ι C →ₐ[C] E)
    (Q : Ideal (MvPolynomial ι C)) : Submodule E (ι → E) :=
  LinearMap.ker (polynomialJacobian φ Q)

abbrev PolynomialNormal (φ : MvPolynomial ι C →ₐ[C] E)
    (Q : Ideal (MvPolynomial ι C)) := (ι → E) ⧸ polynomialTangent φ Q

theorem derivation_mem_polynomialTangent (φ : MvPolynomial ι C →ₐ[C] E)
    (Q : Ideal (MvPolynomial ι C)) (hQ : ∀ p ∈ Q, φ p = 0)
    (d : Derivation C E E) :
    (fun i => d (φ (X i))) ∈ polynomialTangent φ Q := by
  change polynomialJacobian φ Q (fun i => d (φ (X i))) = 0
  ext p
  change (∑ i, φ (pderiv i p.1) * d (φ (X i))) = 0
  rw [← derivation_polynomial_map, hQ p.1 p.2, map_zero]

theorem logarithmic_differential_of_polynomialTangent
    (φ : MvPolynomial ι C →ₐ[C] E) (Q : Ideal (MvPolynomial ι C))
    (hQ : ∀ p ∈ Q, φ p = 0) (i j : ι)
    (h : ∀ t ∈ polynomialTangent φ Q, t i = t j / φ (X j)) :
    D C E (φ (X i)) = (φ (X j))⁻¹ • D C E (φ (X j)) := by
  apply sub_eq_zero.mp
  apply (Module.forall_dual_apply_eq_zero_iff E _).mp
  intro l
  let d : Derivation C E E := l.compDer (D C E)
  have hd := h (fun i => d (φ (X i))) (derivation_mem_polynomialTangent φ Q hQ d)
  change l (D C E (φ (X i))) = l (D C E (φ (X j))) / φ (X j) at hd
  simpa only [map_sub, map_smul, smul_eq_mul, div_eq_mul_inv,
    sub_eq_zero, mul_comm] using hd

theorem differential_eq_zero_of_polynomialTangent
    (φ : MvPolynomial ι C →ₐ[C] E) (Q : Ideal (MvPolynomial ι C))
    (hQ : ∀ p ∈ Q, φ p = 0) (i : ι)
    (h : ∀ t ∈ polynomialTangent φ Q, t i = 0) :
    D C E (φ (X i)) = 0 := by
  apply (Module.forall_dual_apply_eq_zero_iff E _).mp
  intro l
  let d : Derivation C E E := l.compDer (D C E)
  exact h (fun i => d (φ (X i))) (derivation_mem_polynomialTangent φ Q hQ d)

end PolynomialMap

variable {C ι : Type*} [Field C] [Fintype ι]

abbrev PolynomialResidueField (Q : Ideal (MvPolynomial ι C)) [Q.IsPrime] :=
  FractionRing (MvPolynomial ι C ⧸ Q)

def polynomialResidueMap (Q : Ideal (MvPolynomial ι C)) [Q.IsPrime] :
    MvPolynomial ι C →ₐ[C] PolynomialResidueField Q :=
  (IsScalarTower.toAlgHom C (MvPolynomial ι C ⧸ Q) (PolynomialResidueField Q)).comp
    (Ideal.Quotient.mkₐ C Q)

omit [Fintype ι] in

theorem polynomialResidueMap_eq_zero (Q : Ideal (MvPolynomial ι C)) [Q.IsPrime]
    (p : MvPolynomial ι C) (hp : p ∈ Q) : polynomialResidueMap Q p = 0 := by
  change algebraMap (MvPolynomial ι C ⧸ Q) (PolynomialResidueField Q)
    (Ideal.Quotient.mk Q p) = 0
  rw [Ideal.Quotient.eq_zero_iff_mem.mpr hp, map_zero]

omit [Fintype ι] in

theorem polynomialResidueMap_eq_zero_iff (Q : Ideal (MvPolynomial ι C)) [Q.IsPrime]
    (p : MvPolynomial ι C) : polynomialResidueMap Q p = 0 ↔ p ∈ Q := by
  constructor
  · intro h
    apply Ideal.Quotient.eq_zero_iff_mem.mp
    apply IsFractionRing.injective (MvPolynomial ι C ⧸ Q) (PolynomialResidueField Q)
    change algebraMap (MvPolynomial ι C ⧸ Q) (PolynomialResidueField Q)
      (Ideal.Quotient.mk Q p) = 0 at h
    simpa only [map_zero] using h
  · exact polynomialResidueMap_eq_zero Q p

omit [Fintype ι] in

theorem coordinate_sub_constant_mem_prime
    (Q : Ideal (MvPolynomial ι C)) [Q.IsPrime] (j : ι) (c : C)
    (h : algebraMap C (PolynomialResidueField Q) c = polynomialResidueMap Q (X j)) :
    X j - MvPolynomial.C c ∈ Q := by
  apply (polynomialResidueMap_eq_zero_iff Q _).mp
  simp only [map_sub, MvPolynomial.algHom_C, h, sub_self]

end PiExponent

end

end OAI
end Source0089

-- Source: OAI/NumberTheory/PiExponent/Polynomials/PolynomialNormalNonzero.lean
section Source0090
-- Modified in this edition: unused plain lemmas removed; see reduction.json.
/-
Modification notice for the LogTwo project.
Derived from openai/math (Apache-2.0), revision adc7f1241b42e322a6451854ab7e4b4c146bf78a.
Original source: lean/OAI/NumberTheory/PiExponent/Polynomials/PolynomialNormalNonzero.lean
Changes: Convert module/import declarations to the Lean 4.34 public module format.
See ../THIRD_PARTY_NOTICES.txt for provenance and the recorded changes.
-/

namespace OAI

namespace PiExponent

open MvPolynomial

theorem totalDegree_pderiv_lt_of_ne_zero
    {C ι : Type*} [CommSemiring C] (p : MvPolynomial ι C) (i : ι)
    (hp : pderiv i p ≠ 0) : (pderiv i p).totalDegree < p.totalDegree := by
  classical
  have hshift (d : ι →₀ ℕ) (hd : d ∈ (pderiv i p).support) :
      d + Finsupp.single i 1 ∈ p.support := by
    apply mem_support_iff.mpr
    intro hz
    have hh := mem_support_iff.mp hd
    apply hh
    rw [coeff_pderiv, hz, zero_mul]
  have hdegree (d : ι →₀ ℕ) (hd : d ∈ (pderiv i p).support) :
      d.sum (fun _ e => e) < p.totalDegree := by
    have hh := le_totalDegree (hshift d hd)
    have he : (d + Finsupp.single i 1).sum (fun _ e => e) =
        d.sum (fun _ e => e) + 1 := by
      rw [Finsupp.sum_add_index']
      · simp
      · intro; rfl
      · intros; rfl
    rw [he] at hh
    omega
  have hpos : 0 < p.totalDegree := by
    obtain ⟨d, hd⟩ := (MvPolynomial.support_nonempty.mpr hp)
    exact (Nat.zero_le _).trans_lt (hdegree d hd)
  rw [MvPolynomial.totalDegree, Finset.sup_lt_iff hpos]
  exact hdegree

theorem eq_constant_of_pderiv_eq_zero
    {C ι : Type*} [Field C] [CharZero C] (p : MvPolynomial ι C)
    (hp : ∀ i, pderiv i p = 0) : p = MvPolynomial.C (p.coeff 0) := by
  classical
  ext d
  by_cases hd : d = 0
  · subst d
    simp
  · have hex : ∃ i, d i ≠ 0 := by
      by_contra! hh
      exact hd (by ext i; exact hh i)
    obtain ⟨i, hi⟩ := hex
    have he : d - Finsupp.single i 1 + Finsupp.single i 1 = d :=
      Finsupp.sub_add_single_one_cancel hi
    have hh := congrArg (fun q : MvPolynomial ι C =>
      q.coeff (d - Finsupp.single i 1)) (hp i)
    rw [coeff_pderiv, he] at hh
    simp only [Finsupp.tsub_apply, Finsupp.single_eq_same] at hh
    have hfactor : (((d i - 1 : ℕ) : C) + 1) ≠ 0 := by
      simpa only [Nat.cast_add, Nat.cast_one] using
        (Nat.cast_ne_zero.mpr (Nat.succ_ne_zero (d i - 1)) :
          (((d i - 1 + 1 : ℕ) : C)) ≠ 0)
    have hc : p.coeff d = 0 := (mul_eq_zero.mp hh).resolve_right hfactor
    simpa [coeff_C, Ne.symm hd] using hc

theorem ideal_eq_bot_of_pderiv_stable
    {C ι : Type*} [Field C] [CharZero C] (Q : Ideal (MvPolynomial ι C))
    (hproper : Q ≠ ⊤) (hstable : ∀ p ∈ Q, ∀ i, pderiv i p ∈ Q) : Q = ⊥ := by
  have hall : ∀ n : ℕ, ∀ p : MvPolynomial ι C,
      p.totalDegree = n → p ∈ Q → p = 0 := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
      intro p hdegree hp
      have hderiv : ∀ i, pderiv i p = 0 := by
        intro i
        by_contra hn
        have hlt := totalDegree_pderiv_lt_of_ne_zero p i hn
        rw [hdegree] at hlt
        exact hn (ih _ hlt _ rfl (hstable p hp i))
      have hc := eq_constant_of_pderiv_eq_zero p hderiv
      have hcoeff : p.coeff 0 = 0 := by
        by_contra hne
        have hunit : IsUnit (MvPolynomial.C (p.coeff 0) : MvPolynomial ι C) :=
          (isUnit_iff_ne_zero.mpr hne).map (MvPolynomial.C : C →+* MvPolynomial ι C)
        have hmem : MvPolynomial.C (p.coeff 0) ∈ Q := by rw [← hc]; exact hp
        exact hproper (Q.eq_top_of_isUnit_mem hmem hunit)
      simpa [hcoeff] using hc
  apply le_antisymm
  · intro p hp
    exact Ideal.mem_bot.mpr (hall p.totalDegree p rfl hp)
  · exact bot_le

end PiExponent

end OAI
end Source0090

-- Source: OAI/NumberTheory/PiExponent/LocalAlgebra/PrimeNormalRigidity.lean
section Source0091
-- Modified in this edition: unused plain lemmas removed; see reduction.json.
/-
Modification notice for the LogTwo project.
Derived from openai/math (Apache-2.0), revision adc7f1241b42e322a6451854ab7e4b4c146bf78a.
Original source: lean/OAI/NumberTheory/PiExponent/LocalAlgebra/PrimeNormalRigidity.lean
Changes: Convert module/import declarations to the Lean 4.34 public module format.
See ../THIRD_PARTY_NOTICES.txt for provenance and the recorded changes.
-/

namespace OAI

noncomputable section

namespace PiExponent
open Module MvPolynomial NormalBasisRigidity

variable {C : Type*} [Field C] [CharZero C] [IsAlgClosed C] {m : ℕ}

abbrev primeNormalProjection (Q : Ideal (MvPolynomial (Fin (m + 1)) C)) [Q.IsPrime] :=
  (polynomialTangent (polynomialResidueMap Q) Q).mkQ

noncomputable def primeCoordinateNormals
    (Q : Ideal (MvPolynomial (Fin (m + 1)) C)) [Q.IsPrime] :
    Fin (m + 1) → PolynomialNormal (polynomialResidueMap Q) Q :=
  fun i => primeNormalProjection Q (Pi.basisFun (PolynomialResidueField Q) _ i)

noncomputable def primeLogarithmicNormals
    (Q : Ideal (MvPolynomial (Fin (m + 1)) C)) [Q.IsPrime]
    (hy : polynomialResidueMap Q (X (0 : Fin (m + 1))) ≠ 0) :
    Fin (m + 1) → PolynomialNormal (polynomialResidueMap Q) Q :=
  fun i => primeNormalProjection Q
    (frameBasis m (polynomialResidueMap Q (X 0)) hy i)

omit [CharZero C] [IsAlgClosed C] in
theorem constant_coordinate_eq_one_of_center
    (Q : Ideal (MvPolynomial (Fin (m + 1)) C)) (a : Fin (m + 1) → C)
    (ha : a 0 = 1) (hpoint : ∀ p ∈ Q, MvPolynomial.eval a p = 0)
    (hconstant : ∃ c : C, X (0 : Fin (m + 1)) - MvPolynomial.C c ∈ Q) :
    X (0 : Fin (m + 1)) - 1 ∈ Q := by
  obtain ⟨c, hc⟩ := hconstant
  have he := hpoint _ hc
  simp only [eval_sub, eval_X, eval_C, ha, sub_eq_zero] at he
  simpa only [← he, map_one] using hc

end PiExponent

end

end OAI
end Source0091

-- Source: OAI/NumberTheory/PiExponent/Approximation/GenericNormalRigidity.lean
section Source0092
/-
Modification notice for the LogTwo project.
Derived from openai/math (Apache-2.0), revision adc7f1241b42e322a6451854ab7e4b4c146bf78a.
Original source: lean/OAI/NumberTheory/PiExponent/Approximation/GenericNormalRigidity.lean
Changes: Convert module/import declarations to the Lean 4.34 public module format.
See ../THIRD_PARTY_NOTICES.txt for provenance and the recorded changes.
-/

namespace OAI

noncomputable section
namespace PiExponent
open Module MvPolynomial NormalBasisRigidity

variable {C E ι : Type*} [Field C] [CharZero C] [Field E] [Algebra C E] [Fintype ι]

theorem polynomialNormal_mkQ_ne_zero_of_kernel
    (φ : MvPolynomial ι C →ₐ[C] E) (Q : Ideal (MvPolynomial ι C))
    (hker : ∀ p, φ p = 0 ↔ p ∈ Q) (hQ : Q ≠ ⊥) :
    (polynomialTangent φ Q).mkQ ≠ 0 := by
  classical
  intro hzero
  have htop : polynomialTangent φ Q = ⊤ := by
    rw [← Submodule.ker_mkQ (polynomialTangent φ Q), hzero, LinearMap.ker_zero]
  apply hQ
  apply ideal_eq_bot_of_pderiv_stable Q
  · intro h
    have hh := (hker 1).mpr (by rw [h]; trivial)
    exact (one_ne_zero : (1 : E) ≠ 0) (by simpa only [map_one] using hh)
  · intro p hp i
    apply (hker _).mp
    have ht : (Pi.single i 1 : ι → E) ∈ polynomialTangent φ Q := by rw [htop]; trivial
    change polynomialJacobian φ Q (Pi.single i 1) = 0 at ht
    have hh := congrFun ht ⟨p, hp⟩
    simpa [polynomialJacobian, Pi.single_apply] using hh

theorem constant_zeroth_coordinate_of_generic_normal_separation
    [IsAlgClosed C] [Algebra.EssFiniteType C E] {m : ℕ}
    (φ : MvPolynomial (Fin (m + 1)) C →ₐ[C] E)
    (Q : Ideal (MvPolynomial (Fin (m + 1)) C))
    (hker : ∀ p, φ p = 0 ↔ p ∈ Q) (hQ : Q ≠ ⊥)
    (hy : φ (X (0 : Fin (m + 1))) ≠ 0)
    (hexclude : ∀ A B : Finset (Fin (m + 1)),
      IsNormalBasis (K := E)
        (fun j => (polynomialTangent φ Q).mkQ (Pi.basisFun E _ j)) A →
      IsNormalBasis (K := E)
        (fun j => (polynomialTangent φ Q).mkQ (frameBasis m (φ (X 0)) hy j)) B →
      ∀ i, i ≠ 0 → i ∈ A → i ∉ B →
      (∀ j, i < j → (j ∈ A ↔ j ∈ B)) → False) :
    ∃ c : C, X (0 : Fin (m + 1)) - MvPolynomial.C c ∈ Q := by
  let q := (polynomialTangent φ Q).mkQ
  have hvan : ∀ p ∈ Q, φ p = 0 := fun p hp => (hker p).mpr hp
  have hd := normal_basis_differential_dichotomy m (φ (X 0)) hy q
    (Submodule.mkQ_surjective _) (polynomialNormal_mkQ_ne_zero_of_kernel φ Q hker hQ) hexclude
  have hconst : ∃ c : C, algebraMap C E c = φ (X (0 : Fin (m + 1))) := by
    rcases hd with hzero | ⟨i, hlog⟩
    · exact constant_of_differential_eq_zero (φ (X 0))
        (differential_eq_zero_of_polynomialTangent φ Q hvan 0
          (fun t ht => hzero t ((Submodule.Quotient.mk_eq_zero _).mpr ht)))
    · exact constant_of_logarithmic_differential (φ (X i.succ)) (φ (X 0))
        (logarithmic_differential_of_polynomialTangent φ Q hvan i.succ 0
          (fun t ht => hlog t ((Submodule.Quotient.mk_eq_zero _).mpr ht)))
  obtain ⟨c, hc⟩ := hconst
  refine ⟨c, (hker _).mp ?_⟩
  simp only [map_sub, MvPolynomial.algHom_C, hc, sub_self]

end PiExponent

end

end OAI
end Source0092

-- Source: OAI/NumberTheory/PiExponent/Geometry/CurveContact.lean
section Source0093
-- Modified in this edition: unused plain lemmas removed; see reduction.json.
/-
Modification notice for the LogTwo project.
Derived from openai/math (Apache-2.0), revision adc7f1241b42e322a6451854ab7e4b4c146bf78a.
Original source: lean/OAI/NumberTheory/PiExponent/Geometry/CurveContact.lean
Changes: Convert module/import declarations to the Lean 4.34 public module format.
See ../THIRD_PARTY_NOTICES.txt for provenance and the recorded changes.
-/

namespace OAI

namespace PiExponentApprox

noncomputable section

def frameWordCost {m : ℕ} (cost : Fin (m + 1) → ℝ)
    (word : List (Fin (m + 1))) : ℝ := (word.map cost).sum

@[simp] theorem frameWordCost_nil {m : ℕ} (cost : Fin (m + 1) → ℝ) :
    frameWordCost cost [] = 0 := rfl

@[simp] theorem frameWordCost_cons {m : ℕ} (cost : Fin (m + 1) → ℝ)
    (i : Fin (m + 1)) (word : List (Fin (m + 1))) :
    frameWordCost cost (i :: word) = cost i + frameWordCost cost word := rfl

def frameDerivativeIdeal {m : ℕ} (cost : Fin (m + 1) → ℝ)
    (bound : ℝ) (F : FramePolynomial m) : Ideal (FramePolynomial m) :=
  Ideal.span {g | ∃ word, frameWordCost cost word ≤ bound ∧
    polynomialFrameWord m word F = g}

theorem frameWord_mem_derivativeIdeal {m : ℕ} (cost : Fin (m + 1) → ℝ)
    (bound : ℝ) (F : FramePolynomial m) (word : List (Fin (m + 1)))
    (hword : frameWordCost cost word ≤ bound) :
    polynomialFrameWord m word F ∈ frameDerivativeIdeal cost bound F :=
  Ideal.subset_span ⟨word, hword, rfl⟩

theorem frameDerivativeIdeal_mono {m : ℕ} (cost : Fin (m + 1) → ℝ)
    (F : FramePolynomial m) {a b : ℝ} (hab : a ≤ b) :
    frameDerivativeIdeal cost a F ≤ frameDerivativeIdeal cost b F := by
  apply Ideal.span_mono
  intro g hg
  obtain ⟨word, hword, rfl⟩ := hg
  exact ⟨word, hword.trans hab, rfl⟩

theorem polynomial_mem_frameDerivativeIdeal {m : ℕ}
    (cost : Fin (m + 1) → ℝ) (bound : ℝ) (F : FramePolynomial m)
    (hbound : 0 ≤ bound) : F ∈ frameDerivativeIdeal cost bound F :=
  frameWord_mem_derivativeIdeal cost bound F [] hbound

def polynomialDerivativeCore {m : ℕ}
    (D : Derivation ℂ (FramePolynomial m) (FramePolynomial m))
    (I : Ideal (FramePolynomial m)) : Ideal (FramePolynomial m) where
  carrier := {p | p ∈ I ∧ D p ∈ I}
  zero_mem' := by simp only [Set.mem_ofPred_eq, D.map_zero]; exact ⟨I.zero_mem, I.zero_mem⟩
  add_mem' := by
    intro p q hp hq
    refine ⟨I.add_mem hp.1 hq.1, ?_⟩
    rw [map_add]
    exact I.add_mem hp.2 hq.2
  smul_mem' := by
    intro r p hp
    change r * p ∈ I ∧ D (r * p) ∈ I
    refine ⟨I.mul_mem_left r hp.1, ?_⟩
    rw [Derivation.leibniz]
    exact I.add_mem (I.mul_mem_left r hp.2) (by
      simpa only [smul_eq_mul, mul_comm] using I.mul_mem_left (D r) hp.1)

theorem polynomialFrame_mem_derivativeIdeal {m : ℕ}
    (cost : Fin (m + 1) → ℝ) (hcost : ∀ i, 0 ≤ cost i)
    (bound : ℝ) (F p : FramePolynomial m) (i : Fin (m + 1))
    (hp : p ∈ frameDerivativeIdeal cost bound F) :
    polynomialFrame m i p ∈ frameDerivativeIdeal cost (bound + cost i) F := by
  let I := frameDerivativeIdeal cost (bound + cost i) F
  have hle : frameDerivativeIdeal cost bound F ≤
      polynomialDerivativeCore (polynomialFrame m i) I := by
    apply Ideal.span_le.mpr
    intro g hg
    obtain ⟨word, hword, rfl⟩ := hg
    refine ⟨?_, ?_⟩
    · exact frameWord_mem_derivativeIdeal cost (bound + cost i) F word
        (hword.trans (le_add_of_nonneg_right (hcost i)))
    · exact frameWord_mem_derivativeIdeal cost (bound + cost i) F (i :: word)
        (by simpa only [frameWordCost_cons, add_comm] using add_le_add_left hword (cost i))
  exact (hle hp).2

theorem polynomialFrameWord_mem_derivativeIdeal {m : ℕ}
    (cost : Fin (m + 1) → ℝ) (hcost : ∀ i, 0 ≤ cost i)
    (bound : ℝ) (F p : FramePolynomial m) (word : List (Fin (m + 1)))
    (hp : p ∈ frameDerivativeIdeal cost bound F) :
    polynomialFrameWord m word p ∈
      frameDerivativeIdeal cost (bound + frameWordCost cost word) F := by
  induction word with
  | nil => simpa only [polynomialFrameWord_nil, frameWordCost_nil, add_zero] using hp
  | cons i word ih =>
      have h := polynomialFrame_mem_derivativeIdeal cost hcost
        (bound + frameWordCost cost word) F (polynomialFrameWord m word p) i ih
      simpa only [polynomialFrameWord_cons, frameWordCost_cons, add_assoc,
        add_comm (frameWordCost cost word) (cost i)] using h

theorem derivative_vanishes_on_persistent_ideal {m : ℕ}
    (cost : Fin (m + 1) → ℝ) (hcost : ∀ i, 0 ≤ cost i)
    (bound delta : ℝ) (F p : FramePolynomial m)
    (P : Ideal (FramePolynomial m))
    (hp : p ∈ frameDerivativeIdeal cost bound F)
    (hpersist : frameDerivativeIdeal cost (bound + delta) F ≤ P)
    (word : List (Fin (m + 1))) (hword : frameWordCost cost word ≤ delta) :
    polynomialFrameWord m word p ∈ P := by
  apply hpersist
  have hbound : bound + frameWordCost cost word ≤ bound + delta := by linarith
  exact frameDerivativeIdeal_mono cost F hbound
    (polynomialFrameWord_mem_derivativeIdeal cost hcost bound F p word hp)

theorem frameDerivativeIdeal_levels_monotone {m : ℕ}
    (cost : Fin (m + 1) → ℝ) (delta : ℝ) (hdelta : 0 ≤ delta)
    (F : FramePolynomial m) :
    Monotone (fun r : ℕ => frameDerivativeIdeal cost ((r : ℝ) * delta) F) := by
  intro a b hab
  apply frameDerivativeIdeal_mono
  exact mul_le_mul_of_nonneg_right (Nat.cast_le.mpr hab) hdelta

theorem exists_persistent_frame_component {m : ℕ}
    (cost : Fin (m + 1) → ℝ) (hcost : ∀ i, 0 ≤ cost i)
    (delta : ℝ) (hdelta : 0 ≤ delta) (F : FramePolynomial m) (hF : F ≠ 0)
    (P : Ideal (FramePolynomial m)) (hP : P.IsPrime) (hheight : P.height ≤ m)
    (hvanish : ∀ word : List (Fin (m + 1)),
      frameWordCost cost word ≤ ((m : ℝ) + 2) * delta →
        polynomialFrameWord m word F ∈ P) :
    ∃ r < m + 2, ∃ Q : Ideal (FramePolynomial m),
      Q ∈ (frameDerivativeIdeal cost ((r : ℝ) * delta) F).minimalPrimes ∧
      Q ∈ (frameDerivativeIdeal cost (((r : ℝ) + 1) * delta) F).minimalPrimes ∧
      Q ≤ P ∧ 1 ≤ Q.height ∧ Q.height ≤ m ∧
      ∀ p ∈ frameDerivativeIdeal cost ((r : ℝ) * delta) F,
        ∀ word : List (Fin (m + 1)), frameWordCost cost word ≤ delta →
          polynomialFrameWord m word p ∈ Q := by
  let I : ℕ → Ideal (FramePolynomial m) :=
    fun r => frameDerivativeIdeal cost ((r : ℝ) * delta) F
  have hI : Monotone I := frameDerivativeIdeal_levels_monotone cost delta hdelta F
  have htop : I (m + 2) ≤ P := by
    apply Ideal.span_le.mpr
    intro g hg
    obtain ⟨word, hword, rfl⟩ := hg
    apply hvanish word
    simpa only [Nat.cast_add, Nat.cast_ofNat] using hword
  have hinitial : F ∈ I 0 := by
    simpa only [I, Nat.cast_zero, zero_mul] using
      polynomial_mem_frameDerivativeIdeal cost 0 F (le_refl 0)
  obtain ⟨r, hr, Q, hQr, hQnext, hQP, hQlo, hQhi⟩ :=
    PiExponent.PersistentComponents.exists_persistent_component_positive_height
      I hI m P hP htop hheight hF hinitial
  refine ⟨r, hr, Q, hQr, ?_, hQP, hQlo, hQhi, ?_⟩
  · simpa only [I, Nat.cast_add, Nat.cast_one] using hQnext
  · intro p hp word hword
    apply derivative_vanishes_on_persistent_ideal cost hcost
      ((r : ℝ) * delta) delta F p Q hp
    · have hb : (r : ℝ) * delta + delta = ((r + 1 : ℕ) : ℝ) * delta := by
        push_cast
        ring
      rw [hb]
      exact hQnext.le
    · exact hword

end
end PiExponentApprox

end OAI
end Source0093

-- Source: OAI/NumberTheory/PiExponent/Jets/ConormalPairing.lean
section Source0094
/-
Modification notice for the LogTwo project.
Derived from openai/math (Apache-2.0), revision adc7f1241b42e322a6451854ab7e4b4c146bf78a.
Original source: lean/OAI/NumberTheory/PiExponent/Jets/ConormalPairing.lean
Changes: Convert module/import declarations to the Lean 4.34 public module format.
See ../THIRD_PARTY_NOTICES.txt for provenance and the recorded changes.
-/

namespace OAI

noncomputable section
namespace PiExponentSiegel.W58

variable {K R : Type*} [CommRing K] [CommRing R] [Algebra K R]
variable (I : Ideal R) (D : Derivation K R (R ⧸ I))

theorem ideal_smul_quotient_zero (x : I) (z : R ⧸ I) : (x : R) • z = 0 := by
  rw [Algebra.smul_def]
  change Ideal.Quotient.mk I (x : R) * z = 0
  rw [Ideal.Quotient.eq_zero_iff_mem.mpr x.property, zero_mul]

def normalRestriction : I →ₗ[R] R ⧸ I where
  toFun x := D x
  map_add' x y := D.map_add x y
  map_smul' r x := by
    change D (r * (x : R)) = r • D (x : R)
    rw [D.leibniz, ideal_smul_quotient_zero I x, add_zero]

theorem normalRestriction_product_zero (x y : I) : normalRestriction I D (x * y) = 0 := by
  change D ((x : R) * (y : R)) = 0
  rw [D.leibniz, ideal_smul_quotient_zero I x, ideal_smul_quotient_zero I y, add_zero]

def conormalPairing : I.Cotangent →ₗ[R] R ⧸ I :=
  Ideal.Cotangent.lift (normalRestriction I D) (normalRestriction_product_zero I D)

@[simp] theorem conormalPairing_toCotangent (x : I) :
    conormalPairing I D (I.toCotangent x) = D x := rfl

end PiExponentSiegel.W58

end

end OAI
end Source0094

-- Source: OAI/NumberTheory/PiExponent/Jets/ResidueConormalPairing.lean
section Source0095
-- Modified in this edition: unused plain lemmas removed; see reduction.json.
/-
Modification notice for the LogTwo project.
Derived from openai/math (Apache-2.0), revision adc7f1241b42e322a6451854ab7e4b4c146bf78a.
Original source: lean/OAI/NumberTheory/PiExponent/Jets/ResidueConormalPairing.lean
Changes: Convert module/import declarations to the Lean 4.34 public module format.
See ../THIRD_PARTY_NOTICES.txt for provenance and the recorded changes.
-/

namespace OAI

noncomputable section
namespace PiExponentSiegel.W58

variable {K R : Type*} [CommRing K] [CommRing R] [Algebra K R]
variable (I : Ideal R) (D : Derivation K R (R ⧸ I))

instance cotangentQuotientScalarTower : IsScalarTower R (R ⧸ I) I.Cotangent :=
  inferInstance

def residueConormalPairing : I.Cotangent →ₗ[R ⧸ I] R ⧸ I :=
  (conormalPairing I D).extendScalarsOfSurjective
    (show Function.Surjective (algebraMap R (R ⧸ I)) from Ideal.Quotient.mk_surjective)

@[simp] theorem residueConormalPairing_apply (x : I.Cotangent) :
    residueConormalPairing I D x = conormalPairing I D x := rfl

@[simp] theorem residueConormalPairing_toCotangent (x : I) :
    residueConormalPairing I D (I.toCotangent x) = D x := rfl

def reducedDerivation (D₀ : Derivation K R R) : Derivation K R (R ⧸ I) :=
  (Ideal.Quotient.mkₐ R I).toLinearMap.compDer D₀

@[simp] theorem reducedDerivation_apply (D₀ : Derivation K R R) (x : R) :
    reducedDerivation I D₀ x = Ideal.Quotient.mk I (D₀ x) := rfl

def derivationNormal (D₀ : Derivation K R R) : I.Cotangent →ₗ[R ⧸ I] R ⧸ I :=
  residueConormalPairing I (reducedDerivation I D₀)

@[simp] theorem derivationNormal_toCotangent (D₀ : Derivation K R R) (x : I) :
    derivationNormal I D₀ (I.toCotangent x) = Ideal.Quotient.mk I (D₀ x) := rfl

end PiExponentSiegel.W58

end

end OAI
end Source0095

-- Source: OAI/NumberTheory/PiExponent/Jets/PrimeNormalCotangent.lean
section Source0096
/-
Modification notice for the LogTwo project.
Derived from openai/math (Apache-2.0), revision adc7f1241b42e322a6451854ab7e4b4c146bf78a.
Original source: lean/OAI/NumberTheory/PiExponent/Jets/PrimeNormalCotangent.lean
Changes: Convert module/import declarations to the Lean 4.34 public module format.
See ../THIRD_PARTY_NOTICES.txt for provenance and the recorded changes.
-/

namespace OAI

noncomputable section

namespace PiExponent

open KaehlerDifferential
open scoped TensorProduct

def extendModuleDerivation
    {C R A E : Type*} [CommRing C] [CommRing R] [CommRing A] [CommRing E]
    [Algebra C R] [Algebra C A] [Algebra C E]
    [Algebra R A] [Algebra R E] [Algebra A E]
    [IsScalarTower C R A] [IsScalarTower C R E] [IsScalarTower C A E]
    [IsScalarTower R A E] [Algebra.FormallyEtale R A]
    (d : Derivation C R E) : Derivation C A E :=
  ((LinearMap.liftBaseChange A d.liftKaehlerDifferential).comp
    (tensorKaehlerEquivOfFormallyEtale C R A).symm.toLinearMap).compDer (D C A)

@[simp]
theorem extendModuleDerivation_algebraMap
    {C R A E : Type*} [CommRing C] [CommRing R] [CommRing A] [CommRing E]
    [Algebra C R] [Algebra C A] [Algebra C E]
    [Algebra R A] [Algebra R E] [Algebra A E]
    [IsScalarTower C R A] [IsScalarTower C R E] [IsScalarTower C A E]
    [IsScalarTower R A E] [Algebra.FormallyEtale R A]
    (d : Derivation C R E) (r : R) :
    extendModuleDerivation (A := A) d (algebraMap R A r) = d r := by
  simp [extendModuleDerivation, LinearMap.compDer,
    tensorKaehlerEquivOfFormallyEtale_symm_D_algebraMap,
    Derivation.liftKaehlerDifferential_comp_D]

variable {C ι : Type*} [Field C] [Fintype ι]
variable (Q : Ideal (MvPolynomial ι C)) [Q.IsPrime]

abbrev PrimeLocalCotangent := IsLocalRing.CotangentSpace (Localization.AtPrime Q)

def primeResidueMap : MvPolynomial ι C →ₐ[C] Q.ResidueField :=
  IsScalarTower.toAlgHom C (MvPolynomial ι C) Q.ResidueField

def primeLocalPartial (i : ι) : Derivation C (Localization.AtPrime Q) Q.ResidueField := by
  let : Algebra.FormallyEtale (MvPolynomial ι C) (Localization.AtPrime Q) :=
    Algebra.FormallyEtale.of_isLocalization Q.primeCompl
  exact extendModuleDerivation
    ((Algebra.linearMap (MvPolynomial ι C) Q.ResidueField).compDer (MvPolynomial.pderiv i))

omit [Fintype ι] in
@[simp]
theorem primeLocalPartial_polynomial (i : ι) (p : MvPolynomial ι C) :
    primeLocalPartial Q i (algebraMap (MvPolynomial ι C) (Localization.AtPrime Q) p) =
      algebraMap (MvPolynomial ι C) Q.ResidueField (MvPolynomial.pderiv i p) := by
  let : Algebra.FormallyEtale (MvPolynomial ι C) (Localization.AtPrime Q) :=
    Algebra.FormallyEtale.of_isLocalization Q.primeCompl
  change extendModuleDerivation _ (algebraMap (MvPolynomial ι C) (Localization.AtPrime Q) p) = _
  rw [extendModuleDerivation_algebraMap]
  rfl

def primePartialNormal (i : ι) : PrimeLocalCotangent Q →ₗ[Q.ResidueField] Q.ResidueField :=
  PiExponentSiegel.W58.residueConormalPairing
    (IsLocalRing.maximalIdeal (Localization.AtPrime Q)) (primeLocalPartial Q i)

def primeNormalPairing : (ι → Q.ResidueField) →ₗ[Q.ResidueField]
    (PrimeLocalCotangent Q →ₗ[Q.ResidueField] Q.ResidueField) where
  toFun v := ∑ i, v i • primePartialNormal Q i
  map_add' v w := by simp [add_smul, Finset.sum_add_distrib]
  map_smul' c v := by simp [Finset.smul_sum, smul_smul]

def primePolynomialCotangent (p : Q) : PrimeLocalCotangent Q :=
  (IsLocalRing.maximalIdeal (Localization.AtPrime Q)).toCotangent
    ⟨algebraMap (MvPolynomial ι C) (Localization.AtPrime Q) p.1,
      (IsLocalization.AtPrime.to_map_mem_maximal_iff (Localization.AtPrime Q) Q p.1).mpr p.2⟩

@[simp]
theorem primeNormalPairing_polynomial (v : ι → Q.ResidueField) (p : Q) :
    primeNormalPairing Q v (primePolynomialCotangent Q p) =
      ∑ i, v i * primeResidueMap Q (MvPolynomial.pderiv i p.1) := by
  change (∑ i, v i • primePartialNormal Q i) (primePolynomialCotangent Q p) = _
  rw [LinearMap.sum_apply]
  apply Finset.sum_congr rfl
  intro i _
  change v i * primeLocalPartial Q i
    (algebraMap (MvPolynomial ι C) (Localization.AtPrime Q) p.1) = _
  rw [primeLocalPartial_polynomial]
  rfl

theorem primeNormalPairing_ker_le_tangent :
    LinearMap.ker (primeNormalPairing Q) ≤ polynomialTangent (primeResidueMap Q) Q := by
  intro v hv
  change primeNormalPairing Q v = 0 at hv
  change polynomialJacobian (primeResidueMap Q) Q v = 0
  ext p
  have h := LinearMap.congr_fun hv (primePolynomialCotangent Q p)
  simpa only [primeNormalPairing_polynomial, LinearMap.zero_apply,
    polynomialJacobian, LinearMap.coe_mk, AddHom.coe_mk, Pi.zero_apply, mul_comm] using h

def primeLocalDirectional (v : ι → Q.ResidueField) :
    Derivation C (Localization.AtPrime Q) Q.ResidueField :=
  ∑ i, v i • primeLocalPartial Q i

@[simp]
theorem primeNormalPairing_toCotangent (v : ι → Q.ResidueField)
    (x : IsLocalRing.maximalIdeal (Localization.AtPrime Q)) :
    primeNormalPairing Q v ((IsLocalRing.maximalIdeal (Localization.AtPrime Q)).toCotangent x) =
      primeLocalDirectional Q v x := by
  change (∑ i, v i • primePartialNormal Q i) _ = _
  rw [LinearMap.sum_apply]
  change (∑ i, v i * primeLocalPartial Q i x.1) = _
  change (∑ i, v i * primeLocalPartial Q i x.1) =
    (Derivation.coeFnAddMonoidHom (∑ i, v i • primeLocalPartial Q i)) x.1
  rw [map_sum, Finset.sum_apply]
  rfl

theorem primeNormalPairing_linearIndependent {σ : Type*} [Fintype σ]
    (v : σ → ι → Q.ResidueField)
    (hv : LinearIndependent Q.ResidueField
      (fun j => (polynomialTangent (primeResidueMap Q) Q).mkQ (v j))) :
    LinearIndependent Q.ResidueField (fun j => primeNormalPairing Q (v j)) := by
  classical
  apply Fintype.linearIndependent_iff.mpr
  intro a ha j
  have hp : primeNormalPairing Q (∑ j, a j • v j) = 0 := by
    simpa only [map_sum, map_smul] using ha
  have hm := primeNormalPairing_ker_le_tangent Q hp
  have hq : (polynomialTangent (primeResidueMap Q) Q).mkQ (∑ j, a j • v j) = 0 :=
    (Submodule.Quotient.mk_eq_zero _).mpr hm
  have hsum : ∑ j, a j • (polynomialTangent (primeResidueMap Q) Q).mkQ (v j) = 0 := by
    simpa only [map_sum, map_smul] using hq
  exact Fintype.linearIndependent_iff.mp hv a hsum j

theorem prime_cotangent_evaluation_surjective {σ : Type*} [Fintype σ]
    (v : σ → ι → Q.ResidueField)
    (hv : LinearIndependent Q.ResidueField
      (fun j => (polynomialTangent (primeResidueMap Q) Q).mkQ (v j))) :
    Function.Surjective
      (fun x : PrimeLocalCotangent Q => fun j => primeNormalPairing Q (v j) x) := by
  classical
  let f := fun j => primeNormalPairing Q (v j)
  have hf : LinearIndependent Q.ResidueField f := primeNormalPairing_linearIndependent Q v hv
  intro a
  obtain ⟨g, hg⟩ := LinearMap.dualMap_surjective_of_injective
    hf.finsuppLinearCombination_injective (Finsupp.linearCombination Q.ResidueField a)
  refine ⟨(Module.evalEquiv Q.ResidueField (PrimeLocalCotangent Q)).symm g, ?_⟩
  funext j
  change f j ((Module.evalEquiv Q.ResidueField (PrimeLocalCotangent Q)).symm g) = a j
  rw [Module.apply_evalEquiv_symm_apply]
  have hj := LinearMap.congr_fun hg (Finsupp.single j (1 : Q.ResidueField))
  simpa only [LinearMap.dualMap_apply, Finsupp.linearCombination_single, one_smul] using hj

end PiExponent

end

end OAI
end Source0096

-- Source: OAI/NumberTheory/PiExponent/Geometry/CurveComponentRigidity.lean
section Source0097
-- Modified in this edition: unused plain lemmas removed; see reduction.json.
/-
Modification notice for the LogTwo project.
Derived from openai/math (Apache-2.0), revision adc7f1241b42e322a6451854ab7e4b4c146bf78a.
Original source: lean/OAI/NumberTheory/PiExponent/Geometry/CurveComponentRigidity.lean
Changes: Convert module/import declarations to the Lean 4.34 public module format.
See ../THIRD_PARTY_NOTICES.txt for provenance and the recorded changes.
-/

namespace OAI

noncomputable section
namespace PiExponent.CurveComponentRigidity

open scoped BigOperators
open PiExponentApprox NormalBasisRigidity

theorem residueY_ne_zero {m : ℕ} (Q : Ideal (FramePolynomial m)) [Q.IsPrime]
    (hY : MvPolynomial.X (0 : Fin (m + 1)) ∉ Q) :
    primeResidueMap Q (MvPolynomial.X (0 : Fin (m + 1))) ≠ 0 := by
  intro h
  exact hY (Ideal.algebraMap_residueField_eq_zero.mp h)

def NormalProductComparison {m : ℕ} (Q : Ideal (FramePolynomial m)) [Q.IsPrime]
    (hY : MvPolynomial.X (0 : Fin (m + 1)) ∉ Q)
    (w cost : Fin (m + 1) → ℝ) (M : ℝ) : Prop :=
  ∀ A B : Finset (Fin (m + 1)),
    IsNormalBasis (K := Q.ResidueField)
      (fun j => (polynomialTangent (primeResidueMap Q) Q).mkQ
        (Pi.basisFun Q.ResidueField _ j)) A →
    IsNormalBasis (K := Q.ResidueField)
      (fun j => (polynomialTangent (primeResidueMap Q) Q).mkQ
        (frameBasis m (primeResidueMap Q (MvPolynomial.X 0)) (residueY_ne_zero Q hY) j)) B →
    (∏ j ∈ A, w j) ≤ M * ∏ j ∈ B, cost j

def PersistentNormalComparison {m : ℕ} (w cost : Fin (m + 1) → ℝ)
    (M delta : ℝ) (F : FramePolynomial m) (P : Ideal (FramePolynomial m))
    (hY : MvPolynomial.X (0 : Fin (m + 1)) ∉ P) : Prop :=
  ∀ r : ℕ, r < m + 2 → ∀ Q : Ideal (FramePolynomial m), ∀ hQ : Q.IsPrime,
    ∀ hQP : Q ≤ P,
    Q ∈ (frameDerivativeIdeal cost ((r : ℝ) * delta) F).minimalPrimes →
    Q ∈ (frameDerivativeIdeal cost (((r : ℝ) + 1) * delta) F).minimalPrimes →
    1 ≤ Q.height → Q.height ≤ m →
    (∀ p ∈ frameDerivativeIdeal cost ((r : ℝ) * delta) F,
      ∀ word : List (Fin (m + 1)), frameWordCost cost word ≤ delta →
        polynomialFrameWord m word p ∈ Q) →
    @NormalProductComparison m Q hQ (fun h => hY (hQP h)) w cost M

theorem coordinate_constant_of_persistent_comparison {m : ℕ}
    (w cost : Fin (m + 1) → ℝ) (M delta : ℝ)
    (hcost : ∀ i, 0 ≤ cost i) (hdelta : 0 ≤ delta)
    (F : FramePolynomial m) (hF : F ≠ 0)
    (P : Ideal (FramePolynomial m)) (hP : P.IsPrime) (hheight : P.height ≤ m)
    (hY : MvPolynomial.X (0 : Fin (m + 1)) ∉ P)
    (hvanish : ∀ word : List (Fin (m + 1)),
      frameWordCost cost word ≤ ((m : ℝ) + 2) * delta → polynomialFrameWord m word F ∈ P)
    (hcomparison : PersistentNormalComparison w cost M delta F P hY)
    (hseparated : ∀ A B : Finset (Fin (m + 1)), A.card = B.card →
      ∀ i, i ≠ 0 → i ∈ A → i ∉ B →
      (∀ j, i < j → (j ∈ A ↔ j ∈ B)) →
      M * (∏ j ∈ B, cost j) < ∏ j ∈ A, w j) :
    ∃ c : ℂ, MvPolynomial.X (0 : Fin (m + 1)) - MvPolynomial.C c ∈ P := by
  obtain ⟨r, hr, Q, hQr, hQnext, hQP, hQlo, hQhi, hpersist⟩ :=
    exists_persistent_frame_component cost hcost delta hdelta F hF P hP hheight hvanish
  let : Q.IsPrime := hQr.isPrime
  have hYQ : MvPolynomial.X (0 : Fin (m + 1)) ∉ Q := fun h => hY (hQP h)
  have hFQ : F ∈ Q := hQr.le
    (polynomial_mem_frameDerivativeIdeal cost ((r : ℝ) * delta) F
      (mul_nonneg (Nat.cast_nonneg r) hdelta))
  have hQ0 : Q ≠ ⊥ := by
    intro h
    exact hF (by simpa only [h, Ideal.mem_bot] using hFQ)
  have hcomp := hcomparison r hr Q inferInstance hQP hQr hQnext hQlo hQhi hpersist
  let : Algebra.EssFiniteType ℂ Q.ResidueField :=
    Algebra.EssFiniteType.comp ℂ (FramePolynomial m) Q.ResidueField
  have hker (p : FramePolynomial m) : primeResidueMap Q p = 0 ↔ p ∈ Q :=
    Ideal.algebraMap_residueField_eq_zero
  obtain ⟨c, hc⟩ := constant_zeroth_coordinate_of_generic_normal_separation
    (primeResidueMap Q) Q hker hQ0 (residueY_ne_zero Q hYQ)
    (weighted_normalBasis_exclusion _ _ w cost M hcomp hseparated)
  exact ⟨c, hQP hc⟩

end PiExponent.CurveComponentRigidity
end

end OAI
end Source0097

-- Source: OAI/NumberTheory/PiExponent/Approximation/RectangularVolume.lean
section Source0098
-- Modified in this edition: unused plain lemmas removed; see reduction.json.
/-
Modification notice for the LogTwo project.
Derived from openai/math (Apache-2.0), revision adc7f1241b42e322a6451854ab7e4b4c146bf78a.
Original source: lean/OAI/NumberTheory/PiExponent/Approximation/RectangularVolume.lean
Changes: Convert module/import declarations to the Lean 4.34 public module format.
See ../THIRD_PARTY_NOTICES.txt for provenance and the recorded changes.
-/

namespace OAI

open scoped BigOperators

namespace PiExponent

noncomputable def rectangularCutoff {k : ℕ} (κ : Fin k → ℝ) (T : ℝ) (i : Fin k) : ℕ :=
  ⌈T / ((k : ℝ) * κ i)⌉₊

theorem rectangularCutoff_pos {k : ℕ} (hk : 0 < k) (κ : Fin k → ℝ)
    (hκ : ∀ i, 0 < κ i) {T : ℝ} (hT : 0 < T) (i : Fin k) :
    0 < rectangularCutoff κ T i := by
  apply Nat.lt_ceil.mpr
  simpa only [Nat.cast_zero] using
    div_pos hT (mul_pos (by exact_mod_cast hk) (hκ i))

theorem two_le_rectangularCutoff {k : ℕ} (hk : 0 < k) (κ : Fin k → ℝ)
    (hκ : ∀ i, 0 < κ i) {T : ℝ} (i : Fin k)
    (hT : (k : ℝ) * κ i < T) :
    2 ≤ rectangularCutoff κ T i := by
  have hd : 0 < (k : ℝ) * κ i :=
    mul_pos (by exact_mod_cast hk) (hκ i)
  have h : (1 : ℝ) < T / ((k : ℝ) * κ i) :=
    (lt_div_iff₀ hd).mpr (by simpa using hT)
  exact Nat.lt_ceil.mpr (by simpa using h)

theorem rectangularCutoff_coordinate_weight_lt {k : ℕ} (hk : 0 < k)
    (κ : Fin k → ℝ) (hκ : ∀ i, 0 < κ i) {T : ℝ}
    (β : Fin k → ℕ) (hβ : ∀ i, β i < rectangularCutoff κ T i) (i : Fin k) :
    κ i * (β i : ℝ) < T / (k : ℝ) := by
  have hkR : (0 : ℝ) < k := by exact_mod_cast hk
  have hb : (β i : ℝ) < T / ((k : ℝ) * κ i) := Nat.lt_ceil.mp (hβ i)
  have h := mul_lt_mul_of_pos_left hb (hκ i)
  have he : κ i * (T / ((k : ℝ) * κ i)) = T / (k : ℝ) := by
    field_simp [(hκ i).ne']
  simpa only [he] using h

theorem rectangularCutoff_weight_lt {k : ℕ} (hk : 0 < k)
    (κ : Fin k → ℝ) (hκ : ∀ i, 0 < κ i) {T : ℝ}
    (β : Fin k → ℕ) (hβ : ∀ i, β i < rectangularCutoff κ T i) :
    (∑ i, κ i * (β i : ℝ)) < T := by
  have hkR : (0 : ℝ) < k := by exact_mod_cast hk
  have hsum : (∑ i, κ i * (β i : ℝ)) < ∑ _i : Fin k, T / (k : ℝ) := by
    apply Finset.sum_lt_sum
    · intro i hi
      exact (rectangularCutoff_coordinate_weight_lt hk κ hκ β hβ i).le
    · exact ⟨⟨0, hk⟩, Finset.mem_univ _,
        rectangularCutoff_coordinate_weight_lt hk κ hκ β hβ ⟨0, hk⟩⟩
  have he : (∑ _i : Fin k, T / (k : ℝ)) = T := by
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    field_simp [hkR.ne']
  simpa only [he] using hsum

theorem rectangularCutoff_product_lower {k : ℕ} (hk : 0 < k)
    (κ : Fin k → ℝ) (hκ : ∀ i, 0 < κ i) {T : ℝ} (hT : 0 < T) :
    T ^ k / ((k : ℝ) ^ k * ∏ i, κ i) ≤
      ∏ i, (rectangularCutoff κ T i : ℝ) := by
  have hkR : (0 : ℝ) < k := by exact_mod_cast hk
  have hp : (∏ i, T / ((k : ℝ) * κ i)) ≤
      ∏ i, (rectangularCutoff κ T i : ℝ) := by
    apply Finset.prod_le_prod₀
    · intro i hi
      exact (div_pos hT (mul_pos hkR (hκ i))).le
    · intro i hi
      exact Nat.le_ceil _
  simpa only [Finset.prod_div_distrib, Finset.prod_mul_distrib, Finset.prod_const,
    Finset.card_univ, Fintype.card_fin] using hp

end PiExponent

end OAI
end Source0098

-- Source: LogTwo/Geometry/PersistentRigidity.lean
section Source0099
-- Modified in this edition: unused plain lemmas removed; see reduction.json.
/-
Modification notice for the LogTwo project.
Adapted from openai/math (Apache-2.0), revision adc7f1241b42e322a6451854ab7e4b4c146bf78a.
Changes: Adapt the logarithmic rigidity and cutoff arguments to log-two data.
See ../THIRD_PARTY_NOTICES.txt for provenance and the recorded changes.
-/

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

end
end LogTwo.Geometry
end Source0099

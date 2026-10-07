/- Generated rc4 checkpoint for LogTwo.
Modified from the reduced edition: new imports, separate module compilation,
and synchronous elaboration. Original source blocks and notices are retained.
See ../../../THIRD_PARTY_NOTICES.txt and ../../reduction.json.
-/
module
public import LogTwoCheckpoints.Part000
public import LogTwoCheckpoints.Part001
public import LogTwoCheckpoints.Part002
public import LogTwoCheckpoints.Part003
public import LogTwoCheckpoints.Part005
public import LogTwoCheckpoints.Part012
public import LogTwoCheckpoints.Part013
public import LogTwoCheckpoints.Part014
public import Batteries.Logic
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.EpiMono
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Monoidal
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.PullbackFree
public import Mathlib.AlgebraicGeometry.IdealSheaf.Functorial
public import Mathlib.AlgebraicGeometry.Modules.Sheaf
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Basic
public import Mathlib.Analysis.Complex.Polynomial.Basic
public import Mathlib.Data.Opposite
public import Mathlib.Data.SetLike.Basic
public import Mathlib.RingTheory.Length
public import Mathlib.RingTheory.MvPolynomial.Homogeneous
public import Mathlib.RingTheory.Valuation.ValuationSubring
@[expose] public section
set_option Elab.async false

-- Source: LogTwo/Geometry/NormalizationBranch.lean
section Source0375
-- Modified in this edition: unused plain lemmas removed; see reduction.json.
/-
Modification notice for the LogTwo project.
Adapted from openai/math (Apache-2.0), revision adc7f1241b42e322a6451854ab7e4b4c146bf78a.
Changes: Adapt centered-map uniqueness to the constructed weighted compactification.
See ../THIRD_PARTY_NOTICES.txt for provenance and the recorded changes.
-/

/-! Extend the coordinate map to the normalization curve, then identify its
actual DVR pullback with the previously verified varying-center branch.
The extension is constructed by properness and gluing; it is not an input.
The contact formula still requires the stated centered, nonconstant branch
and residue-integrality hypotheses. Divisor degrees are a separate step.
The uniqueness argument follows openai/math ExceptionalCurveDegree.lean
(Apache-2.0); see THIRD_PARTY_NOTICES.txt. -/
namespace LogTwo.Geometry.MatrixCompactification
open OAI PiExponent AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open LogTwo.Interpolation LogTwo.Arithmetic
open CurveValuationCenter PlaceValuationRing PlaceCenteredBranch CurveCenters
open CurveNormalizationModel CurvePlaceCenter
noncomputable section
variable {m : ℕ} (w : Weights m)

instance space_isSeparated : (space w).IsSeparated := by
  constructor
  rw [← terminal.comp_from (structureMap w)]
  infer_instance

variable {E : Type} [Field E] [Algebra ℂ E]
variable (f : E) (hf : Transcendental ℂ f)
variable [FiniteDimensional (IntermediateField.adjoin ℂ {f}) E]

theorem exists_curveMap (z : Fin (m+1) → E) :
    ∃ g : parameterCurve f hf ⟶ space w,
      g ≫ structureMap w = parameterCurveStructureMap f hf ∧
      parameterCurveGenericPoint f hf ≫ g =
        Spec.map (CommRingCat.ofHom (MvPolynomial.aeval z).toRingHom) ≫ affineChart w := by
  apply CurveGlobalMonomial.exists_parameterCurve_extension f hf (structureMap w)
  rw [Category.assoc, affineChart_over, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
  apply congrArg Spec.map
  apply CommRingCat.hom_ext
  ext a
  simp

def curveMap (z : Fin (m+1) → E) : parameterCurve f hf ⟶ space w :=
  (exists_curveMap w f hf z).choose

theorem curveMap_generic (z : Fin (m+1) → E) :
    parameterCurveGenericPoint f hf ≫ curveMap w f hf z =
      Spec.map (CommRingCat.ofHom (MvPolynomial.aeval z).toRingHom) ≫ affineChart w :=
  (exists_curveMap w f hf z).choose_spec.2

variable (p : NormalizedPlace ℂ E)

theorem curveMap_center {J : Type*} (y : J → ℂ) (c : J → Fin m → ℂ)
    (z : Fin (m+1) → E) (j : J) (hc : Centered z (centerPoint (y j) (c j)) p) :
    centerMorphism f hf p ≫ curveMap w f hf z = branchMap w p y c z j hc := by
  apply centerMorphism_comp_eq_of_generic f hf p
  rw [branchMap_generic, curveMap_generic]

/-- The normalization stalk map used below is an isomorphism onto the DVR. -/
instance curve_center_stalk_isIso :
    IsIso (Scheme.stalkClosedPointTo (centerMorphism f hf p)) := inferInstance

/-- Pull back the actual global curve ideal to the DVR and express it using
the canonical affine section-ring isomorphism. No branch choice is an input. -/
def curveLocalIdeal {J : Type*} [Fintype J]
    (y : J → ℂ) (c : J → Fin m → ℂ) (z : Fin (m+1) → E) (T : Fin m → ℕ) :
    Ideal (ring p) :=
  ((((centerIdeal w y c T).comap (curveMap w f hf z)).comap
    (centerMorphism f hf p)).ideal ⟨⊤, isAffineOpen_top _⟩).map
      (Scheme.ΓSpecIso (CommRingCat.of (ring p))).hom.hom

theorem curveLocalIdeal_eq_branchIdeal {J : Type*} [Fintype J]
    (y : J → ℂ) (c : J → Fin m → ℂ) (z : Fin (m+1) → E)
    (j : J) (hc : Centered z (centerPoint (y j) (c j)) p) (T : Fin m → ℕ) :
    curveLocalIdeal w f hf p y c z T = branchIdeal w p y c z j hc T := by
  rw [curveLocalIdeal, ← Scheme.IdealSheafData.comap_comp,
    curveMap_center w f hf p y c z j hc]
  rfl

variable [Algebra.IsIntegral ℂ (IsLocalRing.ResidueField (ring p))]

theorem curveLocalIdeal_colength_eq_contact {J : Type*} [Fintype J]
    (y : J → ℂ) (hy : Function.Injective y) (hy0 : ∀ j, y j ≠ 0)
    (c : J → Fin m → ℂ) (z : Fin (m+1) → E) (j : J)
    (hc : Centered z (centerPoint (y j) (c j)) p)
    (hnc : ∃ i, z i ≠ algebraMap ℂ E (centerPoint (y j) (c j) i))
    (F : ℚ) (hF : 1 / w.theta < F) :
    ((Module.length (ring p) ((ring p) ⧸
      curveLocalIdeal w f hf p y c z (truncationOrders w F))).toNat : ℚ) =
      (scale w).radius * logContactAt p (y j) (hy0 j) z (c j) hc hnc (jetWeight w) := by
  rw [curveLocalIdeal_eq_branchIdeal w f hf p y c z j hc]
  exact branch_colength_eq_contact w p y hy hy0 c z j hc hnc F hF

theorem curveLocalIdeal_colength_ne_top {J : Type*} [Fintype J]
    (y : J → ℂ) (hy : Function.Injective y) (hy0 : ∀ j, y j ≠ 0)
    (c : J → Fin m → ℂ) (z : Fin (m+1) → E) (j : J)
    (hc : Centered z (centerPoint (y j) (c j)) p)
    (hnc : ∃ i, z i ≠ algebraMap ℂ E (centerPoint (y j) (c j) i))
    (F : ℚ) (hF : 1 / w.theta < F) :
    Module.length (ring p) ((ring p) ⧸
      curveLocalIdeal w f hf p y c z (truncationOrders w F)) ≠ ⊤ := by
  rw [curveLocalIdeal_eq_branchIdeal w f hf p y c z j hc]
  exact branch_colength_ne_top w p y hy hy0 c z j hc hnc F hF

end
end LogTwo.Geometry.MatrixCompactification
end Source0375

-- Source: LogTwo/Geometry/JetCenterAt.lean
section Source0376
/-
Modification notice for the LogTwo project.
Adapted from openai/math (Apache-2.0), revision adc7f1241b42e322a6451854ab7e4b4c146bf78a.
Changes: Adapt jet-center identification to varying Y-centers.
See ../THIRD_PARTY_NOTICES.txt for provenance and the recorded changes.
-/

/-! Adapted from openai/math Jets/JetCenterIdentification.lean (Apache-2.0)
to varying Y-centers. A closed point in the chart determines the actual
valuation-center condition; no residue-integrality assumption is needed.
See THIRD_PARTY_NOTICES.txt. -/
namespace LogTwo.Geometry
open OAI PiExponent CategoryTheory AlgebraicGeometry
open CurveValuationCenter PlaceValuationRing
open CompactLogJetIdeal (affineSpace coordinateRing)
noncomputable section
variable {E : Type} [Field E] [Algebra ℂ E]

theorem centeredAt_of_closedPoint_eq {m : ℕ} (p : NormalizedPlace ℂ E)
    (z : Fin (m+1) → E) (y : ℂ) (c : Fin m → ℂ)
    {X : Scheme} (j : affineSpace m ⟶ X) [IsOpenImmersion j]
    (q : Spec (CommRingCat.of (ring p)) ⟶ X)
    (hgeneric : Spec.map (CommRingCat.ofHom (algebraMap (ring p) E)) ≫ q =
      Spec.map (CommRingCat.ofHom (MvPolynomial.aeval z).toRingHom) ≫ j)
    (hclosed : q (IsLocalRing.closedPoint (ring p)) = j (centerPrime y c)) :
    CurveCenters.Centered z (centerPoint y c) p := by
  have hr : Set.range q ⊆ Set.range j := by
    rintro _ ⟨a, rfl⟩
    exact ((IsLocalRing.specializes_closedPoint a).map q.continuous).mem_open
      j.isOpenEmbedding.isOpen_range (hclosed ▸ Set.mem_range_self (centerPrime y c))
  let g := IsOpenImmersion.lift j q hr
  have hg : g ≫ j = q := IsOpenImmersion.lift_fac j q hr
  let φ : coordinateRing m →+* ring p := (Spec.preimage g).hom
  have hgφ : Spec.map (CommRingCat.ofHom φ) = g := Spec.map_preimage g
  have hcomp : CommRingCat.ofHom φ ≫ CommRingCat.ofHom (algebraMap (ring p) E) =
      CommRingCat.ofHom (MvPolynomial.aeval z).toRingHom := by
    apply Spec.map_injective
    rw [Spec.map_comp, hgφ]
    apply (cancel_mono j).mp
    rw [Category.assoc, hg]
    exact hgeneric
  have hgc : g (IsLocalRing.closedPoint (ring p)) = centerPrime y c := by
    apply j.isOpenEmbedding.injective
    change (g ≫ j) (IsLocalRing.closedPoint (ring p)) = _
    rw [hg, hclosed]
  have hcomap : PrimeSpectrum.comap φ (IsLocalRing.closedPoint (ring p)) =
      centerPrime y c := by
    change (Spec.map (CommRingCat.ofHom φ)) (IsLocalRing.closedPoint (ring p)) = _
    rw [hgφ, hgc]
  intro i
  let P : coordinateRing m := MvPolynomial.X i - MvPolynomial.C (centerPoint y c i)
  have hmem : φ P ∈ IsLocalRing.maximalIdeal (ring p) := by
    change P ∈ (PrimeSpectrum.comap φ (IsLocalRing.closedPoint (ring p))).asIdeal
    rw [hcomap]
    change P ∈ WeightedBezout.pointIdeal (centerPoint y c)
    rw [WeightedBezout.mem_pointIdeal]
    simp [P]
  have hpos := p.valuation.toValuation.mem_maximalIdeal_iff.mp hmem
  have heval := congrArg
    (fun f : CommRingCat.of (coordinateRing m) ⟶ CommRingCat.of E => f P) hcomp
  change algebraMap (ring p) E (φ P) = MvPolynomial.aeval z P at heval
  change 0 < p.valuation (algebraMap (ring p) E (φ P)) at hpos
  rw [heval] at hpos
  simpa [P, centerPoint] using hpos

end
end LogTwo.Geometry
end Source0376

-- Source: LogTwo/Geometry/CurveIdealSupport.lean
section Source0377
/-
Modification notice for the LogTwo project.
Adapted from openai/math (Apache-2.0), revision adc7f1241b42e322a6451854ab7e4b4c146bf78a.
Changes: Adapt generic-image and off-support ideal arguments to the project geometry.
See ../THIRD_PARTY_NOTICES.txt for provenance and the recorded changes.
-/

/-! Nonzero curve pullbacks and their actual finite colength sum.
The finite set of all centered places is reused, avoiding a new general
curve-zero-locus finiteness argument. Its identification with a section divisor and Euler degree is proved in
CurveSectionDegree under an explicit invertible-presentation hypothesis.
The generic-image and off-support arguments adapt openai/math
Ampleness/ExceptionalCurveDegree.lean (Apache-2.0).
See THIRD_PARTY_NOTICES.txt. -/
namespace LogTwo.Geometry
open OAI PiExponent AlgebraicGeometry CategoryTheory MvPolynomial
open CurveValuationCenter PlaceValuationRing CurveCenters
noncomputable section
variable {m : ℕ} {E : Type} [Field E] [Algebra ℂ E]

/-- A coordinate difference in the radical suffices; logarithmic generators
do not have to be evaluated or expanded. -/
theorem map_jetIdealAt_eq_top_of_nonconstant
    (y : ℂ) (c : Fin m → ℂ) (T : Fin m → ℕ) (e : Fin (m+1) → ℕ)
    (he : ∀ i, 0 < e i) (z : Fin (m+1) → E)
    (hnc : ∃ i, z i ≠ algebraMap ℂ E (centerPoint y c i)) :
    (jetIdealAt y c T e).map (MvPolynomial.aeval z).toRingHom = ⊤ := by
  obtain ⟨i, hi⟩ := hnc
  have hg : X i - C (centerPoint y c i) ∈ (jetIdealAt y c T e).radical := by
    rw [radical_jetIdealAt y c T e he]
    simp
  obtain ⟨n, hn⟩ := hg
  apply Ideal.eq_top_of_isUnit_mem _
    (Ideal.mem_map_of_mem (MvPolynomial.aeval z).toRingHom hn)
  change IsUnit (MvPolynomial.aeval z ((X i - C (centerPoint y c i)) ^ n))
  rw [map_pow]
  apply IsUnit.pow
  apply isUnit_iff_ne_zero.mpr
  simpa using sub_ne_zero.mpr hi

theorem map_jetProductIdeal_eq_top_of_transcendental {J : Type*} [Fintype J]
    (y : J → ℂ) (c : J → Fin m → ℂ) (T : Fin m → ℕ)
    (e : Fin (m+1) → ℕ) (he : ∀ i, 0 < e i) (z : Fin (m+1) → E)
    (hz : ∃ i, Transcendental ℂ (z i)) :
    (jetProductIdeal y c T e).map (MvPolynomial.aeval z).toRingHom = ⊤ := by
  classical
  change Ideal.mapHom (MvPolynomial.aeval z).toRingHom
    (∏ j, jetIdealAt (y j) (c j) T e) = _
  rw [map_prod]
  simp only [Ideal.mapHom_apply, map_jetIdealAt_eq_top_of_nonconstant
    _ _ T e he z (ContactFamilyAt.nonconstant z _ _ hz)]
  rw [← Ideal.one_eq_top]
  exact Finset.prod_const_one

namespace MatrixCompactification
open LogTwo.Interpolation LogTwo.Arithmetic
open CurveNormalizationModel CurvePlaceCenter
variable (w : Weights m)
variable (f : E) (hf : Transcendental ℂ f)
variable [FiniteDimensional (IntermediateField.adjoin ℂ {f}) E]

theorem curveIdeal_generic_pullback {J : Type*} [Fintype J]
    (y : J → ℂ) (c : J → Fin m → ℂ) (T : Fin m → ℕ)
    (z : Fin (m+1) → E) (hz : ∃ i, Transcendental ℂ (z i)) :
    ((centerIdeal w y c T).comap (curveMap w f hf z)).comap
      (parameterCurveGenericPoint f hf) =
      PiExponentSeshadri.IdealPullback.specIdeal (⊤ : Ideal E) := by
  rw [← Scheme.IdealSheafData.comap_comp, curveMap_generic, centerIdeal_affine_pullback,
    map_jetProductIdeal_eq_top_of_transcendental y c T _ (scale w).jetPowers_pos z hz]

theorem curveIdeal_ne_bot {J : Type*} [Fintype J]
    (y : J → ℂ) (c : J → Fin m → ℂ) (T : Fin m → ℕ)
    (z : Fin (m+1) → E) (hz : ∃ i, Transcendental ℂ (z i)) :
    (centerIdeal w y c T).comap (curveMap w f hf z) ≠ ⊥ := by
  intro h
  have he := curveIdeal_generic_pullback w f hf y c T z hz
  rw [h, Scheme.IdealSheafData.comap_bot] at he
  have he' := congrArg (fun I : (Spec (.of E)).IdealSheafData =>
    (I.ideal ⟨⊤, isAffineOpen_top _⟩).map (Scheme.ΓSpecIso (.of E)).hom.hom) he
  simp [Ideal.map_top] at he'

variable (p : NormalizedPlace ℂ E)

theorem curveMap_centered_of_mem_support {J : Type*} [Fintype J]
    (y : J → ℂ) (c : J → Fin m → ℂ) (T : Fin m → ℕ)
    (z : Fin (m+1) → E)
    (hp : (centerMorphism f hf p ≫ curveMap w f hf z)
      (IsLocalRing.closedPoint (ring p)) ∈ (centerIdeal w y c T).support) :
    ∃ j, Centered z (centerPoint (y j) (c j)) p := by
  change _ ∈ ((centerIdeal w y c T).support : Set (space w)) at hp
  rw [centerIdeal_support] at hp
  obtain ⟨j, a, ha⟩ := Set.mem_iUnion.mp hp
  have hap : CompactJetIdealAt.point (y j) (c j) a = centerPrime (y j) (c j) := by
    have h := Set.mem_range_self (f := CompactJetIdealAt.point (y j) (c j)) a
    rw [CompactJetIdealAt.range_point] at h
    exact h
  refine ⟨j, centeredAt_of_closedPoint_eq p z (y j) (c j) (affineChart w)
    (centerMorphism f hf p ≫ curveMap w f hf z) ?_ ?_⟩
  · rw [← Category.assoc, centerMorphism_generic, curveMap_generic]
  · exact ha.symm.trans (congrArg (affineChart w) hap)

theorem curveLocalIdeal_eq_top_of_not_mem_support {J : Type*} [Fintype J]
    (y : J → ℂ) (c : J → Fin m → ℂ) (T : Fin m → ℕ)
    (z : Fin (m+1) → E)
    (hp : (centerMorphism f hf p ≫ curveMap w f hf z)
      (IsLocalRing.closedPoint (ring p)) ∉ (centerIdeal w y c T).support) :
    curveLocalIdeal w f hf p y c z T = ⊤ := by
  let q := centerMorphism f hf p ≫ curveMap w f hf z
  have havoid (a : Spec (.of (ring p))) : q a ∉ (centerIdeal w y c T).support :=
    ((IsLocalRing.specializes_closedPoint a).map q.continuous).mem_open
      (centerIdeal w y c T).support.isClosed.isOpen_compl hp
  have ht := CompactJetIdeal.restrict_eq_top_of_disjoint (centerIdeal w y c T) q havoid
  rw [curveLocalIdeal, ← Scheme.IdealSheafData.comap_comp, ht]
  exact Ideal.map_top _

variable {K : ℕ}
variable (hfinite : ∀ t : E, Transcendental ℂ t →
  FiniteDimensional (IntermediateField.adjoin ℂ {t}) E)
variable (z : Fin (m+1) → E) (y : Fin K → ℂ) (c : Fin K → Fin m → ℂ)
variable (hz : ∃ i, Transcendental ℂ (z i))

theorem curveLocalIdeal_eq_top_of_not_mem_places (T : Fin m → ℕ)
    (hp : p ∉ ContactFamilyAt.places hfinite z y c hz) :
    curveLocalIdeal w f hf p y c z T = ⊤ := by
  apply curveLocalIdeal_eq_top_of_not_mem_support
  intro h
  exact hp ((ContactFamilyAt.mem_places hfinite z y c hz p).mpr
    (curveMap_centered_of_mem_support w f hf p y c T z h))

theorem curveLocalIdeal_colength_zero_off_places (T : Fin m → ℕ)
    (hp : p ∉ ContactFamilyAt.places hfinite z y c hz) :
    Module.length (ring p) ((ring p) ⧸ curveLocalIdeal w f hf p y c z T) = 0 := by
  rw [curveLocalIdeal_eq_top_of_not_mem_places w f hf p hfinite z y c hz T hp]
  exact Module.length_eq_zero

/-- The actual local colength function, supported on all centered places.
The section-divisor comparison is in CurveSectionDegree and requires an
invertible presentation of the ideal. -/
def curveColengthCycle (T : Fin m → ℕ) : NormalizedPlace ℂ E →₀ ℕ :=
  Finsupp.onFinset (ContactFamilyAt.places hfinite z y c hz)
    (fun p => (Module.length (ring p) ((ring p) ⧸ curveLocalIdeal w f hf p y c z T)).toNat)
    (fun p hp => by
      by_contra hn
      exact hp (by rw [curveLocalIdeal_colength_zero_off_places w f hf p hfinite z y c hz T hn]; rfl))

theorem curveColengthCycle_apply (T : Fin m → ℕ) (p : NormalizedPlace ℂ E) :
    curveColengthCycle w f hf hfinite z y c hz T p =
      (Module.length (ring p) ((ring p) ⧸ curveLocalIdeal w f hf p y c z T)).toNat := rfl

theorem curveColengthCycle_support_subset (T : Fin m → ℕ) :
    (curveColengthCycle w f hf hfinite z y c hz T).support ⊆
      ContactFamilyAt.places hfinite z y c hz := Finsupp.support_onFinset_subset

variable (hres : ∀ p : NormalizedPlace ℂ E,
  Algebra.IsIntegral ℂ (IsLocalRing.ResidueField (ring p)))
variable (hy : Function.Injective y) (hy0 : ∀ j, y j ≠ 0) (hK : 0 < K)

include hfinite hz hres hy hy0 hK in
theorem curveLocalIdeal_colength_finite_all (F : ℚ) (hF : 1 / w.theta < F)
    (p : NormalizedPlace ℂ E) :
    Module.length (ring p) ((ring p) ⧸
      curveLocalIdeal w f hf p y c z (truncationOrders w F)) ≠ ⊤ := by
  let := hres p
  by_cases hp : p ∈ ContactFamilyAt.places hfinite z y c hz
  · let j := ContactFamilyAt.center hfinite z y c hz hK p
    exact curveLocalIdeal_colength_ne_top w f hf p y hy hy0 c z j
      (ContactFamilyAt.centered hfinite z y c hz hK p hp)
      (ContactFamilyAt.nonconstant z _ _ hz) F hF
  · rw [curveLocalIdeal_colength_zero_off_places w f hf p hfinite z y c hz _ hp]
    simp

include hy in
theorem curveColengthCycle_eq_contact (F : ℚ) (hF : 1 / w.theta < F)
    (p : NormalizedPlace ℂ E) :
    (curveColengthCycle w f hf hfinite z y c hz (truncationOrders w F) p : ℚ) =
      (scale w).radius * ContactFamilyAt.contact hres hfinite z y hy0 c hz hK (jetWeight w) p := by
  let := hres p
  by_cases hp : p ∈ ContactFamilyAt.places hfinite z y c hz
  · rw [ContactFamilyAt.contact_eq hres hfinite z y hy0 c hz hK _ p hp]
    exact curveLocalIdeal_colength_eq_contact w f hf p y hy hy0 c z _
      (ContactFamilyAt.centered hfinite z y c hz hK p hp)
      (ContactFamilyAt.nonconstant z _ _ hz) F hF
  · rw [curveColengthCycle_apply,
      curveLocalIdeal_colength_zero_off_places w f hf p hfinite z y c hz _ hp]
    simp [ContactFamilyAt.contact, hp]

include hy in
theorem curveColengthCycle_sum_eq_contact (F : ℚ) (hF : 1 / w.theta < F) :
    (curveColengthCycle w f hf hfinite z y c hz (truncationOrders w F)).sum
      (fun _ n => (n : ℚ)) =
      (scale w).radius * ∑ p ∈ ContactFamilyAt.places hfinite z y c hz,
        ContactFamilyAt.contact hres hfinite z y hy0 c hz hK (jetWeight w) p := by
  rw [Finsupp.sum_of_support_subset _ (curveColengthCycle_support_subset w f hf hfinite z y c hz _)
    (fun _ n => (n : ℚ)) (by simp), Finset.mul_sum]
  exact Finset.sum_congr rfl (fun p _ =>
    curveColengthCycle_eq_contact w f hf hfinite z y c hz hres hy hy0 hK F hF p)

include hres hy hy0 hK in
theorem curveColengthCycle_natCast_eq_length (F : ℚ) (hF : 1 / w.theta < F)
    (p : NormalizedPlace ℂ E) :
    (curveColengthCycle w f hf hfinite z y c hz (truncationOrders w F) p : ℕ∞) =
      Module.length (ring p) ((ring p) ⧸
        curveLocalIdeal w f hf p y c z (truncationOrders w F)) := by
  rw [curveColengthCycle_apply]
  exact ENat.natCast_toNat
    (curveLocalIdeal_colength_finite_all w f hf hfinite z y c hz hres hy hy0 hK F hF p)

include hres hy hy0 hK in
theorem curveColengthCycle_support_eq_places (F : ℚ) (hF : 1 / w.theta < F) :
    (curveColengthCycle w f hf hfinite z y c hz (truncationOrders w F)).support =
      ContactFamilyAt.places hfinite z y c hz := by
  classical
  apply Finset.Subset.antisymm
  · exact curveColengthCycle_support_subset w f hf hfinite z y c hz _
  · intro p hp
    apply Finsupp.mem_support_iff.mpr
    intro he
    have hc := curveColengthCycle_eq_contact w f hf hfinite z y c hz hres hy hy0 hK F hF p
    rw [he, Nat.cast_zero] at hc
    have hR : (0 : ℚ) < (scale w).radius := by exact_mod_cast (scale w).radius_pos
    have hpos := mul_pos hR
      (ContactFamilyAt.contact_pos hres hfinite z y hy0 c hz hK (jetWeight w)
        (jetWeight_pos w) p hp)
    exact (ne_of_gt hpos) hc.symm

end MatrixCompactification
end
end LogTwo.Geometry
end Source0377

-- Source: OAI/NumberTheory/PiExponent/Approximation/LinePowerLaws.lean
section Source0378
/-
Modification notice for the LogTwo project.
Derived from openai/math (Apache-2.0), revision adc7f1241b42e322a6451854ab7e4b4c146bf78a.
Original source: lean/OAI/NumberTheory/PiExponent/Approximation/LinePowerLaws.lean
Changes: Convert module/import declarations to the Lean 4.34 public module format.
See ../THIRD_PARTY_NOTICES.txt for provenance and the recorded changes.
-/

namespace OAI

noncomputable section

universe u v

namespace PiExponent.NumericalAmpleness
open CategoryTheory AlgebraicGeometry
lemma isIso_of_locally_isIso {X : Scheme} {M N : X.Modules} (f : M ⟶ N)
    (h : ∀ x : X, ∃ U : X.Opens, x ∈ U ∧ IsIso ((Scheme.Modules.restrictFunctor U.ι).map f)) :
    IsIso f := by
  have : Mono f := PiExponent.CoherentTwist.mono_of_local f (fun x => by
    obtain ⟨U,hx,hi⟩ := h x
    have := hi
    exact ⟨U,hx,inferInstance⟩)
  have : Epi f := PiExponent.CoherentTwist.epi_of_local f (fun x => by
    obtain ⟨U,hx,hi⟩ := h x
    have := hi
    exact ⟨U,hx,inferInstance⟩)
  exact isIso_of_mono_of_epi f
end PiExponent.NumericalAmpleness

namespace PiExponentSeshadri.TensorLocalization
open CategoryTheory MonoidalCategory
universe v' u'
variable {C : Type u} [Category.{v} C] [MonoidalCategory C]
  {D : Type u'} [Category.{v'} D] (F : C ⥤ D)

lemma map_tensor_right_unit {P Q L : C} (f : P ⟶ Q) (e : L ≅ 𝟙_ C)
    [IsIso (F.map f)] : IsIso (F.map (f ⊗ₘ 𝟙 L)) := by
  let ε (A : C) : A ⊗ L ≅ A := tensorIso (Iso.refl A) e ≪≫ ρ_ A
  have h : (f ⊗ₘ 𝟙 L) ≫ (ε Q).hom = (ε P).hom ≫ f := by
    simp only [ε, Iso.trans_hom, tensorIso_hom, Iso.refl_hom]
    rw [← Category.assoc, tensorHom_comp_tensorHom, Category.comp_id, Category.id_comp]
    have ht : f ⊗ₘ e.hom = (𝟙 P ⊗ₘ e.hom) ≫ (f ⊗ₘ 𝟙 (𝟙_ C)) := by
      rw [tensorHom_comp_tensorHom]
      simp only [Category.id_comp, Category.comp_id]
    rw [ht, Category.assoc, tensorHom_id, rightUnitor_naturality, Category.assoc]
  have hh : IsIso (F.map ((f ⊗ₘ 𝟙 L) ≫ (ε Q).hom)) := by
    rw [h, F.map_comp]
    infer_instance
  rw [F.map_comp] at hh
  exact (isIso_comp_right_iff _ _).mp hh

end PiExponentSeshadri.TensorLocalization

namespace PiExponentSeshadri.Geometry

section
open CategoryTheory AlgebraicGeometry TopologicalSpace MonoidalCategory
open scoped AlgebraicGeometry
variable {X : Scheme}

lemma sheafification_tensor_right_isIso
    {P Q : PresheafOfModules X.ringCatSheaf.obj} (f : P ⟶ Q) (L : LineBundle X)
    [IsIso ((PresheafOfModules.sheafification (𝟙 X.ringCatSheaf.obj)).map f)] :
    IsIso ((PresheafOfModules.sheafification (𝟙 X.ringCatSheaf.obj)).map
      (PresheafOfModulesOfCommRing.Monoidal.tensorHom (R := X.presheaf) f (𝟙 L.sheaf.val))) := by
  let F : PresheafOfModules X.ringCatSheaf.obj ⥤ X.Modules :=
    PresheafOfModules.sheafification (𝟙 X.ringCatSheaf.obj)
  apply PiExponent.NumericalAmpleness.isIso_of_locally_isIso
  intro x
  obtain ⟨U, hx, ⟨e⟩⟩ := L.locallyRankOne x
  refine ⟨U, hx, ?_⟩
  let R : PresheafOfModules X.ringCatSheaf.obj ⥤
      PresheafOfModules U.toScheme.ringCatSheaf.obj := modulePresheafRestrict U.ι
  let S : PresheafOfModules U.toScheme.ringCatSheaf.obj ⥤ U.toScheme.Modules :=
    PresheafOfModules.sheafification (𝟙 U.toScheme.ringCatSheaf.obj)
  let : MonoidalCategory (PresheafOfModules U.toScheme.ringCatSheaf.obj) :=
    PresheafOfModulesOfCommRing.monoidalCategory (R := U.toScheme.presheaf)
  have hf : IsIso (S.map (R.map f)) := by
    apply (NatIso.isIso_map_iff (moduleSheafificationRestrict U.ι) f).mp
    change IsIso ((Scheme.Modules.restrictFunctor U.ι).map (F.map f))
    let : IsIso (F.map f) := inferInstanceAs
      (IsIso ((PresheafOfModules.sheafification (𝟙 X.ringCatSheaf.obj)).map f))
    exact (Scheme.Modules.restrictFunctor U.ι).map_isIso (F.map f)
  let ep : R.obj L.sheaf.val ≅ 𝟙_ (PresheafOfModules U.toScheme.ringCatSheaf.obj) :=
    (SheafOfModules.forget _).mapIso e
  have ht : IsIso (S.map ((R.map f) ⊗ₘ 𝟙 (R.obj L.sheaf.val))) :=
    TensorLocalization.map_tensor_right_unit S (R.map f) ep
  apply (NatIso.isIso_map_iff (moduleSheafificationRestrict U.ι) _).mpr
  let g := PresheafOfModulesOfCommRing.Monoidal.tensorHom (R := X.presheaf) f (𝟙 L.sheaf.val)
  change IsIso (S.map (R.map g))
  have heq := modulePresheafTensorRestrict_natural U f (𝟙 L.sheaf.val)
  let : IsIso (S.map (modulePresheafTensorRestrict U P L.sheaf.val).hom) :=
    (S.mapIso (modulePresheafTensorRestrict U P L.sheaf.val)).isIso_hom
  let : IsIso (S.map (modulePresheafTensorRestrict U Q L.sheaf.val).hom) :=
    (S.mapIso (modulePresheafTensorRestrict U Q L.sheaf.val)).isIso_hom
  have hcomp : IsIso (S.map (R.map g ≫
      (modulePresheafTensorRestrict U Q L.sheaf.val).hom)) := by
    erw [heq, S.map_comp]
    have ht' : IsIso (S.map
        (PresheafOfModulesOfCommRing.Monoidal.tensorHom (R := U.toScheme.presheaf)
          (R.map f) (R.map (𝟙 L.sheaf.val)))) := by
      rw [R.map_id]
      exact ht
    exact (inferInstance : IsIso (C := U.toScheme.Modules)
      (S.map (modulePresheafTensorRestrict U P L.sheaf.val).hom ≫ S.map
        (PresheafOfModulesOfCommRing.Monoidal.tensorHom (R := U.toScheme.presheaf)
          (R.map f) (R.map (𝟙 L.sheaf.val)))))
  erw [S.map_comp] at hcomp
  exact (isIso_comp_right_iff (C := U.toScheme.Modules) _ _).mp hcomp

end

open CategoryTheory AlgebraicGeometry TopologicalSpace MonoidalCategory BraidedCategory
open scoped AlgebraicGeometry
variable {X : Scheme}

lemma sheafification_tensor_left_isIso
    {P Q : PresheafOfModules X.ringCatSheaf.obj} (f : P ⟶ Q) (L : LineBundle X)
    [IsIso ((PresheafOfModules.sheafification (𝟙 X.ringCatSheaf.obj)).map f)] :
    IsIso ((PresheafOfModules.sheafification (𝟙 X.ringCatSheaf.obj)).map
      (PresheafOfModulesOfCommRing.Monoidal.tensorHom (R := X.presheaf) (𝟙 L.sheaf.val) f)) := by
  let : MonoidalCategory (PresheafOfModules X.ringCatSheaf.obj) :=
    PresheafOfModulesOfCommRing.monoidalCategory (R := X.presheaf)
  let : SymmetricCategory (PresheafOfModules X.ringCatSheaf.obj) :=
    PresheafOfModulesOfCommRing.symmetricCategory (R := X.presheaf)
  let F : PresheafOfModules X.ringCatSheaf.obj ⥤ X.Modules :=
    PresheafOfModules.sheafification (𝟙 X.ringCatSheaf.obj)
  have : IsIso (F.map (f ⊗ₘ 𝟙 L.sheaf.val)) := sheafification_tensor_right_isIso f L
  let : IsIso (F.map (β_ L.sheaf.val P).hom) :=
    (F.mapIso (β_ L.sheaf.val P)).isIso_hom
  have h : IsIso (F.map ((𝟙 L.sheaf.val ⊗ₘ f) ≫ (β_ L.sheaf.val Q).hom)) := by
    rw [braiding_naturality, F.map_comp]
    exact (inferInstance : IsIso (C := X.Modules)
      (F.map (β_ L.sheaf.val P).hom ≫ F.map (f ⊗ₘ 𝟙 L.sheaf.val)))
  rw [F.map_comp] at h
  exact (isIso_comp_right_iff _ _).mp h

def sheafificationTensorRight (P : PresheafOfModules X.ringCatSheaf.obj)
    (L : LineBundle X) :
    (PresheafOfModules.sheafification (𝟙 X.ringCatSheaf.obj)).obj
      (PresheafOfModulesOfCommRing.Monoidal.tensorObj (R := X.presheaf) P L.sheaf.val) ≅
    moduleTensor X ((PresheafOfModules.sheafification (𝟙 X.ringCatSheaf.obj)).obj P)
      L.sheaf := by
  let F := PresheafOfModules.sheafification (𝟙 X.ringCatSheaf.obj)
  let η := (PresheafOfModules.sheafificationAdjunction (𝟙 X.ringCatSheaf.obj)).unit.app P
  have : IsIso (F.map η) :=
    isIso_of_comp_hom_eq_id _
      ((PresheafOfModules.sheafificationAdjunction (𝟙 X.ringCatSheaf.obj)).left_triangle_components P)
  let ht : IsIso (F.map (PresheafOfModulesOfCommRing.Monoidal.tensorHom
      (R := X.presheaf) η (𝟙 L.sheaf.val))) := sheafification_tensor_right_isIso η L
  exact @asIso _ _ _ _ (F.map (PresheafOfModulesOfCommRing.Monoidal.tensorHom (R := X.presheaf)
    η (𝟙 L.sheaf.val))) ht

def sheafificationTensorLeft (P : PresheafOfModules X.ringCatSheaf.obj)
    (L : LineBundle X) :
    (PresheafOfModules.sheafification (𝟙 X.ringCatSheaf.obj)).obj
      (PresheafOfModulesOfCommRing.Monoidal.tensorObj (R := X.presheaf) L.sheaf.val P) ≅
    moduleTensor X L.sheaf
      ((PresheafOfModules.sheafification (𝟙 X.ringCatSheaf.obj)).obj P) := by
  let F := PresheafOfModules.sheafification (𝟙 X.ringCatSheaf.obj)
  let η := (PresheafOfModules.sheafificationAdjunction (𝟙 X.ringCatSheaf.obj)).unit.app P
  have : IsIso (F.map η) :=
    isIso_of_comp_hom_eq_id _
      ((PresheafOfModules.sheafificationAdjunction (𝟙 X.ringCatSheaf.obj)).left_triangle_components P)
  let ht : IsIso (F.map (PresheafOfModulesOfCommRing.Monoidal.tensorHom
      (R := X.presheaf) (𝟙 L.sheaf.val) η)) := sheafification_tensor_left_isIso η L
  exact @asIso _ _ _ _ (F.map (PresheafOfModulesOfCommRing.Monoidal.tensorHom (R := X.presheaf)
    (𝟙 L.sheaf.val) η)) ht

def lineTensorAssoc (L M N : LineBundle X) :
    moduleTensor X (moduleTensor X L.sheaf M.sheaf) N.sheaf ≅
      moduleTensor X L.sheaf (moduleTensor X M.sheaf N.sheaf) := by
  let : MonoidalCategory (PresheafOfModules X.ringCatSheaf.obj) :=
    PresheafOfModulesOfCommRing.monoidalCategory (R := X.presheaf)
  exact (sheafificationTensorRight (L.sheaf.val ⊗ M.sheaf.val) N).symm ≪≫
    (PresheafOfModules.sheafification (𝟙 X.ringCatSheaf.obj)).mapIso
      (α_ L.sheaf.val M.sheaf.val N.sheaf.val) ≪≫
    sheafificationTensorLeft (M.sheaf.val ⊗ N.sheaf.val) L

def linePowerAdd (L : LineBundle X) : ∀ m n : ℕ,
    modulePow X L.sheaf (m + n) ≅
      moduleTensor X (modulePow X L.sheaf m) (modulePow X L.sheaf n)
  | 0, n => by
      simpa only [Nat.zero_add, modulePow, structureSheaf] using (moduleTensorUnit (modulePow X L.sheaf n)).symm
  | m + 1, n => by
      rw [Nat.succ_add]
      exact moduleTensorIso (Iso.refl _) (linePowerAdd L m n) ≪≫
        (lineTensorAssoc L (L.pow m) (L.pow n)).symm

def linePowerMul (L : LineBundle X) (m : ℕ) : ∀ n : ℕ,
    modulePow X (modulePow X L.sheaf m) n ≅ modulePow X L.sheaf (m * n)
  | 0 => Iso.refl _
  | n + 1 => by
      rw [Nat.mul_succ, Nat.add_comm (m * n) m]
      exact moduleTensorIso (Iso.refl _) (linePowerMul L m n) ≪≫
        (linePowerAdd L m (m * n)).symm

end PiExponentSeshadri.Geometry

end

end OAI
end Source0378

-- Source: OAI/NumberTheory/PiExponent/Approximation/FrameTensorPowers.lean
section Source0379
-- Modified in this edition: unused plain lemmas removed; see reduction.json.
/-
Modification notice for the LogTwo project.
Derived from openai/math (Apache-2.0), revision adc7f1241b42e322a6451854ab7e4b4c146bf78a.
Original source: lean/OAI/NumberTheory/PiExponent/Approximation/FrameTensorPowers.lean
Changes: Convert module/import declarations to the Lean 4.34 public module format.
See ../THIRD_PARTY_NOTICES.txt for provenance and the recorded changes.
-/

namespace OAI

namespace PiExponentSeshadri.Geometry
noncomputable section
open CategoryTheory AlgebraicGeometry TopologicalSpace MonoidalCategory
open scoped AlgebraicGeometry
open PiExponentSeshadri.Frames
variable {X : Scheme}

lemma tensor_unit_end {C : Type*} [Category C] [MonoidalCategory C]
    (f g : 𝟙_ C ⟶ 𝟙_ C) :
    (f ⊗ₘ g) ≫ (λ_ (𝟙_ C)).hom = (λ_ (𝟙_ C)).hom ≫ (f ≫ g) := by
  rw [MonoidalCategory.tensorHom_def, Category.assoc, leftUnitor_naturality, ← Category.assoc,
    unitors_equal, rightUnitor_naturality, Category.assoc]

lemma moduleTensorUnit_scalar (f g : structureSheaf X ⟶ structureSheaf X) :
    moduleTensorMap f g ≫ (moduleTensorUnit (structureSheaf X)).hom =
      (moduleTensorUnit (structureSheaf X)).hom ≫ (f ≫ g) := by
  let : MonoidalCategory (PresheafOfModules X.ringCatSheaf.obj) :=
    PresheafOfModulesOfCommRing.monoidalCategory (R := X.presheaf)
  let F : PresheafOfModules X.ringCatSheaf.obj ⥤ X.Modules :=
    PresheafOfModules.sheafification (𝟙 X.ringCatSheaf.obj)
  let G : X.Modules ⥤ PresheafOfModules X.ringCatSheaf.obj :=
    SheafOfModules.forget X.ringCatSheaf ⋙
      PresheafOfModules.restrictScalars (𝟙 X.ringCatSheaf.obj)
  let ε : G ⋙ F ⟶ 𝟭 X.Modules :=
    (PresheafOfModules.sheafificationAdjunction (𝟙 X.ringCatSheaf.obj)).counit
  have h : (f.val ⊗ₘ g.val) ≫ (λ_ (structureSheaf X).val).hom =
      (λ_ (structureSheaf X).val).hom ≫ (f ≫ g).val := by
    let f₀ : 𝟙_ (PresheafOfModules X.ringCatSheaf.obj) ⟶
        𝟙_ (PresheafOfModules X.ringCatSheaf.obj) := f.val
    let g₀ : 𝟙_ (PresheafOfModules X.ringCatSheaf.obj) ⟶
        𝟙_ (PresheafOfModules X.ringCatSheaf.obj) := g.val
    exact tensor_unit_end f₀ g₀
  change F.map (f.val ⊗ₘ g.val) ≫ (F.map (λ_ (structureSheaf X).val).hom ≫ ε.app (structureSheaf X)) =
    (F.map (λ_ (structureSheaf X).val).hom ≫ ε.app (structureSheaf X)) ≫ (f ≫ g)
  erw [← Category.assoc, ← F.map_comp, h, F.map_comp, Category.assoc, Category.assoc]
  congr 1
  exact ε.naturality (f ≫ g)

def endPower (f : structureSheaf X ⟶ structureSheaf X) : ℕ → (structureSheaf X ⟶ structureSheaf X)
  | 0 => 𝟙 _
  | n + 1 => f ≫ endPower f n

lemma endValue_endPower (f : structureSheaf X ⟶ structureSheaf X) (n : ℕ) :
    endValue (endPower f n) = endValue f ^ n := by
  induction n with
  | zero =>
    change (1 : Γ(X, ⊤)) = endValue f ^ 0
    exact (pow_zero _).symm
  | succ n hn =>
    calc
      endValue (endPower f (n + 1)) = endValue f * endValue (endPower f n) :=
        endValue_comp f (endPower f n)
      _ = endValue f * endValue f ^ n := congrArg (endValue f * ·) hn
      _ = _ := (pow_succ' _ _).symm

lemma moduleTensorUnit_natural {M N : X.Modules} (g : M ⟶ N) :
    moduleTensorMap (𝟙 (structureSheaf X)) g ≫ (moduleTensorUnit N).hom =
      (moduleTensorUnit M).hom ≫ g := by
  let : MonoidalCategory (PresheafOfModules X.ringCatSheaf.obj) :=
    PresheafOfModulesOfCommRing.monoidalCategory (R := X.presheaf)
  let F : PresheafOfModules X.ringCatSheaf.obj ⥤ X.Modules :=
    PresheafOfModules.sheafification (𝟙 X.ringCatSheaf.obj)
  let G : X.Modules ⥤ PresheafOfModules X.ringCatSheaf.obj :=
    SheafOfModules.forget X.ringCatSheaf ⋙
      PresheafOfModules.restrictScalars (𝟙 X.ringCatSheaf.obj)
  let ε : G ⋙ F ⟶ 𝟭 X.Modules :=
    (PresheafOfModules.sheafificationAdjunction (𝟙 X.ringCatSheaf.obj)).counit
  change F.map ((𝟙 (structureSheaf X).val) ⊗ₘ g.val) ≫
    (F.map (λ_ N.val).hom ≫ ε.app N) =
    (F.map (λ_ M.val).hom ≫ ε.app M) ≫ g
  have h : ((𝟙 (structureSheaf X).val) ⊗ₘ g.val) ≫ (λ_ N.val).hom =
      (λ_ M.val).hom ≫ g.val := by
    rw [id_tensorHom]
    exact leftUnitor_naturality g.val
  have hF : F.map (𝟙 (structureSheaf X).val ⊗ₘ g.val) ≫ F.map (λ_ N.val).hom =
      F.map (λ_ M.val).hom ≫ F.map g.val :=
    (F.map_comp _ _).symm.trans ((congrArg F.map h).trans (F.map_comp _ _))
  refine (Category.assoc _ _ _).symm.trans ?_
  refine (congrArg (· ≫ ε.app N) hF).trans ?_
  refine (Category.assoc _ _ _).trans ?_
  refine (congrArg (F.map (λ_ M.val).hom ≫ ·) (ε.naturality g)).trans ?_
  exact (Category.assoc _ _ _).symm

lemma modulePowMap_unitPower (f : structureSheaf X ⟶ structureSheaf X) (n : ℕ) :
    modulePowMap f n ≫ (unitPowerIso n).hom =
      (unitPowerIso n).hom ≫ endPower f n := by
  induction n with
  | zero =>
    change 𝟙 (structureSheaf X) ≫ 𝟙 (structureSheaf X) = 𝟙 (structureSheaf X) ≫ 𝟙 (structureSheaf X)
    rfl
  | succ n hn =>
    change moduleTensorMap f (modulePowMap f n) ≫
      ((moduleTensorUnit _).hom ≫ (unitPowerIso n).hom) =
        ((moduleTensorUnit _).hom ≫ (unitPowerIso n).hom) ≫ (f ≫ endPower f n)
    calc
      _ = moduleTensorMap f (modulePowMap f n) ≫
          moduleTensorMap (𝟙 (structureSheaf X)) (unitPowerIso n).hom ≫
            (moduleTensorUnit (structureSheaf X)).hom := by
        rw [moduleTensorUnit_natural]
      _ = moduleTensorMap f ((unitPowerIso n).hom ≫ endPower f n) ≫
            (moduleTensorUnit (structureSheaf X)).hom := by
        rw [← Category.assoc, ← moduleTensorMap_comp, Category.comp_id, hn]
      _ = moduleTensorMap (𝟙 (structureSheaf X)) (unitPowerIso n).hom ≫
          moduleTensorMap f (endPower f n) ≫ (moduleTensorUnit (structureSheaf X)).hom := by
        rw [← Category.assoc, ← moduleTensorMap_comp, Category.id_comp]
      _ = (moduleTensorUnit (modulePow X (structureSheaf X) n)).hom ≫
          (unitPowerIso n).hom ≫ (f ≫ endPower f n) := by
        rw [moduleTensorUnit_scalar, ← Category.assoc, moduleTensorUnit_natural,
          Category.assoc]
      _ = _ := by simp only [Category.assoc]

def globalPowerFrame {M : X.Modules} (e : M ≅ structureSheaf X) (n : ℕ) :
    modulePow X M n ≅ structureSheaf X :=
  (modulePowFunctor n).mapIso e ≪≫ unitPowerIso n

lemma powerSection_coefficient {M : X.Modules} (e : M ≅ structureSheaf X)
    (s : structureSheaf X ⟶ M) (n : ℕ) :
    coefficient (globalPowerFrame e n) (powerSection s n) = coefficient e s ^ n := by
  change endValue ((unitPowerIso n).inv ≫ modulePowMap s n ≫
    (modulePowMap e.hom n ≫ (unitPowerIso n).hom)) = _
  erw [← Category.assoc (modulePowMap s n), ← modulePowMap_comp,
    modulePowMap_unitPower, Iso.inv_hom_id_assoc, endValue_endPower]
  rfl

end
end PiExponentSeshadri.Geometry

end OAI
end Source0379

-- Source: OAI/NumberTheory/PiExponent/Approximation/TensorPowerRestriction.lean
section Source0380
/-
Modification notice for the LogTwo project.
Derived from openai/math (Apache-2.0), revision adc7f1241b42e322a6451854ab7e4b4c146bf78a.
Original source: lean/OAI/NumberTheory/PiExponent/Approximation/TensorPowerRestriction.lean
Changes: Convert module/import declarations to the Lean 4.34 public module format.
See ../THIRD_PARTY_NOTICES.txt for provenance and the recorded changes.
-/

namespace OAI

noncomputable section

namespace PiExponentSeshadri.Geometry

section
open CategoryTheory AlgebraicGeometry TopologicalSpace MonoidalCategory
open scoped AlgebraicGeometry
variable {X : Scheme}

def modulePowRestrict (U : X.Opens) (M : X.Modules) :
    ∀ n, (modulePow X M n).restrict U.ι ≅ modulePow U.toScheme (M.restrict U.ι) n
  | 0 => Scheme.Modules.restrictUnitIso U.ι
  | n + 1 => moduleTensorRestrict U M (modulePow X M n) ≪≫
      moduleTensorIso (Iso.refl _) (modulePowRestrict U M n)

lemma modulePowRestrict_natural (U : X.Opens) {M N : X.Modules} (f : M ⟶ N) (n : ℕ) :
    (Scheme.Modules.restrictFunctor U.ι).map (modulePowMap f n) ≫
      (modulePowRestrict U N n).hom =
    (modulePowRestrict U M n).hom ≫
      modulePowMap ((Scheme.Modules.restrictFunctor U.ι).map f) n := by
  induction n with
  | zero =>
    change (Scheme.Modules.restrictFunctor U.ι).map (𝟙 (structureSheaf X)) ≫
      (Scheme.Modules.restrictUnitIso U.ι).hom =
      (Scheme.Modules.restrictUnitIso U.ι).hom ≫ 𝟙 _
    erw [(Scheme.Modules.restrictFunctor U.ι).map_id, Category.id_comp]
  | succ n hn =>
    change (Scheme.Modules.restrictFunctor U.ι).map (moduleTensorMap f (modulePowMap f n)) ≫
      ((moduleTensorRestrict U N (modulePow X N n)).hom ≫
        (moduleTensorIso (Iso.refl _) (modulePowRestrict U N n)).hom) =
      ((moduleTensorRestrict U M (modulePow X M n)).hom ≫
        (moduleTensorIso (Iso.refl _) (modulePowRestrict U M n)).hom) ≫
          moduleTensorMap ((Scheme.Modules.restrictFunctor U.ι).map f)
            (modulePowMap ((Scheme.Modules.restrictFunctor U.ι).map f) n)
    simp only [moduleTensorIso_hom, Iso.refl_hom]
    rw [← Category.assoc, moduleTensorRestrict_natural, Category.assoc,
      ← moduleTensorMap_comp, Category.comp_id, hn]
    rw [Category.assoc, ← moduleTensorMap_comp, Category.id_comp]

lemma modulePowMap_restrict_isIso (U : X.Opens) {M N : X.Modules} (f : M ⟶ N)
    [IsIso ((Scheme.Modules.restrictFunctor U.ι).map f)] (n : ℕ) :
    IsIso ((Scheme.Modules.restrictFunctor U.ι).map (modulePowMap f n)) := by
  have h := modulePowRestrict_natural U f n
  have heq : (Scheme.Modules.restrictFunctor U.ι).map (modulePowMap f n) =
      (modulePowRestrict U M n).hom ≫
        modulePowMap ((Scheme.Modules.restrictFunctor U.ι).map f) n ≫
          (modulePowRestrict U N n).inv := by
    rw [← Category.assoc, ← h, Category.assoc, Iso.hom_inv_id, Category.comp_id]
  rw [heq]
  infer_instance

lemma powerSection_restrict_isIso (U : X.Opens) {M : X.Modules}
    (s : structureSheaf X ⟶ M)
    [IsIso ((Scheme.Modules.restrictFunctor U.ι).map s)] (n : ℕ) :
    IsIso ((Scheme.Modules.restrictFunctor U.ι).map (powerSection s n)) := by
  let := modulePowMap_restrict_isIso U s n
  unfold powerSection
  rw [(Scheme.Modules.restrictFunctor U.ι).map_comp]
  infer_instance

lemma sectionOpen_le_powerSection {M : X.Modules} (s : structureSheaf X ⟶ M) (n : ℕ) :
    sectionOpen X s ≤ sectionOpen X (powerSection s n) := by
  refine iSup_le fun U => iSup_le fun hU => ?_
  let := hU
  exact le_iSup_of_le U (le_iSup_of_le (powerSection_restrict_isIso U s n) le_rfl)

end

open CategoryTheory AlgebraicGeometry TopologicalSpace
open scoped AlgebraicGeometry
open PiExponentSeshadri.Frames
variable {X : Scheme}

def powerRestrictionUnit (U : X.Opens) (n : ℕ) :
    structureSheaf U.toScheme ≅ structureSheaf U.toScheme :=
  (Scheme.Modules.restrictUnitIso U.ι).symm ≪≫
    (Scheme.Modules.restrictFunctor U.ι).mapIso (unitPowerIso n).symm ≪≫
      modulePowRestrict U (structureSheaf X) n ≪≫
        (modulePowFunctor n).mapIso (Scheme.Modules.restrictUnitIso U.ι) ≪≫
          unitPowerIso n

lemma restrictPowerSection_factor (U : X.Opens) {M : X.Modules}
    (s : structureSheaf X ⟶ M) (n : ℕ) :
    restrictSection U.ι (powerSection s n) ≫ (modulePowRestrict U M n).hom =
      (powerRestrictionUnit U n).hom ≫
        powerSection (restrictSection U.ι s) n := by
  have hs : (Scheme.Modules.restrictUnitIso U.ι).hom ≫ restrictSection U.ι s =
      (Scheme.Modules.restrictFunctor U.ι).map s := by
    let F : X.Modules ⥤ U.toScheme.Modules := Scheme.Modules.restrictFunctor U.ι
    let e : F.obj (structureSheaf X) ≅ structureSheaf U.toScheme :=
      Scheme.Modules.restrictUnitIso U.ι
    exact e.hom_inv_id_assoc (F.map s)
  dsimp only [restrictSection, powerSection, powerRestrictionUnit, Iso.trans_hom,
    Iso.symm_hom, Functor.mapIso_hom, modulePowFunctor]
  erw [(Scheme.Modules.restrictFunctor U.ι).map_comp]
  repeat' erw [Category.assoc]
  erw [modulePowRestrict_natural]
  erw [Iso.hom_inv_id_assoc, ← modulePowMap_comp]
  erw [show (Scheme.Modules.restrictUnitIso U.ι).hom ≫
      ((Scheme.Modules.restrictUnitIso U.ι).inv ≫
        (Scheme.Modules.restrictFunctor U.ι).map s) =
        (Scheme.Modules.restrictFunctor U.ι).map s from hs]
  rfl

end PiExponentSeshadri.Geometry

end

end OAI
end Source0380

-- Source: OAI/NumberTheory/PiExponent/Approximation/SectionPowerOpens.lean
section Source0381
/-
Modification notice for the LogTwo project.
Derived from openai/math (Apache-2.0), revision adc7f1241b42e322a6451854ab7e4b4c146bf78a.
Original source: lean/OAI/NumberTheory/PiExponent/Approximation/SectionPowerOpens.lean
Changes: Convert module/import declarations to the Lean 4.34 public module format.
See ../THIRD_PARTY_NOTICES.txt for provenance and the recorded changes.
-/

namespace OAI

noncomputable section

namespace PiExponentSeshadri

namespace Frames
open CategoryTheory AlgebraicGeometry
lemma coefficient_precompose {X : Scheme} {M : X.Modules} (e : M ≅ O X)
    (a : O X ⟶ O X) (s : O X ⟶ M) :
    coefficient e (a ≫ s) = endValue a * coefficient e s := by
  change endValue ((a ≫ s) ≫ e.hom) = _
  rw [Category.assoc]
  exact endValue_comp a (s ≫ e.hom)
end Frames

namespace Geometry
open CategoryTheory AlgebraicGeometry TopologicalSpace
open scoped AlgebraicGeometry
open PiExponentSeshadri.Frames
variable {X : Scheme}

def localPowerFrame (U : X.Opens) {M : X.Modules}
    (e : M.restrict U.ι ≅ structureSheaf U.toScheme) (n : ℕ) :
    (modulePow X M n).restrict U.ι ≅ structureSheaf U.toScheme :=
  modulePowRestrict U M n ≪≫ globalPowerFrame e n

lemma local_powerSection_coefficient (U : X.Opens) {M : X.Modules}
    (e : M.restrict U.ι ≅ structureSheaf U.toScheme)
    (s : structureSheaf X ⟶ M) (n : ℕ) :
    coefficient (localPowerFrame U e n) (restrictSection U.ι (powerSection s n)) =
      endValue (powerRestrictionUnit U n).hom *
        coefficient e (restrictSection U.ι s) ^ n := by
  change coefficient (globalPowerFrame e n)
    (restrictSection U.ι (powerSection s n) ≫ (modulePowRestrict U M n).hom) = _
  calc
    _ = coefficient (globalPowerFrame e n)
        ((powerRestrictionUnit U n).hom ≫ powerSection (restrictSection U.ι s) n) :=
      congrArg (coefficient (globalPowerFrame e n)) (restrictPowerSection_factor U s n)
    _ = endValue (powerRestrictionUnit U n).hom *
        coefficient (globalPowerFrame e n) (powerSection (restrictSection U.ι s) n) :=
      coefficient_precompose _ _ _
    _ = _ := congrArg (endValue (powerRestrictionUnit U n).hom * ·)
      (powerSection_coefficient e _ n)

lemma local_powerSection_coefficient_unit (U : X.Opens) (n : ℕ) :
    IsUnit (endValue (powerRestrictionUnit U n).hom) := by
  have h : IsIso (powerRestrictionUnit U n).hom := inferInstance
  exact (end_isIso_iff (powerRestrictionUnit U n).hom).mp h

theorem LineBundle.sectionOpen_power (L : LineBundle X) (s : GlobalSections X L.sheaf)
    {n : ℕ} (hn : 0 < n) :
    sectionOpen X (powerSection s n) = sectionOpen X s := by
  have hlocal (U : X.Opens) (e : L.sheaf.restrict U.ι ≅ structureSheaf U.toScheme) :
      U.ι ⁻¹ᵁ sectionOpen X (powerSection s n) = U.ι ⁻¹ᵁ sectionOpen X s := by
    change U.ι ⁻¹ᵁ SectionOpens.isoOpen (powerSection s n) =
      U.ι ⁻¹ᵁ SectionOpens.isoOpen s
    calc
      _ = U.toScheme.basicOpen (coefficient (localPowerFrame U e n)
          (restrictSection U.ι (powerSection s n))) :=
        preimage_isoOpen (powerSection s n) U.ι (localPowerFrame U e n)
      _ = U.toScheme.basicOpen (endValue (powerRestrictionUnit U n).hom *
          coefficient e (restrictSection U.ι s) ^ n) :=
        congrArg U.toScheme.basicOpen (local_powerSection_coefficient U e s n)
      _ = U.toScheme.basicOpen (coefficient e (restrictSection U.ι s)) := by
        rw [Scheme.basicOpen_mul,
          Scheme.basicOpen_of_isUnit _ (local_powerSection_coefficient_unit U n),
          top_inf_eq]
        exact U.toScheme.basicOpen_pow (coefficient e (restrictSection U.ι s)) hn
      _ = _ := (preimage_isoOpen s U.ι e).symm
  ext x
  obtain ⟨U, hxU, ⟨e⟩⟩ := L.locallyRankOne x
  have h := congrArg (fun V : U.toScheme.Opens => (⟨x, hxU⟩ : U.toScheme) ∈ V) (hlocal U e)
  exact Iff.of_eq h

end Geometry

end PiExponentSeshadri

end

end OAI
end Source0381

-- Source: OAI/NumberTheory/PiExponent/Ampleness/AmpleCommonDegree.lean
section Source0382
/-
Modification notice for the LogTwo project.
Derived from openai/math (Apache-2.0), revision adc7f1241b42e322a6451854ab7e4b4c146bf78a.
Original source: lean/OAI/NumberTheory/PiExponent/Ampleness/AmpleCommonDegree.lean
Changes: Convert module/import declarations to the Lean 4.34 public module format.
See ../THIRD_PARTY_NOTICES.txt for provenance and the recorded changes.
-/

namespace OAI

namespace PiExponentSeshadri.Geometry
noncomputable section
open CategoryTheory AlgebraicGeometry TopologicalSpace TopologicalSpace.Opens
open scoped AlgebraicGeometry
variable {X : Scheme}

theorem LineBundle.common_degree (L : LineBundle X) {ι : Type} [Fintype ι]
    (d : ι → ℕ) (hd : ∀ i, 0 < d i)
    (s : ∀ i, GlobalSections X (modulePow X L.sheaf (d i))) :
    ∃ n : ℕ, 0 < n ∧ ∃ t : ι → GlobalSections X (modulePow X L.sheaf n),
      ∀ i, sectionOpen X (t i) = sectionOpen X (s i) := by
  classical
  let n := ∏ i, d i
  have hn : 0 < n := Finset.prod_pos (fun i _ => hd i)
  have hdiv (i : ι) : d i ∣ n := Finset.dvd_prod_of_mem d (Finset.mem_univ i)
  have heq (i : ι) : d i * (n / d i) = n := Nat.mul_div_cancel' (hdiv i)
  let e (i : ι) : modulePow X (modulePow X L.sheaf (d i)) (n / d i) ≅
      modulePow X L.sheaf n :=
    linePowerMul L (d i) (n / d i) ≪≫ eqToIso (congrArg (modulePow X L.sheaf) (heq i))
  refine ⟨n, hn, fun i => powerSection (s i) (n / d i) ≫ (e i).hom, ?_⟩
  intro i
  change SectionOpens.isoOpen (powerSection (s i) (n / d i) ≫ (e i).hom) = _
  rw [SectionOpens.isoOpen_postcomp]
  exact (L.pow (d i)).sectionOpen_power (s i)
    (Nat.div_pos (Nat.le_of_dvd hn (hdiv i)) (hd i))

theorem LineBundle.ample_common_degree_cover [CompactSpace X] (L : LineBundle X)
    (hL : L.IsAmple) :
    ∃ n : ℕ, 0 < n ∧ ∃ l : ℕ,
      ∃ s : Fin l → GlobalSections X (modulePow X L.sheaf n),
        (⨆ i, sectionOpen X (s i)) = ⊤ ∧
        (∀ i, IsAffineOpen (sectionOpen X (s i))) ∧
        (∀ i, (sectionOpen X (s i) : Set X).Nonempty) := by
  classical
  have hex (x : X) := hL x ⊤ (by trivial)
  choose d hd s hs hst ha using hex
  obtain ⟨I, hI⟩ := isCompact_univ.elim_finite_subcover
    (fun x => (sectionOpen X (s x) : Set X)) (fun x => (sectionOpen X (s x)).isOpen)
    (by intro x _; exact Set.mem_iUnion.mpr ⟨x, hs x⟩)
  obtain ⟨n, hn, t, ht⟩ := L.common_degree (fun i : I => d i.val)
    (fun i => hd i.val) (fun i => s i.val)
  let e := (Fintype.equivFin I).symm
  refine ⟨n, hn, Fintype.card I, fun i => t (e i), ?_, ?_, ?_⟩
  · apply top_unique
    intro x _
    obtain ⟨i, hi⟩ := Set.mem_iUnion.mp (hI (show x ∈ Set.univ from trivial))
    obtain ⟨hi, hx⟩ := Set.mem_iUnion.mp hi
    apply Opens.mem_iSup.mpr
    refine ⟨e.symm ⟨i, hi⟩, ?_⟩
    change x ∈ sectionOpen X (t (e (e.symm ⟨i, hi⟩)))
    rw [Equiv.apply_symm_apply, ht]
    exact hx
  · intro i
    rw [ht]
    exact ha (e i).val
  · intro i
    rw [ht]
    exact ⟨(e i).val, hs (e i).val⟩

end
end PiExponentSeshadri.Geometry

end OAI
end Source0382

-- Source: OAI/NumberTheory/PiExponent/Approximation/IntegralLineSections.lean
section Source0383
-- Modified in this edition: unused plain lemmas removed; see reduction.json.
/-
Modification notice for the LogTwo project.
Derived from openai/math (Apache-2.0), revision adc7f1241b42e322a6451854ab7e4b4c146bf78a.
Original source: lean/OAI/NumberTheory/PiExponent/Approximation/IntegralLineSections.lean
Changes: Convert module/import declarations to the Lean 4.34 public module format.
See ../THIRD_PARTY_NOTICES.txt for provenance and the recorded changes.
-/

namespace OAI

noncomputable section

namespace PiExponentSeshadri

namespace Geometry
open CategoryTheory AlgebraicGeometry TopologicalSpace
open scoped AlgebraicGeometry
variable {X : Scheme}

lemma trivialModule_restriction_injective [IsIntegral X] (M : X.Modules)
    (e : M ≅ structureSheaf X) {U V : X.Opens} (i : U ⟶ V) [Nonempty U] :
    Function.Injective (M.presheaf.map i.op) := by
  intro s t h
  apply (ConcreteCategory.bijective_of_isIso
    (((Scheme.Modules.toPresheaf X).mapIso e).app (Opposite.op V)).hom).injective
  have hn := e.hom.mapPresheaf.naturality i.op
  have heq := congrArg (fun a => e.hom.app U a) h
  have hh (a : Γ(M, V)) :
      e.hom.app U (M.presheaf.map i.op a) =
        X.presheaf.map i.op (e.hom.app V a) := by
    exact CategoryTheory.congr_fun hn a
  rw [hh, hh] at heq
  exact map_injective_of_isIntegral X i heq

theorem LineBundle.restriction_injective [IsIntegral X] (L : LineBundle X)
    {U V : X.Opens} (i : U ⟶ V) [Nonempty U] :
    Function.Injective (L.sheaf.presheaf.map i.op) := by
  intro s t h
  apply L.sheaf.isSheaf.section_ext
  intro x hx
  obtain ⟨T, hxT, ⟨e⟩⟩ := L.locallyRankOne x
  let f := T.ι
  let U' : T.toScheme.Opens := f ⁻¹ᵁ U
  let V' : T.toScheme.Opens := f ⁻¹ᵁ V
  have hU' : Nonempty U' := by
    obtain ⟨y, hyT, hyU⟩ := nonempty_preirreducible_inter T.isOpen U.isOpen
      ⟨x, hxT⟩ (by obtain ⟨u⟩ := ‹Nonempty U›; exact ⟨u.val, u.property⟩)
    exact ⟨⟨⟨y, hyT⟩, hyU⟩⟩
  have : Nonempty U' := hU'
  have : Nonempty T := ⟨⟨x, hxT⟩⟩
  let j : U' ⟶ V' := homOfLE (fun _ h => leOfHom i h)
  let W := f ''ᵁ V'
  have hWV : W ≤ V := f.image_preimage_le V
  refine ⟨W, hWV, ?_, ?_⟩
  · exact ⟨⟨x, hxT⟩, hx, rfl⟩
  · apply trivialModule_restriction_injective (L.sheaf.restrict f) e j
    change L.sheaf.presheaf.map ((f.opensFunctor.map j).op)
        (L.sheaf.presheaf.map (homOfLE hWV).op s) =
      L.sheaf.presheaf.map ((f.opensFunctor.map j).op)
        (L.sheaf.presheaf.map (homOfLE hWV).op t)
    have hh := congrArg
      (fun a => L.sheaf.presheaf.map (homOfLE (f.image_preimage_le U)).op a) h
    simp only [← ConcreteCategory.comp_apply, ← Functor.map_comp] at hh ⊢
    have eq : i.op ≫ (homOfLE (f.image_preimage_le U)).op =
        (homOfLE hWV).op ≫ (f.opensFunctor.map j).op := Subsingleton.elim _ _
    rw [eq] at hh
    simpa only [Functor.map_comp, ConcreteCategory.comp_apply] using hh

theorem LineBundle.section_restriction_injective [IsIntegral X] (L : LineBundle X)
    (U : X.Opens) [Nonempty U] :
    Function.Injective (fun s : GlobalSections X L.sheaf => s.app U (1 : Γ(X, U))) := by
  intro s t h
  have natural (s : GlobalSections X L.sheaf) (V : X.Opens) :
      s.app V (1 : Γ(X, V)) = L.sheaf.presheaf.map
        (homOfLE (show V ≤ ⊤ from le_top)).op (s.app ⊤ (1 : Γ(X, ⊤))) := by
    have hs := CategoryTheory.congr_fun (s.mapPresheaf.naturality
      (homOfLE (show V ≤ ⊤ from le_top)).op) (1 : Γ(X, ⊤))
    change s.app V (X.presheaf.map (homOfLE (show V ≤ ⊤ from le_top)).op 1) =
      L.sheaf.presheaf.map (homOfLE (show V ≤ ⊤ from le_top)).op
        (s.app ⊤ (1 : Γ(X, ⊤))) at hs
    simpa only [map_one, ConcreteCategory.comp_apply] using hs
  have ht : s.app ⊤ (1 : Γ(X, ⊤)) = t.app ⊤ (1 : Γ(X, ⊤)) := by
    apply L.restriction_injective (homOfLE (show U ≤ ⊤ from le_top))
    rw [← natural s U, ← natural t U]
    exact h
  ext V a
  change Γ(X, V) at a
  have hv : s.app V (1 : Γ(X, V)) = t.app V (1 : Γ(X, V)) := by
    rw [natural s, natural t, ht]
  have scalar (s : GlobalSections X L.sheaf) :
      s.app V a = a • s.app V (1 : Γ(X, V)) := by
    have hs := s.app_smul (r := a) (x := (1 : Γ(X, V)))
    change s.app V (a * 1 : Γ(X, V)) = _ at hs
    simpa only [mul_one] using hs
  rw [scalar s, scalar t, hv]

variable [IsIntegral X]

theorem LineBundle.noZeroSMulDivisors (L : LineBundle X)
    (U : X.Opens) [Nonempty U] : NoZeroSMulDivisors Γ(X, U) Γ(L.sheaf, U) where
  eq_zero_or_eq_zero_of_smul_eq_zero {a m} h := by
    obtain ⟨x, hx⟩ := ‹Nonempty U›
    obtain ⟨T, hxT, ⟨e⟩⟩ := L.locallyRankOne x
    let V : T.toScheme.Opens := T.ι ⁻¹ᵁ U
    have : Nonempty V := ⟨⟨⟨x, hxT⟩, hx⟩⟩
    have : Nonempty T := ⟨⟨x, hxT⟩⟩
    let W : X.Opens := T.ι ''ᵁ V
    have : Nonempty W := ⟨⟨x, ⟨x, hxT⟩, hx, rfl⟩⟩
    let i : W ⟶ U := homOfLE (T.ι.image_preimage_le U)
    let ar : Γ(X, W) := X.presheaf.map i.op a
    let mr : Γ(L.sheaf, W) := L.sheaf.presheaf.map i.op m
    have hr : ar • mr = 0 := by
      have hh := congrArg (fun z => L.sheaf.presheaf.map i.op z) h
      simpa only [L.sheaf.map_smul, map_zero] using hh
    let ar' : Γ(T.toScheme, V) := (T.ι.appIso V).hom ar
    let mr' : Γ(L.sheaf.restrict T.ι, V) := (L.sheaf.restrictAppIso T.ι V).inv mr
    let cr : Γ(T.toScheme, V) := e.hom.app V mr'
    have hr' : ar' • mr' = 0 := by
      rw [← Scheme.Modules.smul_restrictAppIso_inv_apply]
      simp only [hr, map_zero]
    have hmul : ar' * cr = 0 := by
      have hh := e.hom.app_smul (r := ar') (x := mr')
      change e.hom.app V (ar' • mr') = ar' * cr at hh
      rw [hr', map_zero] at hh
      exact hh.symm
    rcases mul_eq_zero.mp hmul with ha | hm
    · left
      apply map_injective_of_isIntegral X i
      have hinj := (ConcreteCategory.bijective_of_isIso (T.ι.appIso V).hom).injective
      apply hinj
      simpa only [map_zero] using ha
    · right
      apply L.restriction_injective i
      have hinj := (ConcreteCategory.bijective_of_isIso
        (((Scheme.Modules.toPresheaf T.toScheme).mapIso e).app (Opposite.op V)).hom).injective
      apply (ConcreteCategory.bijective_of_isIso (L.sheaf.restrictAppIso T.ι V).inv).injective
      apply hinj
      change cr = e.hom.app V ((L.sheaf.restrictAppIso T.ι V).inv
        (L.sheaf.presheaf.map i.op 0))
      refine hm.trans ?_
      simp only [map_zero]
      rfl

theorem LineBundle.mono_section (L : LineBundle X)
    (s : GlobalSections X L.sheaf) (hs : s ≠ 0) : Mono s := by
  have hmono : Mono s.val := by
    apply PresheafOfModules.mono_of_injective
    intro U
    by_cases hU : Nonempty U.unop
    · let := hU
      let := L.noZeroSMulDivisors U.unop
      intro a b hab
      change Γ(X, U.unop) at a b
      have hc : s.app U.unop (1 : Γ(X, U.unop)) ≠ 0 := by
        intro h
        apply hs
        apply L.section_restriction_injective U.unop
        exact h
      have hscalar (a : Γ(X, U.unop)) : s.app U.unop a =
          a • s.app U.unop (1 : Γ(X, U.unop)) := by
        have hh := s.app_smul (r := a) (x := (1 : Γ(X, U.unop)))
        change s.app U.unop (a * 1 : Γ(X, U.unop)) = _ at hh
        simpa only [mul_one] using hh
      have heq : s.app U.unop a = s.app U.unop b := hab
      rw [hscalar a, hscalar b] at heq
      exact (smul_left_injective Γ(X, U.unop) hc) heq
    · have he : U.unop = ⊥ := by
        apply Opens.ext
        ext x
        exact ⟨fun hx => (hU ⟨⟨x, hx⟩⟩).elim, fun h => h.elim⟩
      have : Subsingleton Γ(X, U.unop) := by rw [he]; infer_instance
      intro a b _
      change Γ(X, U.unop) at a b
      exact Subsingleton.elim a b
  exact (SheafOfModules.forget X.ringCatSheaf).mono_of_mono_map hmono

end Geometry

namespace Frames
open CategoryTheory AlgebraicGeometry
variable {X Y : Scheme}
lemma coefficient_injective {M : X.Modules} (e : M ≅ O X) :
    Function.Injective (coefficient e) := by
  intro s t h
  apply (cancel_mono e.hom).1
  exact endValue_injective h
lemma coefficient_zero {M : X.Modules} (e : M ≅ O X) :
    coefficient e (0 : O X ⟶ M) = 0 := by
  rw [coefficient, CategoryTheory.Limits.zero_comp]
  rfl
lemma restrictSection_zero (φ : Y ⟶ X) [IsOpenImmersion φ] {M : X.Modules} :
    restrictSection φ (0 : O X ⟶ M) = 0 := by
  ext U a
  rfl
end Frames

namespace Geometry
open CategoryTheory AlgebraicGeometry TopologicalSpace
open PiExponentSeshadri.Frames
variable {X Y : Scheme}
lemma LineBundle.restrict_sections_injective [IsIntegral X] (L : LineBundle X)
    (f : Y ⟶ X) [IsOpenImmersion f] [Nonempty Y] :
    Function.Injective (fun s : GlobalSections X L.sheaf =>
      (Scheme.Modules.restrictFunctor f).map s) := by
  intro s t h
  let U : X.Opens := f ''ᵁ ⊤
  have : Nonempty U := by
    obtain ⟨y⟩ := ‹Nonempty Y›
    exact ⟨⟨f y, y, Set.mem_univ y, rfl⟩⟩
  apply L.section_restriction_injective U
  have he := congrArg (fun s : (structureSheaf X).restrict f ⟶ L.sheaf.restrict f =>
    s.app ⊤ (1 : Γ(X, U))) h
  exact he

lemma LineBundle.restricted_coefficient_injective [IsIntegral X] (L : LineBundle X)
    (f : Y ⟶ X) [IsOpenImmersion f] [Nonempty Y]
    (e : L.sheaf.restrict f ≅ O Y) :
    Function.Injective (fun s : GlobalSections X L.sheaf => coefficient e (restrictSection f s)) := by
  intro s t h
  apply L.restrict_sections_injective f
  let u : (structureSheaf X).restrict f ≅ structureSheaf Y :=
    Scheme.Modules.restrictUnitIso f
  apply (cancel_epi u.inv).mp
  exact coefficient_injective e h

end Geometry

end PiExponentSeshadri

end

end OAI
end Source0383

-- Source: OAI/NumberTheory/PiExponent/Approximation/PowerSectionExtension.lean
section Source0384
/-
Modification notice for the LogTwo project.
Derived from openai/math (Apache-2.0), revision adc7f1241b42e322a6451854ab7e4b4c146bf78a.
Original source: lean/OAI/NumberTheory/PiExponent/Approximation/PowerSectionExtension.lean
Changes: Convert module/import declarations to the Lean 4.34 public module format.
See ../THIRD_PARTY_NOTICES.txt for provenance and the recorded changes.
-/

namespace OAI

noncomputable section

namespace PiExponentSeshadri

namespace Frames
open CategoryTheory AlgebraicGeometry
@[simp] lemma coefficient_scalarEnd {X : Scheme} {M : X.Modules}
    (e : M ≅ O X) (a : Γ(X, ⊤)) :
    coefficient e (scalarEnd a ≫ e.inv) = a := by
  simp only [coefficient, Category.assoc, Iso.inv_hom_id, Category.comp_id,
    endValue_scalarEnd]
end Frames

namespace Geometry

section
open CategoryTheory AlgebraicGeometry TopologicalSpace
open scoped AlgebraicGeometry
open PiExponentSeshadri.Frames
variable {X : Scheme}

lemma affine_function_denom [IsAffine X] (a : Γ(X, ⊤))
    (f : Γ((X.basicOpen a).toScheme, ⊤)) :
    ∃ N : ℕ, ∀ n ≥ N, ∃ g : Γ(X, ⊤),
      (X.basicOpen a).ι.appTop g = f * (X.basicOpen a).ι.appTop a ^ n := by
  obtain ⟨N, g, hg⟩ := IsLocalization.Away.surj a f
  refine ⟨N, fun n hn => ⟨g * a ^ (n - N), ?_⟩⟩
  change algebraMap Γ(X, ⊤) Γ((X.basicOpen a).toScheme, ⊤) (g * a ^ (n - N)) =
    f * algebraMap Γ(X, ⊤) Γ((X.basicOpen a).toScheme, ⊤) a ^ n
  rw [map_mul, map_pow, ← hg, mul_assoc, ← pow_add, Nat.add_sub_of_le hn]

theorem local_affine_power_extension (U : X.Opens) [IsAffine U.toScheme]
    {M : X.Modules} (e : M.restrict U.ι ≅ structureSheaf U.toScheme)
    (s : GlobalSections X M)
    (f : Γ((U.toScheme.basicOpen (coefficient e (restrictSection U.ι s))).toScheme, ⊤)) :
    ∃ N : ℕ, ∀ n ≥ N, ∃ t : structureSheaf U.toScheme ⟶ (modulePow X M n).restrict U.ι,
      restrictSection (U.toScheme.basicOpen (coefficient e (restrictSection U.ι s))).ι t =
        scalarEnd f ≫ restrictSection
          (U.toScheme.basicOpen (coefficient e (restrictSection U.ι s))).ι
          (restrictSection U.ι (powerSection s n)) := by
  let a := coefficient e (restrictSection U.ι s)
  obtain ⟨N, hN⟩ := affine_function_denom a f
  refine ⟨N, fun n hn => ?_⟩
  obtain ⟨g, hg⟩ := hN n hn
  let eₙ := localPowerFrame U e n
  let c := endValue (powerRestrictionUnit U n).hom
  let φ := (U.toScheme.basicOpen a).ι
  refine ⟨scalarEnd (c * g) ≫ eₙ.inv, ?_⟩
  apply coefficient_injective (restrictFrame φ eₙ)
  calc
    _ = φ.appTop (c * g) := (coefficient_restrict φ eₙ _).trans
      (congrArg φ.appTop (coefficient_scalarEnd eₙ (c * g)))
    _ = φ.appTop c * φ.appTop g := map_mul φ.appTop.hom c g
    _ = φ.appTop c * (f * φ.appTop a ^ n) := congrArg (φ.appTop c * ·) hg
    _ = f * φ.appTop (c * a ^ n) := by
      simp only [map_mul, map_pow]
      ring
    _ = f * φ.appTop (coefficient eₙ (restrictSection U.ι (powerSection s n))) :=
      congrArg (fun z => f * φ.appTop z) (local_powerSection_coefficient U e s n).symm
    _ = endValue (scalarEnd f) * coefficient (restrictFrame φ eₙ)
        (restrictSection φ (restrictSection U.ι (powerSection s n))) :=
      congrArg₂ (· * ·) (endValue_scalarEnd f).symm (coefficient_restrict φ eₙ _).symm
    _ = _ := (coefficient_precompose _ _ _).symm

end

section
open CategoryTheory AlgebraicGeometry TopologicalSpace TopologicalSpace.Opens
open scoped AlgebraicGeometry
variable {X : Scheme}

theorem LineBundle.glue_dense_subopens [IsIntegral X] (L : LineBundle X)
    (D : X.Opens) {ι : Type*} [Nonempty ι] (U W : ι → X.Opens)
    (hcover : (⊤ : X.Opens) ≤ iSup U)
    (hWU : ∀ i, W i ≤ U i) (hWD : ∀ i, W i ≤ D)
    (hW : ∀ i, (W i : Set X).Nonempty)
    (sf : ∀ i, Γ(L.sheaf, U i)) (target : Γ(L.sheaf, D))
    (heq : ∀ i, L.sheaf.presheaf.map (homOfLE (hWU i)).op (sf i) =
      L.sheaf.presheaf.map (homOfLE (hWD i)).op target) :
    ∃! g : Γ(L.sheaf, ⊤),
      (∀ i, L.sheaf.presheaf.map (homOfLE le_top).op g = sf i) ∧
        L.sheaf.presheaf.map (homOfLE le_top).op g = target := by
  let F : TopCat.Sheaf AddCommGrpCat X := ⟨L.sheaf.presheaf, L.sheaf.isSheaf⟩
  have hc : TopCat.Presheaf.IsCompatible L.sheaf.presheaf U sf := by
    intro i j
    have : Nonempty (W i ⊓ W j : X.Opens) := by
      obtain ⟨x, hi, hj⟩ := nonempty_preirreducible_inter (W i).isOpen (W j).isOpen
        (hW i) (hW j)
      exact ⟨⟨x, hi, hj⟩⟩
    apply L.restriction_injective (homOfLE
      (show W i ⊓ W j ≤ U i ⊓ U j from fun _ hx => ⟨hWU i hx.1, hWU j hx.2⟩))
    have hi := congrArg (L.sheaf.presheaf.map (infLELeft (W i) (W j)).op) (heq i)
    have hj := congrArg (L.sheaf.presheaf.map (infLERight (W i) (W j)).op) (heq j)
    simp only [← ConcreteCategory.comp_apply, ← Functor.map_comp] at hi hj ⊢
    exact hi.trans hj.symm
  obtain ⟨g, hg, hguniq⟩ := F.existsUnique_gluing' U ⊤
    (fun _ => homOfLE le_top) hcover sf hc
  have hD : L.sheaf.presheaf.map (homOfLE (show D ≤ ⊤ from le_top)).op g = target := by
    obtain ⟨i⟩ := ‹Nonempty ι›
    have : Nonempty (W i) := by obtain ⟨x, hx⟩ := hW i; exact ⟨⟨x, hx⟩⟩
    apply L.restriction_injective (homOfLE (hWD i))
    have hi : L.sheaf.presheaf.map (homOfLE (show U i ≤ ⊤ from le_top)).op g = sf i := hg i
    have hgi := congrArg (L.sheaf.presheaf.map (homOfLE (hWU i)).op) hi
    simp only [← ConcreteCategory.comp_apply, ← Functor.map_comp] at hgi ⊢
    exact hgi.trans (heq i)
  exact ⟨g, ⟨hg, hD⟩, fun g' h' => hguniq g' h'.1⟩

end

open CategoryTheory AlgebraicGeometry TopologicalSpace TopologicalSpace.Opens
open scoped AlgebraicGeometry
open PiExponentSeshadri.Frames
variable {X : Scheme}

theorem LineBundle.finite_cover_power_extension [IsIntegral X] (L : LineBundle X)
    {ι : Type*} [Fintype ι] [Nonempty ι] (U : ι → X.Opens)
    (hcover : (⊤ : X.Opens) ≤ iSup U)
    (haff : ∀ i, IsAffine (U i).toScheme)
    (hU : ∀ i, (U i : Set X).Nonempty)
    (e : ∀ i, L.sheaf.restrict (U i).ι ≅ structureSheaf (U i).toScheme)
    (s : GlobalSections X L.sheaf) (hD : (sectionOpen X s : Set X).Nonempty)
    (f : Γ(X, sectionOpen X s)) :
    ∃ N : ℕ, ∀ n ≥ N, ∃ t : GlobalSections X (modulePow X L.sheaf n),
      t.app (sectionOpen X s) (1 : Γ(X, sectionOpen X s)) =
        f • (powerSection s n).app (sectionOpen X s) (1 : Γ(X, sectionOpen X s)) := by
  classical
  let D := sectionOpen X s
  let V (i : ι) := (U i).toScheme.basicOpen (coefficient (e i) (restrictSection (U i).ι s))
  let W (i : ι) := (U i).ι ''ᵁ V i
  have hV (i : ι) : V i = (U i).ι ⁻¹ᵁ D :=
    (preimage_isoOpen s (U i).ι (e i)).symm
  have hW_eq (i : ι) : W i = U i ⊓ D := by
    simp only [W, hV, Scheme.Hom.image_preimage_eq_opensRange_inf, Scheme.Opens.opensRange_ι]
  have hWU (i : ι) : W i ≤ U i := (U i).ι_image_le (V i)
  have hWD (i : ι) : W i ≤ D := (hW_eq i).le.trans inf_le_right
  have hW (i : ι) : (W i : Set X).Nonempty := by
    rw [hW_eq]
    exact nonempty_preirreducible_inter (U i).isOpen D.isOpen (hU i) hD
  let fi (i : ι) : Γ((V i).toScheme, ⊤) :=
    (V i).topIso.inv (((U i).ι.appIso (V i)).hom (X.presheaf.map (homOfLE (hWD i)).op f))
  have hf (i : ι) : ∃ N : ℕ, ∀ n ≥ N,
      ∃ t : structureSheaf (U i).toScheme ⟶ (modulePow X L.sheaf n).restrict (U i).ι,
        restrictSection (V i).ι t = scalarEnd (fi i) ≫
          restrictSection (V i).ι (restrictSection (U i).ι (powerSection s n)) := by
    let := haff i
    exact local_affine_power_extension (U i) (e i) s (fi i)
  choose N hN using hf
  refine ⟨Finset.univ.sup N, fun n hn => ?_⟩
  have hn' (i : ι) : N i ≤ n := (Finset.le_sup (f := N) (Finset.mem_univ i)).trans hn
  choose t ht using fun i => hN i n (hn' i)
  let M := modulePow X L.sheaf n
  let target : Γ((L.pow n).sheaf, D) := f • (powerSection s n).app D (1 : Γ(X, D))
  have heq (i : ι) : M.presheaf.map (homOfLE (hWU i)).op (openSectionEquiv M (U i) (t i)) =
      M.presheaf.map (homOfLE (hWD i)).op target := by
    have hi := image_section_extension M (U i) (restrictSection (U i).ι (powerSection s n))
      (t i) (V i) (fi i) (ht i)
    have hfi : ((U i).ι.appIso (V i)).inv ((V i).topIso.hom (fi i)) =
        X.presheaf.map (homOfLE (hWD i)).op f := by
      dsimp only [fi]
      rw [Iso.inv_hom_id_apply, Iso.hom_inv_id_apply]
    rw [hfi] at hi
    have hp : openSectionEquiv M (U i) (restrictSection (U i).ι (powerSection s n)) =
        (powerSection s n).app (U i) (1 : Γ(X, U i)) := openSectionEquiv_restrict _ _
    have hs : M.presheaf.map (homOfLE (hWU i)).op
        (openSectionEquiv M (U i) (restrictSection (U i).ι (powerSection s n))) =
        (powerSection s n).app (W i) (1 : Γ(X, W i)) :=
      (congrArg (M.presheaf.map (homOfLE (hWU i)).op) hp).trans
        (section_value_natural (powerSection s n) (homOfLE (hWU i)))
    have hr : M.presheaf.map (homOfLE (hWD i)).op target =
        X.presheaf.map (homOfLE (hWD i)).op f •
          (powerSection s n).app (W i) (1 : Γ(X, W i)) :=
      (M.map_smul (homOfLE (hWD i)) f _).trans
        (congrArg (X.presheaf.map (homOfLE (hWD i)).op f • ·)
          (section_value_natural (powerSection s n) (homOfLE (hWD i))))
    exact (hi.trans (congrArg (X.presheaf.map (homOfLE (hWD i)).op f • ·) hs)).trans hr.symm
  obtain ⟨g, hg, -⟩ := (L.pow n).glue_dense_subopens D U W hcover hWU hWD hW
    (fun i => openSectionEquiv M (U i) (t i)) target heq
  refine ⟨(moduleSectionEquiv M).symm g, ?_⟩
  have H := section_value_natural ((moduleSectionEquiv M).symm g)
    (homOfLE (show D ≤ ⊤ from le_top))
  have Htop : ((moduleSectionEquiv M).symm g).app ⊤ (1 : Γ(X, ⊤)) = g :=
    (moduleSectionEquiv M).apply_symm_apply g
  rw [Htop] at H
  exact H.symm.trans hg.2

end Geometry

namespace InvertibleLocal
open CategoryTheory AlgebraicGeometry
open PiExponentSeshadri.Geometry
variable {X Y : Scheme}

def frameOfLE (M : Y.Modules) {U V : Y.Opens} (h : V ≤ U)
    (e : M.restrict U.ι ≅ structureSheaf U.toScheme) :
    M.restrict V.ι ≅ structureSheaf V.toScheme := by
  let e' := (Scheme.Modules.restrictFunctorComp (Y.homOfLE h) U.ι).app M ≪≫
    (Scheme.Modules.restrictFunctor (Y.homOfLE h)).mapIso e ≪≫
    Scheme.Modules.restrictUnitIso (Y.homOfLE h)
  simp only [Y.homOfLE_ι h] at e'
  exact e'

lemma affine_frame (J : LineBundle Y) (y : Y) :
    ∃ U : Y.affineOpens, y ∈ U.1 ∧
      Nonempty (J.sheaf.restrict U.1.ι ≅ structureSheaf U.1.toScheme) := by
  obtain ⟨V, hyV, ⟨e⟩⟩ := J.locallyRankOne y
  obtain ⟨U, hU, hyU, hUV⟩ := exists_isAffineOpen_mem_and_subset hyV
  exact ⟨⟨U, hU⟩, hyU, ⟨frameOfLE J.sheaf hUV e⟩⟩

end InvertibleLocal

namespace Geometry
open CategoryTheory AlgebraicGeometry TopologicalSpace TopologicalSpace.Opens
open scoped AlgebraicGeometry
open PiExponentSeshadri.Frames
variable {X : Scheme}

theorem LineBundle.power_extension [IsIntegral X] [CompactSpace X] (L : LineBundle X)
    (s : GlobalSections X L.sheaf) (hD : (sectionOpen X s : Set X).Nonempty)
    (f : Γ(X, sectionOpen X s)) :
    ∃ N : ℕ, ∀ n ≥ N, ∃ t : GlobalSections X (modulePow X L.sheaf n),
      t.app (sectionOpen X s) (1 : Γ(X, sectionOpen X s)) =
        f • (powerSection s n).app (sectionOpen X s) (1 : Γ(X, sectionOpen X s)) := by
  classical
  choose U hUx he using InvertibleLocal.affine_frame L
  obtain ⟨I, hI⟩ := isCompact_univ.elim_finite_subcover
    (fun x => (U x).1 : X → Set X) (fun x => (U x).1.isOpen)
    (by intro x _; exact Set.mem_iUnion.mpr ⟨x, hUx x⟩)
  have hic (x : X) : ∃ i ∈ I, x ∈ (U i).1 := by
    obtain ⟨i, hi⟩ := Set.mem_iUnion.mp (hI (show x ∈ Set.univ from trivial))
    obtain ⟨hi, hx⟩ := Set.mem_iUnion.mp hi
    exact ⟨i, hi, hx⟩
  have : Nonempty I := by
    obtain ⟨x, -⟩ := hD
    obtain ⟨i, hi, -⟩ := hic x
    exact ⟨⟨i, hi⟩⟩
  exact L.finite_cover_power_extension (fun i : I => (U i.val).1)
    (by
      intro x _
      obtain ⟨i, hi, hx⟩ := hic x
      exact TopologicalSpace.Opens.mem_iSup.mpr ⟨⟨i, hi⟩, hx⟩)
    (fun i => (U i.val).2) (fun i => ⟨i.val, hUx i.val⟩)
    (fun i => Classical.choice (he i.val)) s hD f

end Geometry

end PiExponentSeshadri

end

end OAI
end Source0384

-- Source: OAI/NumberTheory/PiExponent/Geometry/ProjectiveEmbeddingCharts.lean
section Source0385
/-
Modification notice for the LogTwo project.
Derived from openai/math (Apache-2.0), revision adc7f1241b42e322a6451854ab7e4b4c146bf78a.
Original source: lean/OAI/NumberTheory/PiExponent/Geometry/ProjectiveEmbeddingCharts.lean
Changes: Convert module/import declarations to the Lean 4.34 public module format.
See ../THIRD_PARTY_NOTICES.txt for provenance and the recorded changes.
-/

namespace OAI

noncomputable section

namespace PiExponentSeshadri

universe u

namespace Projective
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace
open scoped AlgebraicGeometry
open MvPolynomial HomogeneousLocalization
variable {K σ R : Type u} [CommRing K] [CommRing R]
attribute [local instance] MvPolynomial.gradedAlgebra

lemma normalized_evalAway_surjective (k : K →+* R) (a : σ → R)
    (i : σ) (hi : a i = 1) (h : Function.Surjective (eval₂Hom k a)) :
    Function.Surjective (evalAway (𝒜 := homogeneousSubmodule σ K) (eval₂Hom k a)
      (X i) (by simpa only [eval₂Hom_X', hi] using (isUnit_one : IsUnit (1 : R)))) := by
  let F := evalAway (𝒜 := homogeneousSubmodule σ K) (eval₂Hom k a)
    (X i) (by simpa only [eval₂Hom_X', hi] using (isUnit_one : IsUnit (1 : R)))
  have hC (r : K) : C r ∈ homogeneousSubmodule σ K (0 • 1) := by simp
  have hX (j : σ) : X j ∈ homogeneousSubmodule σ K (1 • 1) := by
    simpa using isHomogeneous_X K j
  let c : K →+* Away (homogeneousSubmodule σ K) (X i) :=
    (HomogeneousLocalization.fromZeroRingHom _ _).comp
      { toFun := fun r => ⟨C r, isHomogeneous_C _ _⟩
        map_one' := Subtype.ext C_1
        map_mul' := fun _ _ => Subtype.ext C_mul
        map_zero' := Subtype.ext C_0
        map_add' := fun _ _ => Subtype.ext C_add }
  let b (j : σ) := Away.mk _ (isHomogeneous_X K i) 1 (X j) (hX j)
  have hc (r : K) : F (c r) = k r := by
    change F (Away.mk _ (isHomogeneous_X K i) 0 (C r) (hC r)) = k r
    have H := evalAway_mk_clear (eval₂Hom k a) (isHomogeneous_X K i)
      (show IsUnit ((eval₂Hom k a) (X i)) by simpa only [eval₂Hom_X', hi] using
        (isUnit_one : IsUnit (1 : R))) 0 (C r) (hC r)
    simpa only [F, eval₂Hom_C, eval₂Hom_X', pow_zero, mul_one] using H
  have hb (j : σ) : F (b j) = a j := by
    have H := evalAway_mk_clear (eval₂Hom k a) (isHomogeneous_X K i)
      (show IsUnit ((eval₂Hom k a) (X i)) by simpa only [eval₂Hom_X', hi] using
        (isUnit_one : IsUnit (1 : R))) 1 (X j) (hX j)
    simpa only [F, b, eval₂Hom_X', hi, one_pow, mul_one] using H
  have H : F.comp (eval₂Hom c b) = eval₂Hom k a := by
    apply MvPolynomial.ringHom_ext
    · intro r
      simpa only [RingHom.comp_apply, eval₂Hom_C] using hc r
    · intro j
      simpa only [RingHom.comp_apply, eval₂Hom_X'] using hb j
  intro r
  obtain ⟨p, hp⟩ := h r
  exact ⟨eval₂Hom c b p, (RingHom.congr_fun H p).trans hp⟩

lemma normalized_coordinates_closed {X : Scheme.{u}} [IsAffine X]
    (k : K →+* Γ(X, ⊤)) (a : σ → Γ(X, ⊤)) (i : σ) (hi : a i = 1)
    (h : Function.Surjective (eval₂Hom k a)) :
    IsClosedImmersion (X.toSpecΓ ≫ Spec.map (CommRingCat.ofHom
      (evalAway (𝒜 := homogeneousSubmodule σ K) (eval₂Hom k a) (MvPolynomial.X i)
        (by simpa only [eval₂Hom_X', hi] using (isUnit_one : IsUnit (1 : Γ(X, ⊤))))))) := by
  have := IsClosedImmersion.spec_of_surjective
    (CommRingCat.ofHom (evalAway (𝒜 := homogeneousSubmodule σ K) (eval₂Hom k a)
      (MvPolynomial.X i) (by simpa only [eval₂Hom_X', hi] using
        (isUnit_one : IsUnit (1 : Γ(X, ⊤))))))
    (normalized_evalAway_surjective k a i hi h)
  infer_instance

end Projective

namespace Geometry
open CategoryTheory AlgebraicGeometry TopologicalSpace
open scoped AlgebraicGeometry
variable {X Y : Scheme.{u}} {ι : Type u}

theorem closedImmersion_of_source_charts (f : X ⟶ Y) [UniversallyClosed f]
    (U : ι → X.Opens) (V : ι → Y.Opens)
    (hU : (⨆ i, U i) = ⊤) (g : ∀ i, (U i).toScheme ⟶ (V i).toScheme)
    (hg : ∀ i, IsClosedImmersion (g i))
    (hcomm : ∀ i, (U i).ι ≫ f = g i ≫ (V i).ι)
    (hpre : ∀ i, f ⁻¹ᵁ V i = U i) : IsClosedImmersion f := by
  have hinj : Function.Injective f := by
    intro x y hxy
    have hx : x ∈ ⨆ i, U i := by rw [hU]; trivial
    obtain ⟨i, hi⟩ := Opens.mem_iSup.mp hx
    have hy : y ∈ U i := by
      rw [← hpre i]
      change f y ∈ V i
      rw [← hxy]
      change x ∈ f ⁻¹ᵁ V i
      rw [hpre]
      exact hi
    have he (z : (U i).toScheme) : (g i z).val = f z.val :=
      (congrArg (fun a : (U i).toScheme ⟶ Y => a z) (hcomm i)).symm
    have hz : g i ⟨x, hi⟩ = g i ⟨y, hy⟩ := by
      apply Subtype.ext
      exact (he ⟨x, hi⟩).trans (hxy.trans (he ⟨y, hy⟩).symm)
    have := (g i).isClosedEmbedding.injective hz
    exact congrArg Subtype.val this
  have hstalk : SurjectiveOnStalks f := by
    apply IsZariskiLocalAtSource.of_openCover (P := @SurjectiveOnStalks)
      (X.openCoverOfIsOpenCover U hU)
    intro i
    change ι at i
    change SurjectiveOnStalks ((U i).ι ≫ f)
    rw [hcomm]
    have := hg i
    infer_instance
  exact ⟨Topology.IsClosedEmbedding.of_continuous_injective_isClosedMap f.continuous hinj f.isClosedMap⟩

end Geometry

namespace Projective

section
open AlgebraicGeometry CategoryTheory HomogeneousLocalization MvPolynomial
open scoped AlgebraicGeometry
variable {K σ : Type u} [CommRing K]
attribute [local instance] MvPolynomial.gradedAlgebra

def projectiveConstants : K →+* homogeneousSubmodule σ K 0 where
  toFun r := ⟨C r, isHomogeneous_C _ _⟩
  map_one' := Subtype.ext C_1
  map_mul' _ _ := Subtype.ext C_mul
  map_zero' := Subtype.ext C_0
  map_add' _ _ := Subtype.ext C_add

def projectiveBase : Proj (homogeneousSubmodule σ K) ⟶ Spec (CommRingCat.of K) :=
  Proj.toSpecZero _ ≫ Spec.map (CommRingCat.ofHom (projectiveConstants (σ := σ)))

lemma evalAway_constants_comp {R : Type u} [CommRing R] (k : K →+* R) (a : σ → R)
    (i : σ) (hi : a i = 1) :
    (evalAway (𝒜 := homogeneousSubmodule σ K) (eval₂Hom k a) (X i)
      (by simpa only [eval₂Hom_X', hi] using (isUnit_one : IsUnit (1 : R)))).comp
      ((fromZeroRingHom (homogeneousSubmodule σ K) (.powers (X i))).comp
        projectiveConstants) = k := by
  apply RingHom.ext
  intro c
  change IsLocalization.Away.lift (X i)
    (by simpa only [eval₂Hom_X', hi] using (isUnit_one : IsUnit (1 : R)))
    (HomogeneousLocalization.fromZeroRingHom (homogeneousSubmodule σ K)
      (.powers (X i)) (projectiveConstants c)).val = k c
  change IsLocalization.Away.lift (X i)
    (by simpa only [eval₂Hom_X', hi] using (isUnit_one : IsUnit (1 : R)))
    (algebraMap (MvPolynomial σ K) (Localization.Away (X i)) (C c)) = k c
  rw [IsLocalization.Away.lift_eq, eval₂Hom_C]

@[reassoc]
theorem coordinatesMap_over {X : Scheme.{u}} (k : K →+* Γ(X, ⊤))
    (a : σ → Γ(X, ⊤)) (i : σ) (hi : a i = 1) :
    coordinatesMap X k a i hi ≫ projectiveBase =
      X.toSpecΓ ≫ Spec.map (CommRingCat.ofHom k) := by
  simp only [coordinatesMap, fromUnitCoordinate, projectiveBase, Category.assoc,
    Proj.awayι_toSpecZero_assoc, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
  congr 2
  exact congrArg CommRingCat.ofHom (evalAway_constants_comp k a i hi)

@[reassoc]
theorem sectionsMorphism_over {X : Scheme.{u}} {M : X.Modules}
    (k : K →+* Γ(X, ⊤)) (s : σ → (PiExponentSeshadri.Frames.O X ⟶ M))
    (hcover : (⨆ i, SectionOpens.isoOpen (s i)) = ⊤) :
    sectionsMorphism k s hcover ≫ projectiveBase =
      X.toSpecΓ ≫ Spec.map (CommRingCat.ofHom k) := by
  apply (X.openCoverOfIsOpenCover (fun i => SectionOpens.isoOpen (s i)) hcover).hom_ext
  intro i
  change σ at i
  change (SectionOpens.isoOpen (s i)).ι ≫ _ = _
  rw [← Category.assoc, sectionsMorphism_local, coordinatesMap_over]
  change _ = (SectionOpens.isoOpen (s i)).ι ≫ X.toSpecΓ ≫ _
  rw [← Category.assoc, Scheme.toSpecΓ_naturality, Category.assoc, ← Spec.map_comp]
  rfl

end

open AlgebraicGeometry CategoryTheory TopologicalSpace MvPolynomial
open scoped AlgebraicGeometry
open PiExponentSeshadri.Frames
variable {K σ : Type u} [CommRing K] {X : Scheme.{u}}
attribute [local instance] MvPolynomial.gradedAlgebra

instance projectiveBase_separated : IsSeparated (projectiveBase (K := K) (σ := σ)) := by
  unfold projectiveBase
  infer_instance

instance sectionsMorphism_proper {M : X.Modules} (k : K →+* Γ(X, ⊤))
    (s : σ → (O X ⟶ M)) (hcover : (⨆ i, SectionOpens.isoOpen (s i)) = ⊤)
    [IsProper (X.toSpecΓ ≫ Spec.map (CommRingCat.ofHom k))] :
    IsProper (sectionsMorphism k s hcover) := by
  have : IsProper (sectionsMorphism k s hcover ≫ projectiveBase) := by
    rw [sectionsMorphism_over]
    infer_instance
  exact IsProper.of_comp _ projectiveBase

lemma toSpec_scalarMap (p : X ⟶ Spec (CommRingCat.of K)) :
    X.toSpecΓ ≫ Spec.map (CommRingCat.ofHom
      (p.appTop.hom.comp (Scheme.ΓSpecIso (CommRingCat.of K)).inv.hom)) = p := by
  change X.toSpecΓ ≫ Spec.map ((Scheme.ΓSpecIso (CommRingCat.of K)).inv ≫ p.appTop) = p
  rw [Spec.map_comp, ← Category.assoc, ← Scheme.toSpecΓ_naturality]
  simp

end Projective

namespace Geometry
open AlgebraicGeometry CategoryTheory MvPolynomial
open scoped AlgebraicGeometry

lemma finiteType_coordinates {K R : Type u} [CommRing K] [CommRing R]
    (k : K →+* R) (hk : k.FiniteType) :
    ∃ n : ℕ, ∃ a : Fin n → R, Function.Surjective (eval₂Hom k a) := by
  let := k.toAlgebra
  have : Algebra.FiniteType K R := hk
  obtain ⟨n, f, hf⟩ := Algebra.FiniteType.iff_quotient_mvPolynomial''.mp
    (inferInstance : Algebra.FiniteType K R)
  refine ⟨n, fun i => f (X i), ?_⟩
  have heq : eval₂Hom k (fun i => f (X i)) = f.toRingHom := by
    apply MvPolynomial.ringHom_ext
    · intro c
      exact (eval₂Hom_C _ _ _).trans (f.commutes c).symm
    · intro i
      exact eval₂Hom_X' _ _ _
  rw [heq]
  exact hf

theorem affine_coordinate_generators {K : Type u} [CommRing K] {X : Scheme.{u}}
    [IsAffine X] (p : X ⟶ Spec (CommRingCat.of K)) [LocallyOfFiniteType p] :
    ∃ n : ℕ, ∃ a : Fin n → Γ(X, ⊤), Function.Surjective
      (eval₂Hom (p.appTop.hom.comp (Scheme.ΓSpecIso (CommRingCat.of K)).inv.hom) a) := by
  have hp : p.appTop.hom.FiniteType :=
    HasRingHomProperty.appTop (P := @LocallyOfFiniteType) _ inferInstance
  have he : (Scheme.ΓSpecIso (CommRingCat.of K)).inv.hom.FiniteType :=
    RingHom.FiniteType.of_surjective _ (ConcreteCategory.bijective_of_isIso
      (Scheme.ΓSpecIso (CommRingCat.of K)).inv).surjective
  exact finiteType_coordinates _ (hp.comp he)

end Geometry

end PiExponentSeshadri

end

end OAI
end Source0385

-- Source: OAI/NumberTheory/PiExponent/Geometry/ProjectiveFramedSections.lean
section Source0386
/-
Modification notice for the LogTwo project.
Derived from openai/math (Apache-2.0), revision adc7f1241b42e322a6451854ab7e4b4c146bf78a.
Original source: lean/OAI/NumberTheory/PiExponent/Geometry/ProjectiveFramedSections.lean
Changes: Convert module/import declarations to the Lean 4.34 public module format.
See ../THIRD_PARTY_NOTICES.txt for provenance and the recorded changes.
-/

namespace OAI

noncomputable section

universe u

namespace PiExponentSeshadri.Projective

section
open AlgebraicGeometry CategoryTheory TopologicalSpace MvPolynomial
open scoped AlgebraicGeometry
open PiExponentSeshadri.Frames
variable {K σ ι : Type u} [CommRing K] {X : Scheme.{u}} {M : X.Modules}
attribute [local instance] MvPolynomial.gradedAlgebra
variable (k : K →+* Γ(X, ⊤)) (s : σ → (O X ⟶ M))
  (U : ι → X.Opens) (hc : (⨆ i, U i) = ⊤)
  (e : ∀ i, M.restrict (U i).ι ≅ O (U i).toScheme) (a : ι → σ)
  (hnorm : ∀ i, coefficient (e i) (restrictSection (U i).ι (s (a i))) = 1)

def framedSectionsMorphism : X ⟶ Proj (homogeneousSubmodule σ K) :=
  (atlasOfFramedSections k s (X.openCoverOfIsOpenCover U hc) e a hnorm).morphism

@[reassoc]
lemma framedSectionsMorphism_local (i : ι) :
    (U i).ι ≫ framedSectionsMorphism k s U hc e a hnorm =
      coordinatesMap (U i).toScheme ((U i).ι.appTop.hom.comp k)
        (fun j => coefficient (e i) (restrictSection (U i).ι (s j))) (a i) (hnorm i) :=
  CoordinateAtlas.cover_morphism
    (atlasOfFramedSections k s (X.openCoverOfIsOpenCover U hc) e a hnorm) i

theorem framedSectionsMorphism_preimage (j : σ) :
    framedSectionsMorphism k s U hc e a hnorm ⁻¹ᵁ
      Proj.basicOpen (homogeneousSubmodule σ K) (MvPolynomial.X j) = SectionOpens.isoOpen (s j) := by
  ext x
  have hx : x ∈ ⨆ i, U i := by rw [hc]; trivial
  obtain ⟨i, hi⟩ := Opens.mem_iSup.mp hx
  have H : (U i).ι ⁻¹ᵁ (framedSectionsMorphism k s U hc e a hnorm ⁻¹ᵁ
      Proj.basicOpen (homogeneousSubmodule σ K) (MvPolynomial.X j)) =
      (U i).ι ⁻¹ᵁ SectionOpens.isoOpen (s j) := by
    rw [← Scheme.Hom.comp_preimage, framedSectionsMorphism_local,
      coordinatesMap_preimage, preimage_isoOpen (s j) (U i).ι (e i)]
  exact Set.ext_iff.mp (congrArg SetLike.coe H) (⟨x, hi⟩ : (U i).toScheme)

@[reassoc]
theorem framedSectionsMorphism_over :
    framedSectionsMorphism k s U hc e a hnorm ≫ projectiveBase =
      X.toSpecΓ ≫ Spec.map (CommRingCat.ofHom k) := by
  apply (X.openCoverOfIsOpenCover U hc).hom_ext
  intro i
  change ι at i
  change (U i).ι ≫ _ = (U i).ι ≫ _
  rw [← Category.assoc, framedSectionsMorphism_local, coordinatesMap_over,
    ← Category.assoc, Scheme.toSpecΓ_naturality, Category.assoc, ← Spec.map_comp]
  rfl

instance framedSectionsMorphism_proper
    [IsProper (X.toSpecΓ ≫ Spec.map (CommRingCat.ofHom k))] :
    IsProper (framedSectionsMorphism k s U hc e a hnorm) := by
  have : IsProper (framedSectionsMorphism k s U hc e a hnorm ≫ projectiveBase) := by
    rw [framedSectionsMorphism_over]
    infer_instance
  exact IsProper.of_comp _ projectiveBase

theorem framedSectionsMorphism_closed
    [IsProper (X.toSpecΓ ≫ Spec.map (CommRingCat.ofHom k))]
    (hU : ∀ i, SectionOpens.isoOpen (s (a i)) = U i)
    (haff : ∀ i, IsAffine (U i).toScheme)
    (hgen : ∀ i, Function.Surjective
      (eval₂Hom ((U i).ι.appTop.hom.comp k)
        (fun j => coefficient (e i) (restrictSection (U i).ι (s j))))) :
    IsClosedImmersion (framedSectionsMorphism k s U hc e a hnorm) := by
  let V (i : ι) := Proj.basicOpen (homogeneousSubmodule σ K) (MvPolynomial.X (a i))
  let k' (i : ι) := (U i).ι.appTop.hom.comp k
  let b (i : ι) (j : σ) := coefficient (e i) (restrictSection (U i).ι (s j))
  let g (i : ι) := (U i).toScheme.toSpecΓ ≫ Spec.map (CommRingCat.ofHom
    (evalAway (𝒜 := homogeneousSubmodule σ K) (eval₂Hom (k' i) (b i)) (MvPolynomial.X (a i))
      (by simpa only [eval₂Hom_X', b, hnorm] using (isUnit_one : IsUnit (1 : Γ((U i).toScheme, ⊤))))))
  let ep (i : ι) := Proj.basicOpenIsoSpec (homogeneousSubmodule σ K) (MvPolynomial.X (a i))
    (isHomogeneous_X K (a i)) (by decide : 0 < (1 : ℕ))
  apply PiExponentSeshadri.Geometry.closedImmersion_of_source_charts
    (framedSectionsMorphism k s U hc e a hnorm) U V hc (fun i => g i ≫ (ep i).inv)
  · intro i
    let : IsAffine (U i).toScheme := haff i
    have : IsClosedImmersion (g i) := normalized_coordinates_closed (k' i) (b i) (a i) (hnorm i) (hgen i)
    infer_instance
  · intro i
    rw [framedSectionsMorphism_local]
    rfl
  · intro i
    exact (framedSectionsMorphism_preimage k s U hc e a hnorm (a i)).trans (hU i)

end

section
open AlgebraicGeometry CategoryTheory TopologicalSpace MvPolynomial
open scoped AlgebraicGeometry
open PiExponentSeshadri.Frames
variable {K σ ι κ : Type u} [CommRing K] {X : Scheme.{u}} {M : X.Modules}
attribute [local instance] MvPolynomial.gradedAlgebra

theorem framedSectionsMorphism_eq (k : K →+* Γ(X, ⊤)) (s : σ → (O X ⟶ M))
    (U : ι → X.Opens) (hc : (⨆ i, U i) = ⊤)
    (e : ∀ i, M.restrict (U i).ι ≅ O (U i).toScheme) (a : ι → σ)
    (hnorm : ∀ i, coefficient (e i) (restrictSection (U i).ι (s (a i))) = 1)
    (V : κ → X.Opens) (hd : (⨆ i, V i) = ⊤)
    (d : ∀ i, M.restrict (V i).ι ≅ O (V i).toScheme) (b : κ → σ)
    (hnorm' : ∀ i, coefficient (d i) (restrictSection (V i).ι (s (b i))) = 1) :
    framedSectionsMorphism k s U hc e a hnorm =
      framedSectionsMorphism k s V hd d b hnorm' := by
  let W : ι ⊕ κ → X.Opens := Sum.elim U V
  have hw : (⨆ i, W i) = ⊤ := by
    apply top_unique
    rw [← hc]
    apply iSup_le
    intro i
    exact le_iSup W (Sum.inl i)
  let E : ∀ i, M.restrict (W i).ι ≅ O (W i).toScheme :=
    fun i => match i with | Sum.inl j => e j | Sum.inr j => d j
  let A : ι ⊕ κ → σ := Sum.elim a b
  have hN : ∀ i, coefficient (E i) (restrictSection (W i).ι (s (A i))) = 1 := by
    rintro (i | i)
    · exact hnorm i
    · exact hnorm' i
  let F := framedSectionsMorphism k s W hw E A hN
  have hleft : framedSectionsMorphism k s U hc e a hnorm = F := by
    apply (X.openCoverOfIsOpenCover U hc).hom_ext
    intro i
    change ι at i
    change (U i).ι ≫ _ = (U i).ι ≫ F
    rw [framedSectionsMorphism_local]
    exact (framedSectionsMorphism_local k s W hw E A hN (Sum.inl i)).symm
  have hright : framedSectionsMorphism k s V hd d b hnorm' = F := by
    apply (X.openCoverOfIsOpenCover V hd).hom_ext
    intro i
    change κ at i
    change (V i).ι ≫ _ = (V i).ι ≫ F
    rw [framedSectionsMorphism_local]
    exact (framedSectionsMorphism_local k s W hw E A hN (Sum.inr i)).symm
  exact hleft.trans hright.symm

lemma framedSectionsMorphism_eq_sectionsMorphism (k : K →+* Γ(X, ⊤))
    (s : σ → (O X ⟶ M)) (hs : (⨆ i, SectionOpens.isoOpen (s i)) = ⊤)
    (U : ι → X.Opens) (hc : (⨆ i, U i) = ⊤)
    (e : ∀ i, M.restrict (U i).ι ≅ O (U i).toScheme) (a : ι → σ)
    (hnorm : ∀ i, coefficient (e i) (restrictSection (U i).ι (s (a i))) = 1) :
    framedSectionsMorphism k s U hc e a hnorm = sectionsMorphism k s hs :=
  framedSectionsMorphism_eq k s U hc e a hnorm
    (fun i => SectionOpens.isoOpen (s i)) hs (fun i => sectionFrame (s i)) id
    (fun i => sectionFrame_normalized (s i))

end

open AlgebraicGeometry CategoryTheory TopologicalSpace MvPolynomial
open scoped AlgebraicGeometry
open PiExponentSeshadri.Frames
variable {K σ : Type u} [CommRing K] {X : Scheme.{u}} {M N : X.Modules}
attribute [local instance] MvPolynomial.gradedAlgebra

lemma coefficient_postcomp (f : M ≅ N) (φ : X.Opens)
    (e : M.restrict φ.ι ≅ O φ.toScheme) (s : O X ⟶ M) :
    coefficient ((Scheme.Modules.restrictFunctor φ.ι).mapIso f.symm ≪≫ e)
      (restrictSection φ.ι (s ≫ f.hom)) = coefficient e (restrictSection φ.ι s) := by
  simp only [restrictSection]
  let F : X.Modules ⥤ φ.toScheme.Modules := Scheme.Modules.restrictFunctor φ.ι
  let a : O φ.toScheme ⟶ F.obj (O X) := (Scheme.Modules.restrictUnitIso φ.ι).inv
  let e' : F.obj M ≅ O φ.toScheme := e
  change endValue ((a ≫ F.map (s ≫ f.hom)) ≫ F.map f.inv ≫ e'.hom) =
    endValue ((a ≫ F.map s) ≫ e'.hom)
  have hs : (s ≫ f.hom) ≫ f.inv = s := by
    simp only [Category.assoc, Iso.hom_inv_id, Category.comp_id]
  have hm : F.map (s ≫ f.hom) ≫ F.map f.inv = F.map s :=
    (F.map_comp _ _).symm.trans (congrArg F.map hs)
  apply congrArg endValue
  calc
    _ = a ≫ ((F.map (s ≫ f.hom) ≫ F.map f.inv) ≫ e'.hom) := by
      simp only [Category.assoc]
    _ = a ≫ (F.map s ≫ e'.hom) := congrArg (fun t => a ≫ t ≫ e'.hom) hm
    _ = _ := (Category.assoc _ _ _).symm

theorem sectionsMorphism_transport (k : K →+* Γ(X, ⊤))
    (s : σ → (O X ⟶ M)) (hs : (⨆ i, SectionOpens.isoOpen (s i)) = ⊤)
    (f : M ≅ N) (ht : (⨆ i, SectionOpens.isoOpen (s i ≫ f.hom)) = ⊤) :
    sectionsMorphism k (fun i => s i ≫ f.hom) ht = sectionsMorphism k s hs := by
  let U (i : σ) := SectionOpens.isoOpen (s i)
  let e (i : σ) := (Scheme.Modules.restrictFunctor (U i).ι).mapIso f.symm ≪≫ sectionFrame (s i)
  have he (i j : σ) : coefficient (e i) (restrictSection (U i).ι (s j ≫ f.hom)) =
      coefficient (sectionFrame (s i)) (restrictSection (U i).ι (s j)) :=
    coefficient_postcomp f (U i) (sectionFrame (s i)) (s j)
  have hn (i : σ) : coefficient (e i) (restrictSection (U i).ι (s i ≫ f.hom)) = 1 := by
    rw [he]
    exact sectionFrame_normalized (s i)
  rw [← framedSectionsMorphism_eq_sectionsMorphism k (fun i => s i ≫ f.hom) ht U hs e id hn]
  apply (X.openCoverOfIsOpenCover U hs).hom_ext
  intro i
  change σ at i
  change (U i).ι ≫ _ = (U i).ι ≫ _
  rw [framedSectionsMorphism_local, sectionsMorphism_local]
  congr 1
  funext j
  exact he i j

end PiExponentSeshadri.Projective

end

end OAI
end Source0386

-- Source: OAI/NumberTheory/PiExponent/Ampleness/AmpleProjectiveSections.lean
section Source0387
-- Modified in this edition: unused plain lemmas removed; see reduction.json.
/-
Modification notice for the LogTwo project.
Derived from openai/math (Apache-2.0), revision adc7f1241b42e322a6451854ab7e4b4c146bf78a.
Original source: lean/OAI/NumberTheory/PiExponent/Ampleness/AmpleProjectiveSections.lean
Changes: Convert module/import declarations to the Lean 4.34 public module format.
See ../THIRD_PARTY_NOTICES.txt for provenance and the recorded changes.
-/

namespace OAI

noncomputable section

namespace PiExponentSeshadri.Geometry

section
open CategoryTheory AlgebraicGeometry TopologicalSpace
open scoped AlgebraicGeometry
open PiExponentSeshadri.Frames PiExponentSeshadri.Projective
variable {X : Scheme}

lemma isIso_restricted_section {M : X.Modules} (s : O X ⟶ M) (U : X.Opens)
    (hU : SectionOpens.isoOpen s = U) : IsIso (restrictSection U.ι s) := by
  subst U
  change IsIso (sectionFrame s).inv
  exact (sectionFrame s).isIso_inv

theorem LineBundle.power_extension_ratio [IsIntegral X] [CompactSpace X] (L : LineBundle X)
    (s : GlobalSections X L.sheaf) (hD : (sectionOpen X s : Set X).Nonempty)
    (f : Γ((sectionOpen X s).toScheme, ⊤)) :
    ∃ N : ℕ, ∀ n ≥ N, ∃ t : GlobalSections X (modulePow X L.sheaf n),
      restrictSection (sectionOpen X s).ι t = scalarEnd f ≫
        restrictSection (sectionOpen X s).ι (powerSection s n) := by
  obtain ⟨N, hN⟩ := L.power_extension s hD ((sectionOpen X s).topIso.hom f)
  refine ⟨N, fun n hn => ?_⟩
  obtain ⟨t, ht⟩ := hN n hn
  refine ⟨t, ?_⟩
  apply (openSectionEquiv (modulePow X L.sheaf n) (sectionOpen X s)).injective
  erw [openSectionEquiv_restrict, openSectionEquiv_scalar, openSectionEquiv_restrict]
  exact ht

lemma coefficient_ratio {M : X.Modules} {U : X.Opens}
    (e : M.restrict U.ι ≅ O U.toScheme) (s t : O X ⟶ M)
    (f : Γ(U.toScheme, ⊤)) (hs : coefficient e (restrictSection U.ι s) = 1)
    (ht : restrictSection U.ι t = scalarEnd f ≫ restrictSection U.ι s) :
    coefficient e (restrictSection U.ι t) = f := by
  rw [ht]
  change endValue (scalarEnd f ≫ restrictSection U.ι s ≫ e.hom) = f
  rw [endValue_comp, endValue_scalarEnd]
  change f * coefficient e (restrictSection U.ι s) = f
  rw [hs, mul_one]

end

section
open CategoryTheory AlgebraicGeometry TopologicalSpace MvPolynomial
open scoped AlgebraicGeometry
open PiExponentSeshadri.Frames PiExponentSeshadri.Projective
variable {X : Scheme} {K ι : Type} [CommRing K] [Fintype ι]

end

open AlgebraicGeometry CategoryTheory TopologicalSpace
open scoped AlgebraicGeometry
open PiExponentSeshadri.Frames PiExponentSeshadri.Projective
variable {X : Scheme} {K : Type} [CommRing K]

end PiExponentSeshadri.Geometry

end

end OAI
end Source0387

-- Source: OAI/NumberTheory/PiExponent/Approximation/TensorPure.lean
section Source0388
/-
Modification notice for the LogTwo project.
Derived from openai/math (Apache-2.0), revision adc7f1241b42e322a6451854ab7e4b4c146bf78a.
Original source: lean/OAI/NumberTheory/PiExponent/Approximation/TensorPure.lean
Changes: Convert module/import declarations to the Lean 4.34 public module format.
Expose private helpers and adjust helper names where needed for module compatibility.
See ../THIRD_PARTY_NOTICES.txt for provenance and the recorded changes.
-/

namespace OAI

noncomputable section

namespace PiExponentSeshadri.TensorPure

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite
open PiExponentSeshadri.Geometry
open MonoidalCategory

variable {X Y : Scheme.{0}}

local instance sectionModule {X : Scheme.{0}}
    (P : PresheafOfModules X.ringCatSheaf.obj) (U : X.Opens) :
    Module Γ(X, U) (P.obj (op U)) := (P.obj (op U)).isModule

abbrev presheaf (M N : X.Modules) :=
  PresheafOfModulesOfCommRing.Monoidal.tensorObj (R := X.presheaf) M.val N.val

abbrev adj (X : Scheme.{0}) :=
  PresheafOfModules.sheafificationAdjunction (R := X.ringCatSheaf) (𝟙 X.ringCatSheaf.obj)

def pure (M N : X.Modules) (U : X.Opens) (m : M.val.obj (op U)) (n : N.val.obj (op U)) :
    (moduleTensor X M N).val.obj (op U) :=
  (((adj X).unit.app (presheaf M N)).app (op U)).hom (m ⊗ₜ[Γ(X,U)] n)

@[simp] lemma pure_add_left (M N : X.Modules) (U : X.Opens) (m m' : M.val.obj (op U)) (n : N.val.obj (op U)) :
    pure M N U (m+m') n = pure M N U m n + pure M N U m' n := by
  unfold pure
  rw [TensorProduct.add_tmul]
  exact map_add _ _ _

@[simp] lemma pure_add_right (M N : X.Modules) (U : X.Opens) (m : M.val.obj (op U)) (n n' : N.val.obj (op U)) :
    pure M N U m (n+n') = pure M N U m n + pure M N U m n' := by
  unfold pure
  rw [TensorProduct.tmul_add]
  exact map_add _ _ _

@[simp] lemma pure_smul_left (M N : X.Modules) (U : X.Opens) (a : Γ(X,U)) (m : M.val.obj (op U)) (n : N.val.obj (op U)) :
    pure M N U (a • m) n = a • pure M N U m n := by
  unfold pure
  rw [← TensorProduct.smul_tmul']
  exact map_smul _ _ _

@[simp] lemma pure_smul_right (M N : X.Modules) (U : X.Opens) (a : Γ(X,U)) (m : M.val.obj (op U)) (n : N.val.obj (op U)) :
    pure M N U m (a • n) = a • pure M N U m n := by
  simp only [pure]
  rw [TensorProduct.tmul_smul]
  exact map_smul _ _ _

lemma pure_restrict (M N : X.Modules) {U V : X.Opens} (i : V ⟶ U)
    (m : M.val.obj (op U)) (n : N.val.obj (op U)) :
    (moduleTensor X M N).val.map i.op (pure M N U m n) =
      pure M N V (M.val.map i.op m) (N.val.map i.op n) := by
  exact (PresheafOfModules.naturality_apply ((adj X).unit.app (presheaf M N)) i.op
    (m ⊗ₜ[Γ(X,U)] n)).symm

lemma map_pure {M N P Q : X.Modules} (f : M ⟶ P) (g : N ⟶ Q)
    (U : X.Opens) (m : M.val.obj (op U)) (n : N.val.obj (op U)) :
    (moduleTensorMap f g).app U (pure M N U m n) =
      pure P Q U (f.app U m) (g.app U n) := by
  have h := (adj X).unit.naturality
    (PresheafOfModulesOfCommRing.Monoidal.tensorHom (R := X.presheaf) f.val g.val)
  exact (congrArg (fun q => q.app (op U) (m ⊗ₜ[Γ(X,U)] n)) h).symm

lemma hom_ext {M N P : X.Modules} {f g : moduleTensor X M N ⟶ P}
    (h : ∀ U m n, f.app U (pure M N U m n) = g.app U (pure M N U m n)) : f = g := by
  apply ((adj X).homEquiv (presheaf M N) P).injective
  ext U : 1
  apply ModuleCat.MonoidalCategory.tensor_ext
  intro m n
  exact h U.unop m n

lemma sheafify_restrict_unit (f : X ⟶ Y) [IsOpenImmersion f]
    (P : PresheafOfModules Y.ringCatSheaf.obj) :
    (modulePresheafRestrict f).map ((adj Y).unit.app P) ≫
      ((moduleSheafificationRestrict f).hom.app P).val =
    (adj X).unit.app ((modulePresheafRestrict f).obj P) := by
  let a := adj Y
  let b := Scheme.Modules.restrictAdjunction f
  let c := modulePresheafRestrictAdjunction f
  let d := adj X
  apply (c.homEquiv _ _).injective
  erw [Adjunction.homEquiv_unit,Functor.map_comp]
  have hn := c.unit_naturality (a.unit.app P)
  rw [← Category.assoc,hn]
  have he := Adjunction.unit_leftAdjointUniq_hom_app (a.comp b) (c.comp d) P
  have ha := a.comp_unit_app b P
  have hd := c.comp_unit_app d P
  let G : Y.Modules ⥤ PresheafOfModules Y.ringCatSheaf.obj :=
    SheafOfModules.forget Y.ringCatSheaf ⋙
      PresheafOfModules.restrictScalars (𝟙 Y.ringCatSheaf.obj)
  let I : X.Modules ⥤ Y.Modules := Scheme.Modules.pushforward f
  have hh := congrArg (fun h => h ≫ (I ⋙ G).map
    (((a.comp b).leftAdjointUniq (c.comp d)).hom.app P)) ha
  exact hh.symm.trans (he.trans hd)

lemma presheaf_restrict_pure (U : X.Opens) (M N : X.Modules)
    (V : U.toScheme.Opens)
    (m : M.val.obj (op (U.ι ''ᵁ V))) (n : N.val.obj (op (U.ι ''ᵁ V))) :
    ((modulePresheafTensorRestrict U M.val N.val).hom.app (op V)).hom
      (m ⊗ₜ[Γ(X,U.ι ''ᵁ V)] n) = (show ((modulePresheafRestrict U.ι).obj M.val).obj (op V) from m) ⊗ₜ[Γ(U.toScheme,V)]
      (show ((modulePresheafRestrict U.ι).obj N.val).obj (op V) from n) := by
  rfl

lemma restrict_pure (U : X.Opens) (M N : X.Modules) (V : U.toScheme.Opens)
    (m : M.val.obj (op (U.ι ''ᵁ V))) (n : N.val.obj (op (U.ι ''ᵁ V))) :
    (moduleTensorRestrict U M N).hom.app V
      (pure M N (U.ι ''ᵁ V) m n) =
      pure (M.restrict U.ι) (N.restrict U.ι) V m n := by
  have h := sheafify_restrict_unit U.ι (presheaf M N)
  have h' := congrArg (fun q => q.app (op V) (m ⊗ₜ[Γ(X,U.ι ''ᵁ V)] n)) h
  have hn := (adj U.toScheme).unit.naturality
    (modulePresheafTensorRestrict U M.val N.val).hom
  have hn' := congrArg (fun q => q.app (op V) (m ⊗ₜ[Γ(X,U.ι ''ᵁ V)] n)) hn
  change (((PresheafOfModules.sheafification (𝟙 U.toScheme.ringCatSheaf.obj)).map
    (modulePresheafTensorRestrict U M.val N.val).hom).val.app (op V))
    (((moduleSheafificationRestrict U.ι).hom.app (presheaf M N)).val.app (op V)
      (pure M N (U.ι ''ᵁ V) m n)) = _
  simp only [PresheafOfModules.comp_app] at h' hn'
  change (((moduleSheafificationRestrict U.ι).hom.app (presheaf M N)).val.app (op V))
    (pure M N (U.ι ''ᵁ V) m n) = _ at h'
  rw [h']
  refine hn'.symm.trans ?_
  change (((adj U.toScheme).unit.app (presheaf (M.restrict U.ι) (N.restrict U.ι))).app (op V))
    (((modulePresheafTensorRestrict U M.val N.val).hom.app (op V))
      (m ⊗ₜ[Γ(X,U.ι ''ᵁ V)] n)) = _
  exact congrArg (fun t => (((adj U.toScheme).unit.app
    (presheaf (M.restrict U.ι) (N.restrict U.ι))).app (op V)) t)
      (presheaf_restrict_pure U M N V m n)

lemma restrict_pure_inv (U : X.Opens) (M N : X.Modules) (V : U.toScheme.Opens)
    (m : M.val.obj (op (U.ι ''ᵁ V))) (n : N.val.obj (op (U.ι ''ᵁ V))) :
    (moduleTensorRestrict U M N).inv.app V (pure (M.restrict U.ι) (N.restrict U.ι) V m n) =
      pure M N (U.ι ''ᵁ V) m n := by
  have h := congrArg (fun t => (moduleTensorRestrict U M N).inv.app V t)
    (restrict_pure U M N V m n).symm
  refine h.trans ?_
  exact congrArg (fun q => q.app V (pure M N (U.ι ''ᵁ V) m n))
    (moduleTensorRestrict U M N).hom_inv_id

lemma restrict_hom_ext (U : X.Opens) {M N : X.Modules} {P : U.toScheme.Modules}
    {f g : (moduleTensor X M N).restrict U.ι ⟶ P}
    (h : ∀ (V : U.toScheme.Opens) (m : M.val.obj (op (U.ι ''ᵁ V)))
      (n : N.val.obj (op (U.ι ''ᵁ V))), f.app V (pure M N (U.ι ''ᵁ V) m n) =
      g.app V (pure M N (U.ι ''ᵁ V) m n)) : f = g := by
  apply (cancel_epi (moduleTensorRestrict U M N).inv).mp
  apply hom_ext (M := M.restrict U.ι) (N := N.restrict U.ι)
  intro V m n
  change f.app V ((moduleTensorRestrict U M N).inv.app V (pure _ _ V m n)) =
    g.app V ((moduleTensorRestrict U M N).inv.app V (pure _ _ V m n))
  exact (congrArg (fun x => f.app V x) (restrict_pure_inv U M N V m n)).trans
    ((h V m n).trans (congrArg (fun x => g.app V x) (restrict_pure_inv U M N V m n)).symm)

lemma restrict_map (U : X.Opens) {M N P Q : X.Modules}
    (a : M ⟶ P) (b : N ⟶ Q) :
    (Scheme.Modules.restrictFunctor U.ι).map (moduleTensorMap a b) ≫
      (moduleTensorRestrict U P Q).hom =
    (moduleTensorRestrict U M N).hom ≫
      moduleTensorMap ((Scheme.Modules.restrictFunctor U.ι).map a)
        ((Scheme.Modules.restrictFunctor U.ι).map b) := by
  apply restrict_hom_ext U
  intro V m n
  change (moduleTensorRestrict U P Q).hom.app V
    ((moduleTensorMap a b).app (U.ι ''ᵁ V) (pure M N (U.ι ''ᵁ V) m n)) =
    (moduleTensorMap _ _).app V ((moduleTensorRestrict U M N).hom.app V
      (pure M N (U.ι ''ᵁ V) m n))
  exact (congrArg (fun x => (moduleTensorRestrict U P Q).hom.app V x)
    (map_pure a b (U.ι ''ᵁ V) m n)).trans
    ((restrict_pure U P Q V (a.app (U.ι ''ᵁ V) m) (b.app (U.ι ''ᵁ V) n)).trans
      ((map_pure ((Scheme.Modules.restrictFunctor U.ι).map a)
        ((Scheme.Modules.restrictFunctor U.ι).map b) V m n).symm.trans
        (congrArg (fun x => (moduleTensorMap ((Scheme.Modules.restrictFunctor U.ι).map a)
          ((Scheme.Modules.restrictFunctor U.ι).map b)).app V x)
          (restrict_pure U M N V m n)).symm))

lemma unit_pure (M : X.Modules) (U : X.Opens) (a : Γ(X,U)) (m : M.val.obj (op U)) :
    (moduleTensorUnit M).hom.app U (pure (structureSheaf X) M U a m) = a • m := by
  let : MonoidalCategory (PresheafOfModules X.ringCatSheaf.obj) :=
    PresheafOfModulesOfCommRing.monoidalCategory (R := X.presheaf)
  have h := ((adj X).homEquiv _ _).apply_symm_apply (λ_ M.val).hom
  change (adj X).homEquiv _ M (moduleTensorUnit M).hom = (λ_ M.val).hom at h
  exact congrArg (fun q => q.app (op U) (a ⊗ₜ[Γ(X,U)] m)) h

lemma right_unit_pure (M : X.Modules) (U : X.Opens) (m : M.val.obj (op U)) (a : Γ(X,U)) :
    (moduleTensorRightUnit M).hom.app U (pure M (structureSheaf X) U m a) = a • m := by
  let : MonoidalCategory (PresheafOfModules X.ringCatSheaf.obj) :=
    PresheafOfModulesOfCommRing.monoidalCategory (R := X.presheaf)
  have h := ((adj X).homEquiv _ _).apply_symm_apply (ρ_ M.val).hom
  change (adj X).homEquiv _ M (moduleTensorRightUnit M).hom = (ρ_ M.val).hom at h
  exact congrArg (fun q => q.app (op U) (m ⊗ₜ[Γ(X,U)] a)) h

end PiExponentSeshadri.TensorPure

end

end OAI
end Source0388

-- Source: OAI/NumberTheory/PiExponent/Approximation/FrameSubopens.lean
section Source0389
/-
Modification notice for the LogTwo project.
Derived from openai/math (Apache-2.0), revision adc7f1241b42e322a6451854ab7e4b4c146bf78a.
Original source: lean/OAI/NumberTheory/PiExponent/Approximation/FrameSubopens.lean
Changes: Convert module/import declarations to the Lean 4.34 public module format.
See ../THIRD_PARTY_NOTICES.txt for provenance and the recorded changes.
-/

namespace OAI

namespace PiExponentSeshadri.Frames
noncomputable section
open AlgebraicGeometry CategoryTheory TopologicalSpace
variable {X : Scheme} {M : X.Modules}

def restrictOpenFrame {U V : X.Opens} (h : V ≤ U) (e : M.restrict U.ι ≅ O U.toScheme) :
    M.restrict V.ι ≅ O V.toScheme :=
  ((Scheme.Modules.restrictFunctorCongr (X.homOfLE_ι h)).app M).symm ≪≫
    (Scheme.Modules.restrictFunctorComp (X.homOfLE h) U.ι).app M ≪≫
      restrictFrame (X.homOfLE h) e

lemma restrictOpenFrame_coefficient_global {U V : X.Opens} (h : V ≤ U)
    (e : M.restrict U.ι ≅ O U.toScheme) (s : O X ⟶ M) :
    coefficient (restrictOpenFrame h e) (restrictSection V.ι s) =
      (X.homOfLE h).appTop (coefficient e (restrictSection U.ι s)) := by
  unfold restrictOpenFrame
  rw [coefficient_transport]
  rw [← restrictSection_congr (X.homOfLE_ι h) s, Category.assoc]
  have he : (Scheme.Modules.restrictFunctorCongr (X.homOfLE_ι h)).hom.app M ≫
      ((Scheme.Modules.restrictFunctorCongr (X.homOfLE_ι h)).app M).symm.hom = 𝟙 _ :=
    Iso.hom_inv_id ((Scheme.Modules.restrictFunctorCongr (X.homOfLE_ι h)).app M)
  rw [he, Category.comp_id]
  exact coefficient_restrict_comp (X.homOfLE h) U.ι e s

lemma frameChange_restrictOpenFrame {U V W : X.Opens} (hWU : W ≤ U) (hWV : W ≤ V)
    (e : M.restrict U.ι ≅ O U.toScheme) (f : M.restrict V.ι ≅ O V.toScheme)
    (s : O X ⟶ M) (hs : coefficient e (restrictSection U.ι s) = 1) :
    (frameChange (restrictOpenFrame hWU e) (restrictOpenFrame hWV f) : Γ(W.toScheme,⊤)) =
      (X.homOfLE hWV).appTop (coefficient f (restrictSection V.ι s)) := by
  have h := coefficient_change (restrictOpenFrame hWU e) (restrictOpenFrame hWV f)
    (restrictSection W.ι s)
  rw [restrictOpenFrame_coefficient_global, restrictOpenFrame_coefficient_global,
    hs, map_one, mul_one] at h
  exact h.symm

end
end PiExponentSeshadri.Frames

end OAI
end Source0389

-- Source: OAI/NumberTheory/PiExponent/Approximation/LinePullback.lean
section Source0390
/-
Modification notice for the LogTwo project.
Derived from openai/math (Apache-2.0), revision adc7f1241b42e322a6451854ab7e4b4c146bf78a.
Original source: lean/OAI/NumberTheory/PiExponent/Approximation/LinePullback.lean
Changes: Convert module/import declarations to the Lean 4.34 public module format.
See ../THIRD_PARTY_NOTICES.txt for provenance and the recorded changes.
-/

namespace OAI

namespace PiExponentSeshadri.Geometry
noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace
variable {X Y : Scheme.{0}}

instance opensMap_final (f : Y ⟶ X) : (Opens.map f.base).Final := by
  let : PreservesLimit (Functor.empty.{0} X.Opens) (Opens.map f.base) := by
    apply preservesLimit_of_preserves_limit_cone (isTerminalTop (α := X.Opens))
    exact (isLimitMapConeEmptyConeEquiv (Opens.map f.base) (⊤ : X.Opens)).symm isTerminalTop
  infer_instance

def pullbackRestrictIso (f : Y ⟶ X) (L : X.Modules) (U : X.Opens) :
    ((Scheme.Modules.pullback f).obj L).restrict (f ⁻¹ᵁ U).ι ≅
      (Scheme.Modules.pullback (f ∣_ U)).obj (L.restrict U.ι) :=
  (Scheme.Modules.restrictFunctorIsoPullback (f ⁻¹ᵁ U).ι).app _ ≪≫
  (Scheme.Modules.pullbackComp (f ⁻¹ᵁ U).ι f).app L ≪≫
  (Scheme.Modules.pullbackCongr (morphismRestrict_ι f U).symm).app L ≪≫
  ((Scheme.Modules.pullbackComp (f ∣_ U) U.ι).app L).symm ≪≫
  (Scheme.Modules.pullback (f ∣_ U)).mapIso
    ((Scheme.Modules.restrictFunctorIsoPullback U.ι).app L).symm

def LineBundle.pullback (L : LineBundle X) (f : Y ⟶ X) : LineBundle Y where
  sheaf := (Scheme.Modules.pullback f).obj L.sheaf
  locallyRankOne y := by
    obtain ⟨U,hy,⟨e⟩⟩ := L.locallyRankOne (f y)
    refine ⟨f ⁻¹ᵁ U,hy,⟨pullbackRestrictIso f L.sheaf U ≪≫
      (Scheme.Modules.pullback (f ∣_ U)).mapIso e ≪≫ ?_⟩⟩
    letI : (Opens.map (f ∣_ U).base).Final := opensMap_final (f ∣_ U)
    letI : (SheafOfModules.pushforward (f ∣_ U).toRingCatSheafHom).IsRightAdjoint :=
      inferInstanceAs (Scheme.Modules.pushforward (f ∣_ U)).IsRightAdjoint
    let hu : IsIso (SheafOfModules.pullbackObjUnitToUnit (f ∣_ U).toRingCatSheafHom) :=
      SheafOfModules.instIsIsoPullbackObjUnitToUnitOfFinal (f ∣_ U).toRingCatSheafHom
    let a : (SheafOfModules.pullback (f ∣_ U).toRingCatSheafHom).obj
        (SheafOfModules.unit U.toScheme.ringCatSheaf) ≅
        SheafOfModules.unit (f ⁻¹ᵁ U).toScheme.ringCatSheaf :=
      @asIso _ _ _ _ (SheafOfModules.pullbackObjUnitToUnit (f ∣_ U).toRingCatSheafHom) hu
    exact { hom := a.hom, inv := a.inv, hom_inv_id := a.hom_inv_id, inv_hom_id := a.inv_hom_id }

end
end PiExponentSeshadri.Geometry

end OAI
end Source0390

-- Source: OAI/NumberTheory/PiExponent/Approximation/PushforwardTensor.lean
section Source0391
/-
Modification notice for the LogTwo project.
Derived from openai/math (Apache-2.0), revision adc7f1241b42e322a6451854ab7e4b4c146bf78a.
Original source: lean/OAI/NumberTheory/PiExponent/Approximation/PushforwardTensor.lean
Changes: Convert module/import declarations to the Lean 4.34 public module format.
See ../THIRD_PARTY_NOTICES.txt for provenance and the recorded changes.
-/

namespace OAI

noncomputable section

namespace PiExponentSeshadri

namespace PushforwardTensor
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite
open PiExponentSeshadri.Geometry PiExponentSeshadri.TensorPure
variable {X Y : Scheme.{0}} (f : X ⟶ Y)

def presheafHom (M N : X.Modules) :
    presheaf ((Scheme.Modules.pushforward f).obj M) ((Scheme.Modules.pushforward f).obj N) ⟶
      ((Scheme.Modules.pushforward f).obj (moduleTensor X M N)).val where
  app U := ModuleCat.MonoidalCategory.tensorLift
    (fun m n => pure M N (f ⁻¹ᵁ U.unop) m n)
    (fun m m' n => pure_add_left M N _ m m' n)
    (fun a m n => pure_smul_left M N _ ((f.app U.unop).hom a) m n)
    (fun m n n' => pure_add_right M N _ m n n')
    (fun a m n => pure_smul_right M N _ ((f.app U.unop).hom a) m n)
  naturality {U V} i := by
    apply ModuleCat.MonoidalCategory.tensor_ext
    intro m n
    exact (pure_restrict M N ((Opens.map f.base).map i.unop) m n).symm

def hom (M N : X.Modules) :
    moduleTensor Y ((Scheme.Modules.pushforward f).obj M) ((Scheme.Modules.pushforward f).obj N) ⟶
      (Scheme.Modules.pushforward f).obj (moduleTensor X M N) :=
  ((adj Y).homEquiv _ _).symm (presheafHom f M N)

lemma hom_pure (M N : X.Modules) (U : Y.Opens)
    (m : M.val.obj (op (f ⁻¹ᵁ U))) (n : N.val.obj (op (f ⁻¹ᵁ U))) :
    (hom f M N).app U
      (pure ((Scheme.Modules.pushforward f).obj M) ((Scheme.Modules.pushforward f).obj N) U m n) =
      pure M N (f ⁻¹ᵁ U) m n := by
  have h := ((adj Y).homEquiv
    (presheaf ((Scheme.Modules.pushforward f).obj M) ((Scheme.Modules.pushforward f).obj N))
    ((Scheme.Modules.pushforward f).obj (moduleTensor X M N))).apply_symm_apply (presheafHom f M N)
  exact congrArg (fun q => q.app (op U) (m ⊗ₜ[Γ(Y,U)] n)) h

@[reassoc] lemma naturality {M N P Q : X.Modules} (a : M ⟶ P) (b : N ⟶ Q) :
    moduleTensorMap ((Scheme.Modules.pushforward f).map a) ((Scheme.Modules.pushforward f).map b) ≫
      hom f P Q = hom f M N ≫ (Scheme.Modules.pushforward f).map (moduleTensorMap a b) := by
  apply TensorPure.hom_ext
  intro U m n
  change (hom f P Q).app U ((moduleTensorMap _ _).app U (pure _ _ U m n)) =
    (moduleTensorMap a b).app (f ⁻¹ᵁ U) ((hom f M N).app U (pure _ _ U m n))
  have h₁ := TensorPure.map_pure ((Scheme.Modules.pushforward f).map a)
    ((Scheme.Modules.pushforward f).map b) U m n
  have h₂ := hom_pure f P Q U (a.app (f ⁻¹ᵁ U) m) (b.app (f ⁻¹ᵁ U) n)
  have h₃ := hom_pure f M N U m n
  have h₄ := TensorPure.map_pure a b (f ⁻¹ᵁ U) m n
  exact ((congrArg (fun z => (hom f P Q).app U z) h₁).trans h₂).trans
    ((congrArg (fun z => (moduleTensorMap a b).app (f ⁻¹ᵁ U) z) h₃).trans h₄).symm

end PushforwardTensor

namespace Geometry
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace
open PiExponentSeshadri.Frames
variable {X Y Z : Scheme.{0}}

def pullbackUnitIso (f : Y ⟶ X) : (Scheme.Modules.pullback f).obj (O X) ≅ O Y := by
  letI : (Opens.map f.base).Final := opensMap_final f
  letI : (SheafOfModules.pushforward f.toRingCatSheafHom).IsRightAdjoint :=
    inferInstanceAs (Scheme.Modules.pushforward f).IsRightAdjoint
  let hu : IsIso (SheafOfModules.pullbackObjUnitToUnit f.toRingCatSheafHom) :=
    SheafOfModules.instIsIsoPullbackObjUnitToUnitOfFinal f.toRingCatSheafHom
  let a : (SheafOfModules.pullback f.toRingCatSheafHom).obj
      (SheafOfModules.unit X.ringCatSheaf) ≅ SheafOfModules.unit Y.ringCatSheaf :=
    @asIso _ _ _ _ (SheafOfModules.pullbackObjUnitToUnit f.toRingCatSheafHom) hu
  exact { hom := a.hom, inv := a.inv, hom_inv_id := a.hom_inv_id, inv_hom_id := a.inv_hom_id }

def pullbackSection (f : Y ⟶ X) {M : X.Modules} (s : O X ⟶ M) :
    O Y ⟶ (Scheme.Modules.pullback f).obj M :=
  (pullbackUnitIso f).inv ≫ (Scheme.Modules.pullback f).map s

def pullbackFrame (f : Y ⟶ X) {M : X.Modules} (e : M ≅ O X) :
    (Scheme.Modules.pullback f).obj M ≅ O Y :=
  (Scheme.Modules.pullback f).mapIso e ≪≫ pullbackUnitIso f

lemma pullbackUnit_adjunction (f : Y ⟶ X) :
    (Scheme.Modules.pullbackPushforwardAdjunction f).homEquiv _ _ (pullbackUnitIso f).hom =
      SheafOfModules.unitToPushforwardObjUnit f.toRingCatSheafHom := by
  let : (SheafOfModules.pushforward f.toRingCatSheafHom).IsRightAdjoint :=
    inferInstanceAs (Scheme.Modules.pushforward f).IsRightAdjoint
  change (SheafOfModules.pullbackPushforwardAdjunction f.toRingCatSheafHom).homEquiv _ _
    (SheafOfModules.pullbackObjUnitToUnit f.toRingCatSheafHom) = _
  exact SheafOfModules.pullbackPushforwardAdjunction_homEquiv_pullbackObjUnitToUnit _

end Geometry

end PiExponentSeshadri

end

end OAI
end Source0391

-- Source: OAI/NumberTheory/PiExponent/Approximation/TensorOpenBaseChange.lean
section Source0392
/-
Modification notice for the LogTwo project.
Derived from openai/math (Apache-2.0), revision adc7f1241b42e322a6451854ab7e4b4c146bf78a.
Original source: lean/OAI/NumberTheory/PiExponent/Approximation/TensorOpenBaseChange.lean
Changes: Convert module/import declarations to the Lean 4.34 public module format.
See ../THIRD_PARTY_NOTICES.txt for provenance and the recorded changes.
-/

namespace OAI

noncomputable section

namespace PiExponentSeshadri.OpenBaseChange

section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite
open PiExponentSeshadri.Geometry PiExponentSeshadri.Frames
variable {X Y : Scheme.{0}} (f : X ⟶ Y) (U : Y.Opens)

def leftSquare :
    Scheme.Modules.restrictFunctor U.ι ⋙ Scheme.Modules.pullback (f ∣_ U) ≅
      Scheme.Modules.pullback f ⋙ Scheme.Modules.restrictFunctor (f ⁻¹ᵁ U).ι :=
  (conjugateIsoEquiv
    ((Scheme.Modules.pullbackPushforwardAdjunction f).comp
      (Scheme.Modules.restrictAdjunction (f ⁻¹ᵁ U).ι))
    ((Scheme.Modules.restrictAdjunction U.ι).comp
      (Scheme.Modules.pullbackPushforwardAdjunction (f ∣_ U)))).symm (rightSquare f U)

lemma unit_compatibility (M : Y.Modules) :
    (Scheme.Modules.restrictFunctor U.ι).map
      ((Scheme.Modules.pullbackPushforwardAdjunction f).unit.app M) ≫
      (iso f U ((Scheme.Modules.pullback f).obj M)).hom =
    (Scheme.Modules.pullbackPushforwardAdjunction (f ∣_ U)).unit.app (M.restrict U.ι) ≫
      (Scheme.Modules.pushforward (f ∣_ U)).map ((leftSquare f U).hom.app M) := by
  let a := Scheme.Modules.pullbackPushforwardAdjunction f
  let b := Scheme.Modules.restrictAdjunction (f ⁻¹ᵁ U).ι
  let c := Scheme.Modules.restrictAdjunction U.ι
  let d := Scheme.Modules.pullbackPushforwardAdjunction (f ∣_ U)
  have h := unit_conjugateEquiv_symm (a.comp b) (c.comp d) (rightSquare f U).hom M
  rw [Adjunction.comp_unit_app, Adjunction.comp_unit_app] at h
  change (a.unit.app M ≫ (Scheme.Modules.pushforward f).map
    (b.unit.app ((Scheme.Modules.pullback f).obj M))) ≫
      (rightSquare f U).hom.app _ =
    (c.unit.app M ≫ (Scheme.Modules.pushforward U.ι).map
      (d.unit.app (M.restrict U.ι))) ≫
      (Scheme.Modules.pushforward U.ι).map
        ((Scheme.Modules.pushforward (f ∣_ U)).map ((leftSquare f U).hom.app M)) at h
  have hc := congrArg (fun q => (Scheme.Modules.restrictFunctor U.ι).map q ≫
    c.counit.app ((Scheme.Modules.pushforward (f ∣_ U)).obj
      (((Scheme.Modules.pullback f).obj M).restrict (f ⁻¹ᵁ U).ι))) h
  simp only [Functor.map_comp, Category.assoc] at hc
  change _ = _ at hc
  have hn := c.counit.naturality
    (d.unit.app (M.restrict U.ι) ≫
      (Scheme.Modules.pushforward (f ∣_ U)).map ((leftSquare f U).hom.app M))
  dsimp only [Functor.comp_map, Functor.id_map] at hn
  rw [Functor.map_comp, Functor.map_comp] at hn
  rw [Category.assoc] at hn
  dsimp only [Functor.comp_obj, Functor.id_obj] at hn
  rw [hn] at hc
  simp only [← Category.assoc] at hc
  have ht := c.left_triangle_components M
  change (Scheme.Modules.restrictFunctor U.ι).map (c.unit.app M) ≫
    c.counit.app (M.restrict U.ι) = 𝟙 _ at ht
  rw [ht, Category.id_comp] at hc
  simpa only [a, b, c, d, iso, asIso_hom, hom, Category.assoc] using hc

end

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite
open PiExponentSeshadri.Geometry PiExponentSeshadri.TensorPure
variable {X Y : Scheme.{0}} (f : X ⟶ Y) (U : Y.Opens)

lemma modules_comp_app {Z : Scheme.{0}} {M N P : Z.Modules} (a : M ⟶ N) (b : N ⟶ P)
    (W : Z.Opens) : (a ≫ b).app W = a.app W ≫ b.app W := rfl

lemma hom_app (M : X.Modules) (V : U.toScheme.Opens) :
    (hom f U M).app V = M.presheaf.map
      (eqToHom (image_morphismRestrict_preimage f U V)).op := by
  change ((Scheme.Modules.restrictAdjunction (f ⁻¹ᵁ U).ι).unit.app M).app
    (f ⁻¹ᵁ (U.ι ''ᵁ V)) ≫
      ((rightSquare f U).hom.app (M.restrict (f ⁻¹ᵁ U).ι)).app (U.ι ''ᵁ V) ≫
      ((Scheme.Modules.restrictAdjunction U.ι).counit.app
        ((Scheme.Modules.pushforward (f ∣_ U)).obj (M.restrict (f ⁻¹ᵁ U).ι))).app V = _
  simp only [rightSquare, Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app,
    Scheme.Modules.restrictAdjunction_unit_app_app,
    Scheme.Modules.restrictAdjunction_counit_app_app]
  simp only [modules_comp_app,Scheme.Modules.pushforwardComp_hom_app_app,
    Scheme.Modules.pushforwardComp_inv_app_app,
    Scheme.Modules.pushforwardCongr_hom_app_app]
  simp only [Scheme.Modules.pushforward_obj_presheaf_map, Scheme.Modules.restrict_map]
  erw [Category.id_comp, Category.comp_id, ← Functor.map_comp, ← Functor.map_comp]
  congr 1

lemma tensor_pure (M N : X.Modules) (V : U.toScheme.Opens)
    (m : M.val.obj (op (f ⁻¹ᵁ (U.ι ''ᵁ V))))
    (n : N.val.obj (op (f ⁻¹ᵁ (U.ι ''ᵁ V)))) :
    (moduleTensorRestrict (f ⁻¹ᵁ U) M N).hom.app ((f ∣_ U) ⁻¹ᵁ V)
      ((hom f U (moduleTensor X M N)).app V
        (pure M N (f ⁻¹ᵁ (U.ι ''ᵁ V)) m n)) =
    pure (M.restrict (f ⁻¹ᵁ U).ι) (N.restrict (f ⁻¹ᵁ U).ι) ((f ∣_ U) ⁻¹ᵁ V)
      ((hom f U M).app V m) ((hom f U N).app V n) := by
  rw [hom_app, hom_app, hom_app]
  change (moduleTensorRestrict (f ⁻¹ᵁ U) M N).hom.app _
    ((moduleTensor X M N).val.map _ (pure M N _ m n)) = _
  exact (congrArg (fun t => (moduleTensorRestrict (f ⁻¹ᵁ U) M N).hom.app
    ((f ∣_ U) ⁻¹ᵁ V) t) (pure_restrict M N
      (eqToHom (image_morphismRestrict_preimage f U V)) m n)).trans
    (restrict_pure (f ⁻¹ᵁ U) M N ((f ∣_ U) ⁻¹ᵁ V) _ _)

lemma tensor_square (M N : X.Modules) :
    (Scheme.Modules.restrictFunctor U.ι).map (PushforwardTensor.hom f M N) ≫
      (iso f U (moduleTensor X M N)).hom ≫
      (Scheme.Modules.pushforward (f ∣_ U)).map
        (moduleTensorRestrict (f ⁻¹ᵁ U) M N).hom =
    (moduleTensorRestrict U ((Scheme.Modules.pushforward f).obj M)
      ((Scheme.Modules.pushforward f).obj N)).hom ≫
      moduleTensorMap (iso f U M).hom (iso f U N).hom ≫
      PushforwardTensor.hom (f ∣_ U) (M.restrict (f ⁻¹ᵁ U).ι) (N.restrict (f ⁻¹ᵁ U).ι) := by
  apply TensorPure.restrict_hom_ext U
  intro V m n
  change (moduleTensorRestrict (f ⁻¹ᵁ U) M N).hom.app ((f ∣_ U) ⁻¹ᵁ V)
    ((hom f U (moduleTensor X M N)).app V
      ((PushforwardTensor.hom f M N).app (U.ι ''ᵁ V)
        (pure _ _ (U.ι ''ᵁ V) m n))) =
    (PushforwardTensor.hom (f ∣_ U) _ _).app V
      ((moduleTensorMap (iso f U M).hom (iso f U N).hom).app V
        ((moduleTensorRestrict U _ _).hom.app V (pure _ _ (U.ι ''ᵁ V) m n)))
  have hA := congrArg (fun z =>
    (moduleTensorRestrict (f ⁻¹ᵁ U) M N).hom.app ((f ∣_ U) ⁻¹ᵁ V)
      ((hom f U (moduleTensor X M N)).app V z))
    (PushforwardTensor.hom_pure f M N (U.ι ''ᵁ V) m n)
  have hB := congrArg (fun z => (PushforwardTensor.hom (f ∣_ U) _ _).app V
    ((moduleTensorMap (iso f U M).hom (iso f U N).hom).app V z))
    (restrict_pure U ((Scheme.Modules.pushforward f).obj M)
      ((Scheme.Modules.pushforward f).obj N) V m n)
  have hC := congrArg (fun z => (PushforwardTensor.hom (f ∣_ U) _ _).app V z)
    (map_pure (iso f U M).hom (iso f U N).hom V m n)
  have hD := PushforwardTensor.hom_pure (f ∣_ U)
    (M.restrict (f ⁻¹ᵁ U).ι) (N.restrict (f ⁻¹ᵁ U).ι) V
      ((hom f U M).app V m) ((hom f U N).app V n)
  exact hA.trans ((tensor_pure f U M N V m n).trans ((hB.trans (hC.trans hD)).symm))

@[reassoc] lemma naturality {M N : X.Modules} (a : M ⟶ N) :
    (Scheme.Modules.restrictFunctor U.ι).map ((Scheme.Modules.pushforward f).map a) ≫
      (iso f U N).hom =
    (iso f U M).hom ≫ (Scheme.Modules.pushforward (f ∣_ U)).map
      ((Scheme.Modules.restrictFunctor (f ⁻¹ᵁ U).ι).map a) := by
  ext V x
  change (hom f U N).app V (a.app (f ⁻¹ᵁ (U.ι ''ᵁ V)) x) =
    a.app ((f ⁻¹ᵁ U).ι ''ᵁ ((f ∣_ U) ⁻¹ᵁ V)) ((hom f U M).app V x)
  rw [hom_app,hom_app]
  exact (CategoryTheory.congr_fun (a.mapPresheaf.naturality
    (eqToHom (image_morphismRestrict_preimage f U V)).op) x).symm

end PiExponentSeshadri.OpenBaseChange

end

end OAI
end Source0392

-- Source: OAI/NumberTheory/PiExponent/Approximation/LinePullbackPowers.lean
section Source0393
/-
Modification notice for the LogTwo project.
Derived from openai/math (Apache-2.0), revision adc7f1241b42e322a6451854ab7e4b4c146bf78a.
Original source: lean/OAI/NumberTheory/PiExponent/Approximation/LinePullbackPowers.lean
Changes: Convert module/import declarations to the Lean 4.34 public module format.
See ../THIRD_PARTY_NOTICES.txt for provenance and the recorded changes.
-/

namespace OAI

noncomputable section

namespace PiExponentSeshadri.PullbackTensor
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite MonoidalCategory
open PiExponentSeshadri.Geometry PiExponentSeshadri.TensorPure PiExponentSeshadri.Frames
variable {X Y : Scheme.{0}} (f : X ⟶ Y) (U : Y.Opens)

def hom (M N : Y.Modules) : (Scheme.Modules.pullback f).obj (moduleTensor Y M N) ⟶
    moduleTensor X ((Scheme.Modules.pullback f).obj M) ((Scheme.Modules.pullback f).obj N) :=
  ((Scheme.Modules.pullbackPushforwardAdjunction f).homEquiv _ _).symm
    (moduleTensorMap ((Scheme.Modules.pullbackPushforwardAdjunction f).unit.app M)
      ((Scheme.Modules.pullbackPushforwardAdjunction f).unit.app N) ≫
      PushforwardTensor.hom f _ _)

lemma unit_hom (M N : Y.Modules) :
    (Scheme.Modules.pullbackPushforwardAdjunction f).unit.app (moduleTensor Y M N) ≫
      (Scheme.Modules.pushforward f).map (hom f M N) =
    moduleTensorMap ((Scheme.Modules.pullbackPushforwardAdjunction f).unit.app M)
      ((Scheme.Modules.pullbackPushforwardAdjunction f).unit.app N) ≫
      PushforwardTensor.hom f _ _ :=
  ((Scheme.Modules.pullbackPushforwardAdjunction f).homEquiv _ _).apply_symm_apply _

@[reassoc] lemma naturality {M N P Q : Y.Modules} (a : M ⟶ P) (b : N ⟶ Q) :
    (Scheme.Modules.pullback f).map (moduleTensorMap a b) ≫ hom f P Q =
      hom f M N ≫ moduleTensorMap ((Scheme.Modules.pullback f).map a)
        ((Scheme.Modules.pullback f).map b) := by
  apply ((Scheme.Modules.pullbackPushforwardAdjunction f).homEquiv _ _).injective
  rw [Adjunction.homEquiv_naturality_left,Adjunction.homEquiv_naturality_right]
  simp only [hom,Equiv.apply_symm_apply]
  rw [← Category.assoc,← moduleTensorMap_comp]
  rw [Category.assoc,← PushforwardTensor.naturality,← Category.assoc,← moduleTensorMap_comp]
  rw [← (Scheme.Modules.pullbackPushforwardAdjunction f).unit_naturality,
    ← (Scheme.Modules.pullbackPushforwardAdjunction f).unit_naturality]

lemma unit_pure_structure (Z : Scheme.{0}) (U : Z.Opens)
    (a b : (O Z).val.obj (op U)) :
    (moduleTensorUnit (O Z)).hom.app U (pure (O Z) (O Z) U a b) =
      (show Γ(Z,U) from a) * (show Γ(Z,U) from b) :=
  TensorPure.unit_pure (O Z) U a b

lemma unit_compatibility :
    hom f (O Y) (O Y) ≫
      (moduleTensorIso (pullbackUnitIso f) (pullbackUnitIso f)).hom ≫
      (moduleTensorUnit (O X)).hom =
    (Scheme.Modules.pullback f).map (moduleTensorUnit (O Y)).hom ≫
      (pullbackUnitIso f).hom := by
  apply ((Scheme.Modules.pullbackPushforwardAdjunction f).homEquiv _ _).injective
  let adj := Scheme.Modules.pullbackPushforwardAdjunction f
  have hl := adj.homEquiv_naturality_left (moduleTensorUnit (O Y)).hom
    (pullbackUnitIso f).hom
  have hr := adj.homEquiv_naturality_right (hom f (O Y) (O Y))
    ((moduleTensorIso (pullbackUnitIso f) (pullbackUnitIso f)).hom ≫
      (moduleTensorUnit (O X)).hom)
  have hu := congrArg (fun q => (moduleTensorUnit (O Y)).hom ≫ q)
    (pullbackUnit_adjunction f)
  refine hr.trans (Eq.trans ?_ (hu.symm.trans hl.symm))
  simp only [adj, hom, Equiv.apply_symm_apply]
  apply TensorPure.hom_ext
  intro U a b
  change (moduleTensorUnit (O X)).hom.app (f ⁻¹ᵁ U)
    ((moduleTensorMap (pullbackUnitIso f).hom (pullbackUnitIso f).hom).app (f ⁻¹ᵁ U)
      ((PushforwardTensor.hom f _ _).app U ((moduleTensorMap _ _).app U
        (pure (O Y) (O Y) U a b)))) =
    (f.app U) ((moduleTensorUnit (O Y)).hom.app U (pure (O Y) (O Y) U a b))
  let η := (Scheme.Modules.pullbackPushforwardAdjunction f).unit.app (O Y)
  let m := η.app U a
  let n := η.app U b
  have h₁ := congrArg (fun z => (moduleTensorUnit (O X)).hom.app (f ⁻¹ᵁ U)
    ((moduleTensorMap (pullbackUnitIso f).hom (pullbackUnitIso f).hom).app (f ⁻¹ᵁ U)
      ((PushforwardTensor.hom f _ _).app U z)))
    (TensorPure.map_pure η η U a b)
  have h₂ := congrArg (fun z => (moduleTensorUnit (O X)).hom.app (f ⁻¹ᵁ U)
    ((moduleTensorMap (pullbackUnitIso f).hom (pullbackUnitIso f).hom).app (f ⁻¹ᵁ U) z))
    (PushforwardTensor.hom_pure f ((Scheme.Modules.pullback f).obj (O Y))
      ((Scheme.Modules.pullback f).obj (O Y)) U m n)
  have h₃ := congrArg (fun z => (moduleTensorUnit (O X)).hom.app (f ⁻¹ᵁ U) z)
    (TensorPure.map_pure (pullbackUnitIso f).hom (pullbackUnitIso f).hom (f ⁻¹ᵁ U) m n)
  refine h₁.trans (h₂.trans (h₃.trans ((unit_pure_structure X (f ⁻¹ᵁ U) _ _).trans ?_)))
  have hy := congrArg (fun z => (f.app U) z) (unit_pure_structure Y U a b)
  refine Eq.trans ?_ hy.symm
  have hu := congrArg (fun q => q.app U) (pullbackUnit_adjunction f)
  have ha := congrArg (fun q => q a) hu
  have hb := congrArg (fun q => q b) hu
  change (pullbackUnitIso f).hom.app (f ⁻¹ᵁ U)
    (((Scheme.Modules.pullbackPushforwardAdjunction f).unit.app (O Y)).app U a) =
    (f.app U) a at ha
  change (pullbackUnitIso f).hom.app (f ⁻¹ᵁ U)
    (((Scheme.Modules.pullbackPushforwardAdjunction f).unit.app (O Y)).app U b) =
    (f.app U) b at hb
  exact (congrArg₂ (fun a b : Γ(X,f ⁻¹ᵁ U) => a * b) ha hb).trans
    (map_mul (f.app U).hom (show Γ(Y,U) from a) (show Γ(Y,U) from b)).symm

instance unit_isIso : IsIso (hom f (O Y) (O Y)) := by
  let e := (Scheme.Modules.pullback f).mapIso (moduleTensorUnit (O Y)) ≪≫
    pullbackUnitIso f
  let d := moduleTensorIso (pullbackUnitIso f) (pullbackUnitIso f) ≪≫
    moduleTensorUnit (O X)
  have hi : IsIso (hom f (O Y) (O Y) ≫ d.hom) := by
    change IsIso (hom f (O Y) (O Y) ≫
      (moduleTensorIso (pullbackUnitIso f) (pullbackUnitIso f)).hom ≫
      (moduleTensorUnit (O X)).hom)
    rw [unit_compatibility]
    exact e.isIso_hom
  let hd : IsIso (C := X.Modules) d.hom := d.isIso_hom
  exact (@isIso_comp_right_iff X.Modules _ _ _ _ _ _ hd).mp hi

lemma open_transpose (M : Y.Modules) :
    (Scheme.Modules.pullbackPushforwardAdjunction (f ∣_ U)).homEquiv _ _
      ((OpenBaseChange.leftSquare f U).hom.app M) =
    (Scheme.Modules.restrictFunctor U.ι).map
      ((Scheme.Modules.pullbackPushforwardAdjunction f).unit.app M) ≫
        (OpenBaseChange.iso f U ((Scheme.Modules.pullback f).obj M)).hom :=
  (OpenBaseChange.unit_compatibility f U M).symm

lemma restrict_compatibility (M N : Y.Modules) :
    (OpenBaseChange.leftSquare f U).hom.app (moduleTensor Y M N) ≫
      (Scheme.Modules.restrictFunctor (f ⁻¹ᵁ U).ι).map (hom f M N) ≫
      (moduleTensorRestrict (f ⁻¹ᵁ U) ((Scheme.Modules.pullback f).obj M)
        ((Scheme.Modules.pullback f).obj N)).hom =
    (Scheme.Modules.pullback (f ∣_ U)).map (moduleTensorRestrict U M N).hom ≫
      hom (f ∣_ U) (M.restrict U.ι) (N.restrict U.ι) ≫
      moduleTensorMap ((OpenBaseChange.leftSquare f U).hom.app M)
        ((OpenBaseChange.leftSquare f U).hom.app N) := by
  apply ((Scheme.Modules.pullbackPushforwardAdjunction (f ∣_ U)).homEquiv _ _).injective
  conv_rhs => rw [Adjunction.homEquiv_naturality_left,
    Adjunction.homEquiv_naturality_right]
  conv_lhs => rw [Adjunction.homEquiv_naturality_right]
  rw [open_transpose]
  have ht : (Scheme.Modules.pullbackPushforwardAdjunction (f ∣_ U)).homEquiv _ _
      (hom (f ∣_ U) (M.restrict U.ι) (N.restrict U.ι)) =
      moduleTensorMap ((Scheme.Modules.pullbackPushforwardAdjunction (f ∣_ U)).unit.app (M.restrict U.ι))
        ((Scheme.Modules.pullbackPushforwardAdjunction (f ∣_ U)).unit.app (N.restrict U.ι)) ≫
        PushforwardTensor.hom (f ∣_ U) _ _ := Equiv.apply_symm_apply _ _
  rw [ht]
  simp only [Functor.map_comp, Category.assoc]
  rw [← OpenBaseChange.naturality_assoc]
  rw [← Functor.map_comp_assoc, unit_hom, Functor.map_comp]
  simp only [Category.assoc]
  rw [OpenBaseChange.tensor_square]
  rw [← Category.assoc]
  refine (congrArg (fun q => q ≫
    moduleTensorMap (OpenBaseChange.iso f U ((Scheme.Modules.pullback f).obj M)).hom
      (OpenBaseChange.iso f U ((Scheme.Modules.pullback f).obj N)).hom ≫
    PushforwardTensor.hom (f ∣_ U)
      (((Scheme.Modules.pullback f).obj M).restrict (f ⁻¹ᵁ U).ι)
      (((Scheme.Modules.pullback f).obj N).restrict (f ⁻¹ᵁ U).ι))
    (TensorPure.restrict_map U
      ((Scheme.Modules.pullbackPushforwardAdjunction f).unit.app M)
      ((Scheme.Modules.pullbackPushforwardAdjunction f).unit.app N))).trans ?_
  simp only [Category.assoc]
  rw [← moduleTensorMap_comp_assoc]
  rw [OpenBaseChange.unit_compatibility,OpenBaseChange.unit_compatibility]
  rw [moduleTensorMap_comp]
  simp only [Category.assoc]
  exact congrArg (fun q => (moduleTensorRestrict U M N).hom ≫
    moduleTensorMap ((Scheme.Modules.pullbackPushforwardAdjunction (f ∣_ U)).unit.app (M.restrict U.ι))
      ((Scheme.Modules.pullbackPushforwardAdjunction (f ∣_ U)).unit.app (N.restrict U.ι)) ≫ q)
    (PushforwardTensor.naturality (f ∣_ U)
      ((OpenBaseChange.leftSquare f U).hom.app M) ((OpenBaseChange.leftSquare f U).hom.app N))

lemma framed_isIso (M N : Y.Modules) (e : M ≅ O Y) (d : N ≅ O Y) :
    IsIso (hom f M N) := by
  have h := naturality f e.hom d.hom
  have : IsIso ((Scheme.Modules.pullback f).map (moduleTensorMap e.hom d.hom) ≫
      hom f (O Y) (O Y)) := by
    change IsIso ((Scheme.Modules.pullback f).map (moduleTensorIso e d).hom ≫ _)
    infer_instance
  have : IsIso (moduleTensorMap ((Scheme.Modules.pullback f).map e.hom)
      ((Scheme.Modules.pullback f).map d.hom)) := by
    change IsIso (moduleTensorIso ((Scheme.Modules.pullback f).mapIso e)
      ((Scheme.Modules.pullback f).mapIso d)).hom
    infer_instance
  have hi : IsIso (hom f M N ≫ moduleTensorMap ((Scheme.Modules.pullback f).map e.hom)
      ((Scheme.Modules.pullback f).map d.hom)) := h ▸ inferInstance
  exact (isIso_comp_right_iff _ _).mp hi

instance power_step_isIso (L : LineBundle Y) (n : ℕ) :
    IsIso (hom f L.sheaf (L.pow n).sheaf) := by
  apply PiExponentSeshadri.SectionOpens.isIso_of_locally_isIso
  intro x
  obtain ⟨U,hx,⟨e⟩⟩ := L.locallyRankOne (f x)
  let d := modulePowFrame U e n
  refine ⟨f ⁻¹ᵁ U,hx,?_⟩
  let : IsIso (hom (f ∣_ U) (L.sheaf.restrict U.ι) ((L.pow n).sheaf.restrict U.ι)) :=
    framed_isIso (f ∣_ U) _ _ e d
  have : IsIso (moduleTensorMap ((OpenBaseChange.leftSquare f U).hom.app L.sheaf)
      ((OpenBaseChange.leftSquare f U).hom.app (L.pow n).sheaf)) := by
    change IsIso (moduleTensorIso ((OpenBaseChange.leftSquare f U).app L.sheaf)
      ((OpenBaseChange.leftSquare f U).app (L.pow n).sheaf)).hom
    infer_instance
  have h := restrict_compatibility f U L.sheaf (L.pow n).sheaf
  have : IsIso ((OpenBaseChange.leftSquare f U).hom.app (moduleTensor Y L.sheaf (L.pow n).sheaf) ≫
      (Scheme.Modules.restrictFunctor (f ⁻¹ᵁ U).ι).map (hom f L.sheaf (L.pow n).sheaf) ≫
      (moduleTensorRestrict (f ⁻¹ᵁ U) ((Scheme.Modules.pullback f).obj L.sheaf)
        ((Scheme.Modules.pullback f).obj (L.pow n).sheaf)).hom) := by rw [h]; infer_instance
  have hi : IsIso ((Scheme.Modules.restrictFunctor (f ⁻¹ᵁ U).ι).map
      (hom f L.sheaf (L.pow n).sheaf) ≫
      (moduleTensorRestrict (f ⁻¹ᵁ U) ((Scheme.Modules.pullback f).obj L.sheaf)
        ((Scheme.Modules.pullback f).obj (L.pow n).sheaf)).hom) :=
    (isIso_comp_left_iff ((OpenBaseChange.leftSquare f U).hom.app
      (moduleTensor Y L.sheaf (L.pow n).sheaf)) _).mp inferInstance
  exact (isIso_comp_right_iff _ _).mp hi

def powIso (L : LineBundle Y) : ∀ n : ℕ,
    (Scheme.Modules.pullback f).obj (L.pow n).sheaf ≅ ((L.pullback f).pow n).sheaf
  | 0 => pullbackUnitIso f
  | n+1 => @asIso _ _ _ _ (hom f L.sheaf (L.pow n).sheaf) (power_step_isIso f L n) ≪≫
      moduleTensorIso (Iso.refl _) (powIso L n)

end PiExponentSeshadri.PullbackTensor

end

end OAI
end Source0393

-- Source: OAI/NumberTheory/PiExponent/Geometry/LineBundleProduct.lean
section Source0394
/-
Modification notice for the LogTwo project.
Derived from openai/math (Apache-2.0), revision adc7f1241b42e322a6451854ab7e4b4c146bf78a.
Original source: lean/OAI/NumberTheory/PiExponent/Geometry/LineBundleProduct.lean
Changes: Convert module/import declarations to the Lean 4.34 public module format.
See ../THIRD_PARTY_NOTICES.txt for provenance and the recorded changes.
-/

namespace OAI

noncomputable section

namespace PiExponentSeshadri

namespace Geometry
open AlgebraicGeometry CategoryTheory TopologicalSpace
open PiExponentSeshadri.Frames
variable {X : Scheme.{0}}

theorem common_affine_frames (L M : LineBundle X) (x : X) :
    ∃ U : X.affineOpens, x ∈ U.1 ∧
      Nonempty (L.sheaf.restrict U.1.ι ≅ structureSheaf U.1.toScheme) ∧
      Nonempty (M.sheaf.restrict U.1.ι ≅ structureSheaf U.1.toScheme) := by
  obtain ⟨U, hxU, ⟨e⟩⟩ := L.locallyRankOne x
  obtain ⟨V, hxV, ⟨d⟩⟩ := M.locallyRankOne x
  obtain ⟨W, hW, hxW, hWUV⟩ := exists_isAffineOpen_mem_and_subset
    (show x ∈ U ⊓ V from ⟨hxU, hxV⟩)
  exact ⟨⟨W, hW⟩, hxW,
    ⟨restrictOpenFrame (fun _ hx => (hWUV hx).1) e⟩,
    ⟨restrictOpenFrame (fun _ hx => (hWUV hx).2) d⟩⟩

def LineBundle.tensor (L M : LineBundle X) : LineBundle X where
  sheaf := moduleTensor X L.sheaf M.sheaf
  locallyRankOne x := by
    obtain ⟨U, hx, ⟨e⟩, ⟨d⟩⟩ := common_affine_frames L M x
    exact ⟨U.1, hx, ⟨moduleTensorRestrict U.1 L.sheaf M.sheaf ≪≫
      moduleTensorIso e d ≪≫ moduleTensorUnit (structureSheaf U.1.toScheme)⟩⟩

end Geometry

namespace PullbackTensor
open AlgebraicGeometry CategoryTheory TopologicalSpace
open PiExponentSeshadri.Geometry PiExponentSeshadri.Frames
variable {X Y : Scheme.{0}} (f : X ⟶ Y)

instance line_isIso (L M : LineBundle Y) : IsIso (hom f L.sheaf M.sheaf) := by
  apply PiExponentSeshadri.SectionOpens.isIso_of_locally_isIso
  intro x
  obtain ⟨U, hx, ⟨e⟩, ⟨d⟩⟩ := common_affine_frames L M (f x)
  refine ⟨f ⁻¹ᵁ U.1, hx, ?_⟩
  have := framed_isIso (f ∣_ U.1) _ _ e d
  have : IsIso (moduleTensorMap ((OpenBaseChange.leftSquare f U.1).hom.app L.sheaf)
      ((OpenBaseChange.leftSquare f U.1).hom.app M.sheaf)) := by
    change IsIso (moduleTensorIso ((OpenBaseChange.leftSquare f U.1).app L.sheaf)
      ((OpenBaseChange.leftSquare f U.1).app M.sheaf)).hom
    infer_instance
  have h := restrict_compatibility f U.1 L.sheaf M.sheaf
  have : IsIso ((OpenBaseChange.leftSquare f U.1).hom.app (moduleTensor Y L.sheaf M.sheaf) ≫
      (Scheme.Modules.restrictFunctor (f ⁻¹ᵁ U.1).ι).map (hom f L.sheaf M.sheaf) ≫
      (moduleTensorRestrict (f ⁻¹ᵁ U.1) ((Scheme.Modules.pullback f).obj L.sheaf)
        ((Scheme.Modules.pullback f).obj M.sheaf)).hom) := by rw [h]; infer_instance
  have hi : IsIso ((Scheme.Modules.restrictFunctor (f ⁻¹ᵁ U.1).ι).map (hom f L.sheaf M.sheaf) ≫
      (moduleTensorRestrict (f ⁻¹ᵁ U.1) ((Scheme.Modules.pullback f).obj L.sheaf)
        ((Scheme.Modules.pullback f).obj M.sheaf)).hom) :=
    (isIso_comp_left_iff ((OpenBaseChange.leftSquare f U.1).hom.app
      (moduleTensor Y L.sheaf M.sheaf)) _).mp inferInstance
  exact (isIso_comp_right_iff _ _).mp hi

def iso (L M : LineBundle Y) :
    (Scheme.Modules.pullback f).obj (L.tensor M).sheaf ≅
      ((L.pullback f).tensor (M.pullback f)).sheaf :=
  @asIso _ _ _ _ (hom f L.sheaf M.sheaf) (line_isIso f L M)

end PullbackTensor

end PiExponentSeshadri

end

end OAI
end Source0394

-- Source: OAI/NumberTheory/PiExponent/Approximation/TensorSectionOpen.lean
section Source0395
/-
Modification notice for the LogTwo project.
Derived from openai/math (Apache-2.0), revision adc7f1241b42e322a6451854ab7e4b4c146bf78a.
Original source: lean/OAI/NumberTheory/PiExponent/Approximation/TensorSectionOpen.lean
Changes: Convert module/import declarations to the Lean 4.34 public module format.
See ../THIRD_PARTY_NOTICES.txt for provenance and the recorded changes.
-/

namespace OAI

noncomputable section

namespace PiExponentSeshadri

namespace Geometry
open AlgebraicGeometry CategoryTheory
open PiExponentSeshadri.Frames
variable {X : Scheme.{0}}
def tensorFrame (L M : LineBundle X) (U : X.Opens)
    (e : L.sheaf.restrict U.ι ≅ O U.toScheme)
    (f : M.sheaf.restrict U.ι ≅ O U.toScheme) :
    (L.tensor M).sheaf.restrict U.ι ≅ O U.toScheme :=
  moduleTensorRestrict U L.sheaf M.sheaf ≪≫ moduleTensorIso e f ≪≫
    moduleTensorUnit (O U.toScheme)

end Geometry

namespace TensorPure

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite
open PiExponentSeshadri.Geometry PiExponentSeshadri.Frames PiExponentSeshadri.SectionOpens
variable {X : Scheme.{0}}

def tensorSection {M N : X.Modules} (s : O X ⟶ M) (t : O X ⟶ N) :
    O X ⟶ moduleTensor X M N :=
  (moduleTensorUnit (O X)).inv ≫ moduleTensorMap s t

lemma section_apply {M N : X.Modules} (s : O X ⟶ M) (t : O X ⟶ N) (U : X.Opens) :
    (tensorSection s t).app U (1 : Γ(X,U)) = pure M N U (s.app U (1 : Γ(X,U))) (t.app U (1 : Γ(X,U))) := by
  have h : (moduleTensorUnit (O X)).inv.app U (1 : Γ(X,U)) =
      pure (O X) (O X) U (1 : Γ(X,U)) (1 : Γ(X,U)) := by
    have he := unit_pure (O X) U (1 : Γ(X,U)) (1 : Γ(X,U))
    have he : (moduleTensorUnit (O X)).hom.app U (pure (O X) (O X) U (1 : Γ(X,U)) (1 : Γ(X,U))) = (1 : Γ(X,U)) := by
      simp only [O, structureSheaf] at he
      exact he.trans (by change (1 : Γ(X,U)) * 1 = 1; exact one_mul _)
    have hi := congrArg ((moduleTensorUnit (O X)).inv.app U) he
    change ((moduleTensorUnit (O X)).hom ≫ (moduleTensorUnit (O X)).inv).app U
      (pure (O X) (O X) U (1 : Γ(X,U)) (1 : Γ(X,U))) = _ at hi
    rw [Iso.hom_inv_id] at hi
    exact hi.symm
  change (moduleTensorMap s t).app U ((moduleTensorUnit (O X)).inv.app U (1 : Γ(X,U))) = _
  rw [h]
  exact map_pure s t U (1 : Γ(X,U)) (1 : Γ(X,U))

lemma framed_pure {M N : X.Modules} (e : M ≅ O X) (d : N ≅ O X) (U : X.Opens)
    (m : M.val.obj (op U)) (n : N.val.obj (op U)) :
    (moduleTensorIso e d ≪≫ moduleTensorUnit (O X)).hom.app U (pure M N U m n) =
      (show Γ(X,U) from e.hom.app U m) * (show Γ(X,U) from d.hom.app U n) := by
  change (moduleTensorUnit (O X)).hom.app U ((moduleTensorMap e.hom d.hom).app U
    (pure M N U m n)) = _
  exact (congrArg ((moduleTensorUnit (O X)).hom.app U) (map_pure e.hom d.hom U m n)).trans
    (unit_pure (O X) U _ _)

lemma local_framed_pure (L M : LineBundle X) (U : X.Opens)
    (e : L.sheaf.restrict U.ι ≅ O U.toScheme) (d : M.sheaf.restrict U.ι ≅ O U.toScheme)
    (V : U.toScheme.Opens) (m : L.sheaf.val.obj (op (U.ι ''ᵁ V)))
    (n : M.sheaf.val.obj (op (U.ι ''ᵁ V))) :
    (tensorFrame L M U e d).hom.app V (pure L.sheaf M.sheaf (U.ι ''ᵁ V) m n) =
      (show Γ(U.toScheme,V) from e.hom.app V m) * (show Γ(U.toScheme,V) from d.hom.app V n) := by
  change (moduleTensorIso e d ≪≫ moduleTensorUnit (O U.toScheme)).hom.app V
    ((moduleTensorRestrict U L.sheaf M.sheaf).hom.app V
      (pure L.sheaf M.sheaf (U.ι ''ᵁ V) m n)) = _
  exact (congrArg ((moduleTensorIso e d ≪≫ moduleTensorUnit (O U.toScheme)).hom.app V)
    (restrict_pure U L.sheaf M.sheaf V m n)).trans (framed_pure e d V m n)

lemma local_section_coefficient (L M : LineBundle X) (U : X.Opens)
    (e : L.sheaf.restrict U.ι ≅ O U.toScheme) (d : M.sheaf.restrict U.ι ≅ O U.toScheme)
    (s : O X ⟶ L.sheaf) (t : O X ⟶ M.sheaf) :
    coefficient (tensorFrame L M U e d) (restrictSection U.ι (tensorSection s t)) =
      coefficient e (restrictSection U.ι s) * coefficient d (restrictSection U.ι t) := by
  change (tensorFrame L M U e d).hom.app ⊤
    ((tensorSection s t).app (U.ι ''ᵁ ⊤) ((U.ι.appIso ⊤).inv (1 : Γ(U.toScheme,⊤)))) =
    (show Γ(U.toScheme,⊤) from e.hom.app ⊤ (s.app (U.ι ''ᵁ ⊤)
      ((U.ι.appIso ⊤).inv (1 : Γ(U.toScheme,⊤))))) *
    (show Γ(U.toScheme,⊤) from d.hom.app ⊤ (t.app (U.ι ''ᵁ ⊤)
      ((U.ι.appIso ⊤).inv (1 : Γ(U.toScheme,⊤)))))
  rw [map_one]
  exact (congrArg ((tensorFrame L M U e d).hom.app ⊤) (section_apply s t _)).trans
    (local_framed_pure L M U e d ⊤ _ _)

lemma section_open (L M : LineBundle X) (s : O X ⟶ L.sheaf) (t : O X ⟶ M.sheaf) :
    isoOpen (tensorSection s t) = isoOpen s ⊓ isoOpen t := by
  apply SetLike.coe_injective
  ext x
  obtain ⟨U,hx,⟨e⟩,⟨d⟩⟩ := common_affine_frames L M x
  have h : U.1.ι ⁻¹ᵁ isoOpen (tensorSection s t) =
      U.1.ι ⁻¹ᵁ (isoOpen s ⊓ isoOpen t) := by
    calc
      _ = U.1.toScheme.basicOpen (coefficient (tensorFrame L M U.1 e d)
          (restrictSection U.1.ι (tensorSection s t))) :=
        preimage_isoOpen (tensorSection s t) U.1.ι (tensorFrame L M U.1 e d)
      _ = U.1.toScheme.basicOpen (coefficient e (restrictSection U.1.ι s) *
          coefficient d (restrictSection U.1.ι t)) :=
        congrArg U.1.toScheme.basicOpen (local_section_coefficient L M U.1 e d s t)
      _ = U.1.toScheme.basicOpen (coefficient e (restrictSection U.1.ι s)) ⊓
          U.1.toScheme.basicOpen (coefficient d (restrictSection U.1.ι t)) :=
        U.1.toScheme.basicOpen_mul _ _
      _ = _ := congrArg₂ (· ⊓ ·) (preimage_isoOpen s U.1.ι e).symm
        (preimage_isoOpen t U.1.ι d).symm
  exact SetLike.ext_iff.mp h ⟨x,hx⟩

end TensorPure

end PiExponentSeshadri

end

end OAI
end Source0395

-- Source: OAI/NumberTheory/PiExponent/Ampleness/AmpleFromCover.lean
section Source0396
/-
Modification notice for the LogTwo project.
Derived from openai/math (Apache-2.0), revision adc7f1241b42e322a6451854ab7e4b4c146bf78a.
Original source: lean/OAI/NumberTheory/PiExponent/Ampleness/AmpleFromCover.lean
Changes: Convert module/import declarations to the Lean 4.34 public module format.
See ../THIRD_PARTY_NOTICES.txt for provenance and the recorded changes.
-/

namespace OAI

namespace PiExponentSeshadri.Geometry
noncomputable section
open AlgebraicGeometry CategoryTheory TopologicalSpace
open PiExponentSeshadri.Frames PiExponentSeshadri.Projective PiExponentSeshadri.TensorPure
variable {X : Scheme.{0}}

theorem LineBundle.section_basicOpen [IsIntegral X] [CompactSpace X]
    (L : LineBundle X) (s : O X ⟶ L.sheaf)
    (hne : (sectionOpen X s : Set X).Nonempty) (f : Γ(X,sectionOpen X s)) :
    ∃ n : ℕ, 0 < n ∧ ∃ t : O X ⟶ (L.pow n).sheaf,
      sectionOpen X t = X.basicOpen f := by
  let U := sectionOpen X s
  obtain ⟨N,hN⟩ := L.power_extension_ratio s hne (U.topIso.inv f)
  let n := max N 1
  have hn : 0 < n := lt_of_lt_of_le (by decide : 0<1) (le_max_right N 1)
  obtain ⟨t,ht⟩ := hN n (le_max_left N 1)
  let q := tensorSection s t
  have hsub : SectionOpens.isoOpen q ≤ U := by
    exact (section_open L (L.pow n) s t).le.trans inf_le_left
  have hi : IsIso (restrictSection U.ι (powerSection s n)) :=
    isIso_restricted_section _ _ (L.sectionOpen_power s hn)
  let e : (L.pow n).sheaf.restrict U.ι ≅ O U.toScheme :=
    (asIso (restrictSection U.ι (powerSection s n))).symm
  have hcoef : coefficient e (restrictSection U.ι t) = U.topIso.inv f := by
    apply coefficient_ratio e (powerSection s n) t
    · exact coefficient_frame e
    · exact ht
  have hnorm : coefficient (sectionFrame s) (restrictSection U.ι s) = 1 :=
    sectionFrame_normalized s
  have hpre : U.ι ⁻¹ᵁ SectionOpens.isoOpen q = U.toScheme.basicOpen (U.topIso.inv f) := by
    refine (preimage_isoOpen q U.ι (tensorFrame L (L.pow n) U (sectionFrame s) e)).trans ?_
    apply congrArg U.toScheme.basicOpen
    exact (local_section_coefficient L (L.pow n) U (sectionFrame s) e s t).trans
      ((congrArg₂ (fun (a b : Γ(U.toScheme, ⊤)) => a * b) hnorm hcoef).trans
        (one_mul _))
  refine ⟨n+1,by omega,q,?_⟩
  change SectionOpens.isoOpen q = _
  calc
    _ = U.ι ''ᵁ (U.ι ⁻¹ᵁ SectionOpens.isoOpen q) := by
      rw [Scheme.Hom.image_preimage_eq_opensRange_inf,Scheme.Opens.opensRange_ι,inf_eq_right.mpr hsub]
    _ = _ := by rw [hpre,U.ι_image_basicOpen_topIso_inv]

theorem LineBundle.ample_of_affine_section_cover [IsIntegral X] [CompactSpace X]
    (L : LineBundle X) {ι : Type*} (s : ι → (O X ⟶ L.sheaf))
    (hc : (⨆ i, sectionOpen X (s i)) = ⊤)
    (ha : ∀ i, IsAffineOpen (sectionOpen X (s i))) : L.IsAmple := by
  intro x V hx
  have hc' : x ∈ ⨆ i, sectionOpen X (s i) := by rw [hc]; trivial
  obtain ⟨i,hi⟩ := Opens.mem_iSup.mp hc'
  obtain ⟨f,hf,hxf⟩ := (ha i).exists_basicOpen_le ⟨x,hx⟩ hi
  obtain ⟨n,hn,t,ht⟩ := L.section_basicOpen (s i) ⟨x,hi⟩ f
  exact ⟨n,hn,t,ht.symm ▸ hxf,ht.le.trans hf,ht.symm ▸ (ha i).basicOpen f⟩

end
end PiExponentSeshadri.Geometry

end OAI
end Source0396

-- Source: OAI/NumberTheory/PiExponent/Ampleness/AmpleIso.lean
section Source0397
-- Modified in this edition: unused plain lemmas removed; see reduction.json.
/-
Modification notice for the LogTwo project.
Derived from openai/math (Apache-2.0), revision adc7f1241b42e322a6451854ab7e4b4c146bf78a.
Original source: lean/OAI/NumberTheory/PiExponent/Ampleness/AmpleIso.lean
Changes: Convert module/import declarations to the Lean 4.34 public module format.
See ../THIRD_PARTY_NOTICES.txt for provenance and the recorded changes.
-/

namespace OAI

namespace PiExponent.AmpleIso

noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace
open PiExponentSeshadri.Geometry

variable {X : Scheme}

theorem sectionOpen_postcomp_iso {M N : X.Modules}
    (s : GlobalSections X M) (e : M ≅ N) :
    sectionOpen X (s ≫ e.hom) = sectionOpen X s := by
  simp only [sectionOpen, Functor.map_comp, isIso_comp_right_iff]

theorem isAmple_of_sheaf_iso (L M : LineBundle X) (e : L.sheaf ≅ M.sheaf)
    (hL : L.IsAmple) : M.IsAmple := by
  intro x V hx
  obtain ⟨n, hn, s, hsx, hsV, hsa⟩ := hL x V hx
  let ePow : modulePow X L.sheaf n ≅ modulePow X M.sheaf n :=
    (modulePowFunctor n).mapIso e
  refine ⟨n, hn, s ≫ ePow.hom, ?_, ?_, ?_⟩
  · rwa [sectionOpen_postcomp_iso]
  · rwa [sectionOpen_postcomp_iso]
  · rwa [sectionOpen_postcomp_iso]

end
end PiExponent.AmpleIso

end OAI
end Source0397

-- Source: OAI/NumberTheory/PiExponent/Approximation/SectionPullback.lean
section Source0398
/-
Modification notice for the LogTwo project.
Derived from openai/math (Apache-2.0), revision adc7f1241b42e322a6451854ab7e4b4c146bf78a.
Original source: lean/OAI/NumberTheory/PiExponent/Approximation/SectionPullback.lean
Changes: Convert module/import declarations to the Lean 4.34 public module format.
See ../THIRD_PARTY_NOTICES.txt for provenance and the recorded changes.
-/

namespace OAI

namespace PiExponentSeshadri.Geometry
noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace
open PiExponentSeshadri.Frames
variable {X Y Z : Scheme.{0}}

lemma pullback_endValue (f : Y ⟶ X) (a : O X ⟶ O X) :
    endValue ((pullbackUnitIso f).inv ≫ (Scheme.Modules.pullback f).map a ≫
      (pullbackUnitIso f).hom) = f.appTop (endValue a) := by
  let u := SheafOfModules.unitToPushforwardObjUnit f.toRingCatSheafHom
  let b := (pullbackUnitIso f).inv ≫ (Scheme.Modules.pullback f).map a ≫
      (pullbackUnitIso f).hom
  have he : a ≫ u = u ≫ (Scheme.Modules.pushforward f).map b := by
    have hn := (Scheme.Modules.pullbackPushforwardAdjunction f).homEquiv_naturality_left
      a (pullbackUnitIso f).hom
    have hr := (Scheme.Modules.pullbackPushforwardAdjunction f).homEquiv_naturality_right
      (pullbackUnitIso f).hom b
    rw [pullbackUnit_adjunction] at hn hr
    have hcomp : (pullbackUnitIso f).hom ≫ b =
        (Scheme.Modules.pullback f).map a ≫ (pullbackUnitIso f).hom := by simp [b]
    rw [hcomp] at hr
    exact hn.symm.trans hr
  have hev := congrArg (fun t : O X ⟶ (Scheme.Modules.pushforward f).obj (O Y) =>
      t.app ⊤ (1 : Γ(X,⊤))) he
  change f.app ⊤ (a.app ⊤ (1 : Γ(X,⊤))) = b.app (f ⁻¹ᵁ ⊤) (f.app ⊤ 1) at hev
  have hfOne : f.app ⊤ (1 : Γ(X,⊤)) = (1 : Γ(Y,f ⁻¹ᵁ ⊤)) := map_one (f.app ⊤).hom
  rw [hfOne] at hev
  exact hev.symm

lemma coefficient_pullback (f : Y ⟶ X) {M : X.Modules}
    (e : M ≅ O X) (s : O X ⟶ M) :
    coefficient (pullbackFrame f e) (pullbackSection f s) =
      f.appTop (coefficient e s) := by
  unfold coefficient pullbackFrame pullbackSection
  simp only [Iso.trans_hom, Functor.mapIso_hom, Category.assoc]
  rw [← Functor.map_comp_assoc]
  exact pullback_endValue f (s ≫ e.hom)

end
end PiExponentSeshadri.Geometry

end OAI
end Source0398

-- Source: OAI/NumberTheory/PiExponent/Approximation/FramedPullback.lean
section Source0399
/-
Modification notice for the LogTwo project.
Derived from openai/math (Apache-2.0), revision adc7f1241b42e322a6451854ab7e4b4c146bf78a.
Original source: lean/OAI/NumberTheory/PiExponent/Approximation/FramedPullback.lean
Changes: Convert module/import declarations to the Lean 4.34 public module format.
See ../THIRD_PARTY_NOTICES.txt for provenance and the recorded changes.
-/

namespace OAI

namespace PiExponentSeshadri.Geometry
noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace
open PiExponentSeshadri.Frames
variable {X Y : Scheme.{0}}

lemma endValue_conjugation (b : O Y ≅ O Y) (a : O Y ⟶ O Y) :
    endValue (b.hom ≫ a ≫ b.inv) = endValue a := by
  rw [endValue_comp, endValue_comp]
  have hb : endValue b.hom * endValue b.inv = 1 := by
    rw [← endValue_comp, b.hom_inv_id, endValue_id]
  calc
    endValue b.hom * (endValue a * endValue b.inv) =
      endValue a * (endValue b.hom * endValue b.inv) := by ring
    _ = endValue a := by rw [hb, mul_one]

lemma exists_frame_natIso (F G : X.Modules ⥤ Y.Modules) (v : F ≅ G)
    (uF : F.obj (O X) ≅ O Y) (uG : G.obj (O X) ≅ O Y)
    {M : X.Modules} (e : G.obj M ≅ O Y) (s : O X ⟶ M) :
    ∃ eF : F.obj M ≅ O Y,
      coefficient eF (uF.inv ≫ F.map s) = coefficient e (uG.inv ≫ G.map s) := by
  let b : O Y ≅ O Y := uF.symm ≪≫ v.app (O X) ≪≫ uG
  refine ⟨v.app M ≪≫ e ≪≫ b.symm, ?_⟩
  have h : (uF.inv ≫ F.map s) ≫ (v.app M).hom =
      b.hom ≫ (uG.inv ≫ G.map s) := by
    simp only [b, Iso.trans_hom, Iso.symm_hom, Category.assoc]
    simp only [Iso.hom_inv_id_assoc]
    exact congrArg (fun q => uF.inv ≫ q) (v.hom.naturality s)
  change endValue (((uF.inv ≫ F.map s) ≫ (v.app M).hom) ≫ e.hom ≫ b.inv) = _
  rw [h]
  change endValue (b.hom ≫ (uG.inv ≫ G.map s ≫ e.hom) ≫ b.inv) = _
  exact endValue_conjugation b _

def pullbackRestrictNatIso (f : Y ⟶ X) (U : X.Opens) :
    Scheme.Modules.pullback f ⋙ Scheme.Modules.restrictFunctor (f ⁻¹ᵁ U).ι ≅
      Scheme.Modules.restrictFunctor U.ι ⋙ Scheme.Modules.pullback (f ∣_ U) :=
  Functor.isoWhiskerLeft (Scheme.Modules.pullback f)
    (Scheme.Modules.restrictFunctorIsoPullback (f ⁻¹ᵁ U).ι) ≪≫
  Scheme.Modules.pullbackComp (f ⁻¹ᵁ U).ι f ≪≫
  Scheme.Modules.pullbackCongr (morphismRestrict_ι f U).symm ≪≫
  (Scheme.Modules.pullbackComp (f ∣_ U) U.ι).symm ≪≫
  Functor.isoWhiskerRight (Scheme.Modules.restrictFunctorIsoPullback U.ι).symm
    (Scheme.Modules.pullback (f ∣_ U))

theorem exists_restricted_pullback_frame (f : Y ⟶ X) (U : X.Opens)
    {M : X.Modules} (e : M.restrict U.ι ≅ O U.toScheme) (s : O X ⟶ M) :
    ∃ eF : ((Scheme.Modules.pullback f).obj M).restrict (f ⁻¹ᵁ U).ι ≅
        O (f ⁻¹ᵁ U).toScheme,
      coefficient eF (restrictSection (f ⁻¹ᵁ U).ι (pullbackSection f s)) =
        (f ∣_ U).appTop (coefficient e (restrictSection U.ι s)) := by
  let F : X.Modules ⥤ (f ⁻¹ᵁ U).toScheme.Modules :=
    Scheme.Modules.pullback f ⋙ Scheme.Modules.restrictFunctor (f ⁻¹ᵁ U).ι
  let G : X.Modules ⥤ (f ⁻¹ᵁ U).toScheme.Modules :=
    Scheme.Modules.restrictFunctor U.ι ⋙ Scheme.Modules.pullback (f ∣_ U)
  let uF : F.obj (O X) ≅ O (f ⁻¹ᵁ U).toScheme :=
    (Scheme.Modules.restrictFunctor (f ⁻¹ᵁ U).ι).mapIso (pullbackUnitIso f) ≪≫
      Scheme.Modules.restrictUnitIso (f ⁻¹ᵁ U).ι
  let uG : G.obj (O X) ≅ O (f ⁻¹ᵁ U).toScheme :=
    (Scheme.Modules.pullback (f ∣_ U)).mapIso (Scheme.Modules.restrictUnitIso U.ι) ≪≫
      pullbackUnitIso (f ∣_ U)
  obtain ⟨eF,he⟩ := exists_frame_natIso F G (pullbackRestrictNatIso f U) uF uG
    (pullbackFrame (f ∣_ U) e) s
  refine ⟨eF, ?_⟩
  have he' : coefficient eF (restrictSection (f ⁻¹ᵁ U).ι (pullbackSection f s)) =
      coefficient (pullbackFrame (f ∣_ U) e)
        (pullbackSection (f ∣_ U) (restrictSection U.ι s)) := by
    let P : X.Modules ⥤ Y.Modules := Scheme.Modules.pullback f
    let R : Y.Modules ⥤ (f ⁻¹ᵁ U).toScheme.Modules :=
      Scheme.Modules.restrictFunctor (f ⁻¹ᵁ U).ι
    let S : X.Modules ⥤ U.toScheme.Modules := Scheme.Modules.restrictFunctor U.ι
    let Q : U.toScheme.Modules ⥤ (f ⁻¹ᵁ U).toScheme.Modules :=
      Scheme.Modules.pullback (f ∣_ U)
    let p : P.obj (O X) ≅ O Y := pullbackUnitIso f
    let r : R.obj (O Y) ≅ O (f ⁻¹ᵁ U).toScheme :=
      Scheme.Modules.restrictUnitIso (f ⁻¹ᵁ U).ι
    let a : S.obj (O X) ≅ O U.toScheme := Scheme.Modules.restrictUnitIso U.ι
    let q : Q.obj (O U.toScheme) ≅ O (f ⁻¹ᵁ U).toScheme := pullbackUnitIso (f ∣_ U)
    have hl : restrictSection (f ⁻¹ᵁ U).ι (pullbackSection f s) = uF.inv ≫ F.map s := by
      simp only [restrictSection, pullbackSection]
      change r.inv ≫ R.map (p.inv ≫ P.map s) = (r.inv ≫ R.map p.inv) ≫ R.map (P.map s)
      exact (congrArg (fun k => r.inv ≫ k) (R.map_comp p.inv (P.map s))).trans
        (Category.assoc r.inv (R.map p.inv) (R.map (P.map s))).symm
    have hr : pullbackSection (f ∣_ U) (restrictSection U.ι s) = uG.inv ≫ G.map s := by
      change q.inv ≫ Q.map (a.inv ≫ S.map s) = (q.inv ≫ Q.map a.inv) ≫ Q.map (S.map s)
      exact (congrArg (fun k => q.inv ≫ k) (Q.map_comp a.inv (S.map s))).trans
        (Category.assoc q.inv (Q.map a.inv) (Q.map (S.map s))).symm
    exact (congrArg (coefficient eF) hl).trans
      (he.trans (congrArg (coefficient (pullbackFrame (f ∣_ U) e)) hr).symm)
  rw [he', coefficient_pullback]

end
end PiExponentSeshadri.Geometry

end OAI
end Source0399

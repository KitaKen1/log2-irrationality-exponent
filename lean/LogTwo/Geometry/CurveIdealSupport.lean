/-
Modification notice for the LogTwo project.
Adapted from openai/math (Apache-2.0), revision adc7f1241b42e322a6451854ab7e4b4c146bf78a.
Changes: Adapt generic-image and off-support ideal arguments to the project geometry.
See ../../../THIRD_PARTY_NOTICES.txt for provenance and the recorded changes.
-/

module

public import LogTwo.Geometry.NormalizationBranch
public import LogTwo.Geometry.JetCenterAt
public import LogTwo.Geometry.ContactFamilyAt

@[expose] public section

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

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
public import LogTwoCheckpoints.Part011
public import LogTwoCheckpoints.Part012
public import LogTwoCheckpoints.Part013
public import LogTwoCheckpoints.Part014
public import LogTwoCheckpoints.Part015
public import LogTwoCheckpoints.Part016
public import LogTwoCheckpoints.Part017
public import LogTwoCheckpoints.Part019
public import Mathlib.AlgebraicGeometry.FunctionField
public import Mathlib.AlgebraicGeometry.IdealSheaf.Functorial
public import Mathlib.AlgebraicGeometry.Modules.Tilde
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Basic
public import Mathlib.AlgebraicGeometry.Sites.SmallAffineZariski
public import Mathlib.Analysis.Complex.Polynomial.Basic
public import Mathlib.Data.Opposite
public import Mathlib.Data.SetLike.Basic
public import Mathlib.RingTheory.DiscreteValuationRing.Basic
public import Mathlib.RingTheory.MvPolynomial.Homogeneous
public import Mathlib.RingTheory.ReesAlgebra
@[expose] public section
set_option Elab.async false

-- Source: LogTwo/Geometry/CurveSectionDegree.lean
section Source0500
/-
Modification notice for the LogTwo project.
Adapted from openai/math (Apache-2.0), revision adc7f1241b42e322a6451854ab7e4b4c146bf78a.
Changes: Connect varying-center colength cycles and adapt the rational degree-cast calculation.
See ../THIRD_PARTY_NOTICES.txt for provenance and the recorded changes.
-/

/-! Identify the actual colength cycle with a section divisor, then obtain
its negative Euler degree for an invertible presentation of the pulled-back
ideal. The presentation is an explicit hypothesis; this module does not
construct a blowup or prove ampleness. -/
namespace LogTwo.Geometry.MatrixCompactification
open OAI PiExponent AlgebraicGeometry CategoryTheory TopologicalSpace
open PiExponentSeshadri.Geometry PiExponentSeshadri.Frames
open LogTwo.Interpolation LogTwo.Arithmetic
open CurveNormalizationModel CurvePlaceCenter CurveValuationCenter PlaceValuationRing
open SectionIdealBridge
noncomputable section
variable {m : ℕ} (w : Weights m)
variable {E : Type} [Field E] [Algebra ℂ E]
variable (f : E) (hf : Transcendental ℂ f)
variable [FiniteDimensional (IntermediateField.adjoin ℂ {f}) E]

/-- The generic-point morphism is dominant, so equality there determines
maps from the reduced normalization curve to a separated target. -/
theorem parameterCurveGenericPoint_isDominant :
    IsDominant (parameterCurveGenericPoint f hf) := by
  let X := parameterCurve f hf
  let q := X.fromSpecStalk (genericPoint X)
  have : IsDominant q := by
    constructor
    rw [denseRange_iff_closure_range]
    apply Set.eq_univ_of_univ_subset
    rw [← genericPoint_closure X]
    apply closure_mono
    rw [Set.singleton_subset_iff]
    exact ⟨IsLocalRing.closedPoint _, Scheme.fromSpecStalk_closedPoint⟩
  let e : Spec (CommRingCat.of E) ≅ Spec X.functionField :=
    Scheme.Spec.mapIso (parameterCurveFunctionFieldEquiv f hf).toCommRingCatIso.op
  change IsDominant (e.hom ≫ q)
  infer_instance

theorem curveMap_eq_of_generic (z : Fin (m+1) → E)
    (g : parameterCurve f hf ⟶ space w)
    (hgeneric : parameterCurveGenericPoint f hf ≫ g =
      Spec.map (CommRingCat.ofHom (MvPolynomial.aeval z).toRingHom) ≫ affineChart w) :
    g = curveMap w f hf z := by
  let := parameterCurveGenericPoint_isDominant f hf
  apply ext_of_isDominant (parameterCurveGenericPoint f hf)
  rw [hgeneric, curveMap_generic]

variable {K : ℕ}
variable (hfinite : ∀ t : E, Transcendental ℂ t →
  FiniteDimensional (IntermediateField.adjoin ℂ {t}) E)
variable (z : Fin (m+1) → E) (y : Fin K → ℂ) (c : Fin K → Fin m → ℂ)
variable (hz : ∃ i, Transcendental ℂ (z i))
variable {Y : Scheme.{0}} (π : Y ⟶ space w)
variable (J : LineBundle Y) (ι : J.sheaf ⟶ O Y)
variable (g : parameterCurve f hf ⟶ Y)
variable (hgeneric : parameterCurveGenericPoint f hf ≫ g ≫ π =
  Spec.map (CommRingCat.ofHom (MvPolynomial.aeval z).toRingHom) ≫ affineChart w)

include hz hgeneric in
theorem presented_curveIdeal_ne_bot (T : Fin m → ℕ) :
    (centerIdeal w y c T).comap (g ≫ π) ≠ ⊥ := by
  rw [curveMap_eq_of_generic w f hf z (g ≫ π) hgeneric]
  exact curveIdeal_ne_bot w f hf y c T z hz

theorem presentedDivisor_eq_curveColengthCycle (T : Fin m → ℕ)
    (hJ : PresentsPullbackIdeal (centerIdeal w y c T) π J ι) :
    idealDivisor f hf (centerIdeal w y c T) π J ι hJ g
      (presented_curveIdeal_ne_bot w f hf z y c hz π g hgeneric T) =
        curveColengthCycle w f hf hfinite z y c hz T := by
  ext p
  rw [idealDivisor_apply, curveColengthCycle_apply]
  have hi : localIdeal (centerIdeal w y c T) (centerMorphism f hf p ≫ g ≫ π) =
      curveLocalIdeal w f hf p y c z T := by
    unfold localIdeal curveLocalIdeal
    rw [Scheme.IdealSheafData.comap_comp,
      curveMap_eq_of_generic w f hf z (g ≫ π) hgeneric]
  rw [hi]

include hgeneric in
theorem euler_degree_eq_neg_curveColengthCycle_sum (T : Fin m → ℕ)
    (hJ : PresentsPullbackIdeal (centerIdeal w y c T) π J ι) :
    eulerCharacteristic (parameterCurveStructureMap f hf) 1 (J.pullback g).sheaf -
      eulerCharacteristic (parameterCurveStructureMap f hf) 1
        (structureSheaf (parameterCurve f hf)) =
      -(curveColengthCycle w f hf hfinite z y c hz T).sum (fun _ n => (n : ℤ)) := by
  have hd := degree_eq_neg_idealDivisor_sum f hf (centerIdeal w y c T) π J ι hJ g
    (presented_curveIdeal_ne_bot w f hf z y c hz π g hgeneric T)
  rw [presentedDivisor_eq_curveColengthCycle w f hf hfinite z y c hz π J ι g hgeneric T hJ] at hd
  exact hd

variable (hres : ∀ p : NormalizedPlace ℂ E,
  Algebra.IsIntegral ℂ (IsLocalRing.ResidueField (ring p)))
variable (hy : Function.Injective y) (hy0 : ∀ j, y j ≠ 0) (hK : 0 < K)

include hy hgeneric in
theorem euler_degree_eq_neg_contact_sum (F : ℚ) (hF : 1 / w.theta < F)
    (hJ : PresentsPullbackIdeal (centerIdeal w y c (truncationOrders w F)) π J ι) :
    ((eulerCharacteristic (parameterCurveStructureMap f hf) 1 (J.pullback g).sheaf -
      eulerCharacteristic (parameterCurveStructureMap f hf) 1
        (structureSheaf (parameterCurve f hf)) : ℤ) : ℚ) =
      -((scale w).radius : ℚ) * ∑ p ∈ ContactFamilyAt.places hfinite z y c hz,
        ContactFamilyAt.contact hres hfinite z y hy0 c hz hK (jetWeight w) p := by
  have hd := euler_degree_eq_neg_curveColengthCycle_sum w f hf hfinite z y c hz π J ι g
    hgeneric (truncationOrders w F) hJ
  have hdq : ((eulerCharacteristic (parameterCurveStructureMap f hf) 1 (J.pullback g).sheaf -
      eulerCharacteristic (parameterCurveStructureMap f hf) 1
        (structureSheaf (parameterCurve f hf)) : ℤ) : ℚ) =
      -(curveColengthCycle w f hf hfinite z y c hz (truncationOrders w F)).sum
        (fun _ n => (n : ℚ)) := by
    simpa only [Int.cast_neg, Finsupp.sum, Int.cast_sum, Int.cast_natCast] using
      congrArg (fun a : ℤ => (a : ℚ)) hd
  rw [curveColengthCycle_sum_eq_contact w f hf hfinite z y c hz hres hy hy0 hK F hF] at hdq
  simpa only [neg_mul] using hdq

end
end LogTwo.Geometry.MatrixCompactification
end Source0500

-- Source: OAI/NumberTheory/PiExponent/Ampleness/ReesPrincipalLift.lean
section Source0501
/-
Modification notice for the LogTwo project.
Derived from openai/math (Apache-2.0), revision adc7f1241b42e322a6451854ab7e4b4c146bf78a.
Original source: lean/OAI/NumberTheory/PiExponent/Ampleness/ReesPrincipalLift.lean
Changes: Convert module/import declarations to the Lean 4.34 public module format.
See ../THIRD_PARTY_NOTICES.txt for provenance and the recorded changes.
-/

namespace OAI

noncomputable section

namespace PiExponentSeshadri.BlowupLift
universe u v
variable {R : Type u} [CommRing R] (I : Ideal R)
variable {S : Type v} [CommRing S] (f : R →+* S) (r : S)
variable (hI : I.map f = Ideal.span {r}) (hr : IsLeftRegular r)

def coefficient (a : I) : S :=
  Classical.choose ((Ideal.mem_span_singleton.mp
    (show f a.val ∈ Ideal.span {r} from hI ▸ Ideal.mem_map_of_mem f a.property)))

lemma mul_coefficient (a : I) : r * coefficient I f r hI a = f a.val := by
  exact (Classical.choose_spec ((Ideal.mem_span_singleton.mp
    (show f a.val ∈ Ideal.span {r} from hI ▸ Ideal.mem_map_of_mem f a.property)))).symm

include hr in

lemma coefficients_span : Ideal.span (Set.range (coefficient I f r hI)) = ⊤ := by
  let K : Ideal S := Ideal.span (Set.range (coefficient I f r hI))
  have hmap : I.map f ≤ Submodule.map (LinearMap.mulLeft S r) K := by
    rw [Ideal.map_le_iff_le_comap]
    intro a ha
    change f a ∈ Submodule.map (LinearMap.mulLeft S r) K
    exact ⟨coefficient I f r hI ⟨a, ha⟩,
      Ideal.subset_span (Set.mem_range_self _), mul_coefficient I f r hI ⟨a, ha⟩⟩
  have hmem : r ∈ Submodule.map (LinearMap.mulLeft S r) K := by
    apply hmap
    rw [hI]
    exact Ideal.subset_span (Set.mem_singleton r)
  obtain ⟨s, hs, hrs⟩ := hmem
  have hs1 : s = 1 := hr (by simpa using hrs)
  refine Ideal.eq_top_of_isUnit_mem (I := K) ?_ isUnit_one
  exact hs1 ▸ hs

end PiExponentSeshadri.BlowupLift

namespace PiExponentSeshadri.ReesGrading

section
open Polynomial
universe u v
variable {R : Type u} [CommRing R] (I : Ideal R)
variable {S : Type v} [CommRing S] (f : R →+* S) (r : S)
variable (hI : I.map f = Ideal.span {r}) (hr : IsRegular r)

def principalToLocalization : reesAlgebra I →+* Localization.Away r :=
  (Polynomial.eval₂RingHom ((algebraMap S (Localization.Away r)).comp f)
    (IsLocalization.Away.invSelf r)).comp (reesAlgebra I).val.toRingHom

lemma principalToLocalization_base (s : R) :
    principalToLocalization I f r (algebraMap R (reesAlgebra I) s) =
      algebraMap S (Localization.Away r) (f s) := by
  simp [principalToLocalization]

lemma principalToLocalization_generator (a : I) :
    principalToLocalization I f r (generator I a) =
      algebraMap S (Localization.Away r) (BlowupLift.coefficient I f r hI a) := by
  change (Polynomial.eval₂RingHom ((algebraMap S (Localization.Away r)).comp f)
    (IsLocalization.Away.invSelf r)) (monomial 1 a.val) = _
  simp only [coe_eval₂RingHom, eval₂_monomial, RingHom.comp_apply, pow_one]
  rw [← BlowupLift.mul_coefficient I f r hI a, map_mul]
  calc _ = (algebraMap S (Localization.Away r) r * IsLocalization.Away.invSelf r) *
      algebraMap S (Localization.Away r) (BlowupLift.coefficient I f r hI a) := by ring
       _ = _ := by rw [IsLocalization.Away.mul_invSelf, one_mul]

include hI in
lemma principalToLocalization_range (p : reesAlgebra I) :
    ∃ s : S, algebraMap S (Localization.Away r) s = principalToLocalization I f r p := by
  have hp : p ∈ Algebra.adjoin R (Set.range (generator I)) := by
    rw [generators_adjoin]
    trivial
  induction hp using Algebra.adjoin_induction with
  | mem p hp =>
    obtain ⟨a, rfl⟩ := hp
    exact ⟨BlowupLift.coefficient I f r hI a, (principalToLocalization_generator I f r hI a).symm⟩
  | algebraMap s => exact ⟨f s, (principalToLocalization_base I f r s).symm⟩
  | add p q _ _ hp hq =>
    obtain ⟨s, hs⟩ := hp
    obtain ⟨t, ht⟩ := hq
    exact ⟨s+t, by rw [map_add, hs, ht, map_add]⟩
  | mul p q _ _ hp hq =>
    obtain ⟨s, hs⟩ := hp
    obtain ⟨t, ht⟩ := hq
    exact ⟨s*t, by rw [map_mul, hs, ht, map_mul]⟩

include hr in
lemma principalLocalization_injective : Function.Injective (algebraMap S (Localization.Away r)) :=
  IsLocalization.injective _ (Submonoid.powers_le.mpr (isRegular_iff_mem_nonZeroDivisors.mp hr))

def principalMap : reesAlgebra I →+* S where
  toFun p := Classical.choose (principalToLocalization_range I f r hI p)
  map_zero' := principalLocalization_injective r hr (by
    rw [Classical.choose_spec (principalToLocalization_range I f r hI 0), map_zero, map_zero])
  map_one' := principalLocalization_injective r hr (by
    rw [Classical.choose_spec (principalToLocalization_range I f r hI 1), map_one, map_one])
  map_add' p q := principalLocalization_injective r hr (by
    rw [Classical.choose_spec (principalToLocalization_range I f r hI (p+q)), map_add,
      map_add, Classical.choose_spec (principalToLocalization_range I f r hI p),
      Classical.choose_spec (principalToLocalization_range I f r hI q)])
  map_mul' p q := principalLocalization_injective r hr (by
    rw [Classical.choose_spec (principalToLocalization_range I f r hI (p*q)), map_mul,
      map_mul, Classical.choose_spec (principalToLocalization_range I f r hI p),
      Classical.choose_spec (principalToLocalization_range I f r hI q)])

lemma principalMap_spec (p : reesAlgebra I) :
    algebraMap S (Localization.Away r) (principalMap I f r hI hr p) =
      principalToLocalization I f r p :=
  Classical.choose_spec (principalToLocalization_range I f r hI p)

lemma principalMap_base (s : R) :
    principalMap I f r hI hr (algebraMap R (reesAlgebra I) s) = f s := by
  apply principalLocalization_injective r hr
  rw [principalMap_spec, principalToLocalization_base]

lemma principalMap_generator (a : I) :
    principalMap I f r hI hr (generator I a) = BlowupLift.coefficient I f r hI a := by
  apply principalLocalization_injective r hr
  rw [principalMap_spec, principalToLocalization_generator]

lemma principalMap_irrelevant :
    (HomogeneousIdeal.irrelevant (piece I)).toIdeal.map (principalMap I f r hI hr) = ⊤ := by
  rw [eq_top_iff, ← BlowupLift.coefficients_span I f r hI hr.left]
  apply Ideal.span_le.mpr
  rintro s ⟨a, rfl⟩
  rw [← principalMap_generator I f r hI hr]
  apply Ideal.mem_map_of_mem
  exact HomogeneousIdeal.mem_irrelevant_of_mem (piece I) (by decide : 0 < (1 : ℕ))
    (generator_mem I a)

end

open CategoryTheory AlgebraicGeometry
universe u
variable {R : Type u} [CommRing R] (I : Ideal R)
variable (X : Scheme.{u}) (f : R →+* Γ(X, ⊤)) (r : Γ(X, ⊤))
variable (hI : I.map f = Ideal.span {r}) (hr : IsRegular r)

def principalScheme : X ⟶ affineBlowup I :=
  Proj.fromOfGlobalSections (piece I) (principalMap I f r hI hr)
    (principalMap_irrelevant I f r hI hr)

@[reassoc]
lemma principalScheme_projection :
    principalScheme I X f r hI hr ≫ projection I =
      X.toSpecΓ ≫ Spec.map (CommRingCat.ofHom f) := by
  let g : CommRingCat.of (piece I 0) ⟶ Γ(X, ⊤) :=
    CommRingCat.ofHom ((principalMap I f r hI hr).comp (algebraMap _ _))
  have hg : (zeroIso I).hom ≫ g = CommRingCat.ofHom f := by
    ext s
    exact principalMap_base I f r hI hr s
  have h : principalScheme I X f r hI hr ≫ Proj.toSpecZero (piece I) =
      X.toSpecΓ ≫ Spec.map g :=
    Proj.fromOfGlobalSections_toSpecZero (piece I) (principalMap I f r hI hr)
      (principalMap_irrelevant I f r hI hr)
  change principalScheme I X f r hI hr ≫
    (Proj.toSpecZero (piece I) ≫ Spec.map (zeroIso I).hom) = _
  calc
    _ = (principalScheme I X f r hI hr ≫ Proj.toSpecZero (piece I)) ≫
        Spec.map (zeroIso I).hom := (Category.assoc _ _ _).symm
    _ = (X.toSpecΓ ≫ Spec.map g) ≫ Spec.map (zeroIso I).hom :=
      congrArg (fun q : X ⟶ Spec (CommRingCat.of (piece I 0)) =>
        q ≫ Spec.map (zeroIso I).hom) h
    _ = X.toSpecΓ ≫ Spec.map ((zeroIso I).hom ≫ g) := by
      rw [Category.assoc, Spec.map_comp]
    _ = _ := congrArg (fun q : CommRingCat.of R ⟶ Γ(X, ⊤) =>
      X.toSpecΓ ≫ Spec.map q) hg

lemma principalScheme_preimage (a : I) :
    principalScheme I X f r hI hr ⁻¹ᵁ Proj.basicOpen (piece I) (generator I a) =
      X.basicOpen (BlowupLift.coefficient I f r hI a) := by
  erw [principalScheme, Proj.fromOfGlobalSections_preimage_basicOpen _ _ _
    (show 0 < (1 : ℕ) from Nat.zero_lt_one) (generator_mem I a), principalMap_generator]

end PiExponentSeshadri.ReesGrading

end

end OAI
end Source0501

-- Source: OAI/NumberTheory/PiExponent/Ampleness/BlowupSchemeExt.lean
section Source0502
/-
Modification notice for the LogTwo project.
Derived from openai/math (Apache-2.0), revision adc7f1241b42e322a6451854ab7e4b4c146bf78a.
Original source: lean/OAI/NumberTheory/PiExponent/Ampleness/BlowupSchemeExt.lean
Changes: Convert module/import declarations to the Lean 4.34 public module format.
See ../THIRD_PARTY_NOTICES.txt for provenance and the recorded changes.
-/

namespace OAI

noncomputable section

namespace PiExponentSeshadri

namespace SpecMaps
open CategoryTheory AlgebraicGeometry
universe u
variable {X Y : Scheme.{u}} {R S : CommRingCat.{u}}

def coordinate (f : X ⟶ Spec R) : R ⟶ Γ(X, ⊤) :=
  (Scheme.ΓSpecIso R).inv ≫ f.appTop

lemma coordinate_ext {f g : X ⟶ Spec R} (h : coordinate f = coordinate g) : f = g :=
  (ΓSpec.adjunction.homEquiv X (Opposite.op R)).symm.injective
    (Opposite.unop_injective h)

@[simp] lemma coordinate_comp (f : X ⟶ Y) (g : Y ⟶ Spec R) :
    coordinate (f ≫ g) = coordinate g ≫ f.appTop := by
  simp [coordinate]

@[simp] lemma coordinate_spec (f : R ⟶ S) : coordinate (Spec.map f) = f ≫ (Scheme.ΓSpecIso S).inv := by
  simp [coordinate]

@[simp] lemma coordinate_comp_spec (f : X ⟶ Spec S) (g : R ⟶ S) :
    coordinate (f ≫ Spec.map g) = g ≫ coordinate f := by
  simp [coordinate]

lemma factor (f : X ⟶ Spec R) :
    X.toSpecΓ ≫ Spec.map (coordinate f) = f := by
  unfold coordinate
  rw [Spec.map_comp, ← Scheme.toSpecΓ_naturality_assoc, toSpecΓ_SpecMap_ΓSpecIso_inv,
    Category.comp_id]

lemma preimage_basicOpen (f : X ⟶ Spec R) (a : R) :
    f ⁻¹ᵁ PrimeSpectrum.basicOpen a = X.basicOpen (coordinate f a) := by
  conv_lhs => rw [← factor f]
  erw [Scheme.Hom.comp_preimage, SpecMap_preimage_basicOpen]
  exact Scheme.toSpecΓ_preimage_basicOpen _ _

lemma isUnit_of_basicOpen_eq_top (a : Γ(X, ⊤)) (h : X.basicOpen a = ⊤) : IsUnit a := by
  apply RingedSpace.isUnit_of_isUnit_germ X.toLocallyRingedSpace.toRingedSpace ⊤ a
  intro x hx
  apply (Scheme.mem_basicOpen X a x hx).mp
  rw [h]
  trivial

lemma isUnit_coordinate_of_preimage_top (f : X ⟶ Spec R) (a : R)
    (h : f ⁻¹ᵁ PrimeSpectrum.basicOpen a = ⊤) : IsUnit (coordinate f a) := by
  apply isUnit_of_basicOpen_eq_top
  rwa [preimage_basicOpen] at h

lemma ideal_unit_generator (I : Ideal R) (f : X ⟶ Spec R)
    (hI : I.map (coordinate f).hom = ⊤) (x : X) :
    ∃ a : I, x ∈ f ⁻¹ᵁ PrimeSpectrum.basicOpen a.val := by
  by_contra! hn
  have hle : I ≤ (f x).asIdeal := by
    intro a ha
    exact not_not.mp (hn ⟨a, ha⟩)
  have hmap : I.map (coordinate f).hom ≤ (X.toSpecΓ x).asIdeal := by
    rw [Ideal.map_le_iff_le_comap]
    intro a ha
    have hm := hle ha
    rw [← factor f, Scheme.Hom.comp_apply, Spec.map_apply] at hm
    exact hm
  rw [hI] at hmap
  exact (X.toSpecΓ x).isPrime.ne_top (top_unique hmap)

end SpecMaps

namespace SchematicExt
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
universe u
variable {W X Y Z : Scheme.{u}}

lemma ext_of_ker_eq_bot_of_isSeparated {f g : X ⟶ Y}
    (s : Y ⟶ Z) [IsSeparated s] (h : f ≫ s = g ≫ s)
    (ι : W ⟶ X) (hι : ι.ker = ⊥) (hU : ι ≫ f = ι ≫ g) : f = g := by
  let X' : Over Z := Over.mk (f ≫ s)
  let Y' : Over Z := Over.mk s
  let U' : Over Z := Over.mk (ι ≫ f ≫ s)
  let f' : X' ⟶ Y' := Over.homMk f
  let g' : X' ⟶ Y' := Over.homMk g h.symm
  let ι' : U' ⟶ X' := Over.homMk ι
  have : IsSeparated Y'.hom := ‹_›
  let l : U' ⟶ equalizer f' g' := equalizer.lift ι' (by ext1; exact hU)
  have hl : l.left ≫ (equalizer.ι f' g').left = ι := by
    change (l ≫ equalizer.ι f' g').left = ι
    exact congrArg (fun k : U' ⟶ X' => k.left) (equalizer.lift_ι ι' _)
  have hk : (equalizer.ι f' g').left.ker = ⊥ := by
    apply bot_unique
    calc _ ≤ (l.left ≫ (equalizer.ι f' g').left).ker := l.left.le_ker_comp _
         _ = ⊥ := by rw [hl, hι]
  have : IsIso (equalizer.ι f' g').left := IsClosedImmersion.isIso_iff_ker_eq_bot.mpr hk
  rw [← cancel_epi (equalizer.ι f' g').left]
  exact congr($(equalizer.condition f' g').left)

lemma basicOpen_ker_eq_bot [IsAffine X] (r : Γ(X, ⊤)) (hr : IsRegular r) :
    (X.basicOpen r).ι.ker = ⊥ := by
  apply Scheme.IdealSheafData.ext_of_isAffine
  apply bot_unique
  apply ((X.basicOpen r).ι.ideal_ker_le ⟨⊤, isAffineOpen_top X⟩).trans
  apply le_of_eq
  rw [RingHom.ker_eq_bot_iff_eq_zero]
  intro x hx
  have hinj : Function.Injective (algebraMap Γ(X, ⊤) Γ(X.basicOpen r, ⊤)) :=
    IsLocalization.injective (Γ(X.basicOpen r, ⊤))
      (Submonoid.powers_le.mpr (isRegular_iff_mem_nonZeroDivisors.mp hr))
  apply hinj
  change (algebraMap Γ(X, ⊤) Γ(X.basicOpen r, ⊤)) x = 0 at hx
  simpa only [map_zero] using hx

end SchematicExt

end PiExponentSeshadri

end

end OAI
end Source0502

-- Source: OAI/NumberTheory/PiExponent/Ampleness/ReesUniversalUniqueness.lean
section Source0503
-- Modified in this edition: unused plain lemmas removed; see reduction.json.
/-
Modification notice for the LogTwo project.
Derived from openai/math (Apache-2.0), revision adc7f1241b42e322a6451854ab7e4b4c146bf78a.
Original source: lean/OAI/NumberTheory/PiExponent/Ampleness/ReesUniversalUniqueness.lean
Changes: Convert module/import declarations to the Lean 4.34 public module format.
See ../THIRD_PARTY_NOTICES.txt for provenance and the recorded changes.
-/

namespace OAI

noncomputable section

namespace PiExponentSeshadri.ReesGrading
open Polynomial HomogeneousLocalization
universe u v
variable {R : Type u} [CommRing R] (I : Ideal R) (a : I)
variable {B : Type v} [CommRing B] (f : R →+* B)

lemma base_pow_mul_mk (n : ℕ) (p : reesAlgebra I)
    (hp : p ∈ piece I (n • (1 : ℕ))) :
    chartBase I a (a.val ^ n) *
        HomogeneousLocalization.Away.mk (piece I) (generator_mem I a) n p hp =
      chartBase I a (evaluation I p) := by
  apply chartMap_injective I a
  rw [map_mul, chartMap_base, chartMap_base, chartMap_mk]
  exact IsLocalization.mk'_spec' (M := Submonoid.powers a.val)
    (Localization.Away a.val) (evaluation I p) ⟨a.val ^ n, n, rfl⟩

end PiExponentSeshadri.ReesGrading

namespace PiExponentSeshadri.ProjBase
open CategoryTheory AlgebraicGeometry TopologicalSpace
universe u
variable {σ : Type*} {A : Type u} [CommRing A] [SetLike σ A] [AddSubgroupClass σ A]
variable (𝒜 : ℕ → σ) [GradedRing 𝒜]

lemma basicOpenToSpec_eq (f : A) :
    Scheme.forgetToLocallyRingedSpace.map (Proj.basicOpenToSpec 𝒜 f) =
      ProjectiveSpectrum.Proj.toSpec 𝒜 f := by
  refine Eq.trans ?_ (ΓSpec.locallyRingedSpaceAdjunction.homEquiv_apply _ _ _).symm
  dsimp [Proj.basicOpenToSpec, Scheme.Opens.toSpecΓ]
  simp only [Category.assoc, ← Spec.map_comp]
  rfl

lemma basicOpenToSpec_mem (f : A) (x : Proj.basicOpen 𝒜 f)
    (z : HomogeneousLocalization.NumDenSameDeg 𝒜 (.powers f)) :
    HomogeneousLocalization.mk z ∈ ((Proj.basicOpenToSpec 𝒜 f) x).asIdeal ↔
      z.num.val ∈ x.val.asHomogeneousIdeal := by
  have he := congr($(basicOpenToSpec_eq 𝒜 f).base x)
  change (Proj.basicOpenToSpec 𝒜 f) x = (ProjectiveSpectrum.Proj.toSpec 𝒜 f).base x at he
  rw [he]
  exact ProjectiveSpectrum.Proj.mk_mem_toSpec_base_apply 𝒜 x z

lemma toSpecZero_mem (x : Proj 𝒜) (a : 𝒜 0) :
    a ∈ ((Proj.toSpecZero 𝒜) x).asIdeal ↔ a.val ∈ x.asHomogeneousIdeal := by
  simp only [Proj.toSpecZero, Scheme.Hom.comp_apply, Spec.map_apply]
  change HomogeneousLocalization.fromZeroRingHom 𝒜 (.powers (1 : A)) a ∈
    ((Proj.basicOpenToSpec 𝒜 1) _).asIdeal ↔ _
  rw [show HomogeneousLocalization.fromZeroRingHom 𝒜 (.powers (1 : A)) a =
    HomogeneousLocalization.mk ⟨0, a, 1, one_mem _⟩ from rfl]
  erw [basicOpenToSpec_mem]
  change a.val ∈ ((Proj.basicOpen 𝒜 (1 : A)).ι
    (((Proj 𝒜).isoOfEq (Proj.basicOpen_one 𝒜)).inv ((Proj 𝒜).topIso.inv x))).asHomogeneousIdeal ↔ _
  rw [← Scheme.Hom.comp_apply, Scheme.isoOfEq_inv_ι, ← Scheme.Hom.comp_apply]
  rw [Scheme.toIso_inv_ι]; rfl

end PiExponentSeshadri.ProjBase

namespace PiExponentSeshadri.ReesGrading
open Polynomial CategoryTheory AlgebraicGeometry TopologicalSpace
universe u
variable {R : Type u} [CommRing R] (I : Ideal R)

instance projection_separated : IsSeparated (projection I) := by
  have hP : IsSeparated (Proj.toSpecZero (piece I)) := inferInstance
  have hQ : IsSeparated (Spec.map (zeroIso I).hom) := inferInstance
  exact MorphismProperty.comp_mem (@IsSeparated) _ _ hP hQ

lemma projection_mem (x : affineBlowup I) (s : R) :
    s ∈ ((projection I) x).asIdeal ↔
      algebraMap R (reesAlgebra I) s ∈ x.asHomogeneousIdeal := by
  change zeroEquiv I s ∈ ((Proj.toSpecZero (piece I)) x).asIdeal ↔ _
  exact ProjBase.toSpecZero_mem (piece I) x (zeroEquiv I s)

lemma projection_preimage (s : R) :
    projection I ⁻¹ᵁ PrimeSpectrum.basicOpen s =
      Proj.basicOpen (piece I) (algebraMap R (reesAlgebra I) s) := by
  ext x
  exact not_congr (projection_mem I x s)

lemma base_generator_comm (a b : I) :
    algebraMap R (reesAlgebra I) a.val * generator I b =
      algebraMap R (reesAlgebra I) b.val * generator I a := by
  apply Subtype.ext
  change C a.val * monomial 1 b.val = C b.val * monomial 1 a.val
  simp only [C_mul_monomial, mul_comm a.val b.val]

lemma projection_preimage_le_chart (a : I) :
    projection I ⁻¹ᵁ PrimeSpectrum.basicOpen a.val ≤
      Proj.basicOpen (piece I) (generator I a) := by
  rw [projection_preimage]
  intro x hx
  obtain ⟨b, hb⟩ := Opens.mem_iSup.mp ((iSup_generator_basicOpen I).ge (Set.mem_univ x))
  have h : x ∈ Proj.basicOpen (piece I)
      (algebraMap R (reesAlgebra I) a.val * generator I b) := by
    rw [Proj.basicOpen_mul]
    exact ⟨hx, hb⟩
  rw [base_generator_comm, Proj.basicOpen_mul] at h
  exact h.2

lemma chartHom_ext {S : Type*} [CommRing S] (a : I)
    (g h : chart I a →+* S) (he : g.comp (chartBase I a) = h.comp (chartBase I a))
    (hr : IsRegular (g (chartBase I a a.val))) : g = h := by
  have hb (s : R) : g (chartBase I a s) = h (chartBase I a s) := RingHom.congr_fun he s
  ext x
  obtain ⟨n, p, hp, rfl⟩ := HomogeneousLocalization.Away.mk_surjective (piece I)
    (generator_mem I a) x
  apply (hr.pow n).left
  have h₁ := congrArg g (base_pow_mul_mk I a n p hp)
  have h₂ := congrArg h (base_pow_mul_mk I a n p hp)
  simpa only [map_mul, map_pow, hb] using h₁.trans ((hb ((evaluation I) p)).trans h₂.symm)

open SpecMaps

lemma chart_scheme_ext {Y : Scheme.{u}} (a : I)
    (g h : Y ⟶ Spec (CommRingCat.of (chart I a)))
    (he : g ≫ Spec.map (CommRingCat.ofHom (chartBase I a)) =
      h ≫ Spec.map (CommRingCat.ofHom (chartBase I a)))
    (hr : IsRegular (coordinate g (chartBase I a a.val))) : g = h := by
  apply coordinate_ext
  apply CommRingCat.hom_ext
  apply chartHom_ext I a _ _ _ hr
  have hc := congrArg coordinate he
  simp only [coordinate_comp_spec] at hc
  exact congrArg CommRingCat.Hom.hom hc

lemma ext_of_unit_generator {Y : Scheme.{u}} (a : I)
    (g h : Y ⟶ affineBlowup I) (f : Y ⟶ Spec (CommRingCat.of R))
    (hg : g ≫ projection I = f) (hh : h ≫ projection I = f)
    (hu : IsUnit (coordinate f a.val)) : g = h := by
  let hOpen : IsOpenImmersion ((chartCover I).f a) := (chartCover I).map_prop a
  have ht : f ⁻¹ᵁ PrimeSpectrum.basicOpen a.val = ⊤ := by
    rw [preimage_basicOpen, Scheme.basicOpen_of_isUnit _ hu]
  have hrange (k : Y ⟶ affineBlowup I) (hk : k ≫ projection I = f) :
      Set.range k ⊆ Set.range ((chartCover I).f a) := by
    rintro _ ⟨y, rfl⟩
    change k y ∈ ((chartCover I).f a).opensRange
    change k y ∈ (Proj.awayι (piece I) (generator I a) (generator_mem I a)
      (show 0 < (1 : ℕ) from Nat.zero_lt_one)).opensRange
    rw [Proj.opensRange_awayι]
    apply projection_preimage_le_chart I a
    change (projection I) (k y) ∈ PrimeSpectrum.basicOpen a.val
    rw [← Scheme.Hom.comp_apply, hk]
    exact ht.ge (Set.mem_univ y)
  let g' : Y ⟶ Spec (CommRingCat.of (chart I a)) := @IsOpenImmersion.lift _ _ _ ((chartCover I).f a) g hOpen (hrange g hg)
  let h' : Y ⟶ Spec (CommRingCat.of (chart I a)) := @IsOpenImmersion.lift _ _ _ ((chartCover I).f a) h hOpen (hrange h hh)
  have hg' : g' ≫ (chartCover I).f a = g :=
    @IsOpenImmersion.lift_fac _ _ _ ((chartCover I).f a) g hOpen (hrange g hg)
  have hh' : h' ≫ (chartCover I).f a = h :=
    @IsOpenImmersion.lift_fac _ _ _ ((chartCover I).f a) h hOpen (hrange h hh)
  have eg : g' ≫ Spec.map (CommRingCat.ofHom (chartBase I a)) = f := by
    exact (congrArg (fun q : Spec (CommRingCat.of (chart I a)) ⟶ Spec (CommRingCat.of R) =>
      g' ≫ q) (chartCover_projection I a).symm).trans
      ((Category.assoc _ _ _).symm.trans
        ((congrArg (fun q : Y ⟶ affineBlowup I => q ≫ projection I) hg').trans hg))
  have eh : h' ≫ Spec.map (CommRingCat.ofHom (chartBase I a)) = f := by
    exact (congrArg (fun q : Spec (CommRingCat.of (chart I a)) ⟶ Spec (CommRingCat.of R) =>
      h' ≫ q) (chartCover_projection I a).symm).trans
      ((Category.assoc _ _ _).symm.trans
        ((congrArg (fun q : Y ⟶ affineBlowup I => q ≫ projection I) hh').trans hh))
  have he : coordinate g' (chartBase I a a.val) = coordinate f a.val := by
    have hc := congrArg coordinate eg
    rw [coordinate_comp_spec] at hc
    exact ConcreteCategory.congr_hom hc a.val
  have hgh := chart_scheme_ext I a g' h' (eg.trans eh.symm) (by rw [he]; exact hu.isRegular)
  rw [← hg', ← hh', hgh]

lemma ext_on_generator_open {Y : Scheme.{u}} (a : I)
    (g h : Y ⟶ affineBlowup I) (f : Y ⟶ Spec (CommRingCat.of R))
    (hg : g ≫ projection I = f) (hh : h ≫ projection I = f) :
    (f ⁻¹ᵁ PrimeSpectrum.basicOpen a.val).ι ≫ g =
      (f ⁻¹ᵁ PrimeSpectrum.basicOpen a.val).ι ≫ h := by
  let U : Y.Opens := f ⁻¹ᵁ PrimeSpectrum.basicOpen a.val
  apply ext_of_unit_generator I a _ _ (U.ι ≫ f)
  · rw [Category.assoc, hg]
  · rw [Category.assoc, hh]
  · apply isUnit_coordinate_of_preimage_top
    erw [Scheme.Hom.comp_preimage]
    exact U.ι_preimage_self

lemma ext_of_unit_ideal {Y : Scheme.{u}}
    (g h : Y ⟶ affineBlowup I) (f : Y ⟶ Spec (CommRingCat.of R))
    (hg : g ≫ projection I = f) (hh : h ≫ projection I = f)
    (hI : I.map (coordinate f).hom = ⊤) : g = h := by
  refine Scheme.hom_ext_of_forall g h ?_
  intro y
  have ha : ∃ a : I, y ∈ f ⁻¹ᵁ PrimeSpectrum.basicOpen a.val :=
    ideal_unit_generator (R := CommRingCat.of R) I f hI y
  obtain ⟨a, hay⟩ := ha
  refine ⟨f ⁻¹ᵁ PrimeSpectrum.basicOpen a.val, hay, ?_⟩
  exact ext_on_generator_open I a g h f hg hh

lemma principal_basicOpen_unit_ideal {Y : Scheme.{u}} (f : Y ⟶ Spec (CommRingCat.of R))
    (r : Γ(Y, ⊤)) (hI : I.map (coordinate f).hom = Ideal.span {r}) :
    I.map (coordinate ((Y.basicOpen r).ι ≫ f)).hom = ⊤ := by
  rw [coordinate_comp]
  change I.map ((Y.basicOpen r).ι.appTop.hom.comp (coordinate f).hom) = ⊤
  rw [← Ideal.map_map, hI, Ideal.map_span, Set.image_singleton, Ideal.span_singleton_eq_top]
  apply isUnit_of_basicOpen_eq_top
  rw [← Scheme.preimage_basicOpen_top]
  exact (Y.basicOpen r).ι_preimage_self

lemma principal_unique {Y : Scheme.{u}} [IsAffine Y]
    (g h : Y ⟶ affineBlowup I) (f : Y ⟶ Spec (CommRingCat.of R))
    (hg : g ≫ projection I = f) (hh : h ≫ projection I = f)
    (r : Γ(Y, ⊤)) (hI : I.map (coordinate f).hom = Ideal.span {r}) (hr : IsRegular r) :
    g = h := by
  apply SchematicExt.ext_of_ker_eq_bot_of_isSeparated (projection I) (hg.trans hh.symm)
    (Y.basicOpen r).ι (SchematicExt.basicOpen_ker_eq_bot r hr)
  exact ext_of_unit_ideal I _ _ ((Y.basicOpen r).ι ≫ f)
    (by rw [Category.assoc, hg]) (by rw [Category.assoc, hh])
    (principal_basicOpen_unit_ideal I f r hI)

end PiExponentSeshadri.ReesGrading

end

end OAI
end Source0503

-- Source: OAI/NumberTheory/PiExponent/Ampleness/AffineBlowupUniversal.lean
section Source0504
/-
Modification notice for the LogTwo project.
Derived from openai/math (Apache-2.0), revision adc7f1241b42e322a6451854ab7e4b4c146bf78a.
Original source: lean/OAI/NumberTheory/PiExponent/Ampleness/AffineBlowupUniversal.lean
Changes: Convert module/import declarations to the Lean 4.34 public module format.
See ../THIRD_PARTY_NOTICES.txt for provenance and the recorded changes.
-/

namespace OAI

namespace PiExponentSeshadri.IdealPullback
noncomputable section
open CategoryTheory AlgebraicGeometry
variable {R : Type} [CommRing R] (I : Ideal R)

lemma specIdeal_coordinate {Y : Scheme} [IsAffine Y]
    (f : Y ⟶ Spec (CommRingCat.of R)) :
    ((specIdeal I).comap f).ideal ⟨⊤, isAffineOpen_top Y⟩ =
      I.map (SpecMaps.coordinate f).hom := by
  rw [comap_top, specIdeal_top, Ideal.map_map]
  rfl

end
end PiExponentSeshadri.IdealPullback

namespace PiExponentSeshadri.ReesGrading
noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace
open PiExponentSeshadri.Geometry
open SpecMaps
variable {R : Type} [CommRing R] (I : Ideal R)

lemma invertible_unique {Y : Scheme} (g h : Y ⟶ affineBlowup I)
    (f : Y ⟶ Spec (CommRingCat.of R))
    (hg : g ≫ projection I = f) (hh : h ≫ projection I = f)
    (hf : InvertiblePullbackIdeal (IdealPullback.specIdeal I) f) : g = h := by
  apply Scheme.hom_ext_of_forall g h
  intro y
  obtain ⟨U, hyU, r, hr, hIr⟩ :=
    InvertibleLocal.affine_local_equation (IdealPullback.specIdeal I) f hf y
  refine ⟨U.1, hyU, ?_⟩
  apply principal_unique I (U.1.ι ≫ g) (U.1.ι ≫ h) (U.1.ι ≫ f)
    (by rw [Category.assoc, hg]) (by rw [Category.assoc, hh]) r _ hr
  rwa [← Scheme.IdealSheafData.comap_comp, IdealPullback.specIdeal_coordinate] at hIr

lemma local_lift {Y : Scheme} (f : Y ⟶ Spec (CommRingCat.of R))
    (hf : InvertiblePullbackIdeal (IdealPullback.specIdeal I) f) (y : Y) :
    ∃ U : Y.Opens, y ∈ U ∧ ∃ h : U.toScheme ⟶ affineBlowup I,
      h ≫ projection I = U.ι ≫ f := by
  obtain ⟨U, hyU, r, hr, hIr⟩ :=
    InvertibleLocal.affine_local_equation (IdealPullback.specIdeal I) f hf y
  rw [← Scheme.IdealSheafData.comap_comp, IdealPullback.specIdeal_coordinate] at hIr
  refine ⟨U.1, hyU, principalScheme I U.1.toScheme (coordinate (U.1.ι ≫ f)).hom r hIr hr, ?_⟩
  rw [principalScheme_projection]
  exact factor (U.1.ι ≫ f)

theorem affineBlowup_universal {Y : Scheme} (f : Y ⟶ Spec (CommRingCat.of R))
    (hf : InvertiblePullbackIdeal (IdealPullback.specIdeal I) f) :
    ∃! h : Y ⟶ affineBlowup I, h ≫ projection I = f := by
  classical
  choose U hyU g hg using local_lift I f hf
  let C : Y.OpenCover := {
    I₀ := Y
    X y := (U y).toScheme
    f y := (U y).ι
    mem₀ := by
      rw [Scheme.presieve₀_mem_precoverage_iff]
      refine ⟨fun y => ⟨y, ?_⟩, inferInstance⟩
      simpa using hyU y }
  have hcompat (x y : C.I₀) : pullback.fst (C.f x) (C.f y) ≫ g x =
      pullback.snd (C.f x) (C.f y) ≫ g y := by
    let j := pullback.fst (C.f x) (C.f y) ≫ C.f x
    apply invertible_unique I _ _ (j ≫ f)
    · rw [Category.assoc, hg x]
      rfl
    · rw [Category.assoc, hg y]
      exact (pullback.condition_assoc f).symm
    · exact InvertibleLocal.invertible_restrict (IdealPullback.specIdeal I) f hf j
  refine ⟨C.glueMorphisms g hcompat, ?_, ?_⟩
  · apply C.hom_ext
    intro y
    rw [← Category.assoc, C.ι_glueMorphisms]
    exact hg y
  · intro h hh
    exact invertible_unique I h _ f hh (by
      apply C.hom_ext
      intro y
      rw [← Category.assoc, C.ι_glueMorphisms]
      exact hg y) hf

end
end PiExponentSeshadri.ReesGrading

end OAI
end Source0504

-- Source: OAI/NumberTheory/PiExponent/Ampleness/BlowupUniversalBaseChange.lean
section Source0505
/-
Modification notice for the LogTwo project.
Derived from openai/math (Apache-2.0), revision adc7f1241b42e322a6451854ab7e4b4c146bf78a.
Original source: lean/OAI/NumberTheory/PiExponent/Ampleness/BlowupUniversalBaseChange.lean
Changes: Convert module/import declarations to the Lean 4.34 public module format.
See ../THIRD_PARTY_NOTICES.txt for provenance and the recorded changes.
-/

namespace OAI

namespace PiExponentSeshadri.Geometry
noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

section
variable {X B Y Z : Scheme} {I : X.IdealSheafData} {π : B ⟶ X}

lemma IsBlowup.hom_ext (hπ : IsBlowup I π) (f : Y ⟶ X)
    (hf : InvertiblePullbackIdeal I f) {g h : Y ⟶ B}
    (hg : g ≫ π = f) (hh : h ≫ π = f) : g = h := by
  obtain ⟨l, _, hl⟩ := hπ.2 Y f hf
  exact (hl g hg).trans (hl h hh).symm

lemma IsBlowup.postIso (hπ : IsBlowup I π) (e : X ≅ Z)
    (J : Z.IdealSheafData) (he : J.comap e.hom = I) :
    IsBlowup J (π ≫ e.hom) := by
  have hcongr (W : Scheme) (f : W ⟶ X) :
      InvertiblePullbackIdeal J (f ≫ e.hom) ↔ InvertiblePullbackIdeal I f :=
    InvertibleLocal.invertible_congr (by rw [Scheme.IdealSheafData.comap_comp, he])
  refine ⟨(hcongr B π).mpr hπ.1, ?_⟩
  intro W f hf
  have hf' : InvertiblePullbackIdeal I (f ≫ e.inv) := by
    apply (hcongr W (f ≫ e.inv)).mp
    simpa only [Category.assoc, Iso.inv_hom_id, Category.comp_id] using hf
  obtain ⟨l, hl, huniq⟩ := hπ.2 W (f ≫ e.inv) hf'
  refine ⟨l, ?_, ?_⟩
  · change l ≫ π ≫ e.hom = f
    rw [← Category.assoc, hl, Category.assoc, Iso.inv_hom_id, Category.comp_id]
  · intro m hm
    apply huniq m
    rw [← cancel_mono e.hom, Category.assoc, hm, Category.assoc,
      Iso.inv_hom_id, Category.comp_id]

lemma IsBlowup.open_baseChange (hπ : IsBlowup I π) (j : Z ⟶ X)
    [IsOpenImmersion j] :
    IsBlowup (I.comap j) (pullback.fst j π) := by
  have hcongr {W : Scheme} (g : W ⟶ Z) :
      InvertiblePullbackIdeal (I.comap j) g ↔ InvertiblePullbackIdeal I (g ≫ j) :=
    InvertibleLocal.invertible_congr (Scheme.IdealSheafData.comap_comp I g j).symm
  have hpic : InvertiblePullbackIdeal (I.comap j) (pullback.fst j π) := by
    apply (hcongr _).mpr
    rw [pullback.condition]
    exact InvertibleLocal.invertible_restrict_general I π hπ.1 (pullback.snd j π)
  refine ⟨hpic, ?_⟩
  intro W f hf
  obtain ⟨l, hl, huniq⟩ := hπ.2 W (f ≫ j) ((hcongr f).mp hf)
  refine ⟨pullback.lift f l hl.symm, pullback.lift_fst _ _ _, ?_⟩
  intro m hm
  apply pullback.hom_ext
  · simpa only [pullback.lift_fst] using hm
  · rw [pullback.lift_snd]
    apply huniq
    rw [Category.assoc, ← pullback.condition, ← Category.assoc, hm]

def IsBlowup.iso {B' : Scheme} {π' : B' ⟶ X} (hπ : IsBlowup I π)
    (hπ' : IsBlowup I π') : B ≅ B' where
  hom := (hπ'.2 B π hπ.1).choose
  inv := (hπ.2 B' π' hπ'.1).choose
  hom_inv_id := by
    apply hπ.hom_ext π hπ.1
    · rw [Category.assoc, (hπ.2 B' π' hπ'.1).choose_spec.1]
      exact (hπ'.2 B π hπ.1).choose_spec.1
    · simp
  inv_hom_id := by
    apply hπ'.hom_ext π' hπ'.1
    · rw [Category.assoc, (hπ'.2 B π hπ.1).choose_spec.1]
      exact (hπ.2 B' π' hπ'.1).choose_spec.1
    · simp

@[reassoc (attr := simp)]
lemma IsBlowup.iso_hom_comp {B' : Scheme} {π' : B' ⟶ X} (hπ : IsBlowup I π)
    (hπ' : IsBlowup I π') : (hπ.iso hπ').hom ≫ π' = π :=
  (hπ'.2 B π hπ.1).choose_spec.1

end

section
variable {X B B' Z : Scheme} {I : X.IdealSheafData} {π : B ⟶ X}

lemma IsBlowup.baseChangeSquare (hπ : IsBlowup I π) (j : Z ⟶ X)
    [IsOpenImmersion j] (ρ : B' ⟶ Z) (hρ : IsBlowup (I.comap j) ρ)
    (β : B' ⟶ B) (hβ : β ≫ π = ρ ≫ j) : IsPullback ρ β j π := by
  let e := hρ.iso (hπ.open_baseChange j)
  refine IsPullback.of_iso_pullback ⟨hβ.symm⟩ e
    (hρ.iso_hom_comp (hπ.open_baseChange j)) ?_
  apply hπ.hom_ext (ρ ≫ j)
  · exact (InvertibleLocal.invertible_congr
      (Scheme.IdealSheafData.comap_comp I ρ j)).mpr hρ.1
  · rw [Category.assoc, ← pullback.condition, ← Category.assoc,
      hρ.iso_hom_comp (hπ.open_baseChange j)]
  · exact hβ

end

open TopologicalSpace
open PiExponentSeshadri.Frames
variable {X B B' : Scheme.{0}} {I : X.IdealSheafData} {π : B ⟶ X}

lemma IsBlowup.preIso (hπ : IsBlowup I π) (e : B' ≅ B) :
    IsBlowup I (e.hom ≫ π) := by
  refine ⟨InvertibleLocal.invertible_restrict_general I π hπ.1 e.hom,?_⟩
  intro Y f hf
  obtain ⟨g,hg,huniq⟩ := hπ.2 Y f hf
  refine ⟨g ≫ e.inv,by simp only [Category.assoc,Iso.inv_hom_id_assoc,hg],?_⟩
  intro g' hg'
  rw [← cancel_mono e.hom]
  simpa only [Category.assoc,Iso.inv_hom_id,Category.comp_id] using huniq (g' ≫ e.hom) hg'

lemma IsBlowup.morphismRestrict (hπ : IsBlowup I π) (U : X.Opens) :
    IsBlowup (I.comap U.ι) (π ∣_ U) := by
  have H := (hπ.open_baseChange U.ι).preIso (isPullback_morphismRestrict π U).isoPullback
  rwa [(isPullback_morphismRestrict π U).isoPullback_hom_fst] at H

end
end PiExponentSeshadri.Geometry

end OAI
end Source0505

-- Source: OAI/NumberTheory/PiExponent/Ampleness/GlobalBlowupGluing.lean
section Source0506
/-
Modification notice for the LogTwo project.
Derived from openai/math (Apache-2.0), revision adc7f1241b42e322a6451854ab7e4b4c146bf78a.
Original source: lean/OAI/NumberTheory/PiExponent/Ampleness/GlobalBlowupGluing.lean
Changes: Convert module/import declarations to the Lean 4.34 public module format.
See ../THIRD_PARTY_NOTICES.txt for provenance and the recorded changes.
-/

namespace OAI

noncomputable section

namespace PiExponentSeshadri.Geometry
open CategoryTheory AlgebraicGeometry

theorem rees_isBlowup {R : Type} [CommRing R] (I : Ideal R) :
    IsBlowup (IdealPullback.specIdeal I) (ReesGrading.projection I) :=
  ⟨ReesGrading.exceptional_invertible I, fun _ f hf =>
    ReesGrading.affineBlowup_universal I f hf⟩

end PiExponentSeshadri.Geometry

namespace PiExponentSeshadri.IdealPullback
open CategoryTheory AlgebraicGeometry
variable {X : Scheme.{0}} [IsAffine X]

lemma specIdeal_comap_toSpec (I : X.IdealSheafData) :
    (specIdeal (I.ideal ⟨⊤, isAffineOpen_top X⟩)).comap X.toSpecΓ = I := by
  apply Scheme.IdealSheafData.ext_of_isAffine
  rw [comap_top, specIdeal_top, Scheme.toSpecΓ_appTop, Ideal.map_map]
  change Ideal.map ((Scheme.ΓSpecIso Γ(X, ⊤)).hom.hom.comp
    (Scheme.ΓSpecIso Γ(X, ⊤)).inv.hom) _ = _
  simp only [← CommRingCat.hom_comp, Iso.inv_hom_id, CommRingCat.hom_id, Ideal.map_id]

lemma comap_isoSpec_inv (I : X.IdealSheafData) :
    I.comap X.isoSpec.inv = specIdeal (I.ideal ⟨⊤, isAffineOpen_top X⟩) := by
  conv_lhs => rw [← specIdeal_comap_toSpec I]
  rw [← Scheme.IdealSheafData.comap_comp]
  change (specIdeal _).comap (X.isoSpec.inv ≫ X.isoSpec.hom) = _
  rw [Iso.inv_hom_id, Scheme.IdealSheafData.comap_id]

end PiExponentSeshadri.IdealPullback

namespace PiExponentSeshadri.AffineBlowup
open CategoryTheory AlgebraicGeometry
open PiExponentSeshadri.Geometry
variable {X : Scheme.{0}} [IsAffine X] (I : X.IdealSheafData)

abbrev scheme : Scheme := ReesGrading.affineBlowup (I.ideal ⟨⊤, isAffineOpen_top X⟩)

def projection : scheme I ⟶ X :=
  ReesGrading.projection (I.ideal ⟨⊤, isAffineOpen_top X⟩) ≫ X.isoSpec.inv

theorem isBlowup : IsBlowup I (projection I) :=
  (rees_isBlowup (I.ideal ⟨⊤, isAffineOpen_top X⟩)).postIso X.isoSpec.symm I
    (IdealPullback.comap_isoSpec_inv I)

end PiExponentSeshadri.AffineBlowup

namespace PiExponentSeshadri.BlowupGluing

section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open PiExponentSeshadri.Geometry
variable {X : Scheme.{0}} (I : X.IdealSheafData)

abbrev baseCover (_I : X.IdealSheafData) : X.OpenCover := Scheme.AffineZariskiSite.directedCover X

local instance localAffine (U : X.AffineZariskiSite) : IsAffine U.toOpens.toScheme := U.2

abbrev localCentre (U : X.AffineZariskiSite) : U.toOpens.toScheme.IdealSheafData := I.comap U.toOpens.ι

abbrev localScheme (U : X.AffineZariskiSite) : Scheme :=
  AffineBlowup.scheme (localCentre I U)

abbrev localProjection (U : X.AffineZariskiSite) : localScheme I U ⟶ U.toOpens.toScheme :=
  AffineBlowup.projection (localCentre I U)

lemma local_isBlowup (U : X.AffineZariskiSite) :
    IsBlowup (localCentre I U) (localProjection I U) :=
  AffineBlowup.isBlowup (localCentre I U)

lemma centre_transition {U V : X.AffineZariskiSite} (h : U ⟶ V) :
    (localCentre I V).comap ((baseCover I).trans h) = localCentre I U := by
  rw [localCentre, ← Scheme.IdealSheafData.comap_comp]
  change I.comap ((baseCover I).trans h ≫ (baseCover I).f V) = _
  rw [Scheme.Cover.trans_map]

lemma local_invertible {U V : X.AffineZariskiSite} (h : U ⟶ V) :
    InvertiblePullbackIdeal (localCentre I V)
      (localProjection I U ≫ (baseCover I).trans h) := by
  apply (InvertibleLocal.invertible_congr (I' := localCentre I U)
    (f' := localProjection I U) ?_).mpr (local_isBlowup I U).1
  rw [Scheme.IdealSheafData.comap_comp, centre_transition]

def transition {U V : X.AffineZariskiSite} (h : U ⟶ V) :
    localScheme I U ⟶ localScheme I V :=
  ((local_isBlowup I V).2 _ _ (local_invertible I h)).choose

@[reassoc (attr := simp)]
lemma transition_projection {U V : X.AffineZariskiSite} (h : U ⟶ V) :
    transition I h ≫ localProjection I V = localProjection I U ≫ (baseCover I).trans h :=
  ((local_isBlowup I V).2 _ _ (local_invertible I h)).choose_spec.1

lemma transition_id (U : X.AffineZariskiSite) : transition I (𝟙 U) = 𝟙 (localScheme I U) := by
  apply (local_isBlowup I U).hom_ext (localProjection I U) (local_isBlowup I U).1
  · rw [transition_projection, Scheme.Cover.trans_id (baseCover I) U, Category.comp_id]
  · simp

lemma transition_comp {U V W : X.AffineZariskiSite} (h : U ⟶ V) (k : V ⟶ W) :
    transition I (h ≫ k) = transition I h ≫ transition I k := by
  apply (local_isBlowup I W).hom_ext _ (local_invertible I (h ≫ k))
  · exact transition_projection I (h ≫ k)
  · rw [Category.assoc, transition_projection, ← Category.assoc, transition_projection,
      Category.assoc, Scheme.Cover.trans_comp (baseCover I) h k]

def diagram : X.AffineZariskiSite ⥤ Scheme where
  obj := localScheme I
  map := transition I
  map_id := transition_id I
  map_comp := transition_comp I

def diagramMap : diagram I ⟶ (baseCover I).functorOfLocallyDirected where
  app := localProjection I
  naturality _ _ h := transition_projection I h

lemma diagramMap_equifibered : (diagramMap I).Equifibered := by
  intro U V h
  apply IsPullback.flip
  change IsPullback (localProjection I U) (transition I h)
    ((baseCover I).trans h) (localProjection I V)
  apply (local_isBlowup I V).baseChangeSquare ((baseCover I).trans h)
    (localProjection I U)
  · rw [centre_transition]
    exact local_isBlowup I U
  · exact transition_projection I h

def gluing : (baseCover I).RelativeGluingData where
  functor := diagram I
  natTrans := diagramMap I
  equifibered := diagramMap_equifibered I

abbrev scheme : Scheme := (gluing I).glued
abbrev projection : scheme I ⟶ X := (gluing I).toBase
abbrev cover : (scheme I).OpenCover := (gluing I).cover

@[reassoc (attr := simp)]
lemma cover_projection (U : X.AffineZariskiSite) :
    (cover I).f U ≫ projection I = localProjection I U ≫ U.toOpens.ι :=
  (gluing I).ι_toBase U

lemma local_pullback (U : X.AffineZariskiSite) :
    IsPullback (localProjection I U) ((cover I).f U) U.toOpens.ι (projection I) :=
  (gluing I).isPullback_natTrans_ι_toBase U

end

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open PiExponentSeshadri.Geometry
variable {X : Scheme.{0}} (I : X.IdealSheafData)

lemma projection_invertible : InvertiblePullbackIdeal I (projection I) := by
  apply InvertibleLocal.invertible_of_cover I (projection I) (cover I)
  intro U
  erw [cover_projection]
  apply (InvertibleLocal.invertible_congr
    (Scheme.IdealSheafData.comap_comp I (localProjection I U) U.toOpens.ι)).mpr
  exact (local_isBlowup I U).1

lemma test_invertible {Y : Scheme.{0}} (f : Y ⟶ X)
    (hf : InvertiblePullbackIdeal I f) (U : X.AffineZariskiSite) :
    InvertiblePullbackIdeal (localCentre I U) (pullback.snd f U.toOpens.ι) := by
  apply (InvertibleLocal.invertible_congr (I' := I)
    (f' := pullback.fst f U.toOpens.ι ≫ f) ?_).mpr
  · exact InvertibleLocal.invertible_restrict_general I f hf (pullback.fst f U.toOpens.ι)
  · change ((I.comap U.toOpens.ι).comap (pullback.snd f U.toOpens.ι)) = _
    rw [← Scheme.IdealSheafData.comap_comp, pullback.condition]

lemma hom_ext {Y : Scheme.{0}} (f : Y ⟶ X) (hf : InvertiblePullbackIdeal I f)
    (g h : Y ⟶ scheme I) (hg : g ≫ projection I = f) (hh : h ≫ projection I = f) : g = h := by
  let C : Y.OpenCover := (baseCover I).pullback₁ f
  apply C.hom_ext
  intro U
  let s := pullback.snd f U.toOpens.ι
  let t := pullback.fst f U.toOpens.ι
  have eg : s ≫ U.toOpens.ι = (t ≫ g) ≫ projection I := by
    rw [Category.assoc, hg]
    exact (pullback.condition (f := f) (g := U.toOpens.ι)).symm
  have eh : s ≫ U.toOpens.ι = (t ≫ h) ≫ projection I := by
    rw [Category.assoc, hh]
    exact (pullback.condition (f := f) (g := U.toOpens.ι)).symm
  let g' := (local_pullback I U).lift s (t ≫ g) eg
  let h' := (local_pullback I U).lift s (t ≫ h) eh
  have he : g' = h' := (local_isBlowup I U).hom_ext s (test_invertible I f hf U)
    ((local_pullback I U).lift_fst _ _ _) ((local_pullback I U).lift_fst _ _ _)
  have he' := congrArg (fun k : C.X U ⟶ localScheme I U => k ≫ (cover I).f U) he
  change t ≫ g = t ≫ h
  exact ((local_pullback I U).lift_snd s (t ≫ g) eg).symm.trans
    (he'.trans ((local_pullback I U).lift_snd s (t ≫ h) eh))

theorem universal {Y : Scheme.{0}} (f : Y ⟶ X) (hf : InvertiblePullbackIdeal I f) :
    ∃! h : Y ⟶ scheme I, h ≫ projection I = f := by
  classical
  let C : Y.OpenCover := (baseCover I).pullback₁ f
  let l (U : X.AffineZariskiSite) : C.X U ⟶ localScheme I U :=
    ((local_isBlowup I U).2 _ _ (test_invertible I f hf U)).choose
  have hl (U : X.AffineZariskiSite) : l U ≫ localProjection I U = pullback.snd f U.toOpens.ι :=
    ((local_isBlowup I U).2 _ _ (test_invertible I f hf U)).choose_spec.1
  let g (U : C.I₀) : C.X U ⟶ scheme I := l U ≫ (cover I).f U
  have hg (U : C.I₀) : g U ≫ projection I = C.f U ≫ f := by
    dsimp only [g]
    exact (Category.assoc (l U) ((cover I).f U) (projection I)).trans
      ((congrArg (fun q : localScheme I U ⟶ X => l U ≫ q)
        (cover_projection I U)).trans
        ((Category.assoc (l U) (localProjection I U) U.toOpens.ι).symm.trans
          ((congrArg (fun q : C.X U ⟶ U.toOpens.toScheme => q ≫ U.toOpens.ι)
            (hl U)).trans (pullback.condition (f := f) (g := U.toOpens.ι)).symm)))
  have hcompat (U V : C.I₀) : pullback.fst (C.f U) (C.f V) ≫ g U =
      pullback.snd (C.f U) (C.f V) ≫ g V := by
    let j := pullback.fst (C.f U) (C.f V) ≫ C.f U
    apply hom_ext I (j ≫ f)
    · exact InvertibleLocal.invertible_restrict_general I f hf j
    · rw [Category.assoc, hg]
      rfl
    · rw [Category.assoc, hg]
      exact (pullback.condition_assoc f).symm
  refine ⟨C.glueMorphisms g hcompat, ?_, ?_⟩
  · apply C.hom_ext
    intro U
    rw [← Category.assoc, Scheme.Cover.ι_glueMorphisms C]
    exact hg U
  · intro h hh
    apply hom_ext I f hf h _ hh
    apply C.hom_ext
    intro U
    rw [← Category.assoc, Scheme.Cover.ι_glueMorphisms C]
    exact hg U

theorem isBlowup : IsBlowup I (projection I) :=
  ⟨projection_invertible I, fun _ f hf => universal I f hf⟩

end PiExponentSeshadri.BlowupGluing

end

end OAI
end Source0506

-- Source: OAI/NumberTheory/PiExponent/Ampleness/BlowupComplement.lean
section Source0507
/-
Modification notice for the LogTwo project.
Derived from openai/math (Apache-2.0), revision adc7f1241b42e322a6451854ab7e4b4c146bf78a.
Original source: lean/OAI/NumberTheory/PiExponent/Ampleness/BlowupComplement.lean
Changes: Convert module/import declarations to the Lean 4.34 public module format.
See ../THIRD_PARTY_NOTICES.txt for provenance and the recorded changes.
-/

namespace OAI

namespace PiExponentSeshadri.Geometry
noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
variable {X Y B : Scheme.{0}} {I : X.IdealSheafData} {π : B ⟶ X}

lemma invertible_top (f : Y ⟶ X) : InvertiblePullbackIdeal ⊤ f := by
  apply InvertibleLocal.invertible_of_local_equations
  intro y
  obtain ⟨U, hU, hyU, _⟩ := exists_isAffineOpen_mem_and_subset
    (show y ∈ (⊤ : Y.Opens) from trivial)
  refine ⟨⟨U, hU⟩, hyU, 1, isRegular_one, ?_⟩
  simp

lemma isBlowup_id (hI : InvertiblePullbackIdeal I (𝟙 X)) :
    IsBlowup I (𝟙 X) := by
  refine ⟨hI, fun Y f _ => ⟨f, by simp, ?_⟩⟩
  intro g hg
  simpa using hg

lemma IsBlowup.isIso_of_invertible (hπ : IsBlowup I π)
    (hI : InvertiblePullbackIdeal I (𝟙 X)) : IsIso π := by
  have hπe : (hπ.iso (isBlowup_id hI)).hom = π := by
    simpa using hπ.iso_hom_comp (isBlowup_id hI)
  rw [← hπe]
  infer_instance

lemma IsBlowup.isIso_over_complement (hπ : IsBlowup I π) :
    IsIso (pullback.fst (Scheme.Opens.ι (X := X) I.support.compl) π) := by
  apply (hπ.open_baseChange (Scheme.Opens.ι (X := X) I.support.compl)).isIso_of_invertible
  have he : I.comap (Scheme.Opens.ι (X := X) I.support.compl) = ⊤ := by
    apply (Scheme.IdealSheafData.support_eq_bot_iff _).mp
    rw [Scheme.IdealSheafData.support_comap]
    ext x
    change (x.val ∈ I.support ↔ False)
    exact iff_false_intro x.property
  rw [he]
  exact invertible_top _

end
end PiExponentSeshadri.Geometry

end OAI
end Source0507

-- Source: OAI/NumberTheory/PiExponent/Ampleness/GlobalBlowupRestriction.lean
section Source0508
/-
Modification notice for the LogTwo project.
Derived from openai/math (Apache-2.0), revision adc7f1241b42e322a6451854ab7e4b4c146bf78a.
Original source: lean/OAI/NumberTheory/PiExponent/Ampleness/GlobalBlowupRestriction.lean
Changes: Convert module/import declarations to the Lean 4.34 public module format.
See ../THIRD_PARTY_NOTICES.txt for provenance and the recorded changes.
-/

namespace OAI

noncomputable section
namespace PiExponentSeshadri.BlowupGluing
open CategoryTheory AlgebraicGeometry PiExponentSeshadri.Geometry
variable {X : Scheme.{0}} (I : X.IdealSheafData)

def exceptionalLineBundle : LineBundle (scheme I) := (projection_invertible I).choose

def exceptionalInclusion : (exceptionalLineBundle I).sheaf ⟶ structureSheaf (scheme I) :=
  (projection_invertible I).choose_spec.choose

theorem exceptional_presents :
    PresentsPullbackIdeal I (projection I) (exceptionalLineBundle I) (exceptionalInclusion I) :=
  (projection_invertible I).choose_spec.choose_spec

def restrictionIso (U : X.Opens) :
    ((projection I) ⁻¹ᵁ U).toScheme ≅ scheme (I.comap U.ι) :=
  ((isBlowup I).morphismRestrict U).iso (isBlowup (I.comap U.ι))

@[reassoc (attr := simp)]
theorem restrictionIso_hom_projection (U : X.Opens) :
    (restrictionIso I U).hom ≫ projection (I.comap U.ι) = (projection I) ∣_ U :=
  ((isBlowup I).morphismRestrict U).iso_hom_comp (isBlowup (I.comap U.ι))

def affineRestrictionIso (U : X.affineOpens) :
    ((projection I) ⁻¹ᵁ U.1).toScheme ≅ AffineBlowup.scheme (I.comap U.1.ι) :=
  ((isBlowup I).morphismRestrict U.1).iso (AffineBlowup.isBlowup (I.comap U.1.ι))

@[reassoc (attr := simp)]
theorem affineRestrictionIso_hom_projection (U : X.affineOpens) :
    (affineRestrictionIso I U).hom ≫ AffineBlowup.projection (I.comap U.1.ι) =
      (projection I) ∣_ U.1 :=
  ((isBlowup I).morphismRestrict U.1).iso_hom_comp
    (AffineBlowup.isBlowup (I.comap U.1.ι))

end PiExponentSeshadri.BlowupGluing

end

end OAI
end Source0508

-- Source: OAI/NumberTheory/PiExponent/Ampleness/BlowupProperIntegral.lean
section Source0509
-- Modified in this edition: unused plain lemmas removed; see reduction.json.
/-
Modification notice for the LogTwo project.
Derived from openai/math (Apache-2.0), revision adc7f1241b42e322a6451854ab7e4b4c146bf78a.
Original source: lean/OAI/NumberTheory/PiExponent/Ampleness/BlowupProperIntegral.lean
Changes: Convert module/import declarations to the Lean 4.34 public module format.
See ../THIRD_PARTY_NOTICES.txt for provenance and the recorded changes.
-/

namespace OAI

noncomputable section

namespace PiExponentSeshadri
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

instance AffineBlowup.projection_proper {X : Scheme.{0}} [IsAffine X]
    [IsLocallyNoetherian X] (I : X.IdealSheafData) : IsProper (AffineBlowup.projection I) := by
  let : IsNoetherianRing Γ(X,⊤) := IsLocallyNoetherian.component_noetherian ⟨⊤,isAffineOpen_top X⟩
  unfold AffineBlowup.projection
  infer_instance

instance BlowupGluing.projection_proper {X : Scheme.{0}} [IsLocallyNoetherian X]
    (I : X.IdealSheafData) : IsProper (BlowupGluing.projection I) := by
  apply IsZariskiLocalAtTarget.of_openCover (P := @IsProper) (BlowupGluing.baseCover I)
  intro U
  let he := (BlowupGluing.local_pullback I U).flip.isoPullback
  have hh : he.hom ≫ pullback.snd (BlowupGluing.projection I) U.toOpens.ι =
      BlowupGluing.localProjection I U := by
    exact (BlowupGluing.local_pullback I U).flip.isoPullback_hom_snd
  have h : IsProper (BlowupGluing.localProjection I U) := by infer_instance
  rw [← hh] at h
  exact (MorphismProperty.cancel_left_of_respectsIso (@IsProper) he.hom _).mp h

end PiExponentSeshadri

namespace PiExponentSeshadri.ProjectiveGeometry
open AlgebraicGeometry
universe u v
variable {A : Type u} {σ : Type v} [CommRing A]
  [SetLike σ A] [AddSubgroupClass σ A] (𝒜 : ℕ → σ) [GradedRing 𝒜]

instance homogeneous_isReduced (S : Submonoid A) [_root_.IsReduced A] :
    _root_.IsReduced (HomogeneousLocalization 𝒜 S) :=
  isReduced_of_injective (algebraMap (HomogeneousLocalization 𝒜 S) (Localization S))
    (HomogeneousLocalization.val_injective S)

instance proj_isReduced [_root_.IsReduced A] : IsReduced (Proj 𝒜) := by
  have (x : Proj 𝒜) : _root_.IsReduced ((Proj 𝒜).presheaf.stalk x) :=
    isReduced_of_injective (Proj.stalkIso' 𝒜 x) (Proj.stalkIso' 𝒜 x).injective
  exact isReduced_of_isReduced_stalk _

def genericPoint [IsDomain A] [Nonempty (Proj 𝒜)] : ProjectiveSpectrum 𝒜 where
  asHomogeneousIdeal := ⊥
  isPrime := Ideal.isPrime_bot
  not_irrelevant_le h := by
    obtain ⟨x⟩ := ‹Nonempty (Proj 𝒜)›
    exact x.not_irrelevant_le (h.trans bot_le)

lemma genericPoint_dense [IsDomain A] [Nonempty (Proj 𝒜)] :
    closure ({genericPoint 𝒜} : Set (ProjectiveSpectrum 𝒜)) = Set.univ := by
  apply Set.eq_univ_of_forall
  intro x
  exact (ProjectiveSpectrum.le_iff_mem_closure 𝒜 _ _).mp
    (show (genericPoint 𝒜).asHomogeneousIdeal ≤ x.asHomogeneousIdeal from bot_le)

instance proj_irreducible [IsDomain A] [Nonempty (Proj 𝒜)] :
    IrreducibleSpace (Proj 𝒜) := by
  apply (irreducibleSpace_def _).mpr
  change IsIrreducible (Set.univ : Set (ProjectiveSpectrum 𝒜))
  rw [← genericPoint_dense 𝒜]
  exact (isIrreducible_singleton).closure

instance proj_isIntegral [IsDomain A] [Nonempty (Proj 𝒜)] : IsIntegral (Proj 𝒜) :=
  (isIntegral_iff_irreducibleSpace_and_isReduced _).mpr ⟨inferInstance, inferInstance⟩

end PiExponentSeshadri.ProjectiveGeometry

namespace PiExponentSeshadri.Geometry
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace
variable {X B : Scheme.{0}} {I : X.IdealSheafData} {π : B ⟶ X}

abbrev centreComplement (I : X.IdealSheafData) : X.Opens := I.support.compl

lemma complement_nonempty (hI : I.support ≠ ⊤) : Nonempty (centreComplement I).toScheme := by
  by_contra h
  apply hI
  ext x
  change x ∈ I.support ↔ True
  rw [iff_true]
  by_contra hx
  exact h ⟨⟨x, hx⟩⟩

def IsBlowup.complementLift (hπ : IsBlowup I π) : (centreComplement I).toScheme ⟶ B := by
  let := hπ.isIso_over_complement
  exact inv (pullback.fst (centreComplement I).ι π) ≫
    pullback.snd (centreComplement I).ι π

@[reassoc (attr := simp)]
lemma IsBlowup.complementLift_comp (hπ : IsBlowup I π) :
    hπ.complementLift ≫ π = (centreComplement I).ι := by
  let := hπ.isIso_over_complement
  dsimp only [IsBlowup.complementLift]
  rw [Category.assoc, ← pullback.condition, ← Category.assoc, IsIso.inv_hom_id,
    Category.id_comp]

instance (hπ : IsBlowup I π) : IsOpenImmersion hπ.complementLift := by
  let := hπ.isIso_over_complement
  dsimp only [IsBlowup.complementLift]
  infer_instance

lemma IsBlowup.complementLift_range (hπ : IsBlowup I π) :
    Set.range hπ.complementLift = π ⁻¹' (centreComplement I : Set X) := by
  let := hπ.isIso_over_complement
  change Set.range ((pullback.snd (centreComplement I).ι π) ∘
    (inv (pullback.fst (centreComplement I).ι π))) = _
  rw [Set.range_comp]
  rw [(inv (pullback.fst (centreComplement I).ι π)).surjective.range_eq,
    Set.image_univ, Scheme.Pullback.range_snd]
  simp

lemma IsBlowup.nonempty_of_support_ne_top (hπ : IsBlowup I π) (hI : I.support ≠ ⊤) :
    Nonempty B :=
  (complement_nonempty hI).map hπ.complementLift

end PiExponentSeshadri.Geometry

namespace PiExponentSeshadri.ReesGrading
open AlgebraicGeometry Polynomial
variable {R : Type} [CommRing R] (I : Ideal R)

instance polynomial_isReduced [_root_.IsReduced R] : _root_.IsReduced R[X] where
  eq_zero p hp := by
    ext n
    exact (Polynomial.isNilpotent_iff.mp hp n).eq_zero

instance affineBlowup_isReduced [_root_.IsReduced R] : IsReduced (affineBlowup I) := by
  let : _root_.IsReduced (reesAlgebra I) :=
    isReduced_of_injective (reesAlgebra I).val Subtype.val_injective
  exact ProjectiveGeometry.proj_isReduced (piece I)

instance affineBlowup_isIntegral [IsDomain R] [Nonempty (affineBlowup I)] :
    IsIntegral (affineBlowup I) := by
  let : IsDomain (reesAlgebra I) :=
    Function.Injective.isDomain (reesAlgebra I).val Subtype.val_injective
  let : Nonempty (Proj (piece I)) := ‹Nonempty (affineBlowup I)›
  exact ProjectiveGeometry.proj_isIntegral (piece I)

end PiExponentSeshadri.ReesGrading

namespace PiExponentSeshadri.AffineBlowup
open AlgebraicGeometry
variable {X : Scheme.{0}} [IsAffine X] (I : X.IdealSheafData)

instance scheme_isReduced [IsReduced X] : IsReduced (scheme I) := by
  dsimp only [scheme]
  infer_instance

instance scheme_isIntegral [IsIntegral X] [Nonempty (scheme I)] : IsIntegral (scheme I) := by
  dsimp only [scheme]
  infer_instance

end PiExponentSeshadri.AffineBlowup

namespace PiExponentSeshadri.BlowupGluing
open AlgebraicGeometry
variable {X : Scheme.{0}} (I : X.IdealSheafData)

instance scheme_isReduced [IsReduced X] : IsReduced (scheme I) := by
  let : ∀ U : (cover I).I₀, IsReduced ((cover I).X U) := fun U => by
    change IsReduced (localScheme I U)
    infer_instance
  exact IsReduced.of_openCover _ (cover I)

end PiExponentSeshadri.BlowupGluing

namespace PiExponentSeshadri.Geometry
open AlgebraicGeometry TopologicalSpace
variable {X Y : Scheme.{0}} [IrreducibleSpace X] (I : X.IdealSheafData)

lemma support_comap_ne_top_of_open (hI : I.support ≠ ⊤) (j : Y ⟶ X)
    [IsOpenImmersion j] [Nonempty Y] : (I.comap j).support ≠ ⊤ := by
  have hc : (centreComplement I : Set X).Nonempty := by
    obtain ⟨x⟩ := complement_nonempty hI
    exact ⟨x.val, x.property⟩
  obtain ⟨_, ⟨y, rfl⟩, hy⟩ := nonempty_preirreducible_inter
    j.isOpenEmbedding.isOpen_range (centreComplement I).isOpen (Set.range_nonempty j) hc
  intro he
  have hyn : y ∈ (I.comap j).support := by rw [he]; trivial
  rw [Scheme.IdealSheafData.support_comap] at hyn
  exact hy hyn

end PiExponentSeshadri.Geometry

namespace PiExponentSeshadri.BlowupGluing
open AlgebraicGeometry CategoryTheory TopologicalSpace PiExponentSeshadri.Geometry
variable {X : Scheme.{0}} [IsIntegral X] (I : X.IdealSheafData)

lemma localScheme_isIntegral (hI : I.support ≠ ⊤) (U : X.AffineZariskiSite)
    [Nonempty U.toOpens.toScheme] : IsIntegral (localScheme I U) := by
  let : IsIntegral U.toOpens.toScheme := isIntegral_of_isOpenImmersion U.toOpens.ι
  let : Nonempty (localScheme I U) := (local_isBlowup I U).nonempty_of_support_ne_top
    (support_comap_ne_top_of_open I hI U.toOpens.ι)
  infer_instance

omit [IsIntegral X] in
lemma cover_range (U : X.AffineZariskiSite) :
    Set.range ((cover I).f U) = projection I ⁻¹' (U.toOpens : Set X) := by
  have h := ((gluing I).preimage_toBase_eq_range_ι U).symm
  change Set.range ((cover I).f U) = projection I ⁻¹' Set.range U.toOpens.ι at h
  simpa only [Scheme.Opens.range_ι] using h

lemma complement_dense (hI : I.support ≠ ⊤) :
    Dense (projection I ⁻¹' (centreComplement I : Set X)) := by
  rw [dense_iff_inter_open]
  intro V hV ⟨y, hyV⟩
  obtain ⟨U, z, rfl⟩ := (cover I).exists_eq y
  let : Nonempty U.toOpens.toScheme := ⟨localProjection I U z⟩
  let : IsIntegral ((cover I).X U) := localScheme_isIntegral I hI U
  have hc : (centreComplement I : Set X).Nonempty := by
    obtain ⟨x⟩ := complement_nonempty hI
    exact ⟨x.val, x.property⟩
  have hU : (U.toOpens : Set X).Nonempty := by
    obtain ⟨x⟩ := ‹Nonempty U.toOpens.toScheme›
    exact ⟨x.val, x.property⟩
  obtain ⟨x, hxU, hxc⟩ := nonempty_preirreducible_inter
    U.toOpens.isOpen (centreComplement I).isOpen hU hc
  let b : scheme I := (isBlowup I).complementLift ⟨x, hxc⟩
  have hpb : projection I b = x :=
    congrArg (fun f : (centreComplement I).toScheme ⟶ X => f ⟨x, hxc⟩)
      (isBlowup I).complementLift_comp
  have hbr : b ∈ Set.range ((cover I).f U) := by
    erw [cover_range I U]
    change projection I b ∈ U.toOpens
    rwa [hpb]
  obtain ⟨w, hw⟩ := hbr
  have hwc : (cover I).f U w ∈ projection I ⁻¹' (centreComplement I : Set X) := by
    change projection I ((cover I).f U w) ∈ centreComplement I
    rwa [hw, hpb]
  obtain ⟨q, hqV, hqc⟩ := nonempty_preirreducible_inter
    (hV.preimage ((cover I).f U).continuous)
    (((centreComplement I).isOpen.preimage (projection I).continuous).preimage
      ((cover I).f U).continuous) ⟨z, hyV⟩ ⟨w, hwc⟩
  exact ⟨(cover I).f U q, hqV, hqc⟩

lemma scheme_isIntegral (hI : I.support ≠ ⊤) : IsIntegral (scheme I) := by
  let : Nonempty (centreComplement I).toScheme := complement_nonempty hI
  let : IsIntegral (centreComplement I).toScheme :=
    isIntegral_of_isOpenImmersion (centreComplement I).ι
  have hi : IsIrreducible (Set.range (isBlowup I).complementLift) := by
    simpa only [Set.image_univ] using
      (IrreducibleSpace.isIrreducible_univ (X := (centreComplement I).toScheme)).image
        (isBlowup I).complementLift (isBlowup I).complementLift.continuous.continuousOn
  have hd : Dense (Set.range (isBlowup I).complementLift) := by
    rw [Geometry.IsBlowup.complementLift_range]
    exact complement_dense I hI
  let : IrreducibleSpace (scheme I) := (irreducibleSpace_def _).mpr (by
    change IsIrreducible (Set.univ : Set (scheme I))
    rw [← hd.closure_eq]
    exact hi.closure)
  exact isIntegral_of_irreducibleSpace_of_isReduced _

end PiExponentSeshadri.BlowupGluing

end

end OAI
end Source0509

-- Source: OAI/NumberTheory/PiExponent/Geometry/WeightedProjectiveLineBundle.lean
section Source0510
-- Modified in this edition: unused plain lemmas removed; see reduction.json.
/-
Modification notice for the LogTwo project.
Derived from openai/math (Apache-2.0), revision adc7f1241b42e322a6451854ab7e4b4c146bf78a.
Original source: lean/OAI/NumberTheory/PiExponent/Geometry/WeightedProjectiveLineBundle.lean
Changes: Convert module/import declarations to the Lean 4.34 public module format.
See ../THIRD_PARTY_NOTICES.txt for provenance and the recorded changes.
-/

namespace OAI

noncomputable section

namespace PiExponent.WeightedCompactification

open AlgebraicGeometry CategoryTheory TopologicalSpace
open PiExponentSeshadri.Geometry PiExponentSeshadri.Frames PiExponentSeshadri.LineBundleGluing

variable {R ι σ : Type} [CommRing R]

def lineBundle (a : σ → ι →₀ ℕ) : LineBundle (Proj (imageGrade (R := R) a)) :=
  (ProjectiveO1.lineBundle (R := R) (σ := σ)).pullback (projectiveMonomialMap a)

def coordinateSection (a : σ → ι →₀ ℕ) (s : σ) :
    O (Proj (imageGrade (R := R) a)) ⟶ (lineBundle a).sheaf :=
  pullbackSection (projectiveMonomialMap a) (ProjectiveO1.coordinateSection s)

end PiExponent.WeightedCompactification

end

end OAI
end Source0510

-- Source: OAI/NumberTheory/PiExponent/Geometry/WeightedProjectiveEmbedding.lean
section Source0511
/-
Modification notice for the LogTwo project.
Derived from openai/math (Apache-2.0), revision adc7f1241b42e322a6451854ab7e4b4c146bf78a.
Original source: lean/OAI/NumberTheory/PiExponent/Geometry/WeightedProjectiveEmbedding.lean
Changes: Convert module/import declarations to the Lean 4.34 public module format.
See ../THIRD_PARTY_NOTICES.txt for provenance and the recorded changes.
-/

namespace OAI

noncomputable section

namespace PiExponent.WeightedCompactification

open AlgebraicGeometry CategoryTheory
open PiExponentSeshadri.Geometry PiExponentSeshadri.Projective PiExponentSeshadri.Frames

variable {R ι σ : Type} [CommRing R]

def scalars (a : σ → ι →₀ ℕ) : R →+* Γ(Proj (imageGrade (R := R) a), ⊤) :=
  (projectiveMonomialMap a).appTop.hom.comp (ProjectiveO1.scalars (R := R) (σ := σ))

theorem coordinateSection_cover (a : σ → ι →₀ ℕ) :
    (⨆ i : σ, PiExponentSeshadri.SectionOpens.isoOpen (coordinateSection (R := R) a i)) = ⊤ :=
  pullback_sections_cover (ProjectiveO1.coordinateSection (R := R))
    ProjectiveO1.coordinateSection_cover (projectiveMonomialMap a)

theorem coordinateSection_isoOpen (a : σ → ι →₀ ℕ) (i : σ) :
    PiExponentSeshadri.SectionOpens.isoOpen (coordinateSection (R := R) a i) =
      Proj.basicOpen (imageGrade a) (imageCoordinate a i) := by
  have h := pullback_isoOpen_eq (ProjectiveO1.lineBundle (R := R) (σ := σ))
    (ProjectiveO1.coordinateSection i) (projectiveMonomialMap a)
  rw [ProjectiveO1.coordinateSection_isoOpen] at h
  exact h

theorem coordinateSection_isAffineOpen (a : σ → ι →₀ ℕ) (i : σ) :
    IsAffineOpen (PiExponentSeshadri.SectionOpens.isoOpen (coordinateSection (R := R) a i)) := by
  rw [coordinateSection_isoOpen]
  exact Proj.isAffineOpen_basicOpen _ _ (imageCoordinate_mem a i) (by decide)

theorem coordinate_sectionsMorphism_embedding (a : σ → ι →₀ ℕ) :
    sectionsMorphism (scalars (R := R) a) (coordinateSection a) (coordinateSection_cover a) =
      projectiveMonomialMap a := by
  exact (sectionsMorphism_pullback (ProjectiveO1.scalars (R := R) (σ := σ))
    ProjectiveO1.coordinateSection ProjectiveO1.coordinateSection_cover
    (projectiveMonomialMap a)).symm.trans
      ((congrArg (fun g => projectiveMonomialMap (R := R) a ≫ g)
        ProjectiveO1.coordinate_sectionsMorphism_identity).trans (Category.comp_id _))

instance coordinate_sectionsMorphism_isClosedImmersion (a : σ → ι →₀ ℕ) :
    IsClosedImmersion
      (sectionsMorphism (scalars (R := R) a) (coordinateSection a) (coordinateSection_cover a)) := by
  rw [coordinate_sectionsMorphism_embedding]
  infer_instance

end PiExponent.WeightedCompactification

end

end OAI
end Source0511

-- Source: OAI/NumberTheory/PiExponent/Ampleness/WeightedProjectiveAmple.lean
section Source0512
/-
Modification notice for the LogTwo project.
Derived from openai/math (Apache-2.0), revision adc7f1241b42e322a6451854ab7e4b4c146bf78a.
Original source: lean/OAI/NumberTheory/PiExponent/Ampleness/WeightedProjectiveAmple.lean
Changes: Convert module/import declarations to the Lean 4.34 public module format.
See ../THIRD_PARTY_NOTICES.txt for provenance and the recorded changes.
-/

namespace OAI

noncomputable section

namespace PiExponent.WeightedCompactification

open AlgebraicGeometry CategoryTheory
open PiExponentSeshadri.Geometry PiExponentSeshadri.Frames

variable {R ι σ : Type} [CommRing R]

theorem lineBundle_ample [IsDomain R] [Finite σ] [Nonempty σ] (a : σ → ι →₀ ℕ) :
    (lineBundle (R := R) a).IsAmple :=
  LineBundle.IsAmple.pullback_closedImmersion (ProjectiveO1.lineBundle (R := R) (σ := σ))
    ProjectiveO1.lineBundle_ample (projectiveMonomialMap a)

end PiExponent.WeightedCompactification

end

end OAI
end Source0512

-- Source: LogTwo/Geometry/WeightedBlowup.lean
section Source0513
/-
Modification notice for the LogTwo project.
Adapted from openai/math (Apache-2.0), revision adc7f1241b42e322a6451854ab7e4b4c146bf78a.
Changes: Adapt the blowup construction to the varying-center ideal.
See ../THIRD_PARTY_NOTICES.txt for provenance and the recorded changes.
-/

/-! The actual blowup of the varying-center ideal, its exceptional line
bundle and the verified presentation of the pulled-back ideal. The ambient
hyperplane is ample; ampleness of a line bundle on the blowup is not asserted.
Construction adapted from openai/math Ampleness/AdmissibleBlowupGeometry.lean
(Apache-2.0), using only its scheme-generic APIs. -/
namespace LogTwo.Geometry.MatrixBlowup
open OAI PiExponent AlgebraicGeometry CategoryTheory TopologicalSpace
open PiExponentSeshadri.Geometry PiExponentSeshadri.Frames
open LogTwo.Interpolation LogTwo.Arithmetic
open CurveNormalizationModel CurveValuationCenter PlaceValuationRing
noncomputable section
variable {m : ℕ} (w : Weights m)

def hyperplane : LineBundle (MatrixCompactification.space w) :=
  WeightedCompactification.lineBundle (MatrixCompactification.exponents w)

theorem hyperplane_ample : (hyperplane w).IsAmple :=
  WeightedCompactification.lineBundle_ample _

variable {K : ℕ} (y : Fin K → ℂ) (c : Fin K → Fin m → ℂ) (T : Fin m → ℕ)
abbrev space : Scheme :=
  PiExponentSeshadri.BlowupGluing.scheme (MatrixCompactification.centerIdeal w y c T)
abbrev projection : space w y c T ⟶ MatrixCompactification.space w :=
  PiExponentSeshadri.BlowupGluing.projection (MatrixCompactification.centerIdeal w y c T)
def structureMap : space w y c T ⟶ Spec (.of ℂ) :=
  projection w y c T ≫ MatrixCompactification.structureMap w

instance projection_proper : IsProper (projection w y c T) := by infer_instance
instance structureMap_proper : IsProper (structureMap w y c T) := by
  dsimp [structureMap]
  infer_instance

theorem space_isIntegral (hy0 : ∀ j, y j ≠ 0) : IsIntegral (space w y c T) :=
  PiExponentSeshadri.BlowupGluing.scheme_isIntegral _
    (MatrixCompactification.centerIdeal_support_ne_top w y hy0 c T)

instance space_isLocallyNoetherian : IsLocallyNoetherian (space w y c T) :=
  LocallyOfFiniteType.isLocallyNoetherian (structureMap w y c T)
instance space_compact : CompactSpace (space w y c T) :=
  QuasiCompact.compactSpace_of_compactSpace (structureMap w y c T)
instance space_isNoetherian : IsNoetherian (space w y c T) := {}

def A : LineBundle (space w y c T) := (hyperplane w).pullback (projection w y c T)
abbrev J : LineBundle (space w y c T) :=
  PiExponentSeshadri.BlowupGluing.exceptionalLineBundle (MatrixCompactification.centerIdeal w y c T)
abbrev exceptionalInclusion : (J w y c T).sheaf ⟶ O (space w y c T) :=
  PiExponentSeshadri.BlowupGluing.exceptionalInclusion (MatrixCompactification.centerIdeal w y c T)

theorem exceptional_presents :
    PresentsPullbackIdeal (MatrixCompactification.centerIdeal w y c T)
      (projection w y c T) (J w y c T) (exceptionalInclusion w y c T) :=
  PiExponentSeshadri.BlowupGluing.exceptional_presents _

theorem isBlowup :
    IsBlowup (MatrixCompactification.centerIdeal w y c T) (projection w y c T) :=
  PiExponentSeshadri.BlowupGluing.isBlowup _

variable {E : Type} [Field E] [Algebra ℂ E]
variable (f : E) (hf : Transcendental ℂ f)
variable [FiniteDimensional (IntermediateField.adjoin ℂ {f}) E]
variable (hfinite : ∀ t : E, Transcendental ℂ t →
  FiniteDimensional (IntermediateField.adjoin ℂ {t}) E)
variable (z : Fin (m+1) → E) (hz : ∃ i, Transcendental ℂ (z i))
variable (hres : ∀ p : NormalizedPlace ℂ E,
  Algebra.IsIntegral ℂ (IsLocalRing.ResidueField (ring p)))
variable (hy : Function.Injective y) (hy0 : ∀ j, y j ≠ 0) (hK : 0 < K)

include hy in
/-- The presentation is now constructed, not supplied as a theorem argument. -/
theorem exceptional_degree_eq_neg_contact_sum (F : ℚ) (hF : 1 / w.theta < F)
    (g : parameterCurve f hf ⟶ space w y c (truncationOrders w F))
    (hgeneric : parameterCurveGenericPoint f hf ≫ g ≫
        projection w y c (truncationOrders w F) =
      Spec.map (CommRingCat.ofHom (MvPolynomial.aeval z).toRingHom) ≫
        MatrixCompactification.affineChart w) :
    ((eulerCharacteristic (parameterCurveStructureMap f hf) 1
        ((J w y c (truncationOrders w F)).pullback g).sheaf -
      eulerCharacteristic (parameterCurveStructureMap f hf) 1
        (structureSheaf (parameterCurve f hf)) : ℤ) : ℚ) =
      -((MatrixCompactification.scale w).radius : ℚ) *
        ∑ p ∈ ContactFamilyAt.places hfinite z y c hz,
          ContactFamilyAt.contact hres hfinite z y hy0 c hz hK (jetWeight w) p := by
  exact MatrixCompactification.euler_degree_eq_neg_contact_sum w f hf hfinite z y c hz
    (projection w y c (truncationOrders w F)) (J w y c (truncationOrders w F))
    (exceptionalInclusion w y c (truncationOrders w F)) g hgeneric hres hy hy0 hK F hF
    (exceptional_presents w y c (truncationOrders w F))

end
end LogTwo.Geometry.MatrixBlowup
end Source0513

-- Source: OAI/NumberTheory/PiExponent/Geometry/WeightedLocalSheaf.lean
section Source0514
/-
Modification notice for the LogTwo project.
Derived from openai/math (Apache-2.0), revision adc7f1241b42e322a6451854ab7e4b4c146bf78a.
Original source: lean/OAI/NumberTheory/PiExponent/Geometry/WeightedLocalSheaf.lean
Changes: Convert module/import declarations to the Lean 4.34 public module format.
See ../THIRD_PARTY_NOTICES.txt for provenance and the recorded changes.
-/

namespace OAI

noncomputable section
open CategoryTheory AlgebraicGeometry
open PiExponentSeshadri.Geometry
open PiExponent.WeightedLocalLattice
open scoped BigOperators
universe u

namespace PiExponent.WeightedLocalSheaf

def monomialSheaf
    {A K : Type u} {ι : Type*} [CommRing A] [Field K] [Algebra A K]
    [Fintype ι] (x : ι → Kˣ) (monomials : Finset (ι → ℕ)) :
    (Spec (CommRingCat.of A)).Modules :=
  tilde (ModuleCat.of A (monomialLattice A x monomials))

def monomialFrame
    {A K : Type u} {ι : Type*} [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
    [Field K] [Algebra A K] [IsFractionRing A K] [Fintype ι]
    (x : ι → Kˣ) (monomials : Finset (ι → ℕ)) (hzero : 0 ∈ monomials) :
    monomialSheaf (A := A) x monomials ≅ structureSheaf (Spec (CommRingCat.of A)) :=
  (tilde.functor (CommRingCat.of A)).mapIso
    (monomialLattice_rank_one (A := A) x monomials hzero).some.symm.toModuleIso ≪≫
      tildeSelf

def monomialLineBundle
    {A K : Type u} {ι : Type*} [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
    [Field K] [Algebra A K] [IsFractionRing A K] [Fintype ι]
    (x : ι → Kˣ) (monomials : Finset (ι → ℕ)) (hzero : 0 ∈ monomials) :
    LineBundle (Spec (CommRingCat.of A)) where
  sheaf := monomialSheaf x monomials
  locallyRankOne _ := ⟨⊤, trivial, ⟨
    (Scheme.Modules.restrictFunctor (⊤ : (Spec (CommRingCat.of A)).Opens).ι).mapIso
      (monomialFrame x monomials hzero) ≪≫
        Scheme.Modules.restrictUnitIso (⊤ : (Spec (CommRingCat.of A)).Opens).ι⟩⟩

def monomialSectionMap
    {A K : Type*} {ι : Type*} [CommRing A] [Field K] [Algebra A K]
    [Fintype ι] (x : ι → Kˣ) (monomials : Finset (ι → ℕ))
    (a : ι → ℕ) (ha : a ∈ monomials) : A →ₗ[A] monomialLattice A x monomials where
  toFun c := ⟨c • ((∏ i, x i ^ a i : Kˣ) : K),
    Submodule.smul_mem _ c (Submodule.subset_span ⟨a, ha, rfl⟩)⟩
  map_add' c d := by ext; simp [add_smul]
  map_smul' c d := by ext; simp [mul_smul]

def monomialSection
    {A K : Type u} {ι : Type*} [CommRing A] [Field K] [Algebra A K]
    [Fintype ι] (x : ι → Kˣ) (monomials : Finset (ι → ℕ))
    (a : ι → ℕ) (ha : a ∈ monomials) :
    structureSheaf (Spec (CommRingCat.of A)) ⟶ monomialSheaf (A := A) x monomials :=
  tildeSelf.inv ≫ (tilde.functor (CommRingCat.of A)).map
    (ModuleCat.ofHom (monomialSectionMap x monomials a ha))

def generatedSheaf
    {A K : Type u} {ι : Type*} [CommRing A] [Field K] [Algebra A K]
    (y : ι → K) (s : Finset ι) : (Spec (CommRingCat.of A)).Modules :=
  tilde (ModuleCat.of A (generatedLattice A y s))

def generatedSectionMap
    {A K : Type*} {ι : Type*} [CommRing A] [Field K] [Algebra A K]
    (y : ι → K) (s : Finset ι) (a : ι) (ha : a ∈ s) :
    A →ₗ[A] generatedLattice A y s where
  toFun c := ⟨c • y a, Submodule.smul_mem _ c (Submodule.subset_span ⟨a, ha, rfl⟩)⟩
  map_add' c d := by ext; simp [add_smul]
  map_smul' c d := by ext; simp [mul_smul]

theorem generatedSectionMap_bijective_of_span
    {A K : Type*} {ι : Type*} [CommRing A] [IsDomain A]
    [Field K] [Algebra A K] [IsFractionRing A K]
    (y : ι → K) (s : Finset ι) (a : ι) (ha : a ∈ s) (hya : y a ≠ 0)
    (hspan : generatedLattice A y s = Submodule.span A {y a}) :
    Function.Bijective (generatedSectionMap (A := A) y s a ha) := by
  constructor
  · intro c d h
    have h' := congrArg (fun z : generatedLattice A y s => (z : K)) h
    change c • y a = d • y a at h'
    simp only [Algebra.smul_def] at h'
    exact IsFractionRing.injective A K (mul_right_cancel₀ hya h')
  · intro z
    have hz := hspan.le z.2
    obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp hz
    exact ⟨c, Subtype.ext hc⟩

def generatedSection
    {A K : Type u} {ι : Type*} [CommRing A] [Field K] [Algebra A K]
    (y : ι → K) (s : Finset ι) (a : ι) (ha : a ∈ s) :
    structureSheaf (Spec (CommRingCat.of A)) ⟶ generatedSheaf (A := A) y s :=
  tildeSelf.inv ≫ (tilde.functor (CommRingCat.of A)).map
    (ModuleCat.ofHom (generatedSectionMap y s a ha))

theorem generatedSection_isIso_of_minimum
    {A K : Type u} {ι : Type*} [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
    [Field K] [Algebra A K] [IsFractionRing A K]
    (y : ι → K) (s : Finset ι) (a : ι) (ha : a ∈ s) (hya : y a ≠ 0)
    (hmin : ∀ b ∈ s, CurveLocalOrder.fractionAddValuation A K (y a) ≤
      CurveLocalOrder.fractionAddValuation A K (y b)) :
    IsIso (generatedSection (A := A) y s a ha) := by
  let e : A ≃ₗ[A] generatedLattice A y s := LinearEquiv.ofBijective
    (generatedSectionMap (A := A) y s a ha)
    (generatedSectionMap_bijective_of_span y s a ha hya
      (generatedLattice_eq_span_of_minimum y s a ha hya hmin))
  exact (tildeSelf.symm ≪≫ (tilde.functor (CommRingCat.of A)).mapIso e.toModuleIso).isIso_hom

def generatedLineBundle
    {A K : Type u} {ι : Type*} [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
    [Field K] [Algebra A K] [IsFractionRing A K]
    (y : ι → K) (s : Finset ι) (a : ι) (ha : a ∈ s) (hya : y a ≠ 0)
    (hmin : ∀ b ∈ s, CurveLocalOrder.fractionAddValuation A K (y a) ≤
      CurveLocalOrder.fractionAddValuation A K (y b)) :
    LineBundle (Spec (CommRingCat.of A)) := by
  letI := generatedSection_isIso_of_minimum y s a ha hya hmin
  refine ⟨generatedSheaf y s, fun p => ⟨⊤, trivial, ⟨?_⟩⟩⟩
  exact (Scheme.Modules.restrictFunctor (⊤ : (Spec (CommRingCat.of A)).Opens).ι).mapIso
    (asIso (generatedSection (A := A) y s a ha)).symm ≪≫
      Scheme.Modules.restrictUnitIso (⊤ : (Spec (CommRingCat.of A)).Opens).ι

end PiExponent.WeightedLocalSheaf

end

end OAI
end Source0514

-- Source: OAI/NumberTheory/PiExponent/Polynomials/WeightedMonomialPole.lean
section Source0515
/-
Modification notice for the LogTwo project.
Derived from openai/math (Apache-2.0), revision adc7f1241b42e322a6451854ab7e4b4c146bf78a.
Original source: lean/OAI/NumberTheory/PiExponent/Polynomials/WeightedMonomialPole.lean
Changes: Convert module/import declarations to the Lean 4.34 public module format.
See ../THIRD_PARTY_NOTICES.txt for provenance and the recorded changes.
-/

namespace OAI

noncomputable section
open scoped BigOperators
namespace PiExponent.WeightedMonomialPole

open WeightedCurveDegree WeightedPolynomialPole PolynomialPoleBound

variable {K ι : Type*} [Field K] [Fintype ι]

theorem coordinateOrder_le_realValuation (v : AddValuation K (WithTop ℤ)) (x : K) :
    ((coordinateOrder v x : ℝ) : WithTop ℝ) ≤ realValuation v x := by
  by_cases hx : x = 0
  · simp [hx]
  · rw [realValuation_of_ne_zero v x hx]

theorem realValuation_le_iff (v : AddValuation K (WithTop ℤ)) (x y : K) :
    realValuation v x ≤ realValuation v y ↔ v x ≤ v y :=
  (Int.cast_strictMono (R := ℝ)).withTop_map.le_iff_le

theorem monomial_order_lower (v : AddValuation K (WithTop ℤ)) (x : ι → K)
    (w : ι → ℚ) (hw : ∀ i, 0 < w i) (a : ι → ℕ) {R : ℚ}
    (ha : (∑ i, w i * (a i : ℚ)) ≤ R) :
    ((-(R : ℝ) * (coordinatePole v x w : ℝ) : ℝ) : WithTop ℝ) ≤
      realValuation v (∏ i, x i ^ a i) := by
  have hq : -R * coordinatePole v x w ≤
      ∑ i, (a i : ℚ) * (coordinateOrder v (x i) : ℚ) := by
    have h := monomial_pole_le w (fun i => (coordinateOrder v (x i) : ℚ)) hw a ha
    change -(∑ i, (a i : ℚ) * (coordinateOrder v (x i) : ℚ)) ≤ R * coordinatePole v x w at h
    linarith
  have hr : -(R : ℝ) * (coordinatePole v x w : ℝ) ≤
      ∑ i, (a i : ℝ) * (coordinateOrder v (x i) : ℝ) := by exact_mod_cast hq
  apply (WithTop.coe_le_coe.mpr hr).trans
  rw [WithTop.coe_sum, valuation_prod]
  apply Finset.sum_le_sum
  intro i hi
  rw [(realValuation v).map_pow]
  simpa only [← WithTop.coe_nsmul, nsmul_eq_mul] using
    nsmul_le_nsmul_right (coordinateOrder_le_realValuation v (x i)) (a i)

theorem coordinateOrder_pow (v : AddValuation K (WithTop ℤ))
    (x : K) (hx : x ≠ 0) (n : ℕ) :
    coordinateOrder v (x ^ n) = (n : ℤ) * coordinateOrder v x := by
  rw [coordinateOrder, dite_eq_right (pow_ne_zero n hx), coordinateOrder, dite_eq_right hx]
  have hu : Units.mk0 (x ^ n) (pow_ne_zero n hx) = (Units.mk0 x hx) ^ n := by
    apply Units.ext
    rfl
  rw [hu, integerOrder_pow]

theorem exists_attaining_monomial [DecidableEq ι]
    (v : AddValuation K (WithTop ℤ)) (x : ι → K)
    (w : ι → ℚ) (hw : ∀ i, 0 < w i) {R : ℚ} (_hR : 0 < R)
    (powers : ι → ℕ) (hpowers : ∀ i, w i * (powers i : ℚ) = R)
    (M : Finset (ι → ℕ)) (hzero : 0 ∈ M)
    (hpure : ∀ i, Pi.single i (powers i) ∈ M) :
    ∃ a ∈ M, (∏ i, x i ^ a i) ≠ 0 ∧
      (coordinateOrder v (∏ i, x i ^ a i) : ℚ) = -R * coordinatePole v x w := by
  by_cases hD : coordinatePole v x w = 0
  · refine ⟨0, hzero, by simp, ?_⟩
    simp [hD, coordinateOrder, integerOrder_one]
  have hDpos : 0 < coordinatePole v x w :=
    lt_of_le_of_ne (weightedPole_nonneg w _) (Ne.symm hD)
  obtain ⟨o, _, ho⟩ := Finset.exists_mem_eq_sup'
    (s := (Finset.univ : Finset (Option ι))) Finset.univ_nonempty
    (fun i => i.elim 0 (fun j => -(coordinateOrder v (x j) : ℚ) / w j))
  change coordinatePole v x w = _ at ho
  cases o with
  | none => exact False.elim (hD ho)
  | some i =>
    change coordinatePole v x w = -(coordinateOrder v (x i) : ℚ) / w i at ho
    have hx : x i ≠ 0 := by
      intro hx
      have hh : coordinatePole v x w = 0 := by simpa [hx, coordinateOrder] using ho
      exact hD hh
    have heval : (∏ j, x j ^ (Pi.single i (powers i) : ι → ℕ) j) = x i ^ powers i := by
      simp [Pi.single_apply]
    refine ⟨Pi.single i (powers i), hpure i, ?_, ?_⟩
    · rw [heval]
      exact pow_ne_zero _ hx
    · rw [heval, coordinateOrder_pow v (x i) hx]
      push_cast
      change (powers i : ℚ) * (coordinateOrder v (x i) : ℚ) = -R * coordinatePole v x w
      rw [ho, ← hpowers i]
      field_simp [ne_of_gt (hw i)]

theorem exists_minimizing_monomial [DecidableEq ι]
    (v : AddValuation K (WithTop ℤ)) (x : ι → K)
    (w : ι → ℚ) (hw : ∀ i, 0 < w i) {R : ℚ} (hR : 0 < R)
    (powers : ι → ℕ) (hpowers : ∀ i, w i * (powers i : ℚ) = R)
    (M : Finset (ι → ℕ)) (hzero : 0 ∈ M)
    (hpure : ∀ i, Pi.single i (powers i) ∈ M)
    (hbudget : ∀ a ∈ M, (∑ i, w i * (a i : ℚ)) ≤ R) :
    ∃ a ∈ M, (∏ i, x i ^ a i) ≠ 0 ∧
      (coordinateOrder v (∏ i, x i ^ a i) : ℚ) = -R * coordinatePole v x w ∧
      ∀ b ∈ M, v (∏ i, x i ^ a i) ≤ v (∏ i, x i ^ b i) := by
  obtain ⟨a,ha,han,hao⟩ := exists_attaining_monomial v x w hw hR powers hpowers M hzero hpure
  refine ⟨a,ha,han,hao,?_⟩
  intro b hb
  apply (realValuation_le_iff v _ _).mp
  rw [realValuation_of_ne_zero v _ han]
  have he : (coordinateOrder v (∏ i, x i ^ a i) : ℝ) =
      -(R : ℝ) * (coordinatePole v x w : ℝ) := by exact_mod_cast hao
  rw [he]
  exact monomial_order_lower v x w hw b (hbudget b hb)

end PiExponent.WeightedMonomialPole

end

end OAI
end Source0515

-- Source: OAI/NumberTheory/PiExponent/Approximation/WeightedSectionOrder.lean
section Source0516
-- Modified in this edition: unused plain lemmas removed; see reduction.json.
/-
Modification notice for the LogTwo project.
Derived from openai/math (Apache-2.0), revision adc7f1241b42e322a6451854ab7e4b4c146bf78a.
Original source: lean/OAI/NumberTheory/PiExponent/Approximation/WeightedSectionOrder.lean
Changes: Convert module/import declarations to the Lean 4.34 public module format.
See ../THIRD_PARTY_NOTICES.txt for provenance and the recorded changes.
-/

namespace OAI

noncomputable section
open CategoryTheory AlgebraicGeometry
open PiExponentSeshadri.Geometry PiExponentSeshadri.Frames
open PiExponent.WeightedLocalSheaf PiExponent.WeightedLocalLattice
open PiExponent.LocalSectionOrder PiExponent.CurveLocalOrder
open scoped BigOperators

namespace PiExponent.WeightedSectionOrder

theorem coefficient_tilde_end {A : Type} [CommRing A] (f : A →ₗ[A] A) :
    (Scheme.ΓSpecIso (CommRingCat.of A)).hom
      (endValue (tildeSelf.inv ≫
        (tilde.functor (CommRingCat.of A)).map (ModuleCat.ofHom f) ≫ tildeSelf.hom)) = f 1 := by
  have h := ConcreteCategory.congr_hom
    (tilde.toOpen_map_app (R := CommRingCat.of A) (ModuleCat.ofHom f) ⊤) (1 : A)
  change ((tilde.functor (CommRingCat.of A)).map (ModuleCat.ofHom f)).app ⊤
    ((Scheme.ΓSpecIso (CommRingCat.of A)).inv 1) =
      (Scheme.ΓSpecIso (CommRingCat.of A)).inv (f 1) at h
  rw [map_one] at h
  change (Scheme.ΓSpecIso (CommRingCat.of A)).hom
    (((tilde.functor (CommRingCat.of A)).map (ModuleCat.ofHom f)).app ⊤ (1 : Γ(Spec (CommRingCat.of A), ⊤))) = f 1
  rw [h]
  simp

variable {A K : Type} {ι : Type*} [CommRing A] [IsDomain A]
  [Field K] [Algebra A K] [IsFractionRing A K]

def coordinateBasis (y : ι → K) (s : Finset ι) (a : ι) (ha : a ∈ s)
    (hya : y a ≠ 0) (hspan : generatedLattice A y s = Submodule.span A {y a}) :
    A ≃ₗ[A] generatedLattice A y s :=
  LinearEquiv.ofBijective (generatedSectionMap y s a ha)
    (generatedSectionMap_bijective_of_span y s a ha hya hspan)

def coordinateFrame (y : ι → K) (s : Finset ι) (a : ι) (ha : a ∈ s)
    (hya : y a ≠ 0) (hspan : generatedLattice A y s = Submodule.span A {y a}) :
    generatedSheaf (A := A) y s ≅ O (Spec (CommRingCat.of A)) :=
  (tilde.functor (CommRingCat.of A)).mapIso
    (coordinateBasis y s a ha hya hspan).symm.toModuleIso ≪≫ tildeSelf

theorem coordinate_coefficient (y : ι → K) (s : Finset ι) (a : ι) (ha : a ∈ s)
    (hya : y a ≠ 0) (hspan : generatedLattice A y s = Submodule.span A {y a})
    (b : ι) (hb : b ∈ s) :
    localCoefficient (coordinateFrame y s a ha hya hspan) (generatedSection y s b hb) =
      (coordinateBasis y s a ha hya hspan).symm
        ⟨y b, Submodule.subset_span ⟨b, hb, rfl⟩⟩ := by
  unfold localCoefficient coefficient coordinateFrame generatedSection
  erw [Iso.trans_hom, Functor.mapIso_hom, Category.assoc, ← Functor.map_comp_assoc]
  have h := coefficient_tilde_end
    ((coordinateBasis y s a ha hya hspan).symm.toLinearMap.comp
      (generatedSectionMap y s b hb))
  simp only [LinearMap.comp_apply] at h
  simp [generatedSectionMap] at h
  exact h

theorem coordinate_coefficient_image (y : ι → K) (s : Finset ι) (a : ι) (ha : a ∈ s)
    (hya : y a ≠ 0) (hspan : generatedLattice A y s = Submodule.span A {y a})
    (b : ι) (hb : b ∈ s) :
    algebraMap A K (localCoefficient (coordinateFrame y s a ha hya hspan)
      (generatedSection y s b hb)) = y b / y a := by
  rw [coordinate_coefficient, eq_div_iff hya]
  have h := (coordinateBasis y s a ha hya hspan).apply_symm_apply
    ⟨y b, Submodule.subset_span ⟨b, hb, rfl⟩⟩
  have hh := congrArg (fun z : generatedLattice A y s => (z : K)) h
  change (coordinateBasis y s a ha hya hspan).symm
    ⟨y b, Submodule.subset_span ⟨b, hb, rfl⟩⟩ • y a = y b at hh
  simpa only [Algebra.smul_def] using hh

theorem coordinate_coefficient_ne_zero (y : ι → K) (s : Finset ι) (a : ι) (ha : a ∈ s)
    (hya : y a ≠ 0) (hspan : generatedLattice A y s = Submodule.span A {y a})
    (b : ι) (hb : b ∈ s) (hyb : y b ≠ 0) :
    localCoefficient (coordinateFrame y s a ha hya hspan) (generatedSection y s b hb) ≠ 0 := by
  intro h
  have hr := coordinate_coefficient_image y s a ha hya hspan b hb
  rw [h, map_zero] at hr
  exact div_ne_zero hyb hya hr.symm

def sectionZeroEuler [Algebra ℂ A]
    {M : (Spec (CommRingCat.of A)).Modules}
    (e : M ≅ O (Spec (CommRingCat.of A))) (t : O (Spec (CommRingCat.of A)) ⟶ M)
    (d : ℕ) : ℤ :=
  eulerCharacteristic (CurveZeroEuler.algebraStructureMap
    (A ⧸ Ideal.span {localCoefficient e t})) d (structureSheaf (zeroScheme e t))

end PiExponent.WeightedSectionOrder

end

end OAI
end Source0516

-- Source: OAI/NumberTheory/PiExponent/Geometry/ProjectiveLocalCoefficients.lean
section Source0517
/-
Modification notice for the LogTwo project.
Derived from openai/math (Apache-2.0), revision adc7f1241b42e322a6451854ab7e4b4c146bf78a.
Original source: lean/OAI/NumberTheory/PiExponent/Geometry/ProjectiveLocalCoefficients.lean
Changes: Convert module/import declarations to the Lean 4.34 public module format.
See ../THIRD_PARTY_NOTICES.txt for provenance and the recorded changes.
-/

namespace OAI

noncomputable section
open CategoryTheory AlgebraicGeometry MvPolynomial
open PiExponentSeshadri.Geometry PiExponentSeshadri.Frames
open PiExponentSeshadri.Projective PiExponentSeshadri.LineBundleGluing

namespace PiExponent.ProjectiveLocalCoefficients

variable {R A σ : Type} [CommRing R] [CommRing A]
attribute [local instance] MvPolynomial.gradedAlgebra

def normalizedMap (k : R →+* A) (z : σ → A) (i : σ) (hi : z i = 1) :
    Spec (CommRingCat.of A) ⟶ ProjectiveO1.projectiveSpace R σ :=
  fromUnitCoordinate (eval₂Hom k z) (by decide) (poly_X_mem i)
    (by simpa only [eval₂Hom_X', hi] using (isUnit_one : IsUnit (1 : A)))

theorem chart_inverse_ratio (i j : σ) :
    (Proj.basicOpenIsoSpec (PolyGrade R σ) (X i) (poly_X_mem i) (by decide)).inv.appTop
      (ProjectiveO1.chartRatios i j) =
        (Scheme.ΓSpecIso (CommRingCat.of (PolyChart (R := R) i))).inv
          (chartCoordinate (R := R) i j) := by
  have h := ProjectiveO1.coordinateOpen_pullback (R := R) i
  have hc := congrArg (fun q => q ≫
    (Proj.basicOpenIsoSpec (PolyGrade R σ) (X i) (poly_X_mem i) (by decide)).inv.appTop) h
  simp only [Category.assoc, ← Scheme.Hom.comp_appTop,
    Iso.inv_hom_id, Scheme.Hom.id_appTop, Category.comp_id] at hc
  have hv := ConcreteCategory.congr_hom hc (chartCoordinate (R := R) i j)
  change (Scheme.ΓSpecIso (CommRingCat.of (PolyChart (R := R) i))).inv
      (chartCoordinate (R := R) i j) =
    (Proj.basicOpenIsoSpec (PolyGrade R σ) (X i) (poly_X_mem i) (by decide)).inv.appTop
      ((ProjectiveO1.coordinateOpen i).topIso.inv
        (Proj.awayToSection (PolyGrade R σ) (X i) (chartCoordinate (R := R) i j))) at hv
  rw [ProjectiveO1.awayToSection_coordinate] at hv
  exact hv.symm

theorem exists_frame_coordinate_coefficients
    (k : R →+* A) (z : σ → A) (i : σ) (hi : z i = 1) :
    ∃ e : (Scheme.Modules.pullback (normalizedMap k z i hi)).obj
        (ProjectiveO1.lineBundle (R := R) (σ := σ)).sheaf ≅ O (Spec (CommRingCat.of A)),
      ∀ j : σ,
        LocalSectionOrder.localCoefficient (A := A) e
          (pullbackSection (normalizedMap k z i hi) (ProjectiveO1.coordinateSection j)) = z j := by
  let U := ProjectiveO1.coordinateOpen (R := R) i
  let ev := evalAway (𝒜 := PolyGrade R σ) (eval₂Hom k z) (X i)
    (by simpa only [eval₂Hom_X', hi] using (isUnit_one : IsUnit (1 : A)))
  let q := Spec.map (CommRingCat.ofHom ev)
  let g := q ≫ (Proj.basicOpenIsoSpec (PolyGrade R σ) (X i) (poly_X_mem i) (by decide)).inv
  have hf : normalizedMap k z i hi = g ≫ U.ι := by
    simp only [normalizedMap, fromUnitCoordinate, Proj.awayι, g, q, ev, U, Category.assoc]
  rw [hf]
  obtain ⟨e, he⟩ := PullbackFrameCoefficient.exists_frame_of_factors_through_open U g
    (openFrame ProjectiveO1.coordinateCocycle i U le_rfl)
  refine ⟨e, fun j => ?_⟩
  have hcoef : coefficient (openFrame ProjectiveO1.coordinateCocycle i U le_rfl)
      (restrictSection U.ι (ProjectiveO1.coordinateSection j)) =
        ProjectiveO1.chartRatios i j := by
    exact ProjectiveO1.coordinateSection_coefficient_eq i j U le_rfl
  have hj := he (ProjectiveO1.coordinateSection j)
  rw [hcoef] at hj
  change coefficient e (pullbackSection (g ≫ U.ι) (ProjectiveO1.coordinateSection j)) =
    q.appTop ((Proj.basicOpenIsoSpec (PolyGrade R σ) (X i) (poly_X_mem i) (by decide)).inv.appTop
      (ProjectiveO1.chartRatios i j)) at hj
  rw [chart_inverse_ratio] at hj
  unfold LocalSectionOrder.localCoefficient
  erw [hj]
  change (q.appTop ≫ (Scheme.ΓSpecIso (CommRingCat.of A)).hom)
    ((Scheme.ΓSpecIso (CommRingCat.of (PolyChart (R := R) i))).inv
      (chartCoordinate (R := R) i j)) = z j
  rw [Scheme.ΓSpecIso_naturality]
  change ev ((Scheme.ΓSpecIso (CommRingCat.of (PolyChart (R := R) i))).hom
    ((Scheme.ΓSpecIso (CommRingCat.of (PolyChart (R := R) i))).inv
      (chartCoordinate (R := R) i j))) = z j
  rw [Iso.inv_hom_id_apply]
  exact evalAway_coordinate i k z hi j

end PiExponent.ProjectiveLocalCoefficients

end

end OAI
end Source0517

-- Source: OAI/NumberTheory/PiExponent/Geometry/ProjectiveLatticePullback.lean
section Source0518
-- Modified in this edition: unused plain lemmas removed; see reduction.json.
/-
Modification notice for the LogTwo project.
Derived from openai/math (Apache-2.0), revision adc7f1241b42e322a6451854ab7e4b4c146bf78a.
Original source: lean/OAI/NumberTheory/PiExponent/Geometry/ProjectiveLatticePullback.lean
Changes: Convert module/import declarations to the Lean 4.34 public module format.
See ../THIRD_PARTY_NOTICES.txt for provenance and the recorded changes.
-/

namespace OAI

noncomputable section
open CategoryTheory AlgebraicGeometry
open PiExponentSeshadri.Geometry PiExponentSeshadri.Frames
open PiExponent.WeightedLocalSheaf PiExponent.WeightedLocalLattice
open PiExponent.WeightedSectionOrder PiExponent.LocalSectionOrder

namespace PiExponent.ProjectiveLatticePullback

variable {R A K σ : Type} [CommRing R] [CommRing A] [IsDomain A]
  [Field K] [Algebra A K] [IsFractionRing A K] [Fintype σ]

def latticeCoordinates (y : σ → K) (a : σ) (hya : y a ≠ 0)
    (hspan : generatedLattice A y Finset.univ = Submodule.span A {y a}) (b : σ) : A :=
  localCoefficient (A := A) (coordinateFrame y Finset.univ a (Finset.mem_univ a) hya hspan)
    (generatedSection y Finset.univ b (Finset.mem_univ b))

theorem latticeCoordinates_self (y : σ → K) (a : σ) (hya : y a ≠ 0)
    (hspan : generatedLattice A y Finset.univ = Submodule.span A {y a}) :
    latticeCoordinates y a hya hspan a = 1 := by
  apply IsFractionRing.injective A K
  rw [map_one]
  exact (coordinate_coefficient_image y Finset.univ a (Finset.mem_univ a) hya hspan
    a (Finset.mem_univ a)).trans (div_self hya)

def latticeProjectiveMap (k : R →+* A) (y : σ → K) (a : σ) (hya : y a ≠ 0)
    (hspan : generatedLattice A y Finset.univ = Submodule.span A {y a}) :
    Spec (CommRingCat.of A) ⟶ ProjectiveO1.projectiveSpace R σ :=
  ProjectiveLocalCoefficients.normalizedMap k (latticeCoordinates y a hya hspan) a
    (latticeCoordinates_self y a hya hspan)

end PiExponent.ProjectiveLatticePullback

end

end OAI
end Source0518

-- Source: OAI/NumberTheory/PiExponent/Geometry/ProjectiveSpaceBasics.lean
section Source0519
/-
Modification notice for the LogTwo project.
Derived from openai/math (Apache-2.0), revision adc7f1241b42e322a6451854ab7e4b4c146bf78a.
Original source: lean/OAI/NumberTheory/PiExponent/Geometry/ProjectiveSpaceBasics.lean
Changes: Convert module/import declarations to the Lean 4.34 public module format.
See ../THIRD_PARTY_NOTICES.txt for provenance and the recorded changes.
-/

namespace OAI

namespace PiExponent.ProjectiveO1
noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace
open PiExponentSeshadri.Geometry
variable (R σ : Type) [CommRing R]

instance projectiveSpace_noetherian [IsNoetherianRing R] [Finite σ] :
    IsNoetherian (projectiveSpace R σ) := by
  let : IsLocallyNoetherian (projectiveSpace R σ) :=
    LocallyOfFiniteType.isLocallyNoetherian (polynomialProjectiveProjection R σ)
  let : CompactSpace (projectiveSpace R σ) :=
    QuasiCompact.compactSpace_of_compactSpace (polynomialProjectiveProjection R σ)
  exact {}

instance projectiveSpace_separated [Finite σ] : (projectiveSpace R σ).IsSeparated := by
  constructor
  have h : IsSeparated (polynomialProjectiveProjection R σ ≫
      terminal.from (Spec (CommRingCat.of R))) := inferInstance
  simpa only [terminal.comp_from] using h

instance projectiveSpace_diagonal_affine [Finite σ] :
    IsAffineHom (pullback.diagonal (terminal.from (projectiveSpace R σ))) := by
  infer_instance

theorem scalars_eq_baseScalars :
    scalars (R := ℂ) (σ := σ) = baseScalars (polynomialProjectiveProjection ℂ σ) := rfl

end
end PiExponent.ProjectiveO1

end OAI
end Source0519

-- Source: OAI/NumberTheory/PiExponent/Geometry/CurveGlobalMonomialLocal.lean
section Source0520
-- Modified in this edition: unused plain lemmas removed; see reduction.json.
/-
Modification notice for the LogTwo project.
Derived from openai/math (Apache-2.0), revision adc7f1241b42e322a6451854ab7e4b4c146bf78a.
Original source: lean/OAI/NumberTheory/PiExponent/Geometry/CurveGlobalMonomialLocal.lean
Changes: Convert module/import declarations to the Lean 4.34 public module format.
See ../THIRD_PARTY_NOTICES.txt for provenance and the recorded changes.
-/

namespace OAI

noncomputable section

namespace PiExponent.ProjectiveLocalCoefficients
open AlgebraicGeometry CategoryTheory MvPolynomial
open PiExponentSeshadri.Projective
attribute [local instance] MvPolynomial.gradedAlgebra
variable {R A B σ : Type} [CommRing R] [CommRing A] [CommRing B]

theorem normalizedMap_natural (h : A →+* B) (k : R →+* A)
    (y : σ → A) (i : σ) (hi : y i = 1) :
    Spec.map (CommRingCat.ofHom h) ≫ normalizedMap k y i hi =
      normalizedMap (h.comp k) (fun j => h (y j)) i (by rw [hi, map_one]) := by
  unfold normalizedMap
  rw [fromUnitCoordinate_natural]
  congr 1
  exact coordinates_eval_natural h k y

theorem normalizedMap_scale (k : R →+* A) (a b : σ → A)
    (i j : σ) (hi : a i = 1) (hj : b j = 1)
    (c : Aˣ) (hscale : ∀ q, b q = (c : A) * a q) :
    normalizedMap k a i hi = normalizedMap k b j hj := by
  let f := eval₂Hom k a
  let g := eval₂Hom k b
  have hf : IsUnit (f (MvPolynomial.X (R := R) i)) := by
    simpa only [f, eval₂Hom_X', hi] using (isUnit_one : IsUnit (1 : A))
  have hg : IsUnit (g (MvPolynomial.X (R := R) i)) := by
    simpa only [g, eval₂Hom_X', hscale i, hi, mul_one] using c.isUnit
  have hg' : IsUnit (g (MvPolynomial.X (R := R) j)) := by
    simpa only [g, eval₂Hom_X', hj] using (isUnit_one : IsUnit (1 : A))
  have H : ∀ n p, p ∈ homogeneousSubmodule σ R n →
      g p = (c : A) ^ n * f p := by
    intro n p hp
    change eval₂ k b p = _
    have hb : b = fun q => (c : A) * a q := funext hscale
    rw [hb]
    exact homogeneous_eval₂_scale hp k a c
  unfold normalizedMap
  exact (fromUnitCoordinate_scale (𝒜 := homogeneousSubmodule σ R) (d := 1) f (by decide) (coordinates_X_mem (K := R) i)
    hf g hg c H).trans
      (fromUnitCoordinate_eq (𝒜 := homogeneousSubmodule σ R) (d := 1) (e := 1) g (by decide) (by decide)
        (coordinates_X_mem (K := R) i) (coordinates_X_mem (K := R) j) hg hg')

end PiExponent.ProjectiveLocalCoefficients

namespace PiExponent.CurveGlobalMonomialLocal
open AlgebraicGeometry CategoryTheory MvPolynomial
open ProjectiveLatticePullback ProjectiveLocalCoefficients WeightedSectionOrder
open WeightedLocalLattice PiExponentSeshadri.Projective
open scoped BigOperators
attribute [local instance] MvPolynomial.gradedAlgebra

theorem latticeProjectiveMap_generic
    {F A E σ : Type} [CommRing F] [CommRing A] [IsDomain A]
    [Field E] [Algebra A E] [IsFractionRing A E] [Fintype σ]
    (k : F →+* A) (y : σ → E) (i : σ) (hi : y i ≠ 0)
    (hspan : generatedLattice A y Finset.univ = Submodule.span A {y i})
    (z : σ) (hz : y z = 1) :
    Spec.map (CommRingCat.ofHom (algebraMap A E)) ≫ latticeProjectiveMap k y i hi hspan =
      normalizedMap ((algebraMap A E).comp k) y z hz := by
  rw [latticeProjectiveMap, normalizedMap_natural]
  apply normalizedMap_scale _ _ y i z _ hz (Units.mk0 (y i) hi)
  intro b
  change y b = y i * algebraMap A E (latticeCoordinates y i hi hspan b)
  rw [show algebraMap A E (latticeCoordinates y i hi hspan b) = y b / y i from
    coordinate_coefficient_image y Finset.univ i (Finset.mem_univ i) hi hspan b (Finset.mem_univ b)]
  field_simp

def monomialCoordinates {F E ι σ : Type} [CommRing F] [CommRing E] [Algebra F E]
    (a : σ → ι →₀ ℕ) (x : ι → E) (s : σ) : E :=
  eval₂Hom (algebraMap F E) x (monomial (a s) 1)

theorem monomialCoordinates_eq_prod
    {F E ι σ : Type} [CommRing F] [CommRing E] [Algebra F E] [Fintype ι]
    (a : σ → ι →₀ ℕ) (x : ι → E) (s : σ) :
    monomialCoordinates (F := F) a x s = ∏ j, x j ^ (a s j) := by
  rw [monomialCoordinates, eval₂Hom_monomial, map_one, one_mul]
  exact Finsupp.prod_fintype _ _ (fun _ => pow_zero _)

@[simp] theorem monomialCoordinates_zero
    {F E ι σ : Type} [CommRing F] [CommRing E] [Algebra F E]
    (a : σ → ι →₀ ℕ) (x : ι → E) (z : σ) (hz : a z = 0) :
    monomialCoordinates (F := F) a x z = 1 := by
  simp [monomialCoordinates, hz]

theorem genericMonomialMap_comp_projectiveMonomialMap
    {F E ι σ : Type} [CommRing F] [CommRing E] [Algebra F E]
    (a : σ → ι →₀ ℕ) (z : σ) (hz : a z = 0)
    (coordinate : ι → σ) (hcoordinate : ∀ i, a (coordinate i) = Finsupp.single i 1)
    (x : ι → E) :
    CurveMonomialMap.genericMonomialMap a z hz coordinate hcoordinate x ≫
      WeightedCompactification.projectiveMonomialMap a =
      normalizedMap (algebraMap F E) (monomialCoordinates (F := F) a x) z
        (monomialCoordinates_zero a x z hz) := by
  have heval : (eval₂Hom (algebraMap F E) x).comp
        (WeightedCompactification.affineMonomialMap (R := F) a) =
      eval₂Hom (algebraMap F E) (monomialCoordinates (F := F) a x) := by
    apply MvPolynomial.ringHom_ext
    · intro r
      simp [WeightedCompactification.affineMonomialMap]
    · intro b
      simp [WeightedCompactification.affineMonomialMap, monomialCoordinates]
  rw [CurveMonomialMap.genericMonomialMap, Category.assoc,
    WeightedCompactification.affineChartMap_comp_projectiveMonomialMap,
    fromUnitCoordinate_natural]
  unfold normalizedMap
  congr 1

theorem centerMorphism_eq_latticeProjectiveMap
    {F E σ : Type} [Field F] [Field E] [Algebra F E] [Fintype σ]
    (f : E) (hf : Transcendental F f)
    [FiniteDimensional (IntermediateField.adjoin F {f}) E]
    (g : CurveNormalizationModel.parameterCurve f hf ⟶ ProjectiveO1.projectiveSpace F σ)
    (y : σ → E) (z : σ) (hz : y z = 1)
    (hg : CurveNormalizationModel.parameterCurveGenericPoint f hf ≫ g =
      normalizedMap (algebraMap F E) y z hz)
    (p : CurveValuationCenter.NormalizedPlace F E) (i : σ) (hi : y i ≠ 0)
    (hspan : generatedLattice (PlaceValuationRing.ring p) y Finset.univ =
      Submodule.span (PlaceValuationRing.ring p) {y i}) :
    CurvePlaceCenter.centerMorphism f hf p ≫ g =
      latticeProjectiveMap (algebraMap F (PlaceValuationRing.ring p)) y i hi hspan := by
  apply CurvePlaceCenter.centerMorphism_comp_eq_of_generic f hf p
  rw [latticeProjectiveMap_generic _ y i hi hspan z hz, hg]
  rfl

end PiExponent.CurveGlobalMonomialLocal

end

end OAI
end Source0520

-- Source: OAI/NumberTheory/PiExponent/Geometry/ProjectiveLatticeOrder.lean
section Source0521
/-
Modification notice for the LogTwo project.
Derived from openai/math (Apache-2.0), revision adc7f1241b42e322a6451854ab7e4b4c146bf78a.
Original source: lean/OAI/NumberTheory/PiExponent/Geometry/ProjectiveLatticeOrder.lean
Changes: Convert module/import declarations to the Lean 4.34 public module format.
See ../THIRD_PARTY_NOTICES.txt for provenance and the recorded changes.
-/

namespace OAI

noncomputable section
open CategoryTheory AlgebraicGeometry
open PiExponentSeshadri.Geometry PiExponentSeshadri.Frames
open PiExponent.WeightedLocalSheaf PiExponent.WeightedLocalLattice
open PiExponent.WeightedSectionOrder PiExponent.LocalSectionOrder
open PiExponent.ProjectiveLatticePullback PiExponent.CurveLocalOrder

namespace PiExponent.ProjectiveLatticeOrder

variable {R A K σ : Type} [CommRing R] [CommRing A] [IsDomain A]
  [IsDiscreteValuationRing A] [Field K] [Algebra A K] [IsFractionRing A K] [Fintype σ]

theorem latticeCoordinates_order (y : σ → K) (a : σ) (hya : y a ≠ 0)
    (hspan : generatedLattice A y Finset.univ = Submodule.span A {y a})
    (b : σ) (hyb : y b ≠ 0) :
    ((IsDiscreteValuationRing.addVal A (latticeCoordinates y a hya hspan b)).toNat : ℤ) =
      WeightedPolynomialPole.coordinateOrder (fractionAddValuation A K) (y b) -
        WeightedPolynomialPole.coordinateOrder (fractionAddValuation A K) (y a) := by
  let c : A := latticeCoordinates y a hya hspan b
  have hc : c ≠ 0 := coordinate_coefficient_ne_zero y Finset.univ a
    (Finset.mem_univ a) hya hspan b (Finset.mem_univ b) hyb
  have hi := integerOrder_field_image_eq_length (K := K) hc
  have hu : Units.mk0 (algebraMap A K c)
      ((map_ne_zero_iff _ (IsFractionRing.injective A K)).mpr hc) =
      Units.mk0 (y b) hyb / Units.mk0 (y a) hya := by
    apply Units.ext
    simp only [Units.val_div_eq_div_val, Units.val_mk0]
    exact coordinate_coefficient_image y Finset.univ a (Finset.mem_univ a) hya hspan
      b (Finset.mem_univ b)
  rw [hu, WeightedCurveDegree.integerOrder_div, length_quotient_span_eq_addVal hc] at hi
  simpa only [WeightedPolynomialPole.coordinateOrder, dite_eq_right hyb, dite_eq_right hya] using hi.symm

theorem exists_frame_coordinate_orders
    (k : R →+* A) (y : σ → K) (a : σ) (hya : y a ≠ 0)
    (hspan : generatedLattice A y Finset.univ = Submodule.span A {y a}) :
    ∃ e : (Scheme.Modules.pullback (latticeProjectiveMap k y a hya hspan)).obj
      (ProjectiveO1.lineBundle (R := R) (σ := σ)).sheaf ≅ O (Spec (CommRingCat.of A)),
      ∀ b : σ, y b ≠ 0 →
      ((sectionOrder e (pullbackSection (latticeProjectiveMap k y a hya hspan)
        (ProjectiveO1.coordinateSection b))).toNat : ℤ) =
        WeightedPolynomialPole.coordinateOrder (fractionAddValuation A K) (y b) -
          WeightedPolynomialPole.coordinateOrder (fractionAddValuation A K) (y a) := by
  dsimp only [latticeProjectiveMap]
  obtain ⟨e, he⟩ := ProjectiveLocalCoefficients.exists_frame_coordinate_coefficients k
    (latticeCoordinates y a hya hspan) a (latticeCoordinates_self y a hya hspan)
  refine ⟨e, fun b hb => ?_⟩
  unfold sectionOrder
  rw [he]
  exact latticeCoordinates_order y a hya hspan b hb

end PiExponent.ProjectiveLatticeOrder

end

end OAI
end Source0521

-- Source: OAI/NumberTheory/PiExponent/Polynomials/CompositePullbackCoefficient.lean
section Source0522
/-
Modification notice for the LogTwo project.
Derived from openai/math (Apache-2.0), revision adc7f1241b42e322a6451854ab7e4b4c146bf78a.
Original source: lean/OAI/NumberTheory/PiExponent/Polynomials/CompositePullbackCoefficient.lean
Changes: Convert module/import declarations to the Lean 4.34 public module format.
See ../THIRD_PARTY_NOTICES.txt for provenance and the recorded changes.
-/

namespace OAI

noncomputable section
open AlgebraicGeometry CategoryTheory
open PiExponentSeshadri.Geometry PiExponentSeshadri.Frames

namespace PiExponent.CompositePullbackCoefficient

theorem exists_frame {X Y Z : Scheme.{0}} (f : X ⟶ Y) (g : Y ⟶ Z)
    {M : Z.Modules} (e : (Scheme.Modules.pullback (f ≫ g)).obj M ≅ O X) :
    ∃ e' : (Scheme.Modules.pullback f).obj ((Scheme.Modules.pullback g).obj M) ≅ O X,
      ∀ s : O Z ⟶ M,
      coefficient e' (pullbackSection f (pullbackSection g s)) =
        coefficient e (pullbackSection (f ≫ g) s) := by
  let F := Scheme.Modules.pullback g ⋙ Scheme.Modules.pullback f
  let G := Scheme.Modules.pullback (f ≫ g)
  let uF : F.obj (O Z) ≅ O X :=
    (Scheme.Modules.pullback f).mapIso (pullbackUnitIso g) ≪≫ pullbackUnitIso f
  obtain ⟨e', he'⟩ := PullbackFrameCoefficient.exists_frame_natIso_all
    F G (Scheme.Modules.pullbackComp f g) uF (pullbackUnitIso (f ≫ g)) e
  refine ⟨e', fun s => ?_⟩
  simpa only [F, G, uF, pullbackSection, Iso.trans_inv, Functor.mapIso_inv,
    Functor.comp_map, Functor.map_comp, Category.assoc] using he' s

end PiExponent.CompositePullbackCoefficient

end

end OAI
end Source0522

-- Source: OAI/NumberTheory/PiExponent/Geometry/CurveGlobalCoordinateOrder.lean
section Source0523
/-
Modification notice for the LogTwo project.
Derived from openai/math (Apache-2.0), revision adc7f1241b42e322a6451854ab7e4b4c146bf78a.
Original source: lean/OAI/NumberTheory/PiExponent/Geometry/CurveGlobalCoordinateOrder.lean
Changes: Convert module/import declarations to the Lean 4.34 public module format.
See ../THIRD_PARTY_NOTICES.txt for provenance and the recorded changes.
-/

namespace OAI

noncomputable section
open AlgebraicGeometry CategoryTheory
open PiExponentSeshadri.Geometry PiExponentSeshadri.Frames
open PiExponent.CurveNormalizationModel PiExponent.CurveModelPlaces
open PiExponent.CurveValuationCenter PiExponent.CurvePlaceCenter
open PiExponent.LocalSectionOrder PiExponent.WeightedLocalLattice
open PiExponent.ProjectiveLatticePullback PiExponent.WeightedPolynomialPole

namespace PiExponent.CurveGlobalCoordinateOrder

variable {E σ : Type} [Field E] [Algebra ℂ E] [Fintype σ]
variable (f : E) (hf : Transcendental ℂ f)
variable [FiniteDimensional (IntermediateField.adjoin ℂ {f}) E]
variable (g : parameterCurve f hf ⟶ ProjectiveO1.projectiveSpace ℂ σ)
variable (y : σ → E) (z : σ) (hz : y z = 1)
variable (hg : parameterCurveGenericPoint f hf ≫ g =
  ProjectiveLocalCoefficients.normalizedMap (algebraMap ℂ E) y z hz)
include hg

omit [Fintype σ] in
theorem coordinateSection_ne_zero (b : σ) (hb : y b ≠ 0) :
    pullbackSection g (ProjectiveO1.coordinateSection b) ≠ 0 := by
  have hex : ∃ e : (Scheme.Modules.pullback (parameterCurveGenericPoint f hf ≫ g)).obj
      (ProjectiveO1.lineBundle (R := ℂ) (σ := σ)).sheaf ≅ O (Spec (CommRingCat.of E)),
      localCoefficient e (pullbackSection (parameterCurveGenericPoint f hf ≫ g)
        (ProjectiveO1.coordinateSection b)) = y b := by
    rw [hg]
    obtain ⟨e, he⟩ := ProjectiveLocalCoefficients.exists_frame_coordinate_coefficients
      (algebraMap ℂ E) y z hz
    exact ⟨e, he b⟩
  obtain ⟨e, he⟩ := hex
  obtain ⟨e', he'⟩ := CompositePullbackCoefficient.exists_frame (parameterCurveGenericPoint f hf) g e
  have heq := congrArg (fun c => (Scheme.ΓSpecIso (CommRingCat.of E)).hom c)
    (he' (ProjectiveO1.coordinateSection b))
  change localCoefficient e' (pullbackSection (parameterCurveGenericPoint f hf)
    (pullbackSection g (ProjectiveO1.coordinateSection b))) =
    localCoefficient e (pullbackSection (parameterCurveGenericPoint f hf ≫ g)
      (ProjectiveO1.coordinateSection b)) at heq
  rw [he] at heq
  intro hs
  rw [hs] at heq
  have hz' : pullbackSection (parameterCurveGenericPoint f hf)
      (0 : O (parameterCurve f hf) ⟶
        (Scheme.Modules.pullback g).obj (ProjectiveO1.lineBundle (R := ℂ) (σ := σ)).sheaf) = 0 := by
    simp [pullbackSection]
  rw [hz', (localCoefficient_eq_zero_iff _ _).mpr rfl] at heq
  exact hb heq.symm

theorem coordinate_divisor_order (p : NormalizedPlace ℂ E) (i : σ) (hi : y i ≠ 0)
    (hspan : generatedLattice (PlaceValuationRing.ring p) y Finset.univ =
      Submodule.span (PlaceValuationRing.ring p) {y i})
    (b : σ) (hb : y b ≠ 0) :
    (CurvePlaceSectionDivisor.divisor f hf
      ((ProjectiveO1.lineBundle (R := ℂ) (σ := σ)).pullback g)
      (pullbackSection g (ProjectiveO1.coordinateSection b))
      (coordinateSection_ne_zero f hf g y z hz hg b hb) p : ℤ) =
      coordinateOrder p.valuation (y b) - coordinateOrder p.valuation (y i) := by
  have hmap := CurveGlobalMonomialLocal.centerMorphism_eq_latticeProjectiveMap
    f hf g y z hz hg p i hi hspan
  have hex : ∃ e : (Scheme.Modules.pullback (centerMorphism f hf p ≫ g)).obj
      (ProjectiveO1.lineBundle (R := ℂ) (σ := σ)).sheaf ≅
        O (Spec (CommRingCat.of (PlaceValuationRing.ring p))),
      ((sectionOrder e (pullbackSection (centerMorphism f hf p ≫ g)
        (ProjectiveO1.coordinateSection b))).toNat : ℤ) =
        coordinateOrder p.valuation (y b) - coordinateOrder p.valuation (y i) := by
    rw [hmap, PlaceValuationRing.valuation_eq_fractionAddValuation]
    obtain ⟨e, he⟩ := ProjectiveLatticeOrder.exists_frame_coordinate_orders
      (algebraMap ℂ (PlaceValuationRing.ring p)) y i hi hspan
    exact ⟨e, he b hb⟩
  obtain ⟨e, he⟩ := hex
  obtain ⟨e', he'⟩ := CompositePullbackCoefficient.exists_frame (centerMorphism f hf p) g e
  erw [CurvePlaceSectionOrder.divisor_eq_local_order f hf _ _ _ p e']
  have heq := congrArg
    (fun c => (Scheme.ΓSpecIso (CommRingCat.of (PlaceValuationRing.ring p))).hom c)
    (he' (ProjectiveO1.coordinateSection b))
  change localCoefficient e' (pullbackSection (centerMorphism f hf p)
    (pullbackSection g (ProjectiveO1.coordinateSection b))) =
      localCoefficient e (pullbackSection (centerMorphism f hf p ≫ g)
        (ProjectiveO1.coordinateSection b)) at heq
  unfold sectionOrder at he ⊢
  exact (congrArg (fun c : PlaceValuationRing.ring p =>
    ((IsDiscreteValuationRing.addVal (PlaceValuationRing.ring p) c).toNat : ℤ)) heq).trans he

end PiExponent.CurveGlobalCoordinateOrder

end

end OAI
end Source0523

-- Source: OAI/NumberTheory/PiExponent/Polynomials/WeightedMonomialLattice.lean
section Source0524
-- Modified in this edition: unused plain lemmas removed; see reduction.json.
/-
Modification notice for the LogTwo project.
Derived from openai/math (Apache-2.0), revision adc7f1241b42e322a6451854ab7e4b4c146bf78a.
Original source: lean/OAI/NumberTheory/PiExponent/Polynomials/WeightedMonomialLattice.lean
Changes: Convert module/import declarations to the Lean 4.34 public module format.
See ../THIRD_PARTY_NOTICES.txt for provenance and the recorded changes.
-/

namespace OAI

noncomputable section
open scoped BigOperators
namespace PiExponent.WeightedMonomialLattice

open CurveLocalOrder WeightedLocalLattice WeightedPolynomialPole WeightedMonomialPole

end PiExponent.WeightedMonomialLattice

end

end OAI
end Source0524

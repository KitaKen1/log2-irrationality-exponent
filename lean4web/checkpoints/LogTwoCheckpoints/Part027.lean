/- Generated rc4 checkpoint for LogTwo.
Modified from the reduced edition: new imports, separate module compilation,
and synchronous elaboration. Original source blocks and notices are retained.
See ../../../THIRD_PARTY_NOTICES.txt and ../../reduction.json.
-/
module
public import LogTwoCheckpoints.Part012
public import LogTwoCheckpoints.Part013
public import LogTwoCheckpoints.Part015
public import LogTwoCheckpoints.Part016
public import LogTwoCheckpoints.Part017
public import LogTwoCheckpoints.Part018
public import LogTwoCheckpoints.Part020
public import LogTwoCheckpoints.Part021
public import LogTwoCheckpoints.Part022
public import LogTwoCheckpoints.Part023
public import LogTwoCheckpoints.Part024
public import LogTwoCheckpoints.Part025
public import LogTwoCheckpoints.Part026
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Quasicoherent
public import Mathlib.Algebra.Group.ForwardDiff
public import Mathlib.AlgebraicGeometry.IdealSheaf.Functorial
public import Mathlib.AlgebraicGeometry.Modules.Sheaf
public import Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Basic
public import Mathlib.AlgebraicGeometry.ZariskisMainTheorem
public import Mathlib.Analysis.Asymptotics.SpecificAsymptotics
public import Mathlib.Analysis.Complex.Polynomial.Basic
public import Mathlib.Analysis.SpecialFunctions.Choose
public import Mathlib.Data.SetLike.Basic
public import Mathlib.RingTheory.KrullDimension.Field
public import Mathlib.RingTheory.KrullDimension.Polynomial
public import Mathlib.RingTheory.Polynomial.HilbertPoly
@[expose] public section
set_option Elab.async false

-- Source: OAI/NumberTheory/PiExponent/Geometry/CurveComponentMultiplicity.lean
section Source0675
-- Modified in this edition: unused plain lemmas removed; see reduction.json.
/-
Modification notice for the LogTwo project.
Derived from openai/math (Apache-2.0), revision adc7f1241b42e322a6451854ab7e4b4c146bf78a.
Original source: lean/OAI/NumberTheory/PiExponent/Geometry/CurveComponentMultiplicity.lean
Changes: Convert module/import declarations to the Lean 4.34 public module format.
See ../THIRD_PARTY_NOTICES.txt for provenance and the recorded changes.
-/

namespace OAI

namespace PiExponent.CurveCycle
noncomputable section
open AlgebraicGeometry CategoryTheory TopologicalSpace Topology

theorem generic_stalk_isArtinian {X : Scheme.{0}} [IsLocallyNoetherian X]
    (x : X) (hx : closure {x} ∈ irreducibleComponents X) :
    IsArtinianRing (X.presheaf.stalk x) := by
  wlog hX : ∃ R : CommRingCat, X = Spec R
  · obtain ⟨i,x,rfl⟩ := X.affineCover.exists_eq x
    let hNoeth : IsLocallyNoetherian (X.affineCover.X i) :=
      LocallyOfFiniteType.isLocallyNoetherian (X.affineCover.f i)
    have hloc := this x (by
      rw [(X.affineCover.f i).isOpenEmbedding.closure_eq_preimage_closure_image,
        Set.image_singleton]
      exact preimage_mem_irreducibleComponents hx (X.affineCover.f i).isOpenEmbedding
        ⟨X.affineCover.f i x, subset_closure rfl, _, rfl⟩) ⟨_,rfl⟩
    let := hloc
    exact (asIso ((X.affineCover.f i).stalkMap x)).commRingCatIsoToRingEquiv.symm.isArtinianRing
  obtain ⟨R,rfl⟩ := hX
  let : IsNoetherianRing ((Spec R).presheaf.stalk x) := inferInstance
  change PrimeSpectrum R at x
  change closure {x} ∈ irreducibleComponents (PrimeSpectrum R) at hx
  have hp : x.asIdeal ∈ minimalPrimes R := by
    rwa [← PrimeSpectrum.vanishingIdeal_singleton,
      PrimeSpectrum.vanishingIdeal_mem_minimalPrimes]
  let : Ring.KrullDimLE 0 ((Spec R).presheaf.stalk x) := by
    exact Ring.KrullDimLE.of_isLocalization x.asIdeal hp ((Spec.structureSheaf R).presheaf.stalk x)
  exact IsNoetherianRing.isArtinianRing_of_krullDimLE_zero

def componentMultiplicity (X : Scheme.{0}) (C : irreducibleComponents X) : ℕ :=
  (Module.length (X.presheaf.stalk (genericPoints.ofComponent C).val)
    (X.presheaf.stalk (genericPoints.ofComponent C).val)).toNat

def reducedComponent (X : Scheme.{0}) (C : irreducibleComponents X) : Scheme :=
  (Scheme.IdealSheafData.vanishingIdeal
    (⟨C.val,isClosed_of_mem_irreducibleComponents C.val C.property⟩ : Closeds X)).subscheme

def reducedComponentι (X : Scheme.{0}) (C : irreducibleComponents X) :
    reducedComponent X C ⟶ X :=
  (Scheme.IdealSheafData.vanishingIdeal
    (⟨C.val,isClosed_of_mem_irreducibleComponents C.val C.property⟩ : Closeds X)).subschemeι

instance reducedComponent_closed (X : Scheme.{0}) (C : irreducibleComponents X) :
    IsClosedImmersion (reducedComponentι X C) := by
  let I : X.IdealSheafData := Scheme.IdealSheafData.vanishingIdeal
    (⟨C.val,isClosed_of_mem_irreducibleComponents C.val C.property⟩ : Closeds X)
  change IsClosedImmersion I.subschemeι
  infer_instance

instance reducedComponent_integral (X : Scheme.{0}) (C : irreducibleComponents X) :
    IsIntegral (reducedComponent X C) := by
  let Z : Closeds X := ⟨C.val,isClosed_of_mem_irreducibleComponents C.val C.property⟩
  let I := Scheme.IdealSheafData.vanishingIdeal Z
  have hI : (I.support : Set X) = C.val := by
    simp only [I,Scheme.IdealSheafData.coe_support_vanishingIdeal]
    rfl
  let : IsReduced I.subscheme := NumericalAmpleness.isReduced_vanishingIdeal_subscheme Z
  let : IrreducibleSpace I.subscheme := by
    change IrreducibleSpace (I.support : Set X)
    rw [hI]
    exact Subtype.irreducibleSpace C.property.1
  change IsIntegral I.subscheme
  exact isIntegral_of_irreducibleSpace_of_isReduced _

def componentCurve {X : Scheme.{0}} (C : irreducibleComponents X)
    (hdim : topologicalKrullDim (C.val : Set X) = 1) :
    NumericalAmpleness.IntegralCurve X := by
  refine {
    scheme := reducedComponent X C
    embedding := reducedComponentι X C
    closedImmersion := inferInstance
    integral := inferInstance
    dimension := ?_ }
  change topologicalKrullDim
    ((Scheme.IdealSheafData.vanishingIdeal
      (⟨C.val,isClosed_of_mem_irreducibleComponents C.val C.property⟩ : Closeds X)).support : Set X) = 1
  have he : ((Scheme.IdealSheafData.vanishingIdeal
      (⟨C.val,isClosed_of_mem_irreducibleComponents C.val C.property⟩ : Closeds X)).support : Set X) = C.val := by
    simp only [Scheme.IdealSheafData.coe_support_vanishingIdeal]
    rfl
  rw [he]
  exact hdim

end
end PiExponent.CurveCycle

end OAI
end Source0675

-- Source: OAI/NumberTheory/PiExponent/Ampleness/ReducedComponentAmple.lean
section Source0676
/-
Modification notice for the LogTwo project.
Derived from openai/math (Apache-2.0), revision adc7f1241b42e322a6451854ab7e4b4c146bf78a.
Original source: lean/OAI/NumberTheory/PiExponent/Ampleness/ReducedComponentAmple.lean
Changes: Convert module/import declarations to the Lean 4.34 public module format.
See ../THIRD_PARTY_NOTICES.txt for provenance and the recorded changes.
-/

namespace OAI

noncomputable section
namespace PiExponent.ReducedComponentAmple
open AlgebraicGeometry CategoryTheory TopologicalSpace
open PiExponentSeshadri.Geometry

variable {R : Type} [CommRing R] [IsNoetherianRing R]

theorem isAmple_of_finite_closed_cover {ι : Type*} (s : Finset ι) :
    ∀ {X : Scheme.{0}} [IsNoetherian X] [IsReduced X]
      (p : X ⟶ Spec (CommRingCat.of R)) [IsProper p]
      (L H : LineBundle X), H.IsAmple →
      ∀ I : ι → X.IdealSheafData,
      (∀ x : X, ∃ i ∈ s, x ∈ (I i).support) →
      (∀ i ∈ s, (L.pullback (I i).subschemeι).IsAmple) → L.IsAmple := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    intro X _ _ p _ L H hH I hcover hample x U hx
    obtain ⟨i,hi,_⟩ := hcover x
    simp at hi
  | @insert i s hi ih =>
    intro X _ _ p _ L H hH I hcover hample
    let Z : Closeds X := s.sup (fun j => (I j).support)
    let J : X.IdealSheafData := Scheme.IdealSheafData.vanishingIdeal Z
    have hJsupport : J.support = Z := by
      ext x
      simp only [J, Scheme.IdealSheafData.coe_support_vanishingIdeal]
    let : IsLocallyNoetherian J.subscheme :=
      LocallyOfFiniteType.isLocallyNoetherian J.subschemeι
    let : CompactSpace J.subscheme :=
      QuasiCompact.compactSpace_of_compactSpace J.subschemeι
    let : IsNoetherian J.subscheme := {}
    let : IsReduced J.subscheme := NumericalAmpleness.isReduced_vanishingIdeal_subscheme Z
    have hH' : (H.pullback J.subschemeι).IsAmple :=
      LineBundle.IsAmple.pullback_closedImmersion H hH J.subschemeι
    have hcoverJ : ∀ x : J.subscheme, ∃ j ∈ s,
        x ∈ ((I j).comap J.subschemeι).support := by
      intro x
      have hx : J.subschemeι x ∈ Z := by
        rw [← hJsupport]
        exact x.property
      have hx' : ∃ j ∈ s, J.subschemeι x ∈ ((I j).support : Set X) := by
        change J.subschemeι x ∈ ((s.sup (fun j => (I j).support) : Closeds X) : Set X) at hx
        rw [Closeds.coe_finset_sup] at hx
        simpa only [Finset.sup_eq_iSup, Function.comp_apply, Set.iSup_eq_iUnion,
          Set.mem_iUnion, exists_prop] using hx
      obtain ⟨j,hj,hxj⟩ := hx'
      refine ⟨j,hj,?_⟩
      rw [Scheme.IdealSheafData.support_comap]
      change J.subschemeι x ∈ ((I j).support : Set X)
      exact hxj
    have hampleJ : ∀ j ∈ s,
        ((L.pullback J.subschemeι).pullback ((I j).comap J.subschemeι).subschemeι).IsAmple := by
      intro j hj
      exact isAmple_comap_restriction (I j) J.subschemeι L
        (hample j (Finset.mem_insert_of_mem hj))
    have hJ : (L.pullback J.subschemeι).IsAmple :=
      ih (J.subschemeι ≫ p) (L.pullback J.subschemeι) (H.pullback J.subschemeι)
        hH' (fun j => (I j).comap J.subschemeι) hcoverJ hampleJ
    apply PiExponentSeshadri.ComponentAmpleDescent.isAmple_of_reduced_closed_cover
      p L H hH (I i) J ?_ (hample i (Finset.mem_insert_self _ _)) hJ
    apply top_unique
    intro x _
    change x ∈ ((I i).support : Set X) ∪ (J.support : Set X)
    obtain ⟨j,hj,hxj⟩ := hcover x
    rcases Finset.mem_insert.mp hj with rfl | hj
    · exact Or.inl hxj
    · apply Or.inr
      rw [hJsupport]
      exact (Finset.le_sup (f := fun j => (I j).support) hj) hxj

theorem isAmple_of_reduced_components {X : Scheme.{0}} [IsNoetherian X] [IsReduced X]
    (p : X ⟶ Spec (CommRingCat.of R)) [IsProper p]
    (L H : LineBundle X) (hH : H.IsAmple)
    (hcomponents : ∀ C : irreducibleComponents X,
      (L.pullback (CurveCycle.reducedComponentι X C)).IsAmple) : L.IsAmple := by
  classical
  let : Finite (irreducibleComponents X) :=
    NoetherianSpace.finite_irreducibleComponents.to_subtype
  let : Fintype (irreducibleComponents X) := Fintype.ofFinite _
  let I : irreducibleComponents X → X.IdealSheafData := fun C =>
    Scheme.IdealSheafData.vanishingIdeal
      (⟨C.val, isClosed_of_mem_irreducibleComponents C.val C.property⟩ : Closeds X)
  apply isAmple_of_finite_closed_cover Finset.univ p L H hH I
  · intro x
    have hx : x ∈ ⋃₀ irreducibleComponents X := by
      rw [sUnion_irreducibleComponents]
      trivial
    obtain ⟨C,hC,hxC⟩ := hx
    refine ⟨⟨C,hC⟩, Finset.mem_univ _, ?_⟩
    change x ∈ ((I ⟨C,hC⟩).support : Set X)
    simp only [I, Scheme.IdealSheafData.coe_support_vanishingIdeal]
    change x ∈ C
    exact hxC
  · intro C _
    exact hcomponents C

end PiExponent.ReducedComponentAmple

end

end OAI
end Source0676

-- Source: OAI/NumberTheory/PiExponent/Ampleness/IntegralComponentAmple.lean
section Source0677
/-
Modification notice for the LogTwo project.
Derived from openai/math (Apache-2.0), revision adc7f1241b42e322a6451854ab7e4b4c146bf78a.
Original source: lean/OAI/NumberTheory/PiExponent/Ampleness/IntegralComponentAmple.lean
Changes: Convert module/import declarations to the Lean 4.34 public module format.
See ../THIRD_PARTY_NOTICES.txt for provenance and the recorded changes.
-/

namespace OAI

namespace PiExponent.NumericalAmpleness
noncomputable section
open AlgebraicGeometry CategoryTheory TopologicalSpace
open PiExponentSeshadri.Geometry
variable {X : Scheme.{0}}

theorem isAmple_of_integral_closed_restrictions [IsNoetherian X]
    (p : X ⟶ Spec (CommRingCat.of ℂ)) [IsProper p]
    (L H : LineBundle X) (hH : H.IsAmple)
    (hints : ∀ {Y : Scheme.{0}} [IsIntegral Y] (j : Y ⟶ X) [IsClosedImmersion j],
      (L.pullback j).IsAmple) : L.IsAmple := by
  let I : X.IdealSheafData := Scheme.IdealSheafData.vanishingIdeal (⊤ : Closeds X)
  have hI : I.support = ⊤ := by
    ext x
    simp only [I, Scheme.IdealSheafData.coe_support_vanishingIdeal]
  let : IsLocallyNoetherian I.subscheme :=
    LocallyOfFiniteType.isLocallyNoetherian I.subschemeι
  let : CompactSpace I.subscheme := QuasiCompact.compactSpace_of_compactSpace I.subschemeι
  let : IsNoetherian I.subscheme := {}
  let : IsReduced I.subscheme := isReduced_vanishingIdeal_subscheme ⊤
  apply LineBundle.isAmple_of_fullSupport p I hI L
  apply ReducedComponentAmple.isAmple_of_reduced_components (I.subschemeι ≫ p)
    (L.pullback I.subschemeι) (H.pullback I.subschemeι)
    (hH.pullback_closedImmersion H I.subschemeι)
  intro C
  let j := CurveCycle.reducedComponentι I.subscheme C
  have hc : (L.pullback (j ≫ I.subschemeι)).IsAmple := hints (j ≫ I.subschemeι)
  exact AmpleIso.isAmple_of_sheaf_iso _ _
    ((Scheme.Modules.pullbackComp j I.subschemeι).app L.sheaf).symm hc

end
end PiExponent.NumericalAmpleness

end OAI
end Source0677

-- Source: OAI/NumberTheory/PiExponent/Ampleness/ProperAmpleFiniteDimension.lean
section Source0678
/-
Modification notice for the LogTwo project.
Derived from openai/math (Apache-2.0), revision adc7f1241b42e322a6451854ab7e4b4c146bf78a.
Original source: lean/OAI/NumberTheory/PiExponent/Ampleness/ProperAmpleFiniteDimension.lean
Changes: Convert module/import declarations to the Lean 4.34 public module format.
See ../THIRD_PARTY_NOTICES.txt for provenance and the recorded changes.
-/

namespace OAI

noncomputable section
namespace PiExponent.ProperAmpleFiniteDimension
open AlgebraicGeometry CategoryTheory TopologicalSpace
open PiExponentSeshadri.Geometry PiExponentSeshadri.Projective

section Graded
variable {A S : Type*} [CommRing A] [SetLike S A] [AddSubmonoidClass S A]
    (G : ℕ → S) [GradedRing G]

def projectivePrime : ProjectiveSpectrum G → PrimeSpectrum A :=
  fun x => ⟨x.asHomogeneousIdeal.toIdeal, x.isPrime⟩

theorem projectivePrime_isInducing : Topology.IsInducing (projectivePrime G) := by
  constructor
  apply TopologicalSpace.ext_isClosed
  intro Z
  rw [ProjectiveSpectrum.isClosed_iff_zeroLocus, isClosed_induced_iff]
  constructor
  · rintro ⟨s,rfl⟩
    exact ⟨PrimeSpectrum.zeroLocus s, PrimeSpectrum.isClosed_zeroLocus s, rfl⟩
  · rintro ⟨T,hT,hTZ⟩
    obtain ⟨s,rfl⟩ := (PrimeSpectrum.isClosed_iff_zeroLocus T).mp hT
    exact ⟨s,hTZ.symm⟩

theorem projectiveSpectrum_dimension_le :
    topologicalKrullDim (ProjectiveSpectrum G) ≤ ringKrullDim A := by
  simpa only [PrimeSpectrum.topologicalKrullDim_eq_ringKrullDim] using
    (projectivePrime_isInducing G).topologicalKrullDim_le
end Graded

theorem projectiveSpace_dimension_le_card (K σ : Type) [Field K] [Finite σ] :
    topologicalKrullDim (ProjectiveO1.projectiveSpace K σ) ≤ Nat.card σ := by
  let := MvPolynomial.gradedAlgebra (R := K) (σ := σ)
  change topologicalKrullDim (ProjectiveSpectrum (PolyGrade K σ)) ≤ _
  have h := projectiveSpectrum_dimension_le (PolyGrade K σ)
  simpa only [MvPolynomial.ringKrullDim_of_isNoetherianRing_of_finite,
    ringKrullDim_eq_zero_of_field, zero_add] using h

theorem closedImmersion_dimension_le {X Y : Scheme} (i : X ⟶ Y)
    [IsClosedImmersion i] : topologicalKrullDim X ≤ topologicalKrullDim Y :=
  i.isEmbedding.isInducing.topologicalKrullDim_le

theorem exists_dimension_bound_of_proper_ample {X : Scheme.{0}}
    (p : X ⟶ Spec (CommRingCat.of ℂ)) [IsProper p]
    (H : LineBundle X) (hH : H.IsAmple) :
    ∃ d : ℕ, topologicalKrullDim X ≤ (d : WithBot ℕ∞) := by
  classical
  let : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian p
  let : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace p
  let : IsNoetherian X := ⟨⟩
  obtain ⟨n, hn, σ, hσ, s, hs, hclosed⟩ := H.ample_projective_sections_noetherian p hH
  let : Fintype σ := hσ
  let k := p.appTop.hom.comp (Scheme.ΓSpecIso (CommRingCat.of ℂ)).inv.hom
  let i : X ⟶ ProjectiveO1.projectiveSpace ℂ σ := sectionsMorphism k s hs
  have : IsClosedImmersion i := hclosed
  exact ⟨Nat.card σ, (closedImmersion_dimension_le i).trans
    (projectiveSpace_dimension_le_card ℂ σ)⟩

end PiExponent.ProperAmpleFiniteDimension

end

end OAI
end Source0678

-- Source: OAI/NumberTheory/PiExponent/Ampleness/AmplePositiveTwist.lean
section Source0679
/-
Modification notice for the LogTwo project.
Derived from openai/math (Apache-2.0), revision adc7f1241b42e322a6451854ab7e4b4c146bf78a.
Original source: lean/OAI/NumberTheory/PiExponent/Ampleness/AmplePositiveTwist.lean
Changes: Convert module/import declarations to the Lean 4.34 public module format.
See ../THIRD_PARTY_NOTICES.txt for provenance and the recorded changes.
-/

namespace OAI

namespace PiExponentSeshadri.Geometry
noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite
open PiExponentSeshadri.Frames PiExponentSeshadri.TensorPure PiExponentSeshadri.Projective
variable {X : Scheme.{0}}

theorem LineBundle.ample_framed_cover [CompactSpace X] (L M : LineBundle X)
    (hL : L.IsAmple) (a : ℕ) (ha : 0 < a) :
    ∃ d : ℕ, 0 < d ∧ a ∣ d ∧ ∃ ι : Type, ∃ _ : Fintype ι,
      ∃ s : ι → GlobalSections X (L.pow d).sheaf,
        (⨆ i, sectionOpen X (s i)) = ⊤ ∧
        (∀ i, IsAffineOpen (sectionOpen X (s i))) ∧
        (∀ i, (sectionOpen X (s i) : Set X).Nonempty) ∧
        (∀ i, Nonempty (M.sheaf.restrict (sectionOpen X (s i)).ι ≅ O (sectionOpen X (s i)).toScheme)) := by
  classical
  choose V hV e using M.locallyRankOne
  have hh (x : X) := hL x (V x) (hV x)
  choose d hd s hs hsub haff using hh
  obtain ⟨I,hI⟩ := isCompact_univ.elim_finite_subcover
    (fun x => (sectionOpen X (s x) : Set X)) (fun x => (sectionOpen X (s x)).isOpen)
    (by intro x _; exact Set.mem_iUnion.mpr ⟨x,hs x⟩)
  obtain ⟨n,hn,t,ht⟩ := L.common_degree (fun i : I => d i.val)
    (fun i => hd i.val) (fun i => s i.val)
  let f := linePowerMul L n a
  let q (i : I) : GlobalSections X (L.pow (n*a)).sheaf :=
    powerSection (t i) a ≫ f.hom
  have hq (i : I) : sectionOpen X (q i) = sectionOpen X (s i.val) := by
    change SectionOpens.isoOpen (powerSection (t i) a ≫ f.hom) = _
    erw [SectionOpens.isoOpen_postcomp]
    exact ((L.pow n).sectionOpen_power (t i) ha).trans (ht i)
  refine ⟨n*a,Nat.mul_pos hn ha,dvd_mul_left a n,I,inferInstance,q,?_,?_,?_,?_⟩
  · apply top_unique
    intro x _
    obtain ⟨i,hi⟩ := Set.mem_iUnion.mp (hI (show x ∈ Set.univ from trivial))
    obtain ⟨hi,hx⟩ := Set.mem_iUnion.mp hi
    refine Opens.mem_iSup.mpr ⟨⟨i,hi⟩,?_⟩
    rw [hq]
    exact hx
  · intro i
    rw [hq]
    exact haff i.val
  · intro i
    rw [hq]
    exact ⟨i.val,hs i.val⟩
  · intro i
    exact ⟨Frames.restrictOpenFrame ((hq i).le.trans (hsub i.val)) (Classical.choice (e i.val))⟩

theorem LineBundle.exists_ample_twist [IsIntegral X] [CompactSpace X]
    (L M : LineBundle X) (hL : L.IsAmple) :
    ∃ d : ℕ, 0 < d ∧ ((L.pow d).tensor M).IsAmple := by
  classical
  obtain ⟨a,ha,-,ι,hi,s,hs,hsa,hsn,he⟩ := L.ample_framed_cover M hL 1 (by decide)
  choose N hN using fun i => (L.pow a).mixed_frame_extension M (s i) (hsn i)
    (Classical.choice (he i))
  let n := Finset.univ.sup N
  choose t ht hval using fun i => hN i n (Finset.le_sup (Finset.mem_univ i))
  let e := moduleTensorIso (linePowerMul L a (n+1)) (Iso.refl M.sheaf)
  let q (i : ι) : GlobalSections X ((L.pow (a*(n+1))).tensor M).sheaf :=
    t i ≫ e.hom
  have hq (i : ι) : sectionOpen X (q i) = sectionOpen X (s i) := by
    change SectionOpens.isoOpen (t i ≫ e.hom) = _
    erw [SectionOpens.isoOpen_postcomp]
    exact ht i
  refine ⟨a*(n+1),Nat.mul_pos ha (by omega),
    ((L.pow (a*(n+1))).tensor M).ample_of_affine_section_cover q ?_ ?_⟩
  · simpa only [hq] using hs
  · intro i
    rw [hq]
    exact hsa i

end
end PiExponentSeshadri.Geometry

end OAI
end Source0679

-- Source: OAI/NumberTheory/PiExponent/Ampleness/AmpleSlopeAlgebra.lean
section Source0680
/-
Modification notice for the LogTwo project.
Derived from openai/math (Apache-2.0), revision adc7f1241b42e322a6451854ab7e4b4c146bf78a.
Original source: lean/OAI/NumberTheory/PiExponent/Ampleness/AmpleSlopeAlgebra.lean
Changes: Convert module/import declarations to the Lean 4.34 public module format.
See ../THIRD_PARTY_NOTICES.txt for provenance and the recorded changes.
-/

namespace OAI

namespace PiExponent.NumericalAmpleness
noncomputable section
open AlgebraicGeometry CategoryTheory
open PiExponentSeshadri.Geometry
variable {X : Scheme.{0}}

def slopeBundle (L H : LineBundle X) (a b : ℕ) : LineBundle X :=
  (L.pow b).tensor (H.pow a)

def slopeBundlePowIso (L H : LineBundle X) (a b n : ℕ) :
    ((slopeBundle L H a b).pow n).sheaf ≅ (slopeBundle L H (a*n) (b*n)).sheaf :=
  lineTensorPow (L.pow b) (H.pow a) n ≪≫
    moduleTensorIso (linePowerMul L b n) (linePowerMul H a n)

def slopeBundleAddIso (L H : LineBundle X) (a b e : ℕ) :
    ((slopeBundle L H a b).tensor (H.pow e)).sheaf ≅ (slopeBundle L H (a+e) b).sheaf :=
  lineTensorAssoc (L.pow b) (H.pow a) (H.pow e) ≪≫
    moduleTensorIso (Iso.refl _) (linePowerAdd H a e).symm

def slopeBundleCongrIso (L H : LineBundle X) (a b c d : ℕ)
    (ha : a = c) (hb : b = d) :
    (slopeBundle L H a b).sheaf ≅ (slopeBundle L H c d).sheaf := by
  subst c
  subst d
  exact Iso.refl _

def slopeBundleCrossIso (L H : LineBundle X) (a b c d : ℕ) (h : a*d ≤ c*b) :
    (((slopeBundle L H a b).pow d).tensor (H.pow (c*b-a*d))).sheaf ≅
      ((slopeBundle L H c d).pow b).sheaf :=
  moduleTensorIso (slopeBundlePowIso L H a b d) (Iso.refl _) ≪≫
    slopeBundleAddIso L H (a*d) (b*d) (c*b-a*d) ≪≫
      slopeBundleCongrIso L H (a*d+(c*b-a*d)) (b*d) (c*b) (d*b)
        (Nat.add_sub_of_le h) (Nat.mul_comm b d) ≪≫
      (slopeBundlePowIso L H c d b).symm

theorem ample_tensor_nonnegative_power (A H : LineBundle X)
    (hA : A.IsAmple) (hH : H.IsAmple) (n : ℕ) : (A.tensor (H.pow n)).IsAmple := by
  cases n with
  | zero =>
    exact PiExponent.AmpleIso.isAmple_of_sheaf_iso A (A.tensor (H.pow 0))
      (moduleTensorRightUnit A.sheaf).symm hA
  | succ n => exact hA.tensor (hH.pow (n+1) (by omega))

theorem ample_slope_of_cross_le (L H : LineBundle X) (hH : H.IsAmple)
    (a b c d : ℕ) (hb : 0 < b) (hd : 0 < d) (hcross : a*d ≤ c*b)
    (hA : (slopeBundle L H a b).IsAmple) : (slopeBundle L H c d).IsAmple := by
  have hp := ample_tensor_nonnegative_power ((slopeBundle L H a b).pow d) H
    (hA.pow d hd) hH (c*b-a*d)
  apply LineBundle.IsAmple.of_pow (slopeBundle L H c d) hb
  exact PiExponent.AmpleIso.isAmple_of_sheaf_iso _ _ (slopeBundleCrossIso L H a b c d hcross) hp

def linePowerTensorInverseIso (H : LineBundle X) (a : ℕ) (ha : 0 < a) :
    ((H.pow a).tensor H.inverse).sheaf ≅ (H.pow (a-1)).sheaf :=
  moduleTensorIso
    (eqToIso (congrArg (fun n => (H.pow n).sheaf) (by omega : a = a-1+1)) ≪≫
      linePowerAdd H (a-1) 1 ≪≫
        moduleTensorIso (Iso.refl _) (moduleTensorRightUnit H.sheaf))
    (Iso.refl _) ≪≫ moduleTensorInverseCancelIso (H.pow (a-1)).sheaf H

def slopeBundleSubtractIso (L H : LineBundle X) (a b : ℕ) (ha : 0 < a) :
    ((slopeBundle L H a b).tensor H.inverse).sheaf ≅ (slopeBundle L H (a-1) b).sheaf :=
  lineTensorAssoc (L.pow b) (H.pow a) H.inverse ≪≫
    moduleTensorIso (Iso.refl _) (linePowerTensorInverseIso H a ha)

theorem exists_smaller_ample_slope [IsIntegral X] [CompactSpace X]
    (L H : LineBundle X) (a b : ℕ) (ha : 0 < a) (hb : 0 < b)
    (hA : (slopeBundle L H a b).IsAmple) :
    ∃ n : ℕ, 0 < n ∧ (slopeBundle L H (a*n-1) (b*n)).IsAmple ∧
      ((a*n-1 : ℕ) : ℚ) / (b*n : ℕ) < (a:ℚ)/b := by
  obtain ⟨n,hn,hamp⟩ := (slopeBundle L H a b).exists_ample_twist H.inverse hA
  have han := Nat.mul_pos ha hn
  have ham : (slopeBundle L H (a*n-1) (b*n)).IsAmple :=
    PiExponent.AmpleIso.isAmple_of_sheaf_iso _ _
      (moduleTensorIso (slopeBundlePowIso L H a b n) (Iso.refl _) ≪≫
        slopeBundleSubtractIso L H (a*n) (b*n) han) hamp
  refine ⟨n,hn,ham,?_⟩
  have hbq : (0:ℚ) < b := by exact_mod_cast hb
  have hnq : (0:ℚ) < n := by exact_mod_cast hn
  have hsub : ((a*n-1:ℕ):ℚ) = (a:ℚ)*n-1 := by
    rw [Nat.cast_sub (by omega : 1 ≤ a*n), Nat.cast_mul, Nat.cast_one]
  rw [hsub, Nat.cast_mul]
  apply (div_lt_div_iff₀ (mul_pos hbq hnq) hbq).mpr
  nlinarith

theorem exists_ample_slope [IsIntegral X] [CompactSpace X]
    (L H : LineBundle X) (hH : H.IsAmple) :
    ∃ a : ℕ, 0 < a ∧ (slopeBundle L H a 1).IsAmple := by
  obtain ⟨a,ha,hA⟩ := H.exists_ample_twist L hH
  refine ⟨a,ha,PiExponent.AmpleIso.isAmple_of_sheaf_iso _ _ ?_ hA⟩
  exact moduleTensorComm (H.pow a).sheaf L.sheaf ≪≫
    moduleTensorIso (moduleTensorRightUnit L.sheaf).symm (Iso.refl _)

end
end PiExponent.NumericalAmpleness

end OAI
end Source0680

-- Source: OAI/NumberTheory/PiExponent/Ampleness/AmpleSlopeTopology.lean
section Source0681
-- Modified in this edition: unused plain lemmas removed; see reduction.json.
/-
Modification notice for the LogTwo project.
Derived from openai/math (Apache-2.0), revision adc7f1241b42e322a6451854ab7e4b4c146bf78a.
Original source: lean/OAI/NumberTheory/PiExponent/Ampleness/AmpleSlopeTopology.lean
Changes: Convert module/import declarations to the Lean 4.34 public module format.
See ../THIRD_PARTY_NOTICES.txt for provenance and the recorded changes.
-/

namespace OAI

namespace PiExponent.NumericalAmpleness
noncomputable section
open AlgebraicGeometry CategoryTheory Set
open PiExponentSeshadri.Geometry
variable {X : Scheme.{0}}

def ampleSlopes (L H : LineBundle X) : Set ℝ :=
  {t | ∃ a b : ℕ, 0 < b ∧ t = (a : ℝ)/b ∧ (slopeBundle L H a b).IsAmple}

def ampleThreshold (L H : LineBundle X) : ℝ := sInf (ampleSlopes L H)

lemma ampleSlopes_bddBelow (L H : LineBundle X) : BddBelow (ampleSlopes L H) := by
  refine ⟨0, ?_⟩
  rintro t ⟨a,b,hb,rfl,ha⟩
  exact div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)

lemma ampleSlopes_nonempty [IsIntegral X] [CompactSpace X]
    (L H : LineBundle X) (hH : H.IsAmple) : (ampleSlopes L H).Nonempty := by
  obtain ⟨a,ha,hA⟩ := exists_ample_slope L H hH
  exact ⟨(a:ℝ)/1,a,1,by decide,by norm_num,hA⟩

lemma ampleThreshold_nonneg [IsIntegral X] [CompactSpace X]
    (L H : LineBundle X) (hH : H.IsAmple) : 0 ≤ ampleThreshold L H := by
  apply le_csInf (ampleSlopes_nonempty L H hH)
  rintro t ⟨a,b,hb,rfl,ha⟩
  exact div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)

theorem ample_of_threshold_lt [IsIntegral X] [CompactSpace X]
    (L H : LineBundle X) (hH : H.IsAmple) (a b : ℕ) (hb : 0 < b)
    (ht : ampleThreshold L H < (a:ℝ)/b) : (slopeBundle L H a b).IsAmple := by
  obtain ⟨t,htmem,htt⟩ := exists_lt_of_csInf_lt (ampleSlopes_nonempty L H hH) ht
  obtain ⟨c,e,he,rfl,hA⟩ := htmem
  apply ample_slope_of_cross_le L H hH c e a b he hb _ hA
  have hcross := (div_lt_div_iff₀ (by exact_mod_cast he : (0:ℝ)<e)
    (by exact_mod_cast hb : (0:ℝ)<b)).mp htt
  exact_mod_cast hcross.le

theorem threshold_lt_of_ample [IsIntegral X] [CompactSpace X]
    (L H : LineBundle X) (a b : ℕ) (ha : 0 < a) (hb : 0 < b)
    (hA : (slopeBundle L H a b).IsAmple) : ampleThreshold L H < (a:ℝ)/b := by
  obtain ⟨n,hn,hsmall,hlt⟩ := exists_smaller_ample_slope L H a b ha hb hA
  have hmem : (((a*n-1:ℕ):ℝ)/(b*n:ℕ)) ∈ ampleSlopes L H :=
    ⟨a*n-1,b*n,Nat.mul_pos hb hn,rfl,hsmall⟩
  have hlt' : (((a*n-1:ℕ):ℝ)/(b*n:ℕ)) < (a:ℝ)/b := by
    have h := (Rat.cast_strictMono (K := ℝ)) hlt
    simpa only [Rat.cast_div, Rat.cast_natCast] using h
  exact (csInf_le (ampleSlopes_bddBelow L H) hmem).trans_lt hlt'

lemma slope_zero_isAmple_iff (L H : LineBundle X) (b : ℕ) (hb : 0 < b) :
    (slopeBundle L H 0 b).IsAmple ↔ L.IsAmple := by
  constructor
  · intro h
    apply LineBundle.IsAmple.of_pow L hb
    exact PiExponent.AmpleIso.isAmple_of_sheaf_iso _ _
      (moduleTensorRightUnit (L.pow b).sheaf) h
  · intro h
    exact PiExponent.AmpleIso.isAmple_of_sheaf_iso _ _
      (moduleTensorRightUnit (L.pow b).sheaf).symm (h.pow b hb)

end
end PiExponent.NumericalAmpleness

end OAI
end Source0681

-- Source: OAI/NumberTheory/PiExponent/Ampleness/AmpleThresholdPolynomial.lean
section Source0682
-- Modified in this edition: unused plain lemmas removed; see reduction.json.
/-
Modification notice for the LogTwo project.
Derived from openai/math (Apache-2.0), revision adc7f1241b42e322a6451854ab7e4b4c146bf78a.
Original source: lean/OAI/NumberTheory/PiExponent/Ampleness/AmpleThresholdPolynomial.lean
Changes: Convert module/import declarations to the Lean 4.34 public module format.
See ../THIRD_PARTY_NOTICES.txt for provenance and the recorded changes.
-/

namespace OAI

namespace PiExponent.NumericalAmpleness
open Set
open scoped Topology

theorem polynomial_pos_at_left_of_margin
    (P : Polynomial ℝ) (d : ℕ) (r ε b : ℝ) (hr : 0 ≤ r) (hε : 0 < ε)
    (hrb : r < b) (hpositive : 0 < P.eval b)
    (hderivative : ∀ t : ℝ, r < t →
      (t + ε) * P.derivative.eval t ≤ (d : ℝ) * P.eval t) :
    0 < P.eval r := by
  let Q : ℝ → ℝ := fun t => P.eval t / (t+ε)^d
  have hbase (x : ℝ) (hx : x ∈ Icc r b) : 0 < x+ε := by
    have := hx.1
    linarith
  have hderiv (x : ℝ) (hx : x ∈ Icc r b) :
      HasDerivAt Q
        ((P.derivative.eval x * (x+ε)^d -
          P.eval x * ((d:ℝ) * (x+ε)^(d-1))) / ((x+ε)^d)^2) x := by
    convert! (P.hasDerivAt x).div (((hasDerivAt_id x).add_const ε).pow d)
      (pow_ne_zero d (ne_of_gt (hbase x hx))) using 1
    simp
  have hanti : AntitoneOn Q (Icc r b) := by
    apply antitoneOn_of_deriv_nonpos (convex_Icc r b)
    · exact P.continuousOn.div ((continuous_id.add continuous_const).pow d).continuousOn
        (fun x hx => pow_ne_zero d (ne_of_gt (hbase x hx)))
    · intro x hx
      exact (hderiv x (interior_subset hx)).differentiableAt.differentiableWithinAt
    · intro x hx
      have hx' : r < x := (show x ∈ Ioo r b by simpa only [interior_Icc] using hx).1
      have h := hderivative x hx'
      rw [(hderiv x (interior_subset hx)).deriv]
      apply div_nonpos_of_nonpos_of_nonneg _ (sq_nonneg _)
      cases d with
      | zero =>
        simp only [Nat.cast_zero, zero_mul, pow_zero, mul_one, mul_zero, sub_zero] at h ⊢
        exact nonpos_of_mul_nonpos_left (by simpa only [mul_comm] using h)
          (hbase x (interior_subset hx))
      | succ n =>
        have he : P.derivative.eval x * (x+ε)^(n+1) -
            P.eval x * ((n+1:ℕ):ℝ) * (x+ε)^n =
            (x+ε)^n * ((x+ε)*P.derivative.eval x - ((n+1:ℕ):ℝ)*P.eval x) := by
          rw [pow_succ]
          ring
        have hn : (x+ε)^n * ((x+ε)*P.derivative.eval x -
            ((n+1:ℕ):ℝ)*P.eval x) ≤ 0 :=
          mul_nonpos_of_nonneg_of_nonpos (le_of_lt (pow_pos (hbase x (interior_subset hx)) n))
            (sub_nonpos.mpr h)
        simpa only [Nat.succ_eq_add_one, Nat.add_sub_cancel, ← mul_assoc, he] using hn
  have hle : Q b ≤ Q r := hanti ⟨le_rfl,hrb.le⟩ ⟨hrb.le,le_rfl⟩ hrb.le
  have hq : 0 < Q b := div_pos hpositive
    (pow_pos (by linarith) d)
  exact (div_pos_iff_of_pos_right (pow_pos (by linarith : 0 < r+ε) d)).mp (hq.trans_le hle)

theorem polynomial_pos_at_boundary_of_rational_margin
    (P : Polynomial ℝ) (d : ℕ) (r ε : ℝ) (hr : 0 ≤ r) (hε : 0 < ε)
    (hpositive : ∀ t : ℚ, r < (t:ℝ) → 0 < P.eval (t:ℝ))
    (hderivative : ∀ t : ℚ, r < (t:ℝ) →
      ((t:ℝ)+ε) * P.derivative.eval (t:ℝ) ≤ (d:ℝ) * P.eval (t:ℝ)) :
    0 < P.eval r := by
  have hreal (x : ℝ) : x ≤ r ∨ (x+ε)*P.derivative.eval x ≤ (d:ℝ)*P.eval x := by
    refine DenseRange.induction_on
      (Rat.denseRange_cast : DenseRange (fun q : ℚ => (q:ℝ))) x ?_ ?_
    · exact isClosed_le continuous_id continuous_const |>.union
        (isClosed_le ((continuous_id.add continuous_const).mul P.derivative.continuous)
          (continuous_const.mul P.continuous))
    · intro q
      by_cases hq : (q:ℝ) ≤ r
      · exact Or.inl hq
      · exact Or.inr (hderivative q (lt_of_not_ge hq))
  obtain ⟨b,hrb,hb⟩ := exists_rat_btwn (show r < r+1 by linarith)
  exact polynomial_pos_at_left_of_margin P d r ε (b:ℝ) hr hε hrb (hpositive b hrb)
    (fun x hx => (hreal x).resolve_left (not_le_of_gt hx))

theorem nonnegative_rat_nat_ratio (q : ℚ) (hq : 0 ≤ q) :
    ∃ a b : ℕ, 0 < b ∧ (q:ℝ) = (a:ℝ)/b := by
  refine ⟨q.num.natAbs,q.den,q.pos,?_⟩
  have hn : 0 ≤ q.num := Rat.num_nonneg.mpr hq
  rw [Rat.cast_def, Nat.cast_natAbs, abs_of_nonneg hn]

theorem exists_positive_rational_below_of_polynomial_pos
    (P : Polynomial ℝ) (r : ℝ) (hr : 0 < r) (hP : 0 < P.eval r) :
    ∃ q : ℚ, 0 < (q:ℝ) ∧ (q:ℝ) < r ∧ 0 < P.eval (q:ℝ) := by
  have hn : {t : ℝ | 0 < P.eval t} ∈ 𝓝 r :=
    P.continuousAt.preimage_mem_nhds (Ioi_mem_nhds hP)
  obtain ⟨a,ha,hsub⟩ := exists_Ioc_subset_of_mem_nhds' hn hr
  obtain ⟨q,haq,hqr⟩ := exists_rat_btwn ha.2
  exact ⟨q,ha.1.trans_lt haq,hqr,hsub ⟨haq,hqr.le⟩⟩

end PiExponent.NumericalAmpleness

end OAI
end Source0682

-- Source: OAI/NumberTheory/PiExponent/Ampleness/NakaiBasepointFree.lean
section Source0683
/-
Modification notice for the LogTwo project.
Derived from openai/math (Apache-2.0), revision adc7f1241b42e322a6451854ab7e4b4c146bf78a.
Original source: lean/OAI/NumberTheory/PiExponent/Ampleness/NakaiBasepointFree.lean
Changes: Convert module/import declarations to the Lean 4.34 public module format.
See ../THIRD_PARTY_NOTICES.txt for provenance and the recorded changes.
-/

namespace OAI

namespace PiExponent.NumericalAmpleness
noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace
open PiExponentSeshadri.Geometry
open PiExponent.SectionZeroIdeal
variable {X : Scheme.{0}}

theorem power_nonvanishing_sections_of_divisor_lifts
    (L : LineBundle X) (s : GlobalSections X L.sheaf) (n : ℕ)
    (hlift : Function.Surjective
      (fun t : GlobalSections X (L.pow n).sheaf =>
        pullbackSection (zeroIdeal L s).subschemeι t))
    (hgenerate : ∀ y : (zeroIdeal L s).subscheme, ∃ σ :
      GlobalSections (zeroIdeal L s).subscheme
        ((Scheme.Modules.pullback (zeroIdeal L s).subschemeι).obj (L.pow n).sheaf),
      y ∈ sectionOpen (zeroIdeal L s).subscheme σ) :
    ∀ x : X, ∃ t : GlobalSections X (L.pow n).sheaf, x ∈ sectionOpen X t := by
  intro x
  by_cases hx : x ∈ sectionOpen X s
  · exact ⟨powerSection s n, sectionOpen_le_powerSection s n hx⟩
  · have hxI : x ∈ (zeroIdeal L s).support := by
      change x ∈ ((zeroIdeal L s).support : Set X)
      rw [zeroIdeal_support]
      exact hx
    have hr : x ∈ Set.range (zeroIdeal L s).subschemeι := by
      rwa [Scheme.IdealSheafData.range_subschemeι]
    obtain ⟨y,rfl⟩ := hr
    obtain ⟨σ,hσ⟩ := hgenerate y
    obtain ⟨t,ht⟩ := hlift σ
    change pullbackSection (zeroIdeal L s).subschemeι t = σ at ht
    refine ⟨t,?_⟩
    have he := pullback_isoOpen_eq (L.pow n) t (zeroIdeal L s).subschemeι
    rw [ht] at he
    change y ∈ (zeroIdeal L s).subschemeι ⁻¹ᵁ PiExponentSeshadri.SectionOpens.isoOpen t
    exact he.le hσ

theorem finite_section_cover_of_pointwise [CompactSpace X] (L : LineBundle X)
    (h : ∀ x : X, ∃ t : GlobalSections X L.sheaf, x ∈ sectionOpen X t) :
    ∃ l : ℕ, ∃ t : Fin l → GlobalSections X L.sheaf,
      (⨆ j, sectionOpen X (t j)) = ⊤ := by
  classical
  choose t ht using h
  obtain ⟨I,hI⟩ := isCompact_univ.elim_finite_subcover
    (fun x => (sectionOpen X (t x) : Set X)) (fun x => (sectionOpen X (t x)).isOpen)
    (by intro x _; exact Set.mem_iUnion.mpr ⟨x,ht x⟩)
  let e := (Fintype.equivFin I).symm
  refine ⟨Fintype.card I,fun j => t (e j).val,?_⟩
  apply top_unique
  intro x _
  obtain ⟨i,hi⟩ := Set.mem_iUnion.mp (hI (show x ∈ Set.univ from trivial))
  obtain ⟨hi,hx⟩ := Set.mem_iUnion.mp hi
  apply Opens.mem_iSup.mpr
  refine ⟨e.symm ⟨i,hi⟩,?_⟩
  change x ∈ sectionOpen X (t (e (e.symm ⟨i,hi⟩)).val)
  rw [Equiv.apply_symm_apply]
  exact hx

theorem eventual_power_section_cover_of_divisor [CompactSpace X]
    (p : X ⟶ Spec (CommRingCat.of ℂ)) (L : LineBundle X)
    (s : GlobalSections X L.sheaf) [Mono s]
    (hfinite : ∀ n, letI := Module.compHom (cohomology (L.pow n).sheaf 1) (baseScalars p)
      FiniteDimensional ℂ (cohomology (L.pow n).sheaf 1))
    (hzero : ∃ N, ∀ n, N ≤ n → ∀ z :
      cohomology ((Scheme.Modules.pullback (zeroIdeal L s).subschemeι).obj (L.pow (n+1)).sheaf) 1,
      z = 0)
    (hgenerate : ∃ N, ∀ n, N ≤ n → ∀ y : (zeroIdeal L s).subscheme, ∃ σ :
      GlobalSections (zeroIdeal L s).subscheme
        ((Scheme.Modules.pullback (zeroIdeal L s).subschemeι).obj (L.pow (n+1)).sheaf),
      y ∈ sectionOpen (zeroIdeal L s).subscheme σ) :
    ∃ N, ∀ n, N ≤ n → ∃ l : ℕ, ∃ t : Fin l → GlobalSections X (L.pow (n+1)).sheaf,
      (⨆ j, sectionOpen X (t j)) = ⊤ := by
  obtain ⟨N,hN⟩ := eventual_cartier_restriction_section_lifting p L s hfinite hzero
  obtain ⟨K,hK⟩ := hgenerate
  refine ⟨max N K,fun n hn => ?_⟩
  apply finite_section_cover_of_pointwise (L.pow (n+1))
  exact power_nonvanishing_sections_of_divisor_lifts L s (n+1)
    (hN n ((le_max_left N K).trans hn)) (hK n ((le_max_right N K).trans hn))

end
end PiExponent.NumericalAmpleness

end OAI
end Source0683

-- Source: OAI/NumberTheory/PiExponent/Ampleness/NakaiDivisorAmple.lean
section Source0684
/-
Modification notice for the LogTwo project.
Derived from openai/math (Apache-2.0), revision adc7f1241b42e322a6451854ab7e4b4c146bf78a.
Original source: lean/OAI/NumberTheory/PiExponent/Ampleness/NakaiDivisorAmple.lean
Changes: Convert module/import declarations to the Lean 4.34 public module format.
See ../THIRD_PARTY_NOTICES.txt for provenance and the recorded changes.
-/

namespace OAI

namespace PiExponent.NumericalAmpleness
noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace
open PiExponentSeshadri.Geometry
open PiExponent.SectionZeroIdeal
variable {X : Scheme.{0}}

theorem eventual_zeroDivisor_power_generation
    (L : LineBundle X) (s : GlobalSections X L.sheaf)
    [NoetherianSpace (zeroIdeal L s).subscheme]
    (hD : (L.pullback (zeroIdeal L s).subschemeι).IsAmple) :
    ∃ N, ∀ n, N ≤ n → ∀ y : (zeroIdeal L s).subscheme, ∃ σ :
      GlobalSections (zeroIdeal L s).subscheme
        ((Scheme.Modules.pullback (zeroIdeal L s).subschemeι).obj (L.pow (n+1)).sheaf),
      y ∈ sectionOpen (zeroIdeal L s).subscheme σ := by
  let i := (zeroIdeal L s).subschemeι
  obtain ⟨N,hN⟩ := GeneratorsSectionCover.ample_eventual_fin_section_cover (L.pullback i) hD
  refine ⟨N,fun n hn y => ?_⟩
  obtain ⟨k,t,ht⟩ := hN (n+1) (by omega)
  have hy : y ∈ ⨆ j, sectionOpen (zeroIdeal L s).subscheme (t j) := by rw [ht]; trivial
  obtain ⟨j,hj⟩ := Opens.mem_iSup.mp hy
  let e := PiExponentSeshadri.PullbackTensor.powIso i L (n+1)
  refine ⟨t j ≫ e.inv,?_⟩
  change y ∈ PiExponentSeshadri.SectionOpens.isoOpen (t j ≫ e.symm.hom)
  exact (PiExponentSeshadri.SectionOpens.isoOpen_postcomp (t j) e.symm).ge hj

theorem eventual_zeroDivisor_power_cohomology_zero
    (p : X ⟶ Spec (CommRingCat.of ℂ)) [IsProper p]
    (L : LineBundle X) (s : GlobalSections X L.sheaf)
    (hD : (L.pullback (zeroIdeal L s).subschemeι).IsAmple) :
    ∃ N, ∀ n, N ≤ n → ∀ q, 0 < q → ∀ z :
      cohomology ((Scheme.Modules.pullback (zeroIdeal L s).subschemeι).obj (L.pow (n+1)).sheaf) q,
      z = 0 := by
  let i := (zeroIdeal L s).subschemeι
  obtain ⟨N,hN⟩ := GeometrySupport.NoetherianAmpleSerreVanishing.ample_power_cohomology_zero
    (i ≫ p) (L.pullback i) hD
  refine ⟨N,fun n hn q hq => ?_⟩
  exact GeometrySupport.SerrePowerDescent.ext_zero_of_iso
    (PiExponentSeshadri.PullbackTensor.powIso i L (n+1)).symm q (hN (n+1) (by omega) q hq)

theorem eventual_power_section_cover_of_ample_zeroDivisor
    (p : X ⟶ Spec (CommRingCat.of ℂ)) [IsProper p]
    (L : LineBundle X) (s : GlobalSections X L.sheaf) [Mono s]
    (hfinite : ∀ n, letI := Module.compHom (cohomology (L.pow n).sheaf 1) (baseScalars p)
      FiniteDimensional ℂ (cohomology (L.pow n).sheaf 1))
    (hD : (L.pullback (zeroIdeal L s).subschemeι).IsAmple) :
    ∃ N, ∀ n, N ≤ n → ∃ l : ℕ, ∃ t : Fin l → GlobalSections X (L.pow (n+1)).sheaf,
      (⨆ j, sectionOpen X (t j)) = ⊤ := by
  let : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace p
  let i := (zeroIdeal L s).subschemeι
  let : IsLocallyNoetherian (zeroIdeal L s).subscheme :=
    LocallyOfFiniteType.isLocallyNoetherian (i ≫ p)
  let : CompactSpace (zeroIdeal L s).subscheme :=
    QuasiCompact.compactSpace_of_compactSpace (i ≫ p)
  let : IsNoetherian (zeroIdeal L s).subscheme := {}
  obtain ⟨N,hN⟩ := eventual_zeroDivisor_power_cohomology_zero p L s hD
  exact eventual_power_section_cover_of_divisor p L s hfinite
    ⟨N,fun n hn => hN n hn 1 (by decide)⟩
    (eventual_zeroDivisor_power_generation L s hD)

end
end PiExponent.NumericalAmpleness

end OAI
end Source0684

-- Source: OAI/NumberTheory/PiExponent/Cohomology/CartierEulerPair.lean
section Source0685
/-
Modification notice for the LogTwo project.
Derived from openai/math (Apache-2.0), revision adc7f1241b42e322a6451854ab7e4b4c146bf78a.
Original source: lean/OAI/NumberTheory/PiExponent/Cohomology/CartierEulerPair.lean
Changes: Convert module/import declarations to the Lean 4.34 public module format.
See ../THIRD_PARTY_NOTICES.txt for provenance and the recorded changes.
-/

namespace OAI

namespace PiExponent.NumericalAmpleness
noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace
open PiExponentSeshadri.Geometry PiExponentSeshadri.Frames
open PiExponent.SectionZeroIdeal PiExponent.CartierPowerFrames
variable {X : Scheme.{0}}

theorem regular_tensorSection_restriction_shortExact
    (p : X ⟶ Spec (CommRingCat.of ℂ)) (A F : LineBundle X)
    (s : GlobalSections X A.sheaf) [Mono s] :
    ∃ hz : sectionMultiplyLeft A.sheaf F.sheaf s ≫
        PiExponentSeshadri.LineClosedUnit.map (zeroIdeal A s).subschemeι (A.tensor F) = 0,
      (ShortComplex.mk (sectionMultiplyLeft A.sheaf F.sheaf s)
        (PiExponentSeshadri.LineClosedUnit.map (zeroIdeal A s).subschemeι (A.tensor F)) hz).ShortExact := by
  let : Mono (moduleTensorMap s (𝟙 F.sheaf)) := moduleTensorMap_mono s F
  have hm : Mono (sectionMultiplyLeft A.sheaf F.sheaf s) := mono_comp _ _
  refine @PiExponentSeshadri.CartierSequence.exact X p F (A.tensor F)
    (sectionMultiplyLeft A.sheaf F.sheaf s) hm (zeroIdeal A s) ?_
  intro x
  obtain ⟨U, hx, ⟨a⟩, ⟨f⟩⟩ := common_affine_frames A F x
  refine ⟨U, hx, f, tensorFrame A.sheaf F.sheaf U.1 a f, ?_⟩
  exact (zeroIdeal_on_frame A s U a).trans
    (tensor_multiply_ideal A.sheaf F.sheaf s U a f).symm

def tensorSectionComplex (p : X ⟶ Spec (CommRingCat.of ℂ)) (A F : LineBundle X)
    (s : GlobalSections X A.sheaf) [Mono s] : ShortComplex X.Modules :=
  ShortComplex.mk (sectionMultiplyLeft A.sheaf F.sheaf s)
    (PiExponentSeshadri.LineClosedUnit.map (zeroIdeal A s).subschemeι (A.tensor F))
    (regular_tensorSection_restriction_shortExact p A F s).choose

theorem tensorSectionComplex_shortExact (p : X ⟶ Spec (CommRingCat.of ℂ))
    (A F : LineBundle X) (s : GlobalSections X A.sheaf) [Mono s] :
    (tensorSectionComplex p A F s).ShortExact :=
  (regular_tensorSection_restriction_shortExact p A F s).choose_spec

namespace CartierEulerPair

def source (L M : LineBundle X) (n : ℕ) : LineBundle X := (L.pow n).tensor M

def middle (L B M : LineBundle X) (n : ℕ) : LineBundle X :=
  (L.tensor B).tensor (source L M n)

def middleIso (L B M : LineBundle X) (n : ℕ) :
    (middle L B M n).sheaf ≅ (B.tensor (source L M (n+1))).sheaf :=
  moduleTensorIso (moduleTensorComm L.sheaf B.sheaf) (Iso.refl (source L M n).sheaf) ≪≫
    lineTensorAssoc B L (source L M n) ≪≫
    moduleTensorIso (Iso.refl B.sheaf) (lineTensorAssoc L (L.pow n) M).symm

def leftComplex (p : X ⟶ Spec (CommRingCat.of ℂ)) (L B M : LineBundle X)
    (s : GlobalSections X (L.tensor B).sheaf) [Mono s] (n : ℕ) : ShortComplex X.Modules :=
  tensorSectionComplex p (L.tensor B) (source L M n) s

def rightComplex (p : X ⟶ Spec (CommRingCat.of ℂ)) (L B M : LineBundle X)
    (t : GlobalSections X B.sheaf) [Mono t] (n : ℕ) : ShortComplex X.Modules :=
  let T := tensorSectionComplex p B (source L M (n+1)) t
  ShortComplex.mk (T.f ≫ (middleIso L B M n).inv)
    ((middleIso L B M n).hom ≫ T.g) (by
      exact (Category.assoc T.f (middleIso L B M n).inv
        ((middleIso L B M n).hom ≫ T.g)).trans
        ((congrArg (fun q => T.f ≫ q) ((middleIso L B M n).inv_hom_id_assoc T.g)).trans
          T.zero))

private lemma iso_middle_comm {C : Type*} [Category C] {A B D : C}
    (f : A ⟶ B) (e : D ≅ B) : 𝟙 A ≫ f = (f ≫ e.inv) ≫ e.hom := by
  simp

def rightComplexIso (p : X ⟶ Spec (CommRingCat.of ℂ)) (L B M : LineBundle X)
    (t : GlobalSections X B.sheaf) [Mono t] (n : ℕ) :
    rightComplex p L B M t n ≅ tensorSectionComplex p B (source L M (n+1)) t :=
  ShortComplex.isoMk (Iso.refl _) (middleIso L B M n) (Iso.refl _)
    (by simpa only [rightComplex] using!
      iso_middle_comm (tensorSectionComplex p B (source L M (n+1)) t).f (middleIso L B M n))
    (by simpa only [rightComplex] using!
      (Category.comp_id ((middleIso L B M n).hom ≫
        (tensorSectionComplex p B (source L M (n+1)) t).g)).symm)

theorem left_shortExact (p : X ⟶ Spec (CommRingCat.of ℂ)) (L B M : LineBundle X)
    (s : GlobalSections X (L.tensor B).sheaf) [Mono s] (n : ℕ) :
    (leftComplex p L B M s n).ShortExact :=
  tensorSectionComplex_shortExact p (L.tensor B) (source L M n) s

theorem right_shortExact (p : X ⟶ Spec (CommRingCat.of ℂ)) (L B M : LineBundle X)
    (t : GlobalSections X B.sheaf) [Mono t] (n : ℕ) :
    (rightComplex p L B M t n).ShortExact :=
  ShortComplex.shortExact_of_iso (rightComplexIso p L B M t n).symm
    (tensorSectionComplex_shortExact p B (source L M (n+1)) t)

abbrev FiniteThrough (p : X ⟶ Spec (CommRingCat.of ℂ)) (N : X.Modules) (d : ℕ) : Prop :=
  ∀ q ≤ d, letI := Module.compHom (cohomology N q) (baseScalars p)
    FiniteDimensional ℂ (cohomology N q)

theorem finiteThrough_closedPushforward {Y : Scheme.{0}} (f : Y ⟶ X)
    [IsClosedImmersion f] (p : X ⟶ Spec (CommRingCat.of ℂ)) (N : Y.Modules) (d : ℕ)
    (hfinite : FiniteThrough (f ≫ p) N d) :
    FiniteThrough p ((Scheme.Modules.pushforward f).obj N) d := by
  intro q hq
  let := Module.compHom (cohomology N q) (baseScalars (f ≫ p))
  let := Module.compHom
    (cohomology ((Scheme.Modules.pushforward f).obj N) q) (baseScalars p)
  let := hfinite q hq
  let e := PiExponent.ClosedImmersionSerreTransfer.cohomologyLinearEquiv f p N q
  exact FiniteDimensional.of_surjective e.toLinearMap e.surjective

theorem euler_difference (p : X ⟶ Spec (CommRingCat.of ℂ)) (L B M : LineBundle X)
    (s : GlobalSections X (L.tensor B).sheaf) (t : GlobalSections X B.sheaf)
    [Mono s] [Mono t] (n d : ℕ)
    (hfinitePrev : FiniteThrough p (source L M n).sheaf d)
    (hfiniteNext : FiniteThrough p (source L M (n+1)).sheaf d)
    (hfiniteMiddle : FiniteThrough p (middle L B M n).sheaf d)
    (hfiniteD : FiniteThrough ((zeroIdeal (L.tensor B) s).subschemeι ≫ p)
      ((Scheme.Modules.pullback (zeroIdeal (L.tensor B) s).subschemeι).obj
        (middle L B M n).sheaf) d)
    (hfiniteE : FiniteThrough ((zeroIdeal B t).subschemeι ≫ p)
      ((Scheme.Modules.pullback (zeroIdeal B t).subschemeι).obj
        (B.tensor (source L M (n+1))).sheaf) d)
    (hzeroPrev : ∀ z : cohomology (source L M n).sheaf (d+1), z = 0)
    (hzeroNext : ∀ z : cohomology (source L M (n+1)).sheaf (d+1), z = 0) :
    eulerCharacteristic p d (source L M (n+1)).sheaf -
        eulerCharacteristic p d (source L M n).sheaf =
      eulerCharacteristic ((zeroIdeal (L.tensor B) s).subschemeι ≫ p) d
        ((Scheme.Modules.pullback (zeroIdeal (L.tensor B) s).subschemeι).obj
          (middle L B M n).sheaf) -
      eulerCharacteristic ((zeroIdeal B t).subschemeι ≫ p) d
        ((Scheme.Modules.pullback (zeroIdeal B t).subschemeι).obj
          (B.tensor (source L M (n+1))).sheaf) := by
  let D := zeroIdeal (L.tensor B) s
  let E := zeroIdeal B t
  let Q := (Scheme.Modules.pullback D.subschemeι).obj (middle L B M n).sheaf
  let R := (Scheme.Modules.pullback E.subschemeι).obj (B.tensor (source L M (n+1))).sheaf
  let : Subsingleton (cohomology (leftComplex p L B M s n).X₁ (d+1)) :=
    ⟨fun a b => (hzeroPrev a).trans (hzeroPrev b).symm⟩
  let : Subsingleton (cohomology (rightComplex p L B M t n).X₁ (d+1)) :=
    ⟨fun a b => (hzeroNext a).trans (hzeroNext b).symm⟩
  have hleft := eulerCharacteristic_add p (left_shortExact p L B M s n) d
    hfinitePrev hfiniteMiddle (finiteThrough_closedPushforward D.subschemeι p Q d hfiniteD)
  have hright := eulerCharacteristic_add p (right_shortExact p L B M t n) d
    hfiniteNext hfiniteMiddle (finiteThrough_closedPushforward E.subschemeι p R d hfiniteE)
  change eulerCharacteristic p d (middle L B M n).sheaf =
    eulerCharacteristic p d (source L M n).sheaf +
      eulerCharacteristic p d ((Scheme.Modules.pushforward D.subschemeι).obj Q) at hleft
  change eulerCharacteristic p d (middle L B M n).sheaf =
    eulerCharacteristic p d (source L M (n+1)).sheaf +
      eulerCharacteristic p d ((Scheme.Modules.pushforward E.subschemeι).obj R) at hright
  rw [PiExponent.ClosedImmersionSerreTransfer.euler_pushforward] at hleft hright
  change eulerCharacteristic p d (source L M (n+1)).sheaf -
    eulerCharacteristic p d (source L M n).sheaf =
      eulerCharacteristic (D.subschemeι ≫ p) d Q - eulerCharacteristic (E.subschemeι ≫ p) d R
  omega

end CartierEulerPair
end
end PiExponent.NumericalAmpleness

end OAI
end Source0685

-- Source: OAI/NumberTheory/PiExponent/Cohomology/EulerTwistTransport.lean
section Source0686
/-
Modification notice for the LogTwo project.
Derived from openai/math (Apache-2.0), revision adc7f1241b42e322a6451854ab7e4b4c146bf78a.
Original source: lean/OAI/NumberTheory/PiExponent/Cohomology/EulerTwistTransport.lean
Changes: Convert module/import declarations to the Lean 4.34 public module format.
See ../THIRD_PARTY_NOTICES.txt for provenance and the recorded changes.
-/

namespace OAI

namespace PiExponent.NumericalAmpleness
noncomputable section
open AlgebraicGeometry CategoryTheory
open PiExponentSeshadri.Geometry
variable {X Y : Scheme.{0}}

def pullbackMixedPowerIso (f : Y ⟶ X) (L M : LineBundle X) (n : ℕ) :
    (Scheme.Modules.pullback f).obj ((L.pow n).tensor M).sheaf ≅
      (((L.pullback f).pow n).tensor (M.pullback f)).sheaf :=
  PiExponentSeshadri.PullbackTensor.iso f (L.pow n) M ≪≫
    moduleTensorIso (PiExponentSeshadri.PullbackTensor.powIso f L n) (Iso.refl _)

def cartierMiddlePowerIso (A L M : LineBundle X) (n : ℕ) :
    (A.tensor ((L.pow n).tensor M)).sheaf ≅
      ((L.pow n).tensor (A.tensor M)).sheaf :=
  (lineTensorAssoc A (L.pow n) M).symm ≪≫
    moduleTensorIso (moduleTensorComm A.sheaf (L.pow n).sheaf) (Iso.refl M.sheaf) ≪≫
      lineTensorAssoc (L.pow n) A M

def pullbackCartierMiddleIso (f : Y ⟶ X) (A L M : LineBundle X) (n : ℕ) :
    (Scheme.Modules.pullback f).obj (A.tensor ((L.pow n).tensor M)).sheaf ≅
      (((L.pullback f).pow n).tensor ((A.pullback f).tensor (M.pullback f))).sheaf :=
  PiExponentSeshadri.PullbackTensor.iso f A ((L.pow n).tensor M) ≪≫
    moduleTensorIso (Iso.refl _) (pullbackMixedPowerIso f L M n) ≪≫
      cartierMiddlePowerIso (A.pullback f) (L.pullback f) (M.pullback f) n

theorem eulerCharacteristic_pullback_cartierMiddle
    (p : X ⟶ Spec (CommRingCat.of ℂ)) (f : Y ⟶ X)
    (A L M : LineBundle X) (n r : ℕ) :
    eulerCharacteristic (f ≫ p) r
      ((Scheme.Modules.pullback f).obj (A.tensor ((L.pow n).tensor M)).sheaf) =
    eulerCharacteristic (f ≫ p) r
      (((L.pullback f).pow n).tensor ((A.pullback f).tensor (M.pullback f))).sheaf :=
  eulerCharacteristic_iso (f ≫ p) (pullbackCartierMiddleIso f A L M n) r

theorem fwdDiff_eulerCharacteristic_left_pow_eq_zero [IsNoetherian X]
    (p : X ⟶ Spec (CommRingCat.of ℂ)) (L M : LineBundle X) (r : ℕ)
    (hdim : topologicalKrullDim X ≤ 0) :
    fwdDiff (1 : ℕ) (fun n => eulerCharacteristic p r ((L.pow n).tensor M).sheaf) = 0 := by
  have he (n : ℕ) : eulerCharacteristic p r ((L.pow n).tensor M).sheaf =
      eulerCharacteristic p r M.sheaf := by
    obtain ⟨e⟩ := lineBundle_trivial_of_dim_le_zero hdim (L.pow n)
    exact eulerCharacteristic_iso p
      (moduleTensorIso e (Iso.refl M.sheaf) ≪≫ moduleTensorUnit M.sheaf) r
  funext n
  simp only [fwdDiff, he, sub_self, Pi.zero_apply]

end
end PiExponent.NumericalAmpleness

end OAI
end Source0686

-- Source: OAI/NumberTheory/PiExponent/Ampleness/NakaiStationarity.lean
section Source0687
/-
Modification notice for the LogTwo project.
Derived from openai/math (Apache-2.0), revision adc7f1241b42e322a6451854ab7e4b4c146bf78a.
Original source: lean/OAI/NumberTheory/PiExponent/Ampleness/NakaiStationarity.lean
Changes: Convert module/import declarations to the Lean 4.34 public module format.
See ../THIRD_PARTY_NOTICES.txt for provenance and the recorded changes.
-/

namespace OAI

namespace PiExponent.NumericalAmpleness
noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace Filter
open PiExponentSeshadri.Geometry
open PiExponent.SectionZeroIdeal
variable {X Y : Scheme.{0}}
attribute [local irreducible] CartierEulerPair.middleIso lineTensorAssoc moduleTensorComm
  pullbackCartierMiddleIso

theorem eventual_closed_cartierMiddle_cohomology_zero
    (p : X ⟶ Spec (CommRingCat.of ℂ)) [IsProper p]
    (f : Y ⟶ X) [IsClosedImmersion f] (A L M : LineBundle X)
    (hL : (L.pullback f).IsAmple) :
    ∃ N, ∀ n, N ≤ n → ∀ q, 0 < q → ∀ z : cohomology
      ((Scheme.Modules.pushforward f).obj
        ((Scheme.Modules.pullback f).obj (A.tensor ((L.pow n).tensor M)).sheaf)) q, z = 0 := by
  let T := (A.pullback f).tensor (M.pullback f)
  let := PiExponent.GeometrySupport.LineBundleCoherent.lineBundle_isFinitePresentation T
  obtain ⟨N,hN⟩ := GeometrySupport.NoetherianAmpleSerreVanishing.ample_serre_tensor_vanishing
    (f ≫ p) (L.pullback f) hL T.sheaf
  refine ⟨N,fun n hn q hq => ?_⟩
  apply (ClosedImmersionSerreTransfer.ext_zero_iff f
    ((Scheme.Modules.pullback f).obj (A.tensor ((L.pow n).tensor M)).sheaf) q).mp
  let e := pullbackCartierMiddleIso f A L M n ≪≫
    moduleTensorComm ((L.pullback f).pow n).sheaf T.sheaf
  exact GeometrySupport.SerrePowerDescent.ext_zero_of_iso e.symm q (hN n hn q hq)

theorem eventual_mixedPower_cohomology_stationary
    (p : X ⟶ Spec (CommRingCat.of ℂ)) [IsProper p]
    (L B M : LineBundle X)
    (s : GlobalSections X (L.tensor B).sheaf) (t : GlobalSections X B.sheaf)
    [Mono s] [Mono t]
    (hD : (L.pullback (zeroIdeal (L.tensor B) s).subschemeι).IsAmple)
    (hE : (L.pullback (zeroIdeal B t).subschemeι).IsAmple)
    (q : ℕ) (hq : 0 < q) :
    ∃ N, ∀ n, N ≤ n →
      cohomologyDimension p ((L.pow n).tensor M).sheaf (q+1) =
        cohomologyDimension p ((L.pow N).tensor M).sheaf (q+1) := by
  obtain ⟨D,hDN⟩ := eventual_closed_cartierMiddle_cohomology_zero p
    (zeroIdeal (L.tensor B) s).subschemeι (L.tensor B) L M hD
  obtain ⟨E,hEN⟩ := eventual_closed_cartierMiddle_cohomology_zero p
    (zeroIdeal B t).subschemeι B L M hE
  let N := max D E
  have hstep (n : ℕ) (hn : N ≤ n) :
      cohomologyDimension p ((L.pow n).tensor M).sheaf (q+1) =
        cohomologyDimension p ((L.pow (n+1)).tensor M).sheaf (q+1) := by
    have hnD : D ≤ n := (le_max_left D E).trans hn
    have hnE : E ≤ n+1 := (le_max_right D E).trans (hn.trans (Nat.le_succ n))
    have hleft := cohomologyDimension_eq_of_quotient_vanishing p
      (CartierEulerPair.leftComplex p L B M s n)
      (CartierEulerPair.left_shortExact p L B M s n) q
      (hDN n hnD q hq) (hDN n hnD (q+1) (by omega))
    have hright := cohomologyDimension_eq_of_quotient_vanishing p
      (CartierEulerPair.rightComplex p L B M t n)
      (CartierEulerPair.right_shortExact p L B M t n) q
      (hEN (n+1) hnE q hq) (hEN (n+1) hnE (q+1) (by omega))
    exact hleft.trans hright.symm
  refine ⟨N,fun n hn => ?_⟩
  obtain ⟨j,rfl⟩ := Nat.exists_eq_add_of_le hn
  induction j with
  | zero => simp
  | succ j ih =>
    exact (hstep (N+j) (by omega)).symm.trans (ih (by omega))

theorem eventually_nonzero_mixedPower_sections_of_growth
    (p : X ⟶ Spec (CommRingCat.of ℂ)) [IsProper p]
    (L B M : LineBundle X)
    (s : GlobalSections X (L.tensor B).sheaf) (t : GlobalSections X B.sheaf)
    [Mono s] [Mono t]
    (hD : (L.pullback (zeroIdeal (L.tensor B) s).subschemeι).IsAmple)
    (hE : (L.pullback (zeroIdeal B t).subschemeι).IsAmple)
    (d : ℕ) (hd : 1 ≤ d)
    (hgrowth : Tendsto (fun n => eulerCharacteristic p d ((L.pow n).tensor M).sheaf) atTop atTop) :
    ∀ᶠ n in atTop, ∃ s : GlobalSections X ((L.pow n).tensor M).sheaf, s ≠ 0 := by
  apply eventually_nonzero_globalSection_of_eventually_stationary p
    (fun n => ((L.pow n).tensor M).sheaf) d hd hgrowth
  intro j hj hjd
  obtain ⟨q,rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : j ≠ 0)
  exact eventual_mixedPower_cohomology_stationary p L B M s t hD hE q (by omega)

end
end PiExponent.NumericalAmpleness

end OAI
end Source0687

-- Source: OAI/NumberTheory/PiExponent/Cohomology/EulerRegularTwists.lean
section Source0688
/-
Modification notice for the LogTwo project.
Derived from openai/math (Apache-2.0), revision adc7f1241b42e322a6451854ab7e4b4c146bf78a.
Original source: lean/OAI/NumberTheory/PiExponent/Cohomology/EulerRegularTwists.lean
Changes: Convert module/import declarations to the Lean 4.34 public module format.
See ../THIRD_PARTY_NOTICES.txt for provenance and the recorded changes.
-/

namespace OAI

namespace PiExponent.NumericalAmpleness
noncomputable section
open AlgebraicGeometry CategoryTheory TopologicalSpace
open PiExponentSeshadri.Geometry
variable {X : Scheme.{0}}

theorem exists_common_tensor_generators [IsNoetherian X]
    (H L : LineBundle X) (hH : H.IsAmple) :
    ∃ n : ℕ, ∃ G : (H.pow n).sheaf.GeneratingSections, G.IsFiniteType ∧
      ∃ G' : (L.tensor (H.pow n)).sheaf.GeneratingSections, G'.IsFiniteType := by
  let : L.sheaf.IsFinitePresentation :=
    PiExponent.GeometrySupport.LineBundleCoherent.lineBundle_isFinitePresentation L
  obtain ⟨N, hN⟩ := PiExponent.AmpleGlobalGeneration.ample_eventual_power_global_generators H hH
  obtain ⟨N', hN'⟩ := PiExponent.AmpleGlobalGeneration.ample_eventual_global_generators H hH L.sheaf
  let n := max N N'
  obtain ⟨G, hG⟩ := hN n (le_max_left _ _)
  obtain ⟨G', hG'⟩ := hN' n (le_max_right _ _)
  exact ⟨n, G, hG,
    SheafOfModules.GeneratingSections.equivOfIso (moduleTwistPowerIso H L.sheaf n) G',
    ⟨hG'.finite⟩⟩

end
end PiExponent.NumericalAmpleness

end OAI
end Source0688

-- Source: OAI/NumberTheory/PiExponent/Geometry/ProjectiveSpaceFinite.lean
section Source0689
/-
Modification notice for the LogTwo project.
Derived from openai/math (Apache-2.0), revision adc7f1241b42e322a6451854ab7e4b4c146bf78a.
Original source: lean/OAI/NumberTheory/PiExponent/Geometry/ProjectiveSpaceFinite.lean
Changes: Convert module/import declarations to the Lean 4.34 public module format.
See ../THIRD_PARTY_NOTICES.txt for provenance and the recorded changes.
-/

namespace OAI

namespace PiExponent.ProjectiveSpaceFinite
noncomputable section
open AlgebraicGeometry CategoryTheory TopologicalSpace
open PiExponentSeshadri.Geometry PiExponentSeshadri.Projective
open ProjectiveO1 CohomologyFiniteness
attribute [local instance] MvPolynomial.gradedAlgebra
attribute [local irreducible] ProjectiveO1.lineBundle ProjectiveO1.coordinateCocycle
  ProjectiveO1.coordinateSection sectionsMorphism CoordinateAtlas.morphism atlasOfFramedSections
  CohomologyFinite
variable {X : Scheme.{0}}

theorem projectiveSpace_cohomology_finite (r : ℕ)
    (M : (projectiveSpace ℂ (Fin (r+1))).Modules) [M.IsFinitePresentation] (q : ℕ) :
    CohomologyFinite (polynomialProjectiveProjection ℂ (Fin (r+1))) M q := by
  have hid : sectionsMorphism
      (X := projectiveSpace ℂ (Fin (r+1))) (K := ℂ) (σ := Fin (r+1))
      (M := (lineBundle (R := ℂ) (σ := Fin (r+1))).sheaf)
      (baseScalars (polynomialProjectiveProjection ℂ (Fin (r+1))))
      (coordinateSection (R := ℂ) (σ := Fin (r+1))) coordinateSection_cover =
      (Iso.refl (projectiveSpace ℂ (Fin (r+1)))).hom := by
    change sectionsMorphism
      (M := (lineBundle (R := ℂ) (σ := Fin (r+1))).sheaf)
      (baseScalars (polynomialProjectiveProjection ℂ (Fin (r+1))))
      (coordinateSection (R := ℂ) (σ := Fin (r+1)))
      (coordinateSection_cover (R := ℂ) (σ := Fin (r+1))) =
        𝟙 (projectiveSpace ℂ (Fin (r+1)))
    exact coordinate_sectionsMorphism_identity (R := ℂ) (σ := Fin (r+1))
  exact coordinateBundle_finite (X := projectiveSpace ℂ (Fin (r+1)))
    (polynomialProjectiveProjection ℂ (Fin (r+1)))
    (lineBundle (R := ℂ) (σ := Fin (r+1))) (r+1) (Nat.succ_pos r)
    (coordinateSection (R := ℂ) (σ := Fin (r+1)))
    (coordinateSection_cover (R := ℂ) (σ := Fin (r+1)))
    (Iso.refl (projectiveSpace ℂ (Fin (r+1)))) hid M q

theorem projectiveEmbedding_cohomology_finite (r : ℕ)
    (i : X ⟶ projectiveSpace ℂ (Fin (r+1))) [IsClosedImmersion i]
    (M : X.Modules) [M.IsFinitePresentation] (q : ℕ) :
    letI := Module.compHom (cohomology M q)
      (baseScalars (i ≫ polynomialProjectiveProjection ℂ (Fin (r+1))))
    FiniteDimensional ℂ (cohomology M q) := by
  exact finiteDimensional (i ≫ polynomialProjectiveProjection ℂ (Fin (r+1))) M q
    (closedPushforward_finite i (polynomialProjectiveProjection ℂ (Fin (r+1))) M q
      (projectiveSpace_cohomology_finite r ((Scheme.Modules.pushforward i).obj M) q))

theorem projectiveOver_cohomology_finite (p : X ⟶ Spec (CommRingCat.of ℂ)) (r : ℕ)
    (i : X ⟶ projectiveSpace ℂ (Fin (r+1))) [IsClosedImmersion i]
    (hi : i ≫ polynomialProjectiveProjection ℂ (Fin (r+1)) = p)
    (M : X.Modules) [M.IsFinitePresentation] (q : ℕ) :
    letI := Module.compHom (cohomology M q) (baseScalars p)
    FiniteDimensional ℂ (cohomology M q) := by
  subst p
  exact projectiveEmbedding_cohomology_finite r i M q

end
end PiExponent.ProjectiveSpaceFinite

end OAI
end Source0689

-- Source: OAI/NumberTheory/PiExponent/Ampleness/NakaiEffectivity.lean
section Source0690
/-
Modification notice for the LogTwo project.
Derived from openai/math (Apache-2.0), revision adc7f1241b42e322a6451854ab7e4b4c146bf78a.
Original source: lean/OAI/NumberTheory/PiExponent/Ampleness/NakaiEffectivity.lean
Changes: Convert module/import declarations to the Lean 4.34 public module format.
See ../THIRD_PARTY_NOTICES.txt for provenance and the recorded changes.
-/

namespace OAI

namespace PiExponent.NumericalAmpleness
noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace Filter
open PiExponentSeshadri.Geometry
open PiExponent.SectionZeroIdeal
variable {X : Scheme.{0}}

theorem exists_nonzero_power_section_of_euler_growth
    (p : X ⟶ Spec (CommRingCat.of ℂ)) [IsProper p]
    (H L : LineBundle X) (hH : H.IsAmple) (d : ℕ)
    (hdim : topologicalKrullDim X ≤ d+1)
    (hlower : ∀ I : X.IdealSheafData, topologicalKrullDim I.subscheme ≤ d →
      (L.pullback I.subschemeι).IsAmple)
    (hgrowth : Tendsto (fun n => eulerCharacteristic p (d+1) (L.pow n).sheaf) atTop atTop) :
    ∃ a : ℕ, 0 < a ∧ ∃ s : GlobalSections X (L.pow a).sheaf, s ≠ 0 := by
  let : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian p
  let : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace p
  let : IsNoetherian X := {}
  obtain ⟨b,G,hG,G',hG'⟩ := exists_common_tensor_generators H L hH
  let := hG
  let := hG'
  let B := H.pow b
  obtain ⟨k,u,hu⟩ := GeneratorsSectionCover.exists_fin_section_cover B G
  obtain ⟨k',v,hv⟩ := GeneratorsSectionCover.exists_fin_section_cover (L.tensor B) G'
  obtain ⟨s,hs⟩ := exists_mono_section_of_finite_cover p (L.tensor B) v hv
  obtain ⟨t,ht⟩ := exists_mono_section_of_finite_cover p B u hu
  let := hs
  let := ht
  have hD := hlower (zeroIdeal (L.tensor B) s)
    (regular_sectionZero_dimension_le (L.tensor B) s d hdim)
  have hE := hlower (zeroIdeal B t) (regular_sectionZero_dimension_le B t d hdim)
  have heuler (n : ℕ) : eulerCharacteristic p (d+1) ((L.pow n).tensor (H.pow 0)).sheaf =
      eulerCharacteristic p (d+1) (L.pow n).sheaf :=
    eulerCharacteristic_iso p (moduleTensorRightUnit (L.pow n).sheaf) (d+1)
  have hgrowth' : Tendsto
      (fun n => eulerCharacteristic p (d+1) ((L.pow n).tensor (H.pow 0)).sheaf) atTop atTop := by
    simpa only [heuler] using hgrowth
  have hsections := eventually_nonzero_mixedPower_sections_of_growth p L B (H.pow 0)
    s t hD hE (d+1) (by omega) hgrowth'
  obtain ⟨N,hN⟩ := eventually_atTop.mp hsections
  obtain ⟨σ,hσ⟩ := hN (N+1) (by omega)
  let e := moduleTensorRightUnit (L.pow (N+1)).sheaf
  refine ⟨N+1,by omega,σ ≫ e.hom,?_⟩
  intro hz
  apply hσ
  apply (cancel_mono e.hom).mp
  exact hz.trans (zero_comp (C := X.Modules) (f := e.hom)).symm

theorem exists_power_section_cover_of_euler_growth [IsIntegral X]
    (p : X ⟶ Spec (CommRingCat.of ℂ)) [IsProper p]
    (r : ℕ) (i : X ⟶ ProjectiveO1.projectiveSpace ℂ (Fin (r+1))) [IsClosedImmersion i]
    (hi : i ≫ PiExponent.polynomialProjectiveProjection ℂ (Fin (r+1)) = p)
    (H L : LineBundle X) (hH : H.IsAmple) (d : ℕ)
    (hdim : topologicalKrullDim X ≤ d+1)
    (hlower : ∀ I : X.IdealSheafData, topologicalKrullDim I.subscheme ≤ d →
      (L.pullback I.subschemeι).IsAmple)
    (hgrowth : Tendsto (fun n => eulerCharacteristic p (d+1) (L.pow n).sheaf) atTop atTop) :
    ∃ a : ℕ, 0 < a ∧ ∃ k : ℕ, ∃ s : Fin k → GlobalSections X (L.pow a).sheaf,
      (⨆ j, sectionOpen X (s j)) = ⊤ := by
  obtain ⟨a,ha,s,hs⟩ := exists_nonzero_power_section_of_euler_growth p H L hH d hdim hlower hgrowth
  let A := L.pow a
  let := A.mono_section s hs
  let j := (zeroIdeal A s).subschemeι
  have hL := hlower (zeroIdeal A s) (regular_sectionZero_dimension_le A s d hdim)
  have hA : (A.pullback j).IsAmple :=
    PiExponent.AmpleIso.isAmple_of_sheaf_iso ((L.pullback j).pow a) (A.pullback j)
      (PiExponentSeshadri.PullbackTensor.powIso j L a).symm (hL.pow a ha)
  have hfinite (n : ℕ) : letI := Module.compHom (cohomology (A.pow n).sheaf 1) (baseScalars p)
      FiniteDimensional ℂ (cohomology (A.pow n).sheaf 1) := by
    let := PiExponent.GeometrySupport.LineBundleCoherent.lineBundle_isFinitePresentation (A.pow n)
    exact ProjectiveSpaceFinite.projectiveOver_cohomology_finite p r i hi (A.pow n).sheaf 1
  obtain ⟨N,hN⟩ := eventual_power_section_cover_of_ample_zeroDivisor p A s hfinite hA
  obtain ⟨k,t,ht⟩ := hN N le_rfl
  let e := linePowerMul L a (N+1)
  refine ⟨a*(N+1),Nat.mul_pos ha (by omega),k,fun z => t z ≫ e.hom,?_⟩
  exact (iSup_congr fun j =>
    PiExponent.AmpleIso.sectionOpen_postcomp_iso (t j) e).trans ht

end
end PiExponent.NumericalAmpleness

end OAI
end Source0690

-- Source: OAI/NumberTheory/PiExponent/LocalAlgebra/FiniteFromClosedFibers.lean
section Source0691
/-
Modification notice for the LogTwo project.
Derived from openai/math (Apache-2.0), revision adc7f1241b42e322a6451854ab7e4b4c146bf78a.
Original source: lean/OAI/NumberTheory/PiExponent/LocalAlgebra/FiniteFromClosedFibers.lean
Changes: Convert module/import declarations to the Lean 4.34 public module format.
See ../THIRD_PARTY_NOTICES.txt for provenance and the recorded changes.
-/

namespace OAI

noncomputable section
namespace PiExponent.NumericalAmpleness
open CategoryTheory AlgebraicGeometry TopologicalSpace Set
universe u

theorem isFinite_of_proper_finite_closed_fibers {X Y : Scheme.{u}}
    (f : X ⟶ Y) [IsProper f] [JacobsonSpace Y]
    (hfinite : ∀ y : Y, IsClosed ({y} : Set Y) → (f ⁻¹' {y}).Finite) : IsFinite f := by
  have htop : f.quasiFiniteLocus = ⊤ := by
    apply top_unique
    intro x _
    by_contra hx
    have hclosed : IsClosed (f '' ((f.quasiFiniteLocus : Set X)ᶜ)) :=
      f.isClosedMap _ f.quasiFiniteLocus.isOpen.isClosed_compl
    obtain ⟨y, ⟨z, hz, hzy⟩, hy⟩ :=
      nonempty_inter_closedPoints (Z := f '' ((f.quasiFiniteLocus : Set X)ᶜ))
        ⟨f x, x, hx, rfl⟩ hclosed.isLocallyClosed
    have hfin : (f ⁻¹' {f z}).Finite := by rw [hzy]; exact hfinite y hy
    let : Finite (f.fiber (f z)) := (f.fiberHomeo (f z)).finite_iff.mpr hfin
    have hq : f.QuasiFiniteAt z :=
      Scheme.Hom.quasiFiniteAt_iff_isOpen_singleton_asFiber.mpr (isOpen_discrete _)
    exact hz hq
  let : LocallyQuasiFinite f := (Scheme.Hom.quasiFiniteLocus_eq_top_iff f).mp htop
  exact IsFinite.of_isProper_of_locallyQuasiFinite f

end PiExponent.NumericalAmpleness

end

end OAI
end Source0691

-- Source: OAI/NumberTheory/PiExponent/Geometry/FiniteOfNoContractedCurves.lean
section Source0692
/-
Modification notice for the LogTwo project.
Derived from openai/math (Apache-2.0), revision adc7f1241b42e322a6451854ab7e4b4c146bf78a.
Original source: lean/OAI/NumberTheory/PiExponent/Geometry/FiniteOfNoContractedCurves.lean
Changes: Convert module/import declarations to the Lean 4.34 public module format.
See ../THIRD_PARTY_NOTICES.txt for provenance and the recorded changes.
-/

namespace OAI

noncomputable section
namespace PiExponent.NumericalAmpleness
open CategoryTheory AlgebraicGeometry TopologicalSpace Set

private theorem positive_dimension_eq_nat {D : WithBot ℕ∞} (d : ℕ)
    (hD : D ≤ d) (hpos : 0 < D) : ∃ n : ℕ, D = n ∧ 0 < n := by
  have hbot : D ≠ ⊥ := by
    intro h
    rw [h] at hpos
    exact not_lt_bot hpos
  obtain ⟨e, rfl⟩ := WithBot.ne_bot_iff_exists.mp hbot
  have he : e ≤ (d : ℕ∞) := by exact_mod_cast hD
  have hetop : e ≠ ⊤ := ne_of_lt (he.trans_lt (by simp))
  obtain ⟨n, rfl⟩ := ENat.ne_top_iff_exists.mp hetop
  exact ⟨n, rfl, by exact_mod_cast hpos⟩

def integralCurveFromClosedFiber {X Y : Scheme.{0}} (f : X ⟶ Y) (y : Y)
    (hy : IsClosed ({y} : Set Y)) (C : IntegralCurve (f.fiber y)) : IntegralCurve X := by
  let : IsClosedImmersion (Y.fromSpecResidueField y) :=
    isClosed_singleton_iff_isClosedImmersion.mp hy
  let : IsClosedImmersion (f.fiberι y) := by
    unfold Scheme.Hom.fiberι
    let : MorphismProperty.IsStableUnderBaseChange (@IsClosedImmersion.{0}) :=
      IsClosedImmersion.isStableUnderBaseChange
    exact MorphismProperty.of_isPullback (P := @IsClosedImmersion.{0})
      (IsPullback.of_hasPullback f (Y.fromSpecResidueField y)).flip
      (show IsClosedImmersion (Y.fromSpecResidueField y) from inferInstance)
  exact {
    scheme := C.scheme
    embedding := C.embedding ≫ f.fiberι y
    closedImmersion := inferInstance
    integral := C.integral
    dimension := C.dimension }

theorem finite_closed_fiber_of_no_integralCurve {X Y : Scheme.{0}}
    (f : X ⟶ Y) [IsProper f] (d : ℕ) (hdim : topologicalKrullDim X ≤ d)
    (y : Y) (hno : IsEmpty (IntegralCurve (f.fiber y))) : (f ⁻¹' {y}).Finite := by
  have hbound : topologicalKrullDim (f.fiber y) ≤ d :=
    (f.fiberι y).isEmbedding.topologicalKrullDim_le.trans hdim
  have hzero : topologicalKrullDim (f.fiber y) ≤ 0 := by
    by_contra h
    obtain ⟨n, hn, hpos⟩ := positive_dimension_eq_nat d hbound (lt_of_not_ge h)
    obtain ⟨C⟩ := nonempty_integralCurve_of_dimension_pos (f.fiber y) n hn hpos
    exact hno.false C
  let : IsLocallyNoetherian (f.fiber y) := by
    unfold Scheme.Hom.fiber
    infer_instance
  let : IsLocallyArtinian (f.fiber y) := IsLocallyArtinian.of_topologicalKrullDim_le_zero hzero
  let : Finite (f.fiber y) := finite_of_compact_of_discrete
  exact (f.fiberHomeo y).finite_iff.mp inferInstance

theorem isFinite_of_no_contracted_integralCurves {X Y : Scheme.{0}}
    (f : X ⟶ Y) [IsProper f] [JacobsonSpace Y]
    (d : ℕ) (hdim : topologicalKrullDim X ≤ d)
    (hno : ∀ (C : IntegralCurve X) (y : Y) (_hy : IsClosed ({y} : Set Y))
      (j : C.scheme ⟶ f.fiber y), j ≫ f.fiberι y = C.embedding → False) : IsFinite f := by
  apply isFinite_of_proper_finite_closed_fibers f
  intro y hy
  apply finite_closed_fiber_of_no_integralCurve f d hdim y
  refine ⟨fun C => ?_⟩
  exact hno (integralCurveFromClosedFiber f y hy C) y hy C.embedding rfl

end PiExponent.NumericalAmpleness

end

end OAI
end Source0692

-- Source: OAI/NumberTheory/PiExponent/Ampleness/NakaiAmpleFromSections.lean
section Source0693
/-
Modification notice for the LogTwo project.
Derived from openai/math (Apache-2.0), revision adc7f1241b42e322a6451854ab7e4b4c146bf78a.
Original source: lean/OAI/NumberTheory/PiExponent/Ampleness/NakaiAmpleFromSections.lean
Changes: Convert module/import declarations to the Lean 4.34 public module format.
See ../THIRD_PARTY_NOTICES.txt for provenance and the recorded changes.
-/

namespace OAI

namespace PiExponent.NumericalAmpleness
noncomputable section
open AlgebraicGeometry CategoryTheory TopologicalSpace
open PiExponentSeshadri.Geometry PiExponentSeshadri.Projective PiExponentSeshadri.Frames
attribute [local instance] MvPolynomial.gradedAlgebra
variable {X : Scheme.{0}}

theorem curveDegree_eq_zero_of_sectionsMorphism_contracted
    (p : X ⟶ Spec (CommRingCat.of ℂ)) (L : LineBundle X)
    (k : ℕ) (s : Fin k → GlobalSections X L.sheaf)
    (hs : (⨆ z, sectionOpen X (s z)) = ⊤)
    (C : IntegralCurve X)
    (y : ProjectiveO1.projectiveSpace ℂ (Fin k))
    (hconstant : ∀ c : C.scheme, sectionsMorphism (baseScalars p) s hs (C.embedding c) = y) :
    curveDegree p L C = 0 := by
  classical
  obtain ⟨c⟩ : Nonempty C.scheme := inferInstance
  have hc : C.embedding c ∈ ⨆ z, sectionOpen X (s z) := by rw [hs]; trivial
  obtain ⟨z,hz⟩ := Opens.mem_iSup.mp hc
  have hpre : sectionsMorphism (baseScalars p) s hs ⁻¹ᵁ
      Proj.basicOpen (MvPolynomial.homogeneousSubmodule (Fin k) ℂ) (MvPolynomial.X z) =
      sectionOpen X (s z) := sectionsMorphism_preimage (baseScalars p) s hs z
  have hy : y ∈ Proj.basicOpen (MvPolynomial.homogeneousSubmodule (Fin k) ℂ)
      (MvPolynomial.X z) := by
    rw [← hpre] at hz
    change sectionsMorphism (baseScalars p) s hs (C.embedding c) ∈
      Proj.basicOpen (MvPolynomial.homogeneousSubmodule (Fin k) ℂ) (MvPolynomial.X z) at hz
    rwa [hconstant c] at hz
  have hrange : Set.range C.embedding ⊆ (sectionOpen X (s z) : Set X) := by
    rintro x ⟨c',rfl⟩
    rw [← hpre]
    change sectionsMorphism (baseScalars p) s hs (C.embedding c') ∈
      Proj.basicOpen (MvPolynomial.homogeneousSubmodule (Fin k) ℂ) (MvPolynomial.X z)
    rwa [hconstant c']
  let e := ConstantPullbackDegree.pullbackFrame_of_range_subset L C.embedding
    (sectionOpen X (s z)) hrange (sectionFrame (s z))
  change eulerCharacteristic (C.embedding ≫ p) 1 (L.pullback C.embedding).sheaf -
    eulerCharacteristic (C.embedding ≫ p) 1 (structureSheaf C.scheme) = 0
  rw [eulerCharacteristic_iso (C.embedding ≫ p) e 1]
  exact sub_self _

theorem isAmple_of_section_cover_of_curveDegree_pos [IsIntegral X]
    (p : X ⟶ Spec (CommRingCat.of ℂ)) [IsProper p]
    (L : LineBundle X) (d : ℕ) (hdim : topologicalKrullDim X ≤ d)
    (k : ℕ) (s : Fin k → GlobalSections X L.sheaf)
    (hs : (⨆ z, sectionOpen X (s z)) = ⊤)
    (hpositive : ∀ C : IntegralCurve X, 0 < curveDegree p L C) : L.IsAmple := by
  let : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace p
  let : IsProper (X.toSpecΓ ≫ Spec.map (CommRingCat.ofHom (baseScalars p))) := by
    change IsProper (X.toSpecΓ ≫ Spec.map (CommRingCat.ofHom
      (p.appTop.hom.comp (Scheme.ΓSpecIso (CommRingCat.of ℂ)).inv.hom)))
    rw [toSpec_scalarMap p]
    infer_instance
  let f : X ⟶ ProjectiveO1.projectiveSpace ℂ (Fin k) :=
    sectionsMorphism (baseScalars p) s hs
  let : IsProper f := sectionsMorphism_proper (baseScalars p) s hs
  let : JacobsonSpace (ProjectiveO1.projectiveSpace ℂ (Fin k)) :=
    LocallyOfFiniteType.jacobsonSpace (polynomialProjectiveProjection ℂ (Fin k))
  let : IsFinite f := isFinite_of_no_contracted_integralCurves f d hdim (by
    intro C y hy j hj
    have hconstant (c : C.scheme) : f (C.embedding c) = y := by
      have hc : f.fiberι y (j c) ∈ Set.range (f.fiberι y) := ⟨j c,rfl⟩
      rw [f.range_fiberι] at hc
      change f (f.fiberι y (j c)) = y at hc
      have he := congrArg (fun g : C.scheme ⟶ X => g c) hj
      simpa only [Scheme.Hom.comp_apply] using he ▸ hc
    have hz := curveDegree_eq_zero_of_sectionsMorphism_contracted p L k s hs C y hconstant
    have hp := hpositive C
    omega)
  apply L.ample_of_affine_section_cover s hs
  intro z
  change IsAffineOpen (PiExponentSeshadri.SectionOpens.isoOpen (s z))
  exact (sectionsMorphism_preimage (baseScalars p) s hs z) ▸
    (standardChart_isAffineOpen (R := ℂ) z).preimage f

end
end PiExponent.NumericalAmpleness

end OAI
end Source0693

-- Source: OAI/NumberTheory/PiExponent/Cohomology/EulerDifferencePolynomial.lean
section Source0694
/-
Modification notice for the LogTwo project.
Derived from openai/math (Apache-2.0), revision adc7f1241b42e322a6451854ab7e4b4c146bf78a.
Original source: lean/OAI/NumberTheory/PiExponent/Cohomology/EulerDifferencePolynomial.lean
Changes: Convert module/import declarations to the Lean 4.34 public module format.
See ../THIRD_PARTY_NOTICES.txt for provenance and the recorded changes.
-/

namespace OAI

namespace PiExponent.NumericalAmpleness

open Filter Finset Function
open scoped Topology BigOperators

theorem forwardDifference_eq_zero_of_le {G : Type*} [AddCommGroup G]
    (f : ℕ → G) (d : ℕ) (hzero : (fwdDiff (1 : ℕ))^[d] f = 0)
    (k : ℕ) (hk : d ≤ k) : (fwdDiff (1 : ℕ))^[k] f = 0 := by
  obtain ⟨r,rfl⟩ := Nat.exists_eq_add_of_le hk
  rw [Nat.add_comm d r, Function.iterate_add_apply, hzero]
  ext n
  simp [fwdDiff_iter_eq_sum_shift]

theorem newton_sum_of_forwardDifference_eq_zero {G : Type*} [AddCommGroup G]
    (f : ℕ → G) (d : ℕ) (hzero : (fwdDiff (1 : ℕ))^[d+1] f = 0) (n : ℕ) :
    f n = ∑ k ∈ Finset.range (d+1), n.choose k • (fwdDiff (1 : ℕ))^[k] f 0 := by
  have hNewton : f n = ∑ k ∈ Finset.range (n+1),
      n.choose k • (fwdDiff (1 : ℕ))^[k] f 0 := by
    simpa using shift_eq_sum_fwdDiff_iter (1 : ℕ) f n 0
  rw [hNewton]
  by_cases hnd : n ≤ d
  · apply Finset.sum_subset (Finset.range_mono (by omega : n+1 ≤ d+1))
    intro k hk hkn
    have hnk : n < k := by simp only [Finset.mem_range] at hkn; omega
    rw [Nat.choose_eq_zero_of_lt hnk, zero_smul]
  · symm
    apply Finset.sum_subset (Finset.range_mono (by omega : d+1 ≤ n+1))
    intro k hk hkd
    have hdk : d+1 ≤ k := by simp only [Finset.mem_range] at hkd; omega
    rw [forwardDifference_eq_zero_of_le f (d+1) hzero k hdk]
    simp

theorem integer_newton_sum_of_forwardDifference_eq_zero
    (f : ℕ → ℤ) (d : ℕ) (hzero : (fwdDiff (1 : ℕ))^[d+1] f = 0) (n : ℕ) :
    f n = ∑ k ∈ Finset.range (d+1),
      (n.choose k : ℤ) * (fwdDiff (1 : ℕ))^[k] f 0 := by
  simpa only [nsmul_eq_mul] using newton_sum_of_forwardDifference_eq_zero f d hzero n

theorem tendsto_choose_div_pow (k d : ℕ) (hkd : k ≤ d) :
    Tendsto (fun n : ℕ => (n.choose k : ℝ) / (n : ℝ)^d) atTop
      (𝓝 (if k = d then 1 / (d.factorial : ℝ) else 0)) := by
  have he := (isEquivalent_choose k).div
    (Asymptotics.IsEquivalent.refl (u := fun n : ℕ => (n : ℝ)^d) (l := atTop))
  apply he.symm.tendsto_nhds
  by_cases h : k = d
  · subst k
    simp only [ite_true]
    apply tendsto_const_nhds.congr'
    filter_upwards [eventually_gt_atTop (0 : ℕ)] with n hn
    have hn' : (n : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hn)
    dsimp
    field_simp
  · simp only [h, ite_false]
    have ht := (tendsto_pow_div_pow_atTop_zero (𝕜 := ℝ) (lt_of_le_of_ne hkd h)).comp
      tendsto_natCast_atTop_atTop
    have ht' := ht.div_const (k.factorial : ℝ)
    change Tendsto (fun n : ℕ => (n : ℝ)^k / (k.factorial : ℝ) / (n : ℝ)^d) _ _
    convert ht' using 1
    · funext n
      simp only [Function.comp_apply]
      ring
    · simp

theorem tendsto_normalized_of_forwardDifference_eq_zero
    (f : ℕ → ℤ) (d : ℕ) (hzero : (fwdDiff (1 : ℕ))^[d+1] f = 0) :
    Tendsto (fun n : ℕ => (f n : ℝ) / (n : ℝ)^d) atTop
      (𝓝 ((((fwdDiff (1 : ℕ))^[d] f 0 : ℤ) : ℝ) / (d.factorial : ℝ))) := by
  have hterm (k : ℕ) (hk : k ∈ Finset.range (d+1)) :=
    (tendsto_choose_div_pow k d (by simpa only [Finset.mem_range, Nat.lt_succ_iff] using hk)).mul_const
      (((fwdDiff (1 : ℕ))^[k] f 0 : ℤ) : ℝ)
  have hs := tendsto_finsetSum (Finset.range (d+1)) hterm
  have hreal (n : ℕ) : (f n : ℝ) = ∑ k ∈ Finset.range (d+1),
      (n.choose k : ℝ) * (((fwdDiff (1 : ℕ))^[k] f 0 : ℤ) : ℝ) := by
    exact_mod_cast integer_newton_sum_of_forwardDifference_eq_zero f d hzero n
  convert hs using 1
  · funext n
    rw [hreal, Finset.sum_div]
    apply Finset.sum_congr rfl
    intro k _
    ring
  · congr 1
    rw [Finset.sum_eq_single d]
    · simp only [ite_true]
      ring
    · intro k hk hkd
      simp [hkd]
    · simp

theorem tendsto_atTop_of_forwardDifference_eq_zero
    (f : ℕ → ℤ) (d : ℕ) (hd : 0 < d)
    (hzero : (fwdDiff (1 : ℕ))^[d+1] f = 0)
    (hpositive : 0 < (fwdDiff (1 : ℕ))^[d] f 0) :
    Tendsto f atTop atTop := by
  have hlead : (0 : ℝ) <
      (((fwdDiff (1 : ℕ))^[d] f 0 : ℤ) : ℝ) / (d.factorial : ℝ) :=
    div_pos (by exact_mod_cast hpositive) (by exact_mod_cast Nat.factorial_pos d)
  have hpow : Tendsto (fun n : ℕ => (n : ℝ)^d) atTop atTop :=
    (tendsto_pow_atTop (Nat.ne_of_gt hd)).comp tendsto_natCast_atTop_atTop
  have ht := (tendsto_normalized_of_forwardDifference_eq_zero f d hzero).pos_mul_atTop
    hlead hpow
  apply (tendsto_intCast_atTop_iff (R := ℝ)).mp
  apply ht.congr'
  filter_upwards [eventually_gt_atTop (0 : ℕ)] with n hn
  have hn' : (n : ℝ)^d ≠ 0 := pow_ne_zero _ (by exact_mod_cast Nat.ne_of_gt hn)
  exact div_mul_cancel₀ _ hn'

end PiExponent.NumericalAmpleness

end OAI
end Source0694

-- Source: OAI/NumberTheory/PiExponent/Cohomology/ProjectiveEmbeddingCohomologyBound.lean
section Source0695
/-
Modification notice for the LogTwo project.
Derived from openai/math (Apache-2.0), revision adc7f1241b42e322a6451854ab7e4b4c146bf78a.
Original source: lean/OAI/NumberTheory/PiExponent/Cohomology/ProjectiveEmbeddingCohomologyBound.lean
Changes: Convert module/import declarations to the Lean 4.34 public module format.
See ../THIRD_PARTY_NOTICES.txt for provenance and the recorded changes.
-/

namespace OAI

namespace PiExponent.NumericalAmpleness
noncomputable section
open AlgebraicGeometry CategoryTheory
open PiExponentSeshadri.Geometry PiExponentSeshadri.Projective
open PiExponent.ProjectiveO1

theorem projectiveSpace_cohomology_eq_zero (r : ℕ)
    (M : (projectiveSpace ℂ (Fin (r+1))).Modules) [M.IsQuasicoherent]
    (q : ℕ) (hq : r+1 ≤ q) (z : cohomology M q) : z = 0 := by
  exact PiExponent.SerreVanishing.ext_eq_zero_of_affine_cover (r+1) (by omega)
    (coordinateOpen (R := ℂ) (σ := Fin (r+1)))
    (fun j => standardChart_isAffineOpen j) standardChart_cover M q hq z

theorem cohomology_eq_zero_of_projective_embedding {X : Scheme.{0}} (r : ℕ)
    (i : X ⟶ projectiveSpace ℂ (Fin (r+1))) [IsClosedImmersion i]
    (M : X.Modules) [M.IsFinitePresentation] (q : ℕ) (hq : r+1 ≤ q)
    (z : cohomology M q) : z = 0 := by
  let N := (Scheme.Modules.pushforward i).obj M
  let : N.IsFinitePresentation := PiExponentSeshadri.ClosedPushforward.pushforward_isFinitePresentation i M
  let : N.IsQuasicoherent :=
    (SheafOfModules.IsFinitePresentation.exists_quasicoherentData N).choose.isQuasicoherent
  let e := PiExponent.ClosedImmersionSerreTransfer.closedCohomologyEquiv i M q
  apply e.injective
  exact (projectiveSpace_cohomology_eq_zero r N q hq (e z)).trans e.map_zero.symm

theorem lineBundle_cohomology_eq_zero_of_projective_embedding {X : Scheme.{0}} (r : ℕ)
    (i : X ⟶ projectiveSpace ℂ (Fin (r+1))) [IsClosedImmersion i]
    (L : LineBundle X) (q : ℕ) (hq : r+1 ≤ q) (z : cohomology L.sheaf q) : z = 0 := by
  let : L.sheaf.IsFinitePresentation :=
    PiExponent.GeometrySupport.LineBundleCoherent.lineBundle_isFinitePresentation L
  exact cohomology_eq_zero_of_projective_embedding r i L.sheaf q hq z

end
end PiExponent.NumericalAmpleness

end OAI
end Source0695

-- Source: OAI/NumberTheory/PiExponent/Cohomology/EulerCutoff.lean
section Source0696
/-
Modification notice for the LogTwo project.
Derived from openai/math (Apache-2.0), revision adc7f1241b42e322a6451854ab7e4b4c146bf78a.
Original source: lean/OAI/NumberTheory/PiExponent/Cohomology/EulerCutoff.lean
Changes: Convert module/import declarations to the Lean 4.34 public module format.
See ../THIRD_PARTY_NOTICES.txt for provenance and the recorded changes.
-/

namespace OAI

namespace PiExponent.NumericalAmpleness
noncomputable section
open AlgebraicGeometry CategoryTheory
open PiExponentSeshadri.Geometry PiExponentSeshadri.Projective
open PiExponent.ProjectiveO1
variable {X : Scheme.{0}}

theorem eulerCharacteristic_eq_of_le_of_cohomology_zero
    (p : X ⟶ Spec (CommRingCat.of ℂ)) (M : X.Modules) (d e : ℕ) (hde : d ≤ e)
    (hzero : ∀ q : ℕ, d < q → ∀ z : cohomology M q, z = 0) :
    eulerCharacteristic p e M = eulerCharacteristic p d M := by
  induction e, hde using Nat.le_induction with
  | base => rfl
  | succ e hde ih =>
    calc
      eulerCharacteristic p (e+1) M = eulerCharacteristic p e M := by
        simpa only [Nat.add_sub_cancel] using
          eulerCharacteristic_eq_pred_of_cohomology_zero p M (e+1)
            (hzero (e+1) (by omega))
      _ = eulerCharacteristic p d M := ih

theorem eulerCharacteristic_projective_eq_dimension
    (p : X ⟶ Spec (CommRingCat.of ℂ)) (r : ℕ)
    (i : X ⟶ projectiveSpace ℂ (Fin (r+1))) [IsClosedImmersion i]
    (hi : i ≫ polynomialProjectiveProjection ℂ (Fin (r+1)) = p)
    (H : LineBundle X) (hH : H.IsAmple) (M : LineBundle X)
    (d : ℕ) (hdim : topologicalKrullDim X ≤ d) :
    eulerCharacteristic p r M.sheaf = eulerCharacteristic p d M.sheaf := by
  let : IsProper p := by rw [← hi]; infer_instance
  rcases le_total d r with h | h
  · exact eulerCharacteristic_eq_of_le_of_cohomology_zero p M.sheaf d r h
      (lineBundle_cohomology_zero_of_dimension_le d p H hH M hdim)
  · symm
    apply eulerCharacteristic_eq_of_le_of_cohomology_zero p M.sheaf r d h
    intro q hq z
    exact lineBundle_cohomology_eq_zero_of_projective_embedding r i M q (by omega) z

end
end PiExponent.NumericalAmpleness

end OAI
end Source0696

-- Source: OAI/NumberTheory/PiExponent/Cohomology/EulerPolynomialInterpolation.lean
section Source0697
-- Modified in this edition: unused plain lemmas removed; see reduction.json.
/-
Modification notice for the LogTwo project.
Derived from openai/math (Apache-2.0), revision adc7f1241b42e322a6451854ab7e4b4c146bf78a.
Original source: lean/OAI/NumberTheory/PiExponent/Cohomology/EulerPolynomialInterpolation.lean
Changes: Convert module/import declarations to the Lean 4.34 public module format.
See ../THIRD_PARTY_NOTICES.txt for provenance and the recorded changes.
-/

namespace OAI

namespace PiExponent.NumericalAmpleness
noncomputable section
open scoped BigOperators

def newtonPolynomial (f : ℕ → ℤ) (d : ℕ) : Polynomial ℚ :=
  ∑ k ∈ Finset.range (d+1),
    Polynomial.C (((fwdDiff (1 : ℕ))^[k] f 0 : ℤ) : ℚ) *
      Polynomial.preHilbertPoly ℚ k k

end
end PiExponent.NumericalAmpleness

end OAI
end Source0697

-- Source: OAI/NumberTheory/PiExponent/Cohomology/EulerRegularSections.lean
section Source0698
/-
Modification notice for the LogTwo project.
Derived from openai/math (Apache-2.0), revision adc7f1241b42e322a6451854ab7e4b4c146bf78a.
Original source: lean/OAI/NumberTheory/PiExponent/Cohomology/EulerRegularSections.lean
Changes: Convert module/import declarations to the Lean 4.34 public module format.
See ../THIRD_PARTY_NOTICES.txt for provenance and the recorded changes.
-/

namespace OAI

namespace PiExponent.NumericalAmpleness
noncomputable section
open AlgebraicGeometry CategoryTheory
open PiExponentSeshadri.Geometry
variable {X : Scheme.{0}}

theorem exists_mono_section_of_generators [IsNoetherian X]
    (p : X ⟶ Spec (CommRingCat.of ℂ)) (L : LineBundle X)
    (G : L.sheaf.GeneratingSections) [G.IsFiniteType] :
    ∃ s : GlobalSections X L.sheaf, Mono s := by
  obtain ⟨k, s, hs⟩ := PiExponent.GeneratorsSectionCover.exists_fin_section_cover L G
  exact exists_mono_section_of_finite_cover p L s hs

theorem exists_regular_twist_pair [IsNoetherian X]
    (p : X ⟶ Spec (CommRingCat.of ℂ)) (H L : LineBundle X) (hH : H.IsAmple) :
    ∃ B : LineBundle X, ∃ s : GlobalSections X (L.tensor B).sheaf,
      ∃ t : GlobalSections X B.sheaf, Mono s ∧ Mono t := by
  obtain ⟨n, G, hG, G', hG'⟩ := exists_common_tensor_generators H L hH
  let : G.IsFiniteType := hG
  let : G'.IsFiniteType := hG'
  obtain ⟨s, hs⟩ := exists_mono_section_of_generators p (L.tensor (H.pow n)) G'
  obtain ⟨t, ht⟩ := exists_mono_section_of_generators p (H.pow n) G
  exact ⟨H.pow n, s, t, hs, ht⟩

end
end PiExponent.NumericalAmpleness

end OAI
end Source0698

-- Source: OAI/NumberTheory/PiExponent/Cohomology/EulerPolynomialDegree.lean
section Source0699
-- Modified in this edition: unused plain lemmas removed; see reduction.json.
/-
Modification notice for the LogTwo project.
Derived from openai/math (Apache-2.0), revision adc7f1241b42e322a6451854ab7e4b4c146bf78a.
Original source: lean/OAI/NumberTheory/PiExponent/Cohomology/EulerPolynomialDegree.lean
Changes: Convert module/import declarations to the Lean 4.34 public module format.
See ../THIRD_PARTY_NOTICES.txt for provenance and the recorded changes.
-/

namespace OAI

namespace PiExponent.NumericalAmpleness
noncomputable section
open AlgebraicGeometry CategoryTheory TopologicalSpace
open PiExponentSeshadri.Geometry PiExponentSeshadri.Projective
open PiExponent.SectionZeroIdeal PiExponent.ProjectiveO1

lemma iterate_fwdDiff_sub {G : Type*} [AddCommGroup G] (f g : ℕ → G) (k : ℕ) :
    (fwdDiff (1 : ℕ))^[k] (f-g) = (fwdDiff (1 : ℕ))^[k] f - (fwdDiff (1 : ℕ))^[k] g := by
  simpa only [fwdDiff_aux.coe_fwdDiffₗ_pow] using
    map_sub (fwdDiff_aux.fwdDiffₗ ℕ G (1 : ℕ) ^ k) f g

private lemma difference_step {G : Type*} [AddCommGroup G] (f g h : ℕ → G) (k : ℕ)
    (hd : fwdDiff (1 : ℕ) f = g - fun n => h (n+1))
    (hg : (fwdDiff (1 : ℕ))^[k] g=0) (hh : (fwdDiff (1 : ℕ))^[k] h=0) :
    (fwdDiff (1 : ℕ))^[k+1] f=0 := by
  rw [Function.iterate_succ_apply, hd, iterate_fwdDiff_sub, hg]
  have hz : (fwdDiff (1 : ℕ))^[k] (fun n => h (n+1))=0 := by
    funext n
    rw [fwdDiff_iter_comp_add, hh]
    rfl
  rw [hz, sub_self]

theorem projective_line_cohomology_finite {X : Scheme.{0}}
    (p : X ⟶ Spec (CommRingCat.of ℂ)) (r : ℕ)
    (i : X ⟶ projectiveSpace ℂ (Fin (r+1))) [IsClosedImmersion i]
    (hi : i ≫ polynomialProjectiveProjection ℂ (Fin (r+1)) = p)
    (L : LineBundle X) (q : ℕ) :
    letI := Module.compHom (cohomology L.sheaf q) (baseScalars p)
    FiniteDimensional ℂ (cohomology L.sheaf q) := by
  let : L.sheaf.IsFinitePresentation :=
    PiExponent.GeometrySupport.LineBundleCoherent.lineBundle_isFinitePresentation L
  exact PiExponent.ProjectiveSpaceFinite.projectiveOver_cohomology_finite p r i hi L.sheaf q

theorem euler_tensor_power_difference_aux (d : ℕ) :
    ∀ {X : Scheme.{0}} [IsNoetherian X]
      (p : X ⟶ Spec (CommRingCat.of ℂ)) (r : ℕ)
      (i : X ⟶ projectiveSpace ℂ (Fin (r+1))) [IsClosedImmersion i]
      (_hi : i ≫ polynomialProjectiveProjection ℂ (Fin (r+1)) = p)
      (H : LineBundle X), H.IsAmple → ∀ (L M : LineBundle X),
      topologicalKrullDim X ≤ d →
      (fwdDiff (1 : ℕ))^[d+1]
        (fun n => eulerCharacteristic p r ((L.pow n).tensor M).sheaf) = 0 := by
  induction d with
  | zero =>
    intro X _ p r i _ hi H hH L M hdim
    simpa only [Nat.zero_add, Function.iterate_one] using
      fwdDiff_eulerCharacteristic_left_pow_eq_zero p L M r hdim
  | succ d ih =>
    intro X _ p r i _ hi H hH L M hdim
    obtain ⟨B, s, t, hs, ht⟩ := exists_regular_twist_pair p H L hH
    let : Mono s := hs
    let : Mono t := ht
    let A := L.tensor B
    let D := zeroIdeal A s
    let E := zeroIdeal B t
    let jD := D.subschemeι
    let jE := E.subschemeι
    let : IsLocallyNoetherian D.subscheme := LocallyOfFiniteType.isLocallyNoetherian jD
    let : CompactSpace D.subscheme := QuasiCompact.compactSpace_of_compactSpace jD
    let : IsNoetherian D.subscheme := {}
    let : IsLocallyNoetherian E.subscheme := LocallyOfFiniteType.isLocallyNoetherian jE
    let : CompactSpace E.subscheme := QuasiCompact.compactSpace_of_compactSpace jE
    let : IsNoetherian E.subscheme := {}
    have hdD : topologicalKrullDim D.subscheme ≤ d :=
      regular_sectionZero_dimension_le A s d (by
        simpa only [Nat.cast_add, Nat.cast_one] using hdim)
    have hdE : topologicalKrullDim E.subscheme ≤ d :=
      regular_sectionZero_dimension_le B t d (by
        simpa only [Nat.cast_add, Nat.cast_one] using hdim)
    have hiD : (jD ≫ i) ≫ polynomialProjectiveProjection ℂ (Fin (r+1)) = jD ≫ p := by
      rw [Category.assoc, hi]
    have hiE : (jE ≫ i) ≫ polynomialProjectiveProjection ℂ (Fin (r+1)) = jE ≫ p := by
      rw [Category.assoc, hi]
    let f (n : ℕ) := eulerCharacteristic p r ((L.pow n).tensor M).sheaf
    let g (n : ℕ) := eulerCharacteristic (jD ≫ p) r
      (((L.pullback jD).pow n).tensor ((A.pullback jD).tensor (M.pullback jD))).sheaf
    let h (n : ℕ) := eulerCharacteristic (jE ≫ p) r
      (((L.pullback jE).pow n).tensor ((B.pullback jE).tensor (M.pullback jE))).sheaf
    have hg : (fwdDiff (1 : ℕ))^[d+1] g = 0 :=
      ih (jD ≫ p) r (jD ≫ i) hiD (H.pullback jD)
        (LineBundle.IsAmple.pullback_closedImmersion H hH jD)
        (L.pullback jD) ((A.pullback jD).tensor (M.pullback jD)) hdD
    have hh : (fwdDiff (1 : ℕ))^[d+1] h = 0 :=
      ih (jE ≫ p) r (jE ≫ i) hiE (H.pullback jE)
        (LineBundle.IsAmple.pullback_closedImmersion H hH jE)
        (L.pullback jE) ((B.pullback jE).tensor (M.pullback jE)) hdE
    have hd : fwdDiff (1 : ℕ) f = g - fun n => h (n+1) := by
      funext n
      have hv := CartierEulerPair.euler_difference p L B M s t n r
        (fun q _ => projective_line_cohomology_finite p r i hi ((L.pow n).tensor M) q)
        (fun q _ => projective_line_cohomology_finite p r i hi ((L.pow (n+1)).tensor M) q)
        (fun q _ => projective_line_cohomology_finite p r i hi
          (A.tensor ((L.pow n).tensor M)) q)
        (fun q _ => projective_line_cohomology_finite (jD ≫ p) r (jD ≫ i) hiD
          ((A.tensor ((L.pow n).tensor M)).pullback jD) q)
        (fun q _ => projective_line_cohomology_finite (jE ≫ p) r (jE ≫ i) hiE
          ((B.tensor ((L.pow (n+1)).tensor M)).pullback jE) q)
        (lineBundle_cohomology_eq_zero_of_projective_embedding r i
          ((L.pow n).tensor M) (r+1) le_rfl)
        (lineBundle_cohomology_eq_zero_of_projective_embedding r i
          ((L.pow (n+1)).tensor M) (r+1) le_rfl)
      dsimp only [CartierEulerPair.source, CartierEulerPair.middle] at hv
      rw [eulerCharacteristic_pullback_cartierMiddle,
        eulerCharacteristic_pullback_cartierMiddle] at hv
      exact hv
    exact difference_step f g h (d+1) hd hg hh

theorem euler_tensor_power_difference_eq_zero {X : Scheme.{0}} [IsNoetherian X]
    (p : X ⟶ Spec (CommRingCat.of ℂ)) (r : ℕ)
    (i : X ⟶ projectiveSpace ℂ (Fin (r+1))) [IsClosedImmersion i]
    (hi : i ≫ polynomialProjectiveProjection ℂ (Fin (r+1)) = p)
    (L M : LineBundle X) (d : ℕ) (hdim : topologicalKrullDim X ≤ d) :
    (fwdDiff (1 : ℕ))^[d+1]
      (fun n => eulerCharacteristic p r ((L.pow n).tensor M).sheaf) = 0 := by
  let H := (PiExponent.ProjectiveO1.lineBundle (R := ℂ) (σ := Fin (r+1))).pullback i
  have hH : H.IsAmple := LineBundle.IsAmple.pullback_closedImmersion _
    PiExponent.ProjectiveO1.lineBundle_ample i
  exact euler_tensor_power_difference_aux d p r i hi H hH L M hdim

theorem euler_tensor_power_dimension_difference_eq_zero
    {X : Scheme.{0}} [IsNoetherian X]
    (p : X ⟶ Spec (CommRingCat.of ℂ)) (r : ℕ)
    (i : X ⟶ projectiveSpace ℂ (Fin (r+1))) [IsClosedImmersion i]
    (hi : i ≫ polynomialProjectiveProjection ℂ (Fin (r+1)) = p)
    (L M : LineBundle X) (d : ℕ) (hdim : topologicalKrullDim X ≤ d) :
    (fwdDiff (1 : ℕ))^[d+1]
      (fun n => eulerCharacteristic p d ((L.pow n).tensor M).sheaf) = 0 := by
  let H := (PiExponent.ProjectiveO1.lineBundle (R := ℂ) (σ := Fin (r+1))).pullback i
  have hH : H.IsAmple := LineBundle.IsAmple.pullback_closedImmersion _
    PiExponent.ProjectiveO1.lineBundle_ample i
  have he : (fun n => eulerCharacteristic p r ((L.pow n).tensor M).sheaf) =
      (fun n => eulerCharacteristic p d ((L.pow n).tensor M).sheaf) := by
    funext n
    exact eulerCharacteristic_projective_eq_dimension p r i hi H hH
      ((L.pow n).tensor M) d hdim
  have h := euler_tensor_power_difference_eq_zero p r i hi L M d hdim
  rwa [he] at h

theorem euler_power_dimension_difference_eq_zero
    {X : Scheme.{0}} [IsNoetherian X]
    (p : X ⟶ Spec (CommRingCat.of ℂ)) (r : ℕ)
    (i : X ⟶ projectiveSpace ℂ (Fin (r+1))) [IsClosedImmersion i]
    (hi : i ≫ polynomialProjectiveProjection ℂ (Fin (r+1)) = p)
    (L : LineBundle X) (d : ℕ) (hdim : topologicalKrullDim X ≤ d) :
    (fwdDiff (1 : ℕ))^[d+1]
      (fun n => eulerCharacteristic p d (L.pow n).sheaf) = 0 := by
  have h := euler_tensor_power_dimension_difference_eq_zero p r i hi L (L.pow 0) d hdim
  have he : (fun n => eulerCharacteristic p d ((L.pow n).tensor (L.pow 0)).sheaf) =
      (fun n => eulerCharacteristic p d (L.pow n).sheaf) := by
    funext n
    exact eulerCharacteristic_iso p (moduleTensorRightUnit (L.pow n).sheaf) d
  rwa [he] at h

end
end PiExponent.NumericalAmpleness

end OAI
end Source0699

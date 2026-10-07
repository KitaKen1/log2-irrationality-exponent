/- Generated rc4 checkpoint for LogTwo.
Modified from the reduced edition: new imports, separate module compilation,
and synchronous elaboration. Original source blocks and notices are retained.
See ../../../THIRD_PARTY_NOTICES.txt and ../../reduction.json.
-/
module
public import LogTwoCheckpoints.Part000
public import LogTwoCheckpoints.Part001
public import LogTwoCheckpoints.Part002
public import LogTwoCheckpoints.Part005
public import LogTwoCheckpoints.Part012
public import Mathlib.Algebra.Category.Grp.Zero
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Quasicoherent
public import Mathlib.AlgebraicGeometry.IdealSheaf.Functorial
public import Mathlib.AlgebraicGeometry.Modules.Sheaf
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.AlgebraicGeometry.Normalization
public import Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Functor
public import Mathlib.Analysis.Complex.Polynomial.Basic
public import Mathlib.Data.Opposite
public import Mathlib.Data.SetLike.Basic
public import Mathlib.RingTheory.MvPolynomial.Ideal
public import Mathlib.Topology.Sheaves.LocallySurjective
@[expose] public section
set_option Elab.async false

-- Source: OAI/NumberTheory/PiExponent/Approximation/OpenBaseChange.lean
section Source0325
/-
Modification notice for the LogTwo project.
Derived from openai/math (Apache-2.0), revision adc7f1241b42e322a6451854ab7e4b4c146bf78a.
Original source: lean/OAI/NumberTheory/PiExponent/Approximation/OpenBaseChange.lean
Changes: Convert module/import declarations to the Lean 4.34 public module format.
See ../THIRD_PARTY_NOTICES.txt for provenance and the recorded changes.
-/

namespace OAI

namespace PiExponentSeshadri.OpenBaseChange
noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite
variable {X Y : Scheme.{0}} (f : X ⟶ Y) (U : Y.Opens)

lemma restrict_unit_app {Z T : Scheme.{0}} (i : Z ⟶ T) [IsOpenImmersion i]
    (M : T.Modules) (W : T.Opens) :
    ((Scheme.Modules.restrictAdjunction i).unit.app M).app W =
      M.presheaf.map (homOfLE (i.image_preimage_le W)).op := rfl

lemma restrict_unit_app_iso {Z T : Scheme.{0}} (i : Z ⟶ T) [IsOpenImmersion i]
    (M : T.Modules) (W : T.Opens) (hW : W ≤ i.opensRange) :
    IsIso (((Scheme.Modules.restrictAdjunction i).unit.app M).app W) := by
  rw [restrict_unit_app]
  have he : i ''ᵁ i ⁻¹ᵁ W = W := by
    rw [i.image_preimage_eq_opensRange_inf, inf_eq_right.mpr hW]
  have hi : IsIso (homOfLE (i.image_preimage_le W)) :=
    homOfLE_isIso_of_eq _ he
  let e := @asIso _ _ _ _ (homOfLE (i.image_preimage_le W)) hi
  exact (M.presheaf.mapIso e.op).isIso_hom

def rightSquare :
    Scheme.Modules.pushforward (f ⁻¹ᵁ U).ι ⋙ Scheme.Modules.pushforward f ≅
      Scheme.Modules.pushforward (f ∣_ U) ⋙ Scheme.Modules.pushforward U.ι :=
  Scheme.Modules.pushforwardComp _ _ ≪≫
    Scheme.Modules.pushforwardCongr (morphismRestrict_ι f U).symm ≪≫
      (Scheme.Modules.pushforwardComp _ _).symm

def hom (M : X.Modules) :
    ((Scheme.Modules.pushforward f).obj M).restrict U.ι ⟶
      (Scheme.Modules.pushforward (f ∣_ U)).obj (M.restrict (f ⁻¹ᵁ U).ι) :=
  (Scheme.Modules.restrictFunctor U.ι).map
    ((Scheme.Modules.pushforward f).map
      ((Scheme.Modules.restrictAdjunction (f ⁻¹ᵁ U).ι).unit.app M)) ≫
  (Scheme.Modules.restrictFunctor U.ι).map
    ((rightSquare f U).hom.app (M.restrict (f ⁻¹ᵁ U).ι)) ≫
  (Scheme.Modules.restrictAdjunction U.ι).counit.app
    ((Scheme.Modules.pushforward (f ∣_ U)).obj (M.restrict (f ⁻¹ᵁ U).ι))

instance hom_isIso (M : X.Modules) : IsIso (hom f U M) := by
  have ha : IsIso ((Scheme.Modules.restrictFunctor U.ι).map
    ((Scheme.Modules.pushforward f).map
      ((Scheme.Modules.restrictAdjunction (f ⁻¹ᵁ U).ι).unit.app M))) := by
    apply Scheme.Modules.Hom.isIso_iff_isIso_app.mpr
    intro W
    change IsIso (((Scheme.Modules.restrictAdjunction (f ⁻¹ᵁ U).ι).unit.app M).app
      (f ⁻¹ᵁ (U.ι ''ᵁ W)))
    apply restrict_unit_app_iso
    rw [Scheme.Opens.opensRange_ι]
    apply (Opens.map f.base).monotone
    simpa only [Scheme.Opens.opensRange_ι] using U.ι.image_le_opensRange W
  unfold hom
  infer_instance

def iso (M : X.Modules) :
    ((Scheme.Modules.pushforward f).obj M).restrict U.ι ≅
      (Scheme.Modules.pushforward (f ∣_ U)).obj (M.restrict (f ⁻¹ᵁ U).ι) := asIso (hom f U M)

end
end PiExponentSeshadri.OpenBaseChange

end OAI
end Source0325

-- Source: OAI/NumberTheory/PiExponent/Approximation/ClosedPushforwardCoherent.lean
section Source0326
/-
Modification notice for the LogTwo project.
Derived from openai/math (Apache-2.0), revision adc7f1241b42e322a6451854ab7e4b4c146bf78a.
Original source: lean/OAI/NumberTheory/PiExponent/Approximation/ClosedPushforwardCoherent.lean
Changes: Convert module/import declarations to the Lean 4.34 public module format.
See ../THIRD_PARTY_NOTICES.txt for provenance and the recorded changes.
-/

namespace OAI

noncomputable section

namespace PiExponentSeshadri.ClosedPushforward

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite
variable {X Y : Scheme.{0}}

lemma sections_empty (M : X.Modules) (U : X.Opens) (hU : U = ⊥) :
    Subsingleton (M.val.obj (op U)) := by
  exact AddCommGrpCat.subsingleton_of_isZero
    (TopCat.Sheaf.isTerminalOfEqEmpty ((SheafOfModules.toSheaf.{0} X.ringCatSheaf).obj M) hU).isZero

lemma map_epi (f : X ⟶ Y) [IsClosedImmersion f] {M N : X.Modules}
    (φ : M ⟶ N) [Epi φ] : Epi ((Scheme.Modules.pushforward f).map φ) := by
  let FX := SheafOfModules.toSheaf.{0} X.ringCatSheaf
  let FY := SheafOfModules.toSheaf.{0} Y.ringCatSheaf
  let S := ShortComplex.mk _ _ (kernel.condition φ)
  have hS : S.ShortExact := { exact := ShortComplex.exact_kernel φ }
  have hepi : Epi (FX.map φ) := (ModuleSheafExact.shortExact_map X.ringCatSheaf hS).epi_g
  have hφ : TopCat.Presheaf.IsLocallySurjective (FX.map φ).hom :=
    (TopCat.Sheaf.isLocallySurjective_iff_epi _).mpr hepi
  have hloc : TopCat.Presheaf.IsLocallySurjective
      (FY.map ((Scheme.Modules.pushforward f).map φ)).hom := by
    apply (TopCat.Presheaf.isLocallySurjective_iff _).mpr
    intro U t y hy
    by_cases him : y ∈ Set.range f
    · obtain ⟨x, rfl⟩ := him
      obtain ⟨W,hWU,⟨s,hs⟩,hxW⟩ :=
        (TopCat.Presheaf.isLocallySurjective_iff _).mp hφ (f ⁻¹ᵁ U) t x hy
      obtain ⟨V',hV',hpre⟩ := f.isClosedEmbedding.isEmbedding.isInducing.isOpen_iff.mp W.isOpen
      let V : Y.Opens := ⟨V', hV'⟩ ⊓ U
      have hV : f ⁻¹ᵁ V = W := by
        ext z
        change (f z ∈ V' ∧ f z ∈ U) ↔ z ∈ W
        have hh : f z ∈ V' ↔ z ∈ W := Set.ext_iff.mp hpre z
        exact ⟨fun h => hh.mp h.1, fun h => ⟨hh.mpr h,hWU h⟩⟩
      refine ⟨V,inf_le_right,?_,?_,⟩
      · change ∃ s, (φ.val.app (op (f ⁻¹ᵁ V))) s =
          N.val.map ((Opens.map f.base).map (homOfLE inf_le_right)).op t
        subst W
        exact ⟨s,hs⟩
      · exact ⟨(Set.ext_iff.mp hpre x).mpr hxW,hy⟩
    · let V : Y.Opens := U ⊓ ⟨(Set.range f)ᶜ, f.isClosedEmbedding.isClosed_range.isOpen_compl⟩
      have hV : f ⁻¹ᵁ V = ⊥ := by
        ext x
        change (f x ∈ U ∧ f x ∉ Set.range f) ↔ False
        simp
      have := sections_empty N (f ⁻¹ᵁ V) hV
      refine ⟨V,inf_le_left,⟨0,?_⟩,⟨hy,him⟩⟩
      exact @Subsingleton.elim (N.val.obj (op (f ⁻¹ᵁ V))) (sections_empty N _ hV) _ _
  let : Epi (FY.map ((Scheme.Modules.pushforward f).map φ)) :=
    (TopCat.Sheaf.isLocallySurjective_iff_epi _).mp hloc
  exact FY.epi_of_epi_map inferInstance

instance preservesEpis (f : X ⟶ Y) [IsClosedImmersion f] :
    (Scheme.Modules.pushforward f).PreservesEpimorphisms where
  preserves {_ _} φ _ := map_epi f φ

instance preservesHomology (f : X ⟶ Y) [IsClosedImmersion f] :
    (Scheme.Modules.pushforward f).PreservesHomology :=
  Functor.preservesHomology_of_preservesEpis_and_kernels _

instance preservesFiniteColimits (f : X ⟶ Y) [IsClosedImmersion f] :
    PreservesFiniteColimits (Scheme.Modules.pushforward f) :=
  Functor.preservesFiniteColimits_of_preservesHomology _

open PiExponent.CoherentAffineFinite PiExponent.FiniteGlobalPresentation
open PiExponent.ClosedPushforwardAffine

private theorem presentation_transport {Z : Scheme.{0}}
    {M N : SheafOfModules Z.ringCatSheaf} (e : M ≅ N)
    (P : M.Presentation) (hP : P.IsFinite) : ∃ Q : N.Presentation, Q.IsFinite := by
  let : IsIso e.hom := e.isIso_hom
  exact ⟨P.ofIsIso e.hom,
    ⟨⟨hP.isFiniteType_generators.finite⟩, ⟨hP.isFiniteType_relations.finite⟩⟩⟩

instance pushforward_isFinitePresentation (f : X ⟶ Y) [IsClosedImmersion f]
    [IsLocallyNoetherian Y] (M : X.Modules) [M.IsFinitePresentation] :
    ((Scheme.Modules.pushforward f).obj M).IsFinitePresentation := by
  apply isFinitePresentation_of_affine_presentations
  intro U
  have : IsAffine U.1.toScheme := U.2
  have : IsAffine (f ⁻¹ᵁ U.1).toScheme := U.2.preimage f
  let : M.IsQuasicoherent :=
    (SheafOfModules.IsFinitePresentation.exists_quasicoherentData M).choose.isQuasicoherent
  have hM := (locallyFinitelyGenerated_of_finitePresentation M).restrict (f ⁻¹ᵁ U.1).ι
  obtain ⟨P,hP⟩ := affine_pushforward_exists_finitePresentation (f ∣_ U.1)
    (M.restrict (f ⁻¹ᵁ U.1).ι) hM
  exact presentation_transport (Z := U.1.toScheme) (OpenBaseChange.iso f U.1 M).symm P hP

end PiExponentSeshadri.ClosedPushforward

end

end OAI
end Source0326

-- Source: OAI/NumberTheory/PiExponent/Geometry/LineBundleCoherent.lean
section Source0327
/-
Modification notice for the LogTwo project.
Derived from openai/math (Apache-2.0), revision adc7f1241b42e322a6451854ab7e4b4c146bf78a.
Original source: lean/OAI/NumberTheory/PiExponent/Geometry/LineBundleCoherent.lean
Changes: Convert module/import declarations to the Lean 4.34 public module format.
See ../THIRD_PARTY_NOTICES.txt for provenance and the recorded changes.
-/

namespace OAI

namespace PiExponent.GeometrySupport.LineBundleCoherent

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open PiExponentSeshadri.Geometry

variable {X : Scheme}

theorem structureSheaf_isFinitePresentation : (structureSheaf X).IsFinitePresentation := by
  let e : SheafOfModules.free (R := X.ringCatSheaf) PUnit ≅ structureSheaf X :=
    coproductUniqueIso (fun _ : PUnit => structureSheaf X)
  exact (SheafOfModules.isFinitePresentation X.ringCatSheaf).prop_of_iso e
    (PiExponent.FiniteGlobalPresentation.free_isFinitePresentation X PUnit)

theorem lineBundle_isFinitePresentation (L : LineBundle X) : L.sheaf.IsFinitePresentation := by
  let : (structureSheaf X).IsFinitePresentation := structureSheaf_isFinitePresentation
  apply PiExponent.FiniteGlobalPresentation.isFinitePresentation_of_locally_iso
    (structureSheaf X) L.sheaf
  intro x
  obtain ⟨U, hx, ⟨e⟩⟩ := L.locallyRankOne x
  exact ⟨U, hx, ⟨e ≪≫ (Scheme.Modules.restrictUnitIso U.ι).symm⟩⟩

theorem modulePow_isFinitePresentation (L : LineBundle X) (n : ℕ) :
    (modulePow X L.sheaf n).IsFinitePresentation :=
  lineBundle_isFinitePresentation (L.pow n)

theorem modulePow_isQuasicoherent (L : LineBundle X) (n : ℕ) :
    (modulePow X L.sheaf n).IsQuasicoherent := by
  have := modulePow_isFinitePresentation L n
  exact (SheafOfModules.IsFinitePresentation.exists_quasicoherentData
    (modulePow X L.sheaf n)).choose.isQuasicoherent

end
end PiExponent.GeometrySupport.LineBundleCoherent

end OAI
end Source0327

-- Source: OAI/NumberTheory/PiExponent/Jets/CompactJetIdeal.lean
section Source0328
/-
Modification notice for the LogTwo project.
Derived from openai/math (Apache-2.0), revision adc7f1241b42e322a6451854ab7e4b4c146bf78a.
Original source: lean/OAI/NumberTheory/PiExponent/Jets/CompactJetIdeal.lean
Changes: Convert module/import declarations to the Lean 4.34 public module format.
See ../THIRD_PARTY_NOTICES.txt for provenance and the recorded changes.
-/

namespace OAI

noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace
namespace PiExponent.CompactJetIdeal

universe u
variable {U X S : Scheme.{u}}

def extend (I : U.IdealSheafData) (j : U ⟶ X) : X.IdealSheafData := I.map j

theorem restrict_extend (I : U.IdealSheafData) (j : U ⟶ X)
    [IsOpenImmersion j] [QuasiCompact j] : (extend I j).comap j = I := by
  apply Scheme.IdealSheafData.ext
  funext W
  rw [Scheme.IdealSheafData.ideal_comap_of_isOpenImmersion]
  have hsq : IsPullback I.subschemeι (𝟙 I.subscheme) j (I.subschemeι ≫ j) :=
    IsPullback.of_vert_isIso_mono ⟨by simp⟩
  have h := Scheme.ker_ideal_of_isPullback_of_isOpenImmersion
    (I.subschemeι ≫ j) I.subschemeι (𝟙 I.subscheme) j hsq W
  simpa only [Scheme.IdealSheafData.ker_subschemeι, extend, Scheme.IdealSheafData.map] using h.symm

theorem section_isClosedImmersion (π : X ⟶ S) [IsSeparated π]
    (p : S ⟶ X) (hp : p ≫ π = 𝟙 S) : IsClosedImmersion p := by
  have : IsClosedImmersion (p ≫ π) := by rw [hp]; infer_instance
  exact IsClosedImmersion.of_comp p π

theorem image_support_isClosed {J : Type*} [Finite J]
    (I : U.IdealSheafData) (j : U ⟶ X)
    (π : X ⟶ S) [IsSeparated π]
    (p : J → (S ⟶ U)) (hp : ∀ a, (p a ≫ j) ≫ π = 𝟙 S)
    (hsupport : (I.support : Set U) = ⋃ a, Set.range (p a)) :
    IsClosed (j '' (I.support : Set U)) := by
  have heq : j '' (I.support : Set U) = ⋃ a, Set.range (p a ≫ j) := by
    rw [hsupport, Set.image_iUnion]
    congr 1
    funext a
    rw [Scheme.Hom.comp_base, TopCat.coe_comp, Set.range_comp]
  rw [heq]
  apply isClosed_iUnion_of_finite
  intro a
  have := section_isClosedImmersion π (p a ≫ j) (hp a)
  exact (p a ≫ j).isClosedEmbedding.isClosed_range

theorem support_extend {J : Type*} [Finite J]
    (I : U.IdealSheafData) (j : U ⟶ X) [QuasiCompact j]
    (π : X ⟶ S) [IsSeparated π]
    (p : J → (S ⟶ U)) (hp : ∀ a, (p a ≫ j) ≫ π = 𝟙 S)
    (hsupport : (I.support : Set U) = ⋃ a, Set.range (p a)) :
    ((extend I j).support : Set X) = j '' (I.support : Set U) := by
  change ((I.map j).support : Set X) = _
  rw [Scheme.IdealSheafData.support_map]
  exact (image_support_isClosed I j π p hp hsupport).closure_eq

theorem restrict_eq_top_of_disjoint (I : X.IdealSheafData)
    {V : Scheme.{u}} (f : V ⟶ X)
    (havoid : ∀ v, f v ∉ I.support) : I.comap f = ⊤ := by
  apply (Scheme.IdealSheafData.support_eq_bot_iff (I.comap f)).mp
  rw [Scheme.IdealSheafData.support_comap]
  ext v
  exact ⟨fun h => (havoid v h).elim, False.elim⟩

abbrev affineBlowup {R : Type u} [CommRing R] (I : Ideal R) : Scheme.{u} :=
  PiExponentSeshadri.ReesGrading.affineBlowup I

end PiExponent.CompactJetIdeal
end

end OAI
end Source0328

-- Source: OAI/NumberTheory/PiExponent/Jets/CompactJetIdealCoherent.lean
section Source0329
-- Modified in this edition: unused plain lemmas removed; see reduction.json.
/-
Modification notice for the LogTwo project.
Derived from openai/math (Apache-2.0), revision adc7f1241b42e322a6451854ab7e4b4c146bf78a.
Original source: lean/OAI/NumberTheory/PiExponent/Jets/CompactJetIdealCoherent.lean
Changes: Convert module/import declarations to the Lean 4.34 public module format.
See ../THIRD_PARTY_NOTICES.txt for provenance and the recorded changes.
-/

namespace OAI

noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
namespace PiExponent.CompactJetIdeal

theorem closedModule_isFinitePresentation {X : Scheme} [IsLocallyNoetherian X]
    (I : X.IdealSheafData) :
    (PiExponentSeshadri.IdealModule.closedModule I).IsFinitePresentation := by
  let : (PiExponentSeshadri.IdealModule.unit X).IsFinitePresentation :=
    GeometrySupport.LineBundleCoherent.structureSheaf_isFinitePresentation
  let : (PiExponentSeshadri.IdealModule.unit I.subscheme).IsFinitePresentation :=
    GeometrySupport.LineBundleCoherent.structureSheaf_isFinitePresentation
  let : ((Scheme.Modules.pushforward I.subschemeι).obj
      (PiExponentSeshadri.IdealModule.unit I.subscheme)).IsQuasicoherent :=
    (SheafOfModules.IsFinitePresentation.exists_quasicoherentData
      ((Scheme.Modules.pushforward I.subschemeι).obj
        (PiExponentSeshadri.IdealModule.unit I.subscheme))).choose.isQuasicoherent
  exact FiniteGlobalPresentation.kernel_isFinitePresentation
    (PiExponentSeshadri.IdealModule.structureMap I.subschemeι)

end PiExponent.CompactJetIdeal
end

end OAI
end Source0329

-- Source: OAI/NumberTheory/PiExponent/Jets/CompactLogJetIdeal.lean
section Source0330
-- Modified in this edition: unused plain lemmas removed; see reduction.json.
/-
Modification notice for the LogTwo project.
Derived from openai/math (Apache-2.0), revision adc7f1241b42e322a6451854ab7e4b4c146bf78a.
Original source: lean/OAI/NumberTheory/PiExponent/Jets/CompactLogJetIdeal.lean
Changes: Convert module/import declarations to the Lean 4.34 public module format.
See ../THIRD_PARTY_NOTICES.txt for provenance and the recorded changes.
-/

namespace OAI

noncomputable section
open CategoryTheory AlgebraicGeometry
open scoped BigOperators
namespace PiExponent.CompactLogJetIdeal
open CompactJetPolynomial

variable {m : ℕ}

abbrev coordinateRing (m : ℕ) := MvPolynomial (Fin (m+1)) ℂ
abbrev affineSpace (m : ℕ) : Scheme := Spec (CommRingCat.of (coordinateRing m))
abbrev base : Scheme := Spec (CommRingCat.of ℂ)

def structureMap (m : ℕ) : affineSpace m ⟶ base :=
  Spec.map (CommRingCat.ofHom (algebraMap ℂ (coordinateRing m)))

def point (c : Fin m → ℂ) : base ⟶ affineSpace m :=
  Spec.map (CommRingCat.ofHom (MvPolynomial.aeval (center c)).toRingHom)

theorem point_section (c : Fin m → ℂ) : point c ≫ structureMap m = 𝟙 base := by
  change Spec.map _ ≫ Spec.map _ = _
  rw [← Spec.map_comp]
  have h : CommRingCat.ofHom (algebraMap ℂ (coordinateRing m)) ≫
      CommRingCat.ofHom (MvPolynomial.aeval (center c)).toRingHom =
      𝟙 (CommRingCat.of ℂ) := by
    ext a
    simp
  rw [h, Spec.map_id]

theorem range_point (c : Fin m → ℂ) : Set.range (point c) = {centerPoint c} := by
  change Set.range (PrimeSpectrum.comap (MvPolynomial.aeval (center c)).toRingHom) = _
  rw [range_comap_of_surjective _ _ (by
    intro a
    exact ⟨MvPolynomial.C a, by simp⟩)]
  exact PrimeSpectrum.zeroLocus_eq_singleton (WeightedBezout.pointIdeal (center c))

theorem support_specIdeal {R : Type} [CommRing R] (I : Ideal R) :
    ((PiExponentSeshadri.IdealPullback.specIdeal I).support : Set (Spec (CommRingCat.of R))) =
      PrimeSpectrum.zeroLocus (I : Set R) := by
  rw [PiExponentSeshadri.IdealPullback.specIdeal,
    Scheme.IdealSheafData.coe_support_ofIdealTop, Spec_zeroLocus, ← Ideal.coe_comap]
  rw [Ideal.comap_map_of_bijective _
    (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (CommRingCat.of R)).inv)]

def polynomialIdeal {J : Type*} [Fintype J] (c : J → Fin m → ℂ)
    (T : Fin m → ℕ) (e : Fin (m+1) → ℕ) : Ideal (coordinateRing m) :=
  ∏ a, powerIdeal (c a) (logPolynomials T) e

def affineIdeal {J : Type*} [Fintype J] (c : J → Fin m → ℂ)
    (T : Fin m → ℕ) (e : Fin (m+1) → ℕ) : (affineSpace m).IdealSheafData :=
  PiExponentSeshadri.IdealPullback.specIdeal (polynomialIdeal c T e)

theorem support_affineIdeal {J : Type*} [Fintype J] (c : J → Fin m → ℂ)
    (T : Fin m → ℕ) (e : Fin (m+1) → ℕ) (he : ∀ i, 0 < e i) :
    ((affineIdeal c T e).support : Set (affineSpace m)) =
      ⋃ a, Set.range (point (c a)) := by
  rw [affineIdeal, support_specIdeal]
  unfold polynomialIdeal
  rw [zeroLocus_prod_powerIdeal c (logPolynomials T) (logPolynomials_eval_zero T) e he]
  simp only [range_point]
  ext p
  constructor
  · rintro ⟨a, rfl⟩
    exact Set.mem_iUnion.mpr ⟨a, Set.mem_singleton _⟩
  · intro hp
    obtain ⟨a, ha⟩ := Set.mem_iUnion.mp hp
    exact ⟨a, (Set.mem_singleton_iff.mp ha).symm⟩

def compactIdeal {J : Type*} [Fintype J] (c : J → Fin m → ℂ)
    (T : Fin m → ℕ) (e : Fin (m+1) → ℕ)
    {X : Scheme} (j : affineSpace m ⟶ X) : X.IdealSheafData :=
  CompactJetIdeal.extend (affineIdeal c T e) j

theorem restrict_compactIdeal {J : Type*} [Fintype J] (c : J → Fin m → ℂ)
    (T : Fin m → ℕ) (e : Fin (m+1) → ℕ)
    {X : Scheme} (j : affineSpace m ⟶ X) [IsOpenImmersion j] [QuasiCompact j] :
    (compactIdeal c T e j).comap j = affineIdeal c T e :=
  CompactJetIdeal.restrict_extend _ j

theorem support_compactIdeal {J : Type*} [Fintype J] (c : J → Fin m → ℂ)
    (T : Fin m → ℕ) (e : Fin (m+1) → ℕ) (he : ∀ i, 0 < e i)
    {X : Scheme} (j : affineSpace m ⟶ X) [QuasiCompact j]
    (π : X ⟶ base) [IsSeparated π] (hπ : j ≫ π = structureMap m) :
    ((compactIdeal c T e j).support : Set X) =
      ⋃ a, Set.range (point (c a) ≫ j) := by
  rw [compactIdeal, CompactJetIdeal.support_extend (affineIdeal c T e) j π
    (fun a => point (c a)) (fun a => by
      rw [Category.assoc, hπ, point_section]) (support_affineIdeal c T e he),
    support_affineIdeal c T e he, Set.image_iUnion]
  congr 1
  funext a
  rw [Scheme.Hom.comp_base, TopCat.coe_comp, Set.range_comp]

end PiExponent.CompactLogJetIdeal
end

end OAI
end Source0330

-- Source: LogTwo/Geometry/CompactJetIdealAt.lean
section Source0331
-- Modified in this edition: unused plain lemmas removed; see reduction.json.
/-
Modification notice for the LogTwo project.
Adapted from openai/math (Apache-2.0), revision adc7f1241b42e322a6451854ab7e4b4c146bf78a.
Changes: Adapt compact jet ideals to arbitrary Y-centers and add an affine pullback identity.
See ../THIRD_PARTY_NOTICES.txt for provenance and the recorded changes.
-/

/-! Adapted from openai/math at adc7f1241b42e322a6451854ab7e4b4c146bf78a,
Jets/CompactLogJetIdeal.lean (Apache-2.0), to arbitrary Y-centers.
The finite-support ideal extends to an ambient scheme, restricts back to the
given affine chart, and has no support away from the actual centers.
Ampleness, curve-degree transport, and bounded-degree interpolation are separate.
See THIRD_PARTY_NOTICES.txt. -/
namespace LogTwo.Geometry.CompactJetIdealAt
open OAI PiExponent CategoryTheory AlgebraicGeometry
open CompactLogJetIdeal (affineSpace base structureMap support_specIdeal)
noncomputable section

variable {m : ℕ}

def point (y : ℂ) (c : Fin m → ℂ) : base ⟶ affineSpace m :=
  Spec.map (CommRingCat.ofHom (MvPolynomial.aeval (centerPoint y c)).toRingHom)

theorem point_section (y : ℂ) (c : Fin m → ℂ) :
    point y c ≫ structureMap m = 𝟙 base := by
  change Spec.map _ ≫ Spec.map _ = _
  rw [← Spec.map_comp]
  have h : CommRingCat.ofHom (algebraMap ℂ (CompactLogJetIdeal.coordinateRing m)) ≫
      CommRingCat.ofHom (MvPolynomial.aeval (centerPoint y c)).toRingHom =
      𝟙 (CommRingCat.of ℂ) := by
    ext a
    simp
  rw [h, Spec.map_id]

theorem range_point (y : ℂ) (c : Fin m → ℂ) :
    Set.range (point y c) = {centerPrime y c} := by
  change Set.range (PrimeSpectrum.comap (MvPolynomial.aeval (centerPoint y c)).toRingHom) = _
  rw [range_comap_of_surjective _ _ (by
    intro a
    exact ⟨MvPolynomial.C a, by simp⟩)]
  exact PrimeSpectrum.zeroLocus_eq_singleton (WeightedBezout.pointIdeal (centerPoint y c))

def affineIdeal {J : Type*} [Fintype J]
    (y : J → ℂ) (c : J → Fin m → ℂ) (T : Fin m → ℕ) (e : Fin (m+1) → ℕ) :
    (affineSpace m).IdealSheafData :=
  PiExponentSeshadri.IdealPullback.specIdeal (jetProductIdeal y c T e)

theorem support_affineIdeal {J : Type*} [Fintype J]
    (y : J → ℂ) (c : J → Fin m → ℂ)
    (T : Fin m → ℕ) (e : Fin (m+1) → ℕ) (he : ∀ i, 0 < e i) :
    ((affineIdeal y c T e).support : Set (affineSpace m)) =
      ⋃ j, Set.range (point (y j) (c j)) := by
  rw [affineIdeal, support_specIdeal, zeroLocus_jetProductIdeal y c T e he]
  simp only [range_point]
  ext p
  constructor
  · rintro ⟨j, rfl⟩
    exact Set.mem_iUnion.mpr ⟨j, Set.mem_singleton _⟩
  · intro hp
    obtain ⟨j, hj⟩ := Set.mem_iUnion.mp hp
    exact ⟨j, (Set.mem_singleton_iff.mp hj).symm⟩

def compactIdeal {J : Type*} [Fintype J]
    (y : J → ℂ) (c : J → Fin m → ℂ) (T : Fin m → ℕ) (e : Fin (m+1) → ℕ)
    {X : Scheme} (j : affineSpace m ⟶ X) : X.IdealSheafData :=
  CompactJetIdeal.extend (affineIdeal y c T e) j

theorem restrict_compactIdeal {J : Type*} [Fintype J]
    (y : J → ℂ) (c : J → Fin m → ℂ) (T : Fin m → ℕ) (e : Fin (m+1) → ℕ)
    {X : Scheme} (j : affineSpace m ⟶ X) [IsOpenImmersion j] [QuasiCompact j] :
    (compactIdeal y c T e j).comap j = affineIdeal y c T e :=
  CompactJetIdeal.restrict_extend _ j

/-- Pullback along any affine ring map agrees with the algebraic image of the
product ideal. Instantiating the ring map with branch evaluation is now exact. -/
theorem comap_compactIdeal_spec {J : Type*} [Fintype J]
    (y : J → ℂ) (c : J → Fin m → ℂ) (T : Fin m → ℕ) (e : Fin (m+1) → ℕ)
    {X : Scheme} (j : affineSpace m ⟶ X) [IsOpenImmersion j] [QuasiCompact j]
    {A : Type} [CommRing A] (f : CompactLogJetIdeal.coordinateRing m →+* A) :
    (compactIdeal y c T e j).comap (Spec.map (CommRingCat.ofHom f) ≫ j) =
      PiExponentSeshadri.IdealPullback.specIdeal ((jetProductIdeal y c T e).map f) := by
  rw [Scheme.IdealSheafData.comap_comp, restrict_compactIdeal]
  exact PiExponentSeshadri.IdealPullback.specIdeal_comap _ f

theorem support_compactIdeal {J : Type*} [Fintype J]
    (y : J → ℂ) (c : J → Fin m → ℂ)
    (T : Fin m → ℕ) (e : Fin (m+1) → ℕ) (he : ∀ i, 0 < e i)
    {X : Scheme} (j : affineSpace m ⟶ X) [QuasiCompact j]
    (π : X ⟶ base) [IsSeparated π] (hπ : j ≫ π = structureMap m) :
    ((compactIdeal y c T e j).support : Set X) =
      ⋃ a, Set.range (point (y a) (c a) ≫ j) := by
  rw [compactIdeal, CompactJetIdeal.support_extend (affineIdeal y c T e) j π
    (fun a => point (y a) (c a)) (fun a => by
      rw [Category.assoc, hπ, point_section]) (support_affineIdeal y c T e he),
    support_affineIdeal y c T e he, Set.image_iUnion]
  congr 1
  funext a
  rw [Scheme.Hom.comp_base, TopCat.coe_comp, Set.range_comp]

end
end LogTwo.Geometry.CompactJetIdealAt
end Source0331

-- Source: LogTwo/Geometry/StrictJetTruncation.lean
section Source0332
-- Modified in this edition: unused plain lemmas removed; see reduction.json.
/-! The arithmetic matrix's actual truncation orders also satisfy the strict
weight inequality required by the local colength/contact theorem. -/
namespace LogTwo.Geometry
open LogTwo.Arithmetic LogTwo.Parameters LogTwo.Interpolation
noncomputable section

theorem truncation_weight_strict {m : ℕ} (w : Weights m) (F : ℚ)
    (hF : 1 / w.theta < F) (i : Fin m) :
    jetWeight w i.succ < (truncationOrders w F i : ℚ) * jetWeight w 0 := by
  change w.w i / w.theta < (truncationOrders w F i : ℚ) * w.v0
  calc
    _ = (1 / w.theta) * w.w i := by ring
    _ < F * w.w i := mul_lt_mul_of_pos_right hF (w.w_pos i)
    _ ≤ (truncationOrders w F i : ℚ) * w.v0 :=
      (div_le_iff₀ w.v0_pos).mp (Nat.le_ceil _)

end
end LogTwo.Geometry
end Source0332

-- Source: OAI/NumberTheory/PiExponent/Approximation/SectionOpens.lean
section Source0333
/-
Modification notice for the LogTwo project.
Derived from openai/math (Apache-2.0), revision adc7f1241b42e322a6451854ab7e4b4c146bf78a.
Original source: lean/OAI/NumberTheory/PiExponent/Approximation/SectionOpens.lean
Changes: Convert module/import declarations to the Lean 4.34 public module format.
See ../THIRD_PARTY_NOTICES.txt for provenance and the recorded changes.
-/

namespace OAI

noncomputable section

namespace PiExponentSeshadri

universe u

namespace SectionOpens

section
open AlgebraicGeometry CategoryTheory TopologicalSpace
open scoped AlgebraicGeometry
variable {X Y : Scheme.{u}} {M N : X.Modules}

lemma isIso_of_stalks (f : M ⟶ N)
    (h : ∀ x : X, IsIso ((TopCat.Presheaf.stalkFunctor Ab x).map f.mapPresheaf)) :
    IsIso f := by
  apply Scheme.Modules.Hom.isIso_iff_isIso_app.mpr
  intro U
  let A : TopCat.Sheaf Ab X := ⟨M.presheaf, M.isSheaf⟩
  let B : TopCat.Sheaf Ab X := ⟨N.presheaf, N.isSheaf⟩
  let φ : A ⟶ B := ⟨f.mapPresheaf⟩
  let (x : U) : IsIso ((TopCat.Presheaf.stalkFunctor Ab x.val).map φ.hom) := h x.val
  exact TopCat.Presheaf.app_isIso_of_stalkFunctor_map_iso φ U

lemma stalk_isIso_of_restrict (f : M ⟶ N) (φ : Y ⟶ X) [IsOpenImmersion φ]
    [IsIso ((Scheme.Modules.restrictFunctor φ).map f)] (y : Y) :
    IsIso ((TopCat.Presheaf.stalkFunctor Ab (φ y)).map f.mapPresheaf) := by
  apply (NatIso.isIso_map_iff (Scheme.Modules.restrictStalkNatIso φ y) f).mp
  change IsIso ((TopCat.Presheaf.stalkFunctor Ab y).map
    ((Scheme.Modules.toPresheaf Y).map ((Scheme.Modules.restrictFunctor φ).map f)))
  infer_instance

lemma restrict_isIso_of_stalks (f : M ⟶ N) (φ : Y ⟶ X) [IsOpenImmersion φ]
    (h : ∀ y : Y, IsIso ((TopCat.Presheaf.stalkFunctor Ab (φ y)).map f.mapPresheaf)) :
    IsIso ((Scheme.Modules.restrictFunctor φ).map f) := by
  apply isIso_of_stalks
  intro y
  exact (NatIso.isIso_map_iff (Scheme.Modules.restrictStalkNatIso φ y) f).mpr (h y)

lemma isIso_of_locally_isIso (f : M ⟶ N)
    (h : ∀ x : X, ∃ U : X.Opens, x ∈ U ∧
      IsIso ((Scheme.Modules.restrictFunctor U.ι).map f)) : IsIso f := by
  apply isIso_of_stalks
  intro x
  obtain ⟨U, hx, hU⟩ := h x
  let := hU
  exact stalk_isIso_of_restrict f U.ι ⟨x, hx⟩

def isoOpen (f : M ⟶ N) : X.Opens :=
  ⨆ (U : X.Opens) (_ : IsIso ((Scheme.Modules.restrictFunctor U.ι).map f)), U

lemma mem_isoOpen_iff (f : M ⟶ N) (x : X) :
    x ∈ isoOpen f ↔ ∃ U : X.Opens, x ∈ U ∧
      IsIso ((Scheme.Modules.restrictFunctor U.ι).map f) := by
  simp only [isoOpen, Opens.mem_iSup]
  aesop

theorem isIso_restrict_isoOpen (f : M ⟶ N) :
    IsIso ((Scheme.Modules.restrictFunctor (isoOpen f).ι).map f) := by
  apply restrict_isIso_of_stalks
  intro x
  obtain ⟨U, hx, hU⟩ := (mem_isoOpen_iff f x.val).mp x.property
  let := hU
  exact stalk_isIso_of_restrict f U.ι ⟨x.val, hx⟩

end

open AlgebraicGeometry CategoryTheory TopologicalSpace
open scoped AlgebraicGeometry
variable {X Y : Scheme.{u}} {M N P : X.Modules}

lemma isoOpen_postcomp (f : M ⟶ N) (e : N ≅ P) :
    isoOpen (f ≫ e.hom) = isoOpen f := by
  apply le_antisymm
  · intro x hx
    obtain ⟨U, hxU, hU⟩ := (mem_isoOpen_iff (f ≫ e.hom) x).mp hx
    refine (mem_isoOpen_iff f x).mpr ⟨U, hxU, ?_⟩
    rw [Functor.map_comp] at hU
    let := hU
    exact IsIso.of_isIso_comp_right
      ((Scheme.Modules.restrictFunctor U.ι).map f) ((Scheme.Modules.restrictFunctor U.ι).map e.hom)
  · intro x hx
    obtain ⟨U, hxU, hU⟩ := (mem_isoOpen_iff f x).mp hx
    refine (mem_isoOpen_iff (f ≫ e.hom) x).mpr ⟨U, hxU, ?_⟩
    rw [Functor.map_comp]
    let := hU
    infer_instance

lemma isoOpen_precomp (e : P ≅ M) (f : M ⟶ N) :
    isoOpen (e.hom ≫ f) = isoOpen f := by
  apply le_antisymm
  · intro x hx
    obtain ⟨U, hxU, hU⟩ := (mem_isoOpen_iff (e.hom ≫ f) x).mp hx
    refine (mem_isoOpen_iff f x).mpr ⟨U, hxU, ?_⟩
    rw [Functor.map_comp] at hU
    let := hU
    exact IsIso.of_isIso_comp_left
      ((Scheme.Modules.restrictFunctor U.ι).map e.hom) ((Scheme.Modules.restrictFunctor U.ι).map f)
  · intro x hx
    obtain ⟨U, hxU, hU⟩ := (mem_isoOpen_iff f x).mp hx
    refine (mem_isoOpen_iff (e.hom ≫ f) x).mpr ⟨U, hxU, ?_⟩
    rw [Functor.map_comp]
    let := hU
    infer_instance

lemma isoOpen_restrict (f : M ⟶ N) (φ : Y ⟶ X) [IsOpenImmersion φ] :
    isoOpen ((Scheme.Modules.restrictFunctor φ).map f) = φ ⁻¹ᵁ isoOpen f := by
  ext y
  constructor
  · intro hy
    obtain ⟨V, hyV, hV⟩ := (mem_isoOpen_iff _ y).mp hy
    let := hV
    apply (mem_isoOpen_iff f (φ y)).mpr
    refine ⟨φ ''ᵁ V, ⟨y, hyV, rfl⟩, ?_⟩
    apply restrict_isIso_of_stalks
    intro x
    obtain ⟨z, hz, he⟩ := x.property
    change φ z = x.val at he
    change IsIso ((TopCat.Presheaf.stalkFunctor Ab x.val).map f.mapPresheaf)
    rw [← he]
    apply (NatIso.isIso_map_iff (Scheme.Modules.restrictStalkNatIso φ z) f).mp
    exact stalk_isIso_of_restrict ((Scheme.Modules.restrictFunctor φ).map f) V.ι ⟨z, hz⟩
  · intro hy
    change φ y ∈ isoOpen f at hy
    let U := φ ⁻¹ᵁ isoOpen f
    apply (mem_isoOpen_iff _ y).mpr
    refine ⟨U, hy, ?_⟩
    apply restrict_isIso_of_stalks
    intro z
    apply (NatIso.isIso_map_iff (Scheme.Modules.restrictStalkNatIso φ z.val) f).mpr
    let := isIso_restrict_isoOpen f
    exact stalk_isIso_of_restrict f (isoOpen f).ι ⟨φ z.val, z.property⟩

end SectionOpens
namespace Frames
open AlgebraicGeometry CategoryTheory TopologicalSpace
open scoped AlgebraicGeometry
variable {X Y : Scheme.{u}}

lemma isUnit_iff_basicOpen_top (c : Γ(X, ⊤)) :
    IsUnit c ↔ X.basicOpen c = ⊤ := by
  refine ⟨X.basicOpen_of_isUnit, fun h => ?_⟩
  apply X.toRingedSpace.isUnit_of_isUnit_germ ⊤ c
  intro x hx
  apply (X.mem_basicOpen c x hx).mp
  rw [h]
  trivial

lemma coefficient_restrict_isUnit {M : X.Modules} (e : M ≅ O X)
    (s : O X ⟶ M) (φ : Y ⟶ X) [IsOpenImmersion φ] :
    IsUnit (φ.appTop (coefficient e s)) ↔
      IsIso ((Scheme.Modules.restrictFunctor φ).map s) := by
  rw [← coefficient_restrict, coefficient_isUnit_iff]
  let F : X.Modules ⥤ Y.Modules := Scheme.Modules.restrictFunctor φ
  let e : F.obj (O X) ≅ O Y := Scheme.Modules.restrictUnitIso φ
  exact isIso_comp_left_iff e.inv (F.map s)

theorem isoOpen_eq_basicOpen {M : X.Modules} (e : M ≅ O X) (s : O X ⟶ M) :
    SectionOpens.isoOpen s = X.basicOpen (coefficient e s) := by
  ext x
  constructor
  · intro hx
    obtain ⟨U, hxU, hU⟩ := (SectionOpens.mem_isoOpen_iff s x).mp hx
    have hc := (coefficient_restrict_isUnit e s U.ι).mpr hU
    have hb := U.toScheme.basicOpen_of_isUnit hc
    rw [← Scheme.preimage_basicOpen_top] at hb
    have H : (⟨x, hxU⟩ : U.toScheme) ∈ U.ι ⁻¹ᵁ X.basicOpen (coefficient e s) := by
      rw [hb]; trivial
    exact H
  · intro hx
    let U := X.basicOpen (coefficient e s)
    refine (SectionOpens.mem_isoOpen_iff s x).mpr ⟨U, hx, ?_⟩
    apply (coefficient_restrict_isUnit e s U.ι).mp
    apply (isUnit_iff_basicOpen_top _).mpr
    rw [← Scheme.preimage_basicOpen_top]
    ext z
    change z.val ∈ X.basicOpen (coefficient e s) ↔ True
    exact iff_true_intro z.property

lemma isoOpen_restrictSection {M : X.Modules} (s : O X ⟶ M)
    (φ : Y ⟶ X) [IsOpenImmersion φ] :
    SectionOpens.isoOpen (restrictSection φ s) = φ ⁻¹ᵁ SectionOpens.isoOpen s := by
  exact (SectionOpens.isoOpen_precomp (Scheme.Modules.restrictUnitIso φ).symm
    ((Scheme.Modules.restrictFunctor φ).map s)).trans (SectionOpens.isoOpen_restrict s φ)

theorem preimage_isoOpen {M : X.Modules} (s : O X ⟶ M)
    (φ : Y ⟶ X) [IsOpenImmersion φ] (e : M.restrict φ ≅ O Y) :
    φ ⁻¹ᵁ SectionOpens.isoOpen s =
      Y.basicOpen (coefficient e (restrictSection φ s)) := by
  rw [← isoOpen_restrictSection, isoOpen_eq_basicOpen e]

end Frames

end PiExponentSeshadri

end

end OAI
end Source0333

-- Source: OAI/NumberTheory/PiExponent/Geometry/ProjectiveCharts.lean
section Source0334
/-
Modification notice for the LogTwo project.
Derived from openai/math (Apache-2.0), revision adc7f1241b42e322a6451854ab7e4b4c146bf78a.
Original source: lean/OAI/NumberTheory/PiExponent/Geometry/ProjectiveCharts.lean
Changes: Convert module/import declarations to the Lean 4.34 public module format.
See ../THIRD_PARTY_NOTICES.txt for provenance and the recorded changes.
-/

namespace OAI

noncomputable section

namespace PiExponentSeshadri.Projective

section
open AlgebraicGeometry CategoryTheory TopologicalSpace
open MvPolynomial HomogeneousLocalization
attribute [local instance] Classical.propDecidable

lemma homogeneous_eval₂_scale {R S σ : Type*} [CommRing R] [CommRing S]
    {p : MvPolynomial σ R} {n : ℕ} (hp : p.IsHomogeneous n)
    (f : R →+* S) (u : σ → S) (a : S) :
    eval₂ f (fun j => a * u j) p = a ^ n * eval₂ f u p := by
  classical
  rw [p.as_sum]
  simp only [eval₂_sum, eval₂_monomial, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro d hd
  simp only [mul_pow, Finsupp.prod, Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum]
  rw [← hp.degree_eq_sum_deg_support hd]
  ring

variable {R σ : Type*} [CommRing R] (i : σ)
attribute [local instance] MvPolynomial.gradedAlgebra

abbrev PolyGrade (R σ : Type*) [CommRing R] := MvPolynomial.homogeneousSubmodule σ R
lemma poly_X_mem : X (R := R) i ∈ PolyGrade R σ 1 := isHomogeneous_X R i

abbrev PolyChart := HomogeneousLocalization.Away (PolyGrade R σ) (X i)
abbrev ChartVariables := {j : σ // j ≠ i}

def chartConstants : R →+* PolyChart (R := R) i :=
  (HomogeneousLocalization.fromZeroRingHom _ _).comp
    { toFun := fun r => ⟨C r, isHomogeneous_C _ _⟩
      map_one' := Subtype.ext C_1
      map_mul' := fun _ _ => Subtype.ext C_mul
      map_zero' := Subtype.ext C_0
      map_add' := fun _ _ => Subtype.ext C_add }

def chartCoordinate (j : σ) : PolyChart (R := R) i :=
  Away.mk _ (poly_X_mem (R := R) i) 1 (X j) (by simpa using poly_X_mem (R := R) j)

def dehomogenize : MvPolynomial σ R →+* MvPolynomial (ChartVariables i) R :=
  eval₂Hom C (fun j => if h : j = i then 1 else X ⟨j, h⟩)

@[simp] lemma dehomogenize_X_self : dehomogenize (R := R) i (X i) = 1 := by
  classical
  simp [dehomogenize]

def chartToPoly : PolyChart (R := R) i →+* MvPolynomial (ChartVariables i) R :=
  (Localization.awayLift (dehomogenize i) (X i) (by simp)).comp (algebraMap _ _)

def polyToChart : MvPolynomial (ChartVariables i) R →+* PolyChart (R := R) i :=
  eval₂Hom (chartConstants i) (fun j => chartCoordinate i j.val)

@[simp] lemma chartToPoly_mk (n : ℕ) (p : MvPolynomial σ R)
    (hp : p ∈ PolyGrade R σ (n • 1)) :
    chartToPoly i (Away.mk _ (poly_X_mem (R := R) i) n p hp) = dehomogenize i p := by
  have h := Localization.awayLift_mk (dehomogenize (R := R) i) (X i) p 1
    (by simp) n
  simpa only [chartToPoly, RingHom.comp_apply, HomogeneousLocalization.algebraMap_apply,
    Away.val_mk, one_pow, mul_one] using h

@[simp] lemma chartToPoly_constants (r : R) :
    chartToPoly i (chartConstants i r) = C r := by
  exact (chartToPoly_mk i 0 (C r) (by simp)).trans
    (by simp [dehomogenize])

@[simp] lemma chartToPoly_coordinate (j : σ) :
    chartToPoly (R := R) i (chartCoordinate i j) =
      if h : j = i then 1 else X ⟨j, h⟩ := by
  rw [chartCoordinate, chartToPoly_mk]
  simp [dehomogenize]

lemma chartToPoly_comp_polyToChart :
    (chartToPoly (R := R) i).comp (polyToChart i) = RingHom.id _ := by
  classical
  apply MvPolynomial.ringHom_ext
  · intro r
    simp [polyToChart]
  · intro j
    simp [polyToChart, j.property]

lemma chart_val_mk (n : ℕ) (p : MvPolynomial σ R)
    (hp : p ∈ PolyGrade R σ (n • 1)) :
    (Away.mk _ (poly_X_mem (R := R) i) n p hp).val =
      algebraMap (MvPolynomial σ R) (Localization.Away (X (R := R) i)) p *
        (IsLocalization.Away.invSelf (X (R := R) i)) ^ n := by
  rw [Away.val_mk, Localization.mk_eq_mk', IsLocalization.mk'_eq_mul_mk'_one]
  congr 1
  rw [IsLocalization.Away.invSelf, ← IsLocalization.mk'_pow]
  simp only [one_pow]
  rfl

lemma chart_val_constants (r : R) :
    (chartConstants i r).val =
      algebraMap (MvPolynomial σ R) (Localization.Away (X (R := R) i)) (C r) := by
  exact (chart_val_mk i 0 (C r) (by simp)).trans
    (by simp only [pow_zero, mul_one])

lemma chart_val_coordinate (j : σ) :
    (chartCoordinate (R := R) i j).val =
      algebraMap (MvPolynomial σ R) (Localization.Away (X (R := R) i)) (X j) *
        IsLocalization.Away.invSelf (X (R := R) i) := by
  rw [chartCoordinate, chart_val_mk, pow_one]

lemma chart_dehomogenize_val :
    (algebraMap (PolyChart (R := R) i) (Localization.Away (X i))).comp
      ((polyToChart i).comp (dehomogenize i)) =
    eval₂Hom ((algebraMap (MvPolynomial σ R) (Localization.Away (X (R := R) i))).comp C)
      (fun j => IsLocalization.Away.invSelf (X (R := R) i) *
        algebraMap (MvPolynomial σ R) (Localization.Away (X (R := R) i)) (X j)) := by
  apply MvPolynomial.ringHom_ext
  · intro r
    simp [dehomogenize, polyToChart, chart_val_constants]
  · intro j
    by_cases h : j = i
    · subst j
      simp only [RingHom.comp_apply, dehomogenize_X_self, map_one, eval₂Hom_X']
      symm
      rw [mul_comm]
      exact IsLocalization.Away.mul_invSelf (X i)
    · simp [dehomogenize, polyToChart, h, chart_val_coordinate, mul_comm]

lemma polyToChart_comp_chartToPoly :
    (polyToChart (R := R) i).comp (chartToPoly i) = RingHom.id _ := by
  apply RingHom.ext
  intro x
  obtain ⟨n, p, hp, rfl⟩ := Away.mk_surjective _ (poly_X_mem (R := R) i) x
  apply HomogeneousLocalization.val_injective _
  simp only [RingHom.comp_apply, RingHom.id_apply, chartToPoly_mk, chart_val_mk]
  have he := RingHom.congr_fun (chart_dehomogenize_val (R := R) i) p
  change (polyToChart i (dehomogenize i p)).val = _ at he
  rw [he]
  change eval₂ _ _ p = _
  rw [homogeneous_eval₂_scale (by simpa using hp)]
  have hid : eval₂Hom ((algebraMap (MvPolynomial σ R) (Localization.Away (X (R := R) i))).comp C)
      (fun j => algebraMap (MvPolynomial σ R) (Localization.Away (X (R := R) i)) (X j)) =
      algebraMap (MvPolynomial σ R) (Localization.Away (X (R := R) i)) := by
    apply MvPolynomial.ringHom_ext <;> intro r <;> simp
  change _ * (eval₂Hom _ _ p) = _
  rw [hid]
  exact mul_comm _ _

def polynomialChartEquiv : PolyChart (R := R) i ≃+* MvPolynomial (ChartVariables i) R :=
  { chartToPoly i with
    invFun := polyToChart i
    left_inv := fun p => RingHom.congr_fun (polyToChart_comp_chartToPoly i) p
    right_inv := fun p => RingHom.congr_fun (chartToPoly_comp_polyToChart i) p }

def projectiveChartIso :
    (Proj.basicOpen (PolyGrade R σ) (X i)).toScheme ≅
      Spec (CommRingCat.of (MvPolynomial (ChartVariables i) R)) :=
  Proj.basicOpenIsoSpec _ (X i) (poly_X_mem (R := R) i) (by decide) ≪≫
    Scheme.Spec.mapIso ((polynomialChartEquiv i).toCommRingCatIso.symm.op)

end

open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite
open MvPolynomial
attribute [local instance] Classical.propDecidable
attribute [local instance] MvPolynomial.gradedAlgebra
variable {R σ : Type*} [CommRing R] (i : σ)

def chartSectionRingEquiv :
    Γ(Proj (PolyGrade R σ), Proj.basicOpen (PolyGrade R σ) (X i)) ≃+*
      MvPolynomial (ChartVariables i) R :=
  ((Proj.basicOpen (PolyGrade R σ) (X i)).topIso.symm ≪≫
    Scheme.Γ.mapIso (projectiveChartIso (R := R) i).symm.op ≪≫
    Scheme.ΓSpecIso (CommRingCat.of (MvPolynomial (ChartVariables i) R))).commRingCatIsoToRingEquiv

lemma standardChart_isAffineOpen :
    IsAffineOpen (Proj.basicOpen (PolyGrade R σ) (X i)) :=
  Proj.isAffineOpen_basicOpen _ _ (poly_X_mem i) (by decide)

lemma standardChart_cover :
    (⨆ i : σ, Proj.basicOpen (PolyGrade R σ) (X i)) = ⊤ := by
  apply Proj.iSup_basicOpen_eq_top
  rw [HomogeneousIdeal.toIdeal_irrelevant_le]
  intro n hn p hp
  change p ∈ idealOfVars σ R
  rw [← pow_one (idealOfVars σ R), mem_pow_idealOfVars_iff]
  intro d hd
  change 1 ≤ d.sum fun _ v => v
  rw [Finsupp.sum, ← hp.degree_eq_sum_deg_support hd]
  exact hn

end PiExponentSeshadri.Projective

end

end OAI
end Source0334

-- Source: OAI/NumberTheory/PiExponent/Geometry/ProjectiveCoordinates.lean
section Source0335
-- Modified in this edition: unused plain lemmas removed; see reduction.json.
/-
Modification notice for the LogTwo project.
Derived from openai/math (Apache-2.0), revision adc7f1241b42e322a6451854ab7e4b4c146bf78a.
Original source: lean/OAI/NumberTheory/PiExponent/Geometry/ProjectiveCoordinates.lean
Changes: Convert module/import declarations to the Lean 4.34 public module format.
See ../THIRD_PARTY_NOTICES.txt for provenance and the recorded changes.
-/

namespace OAI

noncomputable section

universe u

namespace PiExponentSeshadri.Projective

section
open AlgebraicGeometry CategoryTheory HomogeneousLocalization
variable {A R σ : Type u} [CommRing A] [CommRing R] [SetLike σ A]
  [AddSubgroupClass σ A] {𝒜 : ℕ → σ} [GradedRing 𝒜]
  (f : A →+* R)

def evalAway (s : A) (hs : IsUnit (f s)) : Away 𝒜 s →+* R :=
  (IsLocalization.Away.lift s hs : Localization.Away s →+* R).comp
    (algebraMap (Away 𝒜 s) (Localization.Away s))

lemma evalAway_val (s : A) (hs : IsUnit (f s)) (x : Away 𝒜 s) :
    evalAway f s hs x = IsLocalization.Away.lift s hs x.val := rfl

lemma evalAway_transition {s t : A} {d : ℕ} (ht : t ∈ 𝒜 d)
    (hs : IsUnit (f s)) (hst : IsUnit (f (s * t))) :
    (evalAway f (s * t) hst).comp (awayMap 𝒜 ht rfl) = evalAway f s hs := by
  have hunit : IsUnit (algebraMap A (Localization.Away (s * t)) s) :=
    IsLocalization.Away.isUnit_of_dvd (s * t) (dvd_mul_right s t)
  have H : (IsLocalization.Away.lift (s * t) hst : Localization.Away (s * t) →+* R).comp
      (Localization.awayLift (algebraMap A (Localization.Away (s * t))) s hunit) =
      (IsLocalization.Away.lift s hs : Localization.Away s →+* R) := by
    apply IsLocalization.ringHom_ext (Submonoid.powers s)
    ext a
    simp
  apply RingHom.ext
  intro x
  simpa only [RingHom.comp_apply, evalAway_val, val_awayMap] using RingHom.congr_fun H x.val

lemma evalAway_natural {T : Type u} [CommRing T] (g : R →+* T)
    (s : A) (hs : IsUnit (f s)) :
    g.comp (evalAway (𝒜 := 𝒜) f s hs) = evalAway (g.comp f) s (hs.map g) := by
  have H : g.comp (IsLocalization.Away.lift s hs : Localization.Away s →+* R) =
      (IsLocalization.Away.lift (g := g.comp f) s (hs.map g) : Localization.Away s →+* T) := by
    apply IsLocalization.ringHom_ext (Submonoid.powers s)
    ext a
    simp
  exact congrArg (fun h : Localization.Away s →+* T =>
    h.comp (algebraMap (Away 𝒜 s) (Localization.Away s))) H

lemma evalAway_mk_clear {s : A} {d : ℕ} (hs : s ∈ 𝒜 d) (hu : IsUnit (f s))
    (n : ℕ) (a : A) (ha : a ∈ 𝒜 (n • d)) :
    evalAway f s hu (Away.mk 𝒜 hs n a ha) * f s ^ n = f a := by
  rw [evalAway_val, Away.val_mk, Localization.mk_eq_mk']
  have H := IsLocalization.mk'_spec (Localization.Away s) a
    (⟨s ^ n, ⟨n, rfl⟩⟩ : Submonoid.powers s)
  apply_fun (IsLocalization.Away.lift s hu : Localization.Away s →+* R) at H
  simpa only [map_mul, IsLocalization.Away.lift_eq, map_pow] using H

lemma evalAway_scale {s : A} {d : ℕ} (hs : s ∈ 𝒜 d) (hu : IsUnit (f s))
    (g : A →+* R) (hv : IsUnit (g s)) (c : Rˣ)
    (hscale : ∀ n a, a ∈ 𝒜 n → g a = (c : R) ^ n * f a) :
    evalAway (𝒜 := 𝒜) f s hu = evalAway g s hv := by
  apply RingHom.ext
  intro x
  obtain ⟨n, a, ha, rfl⟩ := Away.mk_surjective 𝒜 hs x
  apply (hv.pow n).mul_right_cancel
  have Hf := evalAway_mk_clear f hs hu n a ha
  have Hg := evalAway_mk_clear g hs hv n a ha
  rw [Hg, hscale d s hs, hscale _ a ha, mul_pow, ← pow_mul]
  rw [smul_eq_mul, Nat.mul_comm n d]
  calc
    _ = (c : R) ^ (d * n) * (evalAway f s hu (Away.mk 𝒜 hs n a ha) * f s ^ n) := by ring
    _ = _ := by rw [Hf]

def fromUnitCoordinate {s : A} {d : ℕ} (hd : 0 < d) (hs : s ∈ 𝒜 d)
    (hu : IsUnit (f s)) : Spec (CommRingCat.of R) ⟶ Proj 𝒜 :=
  Spec.map (CommRingCat.ofHom (evalAway f s hu)) ≫ Proj.awayι 𝒜 s hs hd

lemma fromUnitCoordinate_mul {s t : A} {d e : ℕ} (hd : 0 < d)
    (hs : s ∈ 𝒜 d) (ht : t ∈ 𝒜 e) (hu : IsUnit (f s))
    (hut : IsUnit (f (s * t))) :
    fromUnitCoordinate f hd hs hu =
      fromUnitCoordinate f (Nat.add_pos_left hd e) (SetLike.mul_mem_graded hs ht) hut := by
  unfold fromUnitCoordinate
  rw [← Proj.SpecMap_awayMap_awayι 𝒜 hs hd ht rfl, ← Category.assoc,
    ← Spec.map_comp, ← CommRingCat.ofHom_comp, evalAway_transition f ht hu hut]

@[reassoc]
lemma fromUnitCoordinate_natural {T : Type u} [CommRing T] (g : R →+* T)
    {s : A} {d : ℕ} (hd : 0 < d) (hs : s ∈ 𝒜 d) (hu : IsUnit (f s)) :
    Spec.map (CommRingCat.ofHom g) ≫ fromUnitCoordinate f hd hs hu =
      fromUnitCoordinate (g.comp f) hd hs (hu.map g) := by
  unfold fromUnitCoordinate
  rw [← Category.assoc, ← Spec.map_comp, ← CommRingCat.ofHom_comp, evalAway_natural]

lemma fromUnitCoordinate_scale {s : A} {d : ℕ} (hd : 0 < d)
    (hs : s ∈ 𝒜 d) (hu : IsUnit (f s)) (g : A →+* R) (hv : IsUnit (g s))
    (c : Rˣ) (hscale : ∀ n a, a ∈ 𝒜 n → g a = (c : R) ^ n * f a) :
    fromUnitCoordinate f hd hs hu = fromUnitCoordinate g hd hs hv := by
  unfold fromUnitCoordinate
  rw [evalAway_scale f hs hu g hv c hscale]

lemma fromUnitCoordinate_preimage {s t : A} {e : ℕ} (hs : s ∈ 𝒜 1)
    (hu : IsUnit (f s)) (hsone : f s = 1) (he : 0 < e) (ht : t ∈ 𝒜 e) :
    fromUnitCoordinate f (by decide) hs hu ⁻¹ᵁ Proj.basicOpen 𝒜 t =
      PrimeSpectrum.basicOpen (f t) := by
  rw [fromUnitCoordinate, Scheme.Hom.comp_preimage,
    Proj.awayι_preimage_basicOpen 𝒜 hs (by decide) ht he, SpecMap_preimage_basicOpen]
  congr 1
  change evalAway f s hu (Away.isLocalizationElem hs ht) = f t
  have H := evalAway_mk_clear f hs hu e (t ^ 1)
    (show t ^ 1 ∈ 𝒜 (e • 1) from by simpa using ht)
  simpa only [Away.isLocalizationElem, hsone, one_pow, mul_one, pow_one] using H

theorem fromUnitCoordinate_eq {s t : A} {d e : ℕ} (hd : 0 < d) (he : 0 < e)
    (hs : s ∈ 𝒜 d) (ht : t ∈ 𝒜 e) (hu : IsUnit (f s)) (hv : IsUnit (f t)) :
    fromUnitCoordinate f hd hs hu = fromUnitCoordinate f he ht hv := by
  have huv : IsUnit (f (s * t)) := by rw [map_mul]; exact hu.mul hv
  have hvu : IsUnit (f (t * s)) := by rw [map_mul]; exact hv.mul hu
  rw [fromUnitCoordinate_mul f hd hs ht hu huv,
    fromUnitCoordinate_mul f he ht hs hv hvu]
  congr 1 <;> ac_rfl

end

section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits MvPolynomial TopologicalSpace
variable {K σ : Type u} [CommRing K]
attribute [local instance] MvPolynomial.gradedAlgebra

lemma coordinates_X_mem (i : σ) : MvPolynomial.X i ∈ homogeneousSubmodule σ K 1 :=
  isHomogeneous_X K i

def coordinatesMap (X : Scheme.{u}) (k : K →+* Γ(X, ⊤)) (a : σ → Γ(X, ⊤))
    (i : σ) (hi : a i = 1) : X ⟶ Proj (homogeneousSubmodule σ K) :=
  X.toSpecΓ ≫ fromUnitCoordinate (eval₂Hom k a) (by decide)
    (coordinates_X_mem (K := K) i) (by simpa only [eval₂Hom_X', hi] using isUnit_one)

lemma coordinates_eval_natural {R T : Type u} [CommRing R] [CommRing T]
    (g : R →+* T) (k : K →+* R) (a : σ → R) :
    g.comp (eval₂Hom k a) = eval₂Hom (g.comp k) (fun j => g (a j)) := by
  apply MvPolynomial.ringHom_ext <;> intro j <;> simp

@[reassoc]
lemma coordinatesMap_natural {X Y : Scheme.{u}} (φ : Y ⟶ X)
    (k : K →+* Γ(X, ⊤)) (a : σ → Γ(X, ⊤)) (i : σ) (hi : a i = 1) :
    φ ≫ coordinatesMap X k a i hi =
      coordinatesMap Y (φ.appTop.hom.comp k) (fun j => φ.appTop (a j)) i
        (by simp only [hi, map_one]) := by
  unfold coordinatesMap
  rw [← Category.assoc, Scheme.toSpecΓ_naturality, Category.assoc,
    ]
  congr 1
  change Spec.map (CommRingCat.ofHom φ.appTop.hom) ≫ _ = _
  rw [fromUnitCoordinate_natural]
  congr 1
  exact coordinates_eval_natural φ.appTop.hom k a

lemma coordinatesMap_scale (X : Scheme.{u}) (k : K →+* Γ(X, ⊤))
    (a b : σ → Γ(X, ⊤)) (i j : σ) (hi : a i = 1) (hj : b j = 1)
    (c : Γ(X, ⊤)ˣ) (hscale : ∀ q, b q = (c : Γ(X, ⊤)) * a q) :
    coordinatesMap X k a i hi = coordinatesMap X k b j hj := by
  let f := eval₂Hom k a
  let g := eval₂Hom k b
  have hf : IsUnit (f (MvPolynomial.X (R := K) i)) := by
    simpa only [f, eval₂Hom_X', hi] using (isUnit_one : IsUnit (1 : Γ(X, ⊤)))
  have hg : IsUnit (g (MvPolynomial.X (R := K) i)) := by
    simpa only [g, eval₂Hom_X', hscale i, hi, mul_one] using c.isUnit
  have hg' : IsUnit (g (MvPolynomial.X (R := K) j)) := by
    simpa only [g, eval₂Hom_X', hj] using (isUnit_one : IsUnit (1 : Γ(X, ⊤)))
  have H : ∀ n p, p ∈ homogeneousSubmodule σ K n →
      g p = (c : Γ(X, ⊤)) ^ n * f p := by
    intro n p hp
    change eval₂ k b p = _
    have hb : b = fun q => (c : Γ(X, ⊤)) * a q := funext hscale
    rw [hb]
    exact homogeneous_eval₂_scale hp k a c
  unfold coordinatesMap
  congr 1
  exact (fromUnitCoordinate_scale (𝒜 := homogeneousSubmodule σ K) (d := 1) f (by decide) (coordinates_X_mem (K := K) i)
    hf g hg c H).trans
      (fromUnitCoordinate_eq (𝒜 := homogeneousSubmodule σ K) (d := 1) (e := 1) g (by decide) (by decide)
        (coordinates_X_mem (K := K) i) (coordinates_X_mem (K := K) j) hg hg')

lemma coordinatesMap_preimage (X : Scheme.{u}) (k : K →+* Γ(X, ⊤))
    (a : σ → Γ(X, ⊤)) (i : σ) (hi : a i = 1) (j : σ) :
    coordinatesMap X k a i hi ⁻¹ᵁ
      Proj.basicOpen (homogeneousSubmodule σ K) (MvPolynomial.X j) = X.basicOpen (a j) := by
  rw [coordinatesMap, Scheme.Hom.comp_preimage,
    fromUnitCoordinate_preimage _ (coordinates_X_mem (K := K) i) _
      (by simpa only [eval₂Hom_X'] using hi) (by decide) (coordinates_X_mem (K := K) j),
    eval₂Hom_X', Scheme.toSpecΓ_preimage_basicOpen]

structure CoordinateAtlas (X : Scheme.{u}) where
  cover : X.OpenCover
  scalars : ∀ i : cover.I₀, K →+* Γ(cover.X i, ⊤)
  coordinates : ∀ i : cover.I₀, σ → Γ(cover.X i, ⊤)
  index : cover.I₀ → σ
  normalized : ∀ i, coordinates i (index i) = 1
  scalarOverlap : ∀ i j,
    (pullback.fst (cover.f i) (cover.f j)).appTop.hom.comp (scalars i) =
      (pullback.snd (cover.f i) (cover.f j)).appTop.hom.comp (scalars j)
  coordinateOverlap : ∀ i j,
    ∃ c : Γ(pullback (cover.f i) (cover.f j), ⊤)ˣ, ∀ q,
      (pullback.snd (cover.f i) (cover.f j)).appTop (coordinates j q) =
        (c : Γ(pullback (cover.f i) (cover.f j), ⊤)) *
          (pullback.fst (cover.f i) (cover.f j)).appTop (coordinates i q)

variable {X : Scheme.{u}} (D : CoordinateAtlas (K := K) (σ := σ) X)

def CoordinateAtlas.localMap (i : D.cover.I₀) :
    D.cover.X i ⟶ Proj (homogeneousSubmodule σ K) :=
  coordinatesMap _ (D.scalars i) (D.coordinates i) (D.index i) (D.normalized i)

lemma CoordinateAtlas.compatible (i j : D.cover.I₀) :
    pullback.fst (D.cover.f i) (D.cover.f j) ≫ D.localMap i =
      pullback.snd (D.cover.f i) (D.cover.f j) ≫ D.localMap j := by
  unfold CoordinateAtlas.localMap
  rw [coordinatesMap_natural, coordinatesMap_natural]
  obtain ⟨c, hc⟩ := D.coordinateOverlap i j
  simpa only [D.scalarOverlap i j] using
    coordinatesMap_scale _
      ((pullback.fst (D.cover.f i) (D.cover.f j)).appTop.hom.comp (D.scalars i))
      _ _ (D.index i) (D.index j)
      (by simp only [D.normalized, map_one])
      (by simp only [D.normalized, map_one]) c hc

def CoordinateAtlas.morphism : X ⟶ Proj (homogeneousSubmodule σ K) :=
  D.cover.glueMorphisms D.localMap D.compatible

@[reassoc, simp]
lemma CoordinateAtlas.cover_morphism (i : D.cover.I₀) :
    D.cover.f i ≫ D.morphism = D.localMap i :=
  D.cover.ι_glueMorphisms _ _ i

end

section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace
open scoped AlgebraicGeometry
open PiExponentSeshadri.Frames
attribute [local instance] MvPolynomial.gradedAlgebra
variable {K σ : Type u} [CommRing K] {X : Scheme.{u}}

def atlasOfFramedSections {M : X.Modules} (k : K →+* Γ(X, ⊤))
    (s : σ → (O X ⟶ M)) (𝒰 : X.OpenCover)
    (e : ∀ i, M.restrict (𝒰.f i) ≅ O (𝒰.X i)) (index : 𝒰.I₀ → σ)
    (hnorm : ∀ i, coefficient (e i) (restrictSection (𝒰.f i) (s (index i))) = 1) :
    CoordinateAtlas (K := K) (σ := σ) X where
  cover := 𝒰
  scalars i := (𝒰.f i).appTop.hom.comp k
  coordinates i q := coefficient (e i) (restrictSection (𝒰.f i) (s q))
  index := index
  normalized := hnorm
  scalarOverlap i j := by
    rw [← RingHom.comp_assoc, ← RingHom.comp_assoc]
    congr 1
    simpa only [Scheme.Hom.comp_appTop, CommRingCat.hom_comp] using
      congrArg (fun f : pullback (𝒰.f i) (𝒰.f j) ⟶ X => f.appTop.hom)
        (pullback.condition (f := 𝒰.f i) (g := 𝒰.f j))
  coordinateOverlap i j := by
    obtain ⟨c, hc⟩ := overlap_coefficients (𝒰.f i) (𝒰.f j)
      (pullback.fst (𝒰.f i) (𝒰.f j)) (pullback.snd (𝒰.f i) (𝒰.f j))
      (pullback.condition (f := 𝒰.f i) (g := 𝒰.f j)) (e i) (e j)
    exact ⟨c, fun q => hc (s q)⟩

def sectionFrame {M : X.Modules} (s : O X ⟶ M) :
    M.restrict (SectionOpens.isoOpen s).ι ≅ O (SectionOpens.isoOpen s).toScheme := by
  letI := SectionOpens.isIso_restrict_isoOpen s
  exact (asIso ((Scheme.Modules.restrictFunctor (SectionOpens.isoOpen s).ι).map s)).symm ≪≫
    Scheme.Modules.restrictUnitIso (SectionOpens.isoOpen s).ι

lemma sectionFrame_normalized {M : X.Modules} (s : O X ⟶ M) :
    coefficient (sectionFrame s) (restrictSection (SectionOpens.isoOpen s).ι s) = 1 := by
  change coefficient (sectionFrame s) (sectionFrame s).inv = 1
  exact coefficient_frame (sectionFrame s)

def sectionsMorphism {M : X.Modules} (k : K →+* Γ(X, ⊤))
    (s : σ → (O X ⟶ M)) (hcover : (⨆ i, SectionOpens.isoOpen (s i)) = ⊤) :
    X ⟶ Proj (MvPolynomial.homogeneousSubmodule σ K) :=
  (atlasOfFramedSections k s
    (X.openCoverOfIsOpenCover (fun i => SectionOpens.isoOpen (s i)) hcover)
    (fun i => sectionFrame (s i)) id (fun i => sectionFrame_normalized (s i))).morphism

end

section
open AlgebraicGeometry CategoryTheory TopologicalSpace
open scoped AlgebraicGeometry
open PiExponentSeshadri.Frames
variable {K σ : Type u} [CommRing K] {X : Scheme.{u}}
attribute [local instance] MvPolynomial.gradedAlgebra

lemma sectionsMorphism_local {M : X.Modules} (k : K →+* Γ(X, ⊤))
    (s : σ → (O X ⟶ M)) (hcover : (⨆ i, SectionOpens.isoOpen (s i)) = ⊤) (i : σ) :
    (SectionOpens.isoOpen (s i)).ι ≫ sectionsMorphism k s hcover =
      coordinatesMap (SectionOpens.isoOpen (s i)).toScheme
        ((SectionOpens.isoOpen (s i)).ι.appTop.hom.comp k)
        (fun j => coefficient (sectionFrame (s i))
          (restrictSection (SectionOpens.isoOpen (s i)).ι (s j))) i
        (sectionFrame_normalized (s i)) := by
  exact CoordinateAtlas.cover_morphism
    (atlasOfFramedSections k s
      (X.openCoverOfIsOpenCover (fun a => SectionOpens.isoOpen (s a)) hcover)
      (fun a => sectionFrame (s a)) id (fun a => sectionFrame_normalized (s a))) i

theorem sectionsMorphism_preimage {M : X.Modules} (k : K →+* Γ(X, ⊤))
    (s : σ → (O X ⟶ M)) (hcover : (⨆ i, SectionOpens.isoOpen (s i)) = ⊤) (j : σ) :
    sectionsMorphism k s hcover ⁻¹ᵁ
      Proj.basicOpen (MvPolynomial.homogeneousSubmodule σ K) (MvPolynomial.X j) =
      SectionOpens.isoOpen (s j) := by
  ext x
  have hx : x ∈ ⨆ i, SectionOpens.isoOpen (s i) := by rw [hcover]; trivial
  obtain ⟨i, hi⟩ := Opens.mem_iSup.mp hx
  let U := SectionOpens.isoOpen (s i)
  have H : U.ι ⁻¹ᵁ (sectionsMorphism k s hcover ⁻¹ᵁ
      Proj.basicOpen (MvPolynomial.homogeneousSubmodule σ K) (MvPolynomial.X j)) =
      U.ι ⁻¹ᵁ SectionOpens.isoOpen (s j) := by
    rw [← Scheme.Hom.comp_preimage, sectionsMorphism_local,
      coordinatesMap_preimage, preimage_isoOpen (s j) U.ι (sectionFrame (s i))]
  exact Set.ext_iff.mp (congrArg SetLike.coe H) (⟨x, hi⟩ : U.toScheme)

end
section
open AlgebraicGeometry CategoryTheory TopologicalSpace MvPolynomial
open PiExponentSeshadri.Frames
attribute [local instance] MvPolynomial.gradedAlgebra
variable {K σ : Type} [CommRing K]
variable (M : (Proj (PolyGrade K σ)).Modules)
variable (k : K →+* Γ(Proj (PolyGrade K σ),⊤))
variable (s : σ → (O (Proj (PolyGrade K σ)) ⟶ M))
variable (hc : (⨆ i, SectionOpens.isoOpen (s i)) = ⊤)
variable (hid : sectionsMorphism k s hc = 𝟙 (Proj (PolyGrade K σ)))

include hid

lemma identityCoordinateOpen (i : σ) :
    SectionOpens.isoOpen (s i) = Proj.basicOpen (PolyGrade K σ) (X i) := by
  have h := sectionsMorphism_preimage k s hc i
  rw [hid] at h
  exact h.symm

end

open AlgebraicGeometry CategoryTheory TopologicalSpace
open PiExponentSeshadri.Frames
variable {X : Scheme} {M : X.Modules}

def sectionFrameOn (s : O X ⟶ M) (U : X.Opens) (hU : SectionOpens.isoOpen s = U) :
    M.restrict U.ι ≅ O U.toScheme := hU ▸ sectionFrame s

end PiExponentSeshadri.Projective

end

end OAI
end Source0335

-- Source: OAI/NumberTheory/PiExponent/Polynomials/GradedSubring.lean
section Source0336
/-
Modification notice for the LogTwo project.
Derived from openai/math (Apache-2.0), revision adc7f1241b42e322a6451854ab7e4b4c146bf78a.
Original source: lean/OAI/NumberTheory/PiExponent/Polynomials/GradedSubring.lean
Changes: Convert module/import declarations to the Lean 4.34 public module format.
See ../THIRD_PARTY_NOTICES.txt for provenance and the recorded changes.
-/

namespace OAI

noncomputable section

namespace PiExponent

open DirectSum

variable {A : Type*} [CommRing A]
  (𝒜 : ℕ → Submodule ℤ A) [GradedAlgebra 𝒜]
  (S : Subring A)

def subringGrade (n : ℕ) : Submodule ℤ S :=
  (𝒜 n).comap S.subtype.toAddMonoidHom.toIntLinearMap

theorem subringGrade_independent : iSupIndep (subringGrade 𝒜 S) := by
  have h := (DirectSum.Decomposition.isInternal 𝒜).submodule_iSupIndep
  intro i
  rw [disjoint_iff_inf_le]
  intro x hx
  apply Subtype.ext
  apply (disjoint_iff_inf_le.mp (h i))
  refine ⟨hx.1, ?_⟩
  have hle : (⨆ j, ⨆ (_ : j ≠ i), subringGrade 𝒜 S j) ≤
      (⨆ j, ⨆ (_ : j ≠ i), 𝒜 j).comap S.subtype.toAddMonoidHom.toIntLinearMap := by
    refine iSup_le fun j => iSup_le fun hj => ?_
    exact Submodule.comap_mono (le_iSup_of_le j (le_iSup_of_le hj le_rfl))
  exact hle hx.2

theorem subringGrade_spans
    (hS : ∀ n x, x ∈ S → (decompose 𝒜 x n : A) ∈ S) :
    (⨆ n, subringGrade 𝒜 S n) = ⊤ := by
  classical
  apply top_unique
  intro x _
  let c : ℕ → S := fun n => ⟨decompose 𝒜 x.1 n, hS n x.1 x.2⟩
  have he : x = ∑ n ∈ (decompose 𝒜 x.1).support, c n := by
    apply Subtype.ext
    change x.1 = S.subtype (∑ n ∈ (decompose 𝒜 x.1).support, c n)
    rw [map_sum]
    exact (sum_support_decompose 𝒜 x.1).symm
  rw [he]
  apply Submodule.sum_mem
  intro n hn
  exact (le_iSup (subringGrade 𝒜 S) n) (show c n ∈ subringGrade 𝒜 S n from
    (decompose 𝒜 x.1 n).2)

@[instance_reducible]
def subringGradedAlgebra
    (hS : ∀ n x, x ∈ S → (decompose 𝒜 x n : A) ∈ S) :
    GradedAlgebra (subringGrade 𝒜 S) where
  one_mem := show (1 : A) ∈ 𝒜 0 from SetLike.one_mem_graded 𝒜
  mul_mem := by
    intro i j x y hx hy
    change (x.1 * y.1) ∈ 𝒜 (i + j)
    exact SetLike.mul_mem_graded hx hy
  toDecomposition :=
    (DirectSum.isInternal_submodule_of_iSupIndep_of_iSup_eq_top
      (subringGrade_independent 𝒜 S) (subringGrade_spans 𝒜 S hS)).chooseDecomposition

end PiExponent

end

end OAI
end Source0336

-- Source: OAI/NumberTheory/PiExponent/Polynomials/WeightedMonomialMap.lean
section Source0337
-- Modified in this edition: unused plain lemmas removed; see reduction.json.
/-
Modification notice for the LogTwo project.
Derived from openai/math (Apache-2.0), revision adc7f1241b42e322a6451854ab7e4b4c146bf78a.
Original source: lean/OAI/NumberTheory/PiExponent/Polynomials/WeightedMonomialMap.lean
Changes: Convert module/import declarations to the Lean 4.34 public module format.
See ../THIRD_PARTY_NOTICES.txt for provenance and the recorded changes.
-/

namespace OAI

noncomputable section

namespace PiExponent.WeightedCompactification

open MvPolynomial

variable {R ι σ : Type*} [CommRing R]

attribute [local instance] MvPolynomial.gradedAlgebra

def affineMonomialMap (a : σ → ι →₀ ℕ) : MvPolynomial σ R →+* MvPolynomial ι R :=
  eval₂Hom C (fun s => monomial (a s) 1)

def homogeneousMonomialMap (a : σ → ι →₀ ℕ) :
    MvPolynomial σ R →+* MvPolynomial Unit (MvPolynomial ι R) :=
  eval₂Hom (C.comp C) (fun s => X () * C (monomial (a s) 1))

@[simp]
theorem homogeneousMonomialMap_X (a : σ → ι →₀ ℕ) (s : σ) :
    homogeneousMonomialMap (R := R) a (X s) = X () * C (monomial (a s) 1) := by
  simp [homogeneousMonomialMap]

theorem homogeneousMonomialMap_homogeneous (a : σ → ι →₀ ℕ)
    {p : MvPolynomial σ R} {n : ℕ} (hp : p.IsHomogeneous n) :
    (homogeneousMonomialMap a p).IsHomogeneous n := by
  have h : (homogeneousMonomialMap a p).IsHomogeneous (1 * n) :=
    hp.eval₂ (C.comp C) (fun s => X () * C (monomial (a s) 1))
      (fun r => isHomogeneous_C _ _) (fun s => by
        simpa only [mul_comm] using isHomogeneous_C_mul_X (monomial (a s) (1 : R)) ())
  rw [Nat.one_mul] at h
  exact h

def gradedMonomialMap (a : σ → ι →₀ ℕ) :
    homogeneousSubmodule σ R →+*ᵍ homogeneousSubmodule Unit (MvPolynomial ι R) where
  __ := homogeneousMonomialMap a
  map_mem := homogeneousMonomialMap_homogeneous a

def monomialHomogeneousIdeal (a : σ → ι →₀ ℕ) :
    HomogeneousIdeal (homogeneousSubmodule σ R) :=
  HomogeneousIdeal.comap (gradedMonomialMap a) ⊥

end PiExponent.WeightedCompactification

end

end OAI
end Source0337

-- Source: OAI/NumberTheory/PiExponent/Polynomials/WeightedMonomialImage.lean
section Source0338
/-
Modification notice for the LogTwo project.
Derived from openai/math (Apache-2.0), revision adc7f1241b42e322a6451854ab7e4b4c146bf78a.
Original source: lean/OAI/NumberTheory/PiExponent/Polynomials/WeightedMonomialImage.lean
Changes: Convert module/import declarations to the Lean 4.34 public module format.
See ../THIRD_PARTY_NOTICES.txt for provenance and the recorded changes.
-/

namespace OAI

noncomputable section

namespace PiExponent.WeightedCompactification

open MvPolynomial DirectSum

variable {R ι σ : Type*} [CommRing R]

attribute [local instance] MvPolynomial.gradedAlgebra

abbrev monomialImage (a : σ → ι →₀ ℕ) := (homogeneousMonomialMap (R := R) a).range

abbrev ambientGrade (R ι : Type*) [CommRing R] (n : ℕ) :=
  (homogeneousSubmodule Unit (MvPolynomial ι R) n).restrictScalars ℤ

def gradedMonomialMapInt (a : σ → ι →₀ ℕ) :
    homogeneousSubmodule σ R →+*ᵍ ambientGrade R ι where
  __ := homogeneousMonomialMap a
  map_mem := homogeneousMonomialMap_homogeneous a

theorem monomialImage_homogeneous (a : σ → ι →₀ ℕ) (n : ℕ)
    (p : MvPolynomial Unit (MvPolynomial ι R)) (hp : p ∈ monomialImage a) :
    (decompose (ambientGrade R ι) p n : MvPolynomial Unit (MvPolynomial ι R)) ∈
      monomialImage a := by
  obtain ⟨q, rfl⟩ := hp
  refine ⟨decompose (homogeneousSubmodule σ R) q n, ?_⟩
  exact (gradedMonomialMapInt a).map_directSumDecompose

abbrev imageGrade (a : σ → ι →₀ ℕ) := subringGrade (ambientGrade R ι) (monomialImage a)

instance imageGradedAlgebra (a : σ → ι →₀ ℕ) : GradedAlgebra (imageGrade (R := R) a) :=
  subringGradedAlgebra _ _ (monomialImage_homogeneous a)

def gradedImageMap (a : σ → ι →₀ ℕ) :
    homogeneousSubmodule σ R →+*ᵍ imageGrade (R := R) a where
  __ := (homogeneousMonomialMap a).rangeRestrict
  map_mem := homogeneousMonomialMap_homogeneous a

theorem gradedImageMap_surjective (a : σ → ι →₀ ℕ) :
    Function.Surjective (gradedImageMap (R := R) a) :=
  (homogeneousMonomialMap a).rangeRestrict_surjective

def monomialQuotientEquivImage (a : σ → ι →₀ ℕ) :
    (MvPolynomial σ R ⧸ (monomialHomogeneousIdeal (R := R) a).toIdeal) ≃+* monomialImage (R := R) a :=
  RingHom.quotientKerEquivRange (homogeneousMonomialMap a)

instance monomialHomogeneousIdeal_isPrime [IsDomain R] (a : σ → ι →₀ ℕ) :
    (monomialHomogeneousIdeal (R := R) a).toIdeal.IsPrime :=
  RingHom.ker_isPrime (homogeneousMonomialMap a)

abbrev imageCoordinate (a : σ → ι →₀ ℕ) (s : σ) : monomialImage (R := R) a :=
  ⟨homogeneousMonomialMap a (X s), ⟨X s, rfl⟩⟩

theorem imageCoordinate_mem (a : σ → ι →₀ ℕ) (s : σ) :
    imageCoordinate (R := R) a s ∈ imageGrade a 1 :=
  homogeneousMonomialMap_homogeneous a (isHomogeneous_X R s)

def imageEvaluation (a : σ → ι →₀ ℕ) : monomialImage (R := R) a →+* MvPolynomial ι R :=
  (eval₂Hom (RingHom.id _) (fun _ : Unit => 1)).comp (monomialImage a).subtype

@[simp]
theorem imageEvaluation_coordinate (a : σ → ι →₀ ℕ) (s : σ) :
    imageEvaluation (R := R) a (imageCoordinate a s) = monomial (a s) 1 := by
  simp [imageEvaluation, imageCoordinate, homogeneousMonomialMap]

theorem unit_homogeneous_formula {p : MvPolynomial Unit R} {n : ℕ}
    (hp : p.IsHomogeneous n) :
    p = X () ^ n * C (eval (fun _ : Unit => 1) p) := by
  have he : eval₂Hom C (fun _ : Unit => X () * (1 : MvPolynomial Unit R)) =
      RingHom.id (MvPolynomial Unit R) := by
    apply MvPolynomial.ringHom_ext
    · intro r; simp
    · intro u; cases u; simp
  have hc : (C : R →+* MvPolynomial Unit R).comp (eval₂Hom (RingHom.id _) (fun _ : Unit => 1)) =
      eval₂Hom C (fun _ : Unit => (1 : MvPolynomial Unit R)) := by
    apply MvPolynomial.ringHom_ext <;> intro r <;> simp
  have h := PiExponentSeshadri.Projective.homogeneous_eval₂_scale hp C
    (fun _ : Unit => (1 : MvPolynomial Unit R)) (X ())
  change (eval₂Hom C (fun _ : Unit => X () * (1 : MvPolynomial Unit R))) p =
    X () ^ n * (eval₂Hom C (fun _ : Unit => (1 : MvPolynomial Unit R))) p at h
  rw [he, ← hc] at h
  exact h

theorem imageEvaluation_homogeneous_eq_zero (a : σ → ι →₀ ℕ)
    {p : monomialImage (R := R) a} {n : ℕ} (hp : p ∈ imageGrade a n)
    (he : imageEvaluation a p = 0) : p = 0 := by
  apply Subtype.ext
  have h := unit_homogeneous_formula hp
  change eval (fun _ : Unit => 1) p.1 = 0 at he
  change p.1 = X () ^ n * C (eval (fun _ : Unit => 1) p.1) at h
  rw [he, map_zero, mul_zero] at h
  exact h

end PiExponent.WeightedCompactification

end

end OAI
end Source0338

-- Source: OAI/NumberTheory/PiExponent/Approximation/WeightedCompactification.lean
section Source0339
/-
Modification notice for the LogTwo project.
Derived from openai/math (Apache-2.0), revision adc7f1241b42e322a6451854ab7e4b4c146bf78a.
Original source: lean/OAI/NumberTheory/PiExponent/Approximation/WeightedCompactification.lean
Changes: Convert module/import declarations to the Lean 4.34 public module format.
See ../THIRD_PARTY_NOTICES.txt for provenance and the recorded changes.
-/

namespace OAI

noncomputable section

namespace PiExponent.WeightedCompactification

open MvPolynomial HomogeneousLocalization
open PiExponentSeshadri.Projective
open AlgebraicGeometry CategoryTheory

variable {R ι σ : Type*} [CommRing R]

abbrev constantChart (a : σ → ι →₀ ℕ) (z : σ) :=
  HomogeneousLocalization.Away (imageGrade (R := R) a) (imageCoordinate a z)

def chartEvaluation (a : σ → ι →₀ ℕ) (z : σ) (hz : a z = 0) :
    constantChart (R := R) a z →+* MvPolynomial ι R :=
  evalAway (imageEvaluation a) (imageCoordinate a z)
    (by simp [hz])

@[simp]
theorem chartEvaluation_mk (a : σ → ι →₀ ℕ) (z : σ) (hz : a z = 0)
    (n : ℕ) (p : monomialImage (R := R) a) (hp : p ∈ imageGrade a (n • 1)) :
    chartEvaluation a z hz (Away.mk _ (imageCoordinate_mem a z) n p hp) =
      imageEvaluation a p := by
  have h := evalAway_mk_clear (imageEvaluation a) (imageCoordinate_mem a z)
    (show IsUnit (imageEvaluation a (imageCoordinate a z)) by simp [hz]) n p hp
  simpa [chartEvaluation, hz] using h

theorem chartEvaluation_injective (a : σ → ι →₀ ℕ) (z : σ) (hz : a z = 0) :
    Function.Injective (chartEvaluation (R := R) a z hz) := by
  rw [injective_iff_map_eq_zero]
  intro x hx
  obtain ⟨n, p, hp, rfl⟩ := Away.mk_surjective _ (imageCoordinate_mem a z) x
  rw [chartEvaluation_mk] at hx
  have hpzero := imageEvaluation_homogeneous_eq_zero a hp hx
  subst p
  apply HomogeneousLocalization.val_injective
  simp [Away.val_mk, HomogeneousLocalization.val_zero, Localization.mk_zero]

def affineChartCoordinate (a : σ → ι →₀ ℕ) (z s : σ) : constantChart (R := R) a z :=
  Away.mk _ (imageCoordinate_mem a z) 1 (imageCoordinate a s)
    (by simpa using imageCoordinate_mem (R := R) a s)

@[simp]
theorem chartEvaluation_coordinate (a : σ → ι →₀ ℕ) (z s : σ) (hz : a z = 0) :
    chartEvaluation (R := R) a z hz (affineChartCoordinate a z s) =
      monomial (a s) 1 := by
  rw [affineChartCoordinate, chartEvaluation_mk, imageEvaluation_coordinate]

def imageConstant (a : σ → ι →₀ ℕ) (r : R) : monomialImage (R := R) a :=
  ⟨homogeneousMonomialMap a (C r), ⟨C r, rfl⟩⟩

theorem imageConstant_mem (a : σ → ι →₀ ℕ) (r : R) :
    imageConstant a r ∈ imageGrade a 0 :=
  homogeneousMonomialMap_homogeneous a (isHomogeneous_C σ r)

def affineChartConstant (a : σ → ι →₀ ℕ) (z : σ) (r : R) : constantChart (R := R) a z :=
  Away.mk _ (imageCoordinate_mem a z) 0 (imageConstant a r)
    (show imageConstant a r ∈ imageGrade a (0 • 1) from imageConstant_mem a r)

@[simp]
theorem chartEvaluation_constant (a : σ → ι →₀ ℕ) (z : σ) (hz : a z = 0) (r : R) :
    chartEvaluation a z hz (affineChartConstant a z r) = C r := by
  rw [affineChartConstant, chartEvaluation_mk]
  simp [imageEvaluation, imageConstant, homogeneousMonomialMap]

theorem chartEvaluation_surjective (a : σ → ι →₀ ℕ) (z : σ) (hz : a z = 0)
    (coordinate : ι → σ) (hcoordinate : ∀ i, a (coordinate i) = Finsupp.single i 1) :
    Function.Surjective (chartEvaluation (R := R) a z hz) := by
  intro p
  induction p using MvPolynomial.induction_on with
  | C r => exact ⟨affineChartConstant a z r, chartEvaluation_constant a z hz r⟩
  | add p q hp hq =>
    obtain ⟨x, rfl⟩ := hp
    obtain ⟨y, rfl⟩ := hq
    exact ⟨x + y, map_add _ _ _⟩
  | mul_X p i hp =>
    obtain ⟨x, rfl⟩ := hp
    refine ⟨x * affineChartCoordinate a z (coordinate i), ?_⟩
    rw [map_mul, chartEvaluation_coordinate, hcoordinate]
    rfl

def constantChartEquiv (a : σ → ι →₀ ℕ) (z : σ) (hz : a z = 0)
    (coordinate : ι → σ) (hcoordinate : ∀ i, a (coordinate i) = Finsupp.single i 1) :
    constantChart (R := R) a z ≃+* MvPolynomial ι R :=
  RingEquiv.ofBijective (chartEvaluation a z hz)
    ⟨chartEvaluation_injective a z hz, chartEvaluation_surjective a z hz coordinate hcoordinate⟩

def constantProjectiveChartIso (a : σ → ι →₀ ℕ) (z : σ) (hz : a z = 0)
    (coordinate : ι → σ) (hcoordinate : ∀ i, a (coordinate i) = Finsupp.single i 1) :
    (Proj.basicOpen (imageGrade (R := R) a) (imageCoordinate a z)).toScheme ≅
      Spec (CommRingCat.of (MvPolynomial ι R)) := by
  let e : CommRingCat.of (constantChart (R := R) a z) ≅
      CommRingCat.of (MvPolynomial ι R) :=
    (constantChartEquiv (R := R) a z hz coordinate hcoordinate).toCommRingCatIso
  exact Proj.basicOpenIsoSpec _ _ (imageCoordinate_mem a z) (by decide) ≪≫
    Scheme.Spec.mapIso e.symm.op

def constantChartSectionRingEquiv (a : σ → ι →₀ ℕ) (z : σ) (hz : a z = 0)
    (coordinate : ι → σ) (hcoordinate : ∀ i, a (coordinate i) = Finsupp.single i 1) :
    Γ(Proj (imageGrade (R := R) a), Proj.basicOpen (imageGrade a) (imageCoordinate a z)) ≃+*
      MvPolynomial ι R :=
  ((Proj.basicOpen (imageGrade (R := R) a) (imageCoordinate a z)).topIso.symm ≪≫
    Scheme.Γ.mapIso (constantProjectiveChartIso (R := R) a z hz coordinate hcoordinate).symm.op ≪≫
    Scheme.ΓSpecIso (CommRingCat.of (MvPolynomial ι R))).commRingCatIsoToRingEquiv

abbrev finiteMonomialClosure (S : Finset (ι →₀ ℕ)) :=
  Proj (imageGrade (R := R) (fun s : S => s.1))

def finiteMonomialChartEquiv (S : Finset (ι →₀ ℕ)) (hzero : 0 ∈ S)
    (hcoordinate : ∀ i, Finsupp.single i 1 ∈ S) :
    constantChart (R := R) (fun s : S => s.1) ⟨0, hzero⟩ ≃+* MvPolynomial ι R :=
  constantChartEquiv (R := R) (fun s : S => s.1) ⟨0, hzero⟩ rfl
    (fun i => ⟨Finsupp.single i 1, hcoordinate i⟩) (fun _ => rfl)

def finiteMonomialProjectiveChartIso (S : Finset (ι →₀ ℕ)) (hzero : 0 ∈ S)
    (hcoordinate : ∀ i, Finsupp.single i 1 ∈ S) :
    (Proj.basicOpen (imageGrade (R := R) (fun s : S => s.1))
      (imageCoordinate (fun s : S => s.1) ⟨0, hzero⟩)).toScheme ≅
      Spec (CommRingCat.of (MvPolynomial ι R)) :=
  constantProjectiveChartIso (R := R) (fun s : S => s.1) ⟨0, hzero⟩ rfl
    (fun i => ⟨Finsupp.single i 1, hcoordinate i⟩) (fun _ => rfl)

end PiExponent.WeightedCompactification

end

end OAI
end Source0339

-- Source: OAI/NumberTheory/PiExponent/Geometry/ProjectiveDenseChart.lean
section Source0340
-- Modified in this edition: unused plain lemmas removed; see reduction.json.
/-
Modification notice for the LogTwo project.
Derived from openai/math (Apache-2.0), revision adc7f1241b42e322a6451854ab7e4b4c146bf78a.
Original source: lean/OAI/NumberTheory/PiExponent/Geometry/ProjectiveDenseChart.lean
Changes: Convert module/import declarations to the Lean 4.34 public module format.
See ../THIRD_PARTY_NOTICES.txt for provenance and the recorded changes.
-/

namespace OAI

noncomputable section

namespace PiExponent

section

open AlgebraicGeometry TopologicalSpace
open scoped HomogeneousIdeal

variable {A T : Type*} [CommRing A] [IsDomain A] [SetLike T A] [AddSubgroupClass T A]
  (𝒜 : ℕ → T) [GradedRing 𝒜]

def projectiveGenericPoint {s : A} {d : ℕ} (hs : s ∈ 𝒜 d) (hd : 0 < d) (hne : s ≠ 0) :
    ProjectiveSpectrum 𝒜 where
  asHomogeneousIdeal := ⊥
  isPrime := by
    simpa only [HomogeneousIdeal.toIdeal_bot] using (inferInstance : (⊥ : Ideal A).IsPrime)
  not_irrelevant_le h := by
    have hm := h (HomogeneousIdeal.mem_irrelevant_of_mem 𝒜 hd hs)
    change s ∈ (⊥ : Ideal A) at hm
    exact hne (Ideal.mem_bot.mp hm)

end

namespace WeightedCompactification

open MvPolynomial AlgebraicGeometry

variable {R ι σ : Type*} [CommRing R] [IsDomain R]

end WeightedCompactification

end PiExponent

end

end OAI
end Source0340

-- Source: LogTwo/Geometry/IntegralProj.lean
section Source0341
/-
Modification notice for the LogTwo project.
Adapted from openai/math (Apache-2.0), revision adc7f1241b42e322a6451854ab7e4b4c146bf78a.
Changes: Extract generic graded-domain Proj lemmas into the project namespace.
See ../THIRD_PARTY_NOTICES.txt for provenance and the recorded changes.
-/

/-! Integral Proj of a graded domain with a nonempty projective spectrum.
Adapted from openai/math Ampleness/BlowupProperIntegral.lean, pinned commit,
Apache-2.0. Extracting these general lemmas avoids importing the entire blowup
construction before it is needed. See THIRD_PARTY_NOTICES.txt. -/
namespace LogTwo.Geometry.IntegralProj
noncomputable section
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

end
end LogTwo.Geometry.IntegralProj
end Source0341

-- Source: OAI/NumberTheory/PiExponent/Approximation/WeightedGeometryScale.lean
section Source0342
-- Modified in this edition: unused plain lemmas removed; see reduction.json.
/-
Modification notice for the LogTwo project.
Derived from openai/math (Apache-2.0), revision adc7f1241b42e322a6451854ab7e4b4c146bf78a.
Original source: lean/OAI/NumberTheory/PiExponent/Approximation/WeightedGeometryScale.lean
Changes: Convert module/import declarations to the Lean 4.34 public module format.
See ../THIRD_PARTY_NOTICES.txt for provenance and the recorded changes.
-/

namespace OAI

noncomputable section
open scoped BigOperators
namespace PiExponent.WeightedGeometryScale

theorem exists_power_scale {n : ℕ} (w : Fin n → ℚ) (hw : ∀ i, 0 < w i) :
    ∃ R : ℕ, 0 < R ∧ ∃ e : Fin n → ℕ,
      (∀ i, 0 < e i) ∧ ∀ i, w i * (e i : ℚ) = R := by
  obtain ⟨R,hR,e,he,heq⟩ := positive_rational_weights_common_denominator
    (fun i => (w i)⁻¹) (fun i => inv_pos.mpr (hw i))
  refine ⟨R,hR,e,he,fun i => ?_⟩
  have hi : (w i)⁻¹ = (e i : ℚ) / (R : ℚ) := by
    apply Rat.cast_injective (α := ℝ)
    simpa only [Rat.cast_inv, Rat.cast_div, Rat.cast_natCast] using heq i
  have hR' : (R : ℚ) ≠ 0 := by exact_mod_cast hR.ne'
  have hwi : w i ≠ 0 := (hw i).ne'
  have hi' := (eq_div_iff hR').mp hi
  rw [← hi']
  field_simp

theorem exists_common_scale {n : ℕ} (w v : Fin n → ℚ)
    (hw : ∀ i, 0 < w i) (hv : ∀ i, 0 < v i) :
    ∃ R : ℕ, 0 < R ∧ ∃ e t : Fin n → ℕ,
      (∀ i, 0 < e i) ∧ (∀ i, 0 < t i) ∧
      (∀ i, w i * (e i : ℚ) = R) ∧
      (∀ i, v i * (t i : ℚ) = R) := by
  obtain ⟨A,hA,e,he,heq⟩ := exists_power_scale w hw
  obtain ⟨B,hB,t,ht,htq⟩ := exists_power_scale v hv
  refine ⟨A*B,Nat.mul_pos hA hB,fun i => e i * B,fun i => t i * A,
    fun i => Nat.mul_pos (he i) hB,fun i => Nat.mul_pos (ht i) hA,?_,?_⟩
  · intro i
    push_cast
    rw [← mul_assoc, heq]
  · intro i
    push_cast
    rw [← mul_assoc, htq, mul_comm]

def monomials {n : ℕ} (w : Fin n → ℚ) (R : ℚ) : Finset (Fin n →₀ ℕ) :=
  (realWeightedSimplex (fun i => (w i : ℝ)) (R : ℝ)).image Finsupp.equivFunOnFinite.symm

@[simp] theorem mem_monomials {n : ℕ} (w : Fin n → ℚ) (hw : ∀ i, 0 < w i)
    (R : ℚ) (a : Fin n →₀ ℕ) :
    a ∈ monomials w R ↔ (∑ i, w i * (a i : ℚ)) ≤ R := by
  classical
  rw [monomials, Finset.mem_image]
  constructor
  · rintro ⟨b,hb,rfl⟩
    have h := (mem_realWeightedSimplex (fun i => by exact_mod_cast hw i)).mp hb
    exact_mod_cast h
  · intro ha
    refine ⟨fun i => a i,?_,Finsupp.equivFunOnFinite_symm_coe a⟩
    apply (mem_realWeightedSimplex (fun i => by exact_mod_cast hw i)).mpr
    exact_mod_cast ha

theorem zero_mem_monomials {n : ℕ} (w : Fin n → ℚ) (hw : ∀ i, 0 < w i)
    (R : ℚ) (hR : 0 ≤ R) : (0 : Fin n →₀ ℕ) ∈ monomials w R := by
  rw [mem_monomials w hw]
  simpa using hR

theorem pure_mem_monomials {n : ℕ} (w : Fin n → ℚ) (hw : ∀ i, 0 < w i)
    (R : ℚ) (e : Fin n → ℕ) (he : ∀ i, w i * (e i : ℚ) = R) (i : Fin n) :
    Finsupp.single i (e i) ∈ monomials w R := by
  classical
  rw [mem_monomials w hw]
  simpa [Finsupp.single_apply] using (he i).le

theorem coordinate_mem_monomials {n : ℕ} (w : Fin n → ℚ) (hw : ∀ i, 0 < w i)
    (R : ℚ) (e : Fin n → ℕ) (hepos : ∀ i, 0 < e i)
    (he : ∀ i, w i * (e i : ℚ) = R) (i : Fin n) :
    Finsupp.single i 1 ∈ monomials w R := by
  classical
  rw [mem_monomials w hw]
  have hi : (1 : ℚ) ≤ e i := by exact_mod_cast hepos i
  have h := mul_le_mul_of_nonneg_left hi (hw i).le
  simpa [Finsupp.single_apply, he] using h

structure Scale {n : ℕ} (w v : Fin n → ℚ) where
  radius : ℕ
  radius_pos : 0 < radius
  degreePowers : Fin n → ℕ
  jetPowers : Fin n → ℕ
  degreePowers_pos : ∀ i, 0 < degreePowers i
  jetPowers_pos : ∀ i, 0 < jetPowers i
  degreePowers_eq : ∀ i, w i * (degreePowers i : ℚ) = radius
  jetPowers_eq : ∀ i, v i * (jetPowers i : ℚ) = radius

def chooseScale {n : ℕ} (w v : Fin n → ℚ)
    (hw : ∀ i, 0 < w i) (hv : ∀ i, 0 < v i) : Scale w v := by
  apply Classical.choice
  obtain ⟨R,hR,e,t,he,ht,heq,htq⟩ := exists_common_scale w v hw hv
  exact ⟨⟨R,hR,e,t,he,ht,heq,htq⟩⟩

namespace Scale
variable {n : ℕ} {w v : Fin n → ℚ} (s : Scale w v)

abbrev Index := ↥(monomials w s.radius)

def exponents (i : s.Index) : Fin n →₀ ℕ := i.val

def constantIndex (hw : ∀ i, 0 < w i) : s.Index :=
  ⟨0,zero_mem_monomials w hw s.radius (by exact_mod_cast s.radius_pos.le)⟩

def coordinateIndex (hw : ∀ i, 0 < w i) (i : Fin n) : s.Index :=
  ⟨Finsupp.single i 1,coordinate_mem_monomials w hw s.radius s.degreePowers
    s.degreePowers_pos s.degreePowers_eq i⟩

def pureIndex (hw : ∀ i, 0 < w i) (i : Fin n) : s.Index :=
  ⟨Finsupp.single i (s.degreePowers i),pure_mem_monomials w hw s.radius
    s.degreePowers s.degreePowers_eq i⟩

@[simp] theorem exponents_constant (hw : ∀ i, 0 < w i) :
    s.exponents (s.constantIndex hw) = 0 := rfl

@[simp] theorem exponents_coordinate (hw : ∀ i, 0 < w i) (i : Fin n) :
    s.exponents (s.coordinateIndex hw i) = Finsupp.single i 1 := rfl

@[simp] theorem exponents_pure (hw : ∀ i, 0 < w i) (i : Fin n) :
    s.exponents (s.pureIndex hw i) = Finsupp.single i (s.degreePowers i) := rfl

theorem budget (hw : ∀ i, 0 < w i) (i : s.Index) :
    (∑ j, w j * (s.exponents i j : ℚ)) ≤ s.radius :=
  (mem_monomials w hw s.radius i.val).mp i.property

end Scale

end PiExponent.WeightedGeometryScale

end

end OAI
end Source0342

-- Source: OAI/NumberTheory/PiExponent/Polynomials/SurjectiveGradedMap.lean
section Source0343
/-
Modification notice for the LogTwo project.
Derived from openai/math (Apache-2.0), revision adc7f1241b42e322a6451854ab7e4b4c146bf78a.
Original source: lean/OAI/NumberTheory/PiExponent/Polynomials/SurjectiveGradedMap.lean
Changes: Convert module/import declarations to the Lean 4.34 public module format.
See ../THIRD_PARTY_NOTICES.txt for provenance and the recorded changes.
-/

namespace OAI

noncomputable section

namespace PiExponent

open DirectSum HomogeneousLocalization
open scoped HomogeneousIdeal

variable {A B S T : Type*} [CommRing A] [CommRing B]
  [SetLike S A] [AddSubgroupClass S A] [SetLike T B] [AddSubgroupClass T B]
  {𝒜 : ℕ → S} {ℬ : ℕ → T} [GradedRing 𝒜] [GradedRing ℬ]

theorem gradedMap_homogeneous_lift (f : 𝒜 →+*ᵍ ℬ) (hf : Function.Surjective f)
    {n : ℕ} {y : B} (hy : y ∈ ℬ n) : ∃ x, x ∈ 𝒜 n ∧ f x = y := by
  obtain ⟨x, hx⟩ := hf y
  refine ⟨decompose 𝒜 x n, (decompose 𝒜 x n).2, ?_⟩
  rw [f.map_directSumDecompose, hx]
  exact decompose_of_mem_same ℬ hy

theorem gradedMap_irrelevant_le_map (f : 𝒜 →+*ᵍ ℬ) (hf : Function.Surjective f) :
    ℬ₊ ≤ 𝒜₊.map f := by
  rw [HomogeneousIdeal.irrelevant_le]
  intro n hn y hy
  obtain ⟨x, hx, rfl⟩ := gradedMap_homogeneous_lift f hf hy
  exact Ideal.mem_map_of_mem f (HomogeneousIdeal.mem_irrelevant_of_mem 𝒜 hn hx)

theorem homogeneousAway_map_surjective (f : 𝒜 →+*ᵍ ℬ) (hf : Function.Surjective f)
    {s : A} {d : ℕ} (hs : s ∈ 𝒜 d) : Function.Surjective (Away.map f s) := by
  intro x
  obtain ⟨n, y, hy, rfl⟩ := Away.mk_surjective _ (f.map_mem hs) x
  obtain ⟨p, hp, rfl⟩ := gradedMap_homogeneous_lift f hf hy
  exact ⟨Away.mk _ hs n p hp, Away.map_mk f s hs n p hp⟩

end PiExponent

end

end OAI
end Source0343

-- Source: OAI/NumberTheory/PiExponent/Approximation/WeightedCompactificationImmersion.lean
section Source0344
/-
Modification notice for the LogTwo project.
Derived from openai/math (Apache-2.0), revision adc7f1241b42e322a6451854ab7e4b4c146bf78a.
Original source: lean/OAI/NumberTheory/PiExponent/Approximation/WeightedCompactificationImmersion.lean
Changes: Convert module/import declarations to the Lean 4.34 public module format.
See ../THIRD_PARTY_NOTICES.txt for provenance and the recorded changes.
-/

namespace OAI

noncomputable section

namespace PiExponent.WeightedCompactification

open MvPolynomial HomogeneousLocalization
open PiExponentSeshadri.Projective
open AlgebraicGeometry CategoryTheory
open scoped HomogeneousIdeal

universe u
variable {R ι σ : Type u} [CommRing R]

attribute [local instance] MvPolynomial.gradedAlgebra

abbrev projectiveMonomialMap (a : σ → ι →₀ ℕ) :
    Proj (imageGrade (R := R) a) ⟶ Proj (homogeneousSubmodule σ R) :=
  Proj.map (gradedImageMap a) (gradedMap_irrelevant_le_map _ (gradedImageMap_surjective a))

@[simp]
theorem projectiveMonomialMap_preimage (a : σ → ι →₀ ℕ) (s : σ) :
    projectiveMonomialMap (R := R) a ⁻¹ᵁ Proj.basicOpen (homogeneousSubmodule σ R) (X s) =
      Proj.basicOpen (imageGrade a) (imageCoordinate a s) := rfl

theorem projectiveMonomialMap_restrict (a : σ → ι →₀ ℕ) (s : σ) :
    projectiveMonomialMap (R := R) a ∣_ Proj.basicOpen (homogeneousSubmodule σ R) (X s) =
      (Proj.basicOpenIsoSpec (imageGrade (R := R) a) ((gradedImageMap a) (X s))
        ((gradedImageMap a).map_mem (isHomogeneous_X R s)) (by decide)).hom ≫
        Spec.map (CommRingCat.ofHom (Away.map (gradedImageMap (R := R) a) (X s))) ≫
          (Proj.basicOpenIsoSpec _ _ (isHomogeneous_X R s) (by decide)).inv := by
  let e := Proj.basicOpenIsoSpec (imageGrade (R := R) a) ((gradedImageMap a) (X s))
    ((gradedImageMap a).map_mem (isHomogeneous_X R s)) (by decide)
  apply (cancel_epi e.inv).1
  apply (cancel_mono (Proj.basicOpen (homogeneousSubmodule σ R) (X s)).ι).1
  have h := Proj.awayι_comp_map (gradedImageMap (R := R) a)
    (gradedMap_irrelevant_le_map _ (gradedImageMap_surjective a))
    (by decide : 0 < (1 : ℕ)) (X s) (isHomogeneous_X R s)
  simp only [Category.assoc, e, Iso.inv_hom_id_assoc]
  erw [Category.assoc, morphismRestrict_ι]
  simpa only [Proj.awayι, Category.assoc, projectiveMonomialMap,
    Proj.map_preimage_basicOpen] using h

instance projectiveMonomialMap_isClosedImmersion (a : σ → ι →₀ ℕ) :
    IsClosedImmersion (projectiveMonomialMap (R := R) a) := by
  apply IsZariskiLocalAtTarget.of_iSup_eq_top
    (fun s : σ => Proj.basicOpen (homogeneousSubmodule σ R) (X s)) (standardChart_cover)
  intro s
  rw [projectiveMonomialMap_restrict]
  have : IsClosedImmersion
      (Spec.map (CommRingCat.ofHom (Away.map (gradedImageMap (R := R) a) (X s)))) :=
    IsClosedImmersion.spec_of_surjective _
      (homogeneousAway_map_surjective (gradedImageMap a) (gradedImageMap_surjective a)
        (isHomogeneous_X R s))
  let eB := Proj.basicOpenIsoSpec (imageGrade (R := R) a) ((gradedImageMap a) (X s))
    ((gradedImageMap a).map_mem (isHomogeneous_X R s)) (by decide)
  let eA := Proj.basicOpenIsoSpec (homogeneousSubmodule σ R) (X s)
    (isHomogeneous_X R s) (by decide)
  change IsClosedImmersion (eB.hom ≫ _ ≫ eA.inv)
  have : IsClosedImmersion eB.hom := inferInstance
  have : IsClosedImmersion eA.inv := inferInstance
  exact IsClosedImmersion.comp _ _

end PiExponent.WeightedCompactification

end

end OAI
end Source0344

-- Source: OAI/NumberTheory/PiExponent/Geometry/PolynomialProjectiveStructure.lean
section Source0345
/-
Modification notice for the LogTwo project.
Derived from openai/math (Apache-2.0), revision adc7f1241b42e322a6451854ab7e4b4c146bf78a.
Original source: lean/OAI/NumberTheory/PiExponent/Geometry/PolynomialProjectiveStructure.lean
Changes: Convert module/import declarations to the Lean 4.34 public module format.
See ../THIRD_PARTY_NOTICES.txt for provenance and the recorded changes.
-/

namespace OAI

noncomputable section

namespace PiExponent

open MvPolynomial AlgebraicGeometry CategoryTheory

universe u
variable (R σ : Type u) [CommRing R]

attribute [local instance] MvPolynomial.gradedAlgebra

def polynomialGradeZeroEquiv : R ≃+* homogeneousSubmodule σ R 0 :=
  RingEquiv.ofBijective (algebraMap R (homogeneousSubmodule σ R 0)) (by
    constructor
    · intro a b h
      apply MvPolynomial.C_injective
      exact congrArg (fun x : homogeneousSubmodule σ R 0 => (x : MvPolynomial σ R)) h
    · intro p
      refine ⟨p.1.coeff 0, ?_⟩
      apply Subtype.ext
      exact (MvPolynomial.totalDegree_eq_zero_iff_eq_C.mp
        ((MvPolynomial.totalDegree_zero_iff_isHomogeneous σ).mpr p.2)).symm)

def polynomialProjectiveProjection : Proj (homogeneousSubmodule σ R) ⟶ Spec (CommRingCat.of R) :=
  Proj.toSpecZero (homogeneousSubmodule σ R) ≫
    Spec.map (CommRingCat.ofHom (polynomialGradeZeroEquiv R σ).toRingHom)

instance : IsScalarTower R (homogeneousSubmodule σ R 0) (MvPolynomial σ R) :=
  IsScalarTower.of_algebraMap_eq (R := R) (S := homogeneousSubmodule σ R 0)
    (A := MvPolynomial σ R) (fun _ => rfl)

instance [Finite σ] : Algebra.FiniteType (homogeneousSubmodule σ R 0) (MvPolynomial σ R) :=
  Algebra.FiniteType.of_restrictScalars_finiteType R
    (homogeneousSubmodule σ R 0) (MvPolynomial σ R)

instance polynomialProjectiveProjection_proper [Finite σ] :
    IsProper (polynomialProjectiveProjection R σ) := by
  have : IsProper (Proj.toSpecZero (homogeneousSubmodule σ R)) := inferInstance
  have : IsIso (Spec.map (CommRingCat.ofHom (polynomialGradeZeroEquiv R σ).toRingHom)) := by
    change IsIso (Spec.map (polynomialGradeZeroEquiv R σ).toCommRingCatIso.hom)
    infer_instance
  exact MorphismProperty.comp_mem (@IsProper) _ _ inferInstance inferInstance

end PiExponent

end

end OAI
end Source0345

-- Source: OAI/NumberTheory/PiExponent/Geometry/WeightedProjectiveStructure.lean
section Source0346
-- Modified in this edition: unused plain lemmas removed; see reduction.json.
/-
Modification notice for the LogTwo project.
Derived from openai/math (Apache-2.0), revision adc7f1241b42e322a6451854ab7e4b4c146bf78a.
Original source: lean/OAI/NumberTheory/PiExponent/Geometry/WeightedProjectiveStructure.lean
Changes: Convert module/import declarations to the Lean 4.34 public module format.
See ../THIRD_PARTY_NOTICES.txt for provenance and the recorded changes.
-/

namespace OAI

noncomputable section

namespace PiExponent.WeightedCompactification

open MvPolynomial AlgebraicGeometry CategoryTheory

universe u
variable {R ι σ : Type u} [CommRing R]

attribute [local instance] MvPolynomial.gradedAlgebra

def projection (a : σ → ι →₀ ℕ) :
    Proj (imageGrade (R := R) a) ⟶ Spec (CommRingCat.of R) :=
  projectiveMonomialMap a ≫ polynomialProjectiveProjection R σ

instance projection_proper [Finite σ] (a : σ → ι →₀ ℕ) :
    IsProper (projection (R := R) a) := by
  have : IsProper (projectiveMonomialMap (R := R) a) := inferInstance
  exact MorphismProperty.comp_mem (@IsProper) _ _ inferInstance inferInstance

end PiExponent.WeightedCompactification

end

end OAI
end Source0346

-- Source: OAI/NumberTheory/PiExponent/Approximation/WeightedCompactificationGeometry.lean
section Source0347
-- Modified in this edition: unused plain lemmas removed; see reduction.json.
/-
Modification notice for the LogTwo project.
Derived from openai/math (Apache-2.0), revision adc7f1241b42e322a6451854ab7e4b4c146bf78a.
Original source: lean/OAI/NumberTheory/PiExponent/Approximation/WeightedCompactificationGeometry.lean
Changes: Convert module/import declarations to the Lean 4.34 public module format.
See ../THIRD_PARTY_NOTICES.txt for provenance and the recorded changes.
-/

namespace OAI

noncomputable section

namespace PiExponent.WeightedCompactification

open MvPolynomial AlgebraicGeometry CategoryTheory Topology

universe u
variable {R ι σ : Type u} [CommRing R]

def affineChartMap (a : σ → ι →₀ ℕ) (z : σ) (hz : a z = 0)
    (coordinate : ι → σ) (hcoordinate : ∀ i, a (coordinate i) = Finsupp.single i 1) :
    Spec (CommRingCat.of (MvPolynomial ι R)) ⟶ Proj (imageGrade (R := R) a) :=
  (constantProjectiveChartIso (R := R) a z hz coordinate hcoordinate).inv ≫
    (Proj.basicOpen (imageGrade a) (imageCoordinate a z)).ι

instance affineChartMap_isOpenImmersion (a : σ → ι →₀ ℕ) (z : σ) (hz : a z = 0)
    (coordinate : ι → σ) (hcoordinate : ∀ i, a (coordinate i) = Finsupp.single i 1) :
    IsOpenImmersion (affineChartMap (R := R) a z hz coordinate hcoordinate) := by
  let e := constantProjectiveChartIso (R := R) a z hz coordinate hcoordinate
  have : IsOpenImmersion e.inv := inferInstance
  exact IsOpenImmersion.comp _ _

theorem affineChartMap_range (a : σ → ι →₀ ℕ) (z : σ) (hz : a z = 0)
    (coordinate : ι → σ) (hcoordinate : ∀ i, a (coordinate i) = Finsupp.single i 1) :
    Set.range (affineChartMap (R := R) a z hz coordinate hcoordinate) =
      (Proj.basicOpen (imageGrade (R := R) a) (imageCoordinate a z) : Set (Proj (imageGrade (R := R) a))) := by
  let e := constantProjectiveChartIso (R := R) a z hz coordinate hcoordinate
  ext x
  constructor
  · rintro ⟨y, rfl⟩
    exact (e.inv y).2
  · intro hx
    refine ⟨e.hom ⟨x, hx⟩, ?_⟩
    change ((e.hom ≫ e.inv) ⟨x, hx⟩).1 = x
    simp only [Iso.hom_inv_id]
    rfl

end PiExponent.WeightedCompactification

end

end OAI
end Source0347

-- Source: OAI/NumberTheory/PiExponent/Approximation/WeightedAffineParametrization.lean
section Source0348
-- Modified in this edition: unused plain lemmas removed; see reduction.json.
/-
Modification notice for the LogTwo project.
Derived from openai/math (Apache-2.0), revision adc7f1241b42e322a6451854ab7e4b4c146bf78a.
Original source: lean/OAI/NumberTheory/PiExponent/Approximation/WeightedAffineParametrization.lean
Changes: Convert module/import declarations to the Lean 4.34 public module format.
See ../THIRD_PARTY_NOTICES.txt for provenance and the recorded changes.
-/

namespace OAI

noncomputable section

namespace PiExponent.WeightedCompactification

open AlgebraicGeometry CategoryTheory MvPolynomial HomogeneousLocalization
open PiExponentSeshadri.Projective

universe u
variable {R ι σ : Type u} [CommRing R]
attribute [local instance] MvPolynomial.gradedAlgebra

theorem imageEvaluation_gradedImageMap (a : σ → ι →₀ ℕ) (p : MvPolynomial σ R) :
    imageEvaluation (R := R) a (gradedImageMap (R := R) a p) = affineMonomialMap (R := R) a p := by
  have h : (imageEvaluation (R := R) a).comp (gradedImageMap (R := R) a).toRingHom =
      affineMonomialMap (R := R) a := by
    apply MvPolynomial.ringHom_ext
    · intro r
      simp only [RingHom.comp_apply, affineMonomialMap, eval₂Hom_C]
      change (eval₂Hom (RingHom.id (MvPolynomial ι R)) (fun _ : Unit => 1))
        (homogeneousMonomialMap a (C r)) = C r
      simp [homogeneousMonomialMap]
    · intro s
      simp only [RingHom.comp_apply, affineMonomialMap, eval₂Hom_X']
      change imageEvaluation (R := R) a (imageCoordinate (R := R) a s) = monomial (a s) 1
      exact imageEvaluation_coordinate a s
  exact RingHom.congr_fun h p

theorem chartEvaluation_comp_awayMap (a : σ → ι →₀ ℕ) (z : σ) (hz : a z = 0) :
    (chartEvaluation (R := R) a z hz).comp (Away.map (gradedImageMap (R := R) a) (X z)) =
      evalAway (affineMonomialMap (R := R) a) (X z)
        (by simp [affineMonomialMap, hz]) := by
  apply RingHom.ext
  intro q
  obtain ⟨n,p,hp,rfl⟩ := Away.mk_surjective (PolyGrade R σ) (poly_X_mem z) q
  change chartEvaluation (R := R) a z hz
    (Away.map (gradedImageMap (R := R) a) (X z) (Away.mk _ (poly_X_mem z) n p hp)) = _
  rw [Away.map_mk (gradedImageMap (R := R) a) (X z) (poly_X_mem z) n p hp]
  erw [chartEvaluation_mk]
  rw [imageEvaluation_gradedImageMap]
  have h := evalAway_mk_clear (affineMonomialMap (R := R) a) (poly_X_mem z)
    (show IsUnit (affineMonomialMap (R := R) a (X z)) from by
      simp [affineMonomialMap, hz]) n p hp
  simpa [affineMonomialMap, hz] using h.symm

theorem affineChartMap_comp_projectiveMonomialMap
    (a : σ → ι →₀ ℕ) (z : σ) (hz : a z = 0)
    (coordinate : ι → σ) (hcoordinate : ∀ i, a (coordinate i) = Finsupp.single i 1) :
    affineChartMap (R := R) a z hz coordinate hcoordinate ≫ projectiveMonomialMap a =
      fromUnitCoordinate (affineMonomialMap (R := R) a) (by decide) (poly_X_mem z)
        (by simp [affineMonomialMap, hz]) := by
  have hchart : affineChartMap (R := R) a z hz coordinate hcoordinate =
      Spec.map (CommRingCat.ofHom (chartEvaluation (R := R) a z hz)) ≫
        Proj.awayι (imageGrade (R := R) a) (imageCoordinate (R := R) a z) (imageCoordinate_mem a z) (by decide) := by
    rfl
  rw [hchart, Category.assoc]
  have hmap := Proj.awayι_comp_map (gradedImageMap (R := R) a)
    (gradedMap_irrelevant_le_map _ (gradedImageMap_surjective a))
    (by decide : 0 < (1 : ℕ)) (X z) (poly_X_mem z)
  change Spec.map (CommRingCat.ofHom (chartEvaluation (R := R) a z hz)) ≫
    (Proj.awayι (imageGrade (R := R) a) ((gradedImageMap (R := R) a) (X z))
      ((gradedImageMap (R := R) a).map_mem (poly_X_mem z)) (by decide) ≫
        Proj.map (gradedImageMap (R := R) a) _) = _
  erw [hmap]
  erw [← Category.assoc, ← Spec.map_comp, ← CommRingCat.ofHom_comp,
    chartEvaluation_comp_awayMap]
  rfl

end PiExponent.WeightedCompactification

end

end OAI
end Source0348

-- Source: OAI/NumberTheory/PiExponent/Geometry/CurveNormalizationModel.lean
section Source0349
/-
Modification notice for the LogTwo project.
Derived from openai/math (Apache-2.0), revision adc7f1241b42e322a6451854ab7e4b4c146bf78a.
Original source: lean/OAI/NumberTheory/PiExponent/Geometry/CurveNormalizationModel.lean
Changes: Convert module/import declarations to the Lean 4.34 public module format.
See ../THIRD_PARTY_NOTICES.txt for provenance and the recorded changes.
-/

namespace OAI

noncomputable section

namespace PiExponent.CurveNormalizationModel

open scoped Polynomial
open AlgebraicGeometry CategoryTheory
open PiExponent.CurveZeroPole

def integralClosureTowerHom
    {R S E : Type*} [CommRing R] [CommRing S] [CommRing E]
    [Algebra R S] [Algebra R E] [Algebra S E] [IsScalarTower R S E] :
    integralClosure R E →+* integralClosure S E where
  toFun x := ⟨x.1, x.2.tower_top⟩
  map_zero' := rfl
  map_one' := rfl
  map_add' _ _ := rfl
  map_mul' _ _ := rfl

theorem integralClosureTower_isLocalizationAway
    {R S E : Type*} [CommRing R] [CommRing S] [CommRing E]
    [Algebra R S] [Algebra R E] [Algebra S E] [IsScalarTower R S E]
    (r : R) [IsLocalization.Away r S]
    [IsLocalization.Away (algebraMap R E r) E] :
    letI : Algebra (integralClosure R E) (integralClosure S E) :=
      integralClosureTowerHom.toAlgebra
    IsLocalization.Away (algebraMap R (integralClosure R E) r) (integralClosure S E) := by
  let : Algebra (integralClosure R E) (integralClosure S E) :=
    integralClosureTowerHom.toAlgebra
  have : IsScalarTower (integralClosure R E) (integralClosure S E) E :=
    IsScalarTower.of_algebraMap_eq' rfl
  have : IsScalarTower R (integralClosure R E) (integralClosure S E) :=
    IsScalarTower.of_algebraMap_eq fun _ => rfl
  exact IsLocalization.Away.integralClosure (S := E) (Rf := S) (Sf := E) r

theorem integralClosureTower_SpecMap_isOpenImmersion
    {R S E : Type*} [CommRing R] [CommRing S] [CommRing E]
    [Algebra R S] [Algebra R E] [Algebra S E] [IsScalarTower R S E]
    (r : R) [IsLocalization.Away r S]
    [IsLocalization.Away (algebraMap R E r) E] :
    IsOpenImmersion (Spec.map (CommRingCat.ofHom
      (integralClosureTowerHom (R := R) (S := S) (E := E)))) := by
  let : Algebra (integralClosure R E) (integralClosure S E) :=
    integralClosureTowerHom.toAlgebra
  have : IsLocalization.Away (algebraMap R (integralClosure R E) r) (integralClosure S E) :=
    integralClosureTower_isLocalizationAway r
  exact IsOpenImmersion.of_isLocalization (algebraMap R (integralClosure R E) r)

def parameterLaurentMap {F E : Type*} [Field F] [Field E] [Algebra F E]
    (f : E) (hf : Transcendental F f) : LaurentPolynomial F →+* E :=
  LaurentPolynomial.eval₂ (algebraMap F E) (Units.mk0 f hf.ne_zero)

abbrev parameterLaurentAlgebra {F E : Type*} [Field F] [Field E] [Algebra F E]
    (f : E) (hf : Transcendental F f) : Algebra (LaurentPolynomial F) E :=
  (parameterLaurentMap f hf).toAlgebra

@[simp]
theorem parameterLaurentMap_T {F E : Type*} [Field F] [Field E] [Algebra F E]
    (f : E) (hf : Transcendental F f) :
    parameterLaurentMap f hf (LaurentPolynomial.T 1) = f := by
  simp [parameterLaurentMap, LaurentPolynomial.eval₂_T]

@[simp]
theorem parameterLaurentMap_T_inv {F E : Type*} [Field F] [Field E] [Algebra F E]
    (f : E) (hf : Transcendental F f) :
    parameterLaurentMap f hf (LaurentPolynomial.T (-1)) = f⁻¹ := by
  simp [parameterLaurentMap, LaurentPolynomial.eval₂_T]

theorem parameterLaurent_scalarTower {F E : Type*} [Field F] [Field E] [Algebra F E]
    (f : E) (hf : Transcendental F f) :
    letI := parameterPolynomialAlgebra f hf
    letI := parameterLaurentAlgebra f hf
    IsScalarTower F[X] (LaurentPolynomial F) E := by
  let := parameterPolynomialAlgebra f hf
  let := parameterLaurentAlgebra f hf
  apply IsScalarTower.of_algebraMap_eq
  intro p
  rw [parameterPolynomialAlgebra_map]
  change Polynomial.aeval f p = parameterLaurentMap f hf (Polynomial.toLaurent p)
  rw [parameterLaurentMap, LaurentPolynomial.eval₂_toLaurent]
  rfl

abbrev parameterLaurentChart {F E : Type*} [Field F] [Field E] [Algebra F E]
    (f : E) (hf : Transcendental F f) : Type _ :=
  let := parameterLaurentAlgebra f hf
  integralClosure (LaurentPolynomial F) E

def parameterChartOverlapHom {F E : Type*} [Field F] [Field E] [Algebra F E]
    (f : E) (hf : Transcendental F f) :
    parameterChart f hf →+* parameterLaurentChart f hf := by
  let := parameterPolynomialAlgebra f hf
  let := parameterLaurentAlgebra f hf
  let := parameterLaurent_scalarTower f hf
  exact integralClosureTowerHom

theorem parameterChartOverlap_isOpenImmersion
    {F E : Type*} [Field F] [Field E] [Algebra F E]
    (f : E) (hf : Transcendental F f) :
    IsOpenImmersion (Spec.map (CommRingCat.ofHom (parameterChartOverlapHom f hf))) := by
  let := parameterPolynomialAlgebra f hf
  let := parameterLaurentAlgebra f hf
  let := parameterLaurent_scalarTower f hf
  have hunit : IsLocalization.Away f E := IsLocalization.of_le_isUnit (by
    rintro x ⟨n, rfl⟩
    exact (isUnit_iff_ne_zero.mpr hf.ne_zero).pow n)
  have hX : algebraMap F[X] E Polynomial.X = f := by
    rw [parameterPolynomialAlgebra_map]
    simp
  have : IsLocalization.Away (algebraMap F[X] E Polynomial.X) E := by
    simpa only [hX] using hunit
  exact integralClosureTower_SpecMap_isOpenImmersion (S := LaurentPolynomial F) (E := E)
    (Polynomial.X : F[X])

theorem parameterLaurentMap_invert
    {F E : Type*} [Field F] [Field E] [Algebra F E]
    (f : E) (hf : Transcendental F f) :
    (parameterLaurentMap f hf).comp (LaurentPolynomial.invert (R := F)).toRingHom =
      parameterLaurentMap f⁻¹ (transcendental_inverse f hf) := by
  apply IsLocalization.ringHom_ext (Submonoid.powers (Polynomial.X : F[X]))
  apply Polynomial.ringHom_ext
  · intro c
    simp [RingHom.comp_apply, LaurentPolynomial.algebraMap_eq_toLaurent,
      parameterLaurentMap, LaurentPolynomial.eval₂_C]
  · simp [RingHom.comp_apply, LaurentPolynomial.algebraMap_eq_toLaurent]

theorem isIntegralElem_comp_equiv
    {R S E : Type*} [CommRing R] [CommRing S] [CommRing E]
    (g : S →+* E) (e : R ≃+* S) (x : E) :
    (g.comp e.toRingHom).IsIntegralElem x ↔ g.IsIntegralElem x := by
  constructor
  · exact RingHom.isIntegralElem.of_comp e.toRingHom g
  · intro hx
    apply RingHom.isIntegralElem.of_comp e.symm.toRingHom (g.comp e.toRingHom)
    have heq : (g.comp e.toRingHom).comp e.symm.toRingHom = g := by ext; simp
    rwa [heq]

def reciprocalLaurentChartEquiv
    {F E : Type*} [Field F] [Field E] [Algebra F E]
    (f : E) (hf : Transcendental F f) :
    parameterLaurentChart f hf ≃+*
      parameterLaurentChart f⁻¹ (transcendental_inverse f hf) where
  toFun x := ⟨x.1, by
    have hx := (isIntegralElem_comp_equiv (parameterLaurentMap f hf)
      (LaurentPolynomial.invert (R := F)).toRingEquiv x.1).mpr x.2
    rw [parameterLaurentMap_invert] at hx
    exact hx⟩
  invFun x := ⟨x.1, by
    apply (isIntegralElem_comp_equiv (parameterLaurentMap f hf)
      (LaurentPolynomial.invert (R := F)).toRingEquiv x.1).mp
    rw [parameterLaurentMap_invert]
    exact x.2⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_mul' _ _ := rfl

variable {F E : Type*} [Field F] [Field E] [Algebra F E]
variable (f : E) (hf : Transcendental F f)

def zeroOverlap : Spec (.of (parameterLaurentChart f hf)) ⟶ Spec (.of (parameterChart f hf)) :=
  Spec.map (CommRingCat.ofHom (parameterChartOverlapHom f hf))

instance zeroOverlap_isOpenImmersion : IsOpenImmersion (zeroOverlap f hf) :=
  parameterChartOverlap_isOpenImmersion f hf

def infinityOverlap : Spec (.of (parameterLaurentChart f hf)) ⟶
    Spec (.of (parameterChart f⁻¹ (transcendental_inverse f hf))) :=
  Spec.map (CommRingCat.ofHom ((reciprocalLaurentChartEquiv f hf).symm.toRingHom.comp
    (parameterChartOverlapHom f⁻¹ (transcendental_inverse f hf))))

instance infinityOverlap_isOpenImmersion : IsOpenImmersion (infinityOverlap f hf) := by
  let e := (reciprocalLaurentChartEquiv f hf).symm
  have : IsIso (CommRingCat.ofHom e.toRingHom) :=
    inferInstanceAs (IsIso e.toCommRingCatIso.hom)
  have : IsOpenImmersion
      (Spec.map (CommRingCat.ofHom (parameterChartOverlapHom f⁻¹ (transcendental_inverse f hf)))) :=
    parameterChartOverlap_isOpenImmersion f⁻¹ (transcendental_inverse f hf)
  change IsOpenImmersion (Spec.map (CommRingCat.ofHom
    (e.toRingHom.comp (parameterChartOverlapHom f⁻¹ (transcendental_inverse f hf)))))
  rw [CommRingCat.ofHom_comp, Spec.map_comp]
  infer_instance

def parameterCurve : Scheme :=
  Limits.pushout (zeroOverlap f hf) (infinityOverlap f hf)

def zeroChartInclusion : Spec (.of (parameterChart f hf)) ⟶ parameterCurve f hf :=
  Limits.pushout.inl (zeroOverlap f hf) (infinityOverlap f hf)

def infinityChartInclusion : Spec (.of (parameterChart f⁻¹ (transcendental_inverse f hf))) ⟶
    parameterCurve f hf :=
  Limits.pushout.inr (zeroOverlap f hf) (infinityOverlap f hf)

instance zeroChartInclusion_isOpenImmersion : IsOpenImmersion (zeroChartInclusion f hf) :=
  inferInstanceAs (IsOpenImmersion (Limits.colimit.ι
    (Limits.span (zeroOverlap f hf) (infinityOverlap f hf)) Limits.WalkingSpan.left))

instance infinityChartInclusion_isOpenImmersion : IsOpenImmersion (infinityChartInclusion f hf) :=
  inferInstanceAs (IsOpenImmersion (Limits.colimit.ι
    (Limits.span (zeroOverlap f hf) (infinityOverlap f hf)) Limits.WalkingSpan.right))

theorem parameterCurve_overlap_compatibility :
    zeroOverlap f hf ≫ zeroChartInclusion f hf =
      infinityOverlap f hf ≫ infinityChartInclusion f hf :=
  Limits.pushout.condition

theorem parameterCurve_twoChartCover (x : parameterCurve f hf) :
    (∃ y, zeroChartInclusion f hf y = x) ∨
      ∃ y, infinityChartInclusion f hf y = x := by
  obtain ⟨j, y, hy⟩ := Scheme.IsLocallyDirected.ι_jointly_surjective
    (Limits.span (zeroOverlap f hf) (infinityOverlap f hf)) x
  cases j with
  | none =>
    left
    refine ⟨zeroOverlap f hf y, ?_⟩
    have hh := congrArg (fun g => g y)
      (Limits.colimit.w (Limits.span (zeroOverlap f hf) (infinityOverlap f hf))
        Limits.WalkingSpan.Hom.fst)
    exact hh.trans hy
  | some j =>
    cases j with
    | left => exact Or.inl ⟨y, hy⟩
    | right => exact Or.inr ⟨y, hy⟩

def zeroChartStalkIso (x : PrimeSpectrum (parameterChart f hf)) :
    (parameterCurve f hf).presheaf.stalk (zeroChartInclusion f hf x) ≅
      CommRingCat.of (Localization.AtPrime x.asIdeal) := by
  have : IsIso ((zeroChartInclusion f hf).stalkMap x) :=
    (IsOpenImmersion.iff_isIso_stalkMap.mp (zeroChartInclusion_isOpenImmersion f hf)).2 x
  exact asIso ((zeroChartInclusion f hf).stalkMap x) ≪≫
    Spec.stalkIso (.of (parameterChart f hf)) x

def infinityChartStalkIso
    (x : PrimeSpectrum (parameterChart f⁻¹ (transcendental_inverse f hf))) :
    (parameterCurve f hf).presheaf.stalk (infinityChartInclusion f hf x) ≅
      CommRingCat.of (Localization.AtPrime x.asIdeal) := by
  have : IsIso ((infinityChartInclusion f hf).stalkMap x) :=
    (IsOpenImmersion.iff_isIso_stalkMap.mp (infinityChartInclusion_isOpenImmersion f hf)).2 x
  exact asIso ((infinityChartInclusion f hf).stalkMap x) ≪≫
    Spec.stalkIso (.of (parameterChart f⁻¹ (transcendental_inverse f hf))) x

instance parameterCurve_compactSpace : CompactSpace (parameterCurve f hf) := by
  rw [← isCompact_univ_iff]
  have hcover : Set.range (zeroChartInclusion f hf) ∪
      Set.range (infinityChartInclusion f hf) = Set.univ := by
    ext x
    simp only [Set.mem_union, Set.mem_range, Set.mem_univ, iff_true]
    exact parameterCurve_twoChartCover f hf x
  rw [← hcover]
  exact (isCompact_range (zeroChartInclusion f hf).continuous).union
    (isCompact_range (infinityChartInclusion f hf).continuous)

theorem parameterCurve_genericPoint :
    IsGenericPoint
      (zeroChartInclusion f hf (zeroOverlap f hf
        (genericPoint (Spec (.of (parameterLaurentChart f hf)))))) Set.univ := by
  apply isGenericPoint_iff_specializes.mpr
  intro x
  constructor
  · intro _; trivial
  · intro _
    rcases parameterCurve_twoChartCover f hf x with ⟨y, rfl⟩ | ⟨y, rfl⟩
    · rw [genericPoint_eq_of_isOpenImmersion (zeroOverlap f hf)]
      exact (genericPoint_specializes y).map (zeroChartInclusion f hf).continuous
    · have he := congrArg
        (fun g => g (genericPoint (Spec (.of (parameterLaurentChart f hf)))))
        (parameterCurve_overlap_compatibility f hf)
      change zeroChartInclusion f hf (zeroOverlap f hf _) =
        infinityChartInclusion f hf (infinityOverlap f hf _) at he
      rw [he, genericPoint_eq_of_isOpenImmersion (infinityOverlap f hf)]
      exact (genericPoint_specializes y).map (infinityChartInclusion f hf).continuous

instance parameterCurve_irreducibleSpace : IrreducibleSpace (parameterCurve f hf) :=
  (irreducibleSpace_def _).mpr (parameterCurve_genericPoint f hf).isIrreducible

instance parameterCurve_isReduced : IsReduced (parameterCurve f hf) := by
  have (x : parameterCurve f hf) : _root_.IsReduced ((parameterCurve f hf).presheaf.stalk x) := by
    rcases parameterCurve_twoChartCover f hf x with ⟨y, rfl⟩ | ⟨y, rfl⟩
    · exact isReduced_of_injective (zeroChartStalkIso f hf y).hom.hom
        (zeroChartStalkIso f hf y).commRingCatIsoToRingEquiv.injective
    · exact isReduced_of_injective (infinityChartStalkIso f hf y).hom.hom
        (infinityChartStalkIso f hf y).commRingCatIsoToRingEquiv.injective
  exact isReduced_of_isReduced_stalk _

instance parameterCurve_isIntegral : IsIntegral (parameterCurve f hf) :=
  isIntegral_of_irreducibleSpace_of_isReduced _

def parameterCurveFunctionFieldIso :
    (parameterCurve f hf).functionField ≅ (Spec (.of (parameterChart f hf))).functionField := by
  let x := genericPoint (Spec (.of (parameterChart f hf)))
  have : IsIso ((zeroChartInclusion f hf).stalkMap x) :=
    (IsOpenImmersion.iff_isIso_stalkMap.mp (zeroChartInclusion_isOpenImmersion f hf)).2 x
  have hx : zeroChartInclusion f hf x = genericPoint (parameterCurve f hf) :=
    genericPoint_eq_of_isOpenImmersion (zeroChartInclusion f hf)
  exact eqToIso (congrArg (fun y => (parameterCurve f hf).presheaf.stalk y) hx.symm) ≪≫
    asIso ((zeroChartInclusion f hf).stalkMap x)

def parameterCurveFunctionFieldEquiv
    [FiniteDimensional (IntermediateField.adjoin F {f}) E] :
    (parameterCurve f hf).functionField ≃+* E := by
  let := parameterAlgebra f hf
  let := parameterPolynomialAlgebra f hf
  let := parameter_scalarTower f hf
  let := parameter_finite f hf
  letI : Algebra (parameterChart f hf) (Spec (.of (parameterChart f hf))).functionField :=
    AlgebraicGeometry.instAlgebraCarrierFunctionFieldSpec (.of (parameterChart f hf))
  letI : IsFractionRing (parameterChart f hf) (Spec (.of (parameterChart f hf))).functionField :=
    functionField_isFractionRing_of_affine (.of (parameterChart f hf))
  exact (parameterCurveFunctionFieldIso f hf).commRingCatIsoToRingEquiv.trans
    (IsLocalization.algEquiv (nonZeroDivisors (parameterChart f hf))
      (Spec (.of (parameterChart f hf))).functionField E).toRingEquiv

end PiExponent.CurveNormalizationModel

end

end OAI
end Source0349

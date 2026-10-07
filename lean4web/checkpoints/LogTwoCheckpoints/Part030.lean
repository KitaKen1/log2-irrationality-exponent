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
public import LogTwoCheckpoints.Part019
public import LogTwoCheckpoints.Part020
public import LogTwoCheckpoints.Part022
public import LogTwoCheckpoints.Part025
public import LogTwoCheckpoints.Part026
public import LogTwoCheckpoints.Part029
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Quasicoherent
public import Mathlib.Algebra.Homology.DerivedCategory.Ext.ExactSequences
public import Mathlib.Algebra.Module.LocalizedModule.Away
public import Mathlib.AlgebraicGeometry.IdealSheaf.Functorial
public import Mathlib.AlgebraicGeometry.Modules.Sheaf
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Basic
public import Mathlib.Analysis.Complex.Polynomial.Basic
public import Mathlib.Data.FunLike.Basic
public import Mathlib.Data.Opposite
public import Mathlib.Data.SetLike.Basic
public import Mathlib.RingTheory.MvPolynomial.Homogeneous
public import Mathlib.RingTheory.ReesAlgebra
@[expose] public section
set_option Elab.async false

-- Source: OAI/NumberTheory/PiExponent/Approximation/PushforwardOpenSections.lean
section Source0750
/-
Modification notice for the LogTwo project.
Derived from openai/math (Apache-2.0), revision adc7f1241b42e322a6451854ab7e4b4c146bf78a.
Original source: lean/OAI/NumberTheory/PiExponent/Approximation/PushforwardOpenSections.lean
Changes: Convert module/import declarations to the Lean 4.34 public module format.
Expose private helpers and adjust helper names where needed for module compatibility.
See ../THIRD_PARTY_NOTICES.txt for provenance and the recorded changes.
-/

namespace OAI

namespace PiExponent.GeometrySupport.PushforwardOpenSections
noncomputable section
open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite
open PiExponentSeshadri.ModuleFlasque PiExponentSeshadri.ProjectiveChartSections
open CechOne CechHigher

abbrev schemeFreeOpen (X : Scheme.{0}) (U : X.Opens) : X.Modules :=
  freeOpen X.ringCatSheaf U

variable {X Y : Scheme.{0}} (f : Y ⟶ X) {M : X.Modules} {N : Y.Modules}
    (β : M ⟶ (Scheme.Modules.pushforward f).obj N)

def sectionMap (U : X.Opens) :
    (schemeFreeOpen X U ⟶ M) →+
      (schemeFreeOpen Y (f ⁻¹ᵁ U) ⟶ N) where
  toFun b := (freeOpenAddEquiv (f ⁻¹ᵁ U) N).symm
    (β.app U (freeOpenAddEquiv U M b))
  map_zero' := by
    change (freeOpenAddEquiv (f ⁻¹ᵁ U) N).symm
      ((β.app U).hom (freeOpenAddEquiv U M 0)) = 0
    rw [_root_.map_zero, _root_.map_zero]
    exact (freeOpenAddEquiv (f ⁻¹ᵁ U) N).symm.map_zero
  map_add' b c := by
    change (freeOpenAddEquiv (f ⁻¹ᵁ U) N).symm
      ((β.app U).hom (freeOpenAddEquiv U M (b + c))) = _
    rw [_root_.map_add, _root_.map_add]
    exact (freeOpenAddEquiv (f ⁻¹ᵁ U) N).symm.map_add _ _

@[simp] theorem sectionMap_value (U : X.Opens) (b : schemeFreeOpen X U ⟶ M) :
    freeOpenAddEquiv (f ⁻¹ᵁ U) N (sectionMap f β U b) =
      β.app U (freeOpenAddEquiv U M b) := AddEquiv.apply_symm_apply _ _

theorem sectionMap_bijective (U : X.Opens) (h : Function.Bijective (β.app U)) :
    Function.Bijective (sectionMap f β U) :=
  (freeOpenAddEquiv (f ⁻¹ᵁ U) N).symm.bijective.comp
    (h.comp (freeOpenAddEquiv U M).bijective)

theorem sectionMap_injective (U : X.Opens) (h : Function.Injective (β.app U)) :
    Function.Injective (sectionMap f β U) :=
  (freeOpenAddEquiv (f ⁻¹ᵁ U) N).symm.injective.comp
    (h.comp (freeOpenAddEquiv U M).injective)

theorem sectionMap_restrict {U V : X.Opens} (h : U ≤ V)
    (b : schemeFreeOpen X V ⟶ M) :
    sectionMap f β U (restrictHom X.ringCatSheaf h b) =
      restrictHom Y.ringCatSheaf (f.preimage_mono h) (sectionMap f β V b) := by
  apply (freeOpenAddEquiv (f ⁻¹ᵁ U) N).injective
  erw [sectionMap_value]
  change β.app U (freeOpenEquiv X.ringCatSheaf M U
      (freeOpenMap X.ringCatSheaf (homOfLE h) ≫ b)) =
    freeOpenEquiv Y.ringCatSheaf N (f ⁻¹ᵁ U)
      (freeOpenMap Y.ringCatSheaf (homOfLE (f.preimage_mono h)) ≫ sectionMap f β V b)
  have hleft := freeOpenEquiv_naturality X.ringCatSheaf M (homOfLE h) b
  have hright := freeOpenEquiv_naturality Y.ringCatSheaf N
    (homOfLE (f.preimage_mono h)) (sectionMap f β V b)
  have hn := PresheafOfModules.naturality_apply β.val (homOfLE h).op
    (freeOpenEquiv X.ringCatSheaf M V b)
  change β.app U (M.presheaf.map (homOfLE h).op _) =
    N.presheaf.map (homOfLE (f.preimage_mono h)).op
      (β.app V (freeOpenAddEquiv V M b)) at hn
  exact (congrArg (β.app U) hleft).trans
    (hn.trans ((congrArg (N.presheaf.map (homOfLE (f.preimage_mono h)).op)
      (sectionMap_value f β V b).symm).trans hright.symm))

def restrictEquiv (N : Y.Modules) {U V : Y.Opens} (h : U ≤ V) (h' : V ≤ U) :
    (schemeFreeOpen Y V ⟶ N) ≃+ (schemeFreeOpen Y U ⟶ N) where
  toFun := restrictHom Y.ringCatSheaf h
  invFun := restrictHom Y.ringCatSheaf h'
  left_inv b := by erw [restrictHom_restrictHom, restrictHom_refl]
  right_inv b := by erw [restrictHom_restrictHom, restrictHom_refl]
  map_add' := restrictHom_add Y.ringCatSheaf h

end
end PiExponent.GeometrySupport.PushforwardOpenSections

end OAI
end Source0750

-- Source: OAI/NumberTheory/PiExponent/Approximation/PushforwardSectionComparison.lean
section Source0751
/-
Modification notice for the LogTwo project.
Derived from openai/math (Apache-2.0), revision adc7f1241b42e322a6451854ab7e4b4c146bf78a.
Original source: lean/OAI/NumberTheory/PiExponent/Approximation/PushforwardSectionComparison.lean
Changes: Convert module/import declarations to the Lean 4.34 public module format.
Expose private helpers and adjust helper names where needed for module compatibility.
See ../THIRD_PARTY_NOTICES.txt for provenance and the recorded changes.
-/

namespace OAI

namespace PiExponent.GeometrySupport.PushforwardOpenSections
noncomputable section
open AlgebraicGeometry CategoryTheory TopologicalSpace
open PiExponentSeshadri.ModuleFlasque
open CechOne CechHigher CechH1Transfer

abbrev pushforwardComparisonFreeOpen (X : Scheme.{0}) (U : X.Opens) : X.Modules :=
  freeOpen X.ringCatSheaf U

variable {X Y : Scheme.{0}} (f : Y ⟶ X) {M : X.Modules} {N : Y.Modules}
    (β : M ⟶ (Scheme.Modules.pushforward f).obj N)
    {J : Type} (U : J → X.Opens)

theorem intersection_preimage {k : ℕ} (t : Fin k → J) :
    intersection (fun i => f ⁻¹ᵁ U i) t = f ⁻¹ᵁ intersection U t := by
  ext x
  simp [intersection, Opens.coe_iInf]

def tupleSectionMap {k : ℕ} (t : Fin k → J) :
    (pushforwardComparisonFreeOpen X (intersection U t) ⟶ M) →+
      (pushforwardComparisonFreeOpen Y (intersection (fun i => f ⁻¹ᵁ U i) t) ⟶ N) :=
  (restrictEquiv N (le_of_eq (intersection_preimage f U t))
    (le_of_eq (intersection_preimage f U t).symm)).toAddMonoidHom.comp
      (sectionMap f β (intersection U t))

theorem tupleSectionMap_bijective {k : ℕ} (t : Fin k → J)
    (h : Function.Bijective (β.app (intersection U t))) :
    Function.Bijective (tupleSectionMap f β U t) :=
  (restrictEquiv N (le_of_eq (intersection_preimage f U t))
    (le_of_eq (intersection_preimage f U t).symm)).bijective.comp
      (sectionMap_bijective f β _ h)

theorem tupleSectionMap_injective {k : ℕ} (t : Fin k → J)
    (h : Function.Injective (β.app (intersection U t))) :
    Function.Injective (tupleSectionMap f β U t) :=
  (restrictEquiv N (le_of_eq (intersection_preimage f U t))
    (le_of_eq (intersection_preimage f U t).symm)).injective.comp
      (sectionMap_injective f β _ h)

theorem tupleSectionMap_face {k : ℕ} (t : Fin (k+2) → J) (j : Fin (k+2))
    (b : pushforwardComparisonFreeOpen X (intersection U (t ∘ j.succAbove)) ⟶ M) :
    tupleSectionMap f β U t (restrictHom X.ringCatSheaf (faceLE U t j) b) =
      restrictHom Y.ringCatSheaf (faceLE (fun i => f ⁻¹ᵁ U i) t j)
        (tupleSectionMap f β U (t ∘ j.succAbove) b) := by
  change restrictHom Y.ringCatSheaf _
      (sectionMap f β _ (restrictHom X.ringCatSheaf _ b)) =
    restrictHom Y.ringCatSheaf _
      (restrictHom Y.ringCatSheaf _ (sectionMap f β _ b))
  erw [sectionMap_restrict, restrictHom_restrictHom, restrictHom_restrictHom]

def comparison
    (hvertex : ∀ t : Fin 1 → J, Function.Bijective (β.app (intersection U t)))
    (hpair : ∀ t : Fin 2 → J, Function.Injective (β.app (intersection U t))) :
    SectionComparison U (fun i => f ⁻¹ᵁ U i) M N where
  vertex t := AddEquiv.ofBijective (tupleSectionMap f β U t)
    (tupleSectionMap_bijective f β U t (hvertex t))
  pair t := tupleSectionMap f β U t
  triple t := tupleSectionMap f β U t
  pair_injective t := tupleSectionMap_injective f β U t (hpair t)
  pair_restrict t j b := tupleSectionMap_face f β U t j b
  triple_restrict t j b := tupleSectionMap_face f β U t j b

end
end PiExponent.GeometrySupport.PushforwardOpenSections

end OAI
end Source0751

-- Source: OAI/NumberTheory/PiExponent/Ampleness/FiniteReesComparison.lean
section Source0752
/-
Modification notice for the LogTwo project.
Derived from openai/math (Apache-2.0), revision adc7f1241b42e322a6451854ab7e4b4c146bf78a.
Original source: lean/OAI/NumberTheory/PiExponent/Ampleness/FiniteReesComparison.lean
Changes: Convert module/import declarations to the Lean 4.34 public module format.
See ../THIRD_PARTY_NOTICES.txt for provenance and the recorded changes.
-/

namespace OAI

namespace PiExponent.GeometrySupport.ExceptionalRecoveryMap
noncomputable section
open AlgebraicGeometry CategoryTheory TopologicalSpace
open PiExponentSeshadri.Geometry PiExponentSeshadri.IdealModule PiExponentSeshadri.Frames
open PiExponentSeshadri.ModuleFlasque
open CechHigher
variable {X Y : Scheme.{0}} (f : Y ⟶ X) [QuasiCompact f]
    (I : X.IdealSheafData) (E : LineBundle Y)
    (ι : E.sheaf ⟶ structureSheaf Y) (hE : PresentsPullbackIdeal I f E ι)

private theorem intersection_one {J : Type} (U : J → X.Opens) (t : Fin 1 → J) :
    intersection U t = U (t 0) := by
  apply le_antisymm (iInf_le _ 0)
  apply le_iInf
  intro i
  exact le_of_eq (congrArg (fun j => U (t j)) (Subsingleton.elim 0 i))

private theorem intersection_two {J : Type} (U : J → X.Opens) (t : Fin 2 → J) :
    intersection U t = U (t 0) ⊓ U (t 1) := by
  apply le_antisymm (le_inf (iInf_le _ 0) (iInf_le _ 1))
  apply le_iInf
  intro i
  fin_cases i
  · exact inf_le_left
  · exact inf_le_right

theorem eventual_comparison_of_affine_recovery [CompactSpace X] [X.IsSeparated]
    (A : LineBundle X)
    (hrecover : ∀ U : X.affineOpens, ∃ N, ∀ n, N ≤ n →
      Function.Bijective ((ordinaryMap f I E ι hE n).app U.1)) :
    ∃ k : ℕ, ∃ U : Fin k → X.affineOpens, (⨆ i, (U i).1) = ⊤ ∧
      ∃ N, ∀ n, N ≤ n → Nonempty
        (CechH1Transfer.SectionComparison (fun i => (U i).1)
          (fun i => f ⁻¹ᵁ (U i).1)
          ((moduleTwistFunctor A n).obj (closedModule (I^n)))
          ((E.tensor (A.pullback f)).pow n).sheaf) := by
  classical
  obtain ⟨k,U,hcover,hframe⟩ := A.finite_affine_frame_cover
  let V : Fin k → X.Opens := fun i => (U i).1
  have ha1 (t : Fin 1 → Fin k) : IsAffineOpen (intersection V t) :=
    (intersection_one V t).symm ▸ (U (t 0)).2
  have ha2 (t : Fin 2 → Fin k) : IsAffineOpen (intersection V t) :=
    (intersection_two V t).symm ▸ (U (t 0)).2.inf (U (t 1)).2
  choose Nv hv using fun t : Fin 1 → Fin k => hrecover ⟨intersection V t, ha1 t⟩
  choose Np hp using fun t : Fin 2 → Fin k => hrecover ⟨intersection V t, ha2 t⟩
  let Bv := Finset.univ.sup Nv
  let Bp := Finset.univ.sup Np
  refine ⟨k,U,hcover,Bv ⊔ Bp,?_⟩
  intro n hn
  let β := twistedMap f I E ι hE A n
  have hvn (t : Fin 1 → Fin k) : Function.Bijective (β.app (intersection V t)) := by
    exact twistedMap_app_bijective f I E ι hE A n (intersection V t)
      (restrictOpenFrame (iInf_le _ 0) (Classical.choice (hframe (t 0))))
      (hv t n ((Finset.le_sup (Finset.mem_univ t)).trans (le_sup_left.trans hn)))
  have hpn (t : Fin 2 → Fin k) : Function.Injective (β.app (intersection V t)) := by
    exact (twistedMap_app_bijective f I E ι hE A n (intersection V t)
      (restrictOpenFrame (iInf_le _ 0) (Classical.choice (hframe (t 0))))
      (hp t n ((Finset.le_sup (Finset.mem_univ t)).trans (le_sup_right.trans hn)))).injective
  exact ⟨PushforwardOpenSections.comparison f β V hvn hpn⟩

end
end PiExponent.GeometrySupport.ExceptionalRecoveryMap

end OAI
end Source0752

-- Source: OAI/NumberTheory/PiExponent/Approximation/SerreSectionLifting.lean
section Source0753
-- Modified in this edition: unused plain lemmas removed; see reduction.json.
/-
Modification notice for the LogTwo project.
Derived from openai/math (Apache-2.0), revision adc7f1241b42e322a6451854ab7e4b4c146bf78a.
Original source: lean/OAI/NumberTheory/PiExponent/Approximation/SerreSectionLifting.lean
Changes: Convert module/import declarations to the Lean 4.34 public module format.
See ../THIRD_PARTY_NOTICES.txt for provenance and the recorded changes.
-/

namespace OAI

namespace PiExponent.GeometrySupport.SerreSectionLifting
noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Abelian
open PiExponentSeshadri.Geometry
variable {X : Scheme.{0}} {R : Type} [CommRing R] [IsNoetherianRing R]

theorem globalSections_surjective_of_h1_zero
    (S : ShortComplex X.Modules) (hS : S.ShortExact)
    (hzero : ∀ x : cohomology S.X₁ 1, x = 0) :
    Function.Surjective (fun s : GlobalSections X S.X₂ => s ≫ S.g) := by
  intro s
  obtain ⟨a, ha⟩ := Ext.covariant_sequence_exact₃ (structureSheaf X) hS
    (Ext.mk₀ s) (n₁ := 1) rfl (hzero _)
  refine ⟨Ext.homEquiv₀ a, ?_⟩
  apply (Ext.mk₀_bijective (structureSheaf X) S.X₃).injective
  rw [← Ext.mk₀_comp_mk₀, Ext.mk₀_homEquiv₀_apply]
  exact ha

end
end PiExponent.GeometrySupport.SerreSectionLifting

end OAI
end Source0753

-- Source: OAI/NumberTheory/PiExponent/Ampleness/BlowupJetSurjectivity.lean
section Source0754
/-
Modification notice for the LogTwo project.
Derived from openai/math (Apache-2.0), revision adc7f1241b42e322a6451854ab7e4b4c146bf78a.
Original source: lean/OAI/NumberTheory/PiExponent/Ampleness/BlowupJetSurjectivity.lean
Changes: Convert module/import declarations to the Lean 4.34 public module format.
See ../THIRD_PARTY_NOTICES.txt for provenance and the recorded changes.
-/

namespace OAI

namespace PiExponent.BlowupJetSurjectivity
noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace
open PiExponentSeshadri.Geometry
open PiExponent.GeometrySupport

variable {X B : Scheme.{0}} {R : Type} [CommRing R] [IsNoetherianRing R]

def jetQuotient (I : X.IdealSheafData) : X.Modules :=
  (Scheme.Modules.pushforward I.subschemeι).obj (PiExponentSeshadri.IdealModule.unit I.subscheme)

def twistedIdeal (I : X.IdealSheafData) (A : LineBundle X) (n : ℕ) : X.Modules :=
  (moduleTwistFunctor A n).obj (PiExponentSeshadri.IdealModule.closedModule (I ^ n))

def jetRestriction (I : X.IdealSheafData) (A : LineBundle X) (n : ℕ)
    (s : GlobalSections X (modulePow X A.sheaf n)) :
    GlobalSections X ((moduleTwistFunctor A n).obj (jetQuotient (I ^ n))) :=
  s ≫ (moduleTwistUnitIso A n).inv ≫
    (moduleTwistFunctor A n).map (PiExponentSeshadri.IdealModule.structureMap (I ^ n).subschemeι)

theorem jetRestriction_surjective_of_h1_zero
    (I : X.IdealSheafData) (A : LineBundle X) (n : ℕ)
    (hzero : ∀ x : cohomology (twistedIdeal I A n) 1, x = 0) :
    Function.Surjective (jetRestriction I A n) := by
  let S := ShortComplex.mk (PiExponentSeshadri.IdealModule.inclusion (I ^ n).subschemeι)
    (PiExponentSeshadri.IdealModule.structureMap (I ^ n).subschemeι) (kernel.condition _)
  have hS : S.ShortExact := PiExponentSeshadri.IdealModule.closedSequence_exact (I ^ n).subschemeι
  have hsurj := SerreSectionLifting.globalSections_surjective_of_h1_zero
    (S.map (moduleTwistFunctor A n)) (moduleTwistFunctor_shortExact A n S hS) hzero
  intro s
  obtain ⟨t, ht⟩ := hsurj s
  refine ⟨t ≫ (moduleTwistUnitIso A n).hom, ?_⟩
  change t ≫ (moduleTwistFunctor A n).map
    (PiExponentSeshadri.IdealModule.structureMap (I ^ n).subschemeι) = s at ht
  change (t ≫ (moduleTwistUnitIso A n).hom) ≫ (moduleTwistUnitIso A n).inv ≫ _ = s
  erw [Category.assoc, Iso.hom_inv_id_assoc]
  exact ht

theorem eventual_jetRestriction_surjective_of_ample_comparison
    [IsNoetherian X]
    (f : B ⟶ X) (p : B ⟶ Spec (CommRingCat.of R)) [IsProper p]
    (I : X.IdealSheafData) (A : LineBundle X)
    (F : LineBundle B) (hF : LineBundle.IsAmple B F)
    {J : Type} (U : J → X.Opens) (hU : ∀ i, IsAffineOpen (U i))
    (hcover : (⨆ i, U i) = ⊤)
    (hcomparison : ∃ N, ∀ n, N ≤ n → Nonempty
      (CechH1Transfer.SectionComparison U (fun i => f ⁻¹ᵁ U i)
        (twistedIdeal I A n) (modulePow B F.sheaf n))) :
    ∃ N, ∀ n, N ≤ n → Function.Surjective (jetRestriction I A n) := by
  obtain ⟨N₁, hN₁⟩ := NoetherianAmpleSerreVanishing.ample_power_cohomology_zero p F hF
  obtain ⟨N₂, hN₂⟩ := hcomparison
  refine ⟨max N₁ N₂, fun n hn => ?_⟩
  apply jetRestriction_surjective_of_h1_zero I A n
  let : (PiExponentSeshadri.IdealModule.closedModule (I ^ n)).IsFinitePresentation :=
    CompactJetIdeal.closedModule_isFinitePresentation (I ^ n)
  let : (twistedIdeal I A n).IsFinitePresentation :=
    FiniteGlobalPresentation.moduleTwist_isFinitePresentation A n _
  let : (twistedIdeal I A n).IsQuasicoherent :=
    (SheafOfModules.IsFinitePresentation.exists_quasicoherentData
      (twistedIdeal I A n)).choose.isQuasicoherent
  obtain ⟨P⟩ := hN₂ n ((le_max_right _ _).trans hn)
  apply P.cohomology_one_zero hU hcover _ (hN₁ n ((le_max_left _ _).trans hn) 1 (by decide))
  exact f.iSup_preimage_eq_top hcover

end
end PiExponent.BlowupJetSurjectivity

end OAI
end Source0754

-- Source: OAI/NumberTheory/PiExponent/Ampleness/GlobalBlowupJetSurjectivity.lean
section Source0755
/-
Modification notice for the LogTwo project.
Derived from openai/math (Apache-2.0), revision adc7f1241b42e322a6451854ab7e4b4c146bf78a.
Original source: lean/OAI/NumberTheory/PiExponent/Ampleness/GlobalBlowupJetSurjectivity.lean
Changes: Convert module/import declarations to the Lean 4.34 public module format.
See ../THIRD_PARTY_NOTICES.txt for provenance and the recorded changes.
-/

namespace OAI

namespace PiExponent.BlowupJetSurjectivity
noncomputable section
open AlgebraicGeometry CategoryTheory TopologicalSpace
open PiExponentSeshadri.Geometry
open PiExponent.GeometrySupport
variable {X : Scheme.{0}} {R : Type} [CommRing R] [IsNoetherianRing R]

def blowupBundle (I : X.IdealSheafData) (A : LineBundle X) :
    LineBundle (PiExponentSeshadri.BlowupGluing.scheme I) :=
  (PiExponentSeshadri.BlowupGluing.exceptionalLineBundle I).tensor
    (A.pullback (PiExponentSeshadri.BlowupGluing.projection I))

theorem eventual_blowup_jetRestriction_surjective_of_section_comparison
    (p : X ⟶ Spec (CommRingCat.of R)) [IsProper p]
    (I : X.IdealSheafData) (A : LineBundle X)
    (hample : LineBundle.IsAmple _ (blowupBundle I A))
    {J : Type} (U : J → X.Opens) (hU : ∀ i, IsAffineOpen (U i))
    (hcover : (⨆ i, U i) = ⊤)
    (hcomparison : ∃ N, ∀ n, N ≤ n → Nonempty
      (CechH1Transfer.SectionComparison U
        (fun i => PiExponentSeshadri.BlowupGluing.projection I ⁻¹ᵁ U i)
        (twistedIdeal I A n)
        (modulePow (PiExponentSeshadri.BlowupGluing.scheme I) (blowupBundle I A).sheaf n))) :
    ∃ N, ∀ n, N ≤ n → Function.Surjective (jetRestriction I A n) := by
  let : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian p
  let : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace p
  let : IsNoetherian X := {}
  exact eventual_jetRestriction_surjective_of_ample_comparison
    (PiExponentSeshadri.BlowupGluing.projection I)
    (PiExponentSeshadri.BlowupGluing.projection I ≫ p) I A (blowupBundle I A)
    hample U hU hcover hcomparison

end
end PiExponent.BlowupJetSurjectivity

end OAI
end Source0755

-- Source: OAI/NumberTheory/PiExponent/Ampleness/BlowupJetReesReduction.lean
section Source0756
/-
Modification notice for the LogTwo project.
Derived from openai/math (Apache-2.0), revision adc7f1241b42e322a6451854ab7e4b4c146bf78a.
Original source: lean/OAI/NumberTheory/PiExponent/Ampleness/BlowupJetReesReduction.lean
Changes: Convert module/import declarations to the Lean 4.34 public module format.
See ../THIRD_PARTY_NOTICES.txt for provenance and the recorded changes.
-/

namespace OAI

namespace PiExponent.BlowupJetSurjectivity
noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace
open PiExponentSeshadri.Geometry
open PiExponent.GeometrySupport
variable {X : Scheme.{0}} {R : Type} [CommRing R] [IsNoetherianRing R]

theorem eventual_blowup_jetRestriction_surjective_of_affine_recovery
    (p : X ⟶ Spec (CommRingCat.of R)) [IsProper p] [IsLocallyNoetherian X]
    (I : X.IdealSheafData) (A : LineBundle X)
    (hample : LineBundle.IsAmple _ (blowupBundle I A))
    (hrecover : ∀ U : X.affineOpens, ∃ N, ∀ n, N ≤ n → Function.Bijective
      ((ExceptionalRecoveryMap.ordinaryMap (PiExponentSeshadri.BlowupGluing.projection I)
        I (PiExponentSeshadri.BlowupGluing.exceptionalLineBundle I)
        (PiExponentSeshadri.BlowupGluing.exceptionalInclusion I)
        (PiExponentSeshadri.BlowupGluing.exceptional_presents I) n).app U.1)) :
    ∃ N, ∀ n, N ≤ n → Function.Surjective (jetRestriction I A n) := by
  let : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian p
  let : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace p
  let : X.IsSeparated := ⟨by
    have h : IsSeparated (p ≫ terminal.from (Spec (CommRingCat.of R))) := inferInstance
    simpa only [terminal.comp_from] using h⟩
  obtain ⟨k,U,hcover,N,hN⟩ :=
    ExceptionalRecoveryMap.eventual_comparison_of_affine_recovery
      (PiExponentSeshadri.BlowupGluing.projection I) I
      (PiExponentSeshadri.BlowupGluing.exceptionalLineBundle I)
      (PiExponentSeshadri.BlowupGluing.exceptionalInclusion I)
      (PiExponentSeshadri.BlowupGluing.exceptional_presents I) A hrecover
  exact eventual_blowup_jetRestriction_surjective_of_section_comparison
    p I A hample (fun i => (U i).1) (fun i => (U i).2) hcover ⟨N,hN⟩

end
end PiExponent.BlowupJetSurjectivity

end OAI
end Source0756

-- Source: OAI/NumberTheory/PiExponent/Ampleness/ExceptionalAffineChart.lean
section Source0757
/-
Modification notice for the LogTwo project.
Derived from openai/math (Apache-2.0), revision adc7f1241b42e322a6451854ab7e4b4c146bf78a.
Original source: lean/OAI/NumberTheory/PiExponent/Ampleness/ExceptionalAffineChart.lean
Changes: Convert module/import declarations to the Lean 4.34 public module format.
See ../THIRD_PARTY_NOTICES.txt for provenance and the recorded changes.
-/

namespace OAI

noncomputable section
open CategoryTheory AlgebraicGeometry
open PiExponentSeshadri.Geometry PiExponentSeshadri.Frames
namespace PiExponent.ExceptionalAffineChart
open PiExponentSeshadri.IdealPullback
variable {R A : Type} [CommRing R] [CommRing A] {Y : Scheme}
variable (I : Ideal R) (f : Y ⟶ Spec (CommRingCat.of R))
  (j : Spec (CommRingCat.of A) ⟶ Y) [IsOpenImmersion j]
  (φ : R →+* A) (hf : j ≫ f = Spec.map (CommRingCat.ofHom φ))

def chartOpen : Y.affineOpens :=
  ⟨j.opensRange, isAffineOpen_opensRange _⟩

def affineGammaEquiv {Y : Scheme} {A : CommRingCat} (g : Y ≅ Spec A) :
    Γ(Y,⊤) ≃+* A :=
  (Scheme.Γ.mapIso g.symm.op ≪≫ Scheme.ΓSpecIso A).commRingCatIsoToRingEquiv

def chartFunctionsEquiv : Γ((chartOpen j).1.toScheme, ⊤) ≃+* A :=
  affineGammaEquiv (j.isoOpensRange.symm)

def chartPowerIdeal (n : ℕ) : Ideal Γ((chartOpen j).1.toScheme, ⊤) :=
  powerChartIdeal (f) (specIdeal I) n (chartOpen j)
    ⟨⊤, isAffineOpen_top _⟩ (by simp)

theorem chartPowerIdeal_eq (n : ℕ) :
    chartPowerIdeal I f j n =
      ((((specIdeal I).comap f)^n).comap (chartOpen j).1.ι).ideal
        ⟨⊤, isAffineOpen_top _⟩ := by
  change powerChartIdeal f (specIdeal I) n (chartOpen j)
    ⟨⊤, isAffineOpen_top _⟩ _ = _
  simp only [powerChartIdeal]
  have hlocal := PiExponentSeshadri.IdealPullback.comap_ideal ((specIdeal I)^n)
    f (chartOpen j) ⟨⊤, isAffineOpen_top _⟩ (by simp)
  have hpow := congrArg (fun K : Y.IdealSheafData => K.ideal (chartOpen j))
    (PiExponentSeshadri.IdealPullback.comap_pow (specIdeal I) f n)
  exact (congrArg (Ideal.map (chartOpen j).1.topIso.inv.hom)
    (hlocal.symm.trans hpow)).trans
      (PiExponentSeshadri.IdealPullback.comap_ι_top
        (((specIdeal I).comap f)^n) (chartOpen j)).symm

include hf in

theorem map_chartPowerIdeal (n : ℕ) :
    (chartPowerIdeal I f j n).map (chartFunctionsEquiv j).toRingHom =
      (I^n).map (φ) := by
  let : IsAffine j.opensRange.toScheme := isAffineOpen_opensRange j
  have hlocal : ((((specIdeal I).comap f)^n).comap j).ideal
      ⟨⊤, isAffineOpen_top _⟩ =
      ((I^n).map (φ)).map
        (Scheme.ΓSpecIso (CommRingCat.of (A))).inv.hom := by
    rw [← PiExponentSeshadri.IdealPullback.comap_pow,
      ← PiExponentSeshadri.IdealPullback.specIdeal_pow,
      ← Scheme.IdealSheafData.comap_comp, hf,
      specIdeal_comap, specIdeal_top]
  have hmap : (chartPowerIdeal I f j n).map
      (j.isoOpensRange.hom.appTop.hom) =
      ((((specIdeal I).comap f)^n).comap j).ideal
        ⟨⊤, isAffineOpen_top _⟩ := by
    erw [chartPowerIdeal_eq, ← PiExponentSeshadri.IdealPullback.comap_top,
      ← Scheme.IdealSheafData.comap_comp]
    change (((specIdeal I).comap f ^ n).comap (j.isoOpensRange.hom ≫ j.opensRange.ι)).ideal _ = _
    rw [j.isoOpensRange_hom_ι]
  change (chartPowerIdeal I f j n).map
    ((Scheme.ΓSpecIso (CommRingCat.of (A))).hom.hom.comp
      (j.isoOpensRange.hom.appTop.hom)) = _
  erw [← Ideal.map_map, hmap, hlocal, Ideal.map_map]
  have hi : (Scheme.ΓSpecIso (CommRingCat.of (A))).hom.hom.comp
      (Scheme.ΓSpecIso (CommRingCat.of (A))).inv.hom = RingHom.id _ := by
    apply RingHom.ext
    intro r
    exact (Scheme.ΓSpecIso (CommRingCat.of A)).inv_hom_id_apply r
  rw [hi, Ideal.map_id]

def idealMapAddEquiv {A B : Type*} [CommRing A] [CommRing B]
    (e : A ≃+* B) (J : Ideal A) : J ≃+ J.map e.toRingHom :=
  AddEquiv.ofBijective
    (show J →+ J.map e.toRingHom from
      { toFun := fun x => ⟨e x, Ideal.mem_map_of_mem _ x.property⟩
        map_zero' := by ext; exact e.map_zero
        map_add' := by intro x y; ext; exact e.map_add x y })
    ⟨by intro x y h; exact Subtype.ext (e.injective (congrArg Subtype.val h)), by
      intro y
      obtain ⟨x, hx, he⟩ := (Ideal.mem_map_iff_of_surjective e.toRingHom e.surjective).mp y.property
      exact ⟨⟨x, hx⟩, Subtype.ext he⟩⟩

def sectionsEquiv (L : LineBundle Y) (ι : L.sheaf ⟶ O Y)
    (hL : PresentsPullbackIdeal (specIdeal I) f L ι)
    (e : L.sheaf.restrict (chartOpen j).1.ι ≅ O (chartOpen j).1.toScheme) (n : ℕ) :
    ((L.pow n).sheaf.restrict (chartOpen j).1.ι).val.obj (.op ⊤) ≃+ ↥((I^n).map φ) :=
  (idealPowerSectionsEquiv f (specIdeal I) L ι hL n (chartOpen j)
    ⟨⊤, isAffineOpen_top _⟩ (by simp) e).toAddEquiv |>.trans
      ((idealMapAddEquiv (chartFunctionsEquiv j) (chartPowerIdeal I f j n)).trans
        ((LinearEquiv.ofEq _ _ (map_chartPowerIdeal I f j φ hf n)).toAddEquiv))

theorem sectionsEquiv_apply (L : LineBundle Y) (ι : L.sheaf ⟶ O Y)
    (hL : PresentsPullbackIdeal (specIdeal I) f L ι)
    (e : L.sheaf.restrict (chartOpen j).1.ι ≅ O (chartOpen j).1.toScheme) (n : ℕ)
    (s : ((L.pow n).sheaf.restrict (chartOpen j).1.ι).val.obj (.op ⊤)) :
    (sectionsEquiv I f j φ hf L ι hL e n s).val =
      chartFunctionsEquiv j
        ((PiExponentSeshadri.InvertibleLocal.restrictedInclusion (L.pow n)
          (idealPowerInclusion L ι n) (chartOpen j).1.ι).val.app (.op ⊤) s) := rfl

def idealChartFrame (L : Y.IdealSheafData)
    (r : Γ(Spec (CommRingCat.of A), ⊤))
    (hprincipal : (L.comap j).ideal ⟨⊤, isAffineOpen_top _⟩ = Ideal.span {r})
    (hregular : IsLeftRegular r) :
    (PiExponentSeshadri.IdealModule.closedModule L).restrict (chartOpen j).1.ι ≅
      O (chartOpen j).1.toScheme :=
  PiExponentSeshadri.IdealModule.frameOnRange _ j
    (PiExponentSeshadri.IdealModule.frame_restriction L j r hprincipal hregular).some

end PiExponent.ExceptionalAffineChart
end

end OAI
end Source0757

-- Source: OAI/NumberTheory/PiExponent/Ampleness/ExceptionalAffineChartRestriction.lean
section Source0758
/-
Modification notice for the LogTwo project.
Derived from openai/math (Apache-2.0), revision adc7f1241b42e322a6451854ab7e4b4c146bf78a.
Original source: lean/OAI/NumberTheory/PiExponent/Ampleness/ExceptionalAffineChartRestriction.lean
Changes: Convert module/import declarations to the Lean 4.34 public module format.
Expose private helpers and adjust helper names where needed for module compatibility.
See ../THIRD_PARTY_NOTICES.txt for provenance and the recorded changes.
-/

namespace OAI

namespace PiExponent.ExceptionalAffineChart
noncomputable section
open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite
open PiExponentSeshadri.Geometry PiExponentSeshadri.Frames
open PiExponentSeshadri.ModuleFlasque PiExponentSeshadri.RestrictionCohomology
open PiExponentSeshadri.IdealPullback

abbrev schemeFreeOpen (Y : Scheme) (U : Y.Opens) : Y.Modules :=
  freeOpen Y.ringCatSheaf U

section Functions
variable {A B : Type} [CommRing A] [CommRing B] {Y : Scheme}
variable (j : Spec (CommRingCat.of A) ⟶ Y) [IsOpenImmersion j]
  (j' : Spec (CommRingCat.of B) ⟶ Y) [IsOpenImmersion j']
  (θ : A →+* B) (h : Spec.map (CommRingCat.ofHom θ) ≫ j = j')

include h in
lemma opensRange_le : j'.opensRange ≤ j.opensRange := by
  change Set.range j' ⊆ Set.range j
  rintro y ⟨b,rfl⟩
  refine ⟨Spec.map (CommRingCat.ofHom θ) b, ?_⟩
  exact congr($(h) b)

lemma chart_square :
    j'.isoOpensRange.hom ≫ Y.homOfLE (opensRange_le j j' θ h) =
      Spec.map (CommRingCat.ofHom θ) ≫ j.isoOpensRange.hom := by
  apply (cancel_mono j.opensRange.ι).mp
  simp only [Category.assoc, Scheme.homOfLE_ι, Scheme.Hom.isoOpensRange_hom_ι, h]

def functionsOnOpenEquiv : Γ(Y,j.opensRange) ≃+* A :=
  j.opensRange.topIso.symm.commRingCatIsoToRingEquiv.trans (chartFunctionsEquiv j)

lemma chartFunctions_naturality (s : Γ(j.opensRange.toScheme,⊤)) :
    chartFunctionsEquiv j' ((Y.homOfLE (opensRange_le j j' θ h)).appTop s) =
      θ (chartFunctionsEquiv j s) := by
  change (Scheme.ΓSpecIso (CommRingCat.of B)).hom
      (j'.isoOpensRange.hom.appTop ((Y.homOfLE (opensRange_le j j' θ h)).appTop s)) =
    θ ((Scheme.ΓSpecIso (CommRingCat.of A)).hom (j.isoOpensRange.hom.appTop s))
  have hc := congrArg (fun g => g.appTop) (chart_square j j' θ h)
  simp only [Scheme.Hom.comp_appTop] at hc
  have he : (Y.homOfLE (opensRange_le j j' θ h)).appTop ≫
        j'.isoOpensRange.hom.appTop ≫ (Scheme.ΓSpecIso (CommRingCat.of B)).hom =
      j.isoOpensRange.hom.appTop ≫ (Scheme.ΓSpecIso (CommRingCat.of A)).hom ≫
        CommRingCat.ofHom θ := by
    rw [← Category.assoc, hc, Category.assoc, Scheme.ΓSpecIso_naturality]
  exact CategoryTheory.congr_fun he s

lemma topIso_restriction {U V : Y.Opens} (hUV : U ≤ V) (s : Γ(Y,V)) :
    U.topIso.inv (Y.presheaf.map (homOfLE hUV).op s) =
      (Y.homOfLE hUV).appTop (V.topIso.inv s) := by
  change (Y.presheaf.map (homOfLE hUV).op ≫ U.topIso.inv) s =
    (V.topIso.inv ≫ (Y.homOfLE hUV).appTop) s
  congr 1
  simp only [Scheme.Opens.topIso_inv, Scheme.homOfLE_appTop]
  congr 1
  exact (Y.presheaf.map_comp _ _).symm.trans
    ((congrArg (fun g => Y.presheaf.map g) (Subsingleton.elim _ _)).trans
      (Y.presheaf.map_comp _ _))

lemma functionsOnOpenEquiv_naturality (s : Γ(Y,j.opensRange)) :
    functionsOnOpenEquiv j' (Y.presheaf.map (homOfLE (opensRange_le j j' θ h)).op s) =
      θ (functionsOnOpenEquiv j s) := by
  change chartFunctionsEquiv j' (j'.opensRange.topIso.inv
    (Y.presheaf.map (homOfLE (opensRange_le j j' θ h)).op s)) =
      θ (chartFunctionsEquiv j (j.opensRange.topIso.inv s))
  rw [topIso_restriction]
  exact chartFunctions_naturality j j' θ h _

end Functions

variable {R A : Type} [CommRing R] [CommRing A] {Y : Scheme}

theorem restrictedInclusion_value (L : LineBundle Y) (ι : L.sheaf ⟶ O Y)
    (U : Y.Opens) (s : Γ(L.sheaf, U)) :
    (PiExponentSeshadri.InvertibleLocal.restrictedInclusion L ι U.ι).app ⊤
      ((restrictionSectionsIso U L.sheaf).inv s) = U.topIso.inv (ι.app U s) := by
  change (U.ι.appIso ⊤).hom
    (ι.app (U.ι ''ᵁ ⊤) (L.sheaf.presheaf.map (eqToHom U.ι_image_top).op s)) = _
  rw [Scheme.Opens.ι_appIso]
  change ι.app (U.ι ''ᵁ ⊤) (L.sheaf.presheaf.map (eqToHom U.ι_image_top).op s) =
    Y.presheaf.map (eqToHom U.ι_image_top).op (ι.app U s)
  exact CategoryTheory.congr_fun (ι.mapPresheaf.naturality (eqToHom U.ι_image_top).op) s

variable (I : Ideal R) (f : Y ⟶ Spec (CommRingCat.of R))
  (j : Spec (CommRingCat.of A) ⟶ Y) [IsOpenImmersion j]
  (φ : R →+* A) (hf : j ≫ f = Spec.map (CommRingCat.ofHom φ))
  (L : LineBundle Y) (ι : L.sheaf ⟶ O Y)
  (hL : PresentsPullbackIdeal (specIdeal I) f L ι)
  (e : L.sheaf.restrict (chartOpen j).1.ι ≅ O (chartOpen j).1.toScheme)

def sectionsOnOpenEquiv (n : ℕ) :
    Γ((L.pow n).sheaf, j.opensRange) ≃+ ↥((I^n).map φ) :=
  (restrictionSectionsIso (chartOpen j).1 (L.pow n).sheaf).addCommGroupIsoToAddEquiv.symm.trans
    (sectionsEquiv I f j φ hf L ι hL e n)

theorem sectionsOnOpenEquiv_apply (n : ℕ) (s : Γ((L.pow n).sheaf, j.opensRange)) :
    (sectionsOnOpenEquiv I f j φ hf L ι hL e n s).val =
      chartFunctionsEquiv j ((chartOpen j).1.topIso.inv
        ((idealPowerInclusion L ι n).app j.opensRange s)) := by
  change (sectionsEquiv I f j φ hf L ι hL e n
    ((restrictionSectionsIso (chartOpen j).1 (L.pow n).sheaf).inv s)).val = _
  erw [sectionsEquiv_apply]
  exact congrArg (chartFunctionsEquiv j)
    (restrictedInclusion_value (L.pow n) (idealPowerInclusion L ι n) (chartOpen j).1 s)

def representedSectionsEquiv (n : ℕ) :
    (schemeFreeOpen Y j.opensRange ⟶ (L.pow n).sheaf) ≃+ ↥((I^n).map φ) :=
  ({ freeOpenEquiv Y.ringCatSheaf (L.pow n).sheaf j.opensRange with
      map_add' := fun _ _ => rfl } :
      (schemeFreeOpen Y j.opensRange ⟶ (L.pow n).sheaf) ≃+
        Γ((L.pow n).sheaf, j.opensRange)).trans
    (sectionsOnOpenEquiv I f j φ hf L ι hL e n)

variable {B : Type} [CommRing B]
  (j' : Spec (CommRingCat.of B) ⟶ Y) [IsOpenImmersion j']
  (θ : A →+* B) (h : Spec.map (CommRingCat.ofHom θ) ≫ j = j')
  (φ' : R →+* B) (hf' : j' ≫ f = Spec.map (CommRingCat.ofHom φ'))
  (e' : L.sheaf.restrict (chartOpen j').1.ι ≅ O (chartOpen j').1.toScheme)

theorem sectionsOnOpenEquiv_restrict (n : ℕ) (s : Γ((L.pow n).sheaf, j.opensRange)) :
    (sectionsOnOpenEquiv I f j' φ' hf' L ι hL e' n
      ((L.pow n).sheaf.presheaf.map (homOfLE (opensRange_le j j' θ h)).op s)).val =
      θ (sectionsOnOpenEquiv I f j φ hf L ι hL e n s).val := by
  rw [sectionsOnOpenEquiv_apply, sectionsOnOpenEquiv_apply]
  have hn := CategoryTheory.congr_fun
    ((idealPowerInclusion L ι n).mapPresheaf.naturality
      (homOfLE (opensRange_le j j' θ h)).op) s
  change (idealPowerInclusion L ι n).app j'.opensRange
      ((L.pow n).sheaf.presheaf.map (homOfLE (opensRange_le j j' θ h)).op s) =
    Y.presheaf.map (homOfLE (opensRange_le j j' θ h)).op
      ((idealPowerInclusion L ι n).app j.opensRange s) at hn
  rw [hn]
  exact functionsOnOpenEquiv_naturality j j' θ h _

theorem representedSectionsEquiv_restrict (n : ℕ)
    (s : schemeFreeOpen Y j.opensRange ⟶ (L.pow n).sheaf) :
    (representedSectionsEquiv I f j' φ' hf' L ι hL e' n
      (freeOpenMap Y.ringCatSheaf (homOfLE (opensRange_le j j' θ h)) ≫ s)).val =
      θ (representedSectionsEquiv I f j φ hf L ι hL e n s).val := by
  change (sectionsOnOpenEquiv I f j' φ' hf' L ι hL e' n
    (freeOpenEquiv Y.ringCatSheaf (L.pow n).sheaf j'.opensRange
      (freeOpenMap Y.ringCatSheaf (homOfLE (opensRange_le j j' θ h)) ≫ s))).val = _
  erw [freeOpenEquiv_naturality]
  exact sectionsOnOpenEquiv_restrict I f j φ hf L ι hL e j' θ h φ' hf' e' n _

end
end PiExponent.ExceptionalAffineChart

end OAI
end Source0758

-- Source: OAI/NumberTheory/PiExponent/Ampleness/ExceptionalRepresentedValue.lean
section Source0759
/-
Modification notice for the LogTwo project.
Derived from openai/math (Apache-2.0), revision adc7f1241b42e322a6451854ab7e4b4c146bf78a.
Original source: lean/OAI/NumberTheory/PiExponent/Ampleness/ExceptionalRepresentedValue.lean
Changes: Convert module/import declarations to the Lean 4.34 public module format.
See ../THIRD_PARTY_NOTICES.txt for provenance and the recorded changes.
-/

namespace OAI

namespace PiExponent.ExceptionalAffineChart
noncomputable section
open CategoryTheory AlgebraicGeometry
open PiExponentSeshadri.Geometry PiExponentSeshadri.Frames
open PiExponentSeshadri.ModuleFlasque PiExponentSeshadri.IdealPullback
variable {R A : Type} [CommRing R] [CommRing A] {Y : Scheme}
variable (I : Ideal R) (f : Y ⟶ Spec (CommRingCat.of R))
  (j : Spec (CommRingCat.of A) ⟶ Y) [IsOpenImmersion j]
  (φ : R →+* A) (hf : j ≫ f = Spec.map (CommRingCat.ofHom φ))
  (L : LineBundle Y) (ι : L.sheaf ⟶ O Y)
  (hL : PresentsPullbackIdeal (specIdeal I) f L ι)
  (e : L.sheaf.restrict (chartOpen j).1.ι ≅ O (chartOpen j).1.toScheme)

theorem representedSectionsEquiv_apply (n : ℕ)
    (b : freeOpen Y.ringCatSheaf j.opensRange ⟶ (L.pow n).sheaf) :
    (representedSectionsEquiv I f j φ hf L ι hL e n b).val =
      functionsOnOpenEquiv j
        ((idealPowerInclusion L ι n).app j.opensRange
          (freeOpenEquiv Y.ringCatSheaf (L.pow n).sheaf j.opensRange b)) := by
  exact sectionsOnOpenEquiv_apply I f j φ hf L ι hL e n _

end
end PiExponent.ExceptionalAffineChart

end OAI
end Source0759

-- Source: OAI/NumberTheory/PiExponent/Ampleness/ExceptionalChartPullbackValue.lean
section Source0760
/-
Modification notice for the LogTwo project.
Derived from openai/math (Apache-2.0), revision adc7f1241b42e322a6451854ab7e4b4c146bf78a.
Original source: lean/OAI/NumberTheory/PiExponent/Ampleness/ExceptionalChartPullbackValue.lean
Changes: Convert module/import declarations to the Lean 4.34 public module format.
See ../THIRD_PARTY_NOTICES.txt for provenance and the recorded changes.
-/

namespace OAI

namespace PiExponent.ExceptionalAffineChart
noncomputable section
open CategoryTheory AlgebraicGeometry TopologicalSpace
variable {R A : Type} [CommRing R] [CommRing A] {Y : Scheme}

theorem functionsOnOpenEquiv_global
    (j : Spec (CommRingCat.of A) ⟶ Y) [IsOpenImmersion j] (s : Γ(Y, ⊤)) :
    functionsOnOpenEquiv j (Y.presheaf.map (homOfLE le_top).op s) =
      (Scheme.ΓSpecIso (CommRingCat.of A)).hom (j.appTop s) := by
  change (Scheme.ΓSpecIso (CommRingCat.of A)).hom
    (j.isoOpensRange.hom.appTop
      (j.opensRange.topIso.inv (Y.presheaf.map (homOfLE le_top).op s))) = _
  have ht : j.opensRange.topIso.inv (Y.presheaf.map (homOfLE le_top).op s) =
      j.opensRange.ι.appTop s := by
    change (Y.presheaf.map (homOfLE le_top).op ≫
      j.opensRange.topIso.inv) s = _
    simp only [Scheme.Opens.topIso_inv]
    erw [← Functor.map_comp, ← op_comp]
    rfl
  rw [ht]
  have hj := congrArg (fun f => f.appTop) j.isoOpensRange_hom_ι
  rw [Scheme.Hom.comp_appTop] at hj
  exact congrArg (fun f => (Scheme.ΓSpecIso (CommRingCat.of A)).hom (f s)) hj

theorem functionsOnOpenEquiv_pullback
    (f : Y ⟶ Spec (CommRingCat.of R))
    (j : Spec (CommRingCat.of A) ⟶ Y) [IsOpenImmersion j]
    (φ : R →+* A) (hf : j ≫ f = Spec.map (CommRingCat.ofHom φ)) (r : R) :
    functionsOnOpenEquiv j (Y.presheaf.map (homOfLE le_top).op
      (f.appTop ((Scheme.ΓSpecIso (CommRingCat.of R)).inv r))) = φ r := by
  rw [functionsOnOpenEquiv_global]
  have h := congrArg (fun g => g.appTop) hf
  rw [Scheme.Hom.comp_appTop] at h
  have hv := congrArg (fun g => (Scheme.ΓSpecIso (CommRingCat.of A)).hom
    (g ((Scheme.ΓSpecIso (CommRingCat.of R)).inv r))) h
  refine hv.trans ?_
  have hn := CategoryTheory.congr_fun
    (Scheme.ΓSpecIso_naturality (CommRingCat.ofHom φ))
      ((Scheme.ΓSpecIso (CommRingCat.of R)).inv r)
  change (Scheme.ΓSpecIso (CommRingCat.of A)).hom
      ((Spec.map (CommRingCat.ofHom φ)).appTop
        ((Scheme.ΓSpecIso (CommRingCat.of R)).inv r)) =
    φ ((Scheme.ΓSpecIso (CommRingCat.of R)).hom
      ((Scheme.ΓSpecIso (CommRingCat.of R)).inv r)) at hn
  exact hn.trans (congrArg φ
    (CategoryTheory.congr_fun (Scheme.ΓSpecIso (CommRingCat.of R)).inv_hom_id r))

end
end PiExponent.ExceptionalAffineChart

end OAI
end Source0760

-- Source: OAI/NumberTheory/PiExponent/Ampleness/ExceptionalRepresentedOpaque.lean
section Source0761
/-
Modification notice for the LogTwo project.
Derived from openai/math (Apache-2.0), revision adc7f1241b42e322a6451854ab7e4b4c146bf78a.
Original source: lean/OAI/NumberTheory/PiExponent/Ampleness/ExceptionalRepresentedOpaque.lean
Changes: Convert module/import declarations to the Lean 4.34 public module format.
Expose private helpers and adjust helper names where needed for module compatibility.
See ../THIRD_PARTY_NOTICES.txt for provenance and the recorded changes.
-/

namespace OAI

namespace PiExponent.ExceptionalAffineChart
noncomputable section
open CategoryTheory AlgebraicGeometry
open PiExponentSeshadri.Geometry PiExponentSeshadri.Frames
open PiExponentSeshadri.ModuleFlasque PiExponentSeshadri.IdealPullback
abbrev exceptionalOpaqueFreeOpen (Y : Scheme) (U : Y.Opens) : Y.Modules :=
  freeOpen Y.ringCatSheaf U

variable {R A : Type} [CommRing R] [CommRing A] {Y : Scheme}
variable (I : Ideal R) (f : Y ⟶ Spec (CommRingCat.of R))
  (j : Spec (CommRingCat.of A) ⟶ Y) [IsOpenImmersion j]
  (φ : R →+* A) (hf : j ≫ f = Spec.map (CommRingCat.ofHom φ))
  (L : LineBundle Y) (ι : L.sheaf ⟶ O Y)
  (hL : PresentsPullbackIdeal (specIdeal I) f L ι)
  (e : L.sheaf.restrict (chartOpen j).1.ι ≅ O (chartOpen j).1.toScheme)

theorem exists_representedSectionsOpaque (n : ℕ) :
    ∃ E : (exceptionalOpaqueFreeOpen Y j.opensRange ⟶ (L.pow n).sheaf) ≃+
      ↥((I^n).map φ), E = representedSectionsEquiv I f j φ hf L ι hL e n :=
  ⟨_, rfl⟩

def representedSectionsOpaque (n : ℕ) :
    (exceptionalOpaqueFreeOpen Y j.opensRange ⟶ (L.pow n).sheaf) ≃+ ↥((I^n).map φ) :=
  (exists_representedSectionsOpaque I f j φ hf L ι hL e n).choose

theorem representedSectionsOpaque_eq (n : ℕ) :
    representedSectionsOpaque I f j φ hf L ι hL e n =
      representedSectionsEquiv I f j φ hf L ι hL e n :=
  (exists_representedSectionsOpaque I f j φ hf L ι hL e n).choose_spec

theorem representedSectionsOpaque_apply (n : ℕ)
    (b : exceptionalOpaqueFreeOpen Y j.opensRange ⟶ (L.pow n).sheaf) :
    representedSectionsOpaque I f j φ hf L ι hL e n b =
      representedSectionsEquiv I f j φ hf L ι hL e n b :=
  congrArg (fun E => E b) (representedSectionsOpaque_eq I f j φ hf L ι hL e n)

end
end PiExponent.ExceptionalAffineChart

end OAI
end Source0761

-- Source: OAI/NumberTheory/PiExponent/Ampleness/ExceptionalRepresentedTypes.lean
section Source0762
/-
Modification notice for the LogTwo project.
Derived from openai/math (Apache-2.0), revision adc7f1241b42e322a6451854ab7e4b4c146bf78a.
Original source: lean/OAI/NumberTheory/PiExponent/Ampleness/ExceptionalRepresentedTypes.lean
Changes: Convert module/import declarations to the Lean 4.34 public module format.
See ../THIRD_PARTY_NOTICES.txt for provenance and the recorded changes.
-/

namespace OAI

namespace PiExponent.ExceptionalRepresentedTypes
noncomputable section
open CategoryTheory AlgebraicGeometry
open PiExponentSeshadri.Geometry PiExponentSeshadri.Frames
open PiExponentSeshadri.ModuleFlasque PiExponentSeshadri.IdealPullback
variable {R A : Type} [CommRing R] [CommRing A] {Y : Scheme}

def Frame (j : Spec (CommRingCat.of A) ⟶ Y) [IsOpenImmersion j]
    (L : LineBundle Y) : Type :=
  L.sheaf.restrict (ExceptionalAffineChart.chartOpen j).1.ι ≅
    O (ExceptionalAffineChart.chartOpen j).1.toScheme

def Sections (j : Spec (CommRingCat.of A) ⟶ Y) [IsOpenImmersion j]
    (L : LineBundle Y) (n : ℕ) : Type :=
  freeOpen Y.ringCatSheaf j.opensRange ⟶ (L.pow n).sheaf

instance (j : Spec (CommRingCat.of A) ⟶ Y) [IsOpenImmersion j]
    (L : LineBundle Y) (n : ℕ) : AddCommGroup (Sections j L n) :=
  Preadditive.homGroup (C := Y.Modules)
    (freeOpen Y.ringCatSheaf j.opensRange) (L.pow n).sheaf

variable (I : Ideal R) (f : Y ⟶ Spec (CommRingCat.of R))
  (j : Spec (CommRingCat.of A) ⟶ Y) [IsOpenImmersion j]
  (φ : R →+* A) (hf : j ≫ f = Spec.map (CommRingCat.ofHom φ))
  (L : LineBundle Y) (ι : L.sheaf ⟶ O Y)
  (hL : PresentsPullbackIdeal (specIdeal I) f L ι)
  (e : Frame j L)

def representedSectionsTyped (n : ℕ) : Sections j L n ≃+ ↥((I^n).map φ) :=
  ExceptionalAffineChart.representedSectionsOpaque I f j φ hf L ι hL e n

theorem representedSectionsTyped_apply (n : ℕ) (b : Sections j L n) :
    representedSectionsTyped I f j φ hf L ι hL e n b =
      ExceptionalAffineChart.representedSectionsEquiv I f j φ hf L ι hL e n b :=
  ExceptionalAffineChart.representedSectionsOpaque_apply I f j φ hf L ι hL e n b

end
end PiExponent.ExceptionalRepresentedTypes

end OAI
end Source0762

-- Source: OAI/NumberTheory/PiExponent/Ampleness/ExceptionalTypedTransport.lean
section Source0763
-- Modified in this edition: unused plain lemmas removed; see reduction.json.
/-
Modification notice for the LogTwo project.
Derived from openai/math (Apache-2.0), revision adc7f1241b42e322a6451854ab7e4b4c146bf78a.
Original source: lean/OAI/NumberTheory/PiExponent/Ampleness/ExceptionalTypedTransport.lean
Changes: Convert module/import declarations to the Lean 4.34 public module format.
Expose private helpers and adjust helper names where needed for module compatibility.
See ../THIRD_PARTY_NOTICES.txt for provenance and the recorded changes.
-/

namespace OAI

namespace PiExponent.ExceptionalRepresentedTypes
noncomputable section
open CategoryTheory AlgebraicGeometry
open PiExponentSeshadri.Geometry PiExponentSeshadri.Frames
open PiExponentSeshadri.ModuleFlasque
abbrev schemeFreeOpen (Y : Scheme) (U : Y.Opens) : Y.Modules :=
  freeOpen Y.ringCatSheaf U

variable {A : Type} [CommRing A] {Y : Scheme}
variable (j : Spec (CommRingCat.of A) ⟶ Y) [IsOpenImmersion j]
  (L : LineBundle Y)

theorem frame_nonempty_of_open {U : Y.Opens} (h : U = j.opensRange)
    (he : Nonempty (L.sheaf.restrict U.ι ≅ O U.toScheme)) :
    Nonempty (Frame j L) := by
  subst U
  exact he

def transportSections (n : ℕ) {V : Y.Opens} (h : j.opensRange = V) :
    (schemeFreeOpen Y V ⟶ (L.pow n).sheaf) ≃+ Sections j L n where
  toFun b := freeOpenMap Y.ringCatSheaf (eqToHom h) ≫ b
  invFun b := freeOpenMap Y.ringCatSheaf (eqToHom h.symm) ≫ b
  left_inv b := by
    subst V
    simp [freeOpenMap]
    exact (Category.id_comp _).trans (Category.id_comp b)
  right_inv b := by
    subst V
    simp [freeOpenMap]
    exact (Category.id_comp _).trans (Category.id_comp b)
  map_add' b c := Preadditive.comp_add _ _ _ _ b c

end
end PiExponent.ExceptionalRepresentedTypes

end OAI
end Source0763

-- Source: OAI/NumberTheory/PiExponent/Polynomials/ShiftedFreeGrading.lean
section Source0764
/-
Modification notice for the LogTwo project.
Derived from openai/math (Apache-2.0), revision adc7f1241b42e322a6451854ab7e4b4c146bf78a.
Original source: lean/OAI/NumberTheory/PiExponent/Polynomials/ShiftedFreeGrading.lean
Changes: Convert module/import declarations to the Lean 4.34 public module format.
See ../THIRD_PARTY_NOTICES.txt for provenance and the recorded changes.
-/

namespace OAI

namespace PiExponent.ShiftedFreeGrading
noncomputable section
open scoped BigOperators
open DirectSum
variable {A J σA : Type*} [AddCommGroup A] [Fintype J]
  [SetLike σA A] [AddSubgroupClass σA A]
  (𝒜 : ℤ → σA) [DirectSum.Decomposition 𝒜] (w : J → ℤ)

def piece (d : ℤ) : AddSubgroup (J → A) where
  carrier := {f | ∀ j, f j ∈ 𝒜 (d - w j)}
  zero_mem' := fun _j => zero_mem _
  add_mem' := fun hf hg j => add_mem (hf j) (hg j)
  neg_mem' := fun hf j => neg_mem (hf j)

def component (f : J → A) (d : ℤ) : piece 𝒜 w d :=
  ⟨fun j => (DirectSum.decompose 𝒜 (f j) (d - w j) : A),
    fun j => (DirectSum.decompose 𝒜 (f j) (d - w j)).property⟩

def support (f : J → A) : Finset ℤ := by
  classical
  exact Finset.univ.biUnion fun j =>
    (DirectSum.decompose 𝒜 (f j)).support.image (fun d => d + w j)

theorem component_eq_zero_of_not_mem (f : J → A) (d : ℤ)
    (hd : d ∉ support 𝒜 w f) : component 𝒜 w f d = 0 := by
  classical
  apply Subtype.ext
  funext j
  change (DirectSum.decompose 𝒜 (f j) (d - w j) : A) = 0
  have hh : d - w j ∉ (DirectSum.decompose 𝒜 (f j)).support := by
    intro h
    apply hd
    exact Finset.mem_biUnion.mpr ⟨j, Finset.mem_univ _,
      Finset.mem_image.mpr ⟨d - w j, h, sub_add_cancel _ _⟩⟩
  rw [DFinsupp.notMem_support_iff.mp hh]
  rfl

def decompositionMap : (J → A) →+ ⨁ d, piece 𝒜 w d where
  toFun f := DFinsupp.mk' (component 𝒜 w f)
    (Trunc.mk ⟨(support 𝒜 w f).val, fun d => by
      classical
      by_cases hd : d ∈ support 𝒜 w f
      · exact Or.inl hd
      · exact Or.inr (component_eq_zero_of_not_mem 𝒜 w f d hd)⟩)
  map_zero' := by
    ext d j
    change (DirectSum.decompose 𝒜 (0 : A) (d - w j) : A) = 0
    rw [DirectSum.decompose_zero]
    rfl
  map_add' f g := by
    ext d j
    change (DirectSum.decompose 𝒜 (f j + g j) (d - w j) : A) =
      (DirectSum.decompose 𝒜 (f j) (d - w j) : A) +
      (DirectSum.decompose 𝒜 (g j) (d - w j) : A)
    rw [DirectSum.decompose_add]
    rfl

@[simp] theorem decompositionMap_apply (f : J → A) (d : ℤ) (j : J) :
    (decompositionMap 𝒜 w f d : J → A) j =
      (DirectSum.decompose 𝒜 (f j) (d - w j) : A) := rfl

theorem decompositionMap_injective : Function.Injective (decompositionMap 𝒜 w) := by
  intro f g h
  funext j
  apply (DirectSum.decompose 𝒜).injective
  ext d
  have hh := congrArg (fun z : ⨁ d, piece 𝒜 w d => (z (d + w j) : J → A) j) h
  change (DirectSum.decompose 𝒜 (f j) (d + w j - w j) : A) =
    (DirectSum.decompose 𝒜 (g j) (d + w j - w j) : A) at hh
  rw [show d + w j - w j = d by omega] at hh
  exact hh

theorem decompositionMap_homogeneous (d : ℤ) (f : piece 𝒜 w d) :
    decompositionMap 𝒜 w f.val = DirectSum.of (fun d => piece 𝒜 w d) d f := by
  classical
  ext e j
  by_cases he : d = e
  · subst e
    rw [DirectSum.of_eq_same]
    exact DirectSum.decompose_of_mem_same 𝒜 (f.property j)
  · rw [DirectSum.of_eq_of_ne _ _ _ (Ne.symm he)]
    change (DirectSum.decompose 𝒜 (f.val j) (e - w j) : A) = 0
    exact DirectSum.decompose_of_mem_ne 𝒜 (f.property j) (by omega)

instance decomposition : DirectSum.Decomposition (piece 𝒜 w) := by
  classical
  have hr : (decompositionMap 𝒜 w).comp (DirectSum.coeAddMonoidHom (piece 𝒜 w)) =
      AddMonoidHom.id _ := by
    apply DirectSum.addHom_ext
    intro d f
    simp only [AddMonoidHom.comp_apply, DirectSum.coeAddMonoidHom_of,
      AddMonoidHom.id_apply, decompositionMap_homogeneous]
  apply DirectSum.Decomposition.ofAddHom (piece 𝒜 w) (decompositionMap 𝒜 w) ?_ hr
  apply AddMonoidHom.ext
  intro f
  apply decompositionMap_injective 𝒜 w
  exact DFunLike.congr_fun hr (decompositionMap 𝒜 w f)

@[simp] theorem decompose_apply (f : J → A) (d : ℤ) (j : J) :
    (DirectSum.decompose (piece 𝒜 w) f d : J → A) j =
      (DirectSum.decompose 𝒜 (f j) (d - w j) : A) := rfl

end
end PiExponent.ShiftedFreeGrading

end OAI
end Source0764

-- Source: OAI/NumberTheory/PiExponent/Polynomials/GradedSerre.lean
section Source0765
-- Modified in this edition: unused plain lemmas removed; see reduction.json.
/-
Modification notice for the LogTwo project.
Derived from openai/math (Apache-2.0), revision adc7f1241b42e322a6451854ab7e4b4c146bf78a.
Original source: lean/OAI/NumberTheory/PiExponent/Polynomials/GradedSerre.lean
Changes: Convert module/import declarations to the Lean 4.34 public module format.
See ../THIRD_PARTY_NOTICES.txt for provenance and the recorded changes.
-/

namespace OAI

namespace PiExponent.GradedSerre

noncomputable section
open scoped BigOperators

variable {R M ι σ : Type*} [Ring R] [AddCommGroup M] [Module R M]
  [DecidableEq ι] [SetLike σ M] [AddSubmonoidClass σ M]
  (𝓜 : ι → σ) [DirectSum.Decomposition 𝓜]

theorem span_homogeneous_eq (K : Submodule R M) (hK : K.IsHomogeneous 𝓜) :
    Submodule.span R {x : M | x ∈ K ∧ ∃ d, x ∈ 𝓜 d} = K := by
  classical
  apply le_antisymm
  · exact Submodule.span_le.mpr (fun x hx => hx.1)
  · intro x hx
    rw [← DirectSum.sum_support_decompose 𝓜 x]
    apply Submodule.sum_mem
    intro d hd
    exact Submodule.subset_span ⟨hK d hx, d, (DirectSum.decompose 𝓜 x d).property⟩

theorem exists_finite_homogeneous_generators (K : Submodule R M)
    (hK : K.IsHomogeneous 𝓜) (hfg : K.FG) :
    ∃ (s : Finset M) (degree : s → ι),
      (∀ j : s, j.val ∈ K ∧ j.val ∈ 𝓜 (degree j)) ∧
      Submodule.span R (s : Set M) = K := by
  classical
  have hspan := span_homogeneous_eq 𝓜 K hK
  have hfg' : (Submodule.span R {x : M | x ∈ K ∧ ∃ d, x ∈ 𝓜 d}).FG := by
    rwa [hspan]
  obtain ⟨s, hs, hspan'⟩ :=
    (Submodule.fg_span_iff_fg_span_finset_subset _).mp hfg'
  have hdegree : ∀ j : s, ∃ d, j.val ∈ K ∧ j.val ∈ 𝓜 d := by
    intro j
    obtain ⟨hj, d, hd⟩ := hs j.property
    exact ⟨d, hj, hd⟩
  choose degree hdegree using hdegree
  exact ⟨s, degree, hdegree, hspan'.symm.trans hspan⟩

theorem kernel_homogeneous
    {N τ : Type*} [AddCommMonoid N] [Module R N]
    [SetLike τ N] [AddSubmonoidClass τ N]
    (𝓝 : ι → τ) [DirectSum.Decomposition 𝓝]
    (f : M →ₗ[R] N)
    (hf : ∀ d x, f (DirectSum.decompose 𝓜 x d : M) =
      (DirectSum.decompose 𝓝 (f x) d : N)) :
    f.ker.IsHomogeneous 𝓜 := by
  intro d x hx
  change f (DirectSum.decompose 𝓜 x d : M) = 0
  rw [hf, LinearMap.mem_ker.mp hx, DirectSum.decompose_zero]
  rfl

section IntegerGrading
variable {A P σA σP : Type*} [Ring A] [AddCommGroup P] [Module A P]
  [SetLike σA A] [AddSubgroupClass σA A]
  [SetLike σP P] [AddSubgroupClass σP P]
  (𝒜 : ℤ → σA) (𝓟 : ℤ → σP)
  [DirectSum.Decomposition 𝒜] [DirectSum.Decomposition 𝓟]
  [SetLike.GradedSMul 𝒜 𝓟]

theorem decompose_smul_homogeneous {m : P} {w : ℤ} (hm : m ∈ 𝓟 w)
    (a : A) (d : ℤ) :
    (DirectSum.decompose 𝓟 (a • m) d : P) =
      (DirectSum.decompose 𝒜 a (d - w) : A) • m := by
  induction a using DirectSum.Decomposition.inductionOn 𝒜 with
  | zero => simp
  | homogeneous a =>
      rename_i k
      have ham : (a : A) • m ∈ 𝓟 (k + w) :=
        SetLike.GradedSMul.smul_mem a.property hm
      by_cases h : k + w = d
      · have hk : k = d - w := by omega
        rw [← h, DirectSum.decompose_of_mem_same 𝓟 ham]
        rw [show k + w - w = k by omega, DirectSum.decompose_of_mem_same 𝒜 a.property]
      · rw [DirectSum.decompose_of_mem_ne 𝓟 ham h,
          DirectSum.decompose_of_mem_ne 𝒜 a.property (by omega), zero_smul]
  | add a b ha hb =>
      simp only [add_smul, DirectSum.decompose_add, DirectSum.add_apply, AddMemClass.coe_add]
      rw [ha, hb]

theorem free_cover_degree_compatible {J : Type*} [Fintype J]
    (w : J → ℤ) (v : J → P) (hv : ∀ j, v j ∈ 𝓟 (w j))
    (d : ℤ) (a : J → A) :
    Fintype.linearCombination A v
        (DirectSum.decompose (ShiftedFreeGrading.piece 𝒜 w) a d : J → A) =
      (DirectSum.decompose 𝓟 (Fintype.linearCombination A v a) d : P) := by
  classical
  simp only [Fintype.linearCombination_apply, DirectSum.decompose_sum,
    DirectSum.sum_apply, AddSubmonoidClass.coe_finsetSum]
  apply Finset.sum_congr rfl
  intro j hj
  rw [ShiftedFreeGrading.decompose_apply]
  exact (decompose_smul_homogeneous 𝒜 𝓟 (hv j) (a j) d).symm

theorem exists_graded_free_map (K : Submodule A P) (hK : K.IsHomogeneous 𝓟)
    (hfg : K.FG) :
    ∃ (n : ℕ) (w : Fin n → ℤ) (f : (Fin n → A) →ₗ[A] P),
      LinearMap.range f = K ∧
      ∀ d x, f (DirectSum.decompose (ShiftedFreeGrading.piece 𝒜 w) x d : Fin n → A) =
        (DirectSum.decompose 𝓟 (f x) d : P) := by
  classical
  obtain ⟨s, degree, hs, hspan⟩ := exists_finite_homogeneous_generators 𝓟 K hK hfg
  let e : s ≃ Fin s.card := s.equivFin
  let v : Fin s.card → P := fun j => (e.symm j).val
  let w : Fin s.card → ℤ := fun j => degree (e.symm j)
  refine ⟨s.card, w, Fintype.linearCombination A v, ?_, ?_⟩
  · rw [Fintype.range_linearCombination]
    have hv : Set.range v = (s : Set P) := by
      ext x
      constructor
      · rintro ⟨j, rfl⟩
        exact (e.symm j).property
      · intro hx
        refine ⟨e ⟨x, hx⟩, ?_⟩
        simp only [v, Equiv.symm_apply_apply]
    rw [hv]
    exact hspan
  · exact free_cover_degree_compatible 𝒜 𝓟 w v (fun j => (hs (e.symm j)).2)

instance shiftedFreeGradedSMul [SetLike.GradedMonoid 𝒜] {J : Type*} [Fintype J]
    (w : J → ℤ) : SetLike.GradedSMul 𝒜 (ShiftedFreeGrading.piece 𝒜 w) where
  smul_mem := by
    intro i d a f ha hf j
    change a * f j ∈ 𝒜 (i + d - w j)
    have h : a * f j ∈ 𝒜 (i + (d - w j)) :=
      SetLike.GradedMul.mul_mem ha (hf j)
    convert h using 1
    congr 1
    omega

end IntegerGrading

section FreeTwistCech
open ProjectiveMonomialCech ProjectiveMonomialCechHigher
variable {J C B : Type*} [Fintype J] [Fintype C] [AddCommGroup B]

theorem compatible_vertices_are_polynomial [Nonempty C] {d : ℤ} (hd : 0 ≤ d)
    (c : C → Laurent C B d) (hc : ∀ j, RegularOn {j} (c j))
    (heq : ∀ i j, c i = c j) :
    ∃ f : Laurent C B d, RegularOn ∅ f ∧ ∀ j, c j = f := by
  classical
  let p : C := Classical.choice inferInstance
  refine ⟨c p, ?_, fun j => heq j p⟩
  intro a ha k hk
  obtain ⟨j, hj⟩ := exists_nonnegative_coordinate hd a
  have hcoeff : c j a ≠ 0 := by rw [heq j p]; exact ha
  have hkj := hc j a hcoeff k hk
  have hkj' : k = j := hkj
  exact False.elim ((not_lt_of_ge hj) (hkj' ▸ hk))

end FreeTwistCech

end
end PiExponent.GradedSerre

end OAI
end Source0765

-- Source: OAI/NumberTheory/PiExponent/Ampleness/ReesPolynomialPresentation.lean
section Source0766
-- Modified in this edition: unused plain lemmas removed; see reduction.json.
/-
Modification notice for the LogTwo project.
Derived from openai/math (Apache-2.0), revision adc7f1241b42e322a6451854ab7e4b4c146bf78a.
Original source: lean/OAI/NumberTheory/PiExponent/Ampleness/ReesPolynomialPresentation.lean
Changes: Convert module/import declarations to the Lean 4.34 public module format.
See ../THIRD_PARTY_NOTICES.txt for provenance and the recorded changes.
-/

namespace OAI

namespace PiExponent.ReesPolynomialPresentation
noncomputable section
open scoped BigOperators
open Polynomial PiExponentSeshadri.ReesGrading
variable {R J : Type*} [CommRing R] (I : Ideal R) (a : J → I)

def presentation : MvPolynomial J R →ₐ[R] reesAlgebra I :=
  MvPolynomial.aeval (fun j => generator I (a j))

@[simp] theorem presentation_X (j : J) : presentation I a (MvPolynomial.X j) = generator I (a j) :=
  MvPolynomial.aeval_X _ _

theorem presentation_monomial_mem (b : J →₀ ℕ) (r : R) :
    presentation I a (MvPolynomial.monomial b r) ∈ piece I b.degree := by
  classical
  rw [presentation, MvPolynomial.aeval_monomial]
  have hp : (∏ j ∈ b.support, generator I (a j) ^ b j) ∈ piece I b.degree := by
    have h := SetLike.prod_mem_graded (piece I) (fun j => b j)
      (fun j => generator I (a j) ^ b j) (F := b.support)
      (fun j _ => by simpa using SetLike.pow_mem_graded (b j) (generator_mem I (a j)))
    change (∏ j ∈ b.support, generator I (a j) ^ b j) ∈ piece I (∑ j ∈ b.support, b j)
    exact h
  have hr : algebraMap R (reesAlgebra I) r ∈ piece I 0 := by
    simp [mem_piece]
  simpa only [zero_add, Finsupp.prod] using SetLike.mul_mem_graded hr hp

theorem presentation_homogeneous_mem {n : ℕ} {p : MvPolynomial J R}
    (hp : p.IsHomogeneous n) : presentation I a p ∈ piece I n := by
  classical
  induction hp using MvPolynomial.IsWeightedHomogeneous.induction_on with
  | zero => simpa only [map_zero] using (piece I n).zero_mem
  | add p q hp hq ihp ihq => simpa only [map_add] using (piece I n).add_mem ihp ihq
  | monomial b r hb =>
      have hb' : b.degree = n := by rw [Finsupp.degree_eq_weight_one, ← Pi.one_def, hb]
      simpa only [hb'] using presentation_monomial_mem I a b r

theorem evaluation_presentation (p : MvPolynomial J R) :
    evaluation I (presentation I a p) = MvPolynomial.eval (fun j => (a j).val) p := by
  have h : (evaluation I).comp (presentation I a).toRingHom =
      (MvPolynomial.eval₂Hom (RingHom.id R) (fun j => (a j).val)) := by
    apply MvPolynomial.ringHom_ext
    · intro r
      simp [presentation, evaluation]
    · intro j
      simp [presentation, evaluation_generator]
  exact DFunLike.congr_fun h p

theorem homogeneous_piece_surjective
    (ha : Ideal.span (Set.range fun j => (a j).val) = I) (n : ℕ)
    (z : piece I n) :
    ∃ p : MvPolynomial J R, p.IsHomogeneous n ∧ presentation I a p = z.val := by
  have hz : (((z.val : reesAlgebra I) : R[X]).coeff n) ∈
      (Ideal.span (Set.range fun j => (a j).val)) ^ n := by
    rw [ha]
    exact z.val.property n
  obtain ⟨p, hp, heval⟩ := (Ideal.mem_span_pow_iff_exists_isHomogeneous
    (fun j => (a j).val) _).mp hz
  refine ⟨p, hp, ?_⟩
  have hmem := presentation_homogeneous_mem I a hp
  apply Subtype.ext
  rw [(mem_piece I n _).mp hmem, (mem_piece I n _).mp z.property]
  congr 1
  have h := evaluation_presentation I a p
  rw [evaluation, RingHom.comp_apply, AlgHom.toRingHom_eq_coe] at h
  change Polynomial.eval 1 ((presentation I a p : reesAlgebra I) : R[X]) = _ at h
  rw [(mem_piece I n _).mp hmem] at h
  simpa only [Polynomial.eval_monomial, one_pow, mul_one] using h.trans heval

theorem presentation_surjective
    (ha : Ideal.span (Set.range fun j => (a j).val) = I) :
    Function.Surjective (presentation I a) := by
  classical
  intro z
  have hn (n : ℕ) := homogeneous_piece_surjective I a ha n (component I n z)
  choose p hp hpres using hn
  refine ⟨∑ n ∈ ((z : reesAlgebra I) : R[X]).support, p n, ?_⟩
  rw [map_sum]
  simp_rw [hpres]
  apply Subtype.ext
  change (reesAlgebra I).val (∑ n ∈ ((z : reesAlgebra I) : R[X]).support,
    (component I n z).val) = (z : R[X])
  rw [map_sum]
  exact ((z : R[X]).as_sum_support).symm

@[instance_reducible]
def presentationAlgebra : Algebra (MvPolynomial J R) (reesAlgebra I) :=
  (presentation I a).toRingHom.toAlgebra

theorem finite_presented_module
    (ha : Ideal.span (Set.range fun j => (a j).val) = I) :
    letI := presentationAlgebra I a
    Module.Finite (MvPolynomial J R) (reesAlgebra I) := by
  let := presentationAlgebra I a
  exact Module.Finite.of_surjective
    (Algebra.linearMap (MvPolynomial J R) (reesAlgebra I)) (presentation_surjective I a ha)

end
end PiExponent.ReesPolynomialPresentation

end OAI
end Source0766

-- Source: OAI/NumberTheory/PiExponent/Ampleness/ReesFiniteCover.lean
section Source0767
/-
Modification notice for the LogTwo project.
Derived from openai/math (Apache-2.0), revision adc7f1241b42e322a6451854ab7e4b4c146bf78a.
Original source: lean/OAI/NumberTheory/PiExponent/Ampleness/ReesFiniteCover.lean
Changes: Convert module/import declarations to the Lean 4.34 public module format.
See ../THIRD_PARTY_NOTICES.txt for provenance and the recorded changes.
-/

namespace OAI

noncomputable section
open CategoryTheory AlgebraicGeometry TopologicalSpace
namespace PiExponent.ReesFiniteCover
open PiExponentSeshadri.ReesGrading
variable {R J : Type} [CommRing R] (I : Ideal R) (a : J → I)
variable (ha : Ideal.span (Set.range fun j => (a j).val) = I)
local instance chartOpenImmersion (j : J) : IsOpenImmersion ((chartCover I).f (a j)) :=
  (chartCover I).map_prop (a j)
include ha

theorem adjoin_eq_top : Algebra.adjoin R (Set.range fun j => generator I (a j)) = ⊤ := by
  rw [Algebra.adjoin_range_eq_range_aeval]
  apply top_unique
  intro z hz
  exact ReesPolynomialPresentation.presentation_surjective I a ha z

theorem adjoin_zero_eq_top :
    Algebra.adjoin (piece I 0) (Set.range fun j => generator I (a j)) = ⊤ := by
  apply top_unique
  intro z hz
  clear hz
  have hh : z ∈ Algebra.adjoin R (Set.range fun j => generator I (a j)) := by
    rw [adjoin_eq_top I a ha]
    trivial
  induction hh using Algebra.adjoin_induction with
  | mem x hx => exact Algebra.subset_adjoin hx
  | algebraMap r =>
    exact (Algebra.adjoin (piece I 0) (Set.range fun j => generator I (a j))).algebraMap_mem
      (zeroEquiv I r)
  | add x y _ _ hx hy => exact add_mem hx hy
  | mul x y _ _ hx hy => exact mul_mem hx hy

theorem iSup_generator_basicOpen :
    (⨆ j, Proj.basicOpen (piece I) (generator I (a j))) = ⊤ :=
  Proj.iSup_basicOpen_eq_top' (piece I) (fun j => generator I (a j))
    (fun j => ⟨1, generator_mem I (a j)⟩) (adjoin_zero_eq_top I a ha)

theorem iSup_generator_opensRange :
    (⨆ j, ((chartCover I).f (a j)).opensRange) = ⊤ := by
  have h j : ((chartCover I).f (a j)).opensRange =
      Proj.basicOpen (piece I) (generator I (a j)) :=
    Proj.opensRange_awayι (piece I) _ (generator_mem I (a j)) (by decide)
  simp_rw [h]
  exact iSup_generator_basicOpen I a ha

def cover : (affineBlowup I).AffineOpenCover where
  I₀ := J
  X j := CommRingCat.of (chart I (a j))
  f j := (chartCover I).f (a j)
  map_prop j := (chartCover I).map_prop (a j)
  idx x := (Opens.mem_iSup.mp ((iSup_generator_opensRange I a ha).ge (Set.mem_univ x))).choose
  covers x :=
    (Opens.mem_iSup.mp ((iSup_generator_opensRange I a ha).ge (Set.mem_univ x))).choose_spec

end PiExponent.ReesFiniteCover
end

end OAI
end Source0767

-- Source: OAI/NumberTheory/PiExponent/Ampleness/ReesExceptionalSheaf.lean
section Source0768
/-
Modification notice for the LogTwo project.
Derived from openai/math (Apache-2.0), revision adc7f1241b42e322a6451854ab7e4b4c146bf78a.
Original source: lean/OAI/NumberTheory/PiExponent/Ampleness/ReesExceptionalSheaf.lean
Changes: Convert module/import declarations to the Lean 4.34 public module format.
See ../THIRD_PARTY_NOTICES.txt for provenance and the recorded changes.
-/

namespace OAI

namespace PiExponentSeshadri.ReesGrading
noncomputable section
variable {R : Type} [CommRing R] (I : Ideal R)

theorem exceptionalLineBundle_sheaf_eq :
    (exceptionalLineBundle I).sheaf = IdealModule.closedModule (exceptionalIdeal I) := rfl

end
end PiExponentSeshadri.ReesGrading

end OAI
end Source0768

-- Source: OAI/NumberTheory/PiExponent/Polynomials/GradedLocalizationExact.lean
section Source0769
-- Modified in this edition: unused plain lemmas removed; see reduction.json.
/-
Modification notice for the LogTwo project.
Derived from openai/math (Apache-2.0), revision adc7f1241b42e322a6451854ab7e4b4c146bf78a.
Original source: lean/OAI/NumberTheory/PiExponent/Polynomials/GradedLocalizationExact.lean
Changes: Convert module/import declarations to the Lean 4.34 public module format.
See ../THIRD_PARTY_NOTICES.txt for provenance and the recorded changes.
-/

namespace OAI

namespace PiExponent.GradedLocalizationExact

noncomputable section

variable {R M N P σR σM σN σP : Type*}
  [CommRing R] [AddCommGroup M] [Module R M]
  [AddCommGroup N] [Module R N] [AddCommGroup P] [Module R P]
  [SetLike σR R]
  [SetLike σM M] [AddSubgroupClass σM M]
  [SetLike σN N] [AddSubgroupClass σN N]
  [SetLike σP P] [AddSubgroupClass σP P]

def powerDenominator (a : R) (n : ℕ) : Submonoid.powers a :=
  ⟨a ^ n, ⟨n, rfl⟩⟩

@[simp] theorem powerDenominator_val (a : R) (n : ℕ) :
    (powerDenominator a n : R) = a ^ n := rfl

@[simp] theorem powerDenominator_zero (a : R) : powerDenominator a 0 = 1 := by
  apply Subtype.ext
  simp [powerDenominator]

theorem powerDenominator_add (a : R) (n k : ℕ) :
    powerDenominator a (n + k) = powerDenominator a n * powerDenominator a k := by
  apply Subtype.ext
  exact pow_add a n k

def fraction (a : R) (m : M) (n : ℕ) : LocalizedModule (Submonoid.powers a) M :=
  LocalizedModule.mk m (powerDenominator a n)

@[simp] theorem fraction_zero (a : R) (n : ℕ) : fraction a (0 : M) n = 0 :=
  LocalizedModule.zero_mk _

@[simp] theorem fraction_neg (a : R) (m : M) (n : ℕ) :
    fraction a (-m) n = -fraction a m n := LocalizedModule.mk_neg

theorem fraction_add (a : R) (m m' : M) (n k : ℕ) :
    fraction a m n + fraction a m' k =
      fraction a (a ^ k • m + a ^ n • m') (n + k) := by
  simp only [fraction, powerDenominator_add, LocalizedModule.mk_add_mk,
    Submonoid.smul_def, powerDenominator_val]

theorem fraction_cancel (a : R) (m : M) (n k : ℕ) :
    fraction a (a ^ k • m) (n + k) = fraction a m n := by
  simpa only [fraction, powerDenominator_add, Submonoid.smul_def,
    powerDenominator_val] using
    LocalizedModule.mk_cancel_common_right (powerDenominator a n) (powerDenominator a k) m

theorem fraction_eq_zero (a : R) (m : M) (n : ℕ) :
    fraction a m n = 0 ↔ ∃ k : ℕ, a ^ k • m = 0 := by
  rw [← fraction_zero a 0, fraction, fraction, LocalizedModule.mk_eq]
  simp only [powerDenominator_zero, one_smul, smul_zero]
  constructor
  · rintro ⟨s, hs⟩
    obtain ⟨k, hk⟩ := s.property
    refine ⟨k, ?_⟩
    simpa only [Submonoid.smul_def, ← hk] using hs
  · rintro ⟨k, hk⟩
    exact ⟨powerDenominator a k, hk⟩

variable (𝒜 : ℤ → σR) (𝓜 : ℤ → σM)
  [SetLike.GradedMonoid 𝒜] [SetLike.GradedSMul 𝒜 𝓜]
  (a : R) (e : ℤ) (ha : a ∈ 𝒜 e)

omit [AddSubgroupClass σM M] in
include ha in
theorem power_smul_mem {d : ℤ} {m : M} (hm : m ∈ 𝓜 d) (n : ℕ) :
    a ^ n • m ∈ 𝓜 (d + (n : ℤ) * e) := by
  have h := SetLike.GradedSMul.smul_mem (SetLike.pow_mem_graded n ha) hm
  simpa only [nsmul_eq_mul, vadd_eq_add, add_comm] using h

def degreePiece (d : ℤ) : AddSubgroup (LocalizedModule (Submonoid.powers a) M) where
  carrier := {z | ∃ (n : ℕ) (m : M), m ∈ 𝓜 (d + (n : ℤ) * e) ∧ z = fraction a m n}
  zero_mem' := ⟨0, 0, zero_mem _, (fraction_zero a 0).symm⟩
  add_mem' := by
    rintro z z' ⟨n, m, hm, rfl⟩ ⟨k, m', hm', rfl⟩
    refine ⟨n + k, a ^ k • m + a ^ n • m', ?_, fraction_add a m m' n k⟩
    apply add_mem
    · have h := power_smul_mem 𝒜 𝓜 a e ha hm k
      convert h using 1
      push_cast
      ring_nf
    · have h := power_smul_mem 𝒜 𝓜 a e ha hm' n
      convert h using 1
      push_cast
      ring_nf
  neg_mem' := by
    rintro z ⟨n, m, hm, rfl⟩
    exact ⟨n, -m, neg_mem hm, (fraction_neg a m n).symm⟩

@[simp] theorem mem_degreePiece (d : ℤ) (z : LocalizedModule (Submonoid.powers a) M) :
    z ∈ degreePiece 𝒜 𝓜 a e ha d ↔
      ∃ (n : ℕ) (m : M), m ∈ 𝓜 (d + (n : ℤ) * e) ∧ z = fraction a m n := Iff.rfl

def localizedMap (f : M →ₗ[R] N) :
    LocalizedModule (Submonoid.powers a) M →ₗ[R] LocalizedModule (Submonoid.powers a) N :=
  IsLocalizedModule.map (Submonoid.powers a) (LocalizedModule.mkLinearMap _ M)
    (LocalizedModule.mkLinearMap _ N) f

@[simp] theorem localizedMap_fraction (f : M →ₗ[R] N) (m : M) (n : ℕ) :
    localizedMap a f (fraction a m n) = fraction a (f m) n :=
  IsLocalizedModule.map_LocalizedModules _ f m _

variable (𝓝 : ℤ → σN) [SetLike.GradedSMul 𝒜 𝓝]

def pieceMap (d : ℤ) (f : M →ₗ[R] N)
    (hf : ∀ i m, m ∈ 𝓜 i → f m ∈ 𝓝 i) :
    degreePiece 𝒜 𝓜 a e ha d →+ degreePiece 𝒜 𝓝 a e ha d where
  toFun z := ⟨localizedMap a f z.val, by
    obtain ⟨n, m, hm, hz⟩ := z.property
    refine ⟨n, f m, hf _ _ hm, ?_⟩
    rw [hz, localizedMap_fraction]⟩
  map_zero' := Subtype.ext (map_zero _)
  map_add' z z' := Subtype.ext (map_add _ _ _)

@[simp] theorem pieceMap_coe (d : ℤ) (f : M →ₗ[R] N)
    (hf : ∀ i m, m ∈ 𝓜 i → f m ∈ 𝓝 i)
    (z : degreePiece 𝒜 𝓜 a e ha d) :
    (pieceMap 𝒜 𝓜 a e ha 𝓝 d f hf z).val = localizedMap a f z.val := rfl

section Decomposition
variable [DirectSum.Decomposition 𝓜] [DirectSum.Decomposition 𝓝]

theorem preserves_of_compatible (f : M →ₗ[R] N)
    (hf : ∀ i x, f (DirectSum.decompose 𝓜 x i : M) =
      (DirectSum.decompose 𝓝 (f x) i : N)) :
    ∀ i m, m ∈ 𝓜 i → f m ∈ 𝓝 i := by
  intro i m hm
  have h := hf i m
  rw [DirectSum.decompose_of_mem_same 𝓜 hm] at h
  exact h.symm ▸ (DirectSum.decompose 𝓝 (f m) i).property

theorem homogeneous_preimage (f : M →ₗ[R] N)
    (hf : ∀ i x, f (DirectSum.decompose 𝓜 x i : M) =
      (DirectSum.decompose 𝓝 (f x) i : N))
    {d : ℤ} {y : N} (hy : y ∈ 𝓝 d) (hrange : y ∈ LinearMap.range f) :
    ∃ x : M, x ∈ 𝓜 d ∧ f x = y := by
  obtain ⟨x, hx⟩ := hrange
  refine ⟨DirectSum.decompose 𝓜 x d, (DirectSum.decompose 𝓜 x d).property, ?_⟩
  rw [hf, hx, DirectSum.decompose_of_mem_same 𝓝 hy]

theorem pieceMap_surjective (d : ℤ) (f : M →ₗ[R] N)
    (hf : ∀ i x, f (DirectSum.decompose 𝓜 x i : M) =
      (DirectSum.decompose 𝓝 (f x) i : N)) (hsurj : Function.Surjective f) :
    Function.Surjective
      (pieceMap 𝒜 𝓜 a e ha 𝓝 d f (preserves_of_compatible 𝓜 𝓝 f hf)) := by
  intro z
  obtain ⟨n, y, hy, hz⟩ := z.property
  obtain ⟨x, hx, hxy⟩ := homogeneous_preimage 𝓜 𝓝 f hf hy (hsurj y)
  refine ⟨⟨fraction a x n, n, x, hx, rfl⟩, ?_⟩
  apply Subtype.ext
  change localizedMap a f (fraction a x n) = z.val
  rw [localizedMap_fraction, hxy, ← hz]

variable (𝓟 : ℤ → σP) [SetLike.GradedSMul 𝒜 𝓟] [DirectSum.Decomposition 𝓟]

theorem pieceMap_exact (d : ℤ) (f : M →ₗ[R] N) (g : N →ₗ[R] P)
    (hf : ∀ i x, f (DirectSum.decompose 𝓜 x i : M) =
      (DirectSum.decompose 𝓝 (f x) i : N))
    (hg : ∀ i x, g (DirectSum.decompose 𝓝 x i : N) =
      (DirectSum.decompose 𝓟 (g x) i : P))
    (hex : Function.Exact f g) :
    Function.Exact
      (pieceMap 𝒜 𝓜 a e ha 𝓝 d f (preserves_of_compatible 𝓜 𝓝 f hf))
      (pieceMap 𝒜 𝓝 a e ha 𝓟 d g (preserves_of_compatible 𝓝 𝓟 g hg)) := by
  intro z
  constructor
  · intro hz
    obtain ⟨n, y, hy, hzy⟩ := z.property
    have hzero : localizedMap a g z.val = 0 := congrArg Subtype.val hz
    rw [hzy, localizedMap_fraction, fraction_eq_zero] at hzero
    obtain ⟨k, hk⟩ := hzero
    have hclear : g (a ^ k • y) = 0 := by rw [map_smul, hk]
    have hy' : a ^ k • y ∈ 𝓝 (d + ((n + k : ℕ) : ℤ) * e) := by
      have h := power_smul_mem 𝒜 𝓝 a e ha hy k
      convert h using 1
      push_cast
      ring_nf
    obtain ⟨x, hx, hxy⟩ := homogeneous_preimage 𝓜 𝓝 f hf hy' ((hex _).mp hclear)
    refine ⟨⟨fraction a x (n + k), n + k, x, hx, rfl⟩, ?_⟩
    apply Subtype.ext
    change localizedMap a f (fraction a x (n + k)) = z.val
    rw [localizedMap_fraction, hxy, fraction_cancel, ← hzy]
  · rintro ⟨x, rfl⟩
    apply Subtype.ext
    obtain ⟨n, y, hy, hxy⟩ := x.property
    change localizedMap a g (localizedMap a f x.val) = 0
    rw [hxy, localizedMap_fraction, localizedMap_fraction,
      hex.apply_apply_eq_zero, fraction_zero]

end Decomposition

section FinitePresentation
variable [AddSubgroupClass σR R] [DirectSum.Decomposition 𝒜] [DirectSum.Decomposition 𝓜]
  [IsNoetherianRing R] [Module.Finite R M]

end FinitePresentation

end
end PiExponent.GradedLocalizationExact

end OAI
end Source0769

-- Source: OAI/NumberTheory/PiExponent/Cohomology/GradedCech.lean
section Source0770
/-
Modification notice for the LogTwo project.
Derived from openai/math (Apache-2.0), revision adc7f1241b42e322a6451854ab7e4b4c146bf78a.
Original source: lean/OAI/NumberTheory/PiExponent/Cohomology/GradedCech.lean
Changes: Convert module/import declarations to the Lean 4.34 public module format.
See ../THIRD_PARTY_NOTICES.txt for provenance and the recorded changes.
-/

namespace OAI

namespace PiExponent.GradedCech
noncomputable section
open scoped BigOperators
open GradedLocalizationExact

variable {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]

theorem divisor_isUnit (a c : R) (hac : a ∣ c) :
    IsUnit (algebraMap R (Module.End R (LocalizedModule (Submonoid.powers c) M)) a) := by
  obtain ⟨b, rfl⟩ := hac
  have h := IsLocalizedModule.Away.isUnit_algebraMap
    (LocalizedModule.mkLinearMap (Submonoid.powers (a * b)) M) (a * b)
  rw [map_mul] at h
  exact (((Commute.all a b).map (algebraMap R
    (Module.End R (LocalizedModule (Submonoid.powers (a * b)) M)))).isUnit_mul_iff.mp h).1

theorem divisor_powers_isUnit (a c : R) (hac : a ∣ c) (s : Submonoid.powers a) :
    IsUnit (algebraMap R (Module.End R (LocalizedModule (Submonoid.powers c) M)) s) := by
  obtain ⟨n, hn⟩ := s.property
  rw [← hn, map_pow]
  exact (divisor_isUnit (M := M) a c hac).pow n

def restriction (a c : R) (hac : a ∣ c) :
    LocalizedModule (Submonoid.powers a) M →ₗ[R]
      LocalizedModule (Submonoid.powers c) M :=
  LocalizedModule.lift (Submonoid.powers a)
    (LocalizedModule.mkLinearMap (Submonoid.powers c) M)
    (divisor_powers_isUnit a c hac)

@[simp] theorem restriction_mk_one (a c : R) (hac : a ∣ c) (m : M) :
    restriction a c hac (LocalizedModule.mk m 1) = LocalizedModule.mk m 1 := by
  exact LocalizedModule.lift_mk_one _ _ _ m

@[simp] theorem restriction_fraction_zero (a c : R) (hac : a ∣ c) (m : M) :
    restriction a c hac (fraction a m 0) = fraction c m 0 := by
  simpa only [fraction, powerDenominator_zero] using restriction_mk_one a c hac m

theorem power_smul_fraction (a : R) (m : M) (n : ℕ) :
    a ^ n • fraction a m n = fraction a m 0 := by
  simp only [fraction, powerDenominator_zero, LocalizedModule.smul'_mk]
  exact LocalizedModule.mk_cancel (powerDenominator a n) m

theorem restriction_fraction (a b : R) (m : M) (n : ℕ) :
    restriction a (a * b) (dvd_mul_right a b) (fraction a m n) =
      fraction (a * b) (b ^ n • m) n := by
  have hu := (divisor_isUnit (M := M) a (a * b) (dvd_mul_right a b)).pow n
  rw [← map_pow] at hu
  apply ((Module.End.isUnit_iff _).mp hu).injective
  change a ^ n • restriction a (a * b) (dvd_mul_right a b) (fraction a m n) =
    a ^ n • fraction (a * b) (b ^ n • m) n
  rw [← map_smul, power_smul_fraction, restriction_fraction_zero]
  change fraction (a * b) m 0 =
    a ^ n • LocalizedModule.mk (b ^ n • m) (powerDenominator (a * b) n)
  rw [LocalizedModule.smul'_mk, smul_smul, ← mul_pow]
  simpa only [fraction, LocalizedModule.smul'_mk] using
    (power_smul_fraction (a * b) m n).symm

theorem restriction_refl (a : R) : restriction (M := M) a a dvd_rfl = LinearMap.id := by
  apply IsLocalizedModule.ext (Submonoid.powers a)
    (LocalizedModule.mkLinearMap (Submonoid.powers a) M)
    (divisor_powers_isUnit a a dvd_rfl)
  apply LinearMap.ext
  intro m
  exact restriction_mk_one a a dvd_rfl m

theorem restriction_comp (a b c : R) (hab : a ∣ b) (hbc : b ∣ c) :
    (restriction b c hbc).comp (restriction (M := M) a b hab) =
      restriction a c (hab.trans hbc) := by
  apply IsLocalizedModule.ext (Submonoid.powers a)
    (LocalizedModule.mkLinearMap (Submonoid.powers a) M)
    (divisor_powers_isUnit a c (hab.trans hbc))
  apply LinearMap.ext
  intro m
  simp only [LinearMap.comp_apply, LocalizedModule.mkLinearMap_apply, restriction_mk_one]

theorem restriction_localizedMap {N : Type*} [AddCommGroup N] [Module R N]
    (a c : R) (hac : a ∣ c) (f : M →ₗ[R] N) :
    (localizedMap c f).comp (restriction (M := M) a c hac) =
      (restriction (M := N) a c hac).comp (localizedMap a f) := by
  apply IsLocalizedModule.ext (Submonoid.powers a)
    (LocalizedModule.mkLinearMap (Submonoid.powers a) M)
    (divisor_powers_isUnit (M := N) a c hac)
  apply LinearMap.ext
  intro m
  simp only [LinearMap.comp_apply, LocalizedModule.mkLinearMap_apply]
  rw [show LocalizedModule.mk m (1 : Submonoid.powers a) = fraction a m 0 by
    simp only [fraction, powerDenominator_zero]]
  rw [restriction_fraction_zero, localizedMap_fraction,
    localizedMap_fraction, restriction_fraction_zero]

variable {σR σM : Type*} [SetLike σR R]
  [SetLike σM M] [AddSubgroupClass σM M]
  (𝒜 : ℤ → σR) (𝓜 : ℤ → σM)
  [SetLike.GradedMonoid 𝒜] [SetLike.GradedSMul 𝒜 𝓜]

def degreeRestriction (a c : R) (ea ec : ℤ)
    (ha : a ∈ 𝒜 ea) (hc : c ∈ 𝒜 ec)
    (hfactor : ∃ b : R, b ∈ 𝒜 (ec - ea) ∧ c = a * b) (d : ℤ) :
    degreePiece 𝒜 𝓜 a ea ha d →+ degreePiece 𝒜 𝓜 c ec hc d where
  toFun z := ⟨restriction a c (by obtain ⟨b, _, hb⟩ := hfactor; exact ⟨b, hb⟩) z.val, by
    obtain ⟨n, m, hm, hz⟩ := z.property
    obtain ⟨b, hb, rfl⟩ := hfactor
    refine ⟨n, b ^ n • m, ?_, ?_⟩
    · have h := power_smul_mem 𝒜 𝓜 b (ec - ea) hb hm n
      convert h using 1
      ring_nf
    · rw [hz]
      exact restriction_fraction a b m n⟩
  map_zero' := Subtype.ext (map_zero _)
  map_add' z z' := Subtype.ext (map_add _ _ _)

@[simp] theorem degreeRestriction_coe (a c : R) (ea ec : ℤ)
    (ha : a ∈ 𝒜 ea) (hc : c ∈ 𝒜 ec)
    (hfactor : ∃ b : R, b ∈ 𝒜 (ec - ea) ∧ c = a * b) (d : ℤ)
    (z : degreePiece 𝒜 𝓜 a ea ha d) :
    (degreeRestriction 𝒜 𝓜 a c ea ec ha hc hfactor d z).val =
      restriction a c (by obtain ⟨b, _, hb⟩ := hfactor; exact ⟨b, hb⟩) z.val := rfl

section Cover
variable {J : Type*} [DecidableEq J] (x : J → R) (hx : ∀ j, x j ∈ 𝒜 1)

def coverProduct (s : Finset J) : R := ∏ j ∈ s, x j

include hx in
theorem coverProduct_mem (s : Finset J) : coverProduct x s ∈ 𝒜 (s.card : ℤ) := by
  induction s using Finset.induction_on with
  | empty => simpa [coverProduct] using (SetLike.one_mem_graded 𝒜)
  | @insert j s hj hs =>
      have h := SetLike.GradedMul.mul_mem (hx j) hs
      simpa [coverProduct, Finset.prod_insert hj, Finset.card_insert_of_notMem hj,
        Nat.cast_add, add_comm] using h

include hx in

theorem coverProduct_factor {s t : Finset J} (hst : s ⊆ t) :
    ∃ b : R, b ∈ 𝒜 ((t.card : ℤ) - (s.card : ℤ)) ∧
      coverProduct x t = coverProduct x s * b := by
  refine ⟨coverProduct x (t \ s), ?_, ?_⟩
  · have h := coverProduct_mem 𝒜 x hx (t \ s)
    rwa [Finset.card_sdiff_of_subset hst, Nat.cast_sub (Finset.card_le_card hst)] at h
  · exact (Finset.prod_sdiff hst).symm.trans (mul_comm _ _)

include hx in
theorem coverProduct_dvd {s t : Finset J} (hst : s ⊆ t) :
    coverProduct x s ∣ coverProduct x t := by
  obtain ⟨b, _, hb⟩ := coverProduct_factor 𝒜 x hx hst
  exact ⟨b, hb⟩

abbrev IntersectionPiece (s : Finset J) (d : ℤ) :=
  degreePiece 𝒜 𝓜 (coverProduct x s) (s.card : ℤ) (coverProduct_mem 𝒜 x hx s) d

def setRestriction {s t : Finset J} (hst : s ⊆ t) (d : ℤ) :
    IntersectionPiece 𝒜 𝓜 x hx s d →+ IntersectionPiece 𝒜 𝓜 x hx t d :=
  degreeRestriction 𝒜 𝓜 _ _ _ _ (coverProduct_mem 𝒜 x hx s)
    (coverProduct_mem 𝒜 x hx t) (coverProduct_factor 𝒜 x hx hst) d

@[simp] theorem setRestriction_coe {s t : Finset J} (hst : s ⊆ t) (d : ℤ)
    (z : IntersectionPiece 𝒜 𝓜 x hx s d) :
    (setRestriction 𝒜 𝓜 x hx hst d z).val =
      restriction (coverProduct x s) (coverProduct x t) (coverProduct_dvd 𝒜 x hx hst) z.val := rfl

@[simp] theorem setRestriction_refl (s : Finset J) (d : ℤ)
    (z : IntersectionPiece 𝒜 𝓜 x hx s d) : setRestriction 𝒜 𝓜 x hx (s := s) le_rfl d z = z := by
  apply Subtype.ext
  rw [setRestriction_coe, restriction_refl]
  rfl

theorem setRestriction_comp {s t u : Finset J} (hst : s ⊆ t) (htu : t ⊆ u)
    (d : ℤ) (z : IntersectionPiece 𝒜 𝓜 x hx s d) :
    setRestriction 𝒜 𝓜 x hx htu d (setRestriction 𝒜 𝓜 x hx hst d z) =
      setRestriction 𝒜 𝓜 x hx (hst.trans htu) d z := by
  apply Subtype.ext
  simp only [setRestriction_coe]
  exact DFunLike.congr_fun (restriction_comp (coverProduct x s) (coverProduct x t)
    (coverProduct x u) (coverProduct_dvd 𝒜 x hx hst) (coverProduct_dvd 𝒜 x hx htu)) z.val

def tupleSet {n : ℕ} (t : Fin n → J) : Finset J := Finset.univ.image t

theorem tupleSet_comp_subset {m n : ℕ} (t : Fin n → J) (f : Fin m → Fin n) :
    tupleSet (t ∘ f) ⊆ tupleSet t := by
  intro j hj
  obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hj
  exact Finset.mem_image.mpr ⟨f i, Finset.mem_univ _, rfl⟩

abbrev Cochain (d : ℤ) (q : ℕ) :=
  ∀ t : Fin (q + 1) → J, IntersectionPiece 𝒜 𝓜 x hx (tupleSet t) d

def differential (d : ℤ) {q : ℕ} (c : Cochain 𝒜 𝓜 x hx d q) :
    Cochain 𝒜 𝓜 x hx d (q + 1) :=
  fun t => ∑ k : Fin (q + 2), (-1 : ℤ) ^ k.val •
    setRestriction 𝒜 𝓜 x hx (tupleSet_comp_subset t k.succAbove) d (c (t ∘ k.succAbove))

@[simp] theorem differential_zero (d : ℤ) {q : ℕ} :
    differential 𝒜 𝓜 x hx d (0 : Cochain 𝒜 𝓜 x hx d q) = 0 := by
  funext t
  simp only [differential, Pi.zero_apply, map_zero, smul_zero, Finset.sum_const_zero]

theorem differential_sub (d : ℤ) {q : ℕ} (c b : Cochain 𝒜 𝓜 x hx d q) :
    differential 𝒜 𝓜 x hx d (c - b) = differential 𝒜 𝓜 x hx d c - differential 𝒜 𝓜 x hx d b := by
  funext t
  simp only [differential, Pi.sub_apply, map_sub, smul_sub, Finset.sum_sub_distrib]

theorem tupleSet_subset {L : Type*} (s : Finset J) (f : L → J)
    (hf : ∀ l, f l ∈ s) {n : ℕ} (t : Fin n → L) : tupleSet (f ∘ t) ⊆ s := by
  intro j hj
  obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hj
  exact hf (t i)

def evaluate (d : ℤ) {L : Type*} (s : Finset J) (f : L → J)
    (hf : ∀ l, f l ∈ s) {q : ℕ} (c : Cochain 𝒜 𝓜 x hx d q) :
    ProjectiveMonomialCechHigher.Cochain L (IntersectionPiece 𝒜 𝓜 x hx s d) q :=
  fun t => setRestriction 𝒜 𝓜 x hx (tupleSet_subset s f hf t) d (c (f ∘ t))

theorem evaluate_differential (d : ℤ) {L : Type*} (s : Finset J) (f : L → J)
    (hf : ∀ l, f l ∈ s) {q : ℕ} (c : Cochain 𝒜 𝓜 x hx d q) :
    evaluate 𝒜 𝓜 x hx d s f hf (differential 𝒜 𝓜 x hx d c) =
      ProjectiveMonomialCechHigher.differential (evaluate 𝒜 𝓜 x hx d s f hf c) := by
  funext t
  simp only [evaluate, differential, ProjectiveMonomialCechHigher.differential,
    map_sum, map_zsmul, setRestriction_comp]
  rfl

theorem differential_squared (d : ℤ) {q : ℕ} (c : Cochain 𝒜 𝓜 x hx d q) :
    differential 𝒜 𝓜 x hx d (differential 𝒜 𝓜 x hx d c) = 0 := by
  funext t
  have ht : ∀ i, t i ∈ tupleSet t := fun i =>
    Finset.mem_image.mpr ⟨i, Finset.mem_univ _, rfl⟩
  have h := congrFun (ProjectiveMonomialCechHigher.differential_squared
    (evaluate 𝒜 𝓜 x hx d (tupleSet t) t ht c)) id
  rw [← evaluate_differential, ← evaluate_differential] at h
  change setRestriction 𝒜 𝓜 x hx le_rfl d
    (differential 𝒜 𝓜 x hx d (differential 𝒜 𝓜 x hx d c) t) = 0 at h
  simpa only [setRestriction_refl, Pi.zero_apply] using h

def differentialHom (d : ℤ) (q : ℕ) :
    Cochain 𝒜 𝓜 x hx d q →+ Cochain 𝒜 𝓜 x hx d (q + 1) where
  toFun := differential 𝒜 𝓜 x hx d
  map_zero' := differential_zero 𝒜 𝓜 x hx d
  map_add' c b := by
    funext t
    simp only [differential, Pi.add_apply, map_add, smul_add, Finset.sum_add_distrib]

def augmentation (d : ℤ) : 𝓜 d →+ Cochain 𝒜 𝓜 x hx d 0 where
  toFun m t := ⟨fraction (coverProduct x (tupleSet t)) (m : M) 0,
    0, m, by simpa only [Nat.cast_zero, zero_mul, add_zero] using m.property, rfl⟩
  map_zero' := by
    funext t
    exact Subtype.ext (fraction_zero _ _)
  map_add' m n := by
    funext t
    apply Subtype.ext
    simpa only [fraction, powerDenominator_zero, Pi.add_apply, AddMemClass.coe_add,
      LocalizedModule.mkLinearMap_apply] using
      (LocalizedModule.mkLinearMap (Submonoid.powers (coverProduct x (tupleSet t))) M).map_add
        (m : M) (n : M)

@[simp] theorem augmentation_coe (d : ℤ) (m : 𝓜 d) (t : Fin 1 → J) :
    (augmentation 𝒜 𝓜 x hx d m t).val = fraction (coverProduct x (tupleSet t)) (m : M) 0 := rfl

theorem differential_augmentation (d : ℤ) (m : 𝓜 d) :
    differential 𝒜 𝓜 x hx d (augmentation 𝒜 𝓜 x hx d m) = 0 := by
  funext t
  apply Subtype.ext
  simp [differential, Fin.sum_univ_succ, setRestriction_coe,
    augmentation_coe, restriction_fraction_zero]
  change restriction _ _ _ (fraction _ (m : M) 0) + -fraction _ (m : M) 0 = 0
  rw [restriction_fraction_zero, add_neg_cancel]

section Maps
variable {N σN : Type*} [AddCommGroup N] [Module R N]
  [SetLike σN N] [AddSubgroupClass σN N]
  (𝓝 : ℤ → σN) [SetLike.GradedSMul 𝒜 𝓝]
  (f : M →ₗ[R] N) (hf : ∀ i m, m ∈ 𝓜 i → f m ∈ 𝓝 i)

theorem pieceMap_setRestriction {s t : Finset J} (hst : s ⊆ t) (d : ℤ)
    (z : IntersectionPiece 𝒜 𝓜 x hx s d) :
    pieceMap 𝒜 𝓜 (coverProduct x t) _ (coverProduct_mem 𝒜 x hx t) 𝓝 d f hf
        (setRestriction 𝒜 𝓜 x hx hst d z) =
      setRestriction 𝒜 𝓝 x hx hst d
        (pieceMap 𝒜 𝓜 (coverProduct x s) _ (coverProduct_mem 𝒜 x hx s) 𝓝 d f hf z) := by
  apply Subtype.ext
  simp only [pieceMap_coe, setRestriction_coe]
  exact DFunLike.congr_fun (restriction_localizedMap (coverProduct x s) (coverProduct x t)
    (coverProduct_dvd 𝒜 x hx hst) f) z.val

def cochainMap (d : ℤ) (q : ℕ) : Cochain 𝒜 𝓜 x hx d q →+ Cochain 𝒜 𝓝 x hx d q where
  toFun c t := pieceMap 𝒜 𝓜 (coverProduct x (tupleSet t)) _
    (coverProduct_mem 𝒜 x hx (tupleSet t)) 𝓝 d f hf (c t)
  map_zero' := by funext t; exact map_zero _
  map_add' c b := by funext t; exact map_add _ _ _

theorem cochainMap_differential (d : ℤ) {q : ℕ} (c : Cochain 𝒜 𝓜 x hx d q) :
    cochainMap 𝒜 𝓜 x hx 𝓝 f hf d (q + 1) (differential 𝒜 𝓜 x hx d c) =
      differential 𝒜 𝓝 x hx d (cochainMap 𝒜 𝓜 x hx 𝓝 f hf d q c) := by
  funext t
  simp only [cochainMap, AddMonoidHom.coe_mk, ZeroHom.coe_mk, differential,
    map_sum, map_zsmul, pieceMap_setRestriction]

theorem cochainMap_injective (d : ℤ) (q : ℕ) (hinj : Function.Injective f) :
    Function.Injective (cochainMap 𝒜 𝓜 x hx 𝓝 f hf d q) := by
  intro c b h
  funext t
  apply Subtype.ext
  have ht := congrArg Subtype.val (congrFun h t)
  exact (IsLocalizedModule.map_injective (Submonoid.powers (coverProduct x (tupleSet t)))
    (LocalizedModule.mkLinearMap _ M) (LocalizedModule.mkLinearMap _ N) f hinj) ht

def globalPieceMap (d : ℤ) : 𝓜 d →+ 𝓝 d where
  toFun m := ⟨f m, hf d m m.property⟩
  map_zero' := Subtype.ext (map_zero _)
  map_add' _ _ := Subtype.ext (map_add _ _ _)

theorem augmentation_natural (d : ℤ) (m : 𝓜 d) :
    cochainMap 𝒜 𝓜 x hx 𝓝 f hf d 0 (augmentation 𝒜 𝓜 x hx d m) =
      augmentation 𝒜 𝓝 x hx d (globalPieceMap 𝓜 𝓝 f hf d m) := by
  funext t
  apply Subtype.ext
  change localizedMap (coverProduct x (tupleSet t)) f
      (fraction (coverProduct x (tupleSet t)) (m : M) 0) =
    fraction (coverProduct x (tupleSet t)) (f m) 0
  exact localizedMap_fraction _ f m 0

end Maps

section Exactness
variable {N P σN σP : Type*} [AddCommGroup N] [Module R N]
  [AddCommGroup P] [Module R P]
  [SetLike σN N] [AddSubgroupClass σN N]
  [SetLike σP P] [AddSubgroupClass σP P]
  (𝓝 : ℤ → σN) (𝓟 : ℤ → σP)
  [SetLike.GradedSMul 𝒜 𝓝] [SetLike.GradedSMul 𝒜 𝓟]
  [DirectSum.Decomposition 𝓜] [DirectSum.Decomposition 𝓝] [DirectSum.Decomposition 𝓟]

theorem cochainMap_surjective (d : ℤ) (q : ℕ) (f : M →ₗ[R] N)
    (hf : ∀ i z, f (DirectSum.decompose 𝓜 z i : M) =
      (DirectSum.decompose 𝓝 (f z) i : N)) (hsurj : Function.Surjective f) :
    Function.Surjective (cochainMap 𝒜 𝓜 x hx 𝓝 f
      (preserves_of_compatible 𝓜 𝓝 f hf) d q) := by
  intro c
  have ht (t : Fin (q + 1) → J) := pieceMap_surjective 𝒜 𝓜
    (coverProduct x (tupleSet t)) _ (coverProduct_mem 𝒜 x hx (tupleSet t))
    𝓝 d f hf hsurj (c t)
  choose b hb using ht
  exact ⟨b, funext hb⟩

theorem cochainMap_exact (d : ℤ) (q : ℕ) (f : M →ₗ[R] N) (g : N →ₗ[R] P)
    (hf : ∀ i z, f (DirectSum.decompose 𝓜 z i : M) =
      (DirectSum.decompose 𝓝 (f z) i : N))
    (hg : ∀ i z, g (DirectSum.decompose 𝓝 z i : N) =
      (DirectSum.decompose 𝓟 (g z) i : P)) (hex : Function.Exact f g) :
    Function.Exact
      (cochainMap 𝒜 𝓜 x hx 𝓝 f (preserves_of_compatible 𝓜 𝓝 f hf) d q)
      (cochainMap 𝒜 𝓝 x hx 𝓟 g (preserves_of_compatible 𝓝 𝓟 g hg) d q) := by
  intro c
  have hlocal (t : Fin (q + 1) → J) := pieceMap_exact 𝒜 𝓜
    (coverProduct x (tupleSet t)) _ (coverProduct_mem 𝒜 x hx (tupleSet t))
    𝓝 𝓟 d f g hf hg hex
  constructor
  · intro hc
    have ht (t : Fin (q + 1) → J) := (hlocal t (c t)).mp (congrFun hc t)
    choose b hb using ht
    exact ⟨b, funext hb⟩
  · rintro ⟨b, rfl⟩
    funext t
    exact (hlocal t).apply_apply_eq_zero (b t)

end Exactness

end Cover

end
end PiExponent.GradedCech

end OAI
end Source0770

-- Source: OAI/NumberTheory/PiExponent/Cohomology/GradedH0.lean
section Source0771
-- Modified in this edition: unused plain lemmas removed; see reduction.json.
/-
Modification notice for the LogTwo project.
Derived from openai/math (Apache-2.0), revision adc7f1241b42e322a6451854ab7e4b4c146bf78a.
Original source: lean/OAI/NumberTheory/PiExponent/Cohomology/GradedH0.lean
Changes: Convert module/import declarations to the Lean 4.34 public module format.
See ../THIRD_PARTY_NOTICES.txt for provenance and the recorded changes.
-/

namespace OAI

namespace PiExponent.GradedH0
noncomputable section
open scoped BigOperators
open ProjectiveMonomialCech
variable {ι R : Type*} [Fintype ι] [CommRing R]

def PolynomialExponent (n : ℕ) := {b : ι →₀ ℕ // b.degree = n}

def NonnegativeMonomialSet (d : ℤ) : Set (Monomial ι d) :=
  {a | ∀ j, 0 ≤ a.val j}

def encode (n : ℕ) (b : PolynomialExponent (ι := ι) n) : Monomial ι (n : ℤ) :=
  ⟨fun j => (b.val j : ℤ), by
    rw [← Nat.cast_sum, ← Finsupp.degree_eq_sum, b.property]⟩

@[simp] theorem encode_apply (n : ℕ) (b : PolynomialExponent (ι := ι) n) (j : ι) :
    (encode n b).val j = (b.val j : ℤ) := rfl

theorem encode_nonnegative (n : ℕ) (b : PolynomialExponent (ι := ι) n) :
    encode n b ∈ NonnegativeMonomialSet (n : ℤ) := fun _j => Int.natCast_nonneg _

def decode (n : ℕ) (a : NonnegativeMonomialSet (ι := ι) (n : ℤ)) :
    PolynomialExponent (ι := ι) n := by
  let b : ι →₀ ℕ := Finsupp.equivFunOnFinite.symm (fun j => (a.val.val j).toNat)
  refine ⟨b, ?_⟩
  apply Int.natCast_inj.mp
  calc
    (b.degree : ℤ) = ∑ j, ((a.val.val j).toNat : ℤ) := by
      rw [Finsupp.degree_eq_sum, Nat.cast_sum]
      rfl
    _ = ∑ j, a.val.val j := by
      apply Finset.sum_congr rfl
      intro j _
      exact Int.toNat_of_nonneg (a.property j)
    _ = (n : ℤ) := a.val.property

@[simp] theorem decode_apply (n : ℕ) (a : NonnegativeMonomialSet (ι := ι) (n : ℤ))
    (j : ι) : (decode n a).val j = (a.val.val j).toNat := rfl

def exponentEquiv (n : ℕ) :
    PolynomialExponent (ι := ι) n ≃ NonnegativeMonomialSet (ι := ι) (n : ℤ) where
  toFun b := ⟨encode n b, encode_nonnegative n b⟩
  invFun := decode n
  left_inv b := by
    apply Subtype.ext
    ext j
    simp
  right_inv a := by
    apply Subtype.ext
    apply Subtype.ext
    funext j
    simp only [encode_apply, decode_apply]
    exact Int.toNat_of_nonneg (a.property j)

def homogeneousPolynomialEquiv (n : ℕ) :
    MvPolynomial.homogeneousSubmodule ι R n ≃ₗ[R]
      Finsupp.supported R R (NonnegativeMonomialSet (ι := ι) (n : ℤ)) :=
  (LinearEquiv.ofEq _ _ (MvPolynomial.homogeneousSubmodule_eq_finsupp_supported ι R n)).trans <|
    (AddMonoidAlgebra.supportedEquivFinsupp {b : ι →₀ ℕ | b.degree = n}).trans <|
      (Finsupp.domLCongr (exponentEquiv n)).trans
        (Finsupp.supportedEquivFinsupp (NonnegativeMonomialSet (ι := ι) (n : ℤ))).symm

theorem integer_grading_eq_homogeneous (n : ℕ) :
    MvPolynomial.weightedHomogeneousSubmodule R (1 : ι → ℤ) (n : ℤ) =
      MvPolynomial.homogeneousSubmodule ι R n := by
  rw [MvPolynomial.weightedHomogeneousSubmodule_eq_finsupp_supported,
    MvPolynomial.homogeneousSubmodule_eq_finsupp_supported]
  have hweight (b : ι →₀ ℕ) : Finsupp.weight (1 : ι → ℤ) b = (b.degree : ℤ) := by
    simp [Finsupp.weight_eq_sum, Finsupp.degree_eq_sum, Nat.cast_sum]
  congr 1
  ext b
  simp only [Set.mem_ofPred_eq, hweight, Int.natCast_inj]

def integerHomogeneousPolynomialEquiv (d : ℤ) (hd : 0 ≤ d) :
    MvPolynomial.weightedHomogeneousSubmodule R (1 : ι → ℤ) d ≃ₗ[R]
      Finsupp.supported R R (NonnegativeMonomialSet (ι := ι) d) := by
  cases d with
  | ofNat n =>
      exact (LinearEquiv.ofEq _ _ (integer_grading_eq_homogeneous n)).trans
        (homogeneousPolynomialEquiv n)
  | negSucc n => omega

def polynomialLaurent (n : ℕ) :
    MvPolynomial.homogeneousSubmodule ι R n →ₗ[R] Laurent ι R (n : ℤ) :=
  (Finsupp.supported R R (NonnegativeMonomialSet (ι := ι) (n : ℤ))).subtype.comp
    (homogeneousPolynomialEquiv n).toLinearMap

theorem mem_supported_iff_regular (d : ℤ) (p : Laurent ι R d) :
    p ∈ Finsupp.supported R R (NonnegativeMonomialSet d) ↔ RegularOn ∅ p := by
  classical
  rw [Finsupp.mem_supported]
  constructor
  · intro hp a ha j hj
    exact False.elim ((not_lt_of_ge (hp (Finsupp.mem_support_iff.mpr ha) j)) hj)
  · intro hp a ha j
    by_contra hneg
    exact hp a (Finsupp.mem_support_iff.mp ha) j (lt_of_not_ge hneg)

theorem polynomialLaurent_injective (n : ℕ) :
    Function.Injective (polynomialLaurent (ι := ι) (R := R) n) :=
  Subtype.val_injective.comp (homogeneousPolynomialEquiv n).injective

theorem existsUnique_polynomial_of_regular (n : ℕ) (f : Laurent ι R (n : ℤ))
    (hf : RegularOn ∅ f) :
    ∃! p : MvPolynomial.homogeneousSubmodule ι R n, polynomialLaurent n p = f := by
  let a : Finsupp.supported R R (NonnegativeMonomialSet (ι := ι) (n : ℤ)) :=
    ⟨f, (mem_supported_iff_regular _ _).mpr hf⟩
  refine ⟨(homogeneousPolynomialEquiv n).symm a, ?_, ?_⟩
  · change ((homogeneousPolynomialEquiv n) ((homogeneousPolynomialEquiv n).symm a)).val = f
    rw [LinearEquiv.apply_symm_apply]
  · intro p hp
    apply polynomialLaurent_injective n
    rw [hp]
    change f = ((homogeneousPolynomialEquiv n) ((homogeneousPolynomialEquiv n).symm a)).val
    rw [LinearEquiv.apply_symm_apply]

theorem existsUnique_polynomial_of_compatible_vertices [Nonempty ι] (n : ℕ)
    (c : ι → Laurent ι R (n : ℤ)) (hc : ∀ j, RegularOn {j} (c j))
    (heq : ∀ i j, c i = c j) :
    ∃! p : MvPolynomial.homogeneousSubmodule ι R n,
      ∀ j, polynomialLaurent n p = c j := by
  obtain ⟨f, hf, hcf⟩ := GradedSerre.compatible_vertices_are_polynomial
    (Int.natCast_nonneg n) c hc heq
  obtain ⟨p, hp, huniq⟩ := existsUnique_polynomial_of_regular n f hf
  refine ⟨p, fun j => hp.trans (hcf j).symm, ?_⟩
  intro q hq
  exact huniq q ((hq (Classical.choice inferInstance)).trans (hcf _))

theorem zeroth_cocycle_vertices_eq {d : ℤ}
    (c : ProjectiveMonomialCechHigher.Cochain ι (Laurent ι R d) 0)
    (hc : ProjectiveMonomialCechHigher.differential c = 0) (i j : ι) :
    c (fun _ => i) = c (fun _ => j) := by
  have h := congrFun hc (![i, j] : Fin 2 → ι)
  simp only [ProjectiveMonomialCechHigher.differential, Fin.sum_univ_succ,
    Fin.val_zero, pow_zero, one_zsmul, Fin.val_succ, Fin.sum_univ_zero,
    add_zero, Nat.zero_add, pow_one, neg_one_zsmul, Pi.zero_apply] at h
  have hi : (![i, j] : Fin 2 → ι) ∘ (0 : Fin 2).succAbove = (fun _ => j) := by
    funext k
    fin_cases k
    rfl
  have hj : (![i, j] : Fin 2 → ι) ∘ (Fin.succ (0 : Fin 1)).succAbove = (fun _ => i) := by
    funext k
    fin_cases k
    rfl
  rw [hi, hj] at h
  exact (eq_of_sub_eq_zero (by simpa only [sub_eq_add_neg] using h)).symm

theorem zeroth_cocycle_unique_homogeneous_polynomial [Nonempty ι] (n : ℕ)
    (c : ProjectiveMonomialCechHigher.Cochain ι (Laurent ι R (n : ℤ)) 0)
    (hreg : ProjectiveMonomialCechHigher.Regular c)
    (hc : ProjectiveMonomialCechHigher.differential c = 0) :
    ∃! p : MvPolynomial.homogeneousSubmodule ι R n,
      ∀ t, polynomialLaurent n p = c t := by
  have hreg' (j : ι) : RegularOn {j} (c (fun _ => j)) := by
    have h := hreg (fun _ => j)
    simpa only [Set.range_const] using h
  obtain ⟨p, hp, hu⟩ := existsUnique_polynomial_of_compatible_vertices n
    (fun j => c (fun _ => j)) hreg' (zeroth_cocycle_vertices_eq c hc)
  refine ⟨p, ?_, ?_⟩
  · intro t
    have ht : t = fun _ => t 0 := by
      funext i
      exact congrArg t (show i = 0 by omega)
    rw [ht]
    exact hp (t 0)
  · intro q hq
    exact hu q (fun j => hq (fun _ => j))

end
end PiExponent.GradedH0

end OAI
end Source0771

-- Source: OAI/NumberTheory/PiExponent/Cohomology/GradedPolynomialLaurent.lean
section Source0772
/-
Modification notice for the LogTwo project.
Derived from openai/math (Apache-2.0), revision adc7f1241b42e322a6451854ab7e4b4c146bf78a.
Original source: lean/OAI/NumberTheory/PiExponent/Cohomology/GradedPolynomialLaurent.lean
Changes: Convert module/import declarations to the Lean 4.34 public module format.
See ../THIRD_PARTY_NOTICES.txt for provenance and the recorded changes.
-/

namespace OAI

namespace PiExponent.GradedPolynomialLaurent
noncomputable section
open scoped BigOperators
open PiExponent.GradedCech PiExponent.GradedLocalizationExact PiExponent.ProjectiveMonomialCech
attribute [local instance] Classical.propDecidable MvPolynomial.weightedGradedAlgebra
variable {J R : Type*} [CommRing R]

abbrev GroupAlgebra := AddMonoidAlgebra R (J → ℤ)

def natExponentHom : (J →₀ ℕ) →+ (J → ℤ) where
  toFun b j := b j
  map_zero' := by ext j; simp
  map_add' := by intro a b; ext j; simp

def polynomialToGroupAlgebra : MvPolynomial J R →+* GroupAlgebra (J := J) (R := R) :=
  AddMonoidAlgebra.mapDomainRingHom R natExponentHom

theorem polynomialToGroupAlgebra_injective :
    Function.Injective (polynomialToGroupAlgebra (J := J) (R := R)) := by
  apply AddMonoidAlgebra.mapDomain_injective
  intro a b hab
  ext j
  exact Int.natCast_inj.mp (congrFun hab j)

def product (s : Finset J) : MvPolynomial J R := ∏ j ∈ s, MvPolynomial.X j

def productExponent (s : Finset J) : J → ℤ := ∑ j ∈ s, natExponentHom (Finsupp.single j 1)

theorem single_isUnit (a : J → ℤ) :
    IsUnit (AddMonoidAlgebra.single a (1 : R) : GroupAlgebra (J := J) (R := R)) := by
  apply isUnit_iff_exists_inv.mpr
  refine ⟨AddMonoidAlgebra.single (-a) 1, ?_⟩
  rw [AddMonoidAlgebra.single_mul_single]
  simp only [add_neg_cancel, one_mul]
  rfl

@[simp] theorem polynomialToGroupAlgebra_X (j : J) :
    polynomialToGroupAlgebra (R := R) (MvPolynomial.X j) =
      AddMonoidAlgebra.single (natExponentHom (Finsupp.single j 1)) 1 := by
  change AddMonoidAlgebra.mapDomain _ (AddMonoidAlgebra.single _ _) = _
  exact AddMonoidAlgebra.mapDomain_single

@[simp] theorem polynomialToGroupAlgebra_product (s : Finset J) :
    polynomialToGroupAlgebra (R := R) (product s) =
      AddMonoidAlgebra.single (productExponent s) 1 := by
  classical
  induction s using Finset.induction_on with
  | empty =>
      simp only [product, productExponent, Finset.prod_empty, Finset.sum_empty, map_one]
      rfl
  | @insert j s hj ih =>
      simp only [product, Finset.prod_insert hj, map_mul] at *
      rw [polynomialToGroupAlgebra_X, ih, AddMonoidAlgebra.single_mul_single]
      simp [productExponent, hj]

theorem product_isUnit (s : Finset J) :
    IsUnit (polynomialToGroupAlgebra (R := R) (product s)) := by
  rw [polynomialToGroupAlgebra_product]
  exact single_isUnit _

def ringLocalizationMap (s : Finset J) :
    Localization.Away (product (R := R) s) →+* GroupAlgebra (J := J) (R := R) :=
  Localization.awayLift polynomialToGroupAlgebra (product s) (product_isUnit s)

@[simp] theorem ringLocalizationMap_base (s : Finset J) (p : MvPolynomial J R) :
    ringLocalizationMap s (algebraMap _ _ p) = polynomialToGroupAlgebra p :=
  IsLocalization.Away.lift_eq (product s) (product_isUnit s) p

theorem ringLocalizationMap_injective (s : Finset J) :
    Function.Injective (ringLocalizationMap (R := R) s) := by
  apply (IsLocalization.injective_iff_map_algebraMap_eq
    (Submonoid.powers (product (R := R) s)) (ringLocalizationMap s)).mpr
  intro p q
  constructor
  · exact congrArg _
  · intro h
    rw [ringLocalizationMap_base, ringLocalizationMap_base] at h
    exact congrArg _ (polynomialToGroupAlgebra_injective h)

def moduleRingEquiv (s : Finset J) :
    LocalizedModule (Submonoid.powers (product (R := R) s)) (MvPolynomial J R) ≃ₗ[MvPolynomial J R]
      Localization.Away (product (R := R) s) :=
  IsLocalizedModule.iso _ (Algebra.linearMap _ _)

@[simp] theorem moduleRingEquiv_fraction (s : Finset J) (p : MvPolynomial J R) (n : ℕ) :
    moduleRingEquiv s (fraction (product s) p n) = Localization.mk p (powerDenominator (product s) n) := by
  change IsLocalizedModule.mk' (Algebra.linearMap (MvPolynomial J R)
    (Localization.Away (product (R := R) s))) p (powerDenominator (product s) n) = _
  rw [← IsLocalization.mk'_eq_mk', Localization.mk_eq_mk']

def moduleToGroupAlgebra (s : Finset J) :
    LocalizedModule (Submonoid.powers (product (R := R) s)) (MvPolynomial J R) →+
      GroupAlgebra (J := J) (R := R) :=
  (ringLocalizationMap s).toAddMonoidHom.comp (moduleRingEquiv s).toAddMonoidHom

theorem moduleToGroupAlgebra_injective (s : Finset J) :
    Function.Injective (moduleToGroupAlgebra (R := R) s) :=
  (ringLocalizationMap_injective s).comp (moduleRingEquiv s).injective

@[simp] theorem moduleToGroupAlgebra_fraction (s : Finset J) (p : MvPolynomial J R) (n : ℕ) :
    moduleToGroupAlgebra s (fraction (product s) p n) =
      polynomialToGroupAlgebra p * AddMonoidAlgebra.single (-(n • productExponent s)) 1 := by
  have hinv : polynomialToGroupAlgebra (R := R) (product s) *
      AddMonoidAlgebra.single (-productExponent s) 1 = 1 := by
    rw [polynomialToGroupAlgebra_product, AddMonoidAlgebra.single_mul_single]
    simp only [add_neg_cancel, one_mul]
    rfl
  change ringLocalizationMap s (moduleRingEquiv s (fraction _ p n)) = _
  rw [moduleRingEquiv_fraction]
  change Localization.awayLift polynomialToGroupAlgebra (product s)
    (isUnit_iff_exists_inv.mpr ⟨_, hinv⟩) _ = _
  unfold powerDenominator
  rw [Localization.awayLift_mk polynomialToGroupAlgebra (product s) p
    (AddMonoidAlgebra.single (-productExponent s) 1) hinv n]
  simp only [AddMonoidAlgebra.single_pow, one_pow, smul_neg]

@[simp] theorem productExponent_apply (s : Finset J) (j : J) :
    productExponent s j = if j ∈ s then 1 else 0 := by
  classical
  simp [productExponent, Finset.sum_apply, natExponentHom, Finsupp.single_apply]

variable [Fintype J]

@[simp] theorem sum_productExponent (s : Finset J) : ∑ j, productExponent s j = (s.card : ℤ) := by
  classical
  simp [productExponent_apply]

omit [Fintype J] in
theorem natExponentHom_injective : Function.Injective (natExponentHom (J := J)) := by
  intro a b hab
  ext j
  exact Int.natCast_inj.mp (congrFun hab j)

omit [Fintype J] in
@[simp] theorem polynomialToGroupAlgebra_coefficient (p : MvPolynomial J R) (b : J →₀ ℕ) :
    (polynomialToGroupAlgebra p).coeff (natExponentHom b) = p.coeff b :=
  Finsupp.mapDomain_apply_of_injective natExponentHom_injective p.coeff b

theorem polynomialToGroupAlgebra_support {d : ℤ} (p : MvPolynomial J R)
    (hp : p.IsWeightedHomogeneous (1 : J → ℤ) d) (a : J → ℤ)
    (ha : (polynomialToGroupAlgebra p).coeff a ≠ 0) :
    (∑ j, a j = d) ∧ ∀ j, 0 ≤ a j := by
  obtain ⟨b, rfl⟩ := Finsupp.mem_range_of_mapDomain_ne_zero ha
  rw [polynomialToGroupAlgebra_coefficient] at ha
  constructor
  · simpa only [Finsupp.weight_eq_sum, Pi.one_apply, nsmul_eq_mul, mul_one,
      natExponentHom, AddMonoidHom.coe_mk, ZeroHom.coe_mk] using hp ha
  · intro j
    exact Int.natCast_nonneg _

omit [Fintype J] in
@[simp] theorem moduleToGroupAlgebra_fraction_coefficient
    (s : Finset J) (p : MvPolynomial J R) (n : ℕ) (a : J → ℤ) :
    (moduleToGroupAlgebra s (fraction (product s) p n)).coeff a =
      (polynomialToGroupAlgebra p).coeff (a + n • productExponent s) := by
  rw [moduleToGroupAlgebra_fraction]
  simp only [AddMonoidAlgebra.coeff_mul_single_apply, neg_neg, mul_one]

abbrev grading : ℤ → Submodule R (MvPolynomial J R) :=
  MvPolynomial.weightedHomogeneousSubmodule R (1 : J → ℤ)

omit [Fintype J] in
theorem variable_mem (j : J) : MvPolynomial.X j ∈ grading (R := R) (J := J) 1 :=
  MvPolynomial.isWeightedHomogeneous_X R (1 : J → ℤ) j

omit [Fintype J] in
theorem product_mem (s : Finset J) : product (R := R) s ∈ grading (R := R) (s.card : ℤ) := by
  classical
  exact coverProduct_mem grading MvPolynomial.X variable_mem s

abbrev Piece (s : Finset J) (d : ℤ) :=
  degreePiece (grading (J := J) (R := R)) (grading (J := J) (R := R)) (product (R := R) s) (s.card : ℤ) (product_mem (R := R) s) d

theorem piece_support (s : Finset J) (d : ℤ) (z : Piece (R := R) s d)
    (a : J → ℤ) (ha : (moduleToGroupAlgebra s z.val).coeff a ≠ 0) :
    (∑ j, a j = d) ∧ ∀ j, j ∉ s → 0 ≤ a j := by
  obtain ⟨n, p, hp, hz⟩ := z.property
  rw [hz, moduleToGroupAlgebra_fraction_coefficient] at ha
  obtain ⟨hd, hn⟩ := polynomialToGroupAlgebra_support p hp _ ha
  constructor
  · simp only [Pi.add_apply, Finset.sum_add_distrib,
      sum_productExponent, nsmul_eq_mul, Pi.mul_apply, Pi.natCast_apply, ← Finset.mul_sum] at hd
    omega
  · intro j hj
    simpa only [Pi.add_apply, Pi.smul_apply, productExponent_apply, ite_eq_right hj,
      smul_zero, add_zero] using hn j

def pieceToLaurent (s : Finset J) (d : ℤ) : Piece (R := R) s d →+ Laurent J R d :=
  (Finsupp.subtypeDomainAddMonoidHom (p := fun a : J → ℤ => ∑ j, a j = d)).comp
    ((AddMonoidAlgebra.coeffAddEquiv).toAddMonoidHom.comp
      ((moduleToGroupAlgebra s).comp (degreePiece grading grading (product s)
        s.card (product_mem s) d).subtype))

@[simp] theorem pieceToLaurent_coefficient (s : Finset J) (d : ℤ)
    (z : Piece (R := R) s d) (a : Monomial J d) :
    pieceToLaurent s d z a = (moduleToGroupAlgebra s z.val).coeff a.val := rfl

theorem pieceToLaurent_regular (s : Finset J) (d : ℤ) (z : Piece (R := R) s d) :
    RegularOn (s : Set J) (pieceToLaurent s d z) := by
  intro a ha j hj
  by_contra hjs
  exact (not_lt_of_ge ((piece_support s d z a.val ha).2 j hjs)) hj

theorem pieceToLaurent_injective (s : Finset J) (d : ℤ) :
    Function.Injective (pieceToLaurent (R := R) s d) := by
  intro z w h
  apply Subtype.ext
  apply moduleToGroupAlgebra_injective s
  ext a
  by_cases ha : ∑ j, a j = d
  · exact congrArg (fun l : Laurent J R d => l ⟨a, ha⟩) h
  · have hz : (moduleToGroupAlgebra s z.val).coeff a = 0 := by
      by_contra hz
      exact ha (piece_support s d z a hz).1
    have hw : (moduleToGroupAlgebra s w.val).coeff a = 0 := by
      by_contra hw
      exact ha (piece_support s d w a hw).1
    rw [hz, hw]

theorem exists_cleared_exponent (s : Finset J) (a : J → ℤ)
    (ha : ∀ j, j ∉ s → 0 ≤ a j) :
    ∃ (n : ℕ) (b : J →₀ ℕ), natExponentHom b = a + n • productExponent s := by
  classical
  let n : ℕ := ∑ j, (-a j).toNat
  have hnn : ∀ j, 0 ≤ a j + (n : ℤ) := by
    intro j
    have hn : (-a j).toNat ≤ n :=
      Finset.single_le_sum (fun k _ => Nat.zero_le ((-a k).toNat)) (Finset.mem_univ j)
    have hn' : ((-a j).toNat : ℤ) ≤ (n : ℤ) := by exact_mod_cast hn
    omega
  have hnonneg : ∀ j, 0 ≤ (a + n • productExponent s) j := by
    intro j
    by_cases hj : j ∈ s
    · simpa [Pi.add_apply, Pi.smul_apply, nsmul_eq_mul, productExponent_apply, hj] using hnn j
    · simpa only [Pi.add_apply, Pi.smul_apply, productExponent_apply, ite_eq_right hj,
        smul_zero, add_zero] using ha j hj
  refine ⟨n, Finsupp.equivFunOnFinite.symm (fun j => ((a + n • productExponent s) j).toNat), ?_⟩
  funext j
  exact Int.toNat_of_nonneg (hnonneg j)

theorem single_in_piece_range (s : Finset J) (d : ℤ) (a : Monomial J d) (r : R)
    (ha : ∀ j, j ∉ s → 0 ≤ a.val j) :
    ∃ z : Piece (R := R) s d, pieceToLaurent s d z = Finsupp.single a r := by
  classical
  obtain ⟨n, b, hb⟩ := exists_cleared_exponent s a.val ha
  have hdeg : Finsupp.weight (1 : J → ℤ) b = d + (n : ℤ) * (s.card : ℤ) := by
    simp only [Finsupp.weight_eq_sum, Pi.one_apply, nsmul_eq_mul, mul_one]
    change (∑ j, natExponentHom b j) = _
    rw [hb]
    simp only [Pi.add_apply, Finset.sum_add_distrib,
      sum_productExponent, nsmul_eq_mul, Pi.mul_apply, Pi.natCast_apply, ← Finset.mul_sum, a.property]
  let z : Piece (R := R) s d := ⟨fraction (product s) (MvPolynomial.monomial b r) n,
    n, MvPolynomial.monomial b r, MvPolynomial.isWeightedHomogeneous_monomial _ b r hdeg, rfl⟩
  have hz : moduleToGroupAlgebra s z.val = AddMonoidAlgebra.single a.val r := by
    change moduleToGroupAlgebra s (fraction (product s) (MvPolynomial.monomial b r) n) = _
    rw [moduleToGroupAlgebra_fraction]
    change AddMonoidAlgebra.mapDomain _ (AddMonoidAlgebra.single b r) * _ = _
    rw [AddMonoidAlgebra.mapDomain_single, AddMonoidAlgebra.single_mul_single, hb]
    simp
  refine ⟨z, ?_⟩
  ext a'
  rw [pieceToLaurent_coefficient, hz]
  simp only [AddMonoidAlgebra.coeff_single, Finsupp.single_apply]
  congr 1
  exact propext Subtype.val_inj

theorem pieceToLaurent_surjective_regular (s : Finset J) (d : ℤ) (p : Laurent J R d)
    (hp : RegularOn (s : Set J) p) :
    ∃ z : Piece (R := R) s d, pieceToLaurent s d z = p := by
  classical
  have hs : ∀ a ∈ p.support, ∃ z : Piece (R := R) s d,
      pieceToLaurent s d z = Finsupp.single a (p a) := by
    intro a ha
    apply single_in_piece_range
    intro j hj
    by_contra hn
    exact hj (hp a (Finsupp.mem_support_iff.mp ha) j (lt_of_not_ge hn))
  choose z hz using hs
  refine ⟨∑ a ∈ p.support, if h : a ∈ p.support then z a h else 0, ?_⟩
  rw [map_sum]
  calc
    _ = ∑ a ∈ p.support, Finsupp.single a (p a) := by
      apply Finset.sum_congr rfl
      intro a ha
      simp only [dite_eq_left ha, hz]
    _ = p := p.sum_single

omit [Fintype J] in
theorem moduleToGroupAlgebra_smul (s : Finset J) (p : MvPolynomial J R)
    (z : LocalizedModule (Submonoid.powers (product (R := R) s)) (MvPolynomial J R)) :
    moduleToGroupAlgebra s (p • z) = polynomialToGroupAlgebra p * moduleToGroupAlgebra s z := by
  change ringLocalizationMap s (moduleRingEquiv s (p • z)) =
    polynomialToGroupAlgebra p * ringLocalizationMap s (moduleRingEquiv s z)
  rw [map_smul, Algebra.smul_def, map_mul, ringLocalizationMap_base]

omit [Fintype J] in
theorem moduleToGroupAlgebra_restriction (s t : Finset J)
    (hst : product (R := R) s ∣ product t)
    (z : LocalizedModule (Submonoid.powers (product (R := R) s)) (MvPolynomial J R)) :
    moduleToGroupAlgebra t (restriction (product s) (product t) hst z) =
      moduleToGroupAlgebra s z := by
  induction z using LocalizedModule.induction_on with
  | _ p den =>
    obtain ⟨n, hn⟩ := den.property
    have hden : den = powerDenominator (product (R := R) s) n := Subtype.ext hn.symm
    subst den
    change moduleToGroupAlgebra t (restriction (product s) (product t) hst
      (fraction (product s) p n)) = moduleToGroupAlgebra s (fraction (product s) p n)
    apply ((product_isUnit (R := R) s).pow n).mul_left_cancel
    rw [← map_pow, ← moduleToGroupAlgebra_smul, ← moduleToGroupAlgebra_smul,
      ← map_smul, power_smul_fraction, restriction_fraction_zero]
    simp only [moduleToGroupAlgebra_fraction, zero_smul, neg_zero]

theorem pieceToLaurent_restriction [DecidableEq J] {s t : Finset J} (hst : s ⊆ t)
    (d : ℤ) (z : Piece (R := R) s d) :
    pieceToLaurent t d (setRestriction grading grading MvPolynomial.X variable_mem hst d z) =
      pieceToLaurent s d z := by
  ext a
  change (moduleToGroupAlgebra t (restriction (product s) (product t)
    (coverProduct_dvd grading MvPolynomial.X variable_mem hst) z.val)).coeff a.val =
    (moduleToGroupAlgebra s z.val).coeff a.val
  exact congrArg (fun l : GroupAlgebra (J := J) (R := R) => l.coeff a.val)
    (moduleToGroupAlgebra_restriction s t
      (coverProduct_dvd grading MvPolynomial.X variable_mem hst) z.val)

end
end PiExponent.GradedPolynomialLaurent

end OAI
end Source0772

-- Source: OAI/NumberTheory/PiExponent/Polynomials/NatToIntGrading.lean
section Source0773
/-
Modification notice for the LogTwo project.
Derived from openai/math (Apache-2.0), revision adc7f1241b42e322a6451854ab7e4b4c146bf78a.
Original source: lean/OAI/NumberTheory/PiExponent/Polynomials/NatToIntGrading.lean
Changes: Convert module/import declarations to the Lean 4.34 public module format.
See ../THIRD_PARTY_NOTICES.txt for provenance and the recorded changes.
-/

namespace OAI

namespace PiExponent.NatToIntGrading
noncomputable section
open DirectSum
variable {M σM : Type*} [AddCommGroup M] [SetLike σM M] [AddSubgroupClass σM M]
  (𝓜 : ℕ → σM) [DirectSum.Decomposition 𝓜]

def piece : ℤ → AddSubgroup M
  | .ofNat n => AddSubgroup.ofClass (𝓜 n)
  | .negSucc _ => ⊥

def component (m : M) : ∀ d, piece 𝓜 d
  | .ofNat n => ⟨DirectSum.decompose 𝓜 m n, (DirectSum.decompose 𝓜 m n).property⟩
  | .negSucc _ => 0

def support (m : M) : Finset ℤ := by
  classical
  exact (DirectSum.decompose 𝓜 m).support.image (fun n : ℕ => (n : ℤ))

theorem component_eq_zero_of_not_mem (m : M) (d : ℤ) (hd : d ∉ support 𝓜 m) :
    component 𝓜 m d = 0 := by
  classical
  cases d with
  | ofNat n =>
      apply Subtype.ext
      have hn : n ∉ (DirectSum.decompose 𝓜 m).support := by
        intro hn
        exact hd (Finset.mem_image.mpr ⟨n, hn, rfl⟩)
      change (DirectSum.decompose 𝓜 m n : M) = 0
      rw [DFinsupp.notMem_support_iff.mp hn]
      rfl
  | negSucc n => rfl

def decompositionMap : M →+ ⨁ d, piece 𝓜 d where
  toFun m := DFinsupp.mk' (component 𝓜 m) (Trunc.mk
    ⟨(support 𝓜 m).val, fun d => by
      classical
      by_cases hd : d ∈ support 𝓜 m
      · exact Or.inl hd
      · exact Or.inr (component_eq_zero_of_not_mem 𝓜 m d hd)⟩)
  map_zero' := by
    apply DFinsupp.ext
    intro d
    apply Subtype.ext
    cases d with
    | ofNat n =>
        change (DirectSum.decompose 𝓜 (0 : M) n : M) = 0
        rw [DirectSum.decompose_zero]
        rfl
    | negSucc n => rfl
  map_add' m n := by
    apply DFinsupp.ext
    intro d
    apply Subtype.ext
    cases d with
    | ofNat k =>
        change (DirectSum.decompose 𝓜 (m + n) k : M) =
          (DirectSum.decompose 𝓜 m k : M) + (DirectSum.decompose 𝓜 n k : M)
        rw [DirectSum.decompose_add]
        rfl
    | negSucc k => exact (zero_add (0 : M)).symm

@[simp] theorem decompositionMap_nat (m : M) (n : ℕ) :
    (decompositionMap 𝓜 m (n : ℤ) : M) = (DirectSum.decompose 𝓜 m n : M) := rfl

theorem decompositionMap_injective : Function.Injective (decompositionMap 𝓜) := by
  intro m n h
  apply (DirectSum.decompose 𝓜).injective
  ext k
  exact congrArg (fun z : ⨁ d, piece 𝓜 d => (z (k : ℤ) : M)) h

theorem decompositionMap_homogeneous (d : ℤ) (m : piece 𝓜 d) :
    decompositionMap 𝓜 m.val = DirectSum.of (fun d => piece 𝓜 d) d m := by
  classical
  cases d with
  | negSucc n =>
      have hm : m = 0 := Subtype.ext m.property
      subst m
      simp
  | ofNat n =>
      apply DFinsupp.ext
      intro e
      apply Subtype.ext
      cases e with
      | negSucc k =>
          rw [DirectSum.of_eq_of_ne _ _ _ (show Int.negSucc k ≠ Int.ofNat n from by intro h; cases h)]
          rfl
      | ofNat k =>
          by_cases hnk : n = k
          · subst k
            rw [DirectSum.of_eq_same]
            exact DirectSum.decompose_of_mem_same 𝓜 m.property
          · rw [DirectSum.of_eq_of_ne _ _ _ (show Int.ofNat k ≠ Int.ofNat n from
              fun h => hnk (Int.ofNat.inj h).symm)]
            exact DirectSum.decompose_of_mem_ne 𝓜 m.property hnk

instance decomposition : DirectSum.Decomposition (piece 𝓜) := by
  have hr : (decompositionMap 𝓜).comp (DirectSum.coeAddMonoidHom (piece 𝓜)) = AddMonoidHom.id _ := by
    apply DirectSum.addHom_ext
    intro d m
    simp only [AddMonoidHom.comp_apply, DirectSum.coeAddMonoidHom_of,
      AddMonoidHom.id_apply, decompositionMap_homogeneous]
  apply DirectSum.Decomposition.ofAddHom (piece 𝓜) (decompositionMap 𝓜) ?_ hr
  apply AddMonoidHom.ext
  intro m
  apply decompositionMap_injective 𝓜
  exact DFunLike.congr_fun hr (decompositionMap 𝓜 m)

@[simp] theorem decompose_nat (m : M) (n : ℕ) :
    (DirectSum.decompose (piece 𝓜) m (n : ℤ) : M) = (DirectSum.decompose 𝓜 m n : M) := rfl

@[simp] theorem decompose_negSucc (m : M) (n : ℕ) :
    (DirectSum.decompose (piece 𝓜) m (.negSucc n) : M) = 0 := rfl

section Scalars
variable {R σR : Type*} [Ring R] [Module R M] [SetLike σR R] [AddSubgroupClass σR R]
  (𝒜 : ℕ → σR) [SetLike.GradedSMul 𝒜 𝓜]

instance gradedSMul : SetLike.GradedSMul (piece 𝒜) (piece 𝓜) where
  smul_mem := by
    intro i j a m ha hm
    cases i with
    | negSucc n =>
        have ha' : a = 0 := ha
        rw [ha', zero_smul]
        exact zero_mem _
    | ofNat n =>
        cases j with
        | negSucc k =>
            have hm' : m = 0 := hm
            rw [hm', smul_zero]
            exact zero_mem _
        | ofNat k =>
            change a • m ∈ 𝓜 (n + k)
            exact SetLike.GradedSMul.smul_mem (show a ∈ 𝒜 n from ha) (show m ∈ 𝓜 k from hm)
end Scalars

section Ring
variable {R σR : Type*} [Ring R] [SetLike σR R] [AddSubgroupClass σR R]
  (𝒜 : ℕ → σR) [SetLike.GradedMonoid 𝒜]

instance gradedMonoid : SetLike.GradedMonoid (piece 𝒜) where
  one_mem := by
    change (1 : R) ∈ 𝒜 0
    exact SetLike.GradedOne.one_mem
  mul_mem := by
    intro i j a b ha hb
    cases i with
    | negSucc n =>
        have ha' : a = 0 := ha
        rw [ha', zero_mul]
        exact zero_mem _
    | ofNat n =>
        cases j with
        | negSucc k =>
            have hb' : b = 0 := hb
            rw [hb', mul_zero]
            exact zero_mem _
        | ofNat k =>
            change a * b ∈ 𝒜 (n + k)
            exact SetLike.mul_mem_graded (show a ∈ 𝒜 n from ha) (show b ∈ 𝒜 k from hb)
end Ring

end
end PiExponent.NatToIntGrading

end OAI
end Source0773

-- Source: OAI/NumberTheory/PiExponent/Ampleness/ReesGradedModule.lean
section Source0774
-- Modified in this edition: unused plain lemmas removed; see reduction.json.
/-
Modification notice for the LogTwo project.
Derived from openai/math (Apache-2.0), revision adc7f1241b42e322a6451854ab7e4b4c146bf78a.
Original source: lean/OAI/NumberTheory/PiExponent/Ampleness/ReesGradedModule.lean
Changes: Convert module/import declarations to the Lean 4.34 public module format.
See ../THIRD_PARTY_NOTICES.txt for provenance and the recorded changes.
-/

namespace OAI

namespace PiExponent.ReesGradedModule
noncomputable section
open PiExponentSeshadri.ReesGrading
open PiExponent.ReesPolynomialPresentation PiExponent.GradedPolynomialLaurent
attribute [local instance] MvPolynomial.weightedGradedAlgebra
variable {R J : Type*} [CommRing R] [Fintype J] (I : Ideal R) (a : J → I)

abbrev integerPiece : ℤ → AddSubgroup (reesAlgebra I) :=
  NatToIntGrading.piece (piece I)

instance integerGradedRing : GradedRing (integerPiece I) where
  toGradedMonoid := NatToIntGrading.gradedMonoid (piece I)
  toDecomposition := NatToIntGrading.decomposition (piece I)

def ordinaryPowerEquivIntegerPiece (n : ℕ) : ↥(I ^ n : Ideal R) ≃+ integerPiece I (n : ℤ) :=
  (ReesPushdown.ordinaryPowerEquivPiece I n).toAddEquiv

theorem polynomial_negative_eq_zero (n : ℕ) (p : MvPolynomial J R)
    (hp : p ∈ grading (J := J) (R := R) (.negSucc n)) : p = 0 := by
  apply MvPolynomial.IsWeightedHomogeneous.eq_zero_of_no_monomials hp
  intro b hb
  have hnonneg : 0 ≤ Finsupp.weight (1 : J → ℤ) b := by
    rw [Finsupp.weight_eq_sum]
    exact Finset.sum_nonneg fun j _ => by simp
  omega

theorem presentation_integer_mem {d : ℤ} {p : MvPolynomial J R}
    (hp : p ∈ grading (J := J) (R := R) d) :
    presentation I a p ∈ integerPiece I d := by
  cases d with
  | ofNat n =>
      change presentation I a p ∈ piece I n
      apply presentation_homogeneous_mem I a
      change p ∈ MvPolynomial.weightedHomogeneousSubmodule R (1 : J → ℤ) (n : ℤ) at hp
      rw [GradedH0.integer_grading_eq_homogeneous (R := R) (ι := J) n] at hp
      exact hp
  | negSucc n =>
      rw [polynomial_negative_eq_zero n p hp, map_zero]
      exact zero_mem _

def gradedPresentation : grading (J := J) (R := R) →+*ᵍ integerPiece I where
  __ := (presentation I a).toRingHom
  map_mem := presentation_integer_mem I a

theorem gradedScalarAction :
    letI := presentationAlgebra I a
    SetLike.GradedSMul (grading (J := J) (R := R)) (integerPiece I) := by
  let := presentationAlgebra I a
  constructor
  intro i j p z hp hz
  change presentation I a p * z ∈ integerPiece I (i + j)
  exact SetLike.mul_mem_graded (presentation_integer_mem I a hp) hz

end
end PiExponent.ReesGradedModule

end OAI
end Source0774

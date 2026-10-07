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
public import LogTwoCheckpoints.Part019
public import LogTwoCheckpoints.Part023
public import LogTwoCheckpoints.Part024
public import LogTwoCheckpoints.Part025
public import Mathlib.Algebra.Category.Grp.Zero
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.EpiMono
public import Mathlib.Algebra.Homology.DerivedCategory.Ext.ExactSequences
public import Mathlib.Algebra.Module.Torsion.Basic
public import Mathlib.AlgebraicGeometry.IdealSheaf.Functorial
public import Mathlib.AlgebraicGeometry.Modules.Tilde
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.Analysis.Complex.Polynomial.Basic
public import Mathlib.Data.Opposite
public import Mathlib.Data.SetLike.Basic
@[expose] public section
set_option Elab.async false

-- Source: OAI/NumberTheory/PiExponent/Cohomology/IdealPowerCohomology.lean
section Source0650
/-
Modification notice for the LogTwo project.
Derived from openai/math (Apache-2.0), revision adc7f1241b42e322a6451854ab7e4b4c146bf78a.
Original source: lean/OAI/NumberTheory/PiExponent/Cohomology/IdealPowerCohomology.lean
Changes: Convert module/import declarations to the Lean 4.34 public module format.
See ../THIRD_PARTY_NOTICES.txt for provenance and the recorded changes.
-/

namespace OAI

namespace PiExponentSeshadri.IdealModule
noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian
open PiExponentSeshadri.Geometry
variable {X : Scheme.{0}}
local instance : HasExt.{1} X.Modules := HasExt.standard _

theorem ext_eq_zero_of_isZero (A M : X.Modules) (hM : IsZero M) (q : ℕ)
    (x : Abelian.Ext.{1} A M q) : x = 0 := by
  have hz := (extFunctorObj A q).map_isZero hM
  exact @Subsingleton.elim _ (AddCommGrpCat.subsingleton_of_isZero hz) x 0

theorem powerModule_twist_ext_zero_of_layers (I : X.IdealSheafData) (L : LineBundle X)
    (N n q : ℕ) (hN : IsZero (closedModule (I^N)))
    (hLayer : ∀ k < N, ∀ x : Abelian.Ext.{1} (structureSheaf X)
      ((moduleTwistFunctor L n).obj (powerLayer I k)) q, x = 0)
    (k : ℕ) (hk : k ≤ N)
    (x : Abelian.Ext.{1} (structureSheaf X)
      ((moduleTwistFunctor L n).obj (closedModule (I^k))) q) : x = 0 := by
  have hzero : ∀ k ≤ N, ∀ x : Abelian.Ext.{1} (structureSheaf X)
      ((moduleTwistFunctor L n).obj (closedModule (I^k))) q, x = 0 := by
    intro k hk
    induction hk using Nat.decreasingInduction with
    | self =>
      exact ext_eq_zero_of_isZero _ _ ((moduleTwistFunctor L n).map_isZero hN) q
    | @of_succ k hk ih =>
      intro x
      let S := (powerSequence I k).map (moduleTwistFunctor L n)
      have hS : S.ShortExact := moduleTwistFunctor_shortExact L n _ (powerSequence_shortExact I k)
      obtain ⟨y,hy⟩ := Ext.covariant_sequence_exact₂ (structureSheaf X) hS x
        (hLayer k hk _)
      have hiy : y = 0 := ih y
      exact hy.symm.trans
        ((congrArg (fun z : Abelian.Ext.{1} (structureSheaf X) S.X₁ q =>
          z.comp (Ext.mk₀ S.f) (add_zero q)) hiy).trans
            (Ext.zero_comp (structureSheaf X) q (Ext.mk₀ S.f) q (add_zero q)))
  exact hzero k hk x

theorem powerModule_ext_zero_of_layers (I : X.IdealSheafData)
    (N q : ℕ) (hN : IsZero (closedModule (I^N)))
    (hLayer : ∀ k < N, ∀ x : Abelian.Ext.{1} (structureSheaf X) (powerLayer I k) q, x = 0)
    (k : ℕ) (hk : k ≤ N)
    (x : Abelian.Ext.{1} (structureSheaf X) (closedModule (I^k)) q) : x = 0 := by
  let L : LineBundle X := {
    sheaf := structureSheaf X
    locallyRankOne := fun x => ⟨⊤, trivial, ⟨Scheme.Modules.restrictUnitIso _⟩⟩ }
  exact powerModule_twist_ext_zero_of_layers I L N 0 q hN hLayer k hk x

attribute [local irreducible] closedModule moduleTwistFunctor powerLayer

theorem eventual_ideal_twist_vanishing_of_layers [IsNoetherian X]
    (I : X.IdealSheafData) (hI : I.support = ⊤) (L : LineBundle X)
    (hLayer : ∀ k, ∃ B, ∀ n, B ≤ n → ∀ q, 0 < q →
      ∀ x : Abelian.Ext.{1} (structureSheaf X)
        ((moduleTwistFunctor L n).obj (powerLayer I k)) q, x = 0) :
    ∃ B, ∀ n, B ≤ n → ∀ q, 0 < q →
      ∀ x : Abelian.Ext.{1} (structureSheaf X)
        ((moduleTwistFunctor L n).obj (closedModule I)) q, x = 0 := by
  classical
  obtain ⟨N,hNpos,hN⟩ := powerModule_eventually_isZero I hI
  choose B hB using hLayer
  refine ⟨(Finset.range N).sup B, fun n hn q hq x => ?_⟩
  have hL (k : ℕ) (hk : k < N) := hB k n
    ((Finset.le_sup (Finset.mem_range.mpr hk)).trans hn) q hq
  have h := powerModule_twist_ext_zero_of_layers I L N n q hN hL 1 hNpos
  have h' : ∀ z : Abelian.Ext.{1} (structureSheaf X)
      ((moduleTwistFunctor L n).obj (closedModule I)) q, z = 0 := by
    exact (congrArg (fun J : X.IdealSheafData =>
      ∀ z : Abelian.Ext.{1} (structureSheaf X)
        ((moduleTwistFunctor L n).obj (closedModule J)) q, z = 0) (pow_one I)).mp h
  exact h' x
end
end PiExponentSeshadri.IdealModule

end OAI
end Source0650

-- Source: OAI/NumberTheory/PiExponent/Approximation/ClosedAnnihilatedDescent.lean
section Source0651
-- Modified in this edition: unused plain lemmas removed; see reduction.json.
/-
Modification notice for the LogTwo project.
Derived from openai/math (Apache-2.0), revision adc7f1241b42e322a6451854ab7e4b4c146bf78a.
Original source: lean/OAI/NumberTheory/PiExponent/Approximation/ClosedAnnihilatedDescent.lean
Changes: Convert module/import declarations to the Lean 4.34 public module format.
See ../THIRD_PARTY_NOTICES.txt for provenance and the recorded changes.
-/

namespace OAI

namespace PiExponentSeshadri.ClosedAnnihilatedDescent
noncomputable section
open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite
variable {R S : CommRingCat.{0}}

def specPushforwardSectionsIso (φ : R ⟶ S) (N : (Spec S).Modules) :
    moduleSpecΓFunctor.obj ((Scheme.Modules.pushforward (Spec.map φ)).obj N) ≅
      (ModuleCat.restrictScalars φ.hom).obj (moduleSpecΓFunctor.obj N) := by
  let E : TopCat.Sheaf (ModuleCat R) (Spec R) ⥤ ModuleCat R :=
    TopCat.Sheaf.forget _ _ ⋙ (evaluation _ _).obj (op ⊤)
  exact E.mapIso ((pushforwardCompModulesSpecToSheafIso φ).app N)

def specPushforwardTildeIso (φ : R ⟶ S) (N : ModuleCat S) :
    (Scheme.Modules.pushforward (Spec.map φ)).obj (tilde N) ≅
      tilde ((ModuleCat.restrictScalars φ.hom).obj N) := by
  let P := (Scheme.Modules.pushforward (Spec.map φ)).obj (tilde N)
  let : IsIso P.fromTildeΓ := isIso_fromTildeΓ_pushforward φ (tilde N)
  exact (asIso P.fromTildeΓ).symm ≪≫ (tilde.functor R).mapIso
    (specPushforwardSectionsIso φ (tilde N) ≪≫
      (ModuleCat.restrictScalars φ.hom).mapIso (tilde.isoTop N).symm)

def quotientModule (I : Ideal R) (M : ModuleCat R)
    (h : I ≤ Module.annihilator R M) : ModuleCat (CommRingCat.of (R ⧸ I)) := by
  let ht : Module.IsTorsionBySet R M I := fun {x} {a} =>
    Module.mem_annihilator.mp (h a.property) x
  letI := ht.module
  exact ModuleCat.of _ M

def quotientModuleRestrictIso (I : Ideal R) (M : ModuleCat R)
    (h : I ≤ Module.annihilator R M) :
    (ModuleCat.restrictScalars (Ideal.Quotient.mk I)).obj (quotientModule I M h) ≅ M :=
  Iso.refl M

def affineDescent (I : Ideal R) (M : (Spec R).Modules)
    (h : I ≤ Module.annihilator R (moduleSpecΓFunctor.obj M)) :
    (Spec (CommRingCat.of (R ⧸ I))).Modules :=
  tilde (quotientModule I (moduleSpecΓFunctor.obj M) h)

instance affineDescent_isQuasicoherent (I : Ideal R) (M : (Spec R).Modules)
    (h : I ≤ Module.annihilator R (moduleSpecΓFunctor.obj M)) :
    (affineDescent I M h).IsQuasicoherent := by
  unfold affineDescent
  infer_instance

def affineDescentPushforwardIso (I : Ideal R) (M : (Spec R).Modules) [M.IsQuasicoherent]
    (h : I ≤ Module.annihilator R (moduleSpecΓFunctor.obj M)) :
    (Scheme.Modules.pushforward (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I)))).obj
      (affineDescent I M h) ≅ M :=
  specPushforwardTildeIso _ _ ≪≫
    (tilde.functor R).mapIso (quotientModuleRestrictIso I (moduleSpecΓFunctor.obj M) h) ≪≫
      @asIso _ _ _ _ M.fromTildeΓ
        (Scheme.Modules.isIso_fromTildeΓ_of_isQuasicoherent M)

instance quotientModule_finite (I : Ideal R) (M : ModuleCat R) [Module.Finite R M]
    (h : I ≤ Module.annihilator R M) :
    Module.Finite (CommRingCat.of (R ⧸ I)) (quotientModule I M h) := by
  let ht : Module.IsTorsionBySet R M I := fun {x} {a} =>
    Module.mem_annihilator.mp (h a.property) x
  let := ht.module
  let : IsScalarTower R (R ⧸ I) M := ht.isScalarTower
  change Module.Finite (R ⧸ I) M
  exact Module.Finite.of_restrictScalars_finite R (R ⧸ I) M

end
end PiExponentSeshadri.ClosedAnnihilatedDescent

end OAI
end Source0651

-- Source: OAI/NumberTheory/PiExponent/Approximation/AffineClosedAnnihilatedDescent.lean
section Source0652
/-
Modification notice for the LogTwo project.
Derived from openai/math (Apache-2.0), revision adc7f1241b42e322a6451854ab7e4b4c146bf78a.
Original source: lean/OAI/NumberTheory/PiExponent/Approximation/AffineClosedAnnihilatedDescent.lean
Changes: Convert module/import declarations to the Lean 4.34 public module format.
See ../THIRD_PARTY_NOTICES.txt for provenance and the recorded changes.
-/

namespace OAI

namespace PiExponentSeshadri.ClosedAnnihilatedDescent
noncomputable section
open CategoryTheory AlgebraicGeometry TopologicalSpace Opposite
variable {R S : CommRingCat.{0}}

def surjectiveModule (φ : R ⟶ S) (hφ : Function.Surjective φ) (M : ModuleCat R)
    (h : RingHom.ker φ.hom ≤ Module.annihilator R M) : ModuleCat S :=
  (ModuleCat.restrictScalars (φ.hom.quotientKerEquivOfSurjective hφ).symm.toRingHom).obj
    (quotientModule (RingHom.ker φ.hom) M h)

def surjectiveModuleRestrictIso (φ : R ⟶ S) (hφ : Function.Surjective φ)
    (M : ModuleCat R) (h : RingHom.ker φ.hom ≤ Module.annihilator R M) :
    (ModuleCat.restrictScalars φ.hom).obj (surjectiveModule φ hφ M h) ≅ M :=
  (ModuleCat.restrictScalarsComp'App φ.hom
    (φ.hom.quotientKerEquivOfSurjective hφ).symm.toRingHom
    (Ideal.Quotient.mk (RingHom.ker φ.hom))
    (RingHom.quotientKerEquivOfSurjective_symm_comp hφ).symm
    (quotientModule (RingHom.ker φ.hom) M h)).symm ≪≫ quotientModuleRestrictIso _ M h

def specSurjectiveDescent (φ : R ⟶ S) (hφ : Function.Surjective φ)
    (M : (Spec R).Modules)
    (h : RingHom.ker φ.hom ≤ Module.annihilator R (moduleSpecΓFunctor.obj M)) :
    (Spec S).Modules := tilde (surjectiveModule φ hφ (moduleSpecΓFunctor.obj M) h)

def specSurjectiveDescentPushforwardIso (φ : R ⟶ S) (hφ : Function.Surjective φ)
    (M : (Spec R).Modules) [M.IsQuasicoherent]
    (h : RingHom.ker φ.hom ≤ Module.annihilator R (moduleSpecΓFunctor.obj M)) :
    (Scheme.Modules.pushforward (Spec.map φ)).obj (specSurjectiveDescent φ hφ M h) ≅ M :=
  specPushforwardTildeIso _ _ ≪≫
    (tilde.functor R).mapIso (surjectiveModuleRestrictIso φ hφ (moduleSpecΓFunctor.obj M) h) ≪≫
      @asIso _ _ _ _ M.fromTildeΓ
        (Scheme.Modules.isIso_fromTildeΓ_of_isQuasicoherent M)

variable {X Y : Scheme.{0}}

def affineSpecTopSections [IsAffine X] (M : X.Modules) :
    moduleSpecΓFunctor.obj (PiExponent.GlobalSectionClearing.affineToSpecModule M) ≃ₗ[Γ(X,⊤)]
      Γ(M,⊤) where
  toFun := fun x => x
  invFun := fun x => x
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' r m := by
    change @SMul.smul Γ(X,⊤) Γ(M,⊤) (M.val.obj (op ⊤)).isModule.toSMul
      ((X.toSpecΓ.app ⊤)
        ((Spec Γ(X,⊤)).presheaf.map (homOfLE (show (⊤ : (Spec Γ(X,⊤)).Opens) ≤ ⊤ from le_top)).op
          ((Scheme.ΓSpecIso Γ(X,⊤)).inv r))) m =
      @SMul.smul Γ(X,⊤) Γ(M,⊤) (M.val.obj (op ⊤)).isModule.toSMul r m
    apply congrArg (fun a : Γ(X,⊤) =>
      @SMul.smul Γ(X,⊤) Γ(M,⊤) (M.val.obj (op ⊤)).isModule.toSMul a m)
    have hi : (homOfLE (show (⊤ : (Spec Γ(X,⊤)).Opens) ≤ ⊤ from le_top)).op = 𝟙 _ := rfl
    rw [hi, CategoryTheory.Functor.map_id]
    change X.toSpecΓ.appTop ((Scheme.ΓSpecIso Γ(X,⊤)).inv r) = r
    rw [Scheme.toSpecΓ_appTop]
    exact (Scheme.ΓSpecIso Γ(X,⊤)).inv_hom_id_apply r

lemma affineSpecTopSections_annihilator [IsAffine X] (M : X.Modules) (I : Ideal Γ(X,⊤))
    (h : I ≤ Module.annihilator Γ(X,⊤) Γ(M,⊤)) :
    I ≤ Module.annihilator Γ(X,⊤)
      (moduleSpecΓFunctor.obj (PiExponent.GlobalSectionClearing.affineToSpecModule M)) := by
  intro r hr
  rw [Module.mem_annihilator] at *
  intro m
  apply (affineSpecTopSections M).injective
  rw [map_smul, map_zero]
  exact Module.mem_annihilator.mp (h hr) _

def affineDescentAlong [IsAffine X] [IsAffine Y] (f : Y ⟶ X)
    (hf : Function.Surjective f.appTop) (M : X.Modules)
    (h : RingHom.ker f.appTop.hom ≤ Module.annihilator Γ(X,⊤) Γ(M,⊤)) : Y.Modules :=
  (Scheme.Modules.pushforward Y.isoSpec.inv).obj
    (specSurjectiveDescent f.appTop hf
      (PiExponent.GlobalSectionClearing.affineToSpecModule M)
      (affineSpecTopSections_annihilator M _ h))

def affineDescentAlongPushforwardIso [IsAffine X] [IsAffine Y] (f : Y ⟶ X)
    (hf : Function.Surjective f.appTop) (M : X.Modules) [M.IsQuasicoherent]
    (h : RingHom.ker f.appTop.hom ≤ Module.annihilator Γ(X,⊤) Γ(M,⊤)) :
    (Scheme.Modules.pushforward f).obj (affineDescentAlong f hf M h) ≅ M := by
  let A := specSurjectiveDescent f.appTop hf
    (PiExponent.GlobalSectionClearing.affineToSpecModule M)
    (affineSpecTopSections_annihilator M _ h)
  exact (Scheme.Modules.pushforwardComp Y.isoSpec.inv f).app A ≪≫
    (Scheme.Modules.pushforwardCongr (Scheme.isoSpec_inv_naturality f).symm).app A ≪≫
    ((Scheme.Modules.pushforwardComp (Spec.map f.appTop) X.isoSpec.inv).app A).symm ≪≫
    (Scheme.Modules.pushforward X.isoSpec.inv).mapIso
      (specSurjectiveDescentPushforwardIso f.appTop hf
        (PiExponent.GlobalSectionClearing.affineToSpecModule M)
        (affineSpecTopSections_annihilator M _ h)) ≪≫
    (Scheme.Modules.pushforwardComp X.isoSpec.hom X.isoSpec.inv).app M ≪≫
    (Scheme.Modules.pushforwardCongr X.isoSpec.hom_inv_id).app M ≪≫
    (Scheme.Modules.pushforwardId X).app M

theorem exists_affine_closed_descent [IsAffine X] (f : Y ⟶ X) [IsClosedImmersion f]
    (M : X.Modules) [M.IsQuasicoherent]
    (h : RingHom.ker f.appTop.hom ≤ Module.annihilator Γ(X,⊤) Γ(M,⊤)) :
    ∃ N : Y.Modules, Nonempty ((Scheme.Modules.pushforward f).obj N ≅ M) := by
  obtain ⟨hY, hf⟩ := IsClosedImmersion.isAffine_surjective_of_isAffine f
  exact ⟨affineDescentAlong f hf M h, ⟨affineDescentAlongPushforwardIso f hf M h⟩⟩

end
end PiExponentSeshadri.ClosedAnnihilatedDescent

end OAI
end Source0652

-- Source: OAI/NumberTheory/PiExponent/Approximation/ClosedPullbackUnit.lean
section Source0653
-- Modified in this edition: unused plain lemmas removed; see reduction.json.
/-
Modification notice for the LogTwo project.
Derived from openai/math (Apache-2.0), revision adc7f1241b42e322a6451854ab7e4b4c146bf78a.
Original source: lean/OAI/NumberTheory/PiExponent/Approximation/ClosedPullbackUnit.lean
Changes: Convert module/import declarations to the Lean 4.34 public module format.
See ../THIRD_PARTY_NOTICES.txt for provenance and the recorded changes.
-/

namespace OAI

namespace PiExponentSeshadri.ClosedPullbackUnit
noncomputable section
open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite
variable {X Y : Scheme.{0}} (f : Y ⟶ X)

def opensEquivalence [IsIso f.base] : X.Opens ≌ Y.Opens :=
  Opens.mapMapIso (asIso f.base)

lemma preimage_surjective [IsIso f.base] :
    Function.Surjective (fun U : X.Opens => f ⁻¹ᵁ U) := by
  intro V
  refine ⟨(opensEquivalence f).inverse.obj V, ?_⟩
  exact le_antisymm (leOfHom ((opensEquivalence f).counitIso.app V).hom)
    (leOfHom ((opensEquivalence f).counitIso.app V).inv)

def additivePreimage [IsIso f.base] {M N : Y.Modules}
    (a : (Scheme.Modules.pushforward f).obj M ⟶ (Scheme.Modules.pushforward f).obj N) :
    M.presheaf ⟶ N.presheaf := by
  let : (Opens.map f.base).IsEquivalence := (opensEquivalence f).isEquivalence_functor
  exact ((Functor.whiskeringLeft _ _ AddCommGrpCat).obj (Opens.map f.base).op).preimage a.mapPresheaf

lemma additivePreimage_app [IsIso f.base] {M N : Y.Modules}
    (a : (Scheme.Modules.pushforward f).obj M ⟶ (Scheme.Modules.pushforward f).obj N)
    (U : X.Opens) : (additivePreimage f a).app (op (f ⁻¹ᵁ U)) = a.app U := by
  let : (Opens.map f.base).IsEquivalence := (opensEquivalence f).isEquivalence_functor
  exact congrArg (fun b : (Opens.map f.base).op ⋙ M.presheaf ⟶
      (Opens.map f.base).op ⋙ N.presheaf => b.app (op U))
    (((Functor.whiskeringLeft _ _ AddCommGrpCat).obj (Opens.map f.base).op).map_preimage (X := M.presheaf) (Y := N.presheaf) a.mapPresheaf)

lemma additivePreimage_smul [IsClosedImmersion f] [IsIso f.base]
    {M N : Y.Modules}
    (a : (Scheme.Modules.pushforward f).obj M ⟶ (Scheme.Modules.pushforward f).obj N)
    (V : Y.Opens) (r : Γ(Y,V)) (m : Γ(M,V)) :
    (additivePreimage f a).app (op V) (r • m) =
      r • (additivePreimage f a).app (op V) m := by
  obtain ⟨U, rfl⟩ := preimage_surjective f V
  apply N.isSheaf.section_ext
  intro y hy
  obtain ⟨W, hW, hyW, hWU⟩ := exists_isAffineOpen_mem_and_subset (X := X) (x := f y) (U := U) hy
  let j : W ⟶ U := homOfLE hWU
  let k : f ⁻¹ᵁ W ⟶ f ⁻¹ᵁ U := (Opens.map f.base).map j
  refine ⟨f ⁻¹ᵁ W, leOfHom k, hyW, ?_⟩
  have hn (z : Γ(M,f ⁻¹ᵁ U)) :
      (additivePreimage f a).app (op (f ⁻¹ᵁ W)) (M.presheaf.map k.op z) =
        N.presheaf.map k.op ((additivePreimage f a).app (op (f ⁻¹ᵁ U)) z) :=
    CategoryTheory.congr_fun ((additivePreimage f a).naturality k.op) z
  have hs : N.presheaf.map k.op (r • (additivePreimage f a).app (op (f ⁻¹ᵁ U)) m) =
      Y.presheaf.map k.op r • N.presheaf.map k.op ((additivePreimage f a).app (op (f ⁻¹ᵁ U)) m) :=
    N.val.map_smul k.op r ((additivePreimage f a).app (op (f ⁻¹ᵁ U)) m)
  change N.presheaf.map k.op ((additivePreimage f a).app (op (f ⁻¹ᵁ U)) (r • m)) =
    N.presheaf.map k.op (r • (additivePreimage f a).app (op (f ⁻¹ᵁ U)) m)
  rw [← hn, hs, ← hn, additivePreimage_app]
  obtain ⟨c, hc⟩ := f.app_surjective W hW (Y.presheaf.map k.op r)
  have hm := M.val.map_smul k.op r m
  change M.presheaf.map k.op (r • m) = Y.presheaf.map k.op r • M.presheaf.map k.op m at hm
  rw [hm, ← hc]
  exact a.app_smul (r := c) (x := M.presheaf.map k.op m)

def modulePreimage [IsClosedImmersion f] [IsIso f.base] {M N : Y.Modules}
    (a : (Scheme.Modules.pushforward f).obj M ⟶ (Scheme.Modules.pushforward f).obj N) :
    M ⟶ N where
  val.app V := ModuleCat.ofHom (X := M.val.obj V) (Y := N.val.obj V)
    { toAddHom := ((additivePreimage f a).app V).hom.toAddHom
      map_smul' := fun r m => additivePreimage_smul f a V.unop r m }
  val.naturality {V W} j := by
    ext m
    exact CategoryTheory.congr_fun ((additivePreimage f a).naturality j) m

def pushforwardFullyFaithful [IsClosedImmersion f] [IsIso f.base] :
    (Scheme.Modules.pushforward f).FullyFaithful where
  preimage a := modulePreimage f a
  map_preimage a := by
    ext U m
    exact CategoryTheory.congr_fun (additivePreimage_app f a U) m
  preimage_map a := by
    apply Scheme.Modules.hom_ext
    intro V
    obtain ⟨U, rfl⟩ := preimage_surjective f V
    exact additivePreimage_app f ((Scheme.Modules.pushforward f).map a) U

theorem counit_isIso [IsClosedImmersion f] (hf : Function.Surjective f) :
    IsIso (Scheme.Modules.pullbackPushforwardAdjunction f).counit := by
  let : IsIso f.base := (TopCat.isIso_iff_isHomeomorph f.base).mpr
    (isHomeomorph_iff_isEmbedding_surjective.mpr ⟨f.isClosedEmbedding.isEmbedding, hf⟩)
  let := (pushforwardFullyFaithful f).full
  let := (pushforwardFullyFaithful f).faithful
  exact (Scheme.Modules.pullbackPushforwardAdjunction f).counit_isIso_of_R_fully_faithful

theorem unit_isIso_of_pushforward [IsClosedImmersion f] (hf : Function.Surjective f)
    {M : X.Modules} {N : Y.Modules}
    (e : M ≅ (Scheme.Modules.pushforward f).obj N) :
    IsIso ((Scheme.Modules.pullbackPushforwardAdjunction f).unit.app M) := by
  let : IsIso (Scheme.Modules.pullbackPushforwardAdjunction f).counit := counit_isIso f hf
  let := (Scheme.Modules.pullbackPushforwardAdjunction f).fullyFaithfulROfIsIsoCounit.full
  let := (Scheme.Modules.pullbackPushforwardAdjunction f).fullyFaithfulROfIsIsoCounit.faithful
  exact (Scheme.Modules.pullbackPushforwardAdjunction f).isIso_unit_app_of_iso e

end
end PiExponentSeshadri.ClosedPullbackUnit

end OAI
end Source0653

-- Source: OAI/NumberTheory/PiExponent/Approximation/ClosedImmersionModules.lean
section Source0654
/-
Modification notice for the LogTwo project.
Derived from openai/math (Apache-2.0), revision adc7f1241b42e322a6451854ab7e4b4c146bf78a.
Original source: lean/OAI/NumberTheory/PiExponent/Approximation/ClosedImmersionModules.lean
Changes: Convert module/import declarations to the Lean 4.34 public module format.
See ../THIRD_PARTY_NOTICES.txt for provenance and the recorded changes.
-/

namespace OAI

namespace PiExponentSeshadri.ClosedImmersionModules
noncomputable section
open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite
variable {X Y : Scheme.{0}} (f : Y ⟶ X)

def additiveFullyFaithful [IsClosedImmersion f] :
    ((Functor.whiskeringLeft _ _ AddCommGrpCat).obj (Opens.map f.base).op).FullyFaithful := by
  let h := f.isClosedEmbedding.isEmbedding.isInducing
  let adj := h.adjunction
  have hc (V : Y.Opens) : IsIso (adj.counit.app V) := by
    have he : adj.counit.app V = eqToHom (h.map_functorObj V) := Subsingleton.elim _ _
    exact he.symm ▸ (eqToIso (h.map_functorObj V)).isIso_hom
  let : IsIso adj.counit := NatIso.isIso_of_isIso_app _
  let := adj.fullyFaithfulROfIsIsoCounit.full
  let := adj.fullyFaithfulROfIsIsoCounit.faithful
  let W := (MorphismProperty.isomorphisms Y.Opens).inverseImage (Opens.map f.base)
  let : (Opens.map f.base).IsLocalization W := adj.isLocalization
  let : (Opens.map f.base).op.IsLocalization W.op :=
    (Functor.IsLocalization.op_iff (Opens.map f.base) W).mpr inferInstance
  exact Localization.fullyFaithfulWhiskeringLeft (Opens.map f.base).op W.op AddCommGrpCat

lemma preimage_surjective [IsClosedImmersion f] :
    Function.Surjective (fun U : X.Opens => f ⁻¹ᵁ U) := by
  intro V
  let h := f.isClosedEmbedding.isEmbedding.isInducing
  exact ⟨h.functorObj V, h.map_functorObj V⟩

def additivePreimage [IsClosedImmersion f] {M N : Y.Modules}
    (a : (Scheme.Modules.pushforward f).obj M ⟶ (Scheme.Modules.pushforward f).obj N) :
    M.presheaf ⟶ N.presheaf :=
  (additiveFullyFaithful f).preimage a.mapPresheaf

lemma additivePreimage_app [IsClosedImmersion f] {M N : Y.Modules}
    (a : (Scheme.Modules.pushforward f).obj M ⟶ (Scheme.Modules.pushforward f).obj N)
    (U : X.Opens) : (additivePreimage f a).app (op (f ⁻¹ᵁ U)) = a.app U := by
  exact congrArg (fun b : (Opens.map f.base).op ⋙ M.presheaf ⟶
      (Opens.map f.base).op ⋙ N.presheaf => b.app (op U))
    ((additiveFullyFaithful f).map_preimage (X := M.presheaf) (Y := N.presheaf) a.mapPresheaf)

lemma additivePreimage_smul [IsClosedImmersion f]
    {M N : Y.Modules}
    (a : (Scheme.Modules.pushforward f).obj M ⟶ (Scheme.Modules.pushforward f).obj N)
    (V : Y.Opens) (r : Γ(Y,V)) (m : Γ(M,V)) :
    (additivePreimage f a).app (op V) (r • m) =
      r • (additivePreimage f a).app (op V) m := by
  obtain ⟨U, rfl⟩ := preimage_surjective f V
  apply N.isSheaf.section_ext
  intro y hy
  obtain ⟨W, hW, hyW, hWU⟩ := exists_isAffineOpen_mem_and_subset (X := X) (x := f y) (U := U) hy
  let j : W ⟶ U := homOfLE hWU
  let k : f ⁻¹ᵁ W ⟶ f ⁻¹ᵁ U := (Opens.map f.base).map j
  refine ⟨f ⁻¹ᵁ W, leOfHom k, hyW, ?_⟩
  have hn (z : Γ(M,f ⁻¹ᵁ U)) :
      (additivePreimage f a).app (op (f ⁻¹ᵁ W)) (M.presheaf.map k.op z) =
        N.presheaf.map k.op ((additivePreimage f a).app (op (f ⁻¹ᵁ U)) z) :=
    CategoryTheory.congr_fun ((additivePreimage f a).naturality k.op) z
  have hs : N.presheaf.map k.op (r • (additivePreimage f a).app (op (f ⁻¹ᵁ U)) m) =
      Y.presheaf.map k.op r • N.presheaf.map k.op ((additivePreimage f a).app (op (f ⁻¹ᵁ U)) m) :=
    N.val.map_smul k.op r ((additivePreimage f a).app (op (f ⁻¹ᵁ U)) m)
  change N.presheaf.map k.op ((additivePreimage f a).app (op (f ⁻¹ᵁ U)) (r • m)) =
    N.presheaf.map k.op (r • (additivePreimage f a).app (op (f ⁻¹ᵁ U)) m)
  rw [← hn, hs, ← hn, additivePreimage_app]
  obtain ⟨c, hc⟩ := f.app_surjective W hW (Y.presheaf.map k.op r)
  have hm := M.val.map_smul k.op r m
  change M.presheaf.map k.op (r • m) = Y.presheaf.map k.op r • M.presheaf.map k.op m at hm
  rw [hm, ← hc]
  exact a.app_smul (r := c) (x := M.presheaf.map k.op m)

def modulePreimage [IsClosedImmersion f] {M N : Y.Modules}
    (a : (Scheme.Modules.pushforward f).obj M ⟶ (Scheme.Modules.pushforward f).obj N) :
    M ⟶ N where
  val.app V := ModuleCat.ofHom (X := M.val.obj V) (Y := N.val.obj V)
    { toAddHom := ((additivePreimage f a).app V).hom.toAddHom
      map_smul' := fun r m => additivePreimage_smul f a V.unop r m }
  val.naturality {V W} j := by
    ext m
    exact CategoryTheory.congr_fun ((additivePreimage f a).naturality j) m

def pushforwardFullyFaithful [IsClosedImmersion f] :
    (Scheme.Modules.pushforward f).FullyFaithful where
  preimage a := modulePreimage f a
  map_preimage a := by
    ext U m
    exact CategoryTheory.congr_fun (additivePreimage_app f a U) m
  preimage_map a := by
    apply Scheme.Modules.hom_ext
    intro V
    obtain ⟨U, rfl⟩ := preimage_surjective f V
    exact additivePreimage_app f ((Scheme.Modules.pushforward f).map a) U

theorem counit_isIso [IsClosedImmersion f]  :
    IsIso (Scheme.Modules.pullbackPushforwardAdjunction f).counit := by
  let := (pushforwardFullyFaithful f).full
  let := (pushforwardFullyFaithful f).faithful
  exact (Scheme.Modules.pullbackPushforwardAdjunction f).counit_isIso_of_R_fully_faithful

theorem unit_isIso_of_pushforward [IsClosedImmersion f]
    {M : X.Modules} {N : Y.Modules}
    (e : M ≅ (Scheme.Modules.pushforward f).obj N) :
    IsIso ((Scheme.Modules.pullbackPushforwardAdjunction f).unit.app M) := by
  let : IsIso (Scheme.Modules.pullbackPushforwardAdjunction f).counit := counit_isIso f
  let := (Scheme.Modules.pullbackPushforwardAdjunction f).fullyFaithfulROfIsIsoCounit.full
  let := (Scheme.Modules.pullbackPushforwardAdjunction f).fullyFaithfulROfIsIsoCounit.faithful
  exact (Scheme.Modules.pullbackPushforwardAdjunction f).isIso_unit_app_of_iso e

end
end PiExponentSeshadri.ClosedImmersionModules

end OAI
end Source0654

-- Source: OAI/NumberTheory/PiExponent/Approximation/ClosedPullbackUnitRestriction.lean
section Source0655
-- Modified in this edition: unused plain lemmas removed; see reduction.json.
/-
Modification notice for the LogTwo project.
Derived from openai/math (Apache-2.0), revision adc7f1241b42e322a6451854ab7e4b4c146bf78a.
Original source: lean/OAI/NumberTheory/PiExponent/Approximation/ClosedPullbackUnitRestriction.lean
Changes: Convert module/import declarations to the Lean 4.34 public module format.
See ../THIRD_PARTY_NOTICES.txt for provenance and the recorded changes.
-/

namespace OAI

namespace PiExponentSeshadri.ClosedPullbackUnitRestriction
noncomputable section
open CategoryTheory AlgebraicGeometry TopologicalSpace
variable {X Y : Scheme.{0}} (f : Y ⟶ X)

lemma restrict_unit_isIso_iff (U : X.Opens) (M : X.Modules) :
    IsIso ((Scheme.Modules.restrictFunctor U.ι).map
      ((Scheme.Modules.pullbackPushforwardAdjunction f).unit.app M)) ↔
    IsIso ((Scheme.Modules.pullbackPushforwardAdjunction (f ∣_ U)).unit.app
      (M.restrict U.ι)) := by
  let g := (Scheme.Modules.restrictFunctor U.ι).map
    ((Scheme.Modules.pullbackPushforwardAdjunction f).unit.app M)
  let e := OpenBaseChange.iso f U ((Scheme.Modules.pullback f).obj M)
  let k := (Scheme.Modules.pushforward (f ∣_ U)).map
    ((OpenBaseChange.leftSquare f U).hom.app M)
  calc
    IsIso g ↔ IsIso (g ≫ e.hom) := (isIso_comp_right_iff g e.hom).symm
    _ ↔ IsIso (((Scheme.Modules.pullbackPushforwardAdjunction (f ∣_ U)).unit.app
        (M.restrict U.ι)) ≫ k) := by rw [OpenBaseChange.unit_compatibility]
    _ ↔ _ := isIso_comp_right_iff _ k

theorem unit_isIso_of_affine (M : X.Modules)
    (h : ∀ U : X.affineOpens,
      IsIso ((Scheme.Modules.pullbackPushforwardAdjunction (f ∣_ U.1)).unit.app
        (M.restrict U.1.ι))) :
    IsIso ((Scheme.Modules.pullbackPushforwardAdjunction f).unit.app M) := by
  apply IdealModule.isIso_of_affine_app
  intro U
  have hr := (restrict_unit_isIso_iff f U.1 M).mpr (h U)
  have ht := Scheme.Modules.Hom.isIso_iff_isIso_app.mp hr ⊤
  change IsIso (((Scheme.Modules.pullbackPushforwardAdjunction f).unit.app M).app
    (U.1.ι ''ᵁ ⊤)) at ht
  have he : U.1.ι ''ᵁ ⊤ = U.1 :=
    (Scheme.Hom.image_top_eq_opensRange U.1.ι).trans (Scheme.Opens.opensRange_ι U.1)
  rw [he] at ht
  exact ht

end
end PiExponentSeshadri.ClosedPullbackUnitRestriction

end OAI
end Source0655

-- Source: OAI/NumberTheory/PiExponent/Approximation/ModulePullbackCoherent.lean
section Source0656
/-
Modification notice for the LogTwo project.
Derived from openai/math (Apache-2.0), revision adc7f1241b42e322a6451854ab7e4b4c146bf78a.
Original source: lean/OAI/NumberTheory/PiExponent/Approximation/ModulePullbackCoherent.lean
Changes: Convert module/import declarations to the Lean 4.34 public module format.
Expose private helpers and adjust helper names where needed for module compatibility.
See ../THIRD_PARTY_NOTICES.txt for provenance and the recorded changes.
-/

namespace OAI

namespace PiExponentSeshadri.Geometry
noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace
open PiExponent.FiniteGlobalPresentation

def presentationOfIso (X : Scheme.{0})
    {M N : SheafOfModules X.ringCatSheaf} (e : M ≅ N)
    (P : M.Presentation) : N.Presentation := by
  let : IsIso e.hom := e.isIso_hom
  exact P.ofIsIso e.hom

theorem pullback_isFinitePresentation {X Y : Scheme.{0}} (f : Y ⟶ X)
    (M : X.Modules) [M.IsFinitePresentation] :
    ((Scheme.Modules.pullback f).obj M).IsFinitePresentation := by
  apply isFinitePresentation_of_localPresentations
  intro y
  obtain ⟨U, hy, P, hP⟩ := exists_local_finitePresentation M (f y)
  let F : SheafOfModules U.toScheme.ringCatSheaf ⥤
      SheafOfModules (f ⁻¹ᵁ U).toScheme.ringCatSheaf :=
    Scheme.Modules.pullback (f ∣_ U)
  let : PreservesColimitsOfSize.{0,0} F :=
    (Scheme.Modules.pullbackPushforwardAdjunction (f ∣_ U)).leftAdjoint_preservesColimits
  let Q := P.map F (pullbackUnitIso (f ∣_ U)).symm
  let e := (pullbackRestrictNatIso f U).app M
  exact ⟨f ⁻¹ᵁ U, hy, presentationOfIso (f ⁻¹ᵁ U).toScheme e.symm Q,
    ⟨⟨hP.isFiniteType_generators.finite⟩, ⟨hP.isFiniteType_relations.finite⟩⟩⟩

end
end PiExponentSeshadri.Geometry

end OAI
end Source0656

-- Source: OAI/NumberTheory/PiExponent/Approximation/GlobalClosedAnnihilatedDescent.lean
section Source0657
-- Modified in this edition: unused plain lemmas removed; see reduction.json.
/-
Modification notice for the LogTwo project.
Derived from openai/math (Apache-2.0), revision adc7f1241b42e322a6451854ab7e4b4c146bf78a.
Original source: lean/OAI/NumberTheory/PiExponent/Approximation/GlobalClosedAnnihilatedDescent.lean
Changes: Convert module/import declarations to the Lean 4.34 public module format.
See ../THIRD_PARTY_NOTICES.txt for provenance and the recorded changes.
-/

namespace OAI

namespace PiExponentSeshadri.ClosedAnnihilatedDescent
noncomputable section
open CategoryTheory AlgebraicGeometry TopologicalSpace Opposite
variable {X Y : Scheme.{0}} (f : Y ⟶ X)

def LocallyAnnihilated (M : X.Modules) : Prop :=
  ∀ U : X.affineOpens,
    RingHom.ker (f ∣_ U.1).appTop.hom ≤
      Module.annihilator Γ(U.1.toScheme,⊤) Γ(M.restrict U.1.ι,⊤)

theorem unit_isIso_of_locallyAnnihilated [IsClosedImmersion f]
    (M : X.Modules) [M.IsQuasicoherent] (h : LocallyAnnihilated f M) :
    IsIso ((Scheme.Modules.pullbackPushforwardAdjunction f).unit.app M) := by
  apply ClosedPullbackUnitRestriction.unit_isIso_of_affine f M
  intro U
  let : IsAffine U.1.toScheme := U.2
  obtain ⟨N, ⟨e⟩⟩ := exists_affine_closed_descent (f ∣_ U.1) (M.restrict U.1.ι) (h U)
  exact ClosedImmersionModules.unit_isIso_of_pushforward (f ∣_ U.1) e.symm

def closedDescentPushforwardIso [IsClosedImmersion f]
    (M : X.Modules) [M.IsQuasicoherent] (h : LocallyAnnihilated f M) :
    (Scheme.Modules.pushforward f).obj ((Scheme.Modules.pullback f).obj M) ≅ M := by
  let := unit_isIso_of_locallyAnnihilated f M h
  exact (asIso ((Scheme.Modules.pullbackPushforwardAdjunction f).unit.app M)).symm

theorem exists_closed_coherent_descent [IsClosedImmersion f]
    (M : X.Modules) [M.IsFinitePresentation] (h : LocallyAnnihilated f M) :
    ∃ N : Y.Modules, N.IsFinitePresentation ∧
      Nonempty ((Scheme.Modules.pushforward f).obj N ≅ M) := by
  let : M.IsQuasicoherent :=
    (SheafOfModules.IsFinitePresentation.exists_quasicoherentData M).choose.isQuasicoherent
  exact ⟨(Scheme.Modules.pullback f).obj M, Geometry.pullback_isFinitePresentation f M,
    ⟨closedDescentPushforwardIso f M h⟩⟩

end
end PiExponentSeshadri.ClosedAnnihilatedDescent

end OAI
end Source0657

-- Source: OAI/NumberTheory/PiExponent/Geometry/IdealSheafPowers.lean
section Source0658
/-
Modification notice for the LogTwo project.
Derived from openai/math (Apache-2.0), revision adc7f1241b42e322a6451854ab7e4b4c146bf78a.
Original source: lean/OAI/NumberTheory/PiExponent/Geometry/IdealSheafPowers.lean
Changes: Convert module/import declarations to the Lean 4.34 public module format.
See ../THIRD_PARTY_NOTICES.txt for provenance and the recorded changes.
-/

namespace OAI

namespace PiExponentSeshadri.IdealPullback
noncomputable section
open CategoryTheory AlgebraicGeometry TopologicalSpace
variable {X Y : Scheme}

lemma comap_pow (I : X.IdealSheafData) (f : Y ⟶ X) (m : ℕ) :
    (I^m).comap f = (I.comap f)^m := by
  have hc : ∀ y : Y, ∃ (U : Y.affineOpens) (V : X.affineOpens),
      y ∈ U.1 ∧ U.1 ≤ f ⁻¹ᵁ V.1 := by
    intro y
    obtain ⟨V, hV, hyV, _⟩ := exists_isAffineOpen_mem_and_subset
      (show f y ∈ (⊤ : X.Opens) from trivial)
    obtain ⟨U, hU, hyU, hUV⟩ := exists_isAffineOpen_mem_and_subset
      (show y ∈ f ⁻¹ᵁ V from hyV)
    exact ⟨⟨U, hU⟩, ⟨V, hV⟩, hyU, hUV⟩
  choose U V hy hUV using hc
  apply Scheme.IdealSheafData.ext_of_iSup_eq_top U
  · apply top_unique
    intro y _
    exact Opens.mem_iSup.mpr ⟨y, hy y⟩
  · intro y
    rw [comap_ideal (I^m) f (U y) (V y) (hUV y)]
    change (I.ideal (V y)^m).map _ = ((I.comap f).ideal (U y))^m
    rw [Ideal.map_pow, comap_ideal I f (U y) (V y) (hUV y)]

lemma specIdeal_pow {R : Type} [CommRing R] (I : Ideal R) (m : ℕ) :
    specIdeal (I^m) = (specIdeal I)^m := by
  apply Scheme.IdealSheafData.ext_of_isAffine
  simpa only [specIdeal_top, Scheme.IdealSheafData.ideal_pow, Pi.pow_apply] using
    Ideal.map_pow (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom I m

end
end PiExponentSeshadri.IdealPullback

end OAI
end Source0658

-- Source: OAI/NumberTheory/PiExponent/LocalAlgebra/IdealModuleRestriction.lean
section Source0659
/-
Modification notice for the LogTwo project.
Derived from openai/math (Apache-2.0), revision adc7f1241b42e322a6451854ab7e4b4c146bf78a.
Original source: lean/OAI/NumberTheory/PiExponent/LocalAlgebra/IdealModuleRestriction.lean
Changes: Convert module/import declarations to the Lean 4.34 public module format.
See ../THIRD_PARTY_NOTICES.txt for provenance and the recorded changes.
-/

namespace OAI

namespace PiExponentSeshadri.IdealModule
noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite
variable {X Y : Scheme.{0}}

lemma restrictedInclusion_structureMap_eq_zero (I : Y.IdealSheafData)
    (f : X ⟶ Y) [IsOpenImmersion f] :
    restrictedInclusion I f ≫ structureMap (I.comap f).subschemeι = 0 := by
  apply hom_ext_affine
  intro U
  ext x
  change (I.comap f).subschemeι.app U.1 ((restrictedInclusion I f).app U.1 x) = 0
  apply RingHom.mem_ker.mp
  rw [(I.comap f).ker_subschemeι_app U, ← restricted_image I f U]
  exact ⟨x,rfl⟩

def restrictedToClosed (I : Y.IdealSheafData) (f : X ⟶ Y) [IsOpenImmersion f] :
    (closedModule I).restrict f ⟶ closedModule (I.comap f) :=
  kernel.lift (structureMap (I.comap f).subschemeι) (restrictedInclusion I f)
    (restrictedInclusion_structureMap_eq_zero I f)

@[reassoc (attr := simp)] lemma restrictedToClosed_inclusion (I : Y.IdealSheafData)
    (f : X ⟶ Y) [IsOpenImmersion f] :
    restrictedToClosed I f ≫ closedInclusion (I.comap f) = restrictedInclusion I f :=
  kernel.lift_ι _ _ _

instance restrictedToClosed_isIso (I : Y.IdealSheafData) (f : X ⟶ Y) [IsOpenImmersion f] :
    IsIso (restrictedToClosed I f) := by
  apply isIso_of_affine_app
  intro U
  let : Mono (closedInclusion (I.comap f)).val := inferInstanceAs
    (Mono ((Scheme.Modules.toPresheafOfModules X).map (closedInclusion (I.comap f))))
  let : Mono (restrictedInclusion I f).val := inferInstanceAs
    (Mono ((Scheme.Modules.toPresheafOfModules X).map (restrictedInclusion I f)))
  have ht : Function.Injective ((closedInclusion (I.comap f)).app U.1) := by
    exact PresheafOfModules.injective_of_mono (closedInclusion (I.comap f)).val (op U.1)
  have hs : Function.Injective ((restrictedInclusion I f).app U.1) := by
    exact PresheafOfModules.injective_of_mono (restrictedInclusion I f).val (op U.1)
  have he (x : Γ((closedModule I).restrict f,U.1)) :
      (closedInclusion (I.comap f)).app U.1 ((restrictedToClosed I f).app U.1 x) =
        (restrictedInclusion I f).app U.1 x :=
    congrArg (fun g => g.app U.1 x) (restrictedToClosed_inclusion I f)
  apply (ConcreteCategory.isIso_iff_bijective _).mpr
  constructor
  · intro x y h
    apply hs
    rw [← he x, ← he y, h]
  · intro x
    have hx : (closedInclusion (I.comap f)).app U.1 x ∈ (I.comap f).ideal U := by
      rw [← closed_image (I.comap f) U]
      exact ⟨x,rfl⟩
    rw [← restricted_image I f U] at hx
    obtain ⟨y,hy⟩ := hx
    exact ⟨y, ht ((he y).trans hy)⟩

def closedModuleRestrictIso (I : Y.IdealSheafData) (f : X ⟶ Y) [IsOpenImmersion f] :
    (closedModule I).restrict f ≅ closedModule (I.comap f) := asIso (restrictedToClosed I f)

lemma closedModuleRestrictIso_naturality {I J : Y.IdealSheafData} (h : I ≤ J)
    (f : X ⟶ Y) [IsOpenImmersion f] :
    (Scheme.Modules.restrictFunctor f).map (closedMap h) ≫ (closedModuleRestrictIso J f).hom =
      (closedModuleRestrictIso I f).hom ≫ closedMap (Scheme.IdealSheafData.comap_mono f h) := by
  apply (cancel_mono (closedInclusion (J.comap f))).mp
  simp only [Category.assoc, closedMap_inclusion]
  change (Scheme.Modules.restrictFunctor f).map (closedMap h) ≫
    restrictedToClosed J f ≫ closedInclusion (J.comap f) =
    restrictedToClosed I f ≫ closedInclusion (I.comap f)
  rw [restrictedToClosed_inclusion, restrictedToClosed_inclusion]
  unfold restrictedInclusion
  let F : Y.Modules ⥤ X.Modules := Scheme.Modules.restrictFunctor f
  exact (Category.assoc _ _ _).symm.trans
    ((congrArg (fun g : F.obj (closedModule I) ⟶ F.obj (unit Y) =>
      g ≫ (Scheme.Modules.restrictUnitIso f).hom)
      (F.map_comp (closedMap h) (closedInclusion J)).symm).trans
      (congrArg (fun g : closedModule I ⟶ unit Y =>
        F.map g ≫ (Scheme.Modules.restrictUnitIso f).hom) (closedMap_inclusion h)))

end
end PiExponentSeshadri.IdealModule

end OAI
end Source0659

-- Source: OAI/NumberTheory/PiExponent/LocalAlgebra/IdealPowerRestriction.lean
section Source0660
/-
Modification notice for the LogTwo project.
Derived from openai/math (Apache-2.0), revision adc7f1241b42e322a6451854ab7e4b4c146bf78a.
Original source: lean/OAI/NumberTheory/PiExponent/LocalAlgebra/IdealPowerRestriction.lean
Changes: Convert module/import declarations to the Lean 4.34 public module format.
See ../THIRD_PARTY_NOTICES.txt for provenance and the recorded changes.
-/

namespace OAI

namespace PiExponentSeshadri.IdealModule
noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite
open PiExponentSeshadri.Geometry
variable {X Y : Scheme.{0}}

def closedQuotientRestrictIso {I J : Y.IdealSheafData} (h : I ≤ J)
    (f : X ⟶ Y) [IsOpenImmersion f] :
    (cokernel (closedMap h)).restrict f ≅
      cokernel (closedMap (Scheme.IdealSheafData.comap_mono f h)) :=
  PreservesCokernel.iso (Scheme.Modules.restrictFunctor f) (closedMap h) ≪≫
    cokernel.mapIso _ _ (closedModuleRestrictIso I f) (closedModuleRestrictIso J f)
      (closedModuleRestrictIso_naturality h f)

def closedQuotientCongr {I J I' J' : X.IdealSheafData} (h : I ≤ J) (h' : I' ≤ J')
    (hI : I = I') (hJ : J = J') : cokernel (closedMap h) ≅ cokernel (closedMap h') := by
  subst I'
  subst J'
  exact Iso.refl _

def powerLayerRestrictIso (I : Y.IdealSheafData) (n : ℕ)
    (f : X ⟶ Y) [IsOpenImmersion f] :
    (powerLayer I n).restrict f ≅ powerLayer (I.comap f) n :=
  closedQuotientRestrictIso (fun _U => Ideal.pow_le_pow_right (Nat.le_succ n)) f ≪≫
    closedQuotientCongr _ _ (IdealPullback.comap_pow I f (n+1)) (IdealPullback.comap_pow I f n)

theorem powerLayer_restrict_smul_eq_zero (I : Y.IdealSheafData) (n : ℕ)
    (f : X ⟶ Y) [IsOpenImmersion f] (r : Γ(X,⊤))
    (hr : (I.comap f).subschemeι.appTop r = 0)
    (x : Γ((powerLayer I n).restrict f,⊤)) : r • x = 0 := by
  let e := powerLayerRestrictIso I n f
  have hz : r • e.hom.app ⊤ x = 0 := by
    have h := congrArg (fun a : powerLayer (I.comap f) n ⟶ powerLayer (I.comap f) n =>
      a.app ⊤ (e.hom.app ⊤ x)) (powerLayer_smul_id_eq_zero (I.comap f) n r hr)
    change (X.presheaf.map (𝟙 (op ⊤)) r) • e.hom.app ⊤ x = 0 at h
    have hid : X.presheaf.map (𝟙 (op ⊤)) r = r :=
      congrArg (fun g : Γ(X,⊤) ⟶ Γ(X,⊤) => g r) (X.presheaf.map_id (op ⊤))
    exact (congrArg (fun a : Γ(X,⊤) => a • e.hom.app ⊤ x) hid).symm.trans h
  apply (ConcreteCategory.bijective_of_isIso (e.hom.app ⊤)).injective
  exact (e.hom.app_smul r x).trans (hz.trans (map_zero _).symm)

theorem ker_subscheme_morphismRestrict (I : Y.IdealSheafData) (U : Y.Opens) :
    (I.subschemeι ∣_ U).ker = I.comap U.ι := by
  apply Scheme.IdealSheafData.ext
  funext V
  rw [Scheme.ker_ideal_of_isPullback_of_isOpenImmersion I.subschemeι
    (I.subschemeι ∣_ U) (I.subschemeι ⁻¹ᵁ U).ι U.ι
    (isPullback_morphismRestrict I.subschemeι U), I.ker_subschemeι,
    I.ideal_comap_of_isOpenImmersion]

theorem ker_appTop_subscheme_morphismRestrict (I : Y.IdealSheafData) (U : Y.affineOpens) :
    RingHom.ker (I.subschemeι ∣_ U.1).appTop.hom =
      RingHom.ker (I.comap U.1.ι).subschemeι.appTop.hom := by
  let : IsAffine U.1.toScheme := U.2
  exact (Scheme.Hom.ker_apply (I.subschemeι ∣_ U.1) ⟨⊤,isAffineOpen_top _⟩).symm.trans
    ((congrArg (fun J : U.1.toScheme.IdealSheafData => J.ideal ⟨⊤,isAffineOpen_top _⟩)
      (ker_subscheme_morphismRestrict I U.1)).trans
      ((I.comap U.1.ι).ker_subschemeι_app ⟨⊤,isAffineOpen_top _⟩).symm)

theorem powerLayer_restrict_kernel_smul_eq_zero (I : Y.IdealSheafData) (n : ℕ)
    (U : Y.affineOpens) (r : Γ(U.1.toScheme,⊤))
    (hr : (I.subschemeι ∣_ U.1).appTop r = 0)
    (x : Γ((powerLayer I n).restrict U.1.ι,⊤)) : r • x = 0 := by
  apply powerLayer_restrict_smul_eq_zero I n U.1.ι r _ x
  apply RingHom.mem_ker.mp
  rw [← ker_appTop_subscheme_morphismRestrict I U]
  exact hr

end
end PiExponentSeshadri.IdealModule

end OAI
end Source0660

-- Source: OAI/NumberTheory/PiExponent/LocalAlgebra/IdealPowerDescent.lean
section Source0661
/-
Modification notice for the LogTwo project.
Derived from openai/math (Apache-2.0), revision adc7f1241b42e322a6451854ab7e4b4c146bf78a.
Original source: lean/OAI/NumberTheory/PiExponent/LocalAlgebra/IdealPowerDescent.lean
Changes: Convert module/import declarations to the Lean 4.34 public module format.
See ../THIRD_PARTY_NOTICES.txt for provenance and the recorded changes.
-/

namespace OAI

namespace PiExponentSeshadri.IdealModule
noncomputable section
open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite
open PiExponentSeshadri.Geometry PiExponentSeshadri.ClosedAnnihilatedDescent
variable {X : Scheme.{0}}

theorem powerLayer_locallyAnnihilated (I : X.IdealSheafData) (n : ℕ) :
    LocallyAnnihilated I.subschemeι (powerLayer I n) := by
  intro U r hr
  apply Module.mem_annihilator.mpr
  intro x
  exact powerLayer_restrict_kernel_smul_eq_zero I n U r hr x

def descendedPowerLayer (I : X.IdealSheafData) (n : ℕ) : I.subscheme.Modules :=
  (Scheme.Modules.pullback I.subschemeι).obj (powerLayer I n)

instance descendedPowerLayer_isFinitePresentation [IsLocallyNoetherian X]
    (I : X.IdealSheafData) (n : ℕ) : (descendedPowerLayer I n).IsFinitePresentation := by
  have := powerLayer_isFinitePresentation I n
  exact pullback_isFinitePresentation I.subschemeι (powerLayer I n)

def powerLayerPushforwardIso [IsLocallyNoetherian X] (I : X.IdealSheafData) (n : ℕ) :
    (Scheme.Modules.pushforward I.subschemeι).obj (descendedPowerLayer I n) ≅ powerLayer I n := by
  have := powerLayer_isFinitePresentation I n
  let : (powerLayer I n).IsQuasicoherent :=
    (SheafOfModules.IsFinitePresentation.exists_quasicoherentData
      (powerLayer I n)).choose.isQuasicoherent
  exact closedDescentPushforwardIso I.subschemeι (powerLayer I n)
    (powerLayer_locallyAnnihilated I n)

end
end PiExponentSeshadri.IdealModule

end OAI
end Source0661

-- Source: OAI/NumberTheory/PiExponent/Cohomology/NilpotentIdealVanishing.lean
section Source0662
/-
Modification notice for the LogTwo project.
Derived from openai/math (Apache-2.0), revision adc7f1241b42e322a6451854ab7e4b4c146bf78a.
Original source: lean/OAI/NumberTheory/PiExponent/Cohomology/NilpotentIdealVanishing.lean
Changes: Convert module/import declarations to the Lean 4.34 public module format.
See ../THIRD_PARTY_NOTICES.txt for provenance and the recorded changes.
-/

namespace OAI

namespace PiExponentSeshadri.Geometry
noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian
open PiExponentSeshadri.IdealModule
variable {X : Scheme.{0}}
local instance : HasExt.{1} X.Modules := HasExt.standard _
attribute [local irreducible] closedModule powerLayer moduleTwistFunctor

theorem fullSupport_ideal_ext_zero_of_isAffine [IsNoetherian X]
    (I : X.IdealSheafData) (hI : I.support = ⊤) [IsAffine I.subscheme]
    (q : ℕ) (hq : 0 < q) (x : Abelian.Ext.{1} (structureSheaf X) (closedModule I) q) : x = 0 := by
  let : IsLocallyNoetherian I.subscheme := LocallyOfFiniteType.isLocallyNoetherian I.subschemeι
  let : IsNoetherian I.subscheme := {}
  obtain ⟨N,hNpos,hN⟩ := powerModule_eventually_isZero I hI
  have hLayer (k : ℕ) (_hk : k < N)
      (z : Abelian.Ext.{1} (structureSheaf X) (powerLayer I k) q) : z = 0 := by
    let : (descendedPowerLayer I k).IsQuasicoherent :=
      (SheafOfModules.IsFinitePresentation.exists_quasicoherentData
        (descendedPowerLayer I k)).choose.isQuasicoherent
    exact affine_closed_pushforward_ext_zero I.subschemeι (powerLayer I k)
      (descendedPowerLayer I k) (powerLayerPushforwardIso I k).symm q hq z
  have h := powerModule_ext_zero_of_layers I N q hN hLayer 1 hNpos
  have h' : ∀ z : Abelian.Ext.{1} (structureSheaf X) (closedModule I) q, z = 0 :=
    (congrArg (fun J : X.IdealSheafData =>
      ∀ z : Abelian.Ext.{1} (structureSheaf X) (closedModule J) q, z = 0) (pow_one I)).mp h
  exact h' x

theorem isAffine_of_fullSupport [IsNoetherian X] (I : X.IdealSheafData)
    (hI : I.support = ⊤) [IsAffine I.subscheme] : IsAffine X :=
  isAffine_of_fullSupport_of_ideal_ext_one_zero I hI
    (fullSupport_ideal_ext_zero_of_isAffine I hI 1 (by decide))

theorem fullSupport_eventual_ideal_twist_ext_zero [IsNoetherian X]
    {R : Type} [CommRing R] [IsNoetherianRing R]
    (p : X ⟶ Spec (CommRingCat.of R)) [IsProper p]
    (I : X.IdealSheafData) (hI : I.support = ⊤)
    (L : LineBundle X) (hL : (L.pullback I.subschemeι).IsAmple) :
    ∃ B, ∀ n, B ≤ n → ∀ q, 0 < q →
      ∀ x : Abelian.Ext.{1} (structureSheaf X)
        ((moduleTwistFunctor L n).obj (closedModule I)) q, x = 0 := by
  apply eventual_ideal_twist_vanishing_of_layers I hI L
  intro k
  exact eventual_twist_ext_zero_of_closed_pushforward p I.subschemeι L hL
    (powerLayer I k) (descendedPowerLayer I k) (powerLayerPushforwardIso I k).symm

end
end PiExponentSeshadri.Geometry

end OAI
end Source0662

-- Source: OAI/NumberTheory/PiExponent/Ampleness/NilpotentAmpleDescent.lean
section Source0663
/-
Modification notice for the LogTwo project.
Derived from openai/math (Apache-2.0), revision adc7f1241b42e322a6451854ab7e4b4c146bf78a.
Original source: lean/OAI/NumberTheory/PiExponent/Ampleness/NilpotentAmpleDescent.lean
Changes: Convert module/import declarations to the Lean 4.34 public module format.
See ../THIRD_PARTY_NOTICES.txt for provenance and the recorded changes.
-/

namespace OAI

namespace PiExponentSeshadri.Geometry
noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace
open PiExponentSeshadri.Frames
variable {X : Scheme.{0}}

theorem isAffineOpen_of_fullSupport_preimage [IsNoetherian X]
    (I : X.IdealSheafData) (hI : I.support = ⊤) (U : X.Opens)
    (hU : IsAffineOpen (I.subschemeι ⁻¹ᵁ U)) : IsAffineOpen U := by
  let : IsLocallyNoetherian U.toScheme := LocallyOfFiniteType.isLocallyNoetherian U.ι
  let : NoetherianSpace U.toScheme := U.ι.isOpenEmbedding.isInducing.noetherianSpace
  let : CompactSpace U.toScheme := NoetherianSpace.compactSpace U.toScheme
  let : IsNoetherian U.toScheme := {}
  let J := I.comap U.ι
  have hJ : J.support = ⊤ := by
    dsimp only [J]
    rw [Scheme.IdealSheafData.support_comap, hI]
    rfl
  let e : J.subscheme ≅ (I.subschemeι ⁻¹ᵁ U).toScheme :=
    I.comapIso U.ι ≪≫ pullbackSymmetry _ _ ≪≫ pullbackRestrictIsoRestrict I.subschemeι U
  let : IsAffine (I.subschemeι ⁻¹ᵁ U).toScheme := hU
  let : IsAffine J.subscheme := IsAffine.of_isIso e.hom
  exact isAffine_of_fullSupport J hJ

theorem fullSupport_eventual_powerSection_surjective [IsNoetherian X]
    {R : Type} [CommRing R] [IsNoetherianRing R]
    (p : X ⟶ Spec (CommRingCat.of R)) [IsProper p]
    (I : X.IdealSheafData) (hI : I.support = ⊤)
    (L : LineBundle X) (hL : (L.pullback I.subschemeι).IsAmple) :
    ∃ B, ∀ n, B ≤ n → Function.Surjective (pullbackPowerSection L I.subschemeι n) := by
  obtain ⟨B,hB⟩ := fullSupport_eventual_ideal_twist_ext_zero p I hI L hL
  exact ⟨B, fun n hn => pullbackPowerSection_surjective_of_ideal_ext_zero I.subschemeι L n
    (hB n hn 1 (by decide))⟩

theorem LineBundle.isAmple_of_fullSupport [IsNoetherian X]
    {R : Type} [CommRing R] [IsNoetherianRing R]
    (p : X ⟶ Spec (CommRingCat.of R)) [IsProper p]
    (I : X.IdealSheafData) (hI : I.support = ⊤)
    (L : LineBundle X) (hL : (L.pullback I.subschemeι).IsAmple) : L.IsAmple := by
  obtain ⟨B,hB⟩ := fullSupport_eventual_powerSection_surjective p I hI L hL
  intro x V hx
  obtain ⟨y,hy⟩ := subscheme_surjective_of_fullSupport I hI x
  have hyV : y ∈ I.subschemeι ⁻¹ᵁ V := by change I.subschemeι y ∈ V; rwa [hy]
  obtain ⟨d,hd,s,hys,hsV,hsa⟩ := hL y (I.subschemeι ⁻¹ᵁ V) hyV
  let m := B+1
  have hm : 0 < m := Nat.succ_pos B
  let σ : GlobalSections I.subscheme ((L.pullback I.subschemeι).pow (d*m)).sheaf :=
    powerSection s m ≫ (linePowerMul (L.pullback I.subschemeι) d m).hom
  have hσ : sectionOpen I.subscheme σ = sectionOpen I.subscheme s := by
    exact (PiExponent.AmpleIso.sectionOpen_postcomp_iso
      (powerSection s m) (linePowerMul (L.pullback I.subschemeι) d m)).trans
      (((L.pullback I.subschemeι).pow d).sectionOpen_power s hm)
  have hBd : B ≤ d*m := (Nat.le_succ B).trans (Nat.le_mul_of_pos_left m hd)
  obtain ⟨t,ht⟩ := hB (d*m) hBd σ
  have hpre : I.subschemeι ⁻¹ᵁ sectionOpen X t = sectionOpen I.subscheme s := by
    exact (sectionOpen_pullbackPowerSection L I.subschemeι (d*m) t).symm.trans
      ((congrArg (fun u : GlobalSections I.subscheme
        ((L.pullback I.subschemeι).pow (d*m)).sheaf => sectionOpen I.subscheme u) ht).trans hσ)
  refine ⟨d*m, Nat.mul_pos hd hm, t, ?_, ?_, ?_⟩
  · have hyT : y ∈ I.subschemeι ⁻¹ᵁ sectionOpen X t := by rw [hpre]; exact hys
    change I.subschemeι y ∈ sectionOpen X t at hyT
    rwa [hy] at hyT
  · intro z hz
    obtain ⟨w,hw⟩ := subscheme_surjective_of_fullSupport I hI z
    have hwT : w ∈ I.subschemeι ⁻¹ᵁ sectionOpen X t := by change I.subschemeι w ∈ sectionOpen X t; rwa [hw]
    rw [hpre] at hwT
    have hwV := hsV hwT
    change I.subschemeι w ∈ V at hwV
    rwa [hw] at hwV
  · apply isAffineOpen_of_fullSupport_preimage I hI
    rw [hpre]
    exact hsa

end
end PiExponentSeshadri.Geometry

end OAI
end Source0663

-- Source: OAI/NumberTheory/PiExponent/Ampleness/ClosedAmpleBaseChange.lean
section Source0664
/-
Modification notice for the LogTwo project.
Derived from openai/math (Apache-2.0), revision adc7f1241b42e322a6451854ab7e4b4c146bf78a.
Original source: lean/OAI/NumberTheory/PiExponent/Ampleness/ClosedAmpleBaseChange.lean
Changes: Convert module/import declarations to the Lean 4.34 public module format.
See ../THIRD_PARTY_NOTICES.txt for provenance and the recorded changes.
-/

namespace OAI

noncomputable section
namespace PiExponent.ReducedComponentAmple
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open PiExponentSeshadri.Geometry

variable {X Y : Scheme.{0}}

def closedBaseChange (I : X.IdealSheafData) (f : Y ⟶ X) :
    (I.comap f).subscheme ⟶ I.subscheme :=
  (I.comapIso f).hom ≫ pullback.snd f I.subschemeι

instance closedBaseChange_isClosedImmersion (I : X.IdealSheafData)
    (f : Y ⟶ X) [IsClosedImmersion f] : IsClosedImmersion (closedBaseChange I f) := by
  unfold closedBaseChange
  infer_instance

@[reassoc]
theorem closedBaseChange_condition (I : X.IdealSheafData) (f : Y ⟶ X) :
    closedBaseChange I f ≫ I.subschemeι = (I.comap f).subschemeι ≫ f := by
  simp only [closedBaseChange, Category.assoc, ← pullback.condition,
    Scheme.IdealSheafData.comapIso_hom_fst_assoc]

def closedBaseChangeLineIso (I : X.IdealSheafData) (f : Y ⟶ X) (L : LineBundle X) :
    ((L.pullback I.subschemeι).pullback (closedBaseChange I f)).sheaf ≅
      ((L.pullback f).pullback (I.comap f).subschemeι).sheaf :=
  (Scheme.Modules.pullbackComp (closedBaseChange I f) I.subschemeι).app L.sheaf ≪≫
    (Scheme.Modules.pullbackCongr (closedBaseChange_condition I f)).app L.sheaf ≪≫
    ((Scheme.Modules.pullbackComp (I.comap f).subschemeι f).app L.sheaf).symm

theorem isAmple_comap_restriction (I : X.IdealSheafData) (f : Y ⟶ X)
    [IsClosedImmersion f] (L : LineBundle X) (hL : (L.pullback I.subschemeι).IsAmple) :
    ((L.pullback f).pullback (I.comap f).subschemeι).IsAmple :=
  PiExponent.AmpleIso.isAmple_of_sheaf_iso _ _ (closedBaseChangeLineIso I f L)
    (LineBundle.IsAmple.pullback_closedImmersion _ hL (closedBaseChange I f))

end PiExponent.ReducedComponentAmple

end

end OAI
end Source0664

-- Source: OAI/NumberTheory/PiExponent/Ampleness/AmpleGeneratedTensor.lean
section Source0665
-- Modified in this edition: unused plain lemmas removed; see reduction.json.
/-
Modification notice for the LogTwo project.
Derived from openai/math (Apache-2.0), revision adc7f1241b42e322a6451854ab7e4b4c146bf78a.
Original source: lean/OAI/NumberTheory/PiExponent/Ampleness/AmpleGeneratedTensor.lean
Changes: Convert module/import declarations to the Lean 4.34 public module format.
See ../THIRD_PARTY_NOTICES.txt for provenance and the recorded changes.
-/

namespace OAI

noncomputable section
namespace PiExponentSeshadri.Geometry

open AlgebraicGeometry CategoryTheory TopologicalSpace
open PiExponentSeshadri.Frames PiExponentSeshadri.TensorPure

variable {X : Scheme.{0}}

theorem LineBundle.IsAmple.tensor_of_section_cover {H M : LineBundle X}
    (hH : H.IsAmple) {ι : Type} (s : ι → GlobalSections X M.sheaf)
    (hc : (⨆ i, sectionOpen X (s i)) = ⊤) : (H.tensor M).IsAmple := by
  intro x V hx
  obtain ⟨i, hi⟩ := Opens.mem_iSup.mp
    (show x ∈ ⨆ i, sectionOpen X (s i) by rw [hc]; trivial)
  obtain ⟨n, hn, a, hxa, haV, haa⟩ :=
    hH x (V ⊓ sectionOpen X (s i)) ⟨hx, hi⟩
  let b : GlobalSections X (M.pow n).sheaf := powerSection (s i) n
  have hb : sectionOpen X b = sectionOpen X (s i) := M.sectionOpen_power (s i) hn
  let q : GlobalSections X ((H.tensor M).pow n).sheaf :=
    tensorSection a b ≫ (lineTensorPow H M n).inv
  have hq : sectionOpen X q = sectionOpen X a := by
    change SectionOpens.isoOpen
      (tensorSection a b ≫ (lineTensorPow H M n).symm.hom) = _
    erw [SectionOpens.isoOpen_postcomp]
    calc
      SectionOpens.isoOpen (tensorSection a b) =
          sectionOpen X a ⊓ sectionOpen X b := section_open (H.pow n) (M.pow n) a b
      _ = sectionOpen X a := by
        rw [hb, inf_eq_left.mpr (haV.trans inf_le_right)]
  exact ⟨n, hn, q, hq.symm ▸ hxa, hq.le.trans (haV.trans inf_le_left), hq.symm ▸ haa⟩

def ampleInverseTwistCancel (H L : LineBundle X) (n : ℕ) :
    (H.tensor (H.inverse.tensor (L.pow n))).sheaf ≅ (L.pow n).sheaf :=
  (lineTensorAssoc H H.inverse (L.pow n)).symm ≪≫
    moduleTensorIso (lineTensorInverseIso H) (Iso.refl (L.pow n).sheaf) ≪≫
    moduleTensorUnit (L.pow n).sheaf

theorem LineBundle.isAmple_of_inverse_twist_section_cover (L H : LineBundle X)
    (hH : H.IsAmple) {n : ℕ} (hn : 0 < n) {ι : Type}
    (s : ι → GlobalSections X (H.inverse.tensor (L.pow n)).sheaf)
    (hc : (⨆ i, sectionOpen X (s i)) = ⊤) : L.IsAmple :=
  LineBundle.IsAmple.of_pow L hn
    (PiExponent.AmpleIso.isAmple_of_sheaf_iso
      (H.tensor (H.inverse.tensor (L.pow n))) (L.pow n)
      (ampleInverseTwistCancel H L n) (hH.tensor_of_section_cover s hc))

end PiExponentSeshadri.Geometry

end

end OAI
end Source0665

-- Source: OAI/NumberTheory/PiExponent/Ampleness/ComponentAmpleDescentCover.lean
section Source0666
/-
Modification notice for the LogTwo project.
Derived from openai/math (Apache-2.0), revision adc7f1241b42e322a6451854ab7e4b4c146bf78a.
Original source: lean/OAI/NumberTheory/PiExponent/Ampleness/ComponentAmpleDescentCover.lean
Changes: Convert module/import declarations to the Lean 4.34 public module format.
See ../THIRD_PARTY_NOTICES.txt for provenance and the recorded changes.
-/

namespace OAI

namespace PiExponentSeshadri.ComponentAmpleDescent
noncomputable section
open AlgebraicGeometry CategoryTheory TopologicalSpace
open _root_.OAI.PiExponentSeshadri.Geometry
variable {X Y Z : Scheme.{0}}

def pullbackTwistIso (f : Y ⟶ X) (K L : LineBundle X) (n : ℕ) :
    ((K.tensor (L.pow n)).pullback f).sheaf ≅
      (moduleTwistFunctor (L.pullback f) n).obj (K.pullback f).sheaf :=
  PullbackTensor.iso f K (L.pow n) ≪≫
    moduleTensorIso (Iso.refl _) (PullbackTensor.powIso f L n) ≪≫
    (moduleTwistPowerIso (L.pullback f) (K.pullback f).sheaf n).symm

theorem eventual_pullback_twist_sections [NoetherianSpace Y]
    (f : Y ⟶ X) (K L : LineBundle X) (hL : (L.pullback f).IsAmple) :
    ∃ N : ℕ, ∀ n ≥ N, ∀ y : Y,
      ∃ s : GlobalSections Y ((K.tensor (L.pow n)).pullback f).sheaf,
        y ∈ sectionOpen Y s := by
  have : (K.pullback f).sheaf.IsFinitePresentation :=
    PiExponent.GeometrySupport.LineBundleCoherent.lineBundle_isFinitePresentation _
  obtain ⟨N,hN⟩ := PiExponent.AmpleGlobalGeneration.ample_eventual_global_generators
    (L.pullback f) hL (K.pullback f).sheaf
  refine ⟨N, fun n hn y => ?_⟩
  obtain ⟨G,hG⟩ := hN n hn
  let : G.IsFiniteType := hG
  let D := SheafOfModules.GeneratingSections.equivOfIso (pullbackTwistIso f K L n).symm G
  have hc := @PiExponent.GeneratorsSectionCover.generators_sectionOpen_cover Y
    ((K.tensor (L.pow n)).pullback f) D ⟨hG.finite⟩
  obtain ⟨i,hi⟩ := Opens.mem_iSup.mp
    (show y ∈ ⨆ i, sectionOpen Y
      (PiExponent.GeneratorsSectionCover.generatorSection _ D i) by rw [hc]; trivial)
  exact ⟨_,hi⟩

theorem section_cover_of_jointly_surjective
    (f : Y ⟶ X) (g : Z ⟶ X) (M : LineBundle X)
    (hcover : Set.range f ∪ Set.range g = Set.univ)
    (hf : Function.Surjective (fun s : GlobalSections X M.sheaf => pullbackSection f s))
    (hg : Function.Surjective (fun s : GlobalSections X M.sheaf => pullbackSection g s))
    (hY : ∀ y : Y, ∃ s : GlobalSections Y (M.pullback f).sheaf, y ∈ sectionOpen Y s)
    (hZ : ∀ z : Z, ∃ s : GlobalSections Z (M.pullback g).sheaf, z ∈ sectionOpen Z s) :
    (⨆ s : GlobalSections X M.sheaf, sectionOpen X s) = ⊤ := by
  apply top_unique
  intro x _
  have hx : x ∈ Set.range f ∪ Set.range g := by rw [hcover]; trivial
  rcases hx with ⟨y,rfl⟩ | ⟨z,rfl⟩
  · obtain ⟨s,hs⟩ := hY y
    obtain ⟨t,rfl⟩ := hf s
    apply Opens.mem_iSup.mpr
    refine ⟨t,?_⟩
    change y ∈ f ⁻¹ᵁ SectionOpens.isoOpen t
    exact (pullback_isoOpen_eq M t f).le hs
  · obtain ⟨s,hs⟩ := hZ z
    obtain ⟨t,rfl⟩ := hg s
    apply Opens.mem_iSup.mpr
    refine ⟨t,?_⟩
    change z ∈ g ⁻¹ᵁ SectionOpens.isoOpen t
    exact (pullback_isoOpen_eq M t g).le hs

theorem isAmple_of_eventual_restriction_surjective
    [NoetherianSpace Y] [NoetherianSpace Z]
    (f : Y ⟶ X) (g : Z ⟶ X) (L H : LineBundle X) (hH : H.IsAmple)
    (hcover : Set.range f ∪ Set.range g = Set.univ)
    (hY : (L.pullback f).IsAmple) (hZ : (L.pullback g).IsAmple)
    (hf : ∃ N : ℕ, ∀ n ≥ N, Function.Surjective
      (fun s : GlobalSections X (H.inverse.tensor (L.pow n)).sheaf => pullbackSection f s))
    (hg : ∃ N : ℕ, ∀ n ≥ N, Function.Surjective
      (fun s : GlobalSections X (H.inverse.tensor (L.pow n)).sheaf => pullbackSection g s)) :
    L.IsAmple := by
  obtain ⟨A,hA⟩ := eventual_pullback_twist_sections f H.inverse L hY
  obtain ⟨B,hB⟩ := eventual_pullback_twist_sections g H.inverse L hZ
  obtain ⟨C,hC⟩ := hf
  obtain ⟨D,hD⟩ := hg
  let n := A+B+C+D+1
  have hn : 0 < n := by omega
  have hAn : A ≤ n := by omega
  have hBn : B ≤ n := by omega
  have hCn : C ≤ n := by omega
  have hDn : D ≤ n := by omega
  exact L.isAmple_of_inverse_twist_section_cover H hH hn (fun s => s)
    (section_cover_of_jointly_surjective f g (H.inverse.tensor (L.pow n)) hcover
      (hC n hCn) (hD n hDn) (hA n hAn) (hB n hBn))

end
end PiExponentSeshadri.ComponentAmpleDescent

end OAI
end Source0666

-- Source: OAI/NumberTheory/PiExponent/Ampleness/ComponentAmpleDescentIdeal.lean
section Source0667
/-
Modification notice for the LogTwo project.
Derived from openai/math (Apache-2.0), revision adc7f1241b42e322a6451854ab7e4b4c146bf78a.
Original source: lean/OAI/NumberTheory/PiExponent/Ampleness/ComponentAmpleDescentIdeal.lean
Changes: Convert module/import declarations to the Lean 4.34 public module format.
See ../THIRD_PARTY_NOTICES.txt for provenance and the recorded changes.
-/

namespace OAI

namespace PiExponentSeshadri.ComponentAmpleDescent
noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
open IdealModule
variable {X : Scheme.{0}}

theorem ideal_le_annihilator_closedModule {I J : X.IdealSheafData}
    (h : I * J = ⊥) (U : X.affineOpens) :
    J.ideal U ≤ Module.annihilator Γ(X,U.1) Γ(closedModule I,U.1) := by
  intro a ha
  apply Module.mem_annihilator.mpr
  intro m
  have hinj : Function.Injective ((closedInclusion I).val.app (op U.1)) := by
    let : Mono (closedInclusion I).val :=
      inferInstanceAs (Mono ((Scheme.Modules.toPresheafOfModules X).map (closedInclusion I)))
    exact PresheafOfModules.injective_of_mono (closedInclusion I).val (op U.1)
  apply hinj
  have hm : (closedInclusion I).app U.1 m ∈ I.ideal U := by
    rw [← closed_image I U]
    exact ⟨m,rfl⟩
  have hp := Ideal.mul_mem_mul_rev (R := Γ(X,U.1)) hm ha
  let b : Γ(X,U.1) := (closedInclusion I).app U.1 m
  have hz : a * b = 0 := by
    have hh : I.ideal U * J.ideal U = ⊥ := congrArg (fun K : X.IdealSheafData => K.ideal U) h
    simpa only [hh,Ideal.mem_bot] using hp
  exact (((closedInclusion I).app_smul (r := a) (x := m)).trans hz).trans
    ((closedInclusion I).app U.1).hom.map_zero.symm

theorem ideal_mul_eq_bot_of_reduced_cover [IsReduced X]
    {I J : X.IdealSheafData} (h : I.support ⊔ J.support = ⊤) : I * J = ⊥ := by
  apply Scheme.IdealSheafData.support_eq_top_iff.mp
  simpa only [Scheme.IdealSheafData.support_mul] using h

theorem ideal_le_annihilator_closedModule_of_reduced_cover [IsReduced X]
    {I J : X.IdealSheafData} (h : I.support ⊔ J.support = ⊤) (U : X.affineOpens) :
    J.ideal U ≤ Module.annihilator Γ(X,U.1) Γ(closedModule I,U.1) :=
  ideal_le_annihilator_closedModule (ideal_mul_eq_bot_of_reduced_cover h) U

end
end PiExponentSeshadri.ComponentAmpleDescent

end OAI
end Source0667

-- Source: OAI/NumberTheory/PiExponent/Ampleness/ComponentAmpleDescentLocal.lean
section Source0668
/-
Modification notice for the LogTwo project.
Derived from openai/math (Apache-2.0), revision adc7f1241b42e322a6451854ab7e4b4c146bf78a.
Original source: lean/OAI/NumberTheory/PiExponent/Ampleness/ComponentAmpleDescentLocal.lean
Changes: Convert module/import declarations to the Lean 4.34 public module format.
See ../THIRD_PARTY_NOTICES.txt for provenance and the recorded changes.
-/

namespace OAI

namespace PiExponentSeshadri.ComponentAmpleDescent
noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite
open PiExponentSeshadri.IdealModule
variable {X : Scheme.{0}}

theorem closedModule_restrict_annihilated [IsReduced X]
    {I J : X.IdealSheafData} (h : I.support ⊔ J.support = ⊤) (U : X.affineOpens) :
    RingHom.ker (J.subschemeι ∣_ U.1).appTop.hom ≤
      Module.annihilator Γ(U.1.toScheme,⊤) Γ((closedModule I).restrict U.1.ι,⊤) := by
  let : IsAffine U.1.toScheme := U.2
  have hcover : (I.comap U.1.ι).support ⊔ (J.comap U.1.ι).support = ⊤ := by
    rw [Scheme.IdealSheafData.support_comap, Scheme.IdealSheafData.support_comap]
    ext x
    change U.1.ι x ∈ (I.support : Set X) ∪ (J.support : Set X) ↔ True
    have hx : U.1.ι x ∈ (I.support ⊔ J.support : Closeds X) := by rw [h]; trivial
    exact iff_true_intro hx
  intro a ha
  apply Module.mem_annihilator.mpr
  intro m
  let e := closedModuleRestrictIso I U.1.ι
  have hj : a ∈ (J.comap U.1.ι).ideal ⟨⊤,isAffineOpen_top _⟩ := by
    erw [← (J.comap U.1.ι).ker_subschemeι_app ⟨⊤,isAffineOpen_top _⟩,
      ← ker_appTop_subscheme_morphismRestrict J U]
    exact ha
  have hz := Module.mem_annihilator.mp
    (ideal_le_annihilator_closedModule_of_reduced_cover hcover
      ⟨⊤,isAffineOpen_top _⟩ hj) (e.hom.app ⊤ m)
  apply (ConcreteCategory.bijective_of_isIso (e.hom.app ⊤)).injective
  exact (e.hom.app_smul a m).trans (hz.trans (map_zero _).symm)

end
end PiExponentSeshadri.ComponentAmpleDescent

end OAI
end Source0668

-- Source: OAI/NumberTheory/PiExponent/Ampleness/ComponentAmpleDescentSupported.lean
section Source0669
/-
Modification notice for the LogTwo project.
Derived from openai/math (Apache-2.0), revision adc7f1241b42e322a6451854ab7e4b4c146bf78a.
Original source: lean/OAI/NumberTheory/PiExponent/Ampleness/ComponentAmpleDescentSupported.lean
Changes: Convert module/import declarations to the Lean 4.34 public module format.
See ../THIRD_PARTY_NOTICES.txt for provenance and the recorded changes.
-/

namespace OAI

namespace PiExponentSeshadri.ComponentAmpleDescent
noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Abelian
open PiExponentSeshadri.Geometry
variable {X Y : Scheme.{0}} {R : Type} [CommRing R] [IsNoetherianRing R]

theorem eventual_tensor_cohomology_zero_of_closed_pushforward
    (p : X ⟶ Spec (CommRingCat.of R)) [IsProper p]
    (f : Y ⟶ X) [IsClosedImmersion f]
    (M : X.Modules) (N : Y.Modules) [N.IsFinitePresentation]
    (e : (Scheme.Modules.pushforward f).obj N ≅ M)
    (K L : LineBundle X) (hL : (L.pullback f).IsAmple) :
    ∃ B : ℕ, ∀ n ≥ B, ∀ q, 0 < q →
      ∀ x : cohomology (moduleTensor X M (K.tensor (L.pow n)).sheaf) q, x = 0 := by
  let D : Y.Modules := moduleTensor Y N (K.pullback f).sheaf
  have : D.IsFinitePresentation :=
    PiExponent.FiniteGlobalPresentation.moduleTwist_isFinitePresentation (K.pullback f) 1 N
  obtain ⟨B,hB⟩ :=
    PiExponent.GeometrySupport.NoetherianAmpleSerreVanishing.ample_serre_vanishing
      (f ≫ p) (L.pullback f) hL D
  let e₀ : (Scheme.Modules.pushforward f).obj D ≅ moduleTensor X M K.sheaf :=
    (PiExponent.ProjectionFormula.iso f N K).symm ≪≫
      moduleTensorIso e (Iso.refl K.sheaf)
  refine ⟨B,fun n hn q hq => ?_⟩
  have hz := (PiExponent.ClosedImmersionSerreTransfer.twist_ext_zero_iff f D L n q).mp
    (hB n hn q hq)
  let eₙ : (moduleTwistFunctor L n).obj ((Scheme.Modules.pushforward f).obj D) ≅
      moduleTensor X M (K.tensor (L.pow n)).sheaf :=
    (moduleTwistFunctor L n).mapIso e₀ ≪≫
      moduleTwistPowerIso L (moduleTensor X M K.sheaf) n ≪≫
      moduleLineTensorAssoc M K (L.pow n)
  exact PiExponent.GeometrySupport.SerrePowerDescent.ext_zero_of_iso eₙ q hz

end
end PiExponentSeshadri.ComponentAmpleDescent

end OAI
end Source0669

-- Source: OAI/NumberTheory/PiExponent/Ampleness/NakaiSectionLifting.lean
section Source0670
/-
Modification notice for the LogTwo project.
Derived from openai/math (Apache-2.0), revision adc7f1241b42e322a6451854ab7e4b4c146bf78a.
Original source: lean/OAI/NumberTheory/PiExponent/Ampleness/NakaiSectionLifting.lean
Changes: Convert module/import declarations to the Lean 4.34 public module format.
See ../THIRD_PARTY_NOTICES.txt for provenance and the recorded changes.
-/

namespace OAI

namespace PiExponent.NumericalAmpleness
noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open PiExponentSeshadri.Geometry
open PiExponent.SectionZeroIdeal
variable {X Y : Scheme.{0}}

theorem pullbackSection_surjective_of_unit_surjective (f : Y ⟶ X) (L : LineBundle X)
    (h : Function.Surjective (fun s : GlobalSections X L.sheaf =>
      s ≫ PiExponentSeshadri.LineClosedUnit.map f L)) :
    Function.Surjective (fun s : GlobalSections X L.sheaf => pullbackSection f s) := by
  intro σ
  let A := Scheme.Modules.pullbackPushforwardAdjunction f
  let e := A.homEquiv (structureSheaf X) ((Scheme.Modules.pullback f).obj L.sheaf)
  obtain ⟨s,hs⟩ := h (e ((pullbackUnitIso f).hom ≫ σ))
  have he : (Scheme.Modules.pullback f).map s = (pullbackUnitIso f).hom ≫ σ := by
    apply e.injective
    have hn := A.homEquiv_naturality_left s (𝟙 ((Scheme.Modules.pullback f).obj L.sheaf))
    simpa only [e, Category.comp_id, Adjunction.homEquiv_unit, Functor.map_id,
      Category.comp_id] using! hn.trans hs
  refine ⟨s,?_⟩
  change (pullbackUnitIso f).inv ≫ (Scheme.Modules.pullback f).map s = σ
  exact (congrArg (fun t : (Scheme.Modules.pullback f).obj (structureSheaf X) ⟶
      (Scheme.Modules.pullback f).obj L.sheaf => (pullbackUnitIso f).inv ≫ t) he).trans
    ((pullbackUnitIso f).inv_hom_id_assoc σ)

theorem eventual_cartier_restriction_section_lifting
    (p : X ⟶ Spec (CommRingCat.of ℂ)) (L : LineBundle X)
    (s : GlobalSections X L.sheaf) [Mono s]
    (hfinite : ∀ n, letI := Module.compHom (cohomology (L.pow n).sheaf 1) (baseScalars p)
      FiniteDimensional ℂ (cohomology (L.pow n).sheaf 1))
    (hzero : ∃ N, ∀ n, N ≤ n → ∀ z :
      cohomology ((Scheme.Modules.pullback (zeroIdeal L s).subschemeι).obj (L.pow (n+1)).sheaf) 1,
      z = 0) :
    ∃ N, ∀ n, N ≤ n → Function.Surjective
      (fun t : GlobalSections X (L.pow (n+1)).sheaf =>
        pullbackSection (zeroIdeal L s).subschemeι t) := by
  let i := (zeroIdeal L s).subschemeι
  let F : ℕ → X.Modules := fun n => (L.pow n).sheaf
  let Q : ℕ → X.Modules := fun n => (Scheme.Modules.pushforward i).obj
    ((Scheme.Modules.pullback i).obj (L.pow (n+1)).sheaf)
  let f : ∀ n, F n ⟶ F (n+1) := fun n => cartierPowerMultiply L s n
  let g : ∀ n, F (n+1) ⟶ Q n := fun n => PiExponentSeshadri.LineClosedUnit.map i (L.pow (n+1))
  have hex := fun n => regular_cartierPower_restriction_shortExact p L s n
  let hz : ∀ n, f n ≫ g n = 0 := fun n => (hex n).choose
  have hshort : ∀ n, (ShortComplex.mk (f n) (g n) (hz n)).ShortExact :=
    fun n => (hex n).choose_spec
  have hzero' : ∃ N, ∀ n, N ≤ n → ∀ z : cohomology (Q n) 1, z = 0 := by
    obtain ⟨N,hN⟩ := hzero
    refine ⟨N,fun n hn z => ?_⟩
    let e := ClosedImmersionSerreTransfer.cohomologyLinearEquiv i p
      ((Scheme.Modules.pullback i).obj (L.pow (n+1)).sheaf) 1
    obtain ⟨w,rfl⟩ := e.surjective z
    rw [hN n hn w,map_zero]
  obtain ⟨N,hN⟩ := eventual_globalSections_surjective p F Q f g hz hshort hfinite hzero'
  refine ⟨N,fun n hn => ?_⟩
  exact pullbackSection_surjective_of_unit_surjective i (L.pow (n+1)) (hN n hn)

end
end PiExponent.NumericalAmpleness

end OAI
end Source0670

-- Source: OAI/NumberTheory/PiExponent/Approximation/ClosedSectionLifting.lean
section Source0671
/-
Modification notice for the LogTwo project.
Derived from openai/math (Apache-2.0), revision adc7f1241b42e322a6451854ab7e4b4c146bf78a.
Original source: lean/OAI/NumberTheory/PiExponent/Approximation/ClosedSectionLifting.lean
Changes: Convert module/import declarations to the Lean 4.34 public module format.
See ../THIRD_PARTY_NOTICES.txt for provenance and the recorded changes.
-/

namespace OAI

noncomputable section
namespace PiExponentSeshadri.Geometry

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian

variable {X Y : Scheme.{0}}
local instance (Z : Scheme.{0}) : HasExt.{1} Z.Modules := HasExt.standard _

theorem closed_line_unit_epi (f : Y ⟶ X) [IsClosedImmersion f] (M : LineBundle X) :
    Epi ((Scheme.Modules.pullbackPushforwardAdjunction f).unit.app M.sheaf) :=
  PiExponentSeshadri.LineClosedUnit.epi f M

theorem pullbackSection_surjective_of_kernel_cohomology_zero
    (f : Y ⟶ X) [IsClosedImmersion f] (M : LineBundle X)
    (hzero : ∀ z : cohomology
      (kernel ((Scheme.Modules.pullbackPushforwardAdjunction f).unit.app M.sheaf)) 1,
      z = 0) :
    Function.Surjective (fun s : GlobalSections X M.sheaf => pullbackSection f s) := by
  let u := (Scheme.Modules.pullbackPushforwardAdjunction f).unit.app M.sheaf
  have : Epi u := closed_line_unit_epi f M
  let S := ShortComplex.mk (kernel.ι u) u (kernel.condition u)
  have hS : S.ShortExact := { exact := ShortComplex.exact_kernel u }
  exact PiExponent.NumericalAmpleness.pullbackSection_surjective_of_unit_surjective f M
    (globalSections_surjective_of_ext_one_zero S hS hzero)

end PiExponentSeshadri.Geometry

end

end OAI
end Source0671

-- Source: OAI/NumberTheory/PiExponent/Approximation/ClosedUnitKernel.lean
section Source0672
/-
Modification notice for the LogTwo project.
Derived from openai/math (Apache-2.0), revision adc7f1241b42e322a6451854ab7e4b4c146bf78a.
Original source: lean/OAI/NumberTheory/PiExponent/Approximation/ClosedUnitKernel.lean
Changes: Convert module/import declarations to the Lean 4.34 public module format.
See ../THIRD_PARTY_NOTICES.txt for provenance and the recorded changes.
-/

namespace OAI

noncomputable section
namespace PiExponentSeshadri.Geometry

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian Opposite
open PiExponentSeshadri.TensorPure

variable {X Y : Scheme.{0}}

def closedLineQuotientIso (f : Y ⟶ X) (M : LineBundle X) :
    moduleTensor X ((Scheme.Modules.pushforward f).obj (structureSheaf Y)) M.sheaf ≅
      (Scheme.Modules.pushforward f).obj (M.pullback f).sheaf :=
  PiExponent.ProjectionFormula.iso f (structureSheaf Y) M ≪≫
    (Scheme.Modules.pushforward f).mapIso (moduleTensorUnit (M.pullback f).sheaf)

theorem closedLineQuotientIso_map (f : Y ⟶ X) (M : LineBundle X) :
    moduleTensorMap (PiExponentSeshadri.IdealModule.structureMap f) (𝟙 M.sheaf) ≫
      (closedLineQuotientIso f M).hom =
    (moduleTensorUnit M.sheaf).hom ≫
      (Scheme.Modules.pullbackPushforwardAdjunction f).unit.app M.sheaf := by
  apply PiExponentSeshadri.TensorPure.hom_ext
  intro U a m
  let η := ((Scheme.Modules.pullbackPushforwardAdjunction f).unit.app M.sheaf).val.app (op U)
  have ht := map_pure (PiExponentSeshadri.IdealModule.structureMap f) (𝟙 M.sheaf) U a m
  have hp := PiExponent.ProjectionFormula.hom_pure f (structureSheaf Y) M.sheaf U
    ((PiExponentSeshadri.IdealModule.structureMap f).app U a) m
  have hu := unit_pure (M.pullback f).sheaf (f ⁻¹ᵁ U)
    ((PiExponentSeshadri.IdealModule.structureMap f).app U a) (η m)
  have hv := unit_pure M.sheaf U a m
  have hs := η.hom.map_smul a m
  exact (congrArg (fun z => (moduleTensorUnit (M.pullback f).sheaf).hom.app (f ⁻¹ᵁ U)
      ((PiExponent.ProjectionFormula.hom f (structureSheaf Y) M.sheaf).app U z)) ht).trans
    ((congrArg (fun z => (moduleTensorUnit (M.pullback f).sheaf).hom.app (f ⁻¹ᵁ U) z) hp).trans
      (hu.trans (hs.symm.trans (congrArg (fun z => η z) hv).symm)))

def closedLineUnitKernelIso (f : Y ⟶ X) [IsClosedImmersion f] (M : LineBundle X) :
    moduleTensor X (PiExponentSeshadri.IdealModule.idealModule f) M.sheaf ≅
      kernel ((Scheme.Modules.pullbackPushforwardAdjunction f).unit.app M.sheaf) := by
  let S := ShortComplex.mk (PiExponentSeshadri.IdealModule.inclusion f)
    (PiExponentSeshadri.IdealModule.structureMap f) (kernel.condition _)
  let T := S.map (moduleTwistFunctor M 1)
  have hT : T.ShortExact := moduleTwistFunctor_shortExact M 1 S
    (PiExponentSeshadri.IdealModule.closedSequence_exact f)
  let e : T.X₁ ≅ kernel T.g :=
    hT.fIsKernel.conePointUniqueUpToIso (limit.isLimit _)
  exact e ≪≫ kernel.mapIso T.g
    ((Scheme.Modules.pullbackPushforwardAdjunction f).unit.app M.sheaf)
    (moduleTensorUnit M.sheaf) (closedLineQuotientIso f M)
    (closedLineQuotientIso_map f M)

theorem pullbackSection_surjective_of_idealTensor_cohomology_zero
    (f : Y ⟶ X) [IsClosedImmersion f] (M : LineBundle X)
    (hzero : ∀ z : cohomology
      (moduleTensor X (PiExponentSeshadri.IdealModule.idealModule f) M.sheaf) 1, z = 0) :
    Function.Surjective (fun s : GlobalSections X M.sheaf => pullbackSection f s) := by
  apply pullbackSection_surjective_of_kernel_cohomology_zero f M
  exact PiExponent.GeometrySupport.SerrePowerDescent.ext_zero_of_iso
    (closedLineUnitKernelIso f M) 1 hzero

end PiExponentSeshadri.Geometry

end

end OAI
end Source0672

-- Source: OAI/NumberTheory/PiExponent/Ampleness/ComponentAmpleDescent.lean
section Source0673
/-
Modification notice for the LogTwo project.
Derived from openai/math (Apache-2.0), revision adc7f1241b42e322a6451854ab7e4b4c146bf78a.
Original source: lean/OAI/NumberTheory/PiExponent/Ampleness/ComponentAmpleDescent.lean
Changes: Convert module/import declarations to the Lean 4.34 public module format.
See ../THIRD_PARTY_NOTICES.txt for provenance and the recorded changes.
-/

namespace OAI

namespace PiExponentSeshadri.ComponentAmpleDescent
noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace
open PiExponentSeshadri.Geometry PiExponentSeshadri.IdealModule
variable {X : Scheme.{0}} [IsNoetherian X] [IsReduced X]
variable {R : Type} [CommRing R] [IsNoetherianRing R]

theorem exists_complementary_ideal_descent
    (I J : X.IdealSheafData) (hcover : I.support ⊔ J.support = ⊤) :
    ∃ N : J.subscheme.Modules, N.IsFinitePresentation ∧
      Nonempty ((Scheme.Modules.pushforward J.subschemeι).obj N ≅ closedModule I) := by
  have : (closedModule I).IsFinitePresentation := closedModule_isFinitePresentation I
  apply ClosedAnnihilatedDescent.exists_closed_coherent_descent J.subschemeι (closedModule I)
  intro U
  exact closedModule_restrict_annihilated hcover U

theorem eventual_restriction_surjective_of_complement_ample
    (p : X ⟶ Spec (CommRingCat.of R)) [IsProper p]
    (K L : LineBundle X) (I J : X.IdealSheafData)
    (hcover : I.support ⊔ J.support = ⊤) (hJ : (L.pullback J.subschemeι).IsAmple) :
    ∃ B : ℕ, ∀ n ≥ B, Function.Surjective
      (fun s : GlobalSections X (K.tensor (L.pow n)).sheaf => pullbackSection I.subschemeι s) := by
  obtain ⟨N,hN,⟨e⟩⟩ := exists_complementary_ideal_descent I J hcover
  let : N.IsFinitePresentation := hN
  obtain ⟨B,hB⟩ := eventual_tensor_cohomology_zero_of_closed_pushforward p J.subschemeι
    (closedModule I) N e K L hJ
  refine ⟨B,fun n hn => ?_⟩
  exact pullbackSection_surjective_of_idealTensor_cohomology_zero I.subschemeι
    (K.tensor (L.pow n)) (hB n hn 1 (by decide))

theorem isAmple_of_reduced_closed_cover
    (p : X ⟶ Spec (CommRingCat.of R)) [IsProper p]
    (L H : LineBundle X) (hH : H.IsAmple)
    (I J : X.IdealSheafData) (hcover : I.support ⊔ J.support = ⊤)
    (hI : (L.pullback I.subschemeι).IsAmple) (hJ : (L.pullback J.subschemeι).IsAmple) :
    L.IsAmple := by
  let : NoetherianSpace I.subscheme :=
    I.subschemeι.isClosedEmbedding.isEmbedding.isInducing.noetherianSpace
  let : NoetherianSpace J.subscheme :=
    J.subschemeι.isClosedEmbedding.isEmbedding.isInducing.noetherianSpace
  have hc : Set.range I.subschemeι ∪ Set.range J.subschemeι = Set.univ := by
    rw [I.range_subschemeι,J.range_subschemeι]
    exact congrArg (fun Z : Closeds X => (Z : Set X)) hcover
  exact isAmple_of_eventual_restriction_surjective I.subschemeι J.subschemeι L H hH hc hI hJ
    (eventual_restriction_surjective_of_complement_ample p H.inverse L I J hcover hJ)
    (eventual_restriction_surjective_of_complement_ample p H.inverse L J I
      (by simpa only [sup_comm] using hcover) hI)

end
end PiExponentSeshadri.ComponentAmpleDescent

end OAI
end Source0673

-- Source: OAI/NumberTheory/PiExponent/Geometry/IntegralCurveExistence.lean
section Source0674
/-
Modification notice for the LogTwo project.
Derived from openai/math (Apache-2.0), revision adc7f1241b42e322a6451854ab7e4b4c146bf78a.
Original source: lean/OAI/NumberTheory/PiExponent/Geometry/IntegralCurveExistence.lean
Changes: Convert module/import declarations to the Lean 4.34 public module format.
See ../THIRD_PARTY_NOTICES.txt for provenance and the recorded changes.
-/

namespace OAI

open CategoryTheory AlgebraicGeometry TopologicalSpace Topology Order

namespace PiExponent.NumericalAmpleness

noncomputable section

def irreducibleClosedRestrict {X : Type*} [TopologicalSpace X]
    (Z : IrreducibleCloseds X) (W : Set.Iic Z) : IrreducibleCloseds (Z : Set X) where
  carrier := {x : ↥(Z : Set X) | x.val ∈ (W.val : Set X)}
  isIrreducible' := by
    have : IrreducibleSpace (W.val : Set X) := Subtype.irreducibleSpace W.val.isIrreducible
    have hi := (IrreducibleSpace.isIrreducible_univ (W.val : Set X)).image
      (Set.inclusion W.property) (continuous_inclusion W.property).continuousOn
    convert hi using 1
    ext x
    simp only [Set.mem_image, Set.mem_univ, true_and]
    constructor
    · intro hx
      exact ⟨⟨x.val, hx⟩, Subtype.ext rfl⟩
    · rintro ⟨y, rfl⟩
      exact y.property
  isClosed' := W.val.isClosed.preimage continuous_subtype_val

def irreducibleClosedsBelowEquiv {X : Type*} [TopologicalSpace X]
    (Z : IrreducibleCloseds X) :
    IrreducibleCloseds (Z : Set X) ≃o Set.Iic Z where
  toFun W := ⟨{
    carrier := Subtype.val '' (W : Set (Z : Set X))
    isIrreducible' := W.isIrreducible.image Subtype.val continuous_subtype_val.continuousOn
    isClosed' := Z.isClosed.isClosedMap_subtype_val _ W.isClosed }, by
      rintro _ ⟨x, _, rfl⟩
      exact x.property⟩
  invFun := irreducibleClosedRestrict Z
  left_inv W := by
    ext x
    change x.val ∈ Subtype.val '' (W : Set ↥(Z : Set X)) ↔ x ∈ (W : Set ↥(Z : Set X))
    constructor
    · rintro ⟨y, hy, hxy⟩
      have heq : y = x := Subtype.ext hxy
      exact heq ▸ hy
    · intro hx
      exact ⟨x, hx, rfl⟩
  right_inv W := by
    apply Subtype.ext
    apply SetLike.coe_injective
    change (Subtype.val : ↥(Z : Set X) → X) '' {x : ↥(Z : Set X) | x.val ∈ (W.val : Set X)} = (W.val : Set X)
    apply Set.image_preimage_eq_of_subset
    simpa only [Subtype.range_coe] using (show (W.val : Set X) ⊆ Z from W.property)
  map_rel_iff' := by
    intro W V
    change Subtype.val '' (W : Set (Z : Set X)) ⊆ Subtype.val '' (V : Set (Z : Set X)) ↔ W ≤ V
    exact Set.image_subset_image_iff Subtype.val_injective

theorem topologicalKrullDim_irreducibleClosed {X : Type*} [TopologicalSpace X]
    (Z : IrreducibleCloseds X) :
    topologicalKrullDim (Z : Set X) = (Order.height Z : WithBot ℕ∞) := by
  rw [topologicalKrullDim, Order.krullDim_eq_of_orderIso (irreducibleClosedsBelowEquiv Z),
    ← Order.height_eq_krullDim_Iic]

theorem exists_irreducibleClosed_dimension_one (X : Type*) [TopologicalSpace X]
    (d : ℕ) (hdim : topologicalKrullDim X = d) (hd : 0 < d) :
    ∃ Z : IrreducibleCloseds X, topologicalKrullDim (Z : Set X) = 1 := by
  have hdim' : Order.krullDim (IrreducibleCloseds X) = d := hdim
  obtain ⟨p, hp⟩ := Order.le_krullDim_iff.mp (le_of_eq hdim'.symm)
  have hlast : (p.length : ℕ∞) = Order.height p.last := by
    apply le_antisymm (Order.length_le_height_last (p := p))
    have hh := Order.height_le_krullDim p.last
    rw [hdim', ← hp] at hh
    exact_mod_cast hh
  have hidx : 1 < p.length + 1 := by omega
  refine ⟨p ⟨1, hidx⟩, ?_⟩
  rw [topologicalKrullDim_irreducibleClosed]
  have hh := Order.height_eq_index_of_length_eq_height_last hlast ⟨1, hidx⟩
  simpa using congrArg (fun n : ℕ∞ => (n : WithBot ℕ∞)) hh

theorem isReduced_vanishingIdeal_subscheme {X : Scheme} (Z : Closeds X) :
    IsReduced (Scheme.IdealSheafData.vanishingIdeal Z).subscheme := by
  let I := Scheme.IdealSheafData.vanishingIdeal Z
  apply (IsReduced.iff_of_openCover I.subscheme I.subschemeCover.openCover).mpr
  intro U
  change X.affineOpens at U
  change IsReduced (Spec (CommRingCat.of (Γ(X, U.1) ⧸ I.ideal U)))
  have hI : (I.ideal U).IsRadical := by
    simpa only [I, Scheme.IdealSheafData.vanishingIdeal_ideal] using
      PrimeSpectrum.isRadical_vanishingIdeal (U.2.fromSpec ⁻¹' (Z : Set X))
  have : _root_.IsReduced (Γ(X, U.1) ⧸ I.ideal U) :=
    (Ideal.isRadical_iff_quotient_reduced _).mp hI
  infer_instance

def integralCurveOfIrreducibleClosed {X : Scheme.{0}} (Z : IrreducibleCloseds X)
    (hZ : topologicalKrullDim (Z : Set X) = 1) : IntegralCurve X := by
  let C : Closeds X := ⟨Z, Z.isClosed⟩
  let I := Scheme.IdealSheafData.vanishingIdeal C
  have hs : (I.support : Set X) = (Z : Set X) := by
    simp only [I, Scheme.IdealSheafData.coe_support_vanishingIdeal]
    rfl
  have : IsReduced I.subscheme := isReduced_vanishingIdeal_subscheme C
  have : IrreducibleSpace I.subscheme := by
    change IrreducibleSpace (I.support : Set X)
    rw [hs]
    exact Subtype.irreducibleSpace Z.isIrreducible
  refine {
    scheme := I.subscheme
    embedding := I.subschemeι
    closedImmersion := inferInstance
    integral := isIntegral_of_irreducibleSpace_of_isReduced _
    dimension := ?_ }
  change topologicalKrullDim (I.support : Set X) = 1
  rw [hs]
  exact hZ

theorem nonempty_integralCurve_of_dimension_pos (X : Scheme.{0})
    (d : ℕ) (hdim : topologicalKrullDim X = d) (hd : 0 < d) :
    Nonempty (IntegralCurve X) := by
  obtain ⟨Z, hZ⟩ := exists_irreducibleClosed_dimension_one X d hdim hd
  exact ⟨integralCurveOfIrreducibleClosed Z hZ⟩

end
end PiExponent.NumericalAmpleness

end OAI
end Source0674

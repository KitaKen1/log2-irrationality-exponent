/- Generated rc4 checkpoint for LogTwo.
Modified from the reduced edition: new imports, separate module compilation,
and synchronous elaboration. Original source blocks and notices are retained.
See ../../../THIRD_PARTY_NOTICES.txt and ../../reduction.json.
-/
module
public import LogTwoCheckpoints.Part012
public import LogTwoCheckpoints.Part013
public import LogTwoCheckpoints.Part014
public import LogTwoCheckpoints.Part015
public import LogTwoCheckpoints.Part016
public import LogTwoCheckpoints.Part017
public import Batteries.Logic
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Monoidal
public import Mathlib.Algebra.Module.LocalizedModule.Away
public import Mathlib.AlgebraicGeometry.Artinian
public import Mathlib.AlgebraicGeometry.Modules.Tilde
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.Analysis.Complex.Polynomial.Basic
public import Mathlib.Data.Opposite
@[expose] public section
set_option Elab.async false

-- Source: OAI/NumberTheory/PiExponent/Geometry/CartierPowerFrames.lean
section Source0450
/-
Modification notice for the LogTwo project.
Derived from openai/math (Apache-2.0), revision adc7f1241b42e322a6451854ab7e4b4c146bf78a.
Original source: lean/OAI/NumberTheory/PiExponent/Geometry/CartierPowerFrames.lean
Changes: Convert module/import declarations to the Lean 4.34 public module format.
See ../THIRD_PARTY_NOTICES.txt for provenance and the recorded changes.
-/

namespace OAI

namespace PiExponent.CartierPowerFrames
noncomputable section
open AlgebraicGeometry CategoryTheory TopologicalSpace
open PiExponentSeshadri.Geometry PiExponentSeshadri.Frames
variable {X : Scheme.{0}}
def sectionMultiplyLeft (L M : X.Modules) (s : structureSheaf X ⟶ L) :
    M ⟶ moduleTensor X L M :=
  (moduleTensorUnit M).inv ≫ moduleTensorMap s (𝟙 M)

def tensorFrame (L M : X.Modules) (U : X.Opens)
    (e : L.restrict U.ι ≅ O U.toScheme)
    (f : M.restrict U.ι ≅ O U.toScheme) :
    (moduleTensor X L M).restrict U.ι ≅ O U.toScheme :=
  moduleTensorRestrict U L M ≪≫ moduleTensorIso e f ≪≫
    moduleTensorUnit (O U.toScheme)

def tensorUnitTwist (M : X.Modules) (U : X.Opens)
    (f : M.restrict U.ι ≅ O U.toScheme) : O U.toScheme ≅ O U.toScheme :=
  f.symm ≪≫ (Scheme.Modules.restrictFunctor U.ι).mapIso (moduleTensorUnit M).symm ≪≫
    moduleTensorRestrict U (O X) M ≪≫
      moduleTensorIso (Scheme.Modules.restrictUnitIso U.ι) f ≪≫ moduleTensorUnit (O U.toScheme)

private lemma frame_section {C : Type*} [Category C] {A B D : C}
    (u : A ≅ B) (s : A ⟶ D) (e : D ≅ B) :
    s ≫ e.hom = u.hom ≫ ((u.inv ≫ s) ≫ e.hom) := by
  simp

private lemma framed_multiply {C : Type*} [Category C] {A B D P Q T O : C}
    (g : O ⟶ A) (k : A ⟶ B) (m : B ⟶ D) (r : B ⟶ P) (r' : D ⟶ Q)
    (e : P ⟶ T) (e' : Q ⟶ T) (u : T ⟶ O) (a : O ⟶ O)
    (p : P ⟶ Q) (b : T ⟶ T)
    (hn : m ≫ r' = r ≫ p) (ht : p ≫ e' = e ≫ b) (hs : b ≫ u = u ≫ a) :
    g ≫ (k ≫ m) ≫ (r' ≫ e' ≫ u) = (g ≫ k ≫ r ≫ e ≫ u) ≫ a := by
  simp only [Category.assoc]
  rw [← Category.assoc m r', hn]
  simp only [Category.assoc]
  rw [← Category.assoc p e', ht]
  simp only [Category.assoc]
  rw [hs]

lemma tensor_multiply_framed (L M : X.Modules) (s : O X ⟶ L) (U : X.Opens)
    (e : L.restrict U.ι ≅ O U.toScheme)
    (f : M.restrict U.ι ≅ O U.toScheme) :
    f.inv ≫ (Scheme.Modules.restrictFunctor U.ι).map (sectionMultiplyLeft L M s) ≫
      (tensorFrame L M U e f).hom = (tensorUnitTwist M U f).hom ≫
        (restrictSection U.ι s ≫ e.hom) := by
  let F := Scheme.Modules.restrictFunctor U.ι
  let R := moduleTensorRestrict U (O X) M
  let R' := moduleTensorRestrict U L M
  let E := moduleTensorIso (Scheme.Modules.restrictUnitIso U.ι) f
  let E' := moduleTensorIso e f
  let T := moduleTensorUnit (O U.toScheme)
  let a : O U.toScheme ⟶ O U.toScheme := restrictSection U.ι s ≫ e.hom
  let p := moduleTensorMap (F.map s) (𝟙 (M.restrict U.ι))
  have hn : F.map (moduleTensorMap s (𝟙 M)) ≫ R'.hom = R.hom ≫ p :=
    (moduleTensorRestrict_natural U s (𝟙 M)).trans
      (congrArg (fun q => R.hom ≫ moduleTensorMap (F.map s) q) (F.map_id M))
  have he : F.map s ≫ e.hom = (Scheme.Modules.restrictUnitIso U.ι).hom ≫ a := by
    simpa only [a, restrictSection] using!
      frame_section (Scheme.Modules.restrictUnitIso U.ι) (F.map s) e
  have h₁ := (moduleTensorMap_comp (F.map s) e.hom (𝟙 (M.restrict U.ι)) f.hom).symm.trans
    (congrArg (moduleTensorMap (F.map s ≫ e.hom)) (Category.id_comp f.hom))
  have h₂ := (moduleTensorMap_comp (Scheme.Modules.restrictUnitIso U.ι).hom a
      f.hom (𝟙 (O U.toScheme))).symm.trans
    (congrArg (moduleTensorMap ((Scheme.Modules.restrictUnitIso U.ι).hom ≫ a))
      (Category.comp_id f.hom))
  have ht : p ≫ E'.hom = E.hom ≫ moduleTensorMap a (𝟙 (O U.toScheme)) :=
    h₁.trans ((congrArg (fun q : F.obj (O X) ⟶ O U.toScheme => moduleTensorMap q f.hom)
      he).trans h₂.symm)
  have hs : moduleTensorMap a (𝟙 (O U.toScheme)) ≫ T.hom = T.hom ≫ a :=
    (moduleTensorUnit_scalar (X := U.toScheme) a (𝟙 (O U.toScheme))).trans
      (congrArg (fun q => T.hom ≫ q) (Category.comp_id a))
  have hfinal := framed_multiply f.inv (F.map (moduleTensorUnit M).inv)
    (F.map (moduleTensorMap s (𝟙 M))) R.hom R'.hom E.hom E'.hom T.hom a p _ hn ht hs
  simpa only [sectionMultiplyLeft, tensorFrame, tensorUnitTwist] using!
    (congrArg (fun q => f.inv ≫ q ≫ (tensorFrame L M U e f).hom)
      (F.map_comp (moduleTensorUnit M).inv (moduleTensorMap s (𝟙 M)))).trans hfinal

lemma tensor_multiply_ideal (L M : X.Modules) (s : O X ⟶ L)
    (U : X.affineOpens) (e : L.restrict U.1.ι ≅ O U.1.toScheme)
    (f : M.restrict U.1.ι ≅ O U.1.toScheme) :
    Ideal.span {U.1.topIso.hom (endValue (f.inv ≫
      (Scheme.Modules.restrictFunctor U.1.ι).map (sectionMultiplyLeft L M s) ≫
        (tensorFrame L M U.1 e f).hom))} =
    Ideal.span {U.1.topIso.hom (coefficient e (restrictSection U.1.ι s))} := by
  rw [tensor_multiply_framed,endValue_comp,map_mul,← Ideal.span_singleton_mul_span_singleton]
  have hu : IsUnit (endValue (tensorUnitTwist M U.1 f).hom) :=
    (end_isIso_iff _).mp inferInstance
  rw [Ideal.span_singleton_eq_top.mpr (hu.map U.1.topIso.hom.hom),Ideal.top_mul]
  rfl

theorem cartierPowerMultiply_ideal (L : LineBundle X) (s : GlobalSections X L.sheaf)
    (n : ℕ) (U : X.affineOpens)
    (e : L.sheaf.restrict U.1.ι ≅ structureSheaf U.1.toScheme) :
    Ideal.span {U.1.topIso.hom (endValue ((modulePowFrame U.1 e n).inv ≫
      (Scheme.Modules.restrictFunctor U.1.ι).map
        (PiExponent.NumericalAmpleness.cartierPowerMultiply L s n) ≫
      (modulePowFrame U.1 e (n+1)).hom))} =
    Ideal.span {U.1.topIso.hom (coefficient e (restrictSection U.1.ι s))} :=
  tensor_multiply_ideal L.sheaf (modulePow X L.sheaf n) s U e (modulePowFrame U.1 e n)
end
end PiExponent.CartierPowerFrames

end OAI
end Source0450

-- Source: OAI/NumberTheory/PiExponent/Approximation/GlueGlobalGenerators.lean
section Source0451
/-
Modification notice for the LogTwo project.
Derived from openai/math (Apache-2.0), revision adc7f1241b42e322a6451854ab7e4b4c146bf78a.
Original source: lean/OAI/NumberTheory/PiExponent/Approximation/GlueGlobalGenerators.lean
Changes: Convert module/import declarations to the Lean 4.34 public module format.
See ../THIRD_PARTY_NOTICES.txt for provenance and the recorded changes.
-/

namespace OAI

namespace PiExponent.GlueGlobalGenerators
noncomputable section
universe u
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace
open PiExponentSeshadri.Geometry PiExponentSeshadri.Frames

variable {X : Scheme.{u}} (M : X.Modules) {ι : Type u}
  (U : ι → X.Opens) (hcover : (⨆ i, U i) = ⊤)
  (σ : ∀ i, (M.restrict (U i).ι).GeneratingSections)
  (t : ∀ i, (σ i).I → GlobalSections X M)
  (ht : ∀ i j, restrictSection (U i).ι (t i j) =
    (M.restrict (U i).ι).unitHomEquiv.symm ((σ i).s j))

include hcover ht

theorem globalEvaluation_epi : Epi
    (M.freeHomEquiv.symm (fun ij : Σ i, (σ i).I => M.unitHomEquiv (t ij.1 ij.2))) := by
  let q := M.freeHomEquiv.symm (fun ij : Σ i, (σ i).I => M.unitHomEquiv (t ij.1 ij.2))
  have hq (i : ι) (j : (σ i).I) : SheafOfModules.ιFree ⟨i,j⟩ ≫ q = t i j := by
    erw [← SheafOfModules.unitHomEquiv_symm_freeHomEquiv_apply]
    simp only [q, Equiv.apply_symm_apply]
    exact M.unitHomEquiv.symm_apply_apply (t i j)
  change Epi (C := X.Modules) q
  apply (Preadditive.epi_iff_cancel_zero (C := X.Modules) q).mpr
  intro N g hg
  have hz (i : ι) (j : (σ i).I) : t i j ≫ g = 0 := by
    erw [← hq i j, Category.assoc, hg, comp_zero]
  apply CoherentTwist.eq_zero_of_local
  intro x
  have hx : x ∈ ⨆ i, U i := by rw [hcover]; trivial
  obtain ⟨i, hxi⟩ := Opens.mem_iSup.mp hx
  refine ⟨U i,hxi,?_⟩
  apply (@cancel_epi _ _ _ _ _ (σ i).π (σ i).epi _ _).mp
  erw [comp_zero]
  apply (SheafOfModules.isColimitFreeCofan (σ i).I).hom_ext
  intro j
  change SheafOfModules.ιFree j.as ≫ ((σ i).π ≫
    (Scheme.Modules.restrictFunctor (U i).ι).map g) = SheafOfModules.ιFree j.as ≫ 0
  erw [comp_zero, ← Category.assoc,
    ← SheafOfModules.unitHomEquiv_symm_freeHomEquiv_apply]
  simp only [SheafOfModules.GeneratingSections.π, Equiv.apply_symm_apply]
  erw [← ht i j.as]
  let R : X.Modules ⥤ (U i).toScheme.Modules := Scheme.Modules.restrictFunctor (U i).ι
  let e : R.obj (O X) ≅ O (U i).toScheme := Scheme.Modules.restrictUnitIso (U i).ι
  change (e.inv ≫ R.map (t i j.as)) ≫ R.map g = 0
  erw [Category.assoc, ← Functor.map_comp, hz, Functor.map_zero, comp_zero]

def globalGenerators : M.GeneratingSections where
  I := Σ i, (σ i).I
  s ij := M.unitHomEquiv (t ij.1 ij.2)
  epi := globalEvaluation_epi M U hcover σ t ht

instance [Finite ι] [hσ : ∀ i, (σ i).IsFiniteType] :
    (globalGenerators M U hcover σ t ht).IsFiniteType where
  finite := by
    let (i : ι) : Finite (σ i).I := (hσ i).finite
    exact inferInstanceAs (Finite (Σ i, (σ i).I))

theorem exists_finite_global_generators [Finite ι] [∀ i, (σ i).IsFiniteType] :
    ∃ q : M.GeneratingSections, q.IsFiniteType :=
  ⟨globalGenerators M U hcover σ t ht, inferInstance⟩

end
end PiExponent.GlueGlobalGenerators

end OAI
end Source0451

-- Source: OAI/NumberTheory/PiExponent/Approximation/TwistSectionScalars.lean
section Source0452
-- Modified in this edition: unused plain lemmas removed; see reduction.json.
/-
Modification notice for the LogTwo project.
Derived from openai/math (Apache-2.0), revision adc7f1241b42e322a6451854ab7e4b4c146bf78a.
Original source: lean/OAI/NumberTheory/PiExponent/Approximation/TwistSectionScalars.lean
Changes: Convert module/import declarations to the Lean 4.34 public module format.
See ../THIRD_PARTY_NOTICES.txt for provenance and the recorded changes.
-/

namespace OAI

namespace PiExponentSeshadri.Geometry
noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
open PiExponentSeshadri.TensorPure PiExponentSeshadri.Frames
variable {X : Scheme}

lemma moduleSectionMultiplyRight_pure (M : X.Modules) {L : X.Modules}
    (s : structureSheaf X ⟶ L) (U : X.Opens) (m : Γ(M,U)) :
    (moduleSectionMultiplyRight M s).app U m =
      pure M L U m (s.app U (1 : Γ(X,U))) := by
  have h : (moduleTensorRightUnit M).hom.app U
      (pure M (structureSheaf X) U m (1 : Γ(X,U))) = m := by
    erw [right_unit_pure, one_smul]
  have hi : (moduleTensorRightUnit M).inv.app U m =
      pure M (structureSheaf X) U m (1 : Γ(X,U)) := by
    calc
      _ = (moduleTensorRightUnit M).inv.app U
          ((moduleTensorRightUnit M).hom.app U
            (pure M (structureSheaf X) U m (1 : Γ(X,U)))) := congrArg _ h.symm
      _ = _ := congrArg (fun q => q.app U
        (pure M (structureSheaf X) U m (1 : Γ(X,U)))) (moduleTensorRightUnit M).hom_inv_id
  change (moduleTensorMap (𝟙 M) s).app U ((moduleTensorRightUnit M).inv.app U m) = _
  erw [hi, TensorPure.map_pure]
  rfl

lemma moduleTensorFrame_pure (M : X.Modules) {L : X.Modules}
    (e : L ≅ structureSheaf X) (U : X.Opens) (m : Γ(M,U)) (l : Γ(L,U)) :
    (moduleTensorFrame M e).hom.app U (pure M L U m l) =
      (show Γ(X,U) from e.hom.app U l) • m := by
  change (moduleTensorRightUnit M).hom.app U
    ((moduleTensorMap (𝟙 M) e.hom).app U (pure M L U m l)) = _
  have h := TensorPure.map_pure (𝟙 M) e.hom U m l
  exact (congrArg (fun t => (moduleTensorRightUnit M).hom.app U t) h).trans
    (right_unit_pure M U m (e.hom.app U l))

lemma moduleSectionMultiplyRight_restrict_frame (M : X.Modules) {L : X.Modules}
    (s : structureSheaf X ⟶ L) (U : X.Opens)
    (e : L.restrict U.ι ≅ structureSheaf U.toScheme) (V : U.toScheme.Opens)
    (m : Γ(M,U.ι ''ᵁ V)) :
    ((moduleTensorRestrictFrame U L e).app M).hom.app V
      ((moduleSectionMultiplyRight M s).app (U.ι ''ᵁ V) m) =
      U.toScheme.presheaf.map (homOfLE (show V ≤ ⊤ from le_top)).op (coefficient e (restrictSection U.ι s)) •
        (show Γ(M.restrict U.ι,V) from m) := by
  change (moduleTensorFrame (M.restrict U.ι) e).hom.app V
    ((moduleTensorRestrict U M L).hom.app V
      ((moduleSectionMultiplyRight M s).app (U.ι ''ᵁ V) m)) = _
  have h₁ := moduleSectionMultiplyRight_pure M s (U.ι ''ᵁ V) m
  have h₂ := restrict_pure U M L V m (s.app (U.ι ''ᵁ V) (1 : Γ(X, U.ι ''ᵁ V)))
  have h₃ := moduleTensorFrame_pure (M.restrict U.ι) e V m
    (s.app (U.ι ''ᵁ V) (1 : Γ(X, U.ι ''ᵁ V)))
  refine ((congrArg (fun t => (moduleTensorFrame (M.restrict U.ι) e).hom.app V
      ((moduleTensorRestrict U M L).hom.app V t)) h₁).trans
    ((congrArg (fun t => (moduleTensorFrame (M.restrict U.ι) e).hom.app V t) h₂).trans h₃)).trans ?_
  have h := end_naturality (restrictSection U.ι s ≫ e.hom) V
  apply congrArg (fun a : Γ(U.toScheme,V) => a • (show Γ(M.restrict U.ι,V) from m))
  calc
    _ = (show Γ(U.toScheme,V) from e.hom.app V ((restrictSection U.ι s).app V
        (1 : Γ(U.toScheme,V)))) := by
      change e.hom.app V (s.app (U.ι ''ᵁ V) (1 : Γ(X,U.ι ''ᵁ V))) =
        e.hom.app V (s.app (U.ι ''ᵁ V) ((U.ι.appIso V).inv (1 : Γ(U.toScheme,V))))
      rw [show (U.ι.appIso V).inv (1 : Γ(U.toScheme,V)) =
        (1 : Γ(X,U.ι ''ᵁ V)) from (U.ι.appIso V).inv.hom.map_one]
    _ = _ := h

lemma moduleTwistForward_frame (L : LineBundle X)
    (s : structureSheaf X ⟶ L.sheaf) (U : X.Opens)
    (e : L.sheaf.restrict U.ι ≅ structureSheaf U.toScheme)
    (M : X.Modules) (V : U.toScheme.Opens) (n k : ℕ)
    (m : Γ((moduleTwistFunctor L n).obj M,U.ι ''ᵁ V)) :
    ((moduleTwistRestrictFrame L U e (n+k)).app M).hom.app V
      (((moduleTwistForward L s n k).app M).app (U.ι ''ᵁ V) m) =
      (U.toScheme.presheaf.map (homOfLE (show V ≤ ⊤ from le_top)).op
        (coefficient e (restrictSection U.ι s))) ^ k •
          ((moduleTwistRestrictFrame L U e n).app M).hom.app V m := by
  induction k with
  | zero => simp only [moduleTwistForward, NatTrans.id_app, pow_zero, one_smul]; rfl
  | succ k ih =>
    change ((moduleTwistRestrictFrame L U e (n+k)).app M).hom.app V
      (((moduleTensorRestrictFrame U L.sheaf e).app ((moduleTwistFunctor L (n+k)).obj M)).hom.app V
        ((moduleSectionMultiplyRight ((moduleTwistFunctor L (n+k)).obj M) s).app
          (U.ι ''ᵁ V) (((moduleTwistForward L s n k).app M).app (U.ι ''ᵁ V) m))) = _
    rw [moduleSectionMultiplyRight_restrict_frame, Scheme.Modules.Hom.app_smul,
      ih, smul_smul, pow_succ']

lemma moduleTwistSection_frame (L : LineBundle X)
    (s : structureSheaf X ⟶ L.sheaf) (U : X.Opens)
    (e : L.sheaf.restrict U.ι ≅ structureSheaf U.toScheme)
    (M : X.Modules) (V : U.toScheme.Opens) (n : ℕ) (m : Γ(M,U.ι ''ᵁ V)) :
    ((moduleTwistRestrictFrame L U e n).app M).hom.app V
      (((moduleTwistSection L s n).app M).app (U.ι ''ᵁ V) m) =
      (U.toScheme.presheaf.map (homOfLE (show V ≤ ⊤ from le_top)).op
        (coefficient e (restrictSection U.ι s))) ^ n •
          (show Γ(M.restrict U.ι,V) from m) := by
  induction n with
  | zero =>
      simp only [moduleTwistSection, moduleTwistRestrictFrame, NatTrans.id_app, pow_zero]
      exact (one_smul Γ(U.toScheme, V) (show Γ(M.restrict U.ι, V) from m)).symm
  | succ n ih =>
    change ((moduleTwistRestrictFrame L U e n).app M).hom.app V
      (((moduleTensorRestrictFrame U L.sheaf e).app ((moduleTwistFunctor L n).obj M)).hom.app V
        ((moduleSectionMultiplyRight ((moduleTwistFunctor L n).obj M) s).app
          (U.ι ''ᵁ V) (((moduleTwistSection L s n).app M).app (U.ι ''ᵁ V) m))) = _
    rw [moduleSectionMultiplyRight_restrict_frame, Scheme.Modules.Hom.app_smul,
      ih, smul_smul, pow_succ']

end
end PiExponentSeshadri.Geometry

end OAI
end Source0452

-- Source: OAI/NumberTheory/PiExponent/Approximation/TwistSectionClearing.lean
section Source0453
-- Modified in this edition: unused plain lemmas removed; see reduction.json.
/-
Modification notice for the LogTwo project.
Derived from openai/math (Apache-2.0), revision adc7f1241b42e322a6451854ab7e4b4c146bf78a.
Original source: lean/OAI/NumberTheory/PiExponent/Approximation/TwistSectionClearing.lean
Changes: Convert module/import declarations to the Lean 4.34 public module format.
See ../THIRD_PARTY_NOTICES.txt for provenance and the recorded changes.
-/

namespace OAI

namespace PiExponent.TwistSectionClearing
noncomputable section
open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite
open PiExponentSeshadri.Geometry PiExponentSeshadri.Frames
open PiExponent.GlobalSectionClearing
variable {X : Scheme}

lemma iso_section_restrict_zero_on {P Q : X.Modules} (e : P ≅ Q)
    {V W : X.Opens} (hVW : V ≤ W) (x : Γ(P,W))
    (hx : P.presheaf.map (homOfLE hVW).op x = 0) :
    Q.presheaf.map (homOfLE hVW).op (e.hom.app W x) = 0 := by
  have h := CategoryTheory.congr_fun (e.hom.mapPresheaf.naturality (homOfLE hVW).op) x
  change e.hom.app V (P.presheaf.map (homOfLE hVW).op x) =
    Q.presheaf.map (homOfLE hVW).op (e.hom.app W x) at h
  rw [hx, map_zero] at h
  exact h.symm

lemma frame_local_input_zero_on (L : LineBundle X) (s : structureSheaf X ⟶ L.sheaf)
    (U : X.Opens) (e : L.sheaf.restrict U.ι ≅ structureSheaf U.toScheme)
    (P : X.Modules) (W : X.Opens) (V : U.toScheme.Opens) (hVW : U.ι ''ᵁ V ≤ W)
    (x : Γ(P,W))
    (hx : P.presheaf.map (homOfLE
      (show W ⊓ PiExponentSeshadri.SectionOpens.isoOpen s ≤ W from inf_le_left)).op x = 0) :
    (P.restrict U.ι).presheaf.map (homOfLE
      (show V ⊓ U.toScheme.basicOpen (coefficient e (restrictSection U.ι s)) ≤ V from inf_le_left)).op
      (P.presheaf.map (homOfLE hVW).op x) = 0 := by
  have hD : U.ι ''ᵁ (V ⊓ U.toScheme.basicOpen (coefficient e (restrictSection U.ι s))) ≤
      W ⊓ PiExponentSeshadri.SectionOpens.isoOpen s := by
    apply le_inf
    · exact (U.ι.image_mono inf_le_left).trans hVW
    · apply (U.ι.image_mono inf_le_right).trans
      rw [← preimage_isoOpen s U.ι e]
      exact U.ι.image_preimage_le _
  change openRestriction P (U.ι.image_mono
    (show V ⊓ U.toScheme.basicOpen (coefficient e (restrictSection U.ι s)) ≤ V from inf_le_left))
    (openRestriction P hVW x) = 0
  erw [openRestriction_comp_apply]
  erw [← openRestriction_comp_apply P hD inf_le_left x]
  change openRestriction P hD (P.presheaf.map (homOfLE inf_le_left).op x) = 0
  rw [hx]
  exact map_zero (openRestriction P hD)

theorem frame_twistForward_zero_on (L : LineBundle X)
    (s : structureSheaf X ⟶ L.sheaf) (U : X.Opens)
    (e : L.sheaf.restrict U.ι ≅ structureSheaf U.toScheme)
    (M : X.Modules) [M.IsQuasicoherent] (n : ℕ)
    (V : U.toScheme.Opens) (hV : IsCompact (V : Set U.toScheme))
    (x : Γ(((moduleTwistFunctor L n).obj M).restrict U.ι, V))
    (hx : (((moduleTwistFunctor L n).obj M).restrict U.ι).presheaf.map (homOfLE
      (show V ⊓ U.toScheme.basicOpen (coefficient e (restrictSection U.ι s)) ≤ V from inf_le_left)).op x = 0) :
    ∃ K : ℕ, ∀ k ≥ K,
      (((moduleTwistForward L s n k).app M).app (U.ι ''ᵁ V)) x = 0 := by
  let c := coefficient e (restrictSection U.ι s)
  let E := (moduleTwistRestrictFrame L U e n).app M
  have hz := iso_section_restrict_zero_on E
    (show V ⊓ U.toScheme.basicOpen c ≤ V from inf_le_left) x hx
  obtain ⟨K, hK⟩ := compact_open_section_zero (M.restrict U.ι) c V hV (E.hom.app V x) hz
  refine ⟨K, fun k hk => ?_⟩
  apply (ConcreteCategory.bijective_of_isIso
    (((moduleTwistRestrictFrame L U e (n+k)).app M).hom.app V)).injective
  refine (moduleTwistForward_frame L s U e M V n k x).trans ?_
  have hh := hK k hk
  change (OAI.PiExponent.GlobalSectionClearing.restrictScalar U.toScheme V (c ^ k)) • E.hom.app V x = 0 at hh
  rw [map_pow] at hh
  exact hh.trans (map_zero (((moduleTwistRestrictFrame L U e (n+k)).app M).hom.app V).hom).symm

lemma hom_section_restriction {P Q : X.Modules} (f : P ⟶ Q)
    {V W : X.Opens} (hVW : V ≤ W) (x : Γ(P,W)) :
    Q.presheaf.map (homOfLE hVW).op (f.app W x) =
      f.app V (P.presheaf.map (homOfLE hVW).op x) := by
  have h := CategoryTheory.congr_fun (f.mapPresheaf.naturality (homOfLE hVW).op) x
  exact h.symm

theorem frame_twistForward_ambient_zero [NoetherianSpace X] (L : LineBundle X)
    (s : structureSheaf X ⟶ L.sheaf) (U : X.Opens)
    (e : L.sheaf.restrict U.ι ≅ structureSheaf U.toScheme)
    (M : X.Modules) [M.IsQuasicoherent] (n : ℕ) (W : X.Opens)
    (x : Γ((moduleTwistFunctor L n).obj M, W))
    (hx : ((moduleTwistFunctor L n).obj M).presheaf.map (homOfLE
      (show W ⊓ PiExponentSeshadri.SectionOpens.isoOpen s ≤ W from inf_le_left)).op x = 0) :
    ∃ K : ℕ, ∀ k ≥ K,
      ((moduleTwistFunctor L (n+k)).obj M).presheaf.map
        (homOfLE (show U ⊓ W ≤ W from inf_le_right)).op
        (((moduleTwistForward L s n k).app M).app W x) = 0 := by
  let : NoetherianSpace U.toScheme := NoetherianSpace.set (U : Set X)
  let V := U.ι ⁻¹ᵁ W
  have hVW : U.ι ''ᵁ V ≤ W := U.ι.image_preimage_le W
  have hlocal := frame_local_input_zero_on L s U e ((moduleTwistFunctor L n).obj M) W V hVW x hx
  obtain ⟨K, hK⟩ := frame_twistForward_zero_on L s U e M n V
    (NoetherianSpace.isCompact _) _ hlocal
  refine ⟨K, fun k hk => ?_⟩
  have hh : ((moduleTwistFunctor L (n+k)).obj M).presheaf.map (homOfLE hVW).op
      (((moduleTwistForward L s n k).app M).app W x) = 0 := by
    rw [hom_section_restriction]
    exact hK k hk
  have he : U.ι ''ᵁ V = U ⊓ W := by
    dsimp only [V]
    rw [Scheme.Hom.image_preimage_eq_opensRange_inf, Scheme.Opens.opensRange_ι]
  exact openRestriction_zero_congr ((moduleTwistFunctor L (n+k)).obj M) he _ _ _ hh

theorem twistForward_section_zero [NoetherianSpace X] (L : LineBundle X)
    (s : structureSheaf X ⟶ L.sheaf) (M : X.Modules) [M.IsQuasicoherent]
    (n : ℕ) (W : X.Opens) (x : Γ((moduleTwistFunctor L n).obj M, W))
    (hx : ((moduleTwistFunctor L n).obj M).presheaf.map (homOfLE
      (show W ⊓ PiExponentSeshadri.SectionOpens.isoOpen s ≤ W from inf_le_left)).op x = 0) :
    ∃ K : ℕ, ∀ k ≥ K, ((moduleTwistForward L s n k).app M).app W x = 0 := by
  classical
  choose U hxU he using L.locallyRankOne
  let e (a : X) := Classical.choice (he a)
  have hcover : IsOpenCover U := by
    rw [IsOpenCover]
    apply top_unique
    intro a ha
    exact Opens.mem_iSup.mpr ⟨a, hxU a⟩
  obtain ⟨I, hI⟩ := hcover.exists_finite_of_compactSpace
  have hI' : (⨆ i : I, U i.val) = ⊤ := hI
  choose K hK using fun i : I => frame_twistForward_ambient_zero L s (U i.val)
    (e i.val) M n W x hx
  refine ⟨Finset.univ.sup K, fun k hk => ?_⟩
  let P := (moduleTwistFunctor L (n+k)).obj M
  apply TopCat.Sheaf.eq_of_locally_eq' ⟨P.presheaf, P.isSheaf⟩
    (fun i : I => U i.val ⊓ W) W (fun i => homOfLE inf_le_right)
    (by rw [← iSup_inf_eq, hI', top_inf_eq])
  intro i
  have hi := hK i k ((Finset.le_sup (f := K) (Finset.mem_univ i)).trans hk)
  change P.presheaf.map _ (((moduleTwistForward L s n k).app M).app W x) = P.presheaf.map _ 0
  rw [map_zero]
  exact hi

end
end PiExponent.TwistSectionClearing

end OAI
end Source0453

-- Source: OAI/NumberTheory/PiExponent/Geometry/SheafSectionGluing.lean
section Source0454
/-
Modification notice for the LogTwo project.
Derived from openai/math (Apache-2.0), revision adc7f1241b42e322a6451854ab7e4b4c146bf78a.
Original source: lean/OAI/NumberTheory/PiExponent/Geometry/SheafSectionGluing.lean
Changes: Convert module/import declarations to the Lean 4.34 public module format.
See ../THIRD_PARTY_NOTICES.txt for provenance and the recorded changes.
-/

namespace OAI

namespace PiExponent.SheafSectionGluing
noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open PiExponent.GlobalSectionClearing
universe u
variable {X : Scheme.{u}} {P Q : X.Modules}

def mapSection (f : P ⟶ Q) (U : X.Opens) :
    OpenSections P U →ₗ[Γ(X,⊤)] OpenSections Q U where
  toFun := f.app U
  map_add' := map_add _
  map_smul' r x := by
    exact f.app_smul (r := restrictScalar X U r) (x := x)

lemma mapSection_naturality (f : P ⟶ Q) {U V : X.Opens} (h : U ≤ V)
    (x : OpenSections P V) :
    mapSection f U (openRestriction P h x) = openRestriction Q h (mapSection f V x) :=
  CategoryTheory.congr_fun (f.mapPresheaf.naturality (homOfLE h).op) x

@[simp] lemma mapSection_comp {R : X.Modules} (f : P ⟶ Q) (g : Q ⟶ R)
    (U : X.Opens) (x : OpenSections P U) :
    mapSection (f ≫ g) U x = mapSection g U (mapSection f U x) := rfl

lemma mapSection_congr (f : P ⟶ Q) {U V : X.Opens} (h : U = V)
    (x : OpenSections P U) :
    openSectionsCongr Q h (mapSection f U x) = mapSection f V (openSectionsCongr P h x) := by
  subst V
  rfl

theorem glue_after_map (f : P ⟶ Q) {ι : Type*} (U : ι → X.Opens)
    (hcover : (⨆ i, U i) = ⊤) (y : ∀ i, OpenSections P (U i))
    (hy : ∀ i j,
      mapSection f (U i ⊓ U j) (openRestriction P inf_le_left (y i)) =
        mapSection f (U i ⊓ U j) (openRestriction P inf_le_right (y j))) :
    ∃ z : OpenSections Q ⊤,
      ∀ i, openRestriction Q (show U i ≤ ⊤ from le_top) z = mapSection f (U i) (y i) := by
  have h := TopCat.Sheaf.existsUnique_gluing' ⟨_, Q.isSheaf⟩ U ⊤
    (fun i => homOfLE (show U i ≤ ⊤ from le_top)) (by rw [hcover])
    (fun i => mapSection f (U i) (y i)) ?_
  · obtain ⟨z, hz, _⟩ := h
    exact ⟨z, hz⟩
  · intro i j
    change openRestriction Q (show U i ⊓ U j ≤ U i from inf_le_left) (mapSection f (U i) (y i)) =
      openRestriction Q (show U i ⊓ U j ≤ U j from inf_le_right) (mapSection f (U j) (y j))
    rw [← mapSection_naturality, ← mapSection_naturality]
    exact hy i j

theorem restriction_of_glued_map (f : P ⟶ Q) {ι : Type*} (U : ι → X.Opens)
    (hcover : (⨆ i, U i) = ⊤) (D : X.Opens) (x : OpenSections P D)
    (y : ∀ i, OpenSections P (U i))
    (hy : ∀ i, openRestriction P (show U i ⊓ D ≤ U i from inf_le_left) (y i) =
      openRestriction P inf_le_right x)
    (z : OpenSections Q ⊤)
    (hz : ∀ i, openRestriction Q (show U i ≤ ⊤ from le_top) z = mapSection f (U i) (y i)) :
    openRestriction Q (show D ≤ ⊤ from le_top) z = mapSection f D x := by
  apply TopCat.Sheaf.eq_of_locally_eq' ⟨_, Q.isSheaf⟩ (fun i => U i ⊓ D) D
    (fun i => homOfLE inf_le_right) (by rw [← iSup_inf_eq, hcover, top_inf_eq])
  intro i
  change openRestriction Q inf_le_right (openRestriction Q (show D ≤ ⊤ from le_top) z) =
    openRestriction Q inf_le_right (mapSection f D x)
  rw [openRestriction_comp_apply,
    ← openRestriction_comp_apply Q (show U i ⊓ D ≤ U i from inf_le_left) le_top z,
    hz i, ← mapSection_naturality, hy i, mapSection_naturality]

theorem overlap_difference_zero {ι : Type*} (U : ι → X.Opens) (D : X.Opens)
    (x : OpenSections P D) (y : ∀ i, OpenSections P (U i))
    (hy : ∀ i, openRestriction P (show U i ⊓ D ≤ U i from inf_le_left) (y i) =
      openRestriction P inf_le_right x) (i j : ι) :
    openRestriction P (show (U i ⊓ U j) ⊓ D ≤ U i ⊓ U j from inf_le_left)
      (openRestriction P inf_le_left (y i) - openRestriction P inf_le_right (y j)) = 0 := by
  rw [map_sub, openRestriction_comp_apply, openRestriction_comp_apply]
  have hi := congrArg (openRestriction P
    (show (U i ⊓ U j) ⊓ D ≤ U i ⊓ D from inf_le_inf inf_le_left le_rfl)) (hy i)
  have hj := congrArg (openRestriction P
    (show (U i ⊓ U j) ⊓ D ≤ U j ⊓ D from inf_le_inf inf_le_right le_rfl)) (hy j)
  simp only [openRestriction_comp_apply] at hi hj
  rw [hi, hj, sub_self]

end
end PiExponent.SheafSectionGluing

end OAI
end Source0454

-- Source: OAI/NumberTheory/PiExponent/LocalAlgebra/TwistLocalExtension.lean
section Source0455
/-
Modification notice for the LogTwo project.
Derived from openai/math (Apache-2.0), revision adc7f1241b42e322a6451854ab7e4b4c146bf78a.
Original source: lean/OAI/NumberTheory/PiExponent/LocalAlgebra/TwistLocalExtension.lean
Changes: Convert module/import declarations to the Lean 4.34 public module format.
See ../THIRD_PARTY_NOTICES.txt for provenance and the recorded changes.
-/

namespace OAI

namespace PiExponentSeshadri.Geometry
noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open PiExponentSeshadri.Frames PiExponent.GlobalSectionClearing
variable {X : Scheme}

theorem local_twist_extension (L : LineBundle X)
    (s : structureSheaf X ⟶ L.sheaf) (U : X.Opens) [NoetherianSpace U.toScheme]
    (e : L.sheaf.restrict U.ι ≅ structureSheaf U.toScheme)
    (M : X.Modules) [M.IsQuasicoherent]
    (x : Γ(M.restrict U.ι, U.toScheme.basicOpen (coefficient e (restrictSection U.ι s)))) :
    let a := coefficient e (restrictSection U.ι s)
    let D := U.toScheme.basicOpen a
    ∃ N : ℕ, ∀ n ≥ N, ∃ y : Γ(((moduleTwistFunctor L n).obj M).restrict U.ι,⊤),
      (((moduleTwistFunctor L n).obj M).restrict U.ι).presheaf.map
        (homOfLE (U.toScheme.basicOpen_le a)).op y =
      ((moduleTwistRestrictFrame L U e n).app M).inv.app D
        ((restrictScalar U.toScheme D a)^n • x) := by
  dsimp only
  obtain ⟨N, hN⟩ := global_section_extends_native (M.restrict U.ι)
    (coefficient e (restrictSection U.ι s)) x
  refine ⟨N, fun n hn => ?_⟩
  obtain ⟨y, hy⟩ := hN n hn
  let E := (moduleTwistRestrictFrame L U e n).app M
  refine ⟨E.inv.app ⊤ y, ?_⟩
  have h := CategoryTheory.congr_fun (E.inv.mapPresheaf.naturality
    (homOfLE (U.toScheme.basicOpen_le (coefficient e (restrictSection U.ι s)))).op) y
  exact h.symm.trans (congrArg (E.inv.app _) hy)

theorem local_twist_extension_section (L : LineBundle X)
    (s : structureSheaf X ⟶ L.sheaf) (U : X.Opens) [NoetherianSpace U.toScheme]
    (e : L.sheaf.restrict U.ι ≅ structureSheaf U.toScheme)
    (M : X.Modules) [M.IsQuasicoherent]
    (x : Γ(M.restrict U.ι, U.toScheme.basicOpen (coefficient e (restrictSection U.ι s)))) :
    let a := coefficient e (restrictSection U.ι s)
    let D := U.toScheme.basicOpen a
    ∃ N : ℕ, ∀ n ≥ N, ∃ y : Γ(((moduleTwistFunctor L n).obj M).restrict U.ι,⊤),
      (((moduleTwistFunctor L n).obj M).restrict U.ι).presheaf.map
        (homOfLE (U.toScheme.basicOpen_le a)).op y =
      ((moduleTwistSection L s n).app M).app (U.ι ''ᵁ D) x := by
  dsimp only
  obtain ⟨N, hN⟩ := local_twist_extension L s U e M x
  refine ⟨N, fun n hn => ?_⟩
  obtain ⟨y, hy⟩ := hN n hn
  refine ⟨y, hy.trans ?_⟩
  let D := U.toScheme.basicOpen (coefficient e (restrictSection U.ι s))
  let E := (moduleTwistRestrictFrame L U e n).app M
  have h := moduleTwistSection_frame L s U e M D n x
  calc
    _ = E.inv.app D (E.hom.app D (((moduleTwistSection L s n).app M).app (U.ι ''ᵁ D) x)) :=
      congrArg (E.inv.app D) h.symm
    _ = _ := congrArg (fun q => q.app D
      (((moduleTwistSection L s n).app M).app (U.ι ''ᵁ D) x)) E.hom_inv_id

end
end PiExponentSeshadri.Geometry

end OAI
end Source0455

-- Source: OAI/NumberTheory/PiExponent/Approximation/TwistGlobalExtension.lean
section Source0456
/-
Modification notice for the LogTwo project.
Derived from openai/math (Apache-2.0), revision adc7f1241b42e322a6451854ab7e4b4c146bf78a.
Original source: lean/OAI/NumberTheory/PiExponent/Approximation/TwistGlobalExtension.lean
Changes: Convert module/import declarations to the Lean 4.34 public module format.
See ../THIRD_PARTY_NOTICES.txt for provenance and the recorded changes.
-/

namespace OAI

namespace PiExponent.TwistGlobalExtension
noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open PiExponentSeshadri.Geometry PiExponentSeshadri.Frames
open PiExponent.GlobalSectionClearing PiExponent.SheafSectionGluing
variable {X : Scheme}

lemma section_open_image {L : X.Modules} (s : structureSheaf X ⟶ L)
    (U : X.Opens) (e : L.restrict U.ι ≅ structureSheaf U.toScheme) :
    U.ι ''ᵁ U.toScheme.basicOpen (coefficient e (restrictSection U.ι s)) =
      U ⊓ sectionOpen X s := by
  change U.ι ''ᵁ U.toScheme.basicOpen (coefficient e (restrictSection U.ι s)) =
    U ⊓ PiExponentSeshadri.SectionOpens.isoOpen s
  rw [← preimage_isoOpen s U.ι e, Scheme.Hom.image_preimage_eq_opensRange_inf,
    Scheme.Opens.opensRange_ι]
  rfl

theorem local_twist_extension_ambient (L : LineBundle X)
    (s : structureSheaf X ⟶ L.sheaf) (U : X.Opens) [NoetherianSpace U.toScheme]
    (e : L.sheaf.restrict U.ι ≅ structureSheaf U.toScheme)
    (M : X.Modules) [M.IsQuasicoherent] (x : OpenSections M (sectionOpen X s)) :
    ∃ N : ℕ, ∀ n ≥ N, ∃ y : OpenSections ((moduleTwistFunctor L n).obj M) U,
      openRestriction ((moduleTwistFunctor L n).obj M)
        (show U ⊓ sectionOpen X s ≤ U from inf_le_left) y =
      mapSection ((moduleTwistSection L s n).app M) (U ⊓ sectionOpen X s)
        (openRestriction M inf_le_right x) := by
  let V := U.toScheme.basicOpen (coefficient e (restrictSection U.ι s))
  let W := U.ι ''ᵁ V
  have hWU : W ≤ U := U.ι_image_le V
  have hW : W = U ⊓ sectionOpen X s := section_open_image s U e
  have hWD : W ≤ sectionOpen X s := hW.le.trans inf_le_right
  let x0 : Γ(M.restrict U.ι,V) := M.presheaf.map (homOfLE hWD).op x
  obtain ⟨N, hN⟩ := local_twist_extension_section L s U e M x0
  refine ⟨N, fun n hn => ?_⟩
  obtain ⟨z, hz⟩ := hN n hn
  let P := (moduleTwistFunctor L n).obj M
  let z0 : OpenSections P (U.ι ''ᵁ ⊤) := z
  let y : OpenSections P U := openSectionsCongr P U.ι_image_top z0
  refine ⟨y, ?_⟩
  have ht := openSectionsCongr_naturality P (rfl : W = W) U.ι_image_top
    (U.ι.image_mono (show V ≤ ⊤ from le_top)) hWU z0
  have hres : openRestriction P hWU y =
      mapSection ((moduleTwistSection L s n).app M) W (openRestriction M hWD x) := by
    exact ht.symm.trans hz
  have hh := congrArg (openSectionsCongr P hW) hres
  rw [openSectionsCongr_naturality P hW rfl hWU inf_le_left, mapSection_congr] at hh
  change openRestriction P (show U ⊓ sectionOpen X s ≤ U from inf_le_left) y =
    mapSection ((moduleTwistSection L s n).app M) (U ⊓ sectionOpen X s)
      (openSectionsCongr M hW (openRestriction M hWD x)) at hh
  rw [openSectionsCongr_naturality M hW rfl hWD inf_le_right] at hh
  exact hh

theorem finite_local_twist_extensions [NoetherianSpace X] (L : LineBundle X)
    (s : structureSheaf X ⟶ L.sheaf) (M : X.Modules) [M.IsQuasicoherent]
    {ι : Type*} [Fintype ι] (U : ι → X.Opens)
    (e : ∀ i, L.sheaf.restrict (U i).ι ≅ structureSheaf (U i).toScheme)
    (x : OpenSections M (sectionOpen X s)) :
    ∃ N : ℕ, ∃ y : ∀ i, OpenSections ((moduleTwistFunctor L N).obj M) (U i),
      ∀ i, openRestriction ((moduleTwistFunctor L N).obj M)
        (show U i ⊓ sectionOpen X s ≤ U i from inf_le_left) (y i) =
      mapSection ((moduleTwistSection L s N).app M) (U i ⊓ sectionOpen X s)
        (openRestriction M inf_le_right x) := by
  classical
  have H (i : ι) := by
    letI : NoetherianSpace (U i).toScheme := NoetherianSpace.set (U i : Set X)
    exact local_twist_extension_ambient L s (U i) (e i) M x
  choose N hN using H
  let m := Finset.univ.sup N
  choose y hy using fun i => hN i m (Finset.le_sup (f := N) (Finset.mem_univ i))
  exact ⟨m, y, hy⟩

lemma mapSection_twistSection_add (L : LineBundle X) (s : structureSheaf X ⟶ L.sheaf)
    (M : X.Modules) (D : X.Opens) (x : OpenSections M D) (n k : ℕ) :
    mapSection ((moduleTwistForward L s n k).app M) D
      (mapSection ((moduleTwistSection L s n).app M) D x) =
    mapSection ((moduleTwistSection L s (n+k)).app M) D x := by
  exact congrArg (fun t => mapSection (t.app M) D x) (moduleTwistSection_add L s n k).symm

theorem finite_cover_twist_gluing [NoetherianSpace X] (L : LineBundle X)
    (s : structureSheaf X ⟶ L.sheaf) (M : X.Modules) [M.IsQuasicoherent]
    {ι : Type*} [Fintype ι] (U : ι → X.Opens) (hcover : (⨆ i, U i) = ⊤)
    (x : OpenSections M (sectionOpen X s)) (N : ℕ)
    (y : ∀ i, OpenSections ((moduleTwistFunctor L N).obj M) (U i))
    (hy : ∀ i, openRestriction ((moduleTwistFunctor L N).obj M)
        (show U i ⊓ sectionOpen X s ≤ U i from inf_le_left) (y i) =
      mapSection ((moduleTwistSection L s N).app M) (U i ⊓ sectionOpen X s)
        (openRestriction M inf_le_right x)) :
    ∃ K : ℕ, ∃ z : OpenSections ((moduleTwistFunctor L (N+K)).obj M) ⊤,
      openRestriction ((moduleTwistFunctor L (N+K)).obj M)
        (show sectionOpen X s ≤ ⊤ from le_top) z =
      mapSection ((moduleTwistSection L s (N+K)).app M) (sectionOpen X s) x := by
  classical
  let P := (moduleTwistFunctor L N).obj M
  let a := mapSection ((moduleTwistSection L s N).app M) (sectionOpen X s) x
  have hya (i : ι) : openRestriction P (show U i ⊓ sectionOpen X s ≤ U i from inf_le_left) (y i) =
      openRestriction P inf_le_right a :=
    (hy i).trans (mapSection_naturality ((moduleTwistSection L s N).app M) inf_le_right x)
  let diff (ij : ι × ι) := openRestriction P (show U ij.1 ⊓ U ij.2 ≤ U ij.1 from inf_le_left) (y ij.1) -
    openRestriction P (show U ij.1 ⊓ U ij.2 ≤ U ij.2 from inf_le_right) (y ij.2)
  have H (ij : ι × ι) :=
    PiExponent.TwistSectionClearing.twistForward_section_zero L s M N (U ij.1 ⊓ U ij.2)
      (diff ij) (overlap_difference_zero U (sectionOpen X s) a y hya ij.1 ij.2)
  choose K hK using H
  let k := Finset.univ.sup K
  have hcompat (i j : ι) :
      mapSection ((moduleTwistForward L s N k).app M) (U i ⊓ U j)
        (openRestriction P inf_le_left (y i)) =
      mapSection ((moduleTwistForward L s N k).app M) (U i ⊓ U j)
        (openRestriction P inf_le_right (y j)) := by
    have h := hK (i,j) k (Finset.le_sup (f := K) (Finset.mem_univ (i,j)))
    change mapSection ((moduleTwistForward L s N k).app M) (U i ⊓ U j)
      (openRestriction P inf_le_left (y i) - openRestriction P inf_le_right (y j)) = 0 at h
    rwa [map_sub, sub_eq_zero] at h
  obtain ⟨z, hz⟩ := glue_after_map ((moduleTwistForward L s N k).app M) U hcover y hcompat
  refine ⟨k, z, ?_⟩
  exact (restriction_of_glued_map ((moduleTwistForward L s N k).app M) U hcover
    (sectionOpen X s) a y hya z hz).trans (mapSection_twistSection_add L s M _ x N k)

theorem exists_global_twist_extension [NoetherianSpace X] (L : LineBundle X)
    (s : structureSheaf X ⟶ L.sheaf) (M : X.Modules) [M.IsQuasicoherent]
    (x : OpenSections M (sectionOpen X s)) :
    ∃ N : ℕ, ∃ z : OpenSections ((moduleTwistFunctor L N).obj M) ⊤,
      openRestriction ((moduleTwistFunctor L N).obj M)
        (show sectionOpen X s ≤ ⊤ from le_top) z =
      mapSection ((moduleTwistSection L s N).app M) (sectionOpen X s) x := by
  classical
  choose U hUx he using L.locallyRankOne
  obtain ⟨I, hI⟩ := isCompact_univ.elim_finite_subcover
    (fun x => (U x : Set X)) (fun x => (U x).isOpen)
    (by intro x _; exact Set.mem_iUnion.mpr ⟨x, hUx x⟩)
  have hcover : (⨆ i : I, U i.val) = ⊤ := by
    apply le_antisymm le_top
    intro x hx
    obtain ⟨i, hi⟩ := Set.mem_iUnion.mp (hI hx)
    obtain ⟨hi, hxU⟩ := Set.mem_iUnion.mp hi
    exact Opens.mem_iSup.mpr ⟨⟨i, hi⟩, hxU⟩
  let e (i : I) := Classical.choice (he i.val)
  obtain ⟨N, y, hy⟩ := finite_local_twist_extensions L s M (fun i : I => U i.val) e x
  obtain ⟨K, z, hz⟩ := finite_cover_twist_gluing L s M (fun i : I => U i.val) hcover x N y hy
  exact ⟨N+K, z, hz⟩

theorem global_twist_extension [NoetherianSpace X] (L : LineBundle X)
    (s : structureSheaf X ⟶ L.sheaf) (M : X.Modules) [M.IsQuasicoherent]
    (x : OpenSections M (sectionOpen X s)) :
    ∃ N : ℕ, ∀ n ≥ N, ∃ z : OpenSections ((moduleTwistFunctor L n).obj M) ⊤,
      openRestriction ((moduleTwistFunctor L n).obj M)
        (show sectionOpen X s ≤ ⊤ from le_top) z =
      mapSection ((moduleTwistSection L s n).app M) (sectionOpen X s) x := by
  obtain ⟨N, z, hz⟩ := exists_global_twist_extension L s M x
  refine ⟨N, fun n hn => ?_⟩
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hn
  refine ⟨mapSection ((moduleTwistForward L s N k).app M) ⊤ z, ?_⟩
  rw [← mapSection_naturality, hz]
  exact mapSection_twistSection_add L s M _ x N k

theorem global_twist_extension_native [NoetherianSpace X] (L : LineBundle X)
    (s : structureSheaf X ⟶ L.sheaf) (M : X.Modules) [M.IsQuasicoherent]
    (x : Γ(M,sectionOpen X s)) :
    ∃ N : ℕ, ∀ n ≥ N, ∃ z : Γ((moduleTwistFunctor L n).obj M,⊤),
      ((moduleTwistFunctor L n).obj M).presheaf.map
        (homOfLE (show sectionOpen X s ≤ ⊤ from le_top)).op z =
      ((moduleTwistSection L s n).app M).app (sectionOpen X s) x :=
  global_twist_extension L s M x

end
end PiExponent.TwistGlobalExtension

end OAI
end Source0456

-- Source: OAI/NumberTheory/PiExponent/Ampleness/AmpleGlobalGeneration.lean
section Source0457
-- Modified in this edition: unused plain lemmas removed; see reduction.json.
/-
Modification notice for the LogTwo project.
Derived from openai/math (Apache-2.0), revision adc7f1241b42e322a6451854ab7e4b4c146bf78a.
Original source: lean/OAI/NumberTheory/PiExponent/Ampleness/AmpleGlobalGeneration.lean
Changes: Convert module/import declarations to the Lean 4.34 public module format.
See ../THIRD_PARTY_NOTICES.txt for provenance and the recorded changes.
-/

namespace OAI

namespace PiExponent.AmpleGlobalGeneration
noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite
open PiExponentSeshadri.Geometry PiExponentSeshadri.Frames
open PiExponent.CoherentAffineFinite
variable {X : Scheme.{0}}

theorem sectionMultiply_isIso_restrict (M : X.Modules) {L : X.Modules}
    (s : structureSheaf X ⟶ L) (U : X.Opens)
    [IsIso ((Scheme.Modules.restrictFunctor U.ι).map s)] :
    IsIso ((Scheme.Modules.restrictFunctor U.ι).map (moduleSectionMultiplyRight M s)) := by
  let R := Scheme.Modules.restrictFunctor U.ι
  have h : IsIso (R.map (moduleTensorMap (𝟙 M) s)) := by
    apply (isIso_comp_right_iff _ (moduleTensorRestrict U M L).hom).mp
    rw [moduleTensorRestrict_natural]
    infer_instance
  change IsIso (R.map ((moduleTensorRightUnit M).inv ≫ moduleTensorMap (𝟙 M) s))
  rw [Functor.map_comp]
  infer_instance

theorem twistSection_isIso_restrict (L : LineBundle X)
    (s : structureSheaf X ⟶ L.sheaf) (M : X.Modules) (n : ℕ) :
    IsIso ((Scheme.Modules.restrictFunctor (sectionOpen X s).ι).map
      ((moduleTwistSection L s n).app M)) := by
  have : IsIso ((Scheme.Modules.restrictFunctor (sectionOpen X s).ι).map s) :=
    PiExponentSeshadri.SectionOpens.isIso_restrict_isoOpen s
  induction n with
  | zero => change IsIso ((Scheme.Modules.restrictFunctor (sectionOpen X s).ι).map (𝟙 M)); infer_instance
  | succ n ih =>
    change IsIso ((Scheme.Modules.restrictFunctor (sectionOpen X s).ι).map
      (((moduleTwistSection L s n).app M) ≫
        moduleSectionMultiplyRight ((moduleTwistFunctor L n).obj M) s))
    rw [Functor.map_comp]
    have := sectionMultiply_isIso_restrict ((moduleTwistFunctor L n).obj M) s (sectionOpen X s)
    infer_instance

lemma openSectionEquiv_restrict_from_top (M : X.Modules) (U : X.Opens)
    (z : Γ(M,⊤)) :
    openSectionEquiv M U (restrictSection U.ι ((moduleSectionEquiv M).symm z)) =
      M.presheaf.map (homOfLE (show U ≤ ⊤ from le_top)).op z := by
  rw [openSectionEquiv_restrict]
  have h := section_value_natural ((moduleSectionEquiv M).symm z)
    (homOfLE (show U ≤ ⊤ from le_top))
  rw [← moduleSectionEquiv_apply, Equiv.apply_symm_apply] at h
  exact h.symm

lemma openSectionEquiv_postcomp {M N : X.Modules} (f : M ⟶ N) (U : X.Opens)
    (a : structureSheaf U.toScheme ⟶ M.restrict U.ι) :
    openSectionEquiv N U (a ≫ (Scheme.Modules.restrictFunctor U.ι).map f) =
      f.app U (openSectionEquiv M U a) := by
  change N.presheaf.map (eqToHom U.ι_image_top.symm).op
    (f.app (U.ι ''ᵁ ⊤) (a.app ⊤ (1 : Γ(U.toScheme,⊤)))) =
    f.app U (M.presheaf.map (eqToHom U.ι_image_top.symm).op
      (a.app ⊤ (1 : Γ(U.toScheme,⊤))))
  exact (congr($(f.mapPresheaf.naturality (eqToHom U.ι_image_top.symm).op)
    (a.app ⊤ (1 : Γ(U.toScheme,⊤))))).symm

theorem affine_local_generators (M : X.Modules) [M.IsFinitePresentation]
    (U : X.Opens) (hU : IsAffineOpen U) :
    ∃ σ : (M.restrict U.ι).GeneratingSections, σ.IsFiniteType := by
  have : IsAffine U.toScheme := hU
  let : M.IsQuasicoherent :=
    (SheafOfModules.IsFinitePresentation.exists_quasicoherentData M).choose.isQuasicoherent
  have := affine_sections_finite_of_localGenerators (M.restrict U.ι)
    ((locallyFinitelyGenerated_of_finitePresentation M).restrict U.ι)
  exact affine_exists_finite_generators (M.restrict U.ι)

theorem eventual_global_generators_of_section_cover [NoetherianSpace X]
    (L : LineBundle X) (M : X.Modules) [M.IsFinitePresentation]
    {ι : Type} [Finite ι] (s : ι → (structureSheaf X ⟶ L.sheaf))
    (hcover : (⨆ i, sectionOpen X (s i)) = ⊤)
    (haffine : ∀ i, IsAffineOpen (sectionOpen X (s i))) :
    ∃ N : ℕ, ∀ n ≥ N,
      ∃ G : ((moduleTwistFunctor L n).obj M).GeneratingSections, G.IsFiniteType := by
  classical
  let : M.IsQuasicoherent :=
    (SheafOfModules.IsFinitePresentation.exists_quasicoherentData M).choose.isQuasicoherent
  let U (i : ι) := sectionOpen X (s i)
  choose σ hσ using fun i => affine_local_generators M (U i) (haffine i)
  let (i : ι) : (σ i).IsFiniteType := hσ i
  let (i : ι) : Finite (σ i).I := (hσ i).finite
  let a (i : ι) (j : (σ i).I) :=
    (M.restrict (U i).ι).unitHomEquiv.symm ((σ i).s j)
  let x (i : ι) (j : (σ i).I) : Γ(M,U i) := openSectionEquiv M (U i) (a i j)
  choose d hd using fun ij : Σ i, (σ i).I =>
    PiExponent.TwistGlobalExtension.global_twist_extension_native L (s ij.1) M (x ij.1 ij.2)
  let : Fintype (Σ i, (σ i).I) := Fintype.ofFinite _
  let N := Finset.univ.sup d
  refine ⟨N, fun n hn => ?_⟩
  let Q := (moduleTwistFunctor L n).obj M
  have hn' (ij : Σ i, (σ i).I) : d ij ≤ n :=
    (Finset.le_sup (f := d) (Finset.mem_univ ij)).trans hn
  choose z hz using fun ij : Σ i, (σ i).I => hd ij n (hn' ij)
  let f (i : ι) : M.restrict (U i).ι ⟶ Q.restrict (U i).ι :=
    (Scheme.Modules.restrictFunctor (U i).ι).map ((moduleTwistSection L (s i) n).app M)
  have hf (i : ι) : IsIso (f i) := twistSection_isIso_restrict L (s i) M n
  let τ (i : ι) : (Q.restrict (U i).ι).GeneratingSections :=
    SheafOfModules.GeneratingSections.equivOfIso
      (@asIso _ _ _ _ (f i) (hf i)) (σ i)
  let (i : ι) : (τ i).IsFiniteType := ⟨(hσ i).finite⟩
  let t (i : ι) (j : (τ i).I) : GlobalSections X Q :=
    (moduleSectionEquiv Q).symm (z ⟨i,j⟩)
  have ht (i : ι) (j : (τ i).I) : restrictSection (U i).ι (t i j) =
      (Q.restrict (U i).ι).unitHomEquiv.symm ((τ i).s j) := by
    apply (openSectionEquiv Q (U i)).injective
    change openSectionEquiv Q (U i)
      (restrictSection (U i).ι ((moduleSectionEquiv Q).symm (z ⟨i,j⟩))) =
      openSectionEquiv Q (U i) ((Q.restrict (U i).ι).unitHomEquiv.symm
        (SheafOfModules.sectionsMap (f i) ((σ i).s j)))
    erw [openSectionEquiv_restrict_from_top, ← SheafOfModules.unitHomEquiv_symm_comp]
    erw [openSectionEquiv_postcomp]
    exact hz ⟨i,j⟩
  exact PiExponent.GlueGlobalGenerators.exists_finite_global_generators Q U hcover τ t ht

end
end PiExponent.AmpleGlobalGeneration

end OAI
end Source0457

-- Source: OAI/NumberTheory/PiExponent/Geometry/SheafificationUnitIso.lean
section Source0458
-- Modified in this edition: unused plain lemmas removed; see reduction.json.
/-
Modification notice for the LogTwo project.
Derived from openai/math (Apache-2.0), revision adc7f1241b42e322a6451854ab7e4b4c146bf78a.
Original source: lean/OAI/NumberTheory/PiExponent/Geometry/SheafificationUnitIso.lean
Changes: Convert module/import declarations to the Lean 4.34 public module format.
See ../THIRD_PARTY_NOTICES.txt for provenance and the recorded changes.
-/

namespace OAI

namespace PiExponentSeshadri.Geometry
noncomputable section
open AlgebraicGeometry CategoryTheory
variable {X : Scheme}

theorem sheafification_unit_isIso_of_iso (P : PresheafOfModules X.ringCatSheaf.obj)
    (M : X.Modules) (e : P ≅ M.val) :
    IsIso ((PiExponentSeshadri.TensorPure.adj X).unit.app P) :=
  (PiExponentSeshadri.TensorPure.adj X).isIso_unit_app_of_iso e

end
end PiExponentSeshadri.Geometry

end OAI
end Source0458

-- Source: OAI/NumberTheory/PiExponent/Approximation/ModuleLinePowerLaws.lean
section Source0459
/-
Modification notice for the LogTwo project.
Derived from openai/math (Apache-2.0), revision adc7f1241b42e322a6451854ab7e4b4c146bf78a.
Original source: lean/OAI/NumberTheory/PiExponent/Approximation/ModuleLinePowerLaws.lean
Changes: Convert module/import declarations to the Lean 4.34 public module format.
See ../THIRD_PARTY_NOTICES.txt for provenance and the recorded changes.
-/

namespace OAI

namespace PiExponentSeshadri.Geometry
noncomputable section
open CategoryTheory AlgebraicGeometry TopologicalSpace MonoidalCategory
open PiExponentSeshadri.TensorPure
variable {X : Scheme}

def lineTensorPresheafRestrictFrame (L : LineBundle X) (N : X.Modules)
    (U : X.Opens) (e : L.sheaf.restrict U.ι ≅ structureSheaf U.toScheme) :
    (modulePresheafRestrict U.ι).obj
      (PresheafOfModulesOfCommRing.Monoidal.tensorObj (R := X.presheaf) L.sheaf.val N.val) ≅
        (N.restrict U.ι).val := by
  let : MonoidalCategory (PresheafOfModules U.toScheme.ringCatSheaf.obj) :=
    PresheafOfModulesOfCommRing.monoidalCategory (R := U.toScheme.presheaf)
  let ep : (modulePresheafRestrict U.ι).obj L.sheaf.val ≅
      𝟙_ (PresheafOfModules U.toScheme.ringCatSheaf.obj) :=
    (SheafOfModules.forget _).mapIso e
  exact modulePresheafTensorRestrict U L.sheaf.val N.val ≪≫
    tensorIso ep (Iso.refl _) ≪≫ λ_ _

lemma lineTensorPresheaf_unit_restrict_isIso (L : LineBundle X) (N : X.Modules)
    (U : X.Opens) (e : L.sheaf.restrict U.ι ≅ structureSheaf U.toScheme) :
    IsIso ((modulePresheafRestrict U.ι).map
      ((adj X).unit.app
        (PresheafOfModulesOfCommRing.Monoidal.tensorObj (R := X.presheaf) L.sheaf.val N.val))) := by
  let P := PresheafOfModulesOfCommRing.Monoidal.tensorObj (R := X.presheaf) L.sheaf.val N.val
  let R : PresheafOfModules X.ringCatSheaf.obj ⥤
      PresheafOfModules U.toScheme.ringCatSheaf.obj := modulePresheafRestrict U.ι
  have hη : IsIso ((adj U.toScheme).unit.app (R.obj P)) :=
    sheafification_unit_isIso_of_iso (R.obj P) (N.restrict U.ι)
      (lineTensorPresheafRestrictFrame L N U e)
  have hh : IsIso (R.map ((adj X).unit.app P) ≫
      ((moduleSheafificationRestrict U.ι).hom.app P).val) := by
    erw [sheafify_restrict_unit]
    exact hη
  let V : U.toScheme.Modules ⥤ PresheafOfModules U.toScheme.ringCatSheaf.obj :=
    SheafOfModules.forget U.toScheme.ringCatSheaf
  let hv : IsIso (C := PresheafOfModules U.toScheme.ringCatSheaf.obj)
      (((moduleSheafificationRestrict U.ι).hom.app P).val) :=
    (V.mapIso ((moduleSheafificationRestrict U.ι).app P)).isIso_hom
  exact (@isIso_comp_right_iff (PresheafOfModules U.toScheme.ringCatSheaf.obj)
    _ _ _ _ _ _ hv).mp hh

lemma sheafification_tensor_left_line_unit_isIso (M : X.Modules) (L : LineBundle X)
    (N : X.Modules) :
    IsIso ((PresheafOfModules.sheafification (𝟙 X.ringCatSheaf.obj)).map
      (PresheafOfModulesOfCommRing.Monoidal.tensorHom (R := X.presheaf) (𝟙 M.val)
        ((adj X).unit.app
          (PresheafOfModulesOfCommRing.Monoidal.tensorObj (R := X.presheaf) L.sheaf.val N.val)))) := by
  let P := PresheafOfModulesOfCommRing.Monoidal.tensorObj (R := X.presheaf) L.sheaf.val N.val
  let F : PresheafOfModules X.ringCatSheaf.obj ⥤ X.Modules :=
    PresheafOfModules.sheafification (𝟙 X.ringCatSheaf.obj)
  let η := (adj X).unit.app P
  let Q := (F ⋙ SheafOfModules.forget X.ringCatSheaf ⋙
    PresheafOfModules.restrictScalars (𝟙 X.ringCatSheaf.obj)).obj P
  let g := PresheafOfModulesOfCommRing.Monoidal.tensorHom (R := X.presheaf) (𝟙 M.val) η
  apply PiExponent.NumericalAmpleness.isIso_of_locally_isIso
  intro x
  obtain ⟨U,hx,⟨e⟩⟩ := L.locallyRankOne x
  refine ⟨U,hx,?_⟩
  let R : PresheafOfModules X.ringCatSheaf.obj ⥤
      PresheafOfModules U.toScheme.ringCatSheaf.obj := modulePresheafRestrict U.ι
  let S : PresheafOfModules U.toScheme.ringCatSheaf.obj ⥤ U.toScheme.Modules :=
    PresheafOfModules.sheafification (𝟙 U.toScheme.ringCatSheaf.obj)
  let : MonoidalCategory (PresheafOfModules U.toScheme.ringCatSheaf.obj) :=
    PresheafOfModulesOfCommRing.monoidalCategory (R := U.toScheme.presheaf)
  have : IsIso (R.map η) := lineTensorPresheaf_unit_restrict_isIso L N U e
  apply (NatIso.isIso_map_iff (moduleSheafificationRestrict U.ι) g).mpr
  change IsIso (S.map (R.map g))
  have heq := modulePresheafTensorRestrict_natural U (𝟙 M.val) η
  let : IsIso (S.map (modulePresheafTensorRestrict U M.val P).hom) :=
    (S.mapIso (modulePresheafTensorRestrict U M.val P)).isIso_hom
  let : IsIso (S.map (modulePresheafTensorRestrict U M.val Q).hom) :=
    (S.mapIso (modulePresheafTensorRestrict U M.val Q)).isIso_hom
  have hcomp : IsIso (S.map (R.map g ≫
      (modulePresheafTensorRestrict U M.val Q).hom)) := by
    erw [heq, S.map_comp]
    have ht : IsIso (S.map
      (PresheafOfModulesOfCommRing.Monoidal.tensorHom (R := U.toScheme.presheaf)
        (R.map (𝟙 M.val)) (R.map η))) := by
      rw [R.map_id]
      change IsIso (S.map ((𝟙 (R.obj M.val)) ⊗ₘ (R.map η)))
      infer_instance
    exact (inferInstance : IsIso (C := U.toScheme.Modules)
      (S.map (modulePresheafTensorRestrict U M.val P).hom ≫ S.map
        (PresheafOfModulesOfCommRing.Monoidal.tensorHom (R := U.toScheme.presheaf)
          (R.map (𝟙 M.val)) (R.map η))))
  erw [S.map_comp] at hcomp
  exact (isIso_comp_right_iff (C := U.toScheme.Modules) _ _).mp hcomp

def sheafificationTensorLeftLinePair (M : X.Modules) (L N : LineBundle X) :
    (PresheafOfModules.sheafification (𝟙 X.ringCatSheaf.obj)).obj
      (PresheafOfModulesOfCommRing.Monoidal.tensorObj (R := X.presheaf) M.val
        (PresheafOfModulesOfCommRing.Monoidal.tensorObj (R := X.presheaf) L.sheaf.val N.sheaf.val)) ≅
    moduleTensor X M (moduleTensor X L.sheaf N.sheaf) := by
  let P := PresheafOfModulesOfCommRing.Monoidal.tensorObj (R := X.presheaf) L.sheaf.val N.sheaf.val
  let F := PresheafOfModules.sheafification (𝟙 X.ringCatSheaf.obj)
  let η := (adj X).unit.app P
  let ht : IsIso (F.map (PresheafOfModulesOfCommRing.Monoidal.tensorHom
      (R := X.presheaf) (𝟙 M.val) η)) := sheafification_tensor_left_line_unit_isIso M L N.sheaf
  exact @asIso _ _ _ _ (F.map (PresheafOfModulesOfCommRing.Monoidal.tensorHom (R := X.presheaf)
    (𝟙 M.val) η)) ht

def moduleLineTensorAssoc (M : X.Modules) (L N : LineBundle X) :
    moduleTensor X (moduleTensor X M L.sheaf) N.sheaf ≅
      moduleTensor X M (moduleTensor X L.sheaf N.sheaf) := by
  let : MonoidalCategory (PresheafOfModules X.ringCatSheaf.obj) :=
    PresheafOfModulesOfCommRing.monoidalCategory (R := X.presheaf)
  exact (sheafificationTensorRight (M.val ⊗ L.sheaf.val) N).symm ≪≫
    (PresheafOfModules.sheafification (𝟙 X.ringCatSheaf.obj)).mapIso
      (α_ M.val L.sheaf.val N.sheaf.val) ≪≫
    sheafificationTensorLeftLinePair M L N

def moduleTwistPowerIso (L : LineBundle X) (M : X.Modules) : ∀ n : ℕ,
    (moduleTwistFunctor L n).obj M ≅ moduleTensor X M (modulePow X L.sheaf n)
  | 0 => (moduleTensorRightUnit M).symm
  | n+1 => moduleTensorIso (moduleTwistPowerIso L M n) (Iso.refl L.sheaf) ≪≫
      moduleLineTensorAssoc M (L.pow n) L ≪≫
      moduleTensorIso (Iso.refl M) (moduleTensorComm (modulePow X L.sheaf n) L.sheaf)

def moduleTwistPowerMulIso (L : LineBundle X) (M : X.Modules) (d n : ℕ) :
    (moduleTwistFunctor (L.pow d) n).obj M ≅ (moduleTwistFunctor L (d*n)).obj M :=
  moduleTwistPowerIso (L.pow d) M n ≪≫
    moduleTensorIso (Iso.refl M) (linePowerMul L d n) ≪≫
      (moduleTwistPowerIso L M (d*n)).symm

end
end PiExponentSeshadri.Geometry

end OAI
end Source0459

-- Source: OAI/NumberTheory/PiExponent/Geometry/CurveEffectiveTwist.lean
section Source0460
/-
Modification notice for the LogTwo project.
Derived from openai/math (Apache-2.0), revision adc7f1241b42e322a6451854ab7e4b4c146bf78a.
Original source: lean/OAI/NumberTheory/PiExponent/Geometry/CurveEffectiveTwist.lean
Changes: Convert module/import declarations to the Lean 4.34 public module format.
See ../THIRD_PARTY_NOTICES.txt for provenance and the recorded changes.
-/

namespace OAI

namespace PiExponent.CurveDegree
noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace
open PiExponentSeshadri.Geometry PiExponentSeshadri.Frames PiExponentSeshadri.SectionOpens
variable {X : Scheme.{0}} [IsIntegral X]

private theorem id_eq_zero_of_iso {C : Type*} [Category C] [Preadditive C]
    {A B : C} (e : A ≅ B) (h : 𝟙 A = 0) : 𝟙 B = 0 := by
  have he := congrArg (fun f : A ⟶ A => e.inv ≫ f ≫ e.hom) h
  simpa only [Category.id_comp, comp_zero, zero_comp, Iso.inv_hom_id] using he

private theorem generators_isZero {T : TopCat.{0}} (R : Sheaf (Opens.grothendieckTopology T) RingCat.{0})
    (M : SheafOfModules.{0} R) (G : M.GeneratingSections)
    (h : ∀ s : SheafOfModules.unit.{0} R ⟶ M, s = 0) : IsZero M := by
  have hπ : G.π = 0 := by
    apply M.freeHomEquiv.injective
    funext i
    apply M.unitHomEquiv.symm.injective
    rw [SheafOfModules.unitHomEquiv_symm_freeHomEquiv_apply,
      SheafOfModules.unitHomEquiv_symm_freeHomEquiv_apply]
    simpa only [comp_zero] using h (SheafOfModules.ιFree i ≫ G.π)
  let : Epi G.π := G.epi
  exact IsZero.of_epi_eq_zero G.π hπ

theorem lineBundle_not_isZero (L : LineBundle X) : ¬ IsZero L.sheaf := by
  intro h
  obtain ⟨x⟩ : Nonempty X := inferInstance
  obtain ⟨U, hx, ⟨e⟩⟩ := L.locallyRankOne x
  let : Nonempty U := ⟨⟨x, hx⟩⟩
  let : IsIntegral U.toScheme := isIntegral_of_isOpenImmersion U.ι
  have hL : (𝟙 L.sheaf) = 0 := h.eq_of_src _ _
  have hr := congrArg (Scheme.Modules.restrictFunctor U.ι).map hL
  rw [CategoryTheory.Functor.map_id, CategoryTheory.Functor.map_zero] at hr
  have hid : (𝟙 (O U.toScheme)) = 0 := by
    simpa only [O] using! id_eq_zero_of_iso e hr
  have hh := congrArg (endValue (X := U.toScheme)) hid
  simp only [endValue] at hh
  exact one_ne_zero (show (1 : Γ(U.toScheme, ⊤)) = 0 from hh)

omit [IsIntegral X] in

theorem section_ne_zero_of_mem_isoOpen (L : LineBundle X) (s : O X ⟶ L.sheaf)
    (x : X) (hx : x ∈ isoOpen s) : s ≠ 0 := by
  obtain ⟨U, hxU, ⟨e⟩⟩ := L.locallyRankOne x
  have hm : (⟨x, hxU⟩ : U.toScheme) ∈ U.ι ⁻¹ᵁ isoOpen s := hx
  rw [preimage_isoOpen s U.ι e] at hm
  intro hz
  subst s
  have hrestrict : restrictSection U.ι (0 : O X ⟶ L.sheaf) = 0 := by
    simpa only [restrictSection] using restrictSection_zero (M := L.sheaf) U.ι
  have hz := (congrArg (coefficient e) hrestrict).trans (coefficient_zero e)
  erw [hz, Scheme.basicOpen_zero] at hm
  exact hm

theorem nonzero_section_of_generators (L : LineBundle X) (G : L.sheaf.GeneratingSections) :
    ∃ s : GlobalSections X L.sheaf, s ≠ 0 := by
  classical
  by_contra h
  push Not at h
  exact lineBundle_not_isZero L (generators_isZero X.ringCatSheaf L.sheaf G h)

def twistLineIso (H L : LineBundle X) (n : ℕ) :
    (moduleTwistFunctor H n).obj L.sheaf ≅ ((H.pow n).tensor L).sheaf :=
  moduleTwistPowerIso H L.sheaf n ≪≫
    moduleTensorComm L.sheaf (modulePow X H.sheaf n)

theorem exists_effective_twist [NoetherianSpace X]
    (H : LineBundle X) (hH : H.IsAmple) (L : LineBundle X) :
    ∃ A : LineBundle X,
      (∃ t : GlobalSections X A.sheaf, t ≠ 0) ∧
      (∃ u : GlobalSections X (A.tensor L).sheaf, u ≠ 0) := by
  obtain ⟨d, hd, k, s, hcover, haffine, hcoverData⟩ := H.ample_common_degree_cover hH
  let := PiExponent.GeometrySupport.LineBundleCoherent.lineBundle_isFinitePresentation L
  obtain ⟨N, hN⟩ := AmpleGlobalGeneration.eventual_global_generators_of_section_cover
    (H.pow d) L.sheaf s hcover haffine
  obtain ⟨G, hG⟩ := hN N le_rfl
  let A := (H.pow d).pow N
  obtain ⟨x⟩ : Nonempty X := inferInstance
  have hx : x ∈ ⨆ i, sectionOpen X (s i) := by rw [hcover]; trivial
  obtain ⟨i, hi⟩ := Opens.mem_iSup.mp hx
  let t := powerSection (s i) N
  have ht : t ≠ 0 := section_ne_zero_of_mem_isoOpen A t x
    (sectionOpen_le_powerSection (s i) N hi)
  have hu := nonzero_section_of_generators (A.tensor L)
    (SheafOfModules.GeneratingSections.equivOfIso (twistLineIso (H.pow d) L N) G)
  exact ⟨A, ⟨t, ht⟩, hu⟩

end
end PiExponent.CurveDegree

end OAI
end Source0460

-- Source: OAI/NumberTheory/PiExponent/Approximation/InverseFrames.lean
section Source0461
/-
Modification notice for the LogTwo project.
Derived from openai/math (Apache-2.0), revision adc7f1241b42e322a6451854ab7e4b4c146bf78a.
Original source: lean/OAI/NumberTheory/PiExponent/Approximation/InverseFrames.lean
Changes: Convert module/import declarations to the Lean 4.34 public module format.
See ../THIRD_PARTY_NOTICES.txt for provenance and the recorded changes.
-/

namespace OAI

namespace PiExponent.InverseFrames
noncomputable section
open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite
open PiExponentSeshadri.Geometry PiExponentSeshadri.Frames PiExponentSeshadri.TensorPure
variable {X : Scheme.{0}} {M N : X.Modules}

def regularValue {P : X.Modules} (f : P ⟶ O X) (U : X.Opens)
    (x : P.val.obj (op U)) : Γ(X,U) := f.app U x

def pairingFrame (E : moduleTensor X M N ≅ O X) (e : M ≅ O X) : N ≅ O X :=
  (moduleTensorUnit N).symm ≪≫ moduleTensorIso e.symm (Iso.refl N) ≪≫ E

lemma unit_inv_pure (N : X.Modules) (U : X.Opens) (x : N.val.obj (op U)) :
    (moduleTensorUnit N).inv.app U x = PiExponentSeshadri.TensorPure.pure (O X) N U (1 : Γ(X,U)) x := by
  have h : (moduleTensorUnit N).hom.app U (PiExponentSeshadri.TensorPure.pure (O X) N U (1 : Γ(X,U)) x) = x := by
    change (moduleTensorUnit N).hom.app U
      (PiExponentSeshadri.TensorPure.pure (structureSheaf X) N U (1 : Γ(X,U)) x) = x
    exact (unit_pure N U (1 : Γ(X,U)) x).trans (one_smul Γ(X,U) (show Γ(N,U) from x))
  calc
    (moduleTensorUnit N).inv.app U x =
        (moduleTensorUnit N).inv.app U
          ((moduleTensorUnit N).hom.app U (PiExponentSeshadri.TensorPure.pure (O X) N U (1 : Γ(X,U)) x)) :=
      congrArg (fun z => (moduleTensorUnit N).inv.app U z) h.symm
    _ = _ := congrArg (fun f => f.app U (PiExponentSeshadri.TensorPure.pure (O X) N U (1 : Γ(X,U)) x))
      (moduleTensorUnit N).hom_inv_id

lemma pairingFrame_apply (E : moduleTensor X M N ≅ O X) (e : M ≅ O X)
    (U : X.Opens) (x : N.val.obj (op U)) :
    (pairingFrame E e).hom.app U x =
      E.hom.app U (PiExponentSeshadri.TensorPure.pure M N U (e.inv.app U (1 : Γ(X,U))) x) := by
  change E.hom.app U ((moduleTensorMap e.inv (𝟙 N)).app U
    ((moduleTensorUnit N).inv.app U x)) = _
  rw [unit_inv_pure]
  exact congrArg (fun z => E.hom.app U z)
    (PiExponentSeshadri.TensorPure.map_pure e.inv (𝟙 N) U (1 : Γ(X,U)) x)

lemma frame_generator_change (e f : M ≅ O X) :
    f.inv.app ⊤ (1 : Γ(X,⊤)) = (frameChange f e : Γ(X,⊤)) • e.inv.app ⊤ (1 : Γ(X,⊤)) := by
  have h := e.inv.app_smul (r := (frameChange f e : Γ(X,⊤)))
    (x := (1 : Γ(X,⊤)))
  change e.inv.app ⊤ ((frameChange f e : Γ(X,⊤)) * (1 : Γ(X,⊤)) : Γ(X,⊤)) = _ at h
  rw [mul_one] at h
  rw [← h]
  change f.inv.app ⊤ (1 : Γ(X,⊤)) = e.inv.app ⊤ (e.hom.app ⊤ (f.inv.app ⊤ (1 : Γ(X,⊤))))
  exact (congrArg (fun t => t.app ⊤ (f.inv.app ⊤ (1 : Γ(X,⊤)))) e.hom_inv_id).symm

lemma pairingFrame_change_apply (E : moduleTensor X M N ≅ O X)
    (e f : M ≅ O X) (x : N.val.obj (op (⊤ : X.Opens))) :
    regularValue (pairingFrame E f).hom ⊤ x =
      (frameChange f e : Γ(X,⊤)) * regularValue (pairingFrame E e).hom ⊤ x := by
  dsimp only [regularValue]
  have hf := pairingFrame_apply E f ⊤ x
  have he := pairingFrame_apply E e ⊤ x
  have hg := congrArg (fun m => E.hom.app ⊤ (PiExponentSeshadri.TensorPure.pure M N ⊤ m x))
    (frame_generator_change e f)
  have hs := congrArg (fun z => E.hom.app ⊤ z)
    (pure_smul_left M N ⊤ (frameChange f e : Γ(X,⊤)) (e.inv.app ⊤ (1 : Γ(X,⊤))) x)
  have hm := E.hom.app_smul (r := (frameChange f e : Γ(X,⊤)))
    (x := PiExponentSeshadri.TensorPure.pure M N ⊤ (e.inv.app ⊤ (1 : Γ(X,⊤))) x)
  exact hf.trans (hg.trans (hs.trans (hm.trans
    (congrArg (fun a : Γ(X,⊤) => (frameChange f e : Γ(X,⊤)) * a) he.symm))))

lemma pairingFrame_frameChange (E : moduleTensor X M N ≅ O X)
    (e f : M ≅ O X) :
    frameChange (pairingFrame E e) (pairingFrame E f) = frameChange f e := by
  apply Units.ext
  change (pairingFrame E f).hom.app ⊤ ((pairingFrame E e).inv.app ⊤ (1 : Γ(X,⊤))) = _
  change regularValue (pairingFrame E f).hom ⊤ ((pairingFrame E e).inv.app ⊤ (1 : Γ(X,⊤))) = _
  erw [pairingFrame_change_apply]
  have h := congrArg (fun t => t.app ⊤ (1 : Γ(X,⊤))) (pairingFrame E e).inv_hom_id
  change (pairingFrame E e).hom.app ⊤ ((pairingFrame E e).inv.app ⊤ (1 : Γ(X,⊤))) = (1 : Γ(X,⊤)) at h
  have hv : regularValue (pairingFrame E e).hom ⊤
      ((pairingFrame E e).inv.app ⊤ (1 : Γ(X,⊤))) = 1 := h
  rw [hv, mul_one]

lemma pairing_apply (E : moduleTensor X M N ≅ O X) (e : M ≅ O X)
    (U : X.Opens) (m : M.val.obj (op U)) (n : N.val.obj (op U)) :
    regularValue E.hom U (PiExponentSeshadri.TensorPure.pure M N U m n) =
      regularValue e.hom U m * regularValue (pairingFrame E e).hom U n := by
  have hm : m = (regularValue e.hom U m) • e.inv.app U (1 : Γ(X,U)) := by
    have h := e.inv.app_smul (r := (regularValue e.hom U m))
      (x := (1 : Γ(X,U)))
    change e.inv.app U (regularValue e.hom U m * (1 : Γ(X,U)) : Γ(X,U)) = _ at h
    rw [mul_one] at h
    rw [← h]
    exact (congrArg (fun t => t.app U m) e.hom_inv_id).symm
  calc
    regularValue E.hom U (PiExponentSeshadri.TensorPure.pure M N U m n) =
        regularValue E.hom U (PiExponentSeshadri.TensorPure.pure M N U ((regularValue e.hom U m) • e.inv.app U (1 : Γ(X,U))) n) :=
      congrArg (fun z => regularValue E.hom U (PiExponentSeshadri.TensorPure.pure M N U z n)) hm
    _ = (regularValue e.hom U m) * regularValue E.hom U (PiExponentSeshadri.TensorPure.pure M N U (e.inv.app U (1 : Γ(X,U))) n) := by
      erw [pure_smul_left]
      exact E.hom.app_smul _ _
    _ = _ := by
      dsimp only [regularValue]
      rw [pairingFrame_apply]

lemma pairing_inverse_generator (E : moduleTensor X M N ≅ O X) (e : M ≅ O X)
    (U : X.Opens) (m : M.val.obj (op U)) :
    E.hom.app U (PiExponentSeshadri.TensorPure.pure M N U m ((pairingFrame E e).inv.app U (1 : Γ(X,U)))) = e.hom.app U m := by
  change regularValue E.hom U _ = regularValue e.hom U m
  erw [pairing_apply]
  have h := congrArg (fun t => t.app U (1 : Γ(X,U))) (pairingFrame E e).inv_hom_id
  change (pairingFrame E e).hom.app U ((pairingFrame E e).inv.app U (1 : Γ(X,U))) = (1 : Γ(X,U)) at h
  have hv : regularValue (pairingFrame E e).hom U
      ((pairingFrame E e).inv.app U (1 : Γ(X,U))) = 1 := h
  rw [hv, mul_one]

def dualMap (E : moduleTensor X M N ≅ O X) (s : O X ⟶ M) : N ⟶ O X :=
  (moduleTensorUnit N).inv ≫ moduleTensorMap s (𝟙 N) ≫ E.hom

lemma dualMap_apply (E : moduleTensor X M N ≅ O X) (s : O X ⟶ M)
    (U : X.Opens) (n : N.val.obj (op U)) :
    (dualMap E s).app U n = E.hom.app U (PiExponentSeshadri.TensorPure.pure M N U (s.app U (1 : Γ(X,U))) n) := by
  change E.hom.app U ((moduleTensorMap s (𝟙 N)).app U
    ((moduleTensorUnit N).inv.app U n)) = _
  rw [unit_inv_pure]
  exact congrArg (fun z => E.hom.app U z)
    (PiExponentSeshadri.TensorPure.map_pure s (𝟙 N) U (1 : Γ(X,U)) n)

lemma dualMap_coefficient (E : moduleTensor X M N ≅ O X) (e : M ≅ O X)
    (s : O X ⟶ M) :
    endValue ((pairingFrame E e).inv ≫ dualMap E s) = coefficient e s := by
  change (dualMap E s).app ⊤ ((pairingFrame E e).inv.app ⊤ (1 : Γ(X,⊤))) = e.hom.app ⊤ (s.app ⊤ (1 : Γ(X,⊤)))
  exact (dualMap_apply E s ⊤ ((pairingFrame E e).inv.app ⊤ (1 : Γ(X,⊤)))).trans
    (pairing_inverse_generator E e ⊤ (s.app ⊤ (1 : Γ(X,⊤))))

def restrictPairing (E : moduleTensor X M N ≅ O X) (U : X.Opens) :
    moduleTensor U.toScheme (M.restrict U.ι) (N.restrict U.ι) ≅ O U.toScheme :=
  (moduleTensorRestrict U M N).symm ≪≫
    (Scheme.Modules.restrictFunctor U.ι).mapIso E ≪≫ Scheme.Modules.restrictUnitIso U.ι

def inverseOpenFrame (E : moduleTensor X M N ≅ O X) (U : X.Opens)
    (e : M.restrict U.ι ≅ O U.toScheme) : N.restrict U.ι ≅ O U.toScheme :=
  pairingFrame (restrictPairing E U) e

lemma inverseOpenFrame_frameChange (E : moduleTensor X M N ≅ O X) (U : X.Opens)
    (e f : M.restrict U.ι ≅ O U.toScheme) :
    frameChange (inverseOpenFrame E U e) (inverseOpenFrame E U f) = frameChange f e :=
  pairingFrame_frameChange (restrictPairing E U) e f

end
end PiExponent.InverseFrames

end OAI
end Source0461

-- Source: OAI/NumberTheory/PiExponent/Approximation/CocycleTensor.lean
section Source0462
/-
Modification notice for the LogTwo project.
Derived from openai/math (Apache-2.0), revision adc7f1241b42e322a6451854ab7e4b4c146bf78a.
Original source: lean/OAI/NumberTheory/PiExponent/Approximation/CocycleTensor.lean
Changes: Convert module/import declarations to the Lean 4.34 public module format.
See ../THIRD_PARTY_NOTICES.txt for provenance and the recorded changes.
-/

namespace OAI

noncomputable section

namespace PiExponentSeshadri.LineBundleGluing
open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite MonoidalCategory
open PiExponentSeshadri.Geometry PiExponentSeshadri.TensorPure
variable {X : Scheme} {ι : Type} {U : ι → X.Opens}

def Cocycle.one : Cocycle U where
  transition _ _ _ _ _ := 1
  restriction _ _ _ _ _ := by simp
  identity _ _ _ := rfl
  cocycle _ _ _ _ _ _ _ := one_mul _

def Cocycle.inverse (c : Cocycle U) : Cocycle U where
  transition i j W hi hj := (c.transition i j W hi hj)⁻¹
  restriction := by
    intro i j V W h hi hj
    have h' : restrictUnit h (c.transition i j _ hi hj) =
        c.transition i j _ (h.trans hi) (h.trans hj) := Units.ext (c.restriction i j h hi hj)
    exact congrArg Units.val ((map_inv (restrictUnit h) _).symm.trans (congrArg Inv.inv h'))
  identity i W hi := by rw [c.identity, inv_one]
  cocycle i j k W hi hj hk := by rw [← mul_inv, c.cocycle]

def inverseProduct (c : Cocycle U) (V : X.Opens)
    (s : sections c V) (t : sections c.inverse V) : sections (Cocycle.one (U := U)) V :=
  ⟨fun p => s.val p * t.val p, by
    constructor
    · intro i W W' hW hi h
      change X.presheaf.map (homOfLE h).op (_ * _) = _
      rw [map_mul, s.property.1 i W W' hW hi h, t.property.1 i W W' hW hi h]
    · intro i j W hW hi hj
      change s.val ⟨i,W,hW,hi⟩ * t.val ⟨i,W,hW,hi⟩ = 1 * _
      rw [s.property.2 i j W hW hi hj, t.property.2 i j W hW hi hj, one_mul]
      change (_ * _) * ((↑((c.transition i j W hi hj)⁻¹ : Γ(X,W)ˣ) : Γ(X,W)) * _) = _
      rw [mul_mul_mul_comm, Units.mul_inv, one_mul]⟩

def inverseProductMap (c : Cocycle U) :
    PresheafOfModulesOfCommRing.Monoidal.tensorObj (R := X.presheaf)
      (presheaf c) (presheaf c.inverse) ⟶ presheaf (Cocycle.one (U := U)) where
  app V := ModuleCat.MonoidalCategory.tensorLift (inverseProduct c V.unop)
    (by intros; apply Subtype.ext; funext p; exact add_mul _ _ _)
    (by intros; apply Subtype.ext; funext p; exact mul_assoc _ _ _)
    (by intros; apply Subtype.ext; funext p; exact mul_add _ _ _)
    (by intros; apply Subtype.ext; funext p; exact mul_left_comm _ _ _)
  naturality {V W} f := by
    apply ModuleCat.MonoidalCategory.tensor_ext
    intro s t
    rfl

def trivialCoefficientMap : (structureSheaf X).val ⟶ presheaf (Cocycle.one (U := U)) where
  app V := ModuleCat.ofHom (R := Γ(X, V.unop))
    (X := ModuleCat.of Γ(X, V.unop) Γ(X, V.unop))
    (Y := ModuleCat.of Γ(X, V.unop) (sections (Cocycle.one (U := U)) V.unop)) {
    toFun a := ⟨fun p => X.presheaf.map (homOfLE p.2.property.1).op a, by
      constructor
      · intro i W W' hW hi h
        change (X.presheaf.map _ ≫ X.presheaf.map _) a = _
        rw [← Functor.map_comp]
        rfl
      · intros; exact (one_mul _).symm⟩
    map_add' a b := by apply Subtype.ext; funext p; exact map_add _ _ _
    map_smul' a b := by apply Subtype.ext; funext p; exact map_mul _ _ _ }
  naturality {V W} f := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro a
    apply Subtype.ext
    funext p
    change (X.presheaf.map _ ≫ X.presheaf.map _) a = _
    rw [← Functor.map_comp]
    rfl

lemma cocycleUnit_restrict_isIso (c : Cocycle U) (i : ι) :
    IsIso ((modulePresheafRestrict (U i).ι).map ((adj X).unit.app (presheaf c))) := by
  let R : PresheafOfModules X.ringCatSheaf.obj ⥤
      PresheafOfModules (U i).toScheme.ringCatSheaf.obj := modulePresheafRestrict (U i).ι
  have hη : IsIso ((adj (U i).toScheme).unit.app (R.obj (presheaf c))) :=
    sheafification_unit_isIso_of_iso _ (structureSheaf (U i).toScheme)
      (chartPresheafFrame c i)
  have hh : IsIso (R.map ((adj X).unit.app (presheaf c)) ≫
      ((moduleSheafificationRestrict (U i).ι).hom.app (presheaf c)).val) := by
    erw [sheafify_restrict_unit]
    exact hη
  let V : (U i).toScheme.Modules ⥤ PresheafOfModules (U i).toScheme.ringCatSheaf.obj :=
    SheafOfModules.forget (U i).toScheme.ringCatSheaf
  let hv : IsIso (C := PresheafOfModules (U i).toScheme.ringCatSheaf.obj)
      (((moduleSheafificationRestrict (U i).ι).hom.app (presheaf c)).val) :=
    (V.mapIso ((moduleSheafificationRestrict (U i).ι).app (presheaf c))).isIso_hom
  exact (@isIso_comp_right_iff (PresheafOfModules (U i).toScheme.ringCatSheaf.obj)
    _ _ _ _ _ _ hv).mp hh

lemma trivialCoefficientMap_frame (i : ι) :
    (modulePresheafRestrict (U i).ι).map (trivialCoefficientMap (U := U)) ≫
      (chartPresheafFrame (Cocycle.one (U := U)) i).hom =
    (Scheme.Modules.restrictUnitIso (U i).ι).hom.val := by
  ext V a
  change X.presheaf.map (homOfLE (show (U i).ι ''ᵁ V.unop ≤ (U i).ι ''ᵁ V.unop from le_rfl)).op a = _
  simp only [homOfLE_refl, op_id, CategoryTheory.Functor.map_id]
  change a = ((U i).ι.appIso V.unop).hom a
  simp only [Scheme.Opens.ι_appIso, Iso.refl_hom]
  rfl

lemma trivialCoefficientMap_restrict_isIso (i : ι) :
    IsIso ((modulePresheafRestrict (U i).ι).map (trivialCoefficientMap (U := U))) := by
  let V : (U i).toScheme.Modules ⥤ PresheafOfModules (U i).toScheme.ringCatSheaf.obj :=
    SheafOfModules.forget (U i).toScheme.ringCatSheaf
  have hv : IsIso (C := PresheafOfModules (U i).toScheme.ringCatSheaf.obj)
      ((Scheme.Modules.restrictUnitIso (U i).ι).hom.val) :=
    (V.mapIso (Scheme.Modules.restrictUnitIso (U i).ι)).isIso_hom
  have hh : IsIso ((modulePresheafRestrict (U i).ι).map (trivialCoefficientMap (U := U)) ≫
      (chartPresheafFrame (Cocycle.one (U := U)) i).hom) := by
    rw [trivialCoefficientMap_frame]
    exact hv
  let hc : IsIso (C := PresheafOfModules (U i).toScheme.ringCatSheaf.obj)
      (chartPresheafFrame (Cocycle.one (U := U)) i).hom :=
    (chartPresheafFrame (Cocycle.one (U := U)) i).isIso_hom
  exact (@isIso_comp_right_iff (PresheafOfModules (U i).toScheme.ringCatSheaf.obj)
    _ _ _ _ _ _ hc).mp hh

lemma inverseProductMap_frame (c : Cocycle U) (i : ι) :
    (modulePresheafRestrict (U i).ι).map (inverseProductMap c) ≫
      (chartPresheafFrame (Cocycle.one (U := U)) i).hom =
    (modulePresheafTensorRestrict (U i) (presheaf c) (presheaf c.inverse)).hom ≫
      PresheafOfModulesOfCommRing.Monoidal.tensorHom (R := (U i).toScheme.presheaf)
        (chartPresheafFrame c i).hom (chartPresheafFrame c.inverse i).hom ≫
      (by
        let : MonoidalCategory (PresheafOfModules (U i).toScheme.ringCatSheaf.obj) :=
          PresheafOfModulesOfCommRing.monoidalCategory (R := (U i).toScheme.presheaf)
        exact (λ_ (structureSheaf (U i).toScheme).val).hom) := by
  let : MonoidalCategory (PresheafOfModules (U i).toScheme.ringCatSheaf.obj) :=
    PresheafOfModulesOfCommRing.monoidalCategory (R := (U i).toScheme.presheaf)
  let l := (modulePresheafRestrict (U i).ι).map (inverseProductMap c) ≫
    (chartPresheafFrame (Cocycle.one (U := U)) i).hom
  let r := (modulePresheafTensorRestrict (U i) (presheaf c) (presheaf c.inverse)).hom ≫
    PresheafOfModulesOfCommRing.Monoidal.tensorHom (R := (U i).toScheme.presheaf)
      (chartPresheafFrame c i).hom (chartPresheafFrame c.inverse i).hom ≫
    (λ_ (structureSheaf (U i).toScheme).val).hom
  change l = r
  ext V : 1
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro z
  induction z using TensorProduct.inductionOn with
  | tmul s t => rfl
  | add a b ha hb =>
      exact ((l.app V).hom.map_add a b).trans
        ((congrArg₂ (· + ·) ha hb).trans ((r.app V).hom.map_add a b).symm)

lemma inverseProductMap_restrict_isIso (c : Cocycle U) (i : ι) :
    IsIso ((modulePresheafRestrict (U i).ι).map (inverseProductMap c)) := by
  let : MonoidalCategory (PresheafOfModules (U i).toScheme.ringCatSheaf.obj) :=
    PresheafOfModulesOfCommRing.monoidalCategory (R := (U i).toScheme.presheaf)
  let e := modulePresheafTensorRestrict (U i) (presheaf c) (presheaf c.inverse) ≪≫
    tensorIso (chartPresheafFrame c i) (chartPresheafFrame c.inverse i) ≪≫
      λ_ (structureSheaf (U i).toScheme).val
  have hh : IsIso ((modulePresheafRestrict (U i).ι).map (inverseProductMap c) ≫
      (chartPresheafFrame (Cocycle.one (U := U)) i).hom) := by
    rw [inverseProductMap_frame]
    exact e.isIso_hom
  let hc : IsIso (C := PresheafOfModules (U i).toScheme.ringCatSheaf.obj)
      (chartPresheafFrame (Cocycle.one (U := U)) i).hom :=
    (chartPresheafFrame (Cocycle.one (U := U)) i).isIso_hom
  exact (@isIso_comp_right_iff (PresheafOfModules (U i).toScheme.ringCatSheaf.obj)
    _ _ _ _ _ _ hc).mp hh

lemma sheafification_isIso_of_chart {P Q : PresheafOfModules X.ringCatSheaf.obj}
    (f : P ⟶ Q) (hcover : ⊤ ≤ ⨆ i, U i)
    (hf : ∀ i, IsIso ((modulePresheafRestrict (U i).ι).map f)) :
    IsIso ((PresheafOfModules.sheafification (𝟙 X.ringCatSheaf.obj)).map f) := by
  apply PiExponent.NumericalAmpleness.isIso_of_locally_isIso
  intro x
  obtain ⟨i, hi⟩ := Opens.mem_iSup.mp (hcover (show x ∈ (⊤ : X.Opens) from trivial))
  refine ⟨U i, hi, ?_⟩
  apply (NatIso.isIso_map_iff (moduleSheafificationRestrict (U i).ι) f).mpr
  have := hf i
  change IsIso ((PresheafOfModules.sheafification (𝟙 (U i).toScheme.ringCatSheaf.obj)).map
    ((modulePresheafRestrict (U i).ι).map f))
  infer_instance

end PiExponentSeshadri.LineBundleGluing

end

end OAI
end Source0462

-- Source: OAI/NumberTheory/PiExponent/Approximation/CocycleTensorIso.lean
section Source0463
/-
Modification notice for the LogTwo project.
Derived from openai/math (Apache-2.0), revision adc7f1241b42e322a6451854ab7e4b4c146bf78a.
Original source: lean/OAI/NumberTheory/PiExponent/Approximation/CocycleTensorIso.lean
Changes: Convert module/import declarations to the Lean 4.34 public module format.
See ../THIRD_PARTY_NOTICES.txt for provenance and the recorded changes.
-/

namespace OAI

namespace PiExponentSeshadri.LineBundleGluing
noncomputable section
open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite MonoidalCategory
open PiExponentSeshadri.Geometry PiExponentSeshadri.TensorPure
variable {X : Scheme} {ι : Type} {U : ι → X.Opens}

lemma tensorHom_restrict_isIso (W : X.Opens)
    {P P' Q Q' : PresheafOfModules X.ringCatSheaf.obj} (f : P ⟶ P') (g : Q ⟶ Q')
    [IsIso ((modulePresheafRestrict W.ι).map f)]
    [IsIso ((modulePresheafRestrict W.ι).map g)] :
    IsIso ((modulePresheafRestrict W.ι).map
      (PresheafOfModulesOfCommRing.Monoidal.tensorHom (R := X.presheaf) f g)) := by
  let R := modulePresheafRestrict W.ι
  let : MonoidalCategory (PresheafOfModules W.toScheme.ringCatSheaf.obj) :=
    PresheafOfModulesOfCommRing.monoidalCategory (R := W.toScheme.presheaf)
  have hh : IsIso (R.map (PresheafOfModulesOfCommRing.Monoidal.tensorHom (R := X.presheaf) f g) ≫
      (modulePresheafTensorRestrict W P' Q').hom) := by
    rw [modulePresheafTensorRestrict_natural]
    change IsIso (_ ≫ (R.map f ⊗ₘ R.map g))
    infer_instance
  let hc : IsIso (C := PresheafOfModules W.toScheme.ringCatSheaf.obj)
      (modulePresheafTensorRestrict W P' Q').hom :=
    (modulePresheafTensorRestrict W P' Q').isIso_hom
  exact (@isIso_comp_right_iff (PresheafOfModules W.toScheme.ringCatSheaf.obj)
    _ _ _ _ _ _ hc).mp hh

def cocycleTensorComparison (c d : Cocycle U) (hcover : ⊤ ≤ ⨆ i, U i) :
    (PresheafOfModules.sheafification (𝟙 X.ringCatSheaf.obj)).obj
      (PresheafOfModulesOfCommRing.Monoidal.tensorObj (R := X.presheaf)
        (presheaf c) (presheaf d)) ≅ moduleTensor X (sheaf c) (sheaf d) := by
  let f := PresheafOfModulesOfCommRing.Monoidal.tensorHom (R := X.presheaf)
    ((adj X).unit.app (presheaf c)) ((adj X).unit.app (presheaf d))
  have ht : IsIso ((PresheafOfModules.sheafification (𝟙 X.ringCatSheaf.obj)).map f) := by
    apply sheafification_isIso_of_chart f hcover
    intro i
    have := cocycleUnit_restrict_isIso c i
    have := cocycleUnit_restrict_isIso d i
    exact tensorHom_restrict_isIso (U i) _ _
  exact @asIso _ _ _ _ ((PresheafOfModules.sheafification (𝟙 X.ringCatSheaf.obj)).map f) ht

def trivialSheafIso (hcover : ⊤ ≤ ⨆ i, U i) :
    sheaf (Cocycle.one (U := U)) ≅ structureSheaf X := by
  have ht : IsIso ((PresheafOfModules.sheafification (𝟙 X.ringCatSheaf.obj)).map
      (trivialCoefficientMap (U := U))) :=
    sheafification_isIso_of_chart _ hcover trivialCoefficientMap_restrict_isIso
  exact (@asIso _ _ _ _ ((PresheafOfModules.sheafification (𝟙 X.ringCatSheaf.obj)).map
    (trivialCoefficientMap (U := U))) ht).symm ≪≫
      (asIso (adj X).counit).app (structureSheaf X)

def tensorInverseIso (c : Cocycle U) (hcover : ⊤ ≤ ⨆ i, U i) :
    moduleTensor X (sheaf c) (sheaf c.inverse) ≅ structureSheaf X := by
  have ht : IsIso ((PresheafOfModules.sheafification (𝟙 X.ringCatSheaf.obj)).map
      (inverseProductMap c)) :=
    sheafification_isIso_of_chart _ hcover (inverseProductMap_restrict_isIso c)
  exact (cocycleTensorComparison c c.inverse hcover).symm ≪≫
    @asIso _ _ _ _ ((PresheafOfModules.sheafification (𝟙 X.ringCatSheaf.obj)).map
      (inverseProductMap c)) ht ≪≫
      trivialSheafIso hcover

end
end PiExponentSeshadri.LineBundleGluing

end OAI
end Source0463

-- Source: OAI/NumberTheory/PiExponent/Approximation/FrameSubopensCoherence.lean
section Source0464
/-
Modification notice for the LogTwo project.
Derived from openai/math (Apache-2.0), revision adc7f1241b42e322a6451854ab7e4b4c146bf78a.
Original source: lean/OAI/NumberTheory/PiExponent/Approximation/FrameSubopensCoherence.lean
Changes: Convert module/import declarations to the Lean 4.34 public module format.
See ../THIRD_PARTY_NOTICES.txt for provenance and the recorded changes.
-/

namespace OAI

namespace PiExponentSeshadri.Frames
noncomputable section
open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite
variable {X : Scheme} {M : X.Modules} {U V W : X.Opens}

lemma restrictOpenFrame_app (h : V ≤ U) (e : M.restrict U.ι ≅ O U.toScheme)
    (A : V.toScheme.Opens) (x : Γ(M.restrict V.ι,A)) :
    (restrictOpenFrame h e).hom.app A x =
      X.presheaf.map (homOfLE (show V.ι ''ᵁ A ≤ U.ι ''ᵁ (X.homOfLE h ''ᵁ A) from by
        simp [← Scheme.Hom.comp_image])).op
        (e.hom.app (X.homOfLE h ''ᵁ A)
          (M.presheaf.map (homOfLE
            (show U.ι ''ᵁ (X.homOfLE h ''ᵁ A) ≤ V.ι ''ᵁ A from by
              simp [← Scheme.Hom.comp_image])).op x)) := by
  simp only [restrictOpenFrame, Iso.trans_hom, Iso.symm_hom,
    Scheme.Modules.Hom.comp_app, Iso.app_inv, Iso.app_hom,
    Scheme.Modules.restrictFunctorCongr_inv_app_app,
    Scheme.Modules.restrictFunctorComp_hom_app_app]
  change ((X.homOfLE h).appIso A).hom (e.hom.app (X.homOfLE h ''ᵁ A)
    ((M.presheaf.map _ ≫ M.presheaf.map _) x)) = _
  simp only [Scheme.Hom.appIso_hom', Scheme.homOfLE_appLE]
  erw [← Functor.map_comp]
  rfl

lemma restrictOpenFrame_trans (h : W ≤ V) (k : V ≤ U)
    (e : M.restrict U.ι ≅ O U.toScheme) :
    restrictOpenFrame h (restrictOpenFrame k e) = restrictOpenFrame (h.trans k) e := by
  apply Iso.ext
  ext A x
  have hh := restrictOpenFrame_app h (restrictOpenFrame k e) A x
  let y := M.presheaf.map (homOfLE
    (show V.ι ''ᵁ (X.homOfLE h ''ᵁ A) ≤ W.ι ''ᵁ A from by
      simp [← Scheme.Hom.comp_image])).op x
  have hk := restrictOpenFrame_app k e (X.homOfLE h ''ᵁ A) y
  have hhk := congrArg (X.presheaf.map (homOfLE
    (show W.ι ''ᵁ A ≤ V.ι ''ᵁ (X.homOfLE h ''ᵁ A) from by
      simp [← Scheme.Hom.comp_image])).op) hk
  have hc := restrictOpenFrame_app (h.trans k) e A x
  refine hh.trans (hhk.trans (Eq.trans ?_ hc.symm))
  change (X.presheaf.map _ ≫ X.presheaf.map _)
    (e.hom.app (X.homOfLE k ''ᵁ (X.homOfLE h ''ᵁ A))
      ((M.presheaf.map _ ≫ M.presheaf.map _) x)) =
    X.presheaf.map _ (e.hom.app (X.homOfLE (h.trans k) ''ᵁ A)
      (M.presheaf.map _ x))
  erw [← Functor.map_comp, ← Functor.map_comp]
  let B := X.homOfLE k ''ᵁ (X.homOfLE h ''ᵁ A)
  let C := X.homOfLE (h.trans k) ''ᵁ A
  have hA : C ≤ B := by
    simp only [B, C, ← Scheme.Hom.comp_image, Scheme.homOfLE_homOfLE]
    exact le_rfl
  have hB : U.ι ''ᵁ B ≤ W.ι ''ᵁ A := by
    simp [B, ← Scheme.Hom.comp_image]
  have hC : W.ι ''ᵁ A ≤ U.ι ''ᵁ C := by
    simp [C, ← Scheme.Hom.comp_image]
  have hn := CategoryTheory.congr_fun
    (e.hom.mapPresheaf.naturality (homOfLE hA).op)
    (M.presheaf.map (homOfLE hB).op x)
  change e.hom.app C ((M.restrict U.ι).presheaf.map (homOfLE hA).op
    (M.presheaf.map (homOfLE hB).op x)) =
    U.toScheme.presheaf.map (homOfLE hA).op
      (e.hom.app B (M.presheaf.map (homOfLE hB).op x)) at hn
  refine Eq.trans ?_ (Eq.trans (congrArg (X.presheaf.map (homOfLE hC).op) hn).symm ?_)
  · change X.presheaf.map _ (e.hom.app B (M.presheaf.map _ x)) =
      (X.presheaf.map _ ≫ X.presheaf.map _) (e.hom.app B (M.presheaf.map _ x))
    erw [← Functor.map_comp]
    rfl
  · apply congrArg (X.presheaf.map (homOfLE hC).op)
    apply congrArg (e.hom.app C)
    change (M.presheaf.map _ ≫ M.presheaf.map _) x = M.presheaf.map _ x
    erw [← Functor.map_comp]
    rfl
end
end PiExponentSeshadri.Frames

end OAI
end Source0464

-- Source: OAI/NumberTheory/PiExponent/Polynomials/FrameCoefficientLaws.lean
section Source0465
/-
Modification notice for the LogTwo project.
Derived from openai/math (Apache-2.0), revision adc7f1241b42e322a6451854ab7e4b4c146bf78a.
Original source: lean/OAI/NumberTheory/PiExponent/Polynomials/FrameCoefficientLaws.lean
Changes: Convert module/import declarations to the Lean 4.34 public module format.
See ../THIRD_PARTY_NOTICES.txt for provenance and the recorded changes.
-/

namespace OAI

namespace PiExponentSeshadri.ProjectiveChartSections
noncomputable section
open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite
open PiExponentSeshadri.Geometry ModuleFlasque RestrictionCohomology Frames
variable {X : Scheme} (U : X.Opens) (M : X.Modules)

lemma framedCoefficientsEquiv_smul
    (e : M.restrict U.ι ≅ structureSheaf U.toScheme)
    (a : Γ(X,U)) (s : Γ(M,U)) :
    framedCoefficientsEquiv U M e (a • s) =
      a * framedCoefficientsEquiv U M e s := by
  have hs : (restrictionSectionsIso U M).inv (a • s) =
      U.topIso.inv a • (restrictionSectionsIso U M).inv s := by
    change M.presheaf.map (eqToHom U.ι_image_top).op (a • s) =
      (U.ι.appIso ⊤).inv (U.topIso.inv a) •
        M.presheaf.map (eqToHom U.ι_image_top).op s
    rw [M.map_smul, U.ι_appIso]
    rfl
  change U.topIso.hom (e.hom.app ⊤ ((restrictionSectionsIso U M).inv (a • s))) =
    a * U.topIso.hom (e.hom.app ⊤ ((restrictionSectionsIso U M).inv s))
  rw [hs, e.hom.app_smul]
  change U.topIso.hom (U.topIso.inv a * _) = _
  erw [map_mul]
  erw [Iso.inv_hom_id_apply]

lemma framedCoefficientsEquiv_change
    (e f : M.restrict U.ι ≅ structureSheaf U.toScheme) (s : Γ(M,U)) :
    framedCoefficientsEquiv U M f s =
      U.topIso.hom (frameChange e f : Γ(U.toScheme,⊤)) *
        framedCoefficientsEquiv U M e s := by
  let t := (restrictionSectionsIso U M).inv s
  have he : e.inv.app ⊤ (e.hom.app ⊤ t) = t := by
    exact congrArg (fun q => q.app ⊤ t) e.hom_inv_id
  have h := end_apply (e.inv ≫ f.hom) ⊤ (e.hom.app ⊤ t)
  change f.hom.app ⊤ (e.inv.app ⊤ (e.hom.app ⊤ t)) =
    (show Γ(U.toScheme,⊤) from e.hom.app ⊤ t) *
      (frameChange e f : Γ(U.toScheme,⊤)) at h
  rw [he, mul_comm] at h
  change U.topIso.hom (f.hom.app ⊤ t) =
    U.topIso.hom (frameChange e f : Γ(U.toScheme,⊤)) * U.topIso.hom (e.hom.app ⊤ t)
  rw [h, map_mul]

end
end PiExponentSeshadri.ProjectiveChartSections

end OAI
end Source0465

-- Source: OAI/NumberTheory/PiExponent/Geometry/LineBundleFrameCocycle.lean
section Source0466
/-
Modification notice for the LogTwo project.
Derived from openai/math (Apache-2.0), revision adc7f1241b42e322a6451854ab7e4b4c146bf78a.
Original source: lean/OAI/NumberTheory/PiExponent/Geometry/LineBundleFrameCocycle.lean
Changes: Convert module/import declarations to the Lean 4.34 public module format.
See ../THIRD_PARTY_NOTICES.txt for provenance and the recorded changes.
-/

namespace OAI

namespace PiExponentSeshadri.LineBundleFrameCocycle
noncomputable section
open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite
open PiExponentSeshadri.Geometry PiExponentSeshadri.Frames
open PiExponentSeshadri.ProjectiveChartSections

variable {X : Scheme} {ι : Type} (M : X.Modules) (U : ι → X.Opens)
  (e : ∀ i, M.restrict (U i).ι ≅ structureSheaf (U i).toScheme)

abbrev frame (i : ι) (W : X.Opens) (hi : W ≤ U i) := restrictOpenFrame hi (e i)

abbrev coeff (i : ι) (W : X.Opens) (hi : W ≤ U i) :=
  framedCoefficientsEquiv W M (frame M U e i W hi)

lemma coeff_restrict {V W : X.Opens} (h : V ≤ W) (i : ι) (hi : W ≤ U i)
    (s : Γ(M,W)) :
    coeff M U e i V (h.trans hi) (M.presheaf.map (homOfLE h).op s) =
      X.presheaf.map (homOfLE h).op (coeff M U e i W hi s) := by
  change framedCoefficientsEquiv V M (restrictOpenFrame (h.trans hi) (e i)) _ = _
  rw [← restrictOpenFrame_trans h hi (e i)]
  exact framedCoefficientsEquiv_restrict M h _ s

def transition (i j : ι) (W : X.Opens) (hi : W ≤ U i) (hj : W ≤ U j) : Γ(X,W)ˣ :=
  Units.map W.topIso.hom.hom.toMonoidHom
    (frameChange (frame M U e j W hj) (frame M U e i W hi))

lemma coeff_change (i j : ι) (W : X.Opens) (hi : W ≤ U i) (hj : W ≤ U j)
    (s : Γ(M,W)) :
    coeff M U e i W hi s = (transition M U e i j W hi hj : Γ(X,W)) *
      coeff M U e j W hj s := by
  exact framedCoefficientsEquiv_change W M (frame M U e j W hj) (frame M U e i W hi) s

def ofFrames : LineBundleGluing.Cocycle U where
  transition := transition M U e
  restriction i j {V W} h hi hj := by
    let s := (coeff M U e j W hj).symm 1
    have hj1 : coeff M U e j W hj s = (1 : Γ(X,W)) :=
      (coeff M U e j W hj).apply_symm_apply 1
    have hi1 : coeff M U e i W hi s = (transition M U e i j W hi hj : Γ(X,W)) := by
      rw [coeff_change M U e i j W hi hj, hj1, mul_one]
    have hjV : coeff M U e j V (h.trans hj) (M.presheaf.map (homOfLE h).op s) = 1 := by
      rw [coeff_restrict M U e h j hj, hj1]
      exact map_one (X.presheaf.map (homOfLE h).op).hom
    calc
      _ = X.presheaf.map (homOfLE h).op (coeff M U e i W hi s) := congrArg _ hi1.symm
      _ = coeff M U e i V (h.trans hi) (M.presheaf.map (homOfLE h).op s) :=
        (coeff_restrict M U e h i hi s).symm
      _ = _ := by rw [coeff_change M U e i j V (h.trans hi) (h.trans hj), hjV, mul_one]
  identity i W hi := by
    apply Units.ext
    change W.topIso.hom (endValue ((frame M U e i W hi).inv ≫
      (frame M U e i W hi).hom)) = 1
    simp
  cocycle i j k W hi hj hk := by
    apply Units.ext
    change W.topIso.hom (endValue ((frame M U e j W hj).inv ≫
      (frame M U e i W hi).hom)) *
      W.topIso.hom (endValue ((frame M U e k W hk).inv ≫
        (frame M U e j W hj).hom)) =
      W.topIso.hom (endValue ((frame M U e k W hk).inv ≫
        (frame M U e i W hi).hom))
    rw [← map_mul, mul_comm, ← endValue_comp]
    simp

def toSections (V : X.Opens) (s : Γ(M,V)) : LineBundleGluing.sections (ofFrames M U e) V :=
  ⟨fun p => coeff M U e p.1 p.2.val p.2.property.2
    (M.presheaf.map (homOfLE p.2.property.1).op s), by
    constructor
    · intro i W W' hW hi h
      change X.presheaf.map (homOfLE h).op
        (coeff M U e i W hi (M.presheaf.map (homOfLE hW).op s)) = _
      rw [← coeff_restrict]
      congr 1
      change (M.presheaf.map _ ≫ M.presheaf.map _) s = _
      rw [← Functor.map_comp]
      rfl
    · intro i j W hW hi hj
      exact coeff_change M U e i j W hi hj _⟩

lemma chartEquiv_toSections (i : ι) (V : X.Opens) (hi : V ≤ U i) (s : Γ(M,V)) :
    LineBundleGluing.chartEquiv (ofFrames M U e) i hi (toSections M U e V s) =
      coeff M U e i V hi s := by
  change coeff M U e i V hi (M.presheaf.map (homOfLE (le_refl V)).op s) = _
  simp

lemma toSections_bijective (i : ι) (V : X.Opens) (hi : V ≤ U i) :
    Function.Bijective (toSections M U e V) := by
  constructor
  · intro s t h
    apply (coeff M U e i V hi).injective
    simpa only [chartEquiv_toSections] using
      congrArg (LineBundleGluing.chartEquiv (ofFrames M U e) i hi) h
  · intro t
    refine ⟨(coeff M U e i V hi).symm
      (LineBundleGluing.chartEquiv (ofFrames M U e) i hi t), ?_⟩
    apply (LineBundleGluing.chartEquiv (ofFrames M U e) i hi).injective
    rw [chartEquiv_toSections, AddEquiv.apply_symm_apply]

def presheafHom : M.val ⟶ LineBundleGluing.presheaf (ofFrames M U e) where
  app V := ModuleCat.ofHom
    (X := M.val.obj V)
    (Y := (LineBundleGluing.presheaf (ofFrames M U e)).obj V)
    { toFun := toSections M U e V.unop
      map_add' := by
        intro s t
        apply Subtype.ext
        funext p
        change coeff M U e p.1 p.2.val p.2.property.2
          (M.presheaf.map (homOfLE p.2.property.1).op (s + t)) = _
        erw [map_add]
        exact map_add _ _ _
      map_smul' := by
        intro a s
        apply Subtype.ext
        funext p
        change coeff M U e p.1 p.2.val p.2.property.2
          (M.presheaf.map (homOfLE p.2.property.1).op (a • s)) =
          X.presheaf.map (homOfLE p.2.property.1).op a *
            coeff M U e p.1 p.2.val p.2.property.2
              (M.presheaf.map (homOfLE p.2.property.1).op s)
        erw [M.map_smul]
        exact framedCoefficientsEquiv_smul _ _ _ _ _ }
  naturality {V W} f := by
    ext s
    apply Subtype.ext
    funext p
    change coeff M U e p.1 p.2.val p.2.property.2
      (M.presheaf.map (homOfLE p.2.property.1).op (M.presheaf.map f s)) =
      coeff M U e p.1 p.2.val p.2.property.2 (M.presheaf.map _ s)
    congr 1
    change (M.presheaf.map _ ≫ M.presheaf.map _) s = _
    rw [← Functor.map_comp]
    rfl

lemma restrict_presheafHom_isIso (i : ι) :
    IsIso ((modulePresheafRestrict (U i).ι).map (presheafHom M U e)) := by
  let f := (modulePresheafRestrict (U i).ι).map (presheafHom M U e)
  have (V : (U i).toScheme.Opensᵒᵖ) : IsIso (f.app V) := by
    apply (ConcreteCategory.isIso_iff_bijective (f.app V)).mpr
    exact toSections_bijective M U e i ((U i).ι ''ᵁ V.unop) ((U i).ι_image_le V.unop)
  let a := PresheafOfModules.isoMk (fun V => asIso (f.app V))
    (fun {_ _} k => f.naturality k)
  change IsIso a.hom
  infer_instance

lemma sheafification_presheafHom_isIso (hcover : ⊤ ≤ ⨆ i, U i) :
    IsIso ((PresheafOfModules.sheafification (𝟙 X.ringCatSheaf.obj)).map
      (presheafHom M U e)) := by
  apply SectionOpens.isIso_of_locally_isIso
  intro x
  have hx : x ∈ ⨆ i, U i := hcover (show x ∈ (⊤ : X.Opens) from trivial)
  obtain ⟨i, hi⟩ := Opens.mem_iSup.mp hx
  refine ⟨U i, hi, ?_⟩
  let := restrict_presheafHom_isIso M U e i
  apply (NatIso.isIso_map_iff (moduleSheafificationRestrict (U i).ι)
    (presheafHom M U e)).mpr
  change IsIso ((PresheafOfModules.sheafification (𝟙 (U i).toScheme.ringCatSheaf.obj)).map
    ((modulePresheafRestrict (U i).ι).map (presheafHom M U e)))
  infer_instance

def isoSheaf (hcover : ⊤ ≤ ⨆ i, U i) :
    M ≅ LineBundleGluing.sheaf (ofFrames M U e) := by
  letI := sheafification_presheafHom_isIso M U e hcover
  exact ((asIso (PresheafOfModules.sheafificationAdjunction (R := X.ringCatSheaf)
    (𝟙 X.ringCatSheaf.obj)).counit).app M).symm ≪≫
    @asIso _ _ _ _
      ((PresheafOfModules.sheafification (𝟙 X.ringCatSheaf.obj)).map (presheafHom M U e))
      (sheafification_presheafHom_isIso M U e hcover)

end
end PiExponentSeshadri.LineBundleFrameCocycle

end OAI
end Source0466

-- Source: OAI/NumberTheory/PiExponent/Geometry/LineBundleInverse.lean
section Source0467
/-
Modification notice for the LogTwo project.
Derived from openai/math (Apache-2.0), revision adc7f1241b42e322a6451854ab7e4b4c146bf78a.
Original source: lean/OAI/NumberTheory/PiExponent/Geometry/LineBundleInverse.lean
Changes: Convert module/import declarations to the Lean 4.34 public module format.
See ../THIRD_PARTY_NOTICES.txt for provenance and the recorded changes.
-/

namespace OAI

namespace PiExponentSeshadri.Geometry
noncomputable section
open AlgebraicGeometry CategoryTheory TopologicalSpace
variable {X : Scheme}

def LineBundle.inverseCover (L : LineBundle X) (x : X) : X.Opens :=
  (L.locallyRankOne x).choose

lemma LineBundle.mem_inverseCover (L : LineBundle X) (x : X) :
    x ∈ L.inverseCover x := (L.locallyRankOne x).choose_spec.1

def LineBundle.inverseCoverFrame (L : LineBundle X) (x : X) :
    L.sheaf.restrict (L.inverseCover x).ι ≅ structureSheaf (L.inverseCover x).toScheme :=
  (L.locallyRankOne x).choose_spec.2.some

lemma LineBundle.inverseCover_covers (L : LineBundle X) :
    ⊤ ≤ ⨆ x, L.inverseCover x := by
  intro x _
  exact Opens.mem_iSup.mpr ⟨x, L.mem_inverseCover x⟩

def LineBundle.inverseCocycle (L : LineBundle X) :
    LineBundleGluing.Cocycle L.inverseCover :=
  LineBundleFrameCocycle.ofFrames L.sheaf L.inverseCover L.inverseCoverFrame

def LineBundle.inverse (L : LineBundle X) : LineBundle X :=
  LineBundleGluing.lineBundle L.inverseCocycle.inverse L.inverseCover_covers

def lineTensorInverseIso (L : LineBundle X) :
    moduleTensor X L.sheaf L.inverse.sheaf ≅ structureSheaf X :=
  moduleTensorIso
    (LineBundleFrameCocycle.isoSheaf L.sheaf L.inverseCover L.inverseCoverFrame
      L.inverseCover_covers) (Iso.refl _) ≪≫
    LineBundleGluing.tensorInverseIso L.inverseCocycle L.inverseCover_covers

def moduleTensorInverseCancelIso (M : X.Modules) (L : LineBundle X) :
    moduleTensor X (moduleTensor X M L.sheaf) L.inverse.sheaf ≅ M :=
  moduleLineTensorAssoc M L L.inverse ≪≫
    moduleTensorIso (Iso.refl M) (lineTensorInverseIso L) ≪≫ moduleTensorRightUnit M

def LineBundle.dualSection (L : LineBundle X) (s : structureSheaf X ⟶ L.sheaf) :
    L.inverse.sheaf ⟶ structureSheaf X :=
  (moduleTensorUnit L.inverse.sheaf).inv ≫ moduleTensorMap s (𝟙 _) ≫
    (lineTensorInverseIso L).hom

end
end PiExponentSeshadri.Geometry

end OAI
end Source0467

-- Source: OAI/NumberTheory/PiExponent/Approximation/InverseDualRestriction.lean
section Source0468
/-
Modification notice for the LogTwo project.
Derived from openai/math (Apache-2.0), revision adc7f1241b42e322a6451854ab7e4b4c146bf78a.
Original source: lean/OAI/NumberTheory/PiExponent/Approximation/InverseDualRestriction.lean
Changes: Convert module/import declarations to the Lean 4.34 public module format.
See ../THIRD_PARTY_NOTICES.txt for provenance and the recorded changes.
-/

namespace OAI

namespace PiExponent.InverseFrames
noncomputable section
open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite
open PiExponentSeshadri.Geometry PiExponentSeshadri.Frames PiExponentSeshadri.TensorPure
variable {X : Scheme.{0}} {M N : X.Modules}

lemma dualMap_restrict (E : moduleTensor X M N ≅ O X) (s : O X ⟶ M) (U : X.Opens) :
    (Scheme.Modules.restrictFunctor U.ι).map (dualMap E s) ≫
      (Scheme.Modules.restrictUnitIso U.ι).hom =
    dualMap (restrictPairing E U) (restrictSection U.ι s) := by
  ext A n
  change Γ(N, U.ι ''ᵁ A) at n
  change (U.ι.appIso A).hom ((dualMap E s).app (U.ι ''ᵁ A) n) =
    (dualMap (restrictPairing E U) (restrictSection U.ι s)).app A n
  erw [dualMap_apply E s (U.ι ''ᵁ A) n,
    dualMap_apply (restrictPairing E U) (restrictSection U.ι s) A n]
  change (U.ι.appIso A).hom (E.hom.app (U.ι ''ᵁ A)
      (PiExponentSeshadri.TensorPure.pure M N (U.ι ''ᵁ A)
        (s.app (U.ι ''ᵁ A) (1 : Γ(X,U.ι ''ᵁ A))) n)) =
    (U.ι.appIso A).hom (E.hom.app (U.ι ''ᵁ A)
      ((moduleTensorRestrict U M N).inv.app A
        (PiExponentSeshadri.TensorPure.pure (M.restrict U.ι) (N.restrict U.ι) A
          ((restrictSection U.ι s).app A (1 : Γ(U.toScheme,A))) n)))
  erw [restrict_pure_inv U M N A
    ((restrictSection U.ι s).app A (1 : Γ(U.toScheme,A))) n]
  change (U.ι.appIso A).hom (E.hom.app (U.ι ''ᵁ A)
      (PiExponentSeshadri.TensorPure.pure M N (U.ι ''ᵁ A)
        (s.app (U.ι ''ᵁ A) (1 : Γ(X,U.ι ''ᵁ A))) n)) =
    (U.ι.appIso A).hom (E.hom.app (U.ι ''ᵁ A)
      (PiExponentSeshadri.TensorPure.pure M N (U.ι ''ᵁ A)
        (s.app (U.ι ''ᵁ A) ((U.ι.appIso A).inv (1 : Γ(U.toScheme,A)))) n))
  rw [show (U.ι.appIso A).inv (1 : Γ(U.toScheme,A)) = (1 : Γ(X,U.ι ''ᵁ A)) from
    (U.ι.appIso A).inv.hom.map_one]

lemma dualMap_restrict_coefficient (E : moduleTensor X M N ≅ O X)
    (s : O X ⟶ M) (U : X.Opens) (e : M.restrict U.ι ≅ O U.toScheme) :
    endValue ((inverseOpenFrame E U e).inv ≫
      (Scheme.Modules.restrictFunctor U.ι).map (dualMap E s) ≫
      (Scheme.Modules.restrictUnitIso U.ι).hom) =
    coefficient e (restrictSection U.ι s) := by
  erw [dualMap_restrict]
  exact dualMap_coefficient (restrictPairing E U) e (restrictSection U.ι s)

lemma dualSection_restrict_coefficient (L : LineBundle X)
    (s : structureSheaf X ⟶ L.sheaf) (U : X.Opens)
    (e : L.sheaf.restrict U.ι ≅ structureSheaf U.toScheme) :
    endValue ((inverseOpenFrame (lineTensorInverseIso L) U e).inv ≫
      (Scheme.Modules.restrictFunctor U.ι).map (L.dualSection s) ≫
      (Scheme.Modules.restrictUnitIso U.ι).hom) =
    coefficient e (restrictSection U.ι s) :=
  dualMap_restrict_coefficient (lineTensorInverseIso L) s U e

end
end PiExponent.InverseFrames

end OAI
end Source0468

-- Source: OAI/NumberTheory/PiExponent/LocalAlgebra/SectionImageIdeal.lean
section Source0469
/-
Modification notice for the LogTwo project.
Derived from openai/math (Apache-2.0), revision adc7f1241b42e322a6451854ab7e4b4c146bf78a.
Original source: lean/OAI/NumberTheory/PiExponent/LocalAlgebra/SectionImageIdeal.lean
Changes: Convert module/import declarations to the Lean 4.34 public module format.
See ../THIRD_PARTY_NOTICES.txt for provenance and the recorded changes.
-/

namespace OAI

namespace PiExponent.SectionImageIdeal
noncomputable section
open CategoryTheory AlgebraicGeometry TopologicalSpace Opposite
open PiExponentSeshadri.Geometry
variable {X : Scheme.{0}} {M : X.Modules}

def imageIdeal (φ : M ⟶ structureSheaf X) (U : X.Opens) : Ideal Γ(X,U) :=
  (φ.val.app (op U)).hom.range

lemma map_imageIdeal_le (φ : M ⟶ structureSheaf X) {U V : X.Opens} (h : U ≤ V) :
    (imageIdeal φ V).map (X.presheaf.map (homOfLE h).op).hom ≤ imageIdeal φ U := by
  apply Ideal.map_le_iff_le_comap.mpr
  rintro x ⟨m,rfl⟩
  refine ⟨M.presheaf.map (homOfLE h).op m, ?_⟩
  exact congr($(φ.mapPresheaf.naturality (homOfLE h).op) m)

theorem affine_map_imageIdeal [IsAffine X] [M.IsQuasicoherent]
    (φ : M ⟶ structureSheaf X) (r : Γ(X,⊤)) :
    (imageIdeal φ ⊤).map (X.presheaf.map (homOfLE (X.basicOpen_le r)).op).hom =
      imageIdeal φ (X.basicOpen r) := by
  apply le_antisymm (map_imageIdeal_le φ _)
  rintro x ⟨m,rfl⟩
  change Γ(M, X.basicOpen r) at m
  obtain ⟨n,z,hz⟩ := GlobalSectionClearing.affine_basicOpen_denominators M r m
  let ρ : Γ(X,⊤) →+* Γ(X,X.basicOpen r) :=
    (X.presheaf.map (homOfLE (X.basicOpen_le r)).op).hom
  have he : ρ (φ.app ⊤ z) = ρ r ^ n * (show Γ(X,X.basicOpen r) from φ.app (X.basicOpen r) m) := by
    have hn := congr($(φ.mapPresheaf.naturality (homOfLE (X.basicOpen_le r)).op) z)
    change φ.app (X.basicOpen r)
      (GlobalSectionClearing.openRestriction M (X.basicOpen_le r) z) = ρ (φ.app ⊤ z) at hn
    rw [← hn, hz]
    change φ.app (X.basicOpen r) (ρ (r^n) • m) = _
    rw [map_pow, φ.app_smul]
    rfl
  have hm : ρ (φ.app ⊤ z) ∈ (imageIdeal φ ⊤).map ρ :=
    Ideal.mem_map_of_mem ρ ⟨z,rfl⟩
  rw [he] at hm
  exact (Ideal.unit_mul_mem_iff_mem _
    ((X.toRingedSpace.isUnit_res_basicOpen r).pow n)).mp hm

theorem imageIdeal_restrict {Y : Scheme.{0}} (f : Y ⟶ X) [IsOpenImmersion f]
    (φ : M ⟶ structureSheaf X) (V : Y.Opens) :
    (imageIdeal ((Scheme.Modules.restrictFunctor f).map φ ≫
      (Scheme.Modules.restrictUnitIso f).hom) V).map (f.appIso V).inv.hom =
      imageIdeal φ (f ''ᵁ V) := by
  apply le_antisymm
  · apply Ideal.map_le_iff_le_comap.mpr
    rintro y ⟨m,rfl⟩
    refine ⟨m,?_⟩
    change φ.app (f ''ᵁ V) m = (f.appIso V).inv ((f.appIso V).hom (φ.app (f ''ᵁ V) m))
    exact ((f.appIso V).hom_inv_id_apply _).symm
  · rintro y ⟨m,rfl⟩
    have h := Ideal.mem_map_of_mem (f.appIso V).inv.hom
      (show ((f.appIso V).hom (φ.app (f ''ᵁ V) m)) ∈
        imageIdeal ((Scheme.Modules.restrictFunctor f).map φ ≫
          (Scheme.Modules.restrictUnitIso f).hom) V from ⟨m,rfl⟩)
    change (show Γ(X,f ''ᵁ V) from φ.app (f ''ᵁ V) m) ∈
      (imageIdeal ((Scheme.Modules.restrictFunctor f).map φ ≫
        (Scheme.Modules.restrictUnitIso f).hom) V).map (f.appIso V).inv.hom
    erw [(f.appIso V).hom_inv_id_apply] at h
    exact h

theorem map_imageIdeal_affine_image {Y : Scheme.{0}} [IsAffine Y]
    [M.IsQuasicoherent] (f : Y ⟶ X) [IsOpenImmersion f]
    (φ : M ⟶ structureSheaf X) (r : Γ(Y,⊤)) :
    (imageIdeal φ (f ''ᵁ ⊤)).map
      (X.presheaf.map (f.opensFunctor.map (homOfLE (Y.basicOpen_le r))).op).hom =
      imageIdeal φ (f ''ᵁ Y.basicOpen r) := by
  let ψ : M.restrict f ⟶ structureSheaf Y :=
    (Scheme.Modules.restrictFunctor f).map φ ≫ (Scheme.Modules.restrictUnitIso f).hom
  rw [← imageIdeal_restrict f φ ⊤, Ideal.map_map]
  have hn := congrArg CommRingCat.Hom.hom
    (f.appIso_inv_naturality (homOfLE (Y.basicOpen_le r)).op)
  change (f.appIso (Y.basicOpen r)).inv.hom.comp
      (Y.presheaf.map (homOfLE (Y.basicOpen_le r)).op).hom =
    (X.presheaf.map (f.opensFunctor.map (homOfLE (Y.basicOpen_le r))).op).hom.comp
      (f.appIso ⊤).inv.hom at hn
  rw [← hn, ← Ideal.map_map]
  rw [affine_map_imageIdeal ψ r, imageIdeal_restrict]

theorem map_imageIdeal_basicOpen [M.IsQuasicoherent]
    (φ : M ⟶ structureSheaf X) (U : X.affineOpens) (r : Γ(X,U.1)) :
    (imageIdeal φ U.1).map (X.presheaf.map (homOfLE (X.basicOpen_le r)).op).hom =
      imageIdeal φ (X.basicOpen r) := by
  let : IsAffine U.1.toScheme := U.2
  have h (V W : X.Opens) (hV : U.1.ι ''ᵁ (⊤ : U.1.toScheme.Opens) = V)
      (hW : U.1.ι ''ᵁ U.1.toScheme.basicOpen (U.1.topIso.inv r) = W) (hWV : W ≤ V) :
      (imageIdeal φ V).map (X.presheaf.map (homOfLE hWV).op).hom = imageIdeal φ W := by
    subst V
    subst W
    exact map_imageIdeal_affine_image U.1.ι φ (U.1.topIso.inv r)
  exact h U.1 (X.basicOpen r) U.1.ι_image_top (U.1.ι_image_basicOpen_topIso_inv r)
    (X.basicOpen_le r)

def imageIdealSheaf [M.IsQuasicoherent] (φ : M ⟶ structureSheaf X) : X.IdealSheafData where
  ideal U := imageIdeal φ U.1
  map_ideal_basicOpen U r := map_imageIdeal_basicOpen φ U r

@[simp] theorem imageIdealSheaf_ideal [M.IsQuasicoherent]
    (φ : M ⟶ structureSheaf X) (U : X.affineOpens) :
    (imageIdealSheaf φ).ideal U = imageIdeal φ U.1 := rfl

theorem imageIdeal_top_of_frame (φ : M ⟶ structureSheaf X)
    (e : M ≅ structureSheaf X) :
    imageIdeal φ ⊤ = Ideal.span {PiExponentSeshadri.Frames.endValue (e.inv ≫ φ)} := by
  apply le_antisymm
  · rintro x ⟨m,rfl⟩
    change Γ(M,⊤) at m
    apply Ideal.mem_span_singleton.mpr
    refine ⟨e.hom.app ⊤ m, ?_⟩
    have he : (e.inv ≫ φ).app ⊤ (e.hom.app ⊤ m) = φ.app ⊤ m := by
      change (e.hom ≫ e.inv ≫ φ).app ⊤ m = _
      rw [e.hom_inv_id_assoc]
    exact he.symm.trans ((PiExponentSeshadri.Frames.end_apply (e.inv ≫ φ) ⊤
      (e.hom.app ⊤ m)).trans (mul_comm (show Γ(X,⊤) from e.hom.app ⊤ m)
        (PiExponentSeshadri.Frames.endValue (e.inv ≫ φ))))
  · apply Ideal.span_le.mpr
    rintro x (rfl : x = _)
    exact ⟨e.inv.app ⊤ (1 : Γ(X,⊤)), rfl⟩

lemma imageIdeal_map_eq (φ : M ⟶ structureSheaf X) {U V : X.Opens} (h : U = V) :
    (imageIdeal φ U).map (X.presheaf.map (eqToHom h.symm).op).hom = imageIdeal φ V := by
  subst V
  change (imageIdeal φ U).map (X.presheaf.map (𝟙 (op U))).hom = imageIdeal φ U
  rw [X.presheaf.map_id]
  exact Ideal.map_id _

theorem imageIdealSheaf_on_frame [M.IsQuasicoherent]
    (φ : M ⟶ structureSheaf X) (U : X.affineOpens)
    (e : M.restrict U.1.ι ≅ structureSheaf U.1.toScheme) :
    (imageIdealSheaf φ).ideal U = Ideal.span
      {U.1.topIso.hom (PiExponentSeshadri.Frames.endValue
        (e.inv ≫ (Scheme.Modules.restrictFunctor U.1.ι).map φ ≫
          (Scheme.Modules.restrictUnitIso U.1.ι).hom))} := by
  let ψ := (Scheme.Modules.restrictFunctor U.1.ι).map φ ≫
    (Scheme.Modules.restrictUnitIso U.1.ι).hom
  have h : (imageIdeal ψ ⊤).map U.1.topIso.hom.hom = imageIdeal φ U.1 := by
    have hi := congrArg (fun J : Ideal Γ(X,U.1.ι ''ᵁ ⊤) =>
      J.map (X.presheaf.map (eqToHom U.1.ι_image_top.symm).op).hom)
      (imageIdeal_restrict U.1.ι φ ⊤)
    rw [imageIdeal_map_eq φ U.1.ι_image_top] at hi
    rw [Ideal.map_map] at hi
    convert hi using 1
    congr 1
    ext a
    simp only [Scheme.Opens.topIso_hom, Scheme.Opens.ι_appIso, Iso.refl_inv, RingHom.comp_apply]
    rfl
  rw [imageIdeal_top_of_frame ψ e, Ideal.map_span, Set.image_singleton] at h
  exact h.symm

end
end PiExponent.SectionImageIdeal

end OAI
end Source0469

-- Source: OAI/NumberTheory/PiExponent/LocalAlgebra/SectionZeroIdeal.lean
section Source0470
-- Modified in this edition: unused plain lemmas removed; see reduction.json.
/-
Modification notice for the LogTwo project.
Derived from openai/math (Apache-2.0), revision adc7f1241b42e322a6451854ab7e4b4c146bf78a.
Original source: lean/OAI/NumberTheory/PiExponent/LocalAlgebra/SectionZeroIdeal.lean
Changes: Convert module/import declarations to the Lean 4.34 public module format.
See ../THIRD_PARTY_NOTICES.txt for provenance and the recorded changes.
-/

namespace OAI

namespace PiExponent.SectionZeroIdeal
noncomputable section
open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite
open PiExponentSeshadri.Geometry PiExponentSeshadri.Frames
open PiExponent.SectionImageIdeal PiExponent.InverseFrames
variable {X : Scheme.{0}}

def zeroIdeal (L : LineBundle X) (s : GlobalSections X L.sheaf) : X.IdealSheafData := by
  letI := PiExponent.GeometrySupport.LineBundleCoherent.lineBundle_isFinitePresentation L.inverse
  letI : L.inverse.sheaf.IsQuasicoherent :=
    (SheafOfModules.IsFinitePresentation.exists_quasicoherentData L.inverse.sheaf).choose.isQuasicoherent
  exact imageIdealSheaf (L.dualSection s)

theorem zeroIdeal_on_frame (L : LineBundle X) (s : GlobalSections X L.sheaf)
    (U : X.affineOpens) (e : L.sheaf.restrict U.1.ι ≅ structureSheaf U.1.toScheme) :
    (zeroIdeal L s).ideal U =
      Ideal.span {U.1.topIso.hom (coefficient e (restrictSection U.1.ι s))} := by
  let := PiExponent.GeometrySupport.LineBundleCoherent.lineBundle_isFinitePresentation L.inverse
  let : L.inverse.sheaf.IsQuasicoherent :=
    (SheafOfModules.IsFinitePresentation.exists_quasicoherentData L.inverse.sheaf).choose.isQuasicoherent
  change (imageIdealSheaf (L.dualSection s)).ideal U = _
  rw [imageIdealSheaf_on_frame (L.dualSection s) U
    (inverseOpenFrame (lineTensorInverseIso L) U.1 e), dualSection_restrict_coefficient]

theorem zeroIdeal_ne_bot [IsIntegral X] (L : LineBundle X)
    (s : GlobalSections X L.sheaf) (hs : s ≠ 0) : zeroIdeal L s ≠ ⊥ := by
  obtain ⟨x⟩ : Nonempty X := inferInstance
  obtain ⟨V,hxV,⟨eV⟩⟩ := L.locallyRankOne x
  obtain ⟨U,hU,hxU,hUV⟩ := exists_isAffineOpen_mem_and_subset hxV
  let e := restrictOpenFrame hUV eV
  let : Nonempty U := ⟨⟨x,hxU⟩⟩
  intro h
  have hi := zeroIdeal_on_frame L s ⟨U,hU⟩ e
  rw [h] at hi
  have hz : U.topIso.hom (coefficient e (restrictSection U.ι s)) = 0 := by
    have hm := Ideal.subset_span (Set.mem_singleton
      (U.topIso.hom (coefficient e (restrictSection U.ι s))))
    rw [← hi] at hm
    exact hm
  have hc : coefficient e (restrictSection U.ι s) = 0 := by
    exact (map_eq_zero_iff _ (ConcreteCategory.bijective_of_isIso U.topIso.hom).injective).mp hz
  apply hs
  apply L.restricted_coefficient_injective U.ι e
  exact hc.trans ((congrArg (coefficient e) (restrictSection_zero U.ι)).trans
    (coefficient_zero e)).symm

end
end PiExponent.SectionZeroIdeal

end OAI
end Source0470

-- Source: OAI/NumberTheory/PiExponent/Geometry/CurveDegreeAdditivity.lean
section Source0471
-- Modified in this edition: unused plain lemmas removed; see reduction.json.
/-
Modification notice for the LogTwo project.
Derived from openai/math (Apache-2.0), revision adc7f1241b42e322a6451854ab7e4b4c146bf78a.
Original source: lean/OAI/NumberTheory/PiExponent/Geometry/CurveDegreeAdditivity.lean
Changes: Convert module/import declarations to the Lean 4.34 public module format.
See ../THIRD_PARTY_NOTICES.txt for provenance and the recorded changes.
-/

namespace OAI

namespace PiExponent.CurveDegree
noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace
open PiExponentSeshadri.Geometry PiExponentSeshadri.Frames
open PiExponent.SectionZeroIdeal PiExponent.CartierPowerFrames
variable {X : Scheme.{0}}

def FiniteLineCohomology (p : X ⟶ Spec (CommRingCat.of ℂ)) : Prop :=
  ∀ L : LineBundle X, ∀ n ≤ 1,
    let := Module.compHom (cohomology L.sheaf n) (baseScalars p)
    FiniteDimensional ℂ (cohomology L.sheaf n)

def LineCohomologyTwoZero (X : Scheme.{0}) : Prop :=
  ∀ L : LineBundle X, Subsingleton (cohomology L.sheaf 2)

theorem section_tensor_euler_add [IsIntegral X]
    (p : X ⟶ Spec (CommRingCat.of ℂ)) [IsProper p]
    (hd : topologicalKrullDim X ≤ 1)
    (hfinite : FiniteLineCohomology p) (hH2 : LineCohomologyTwoZero X)
    (L M : LineBundle X) (s : GlobalSections X L.sheaf) (hs : s ≠ 0) :
    eulerCharacteristic p 1 (L.tensor M).sheaf - eulerCharacteristic p 1 M.sheaf =
      eulerCharacteristic p 1 L.sheaf - eulerCharacteristic p 1 (structureSheaf X) := by
  let hsMono : Mono s := L.mono_section s hs
  let I := zeroIdeal L s
  have hI : I ≠ ⊥ := zeroIdeal_ne_bot L s hs
  let φ := sectionMultiplyLeft L.sheaf M.sheaf s
  let : Mono (moduleTensorMap s (𝟙 M.sheaf)) := moduleTensorMap_mono s M
  let hφMono : Mono φ := mono_comp _ _
  have heqTensor : ∀ x : X, ∃ U : X.affineOpens, x ∈ U.1 ∧
      ∃ f : M.sheaf.restrict U.1.ι ≅ O U.1.toScheme,
      ∃ e : (L.tensor M).sheaf.restrict U.1.ι ≅ O U.1.toScheme,
        I.ideal U = Ideal.span {(U.1.topIso.hom
          (endValue (f.inv ≫ (Scheme.Modules.restrictFunctor U.1.ι).map φ ≫ e.hom)))} := by
    intro x
    obtain ⟨U, hx, ⟨e⟩, ⟨f⟩⟩ := common_affine_frames L M x
    refine ⟨U, hx, f, tensorFrame L.sheaf M.sheaf U.1 e f, ?_⟩
    exact (zeroIdeal_on_frame L s U e).trans
      (tensor_multiply_ideal L.sheaf M.sheaf s U e f).symm
  have heqSection : ∀ x : X, ∃ U : X.affineOpens, x ∈ U.1 ∧
      ∃ f : (L.pow 0).sheaf.restrict U.1.ι ≅ O U.1.toScheme,
      ∃ e : L.sheaf.restrict U.1.ι ≅ O U.1.toScheme,
        I.ideal U = Ideal.span {(U.1.topIso.hom
          (endValue (f.inv ≫ (Scheme.Modules.restrictFunctor U.1.ι).map s ≫ e.hom)))} := by
    intro x
    obtain ⟨U, hx, ⟨e⟩, ⟨f⟩⟩ := common_affine_frames L M x
    refine ⟨U, hx, Scheme.Modules.restrictUnitIso U.1.ι, e, ?_⟩
    simpa only [coefficient, restrictSection, Category.assoc] using! zeroIdeal_on_frame L s U e
  let : Subsingleton (cohomology M.sheaf 2) := hH2 M
  let : Subsingleton (cohomology (L.pow 0).sheaf 2) := hH2 (L.pow 0)
  have hTensor := @CartierDegreeLength.cartier_euler_difference_eq_sum_local_lengths
    X inferInstance p inferInstance hd M (L.tensor M) φ hφMono I hI heqTensor (hfinite M) (hfinite (L.tensor M))
  have hSection := @CartierDegreeLength.cartier_euler_difference_eq_sum_local_lengths
    X inferInstance p inferInstance hd (L.pow 0) L s hsMono I hI heqSection (hfinite (L.pow 0)) (hfinite L)
  exact hTensor.trans hSection.symm

theorem tensor_euler_add [IsIntegral X]
    (p : X ⟶ Spec (CommRingCat.of ℂ)) [IsProper p]
    (hd : topologicalKrullDim X ≤ 1) (H : LineBundle X) (hH : H.IsAmple)
    (hfinite : FiniteLineCohomology p) (hH2 : LineCohomologyTwoZero X)
    (L M : LineBundle X) :
    eulerCharacteristic p 1 (L.tensor M).sheaf - eulerCharacteristic p 1 M.sheaf =
      eulerCharacteristic p 1 L.sheaf - eulerCharacteristic p 1 (structureSheaf X) := by
  let : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian p
  let : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace p
  let : IsNoetherian X := ⟨⟩
  obtain ⟨A, ⟨t, ht⟩, ⟨u, hu⟩⟩ := exists_effective_twist H hH L
  have h₀ := section_tensor_euler_add p hd hfinite hH2 A L t ht
  have h₁ := section_tensor_euler_add p hd hfinite hH2 (A.tensor L) M u hu
  have h₂ := section_tensor_euler_add p hd hfinite hH2 A (L.tensor M) t ht
  have he := eulerCharacteristic_iso p (lineTensorAssoc A L M) 1
  change eulerCharacteristic p 1 ((A.tensor L).tensor M).sheaf =
    eulerCharacteristic p 1 (A.tensor (L.tensor M)).sheaf at he
  omega

theorem power_euler [IsIntegral X]
    (p : X ⟶ Spec (CommRingCat.of ℂ)) [IsProper p]
    (hd : topologicalKrullDim X ≤ 1) (H : LineBundle X) (hH : H.IsAmple)
    (hfinite : FiniteLineCohomology p) (hH2 : LineCohomologyTwoZero X)
    (L : LineBundle X) (n : ℕ) :
    eulerCharacteristic p 1 (L.pow n).sheaf - eulerCharacteristic p 1 (structureSheaf X) =
      (n : ℤ) * (eulerCharacteristic p 1 L.sheaf - eulerCharacteristic p 1 (structureSheaf X)) := by
  induction n with
  | zero => simp [LineBundle.pow, modulePow, structureSheaf]
  | succ n ih =>
    have he := tensor_euler_add p hd H hH hfinite hH2 L (L.pow n)
    change eulerCharacteristic p 1 (L.pow (n+1)).sheaf -
      eulerCharacteristic p 1 (L.pow n).sheaf = _ at he
    push_cast
    nlinarith

end
end PiExponent.CurveDegree

namespace PiExponent.NumericalAmpleness
noncomputable section
open AlgebraicGeometry CategoryTheory TopologicalSpace
open PiExponentSeshadri.Geometry
variable {X : Scheme.{0}}

theorem curveDegree_tensor (p : X ⟶ Spec (CommRingCat.of ℂ)) [IsProper p]
    (H : LineBundle X) (hH : H.IsAmple) (L M : LineBundle X) (C : IntegralCurve X)
    (hfinite : CurveDegree.FiniteLineCohomology (C.embedding ≫ p))
    (hH2 : CurveDegree.LineCohomologyTwoZero C.scheme) :
    curveDegree p (L.tensor M) C = curveDegree p L C + curveDegree p M C := by
  have he := CurveDegree.tensor_euler_add (C.embedding ≫ p) C.dimension.le
    (H.pullback C.embedding) (LineBundle.IsAmple.pullback_closedImmersion H hH C.embedding)
    hfinite hH2 (L.pullback C.embedding) (M.pullback C.embedding)
  have hi := eulerCharacteristic_iso (C.embedding ≫ p)
    (PiExponentSeshadri.PullbackTensor.iso C.embedding L M) 1
  unfold curveDegree
  rw [hi]
  change _ - _ = (_ - _) + (_ - _)
  dsimp only [LineBundle.pullback, LineBundle.tensor] at he ⊢
  omega

theorem curveDegree_pow (p : X ⟶ Spec (CommRingCat.of ℂ)) [IsProper p]
    (H : LineBundle X) (hH : H.IsAmple) (L : LineBundle X) (C : IntegralCurve X)
    (hfinite : CurveDegree.FiniteLineCohomology (C.embedding ≫ p))
    (hH2 : CurveDegree.LineCohomologyTwoZero C.scheme) (n : ℕ) :
    curveDegree p (L.pow n) C = (n : ℤ) * curveDegree p L C := by
  have hi := eulerCharacteristic_iso (C.embedding ≫ p)
    (PiExponentSeshadri.PullbackTensor.powIso C.embedding L n) 1
  unfold curveDegree
  rw [hi]
  exact CurveDegree.power_euler (C.embedding ≫ p) C.dimension.le
    (H.pullback C.embedding) (LineBundle.IsAmple.pullback_closedImmersion H hH C.embedding)
    hfinite hH2 (L.pullback C.embedding) n

end
end PiExponent.NumericalAmpleness

end OAI
end Source0471

-- Source: OAI/NumberTheory/PiExponent/Geometry/CurveNormalizationNonaffine.lean
section Source0472
/-
Modification notice for the LogTwo project.
Derived from openai/math (Apache-2.0), revision adc7f1241b42e322a6451854ab7e4b4c146bf78a.
Original source: lean/OAI/NumberTheory/PiExponent/Geometry/CurveNormalizationNonaffine.lean
Changes: Convert module/import declarations to the Lean 4.34 public module format.
See ../THIRD_PARTY_NOTICES.txt for provenance and the recorded changes.
-/

namespace OAI

noncomputable section
namespace PiExponent.CurveNormalizationModel
open AlgebraicGeometry CategoryTheory TopologicalSpace
open PiExponent.CurveZeroPole
universe u
variable {F E : Type u} [Field F] [Field E] [Algebra F E]
variable (f : E) (hf : Transcendental F f)
variable [CharZero F] [FiniteDimensional (IntermediateField.adjoin F {f}) E]

theorem parameterCurve_not_isAffine : ¬ IsAffine (parameterCurve f hf) := by
  intro haff
  let X := parameterCurve f hf
  let p := parameterCurveStructureMap f hf
  have : IsAffine X := haff
  have : IsFinite p := IsFinite.iff_isProper_and_isAffineHom.mpr
    ⟨inferInstance, inferInstance⟩
  let : Algebra F Γ(X,⊤) :=
    (p.appTop.hom.comp (Scheme.ΓSpecIso (CommRingCat.of F)).inv.hom).toAlgebra
  have : Module.Finite F Γ(X,⊤) :=
    p.finite_appTop.comp (RingHom.Finite.of_surjective
      (Scheme.ΓSpecIso (CommRingCat.of F)).inv.hom
      (Scheme.ΓSpecIso (CommRingCat.of F)).symm.commRingCatIsoToRingEquiv.surjective)
  have : IsArtinianRing Γ(X,⊤) := IsArtinianRing.of_finite F Γ(X,⊤)
  have : IsLocallyArtinian (Spec Γ(X,⊤)) :=
    Scheme.isLocallyArtinianScheme_Spec.mpr inferInstance
  have : T1Space (Spec Γ(X,⊤)) := inferInstance
  have : T1Space X := X.isoSpec.hom.isEmbedding.t1Space
  exact (parameterCurve_isClosed_iff_ne_generic f hf
    (genericPoint (parameterCurve f hf))).mp isClosed_singleton rfl

end PiExponent.CurveNormalizationModel

end

end OAI
end Source0472

-- Source: OAI/NumberTheory/PiExponent/Cohomology/PencilCohomologySections.lean
section Source0473
-- Modified in this edition: unused plain lemmas removed; see reduction.json.
/-
Modification notice for the LogTwo project.
Derived from openai/math (Apache-2.0), revision adc7f1241b42e322a6451854ab7e4b4c146bf78a.
Original source: lean/OAI/NumberTheory/PiExponent/Cohomology/PencilCohomologySections.lean
Changes: Convert module/import declarations to the Lean 4.34 public module format.
Expose private helpers and adjust helper names where needed for module compatibility.
See ../THIRD_PARTY_NOTICES.txt for provenance and the recorded changes.
-/

namespace OAI

noncomputable section

namespace PiExponentSeshadri.Geometry

section
open AlgebraicGeometry CategoryTheory TopologicalSpace
variable {X Y : Scheme.{0}}

instance LineBundle.quasicoherent (L : LineBundle X) : L.sheaf.IsQuasicoherent := by
  let : L.sheaf.IsFinitePresentation :=
    PiExponent.GeometrySupport.LineBundleCoherent.lineBundle_isFinitePresentation L
  exact ⟨⟨(SheafOfModules.IsFinitePresentation.exists_quasicoherentData L.sheaf).choose⟩⟩

theorem LineBundle.affine_sections_finite [IsAffine X] (L : LineBundle X) :
    Module.Finite Γ(X,⊤) Γ(L.sheaf,⊤) := by
  let := PiExponent.GeometrySupport.LineBundleCoherent.lineBundle_isFinitePresentation L
  exact PiExponent.CoherentAffineFinite.affine_sections_finite L.sheaf

def LineBundle.restrict (L : LineBundle Y) (f : X ⟶ Y) [IsOpenImmersion f] : LineBundle X where
  sheaf := L.sheaf.restrict f
  locallyRankOne x := by
    obtain ⟨U,hxU,⟨e⟩⟩ := L.locallyRankOne (f x)
    let V := f ⁻¹ᵁ U
    refine ⟨V,hxU,⟨?_⟩⟩
    let e' := (Scheme.Modules.restrictFunctorComp (f ∣_ U) U.ι).app L.sheaf ≪≫
      (Scheme.Modules.restrictFunctor (f ∣_ U)).mapIso e ≪≫
      Scheme.Modules.restrictUnitIso (f ∣_ U)
    have e'' : L.sheaf.restrict (V.ι ≫ f) ≅ structureSheaf V.toScheme := by
      simpa only [V, morphismRestrict_ι, structureSheaf] using e'
    exact ((Scheme.Modules.restrictFunctorComp V.ι f).app L.sheaf).symm ≪≫ e''

end

section
open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite
open ModuleFlasque
variable {X : Scheme.{0}}

def OpenSections (M : X.Modules) (U : X.Opens) := Γ(M,U)
instance (M : X.Modules) (U : X.Opens) : AddCommGroup (OpenSections M U) :=
  inferInstanceAs (AddCommGroup Γ(M,U))
instance (M : X.Modules) (U : X.Opens) : Module Γ(X,⊤) (OpenSections M U) :=
  Module.compHom Γ(M,U) (restrictScalar X U)

abbrev schemeFreeOpen (U : X.Opens) : X.Modules :=
  freeOpen X.ringCatSheaf U

@[instance_reducible] def freeOpenHomAddCommGroup (U : X.Opens) (M : X.Modules) :
    AddCommGroup (freeOpen X.ringCatSheaf U ⟶ M) :=
  inferInstanceAs (AddCommGroup (schemeFreeOpen U ⟶ M))

attribute [local instance] freeOpenHomAddCommGroup

local instance (M : X.Modules) (U : X.Opens) :
    Module Γ(X,⊤) (freeOpen X.ringCatSheaf U ⟶ M) := sheafHomModule X _ _

def freeOpenLinearEquiv (M : X.Modules) (U : X.Opens) :
    (freeOpen X.ringCatSheaf U ⟶ M) ≃ₗ[Γ(X,⊤)] OpenSections M U where
  toEquiv := freeOpenEquiv X.ringCatSheaf M U
  map_add' := by intro f g; rfl
  map_smul' := by intro r f; rfl

def openRestriction (M : X.Modules) {U V : X.Opens} (h : U ≤ V) :
    OpenSections M V →ₗ[Γ(X,⊤)] OpenSections M U where
  toFun := M.val.map (homOfLE h).op
  map_add' := map_add _
  map_smul' := by
    intro r m
    let : Module Γ(X,V) (OpenSections M V) := (M.val.obj (op V)).isModule
    let : Module Γ(X,U) (OpenSections M U) := (M.val.obj (op U)).isModule
    change M.presheaf.map (homOfLE h).op (restrictScalar X V r • (m : Γ(M,V))) =
      restrictScalar X U r • M.presheaf.map (homOfLE h).op m
    erw [M.map_smul, restrictScalar_naturality]

lemma freeOpenLinearEquiv_naturality (M : X.Modules) {U V : X.Opens} (h : U ≤ V)
    (f : freeOpen X.ringCatSheaf V ⟶ M) :
    freeOpenLinearEquiv M U (freeOpenMap X.ringCatSheaf (homOfLE h) ≫ f) =
      openRestriction M h (freeOpenLinearEquiv M V f) :=
  freeOpenEquiv_naturality X.ringCatSheaf M _ f

end

section
open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite
variable {X Y : Scheme.{0}}

theorem quasicoherent_pushforward_iso (e : X ≅ Y) (M : X.Modules) [M.IsQuasicoherent] :
    ((Scheme.Modules.pushforward e.hom).obj M).IsQuasicoherent := by
  let N := (Scheme.Modules.pushforward e.hom).obj M
  let q : (Scheme.Modules.pushforward e.inv).obj N ≅ M :=
    (Scheme.Modules.pushforwardComp e.hom e.inv).app M ≪≫
      (Scheme.Modules.pushforwardCongr e.hom_inv_id).app M ≪≫
      (Scheme.Modules.pushforwardId X).app M
  let j : N ≅ M.restrict e.inv :=
    ((Scheme.Modules.restrictFunctorAdjCounitIso e.inv).app N).symm ≪≫
      (Scheme.Modules.restrictFunctor e.inv).mapIso q
  exact (SheafOfModules.isQuasicoherent Y.ringCatSheaf).prop_of_iso j.symm inferInstance

abbrev affineToSpecModule [IsAffine X] (M : X.Modules) :=
  (Scheme.Modules.pushforward X.toSpecΓ).obj M

instance affineToSpecModule_quasicoherent [IsAffine X] (M : X.Modules)
    [M.IsQuasicoherent] : (affineToSpecModule M).IsQuasicoherent :=
  quasicoherent_pushforward_iso X.isoSpec M

theorem affine_sections_localize [IsAffine X] (M : X.Modules) [M.IsQuasicoherent]
    (r : Γ(X,⊤)) :
    IsLocalizedModule.Away r
      (((modulesSpecToSheaf.obj (affineToSpecModule M)).obj.map
        (PrimeSpectrum.basicOpen r).leTop.op).hom) :=
  ((isIso_fromTildeΓ_iff_isLocalizing (affineToSpecModule M)).mp inferInstance) r

def affineSpecSections [IsAffine X] (M : X.Modules)
    (U : (Spec Γ(X,⊤)).Opens) :
    ((modulesSpecToSheaf.obj (affineToSpecModule M)).obj.obj (op U)) ≃ₗ[Γ(X,⊤)]
      OpenSections M (X.toSpecΓ ⁻¹ᵁ U) where
  toFun := fun x => x
  invFun := fun x => x
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' r m := by
    let : Module Γ(X,X.toSpecΓ ⁻¹ᵁ U) Γ(M,X.toSpecΓ ⁻¹ᵁ U) :=
      (M.val.obj (op (X.toSpecΓ ⁻¹ᵁ U))).isModule
    change @SMul.smul Γ(X,X.toSpecΓ ⁻¹ᵁ U) Γ(M,X.toSpecΓ ⁻¹ᵁ U) _
      ((X.toSpecΓ.app U).hom
        ((Spec Γ(X,⊤)).presheaf.map U.leTop.op ((Scheme.ΓSpecIso Γ(X,⊤)).inv r))) m =
      @SMul.smul Γ(X,X.toSpecΓ ⁻¹ᵁ U) Γ(M,X.toSpecΓ ⁻¹ᵁ U) _
        (restrictScalar X (X.toSpecΓ ⁻¹ᵁ U) r) m
    congr 1
    have h := congrArg (fun f : Γ(Spec Γ(X,⊤),⊤) ⟶ Γ(X,X.toSpecΓ ⁻¹ᵁ U) =>
      f ((Scheme.ΓSpecIso Γ(X,⊤)).inv r)) (X.toSpecΓ.naturality U.leTop.op)
    simp only [CommRingCat.comp_apply, Scheme.toSpecΓ_appTop] at h
    change _ = restrictScalar X (X.toSpecΓ ⁻¹ᵁ U)
      ((Scheme.ΓSpecIso Γ(X,⊤)).hom ((Scheme.ΓSpecIso Γ(X,⊤)).inv r)) at h
    rw [(Scheme.ΓSpecIso Γ(X,⊤)).inv_hom_id_apply r] at h
    exact h

def openSectionsCongr (M : X.Modules) {U V : X.Opens} (h : U = V) :
    OpenSections M U ≃ₗ[Γ(X,⊤)] OpenSections M V := by
  subst V
  exact LinearEquiv.refl _ _

lemma openSectionsCongr_restriction (M : X.Modules) {U V : X.Opens} (h : U = V)
    (m : OpenSections M ⊤) :
    openSectionsCongr M h (openRestriction M (show U ≤ ⊤ from le_top) m) = openRestriction M (show V ≤ ⊤ from le_top) m := by
  subst V
  rfl

theorem affine_openRestriction_localize [IsAffine X] (M : X.Modules) [M.IsQuasicoherent]
    (r : Γ(X,⊤)) :
    IsLocalizedModule.Away r (openRestriction M (X.basicOpen_le r)) := by
  let F := modulesSpecToSheaf.obj (affineToSpecModule M)
  let f := (F.obj.map (PrimeSpectrum.basicOpen r).leTop.op).hom
  let e0 : (F.obj.obj (op ⊤)) ≃ₗ[Γ(X,⊤)] OpenSections M ⊤ := affineSpecSections M ⊤
  let e1 := (affineSpecSections M (PrimeSpectrum.basicOpen r)).trans
    (openSectionsCongr M (Scheme.toSpecΓ_preimage_basicOpen X r))
  have hf : IsLocalizedModule.Away r f := affine_sections_localize M r
  have hq : IsLocalizedModule.Away r (e1.toLinearMap ∘ₗ f ∘ₗ e0.symm.toLinearMap) := by
    let := hf
    let := IsLocalizedModule.of_linearEquiv (.powers r) f e1
    exact IsLocalizedModule.of_linearEquiv_right (.powers r) (e1.toLinearMap ∘ₗ f) e0.symm
  have he : e1.toLinearMap ∘ₗ f ∘ₗ e0.symm.toLinearMap =
      openRestriction M (X.basicOpen_le r) := by
    ext m
    exact openSectionsCongr_restriction M (Scheme.toSpecΓ_preimage_basicOpen X r) m
  rwa [he] at hq

theorem affine_basicOpen_denominators [IsAffine X] (M : X.Modules) [M.IsQuasicoherent]
    (r : Γ(X,⊤)) (x : OpenSections M (X.basicOpen r)) :
    ∃ n : ℕ, ∃ y : OpenSections M ⊤,
      openRestriction M (X.basicOpen_le r) y = r^n • x := by
  let f := openRestriction M (X.basicOpen_le r)
  let : IsLocalizedModule.Away r f := affine_openRestriction_localize M r
  obtain ⟨n,y,hy⟩ := (inferInstance : IsLocalizedModule.Away r f).surj _ _ x
  exact ⟨n,y,hy.symm⟩

def openTopSections (M : X.Modules) :
    letI : Module Γ(X,⊤) Γ(M,⊤) := (M.val.obj (op ⊤)).isModule
    OpenSections M ⊤ ≃ₗ[Γ(X,⊤)] Γ(M,⊤) := by
  letI : Module Γ(X,⊤) Γ(M,⊤) := (M.val.obj (op ⊤)).isModule
  refine { toFun := fun x => x
           invFun := fun x => x
           left_inv := fun _ => rfl
           right_inv := fun _ => rfl
           map_add' := fun _ _ => rfl
           map_smul' := ?_ }
  intro r m
  change @SMul.smul Γ(X,⊤) Γ(M,⊤) _ (restrictScalar X ⊤ r) m =
    @SMul.smul Γ(X,⊤) Γ(M,⊤) _ r m
  congr 1
  change (X.presheaf.map (𝟙 (op ⊤))) r = r
  rw [X.presheaf.map_id]
  rfl

theorem LineBundle.affine_openSections_finite [IsAffine X] (L : LineBundle X) :
    Module.Finite Γ(X,⊤) (OpenSections L.sheaf ⊤) := by
  let : Module Γ(X,⊤) Γ(L.sheaf,⊤) := (L.sheaf.val.obj (op ⊤)).isModule
  let := L.affine_sections_finite
  exact Module.Finite.of_surjective (openTopSections L.sheaf).symm.toLinearMap
    (openTopSections L.sheaf).symm.surjective

lemma restrictScalar_appIso (f : Y ⟶ X) [IsOpenImmersion f] (U : Y.Opens)
    (r : Γ(X,⊤)) :
    (f.appIso U).inv (restrictScalar Y U (f.appTop r)) =
      restrictScalar X (f ''ᵁ U) r := by
  have h := congrArg (fun g : Γ(X,⊤) ⟶ Γ(X,f ''ᵁ U) => g r)
    (Scheme.Hom.appLE_appIso_inv f (U := ⊤) (V := U) (by simp))
  change (f.appIso U).inv ((f.appLE ⊤ U (by simp)) r) = _ at h
  have he : f.appLE ⊤ U (by simp) = f.appTop ≫ Y.presheaf.map U.leTop.op := by
    erw [Scheme.Hom.appTop, Scheme.Hom.app_eq_appLE, Scheme.Hom.appLE_map]
  rw [he] at h
  exact h

def restrictedOpenSections (M : X.Modules) (f : Y ⟶ X) [IsOpenImmersion f]
    (U : Y.Opens) :
    letI := Module.compHom (OpenSections (M.restrict f) U) f.appTop.hom
    OpenSections (M.restrict f) U ≃ₗ[Γ(X,⊤)] OpenSections M (f ''ᵁ U) := by
  letI := Module.compHom (OpenSections (M.restrict f) U) f.appTop.hom
  letI : Module Γ(X,f ''ᵁ U) Γ(M,f ''ᵁ U) := (M.val.obj (op (f ''ᵁ U))).isModule
  refine { toFun := fun x => x
           invFun := fun x => x
           left_inv := fun _ => rfl
           right_inv := fun _ => rfl
           map_add' := fun _ _ => rfl
           map_smul' := ?_ }
  intro r m
  change @SMul.smul Γ(X,f ''ᵁ U) Γ(M,f ''ᵁ U) _
      ((f.appIso U).inv (restrictScalar Y U (f.appTop r))) m =
    @SMul.smul Γ(X,f ''ᵁ U) Γ(M,f ''ᵁ U) _ (restrictScalar X (f ''ᵁ U) r) m
  rw [restrictScalar_appIso]

lemma restrictedOpenSections_naturality (M : X.Modules) (f : Y ⟶ X) [IsOpenImmersion f]
    {U V : Y.Opens} (h : U ≤ V) (m : OpenSections (M.restrict f) V) :
    restrictedOpenSections M f U (openRestriction (M.restrict f) h m) =
      openRestriction M (f.image_mono h) (restrictedOpenSections M f V m) := rfl

end

open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite
variable {X Y Z : Scheme.{0}}

def moduleIsoSections {M N : X.Modules} (e : M ≅ N) (U : X.Opens) :
    OpenSections M U ≃ₗ[Γ(X,⊤)] OpenSections N U where
  toFun := e.hom.val.app (op U)
  invFun := e.inv.val.app (op U)
  left_inv m := by
    have h := congrArg (fun f : M ⟶ M => f.val.app (op U) m) e.hom_inv_id
    exact h
  right_inv m := by
    have h := congrArg (fun f : N ⟶ N => f.val.app (op U) m) e.inv_hom_id
    exact h
  map_add' := map_add _
  map_smul' r m := (e.hom.val.app (op U)).hom.map_smul (restrictScalar X U r) m

def openImmersionTop (M : X.Modules) (f : Y ⟶ X) [IsOpenImmersion f] :
    letI := Module.compHom (OpenSections (M.restrict f) ⊤) f.appTop.hom
    OpenSections M ⊤ →ₗ[Γ(X,⊤)] OpenSections (M.restrict f) ⊤ := by
  letI := Module.compHom (OpenSections (M.restrict f) ⊤) f.appTop.hom
  exact (restrictedOpenSections M f ⊤).symm.toLinearMap ∘ₗ
    openRestriction M (show f ''ᵁ ⊤ ≤ ⊤ from le_top)

theorem openImmersionTop_localize [IsAffine X] (M : X.Modules) [M.IsQuasicoherent]
    (f : Y ⟶ X) [IsOpenImmersion f] (t : Γ(X,⊤))
    (hf : f.opensRange = X.basicOpen t) :
    letI := Module.compHom (OpenSections (M.restrict f) ⊤) f.appTop.hom
    IsLocalizedModule.Away t (openImmersionTop M f) := by
  let := Module.compHom (OpenSections (M.restrict f) ⊤) f.appTop.hom
  have he : X.basicOpen t = f ''ᵁ (⊤ : Y.Opens) :=
    hf.symm.trans (Scheme.Hom.image_top_eq_opensRange f).symm
  let e := (openSectionsCongr M he).trans (restrictedOpenSections M f ⊤).symm
  let g := openRestriction M (X.basicOpen_le t)
  let : IsLocalizedModule.Away t g := affine_openRestriction_localize M t
  have h := IsLocalizedModule.of_linearEquiv (.powers t) g e
  have hp : e.toLinearMap ∘ₗ g = openImmersionTop M f := by
    ext m
    change (restrictedOpenSections M f ⊤).symm
      (openSectionsCongr M he (openRestriction M (X.basicOpen_le t) m)) = _
    rw [openSectionsCongr_restriction]
    rfl
  rwa [hp] at h

end PiExponentSeshadri.Geometry

end

end OAI
end Source0473

-- Source: OAI/NumberTheory/PiExponent/Cohomology/PencilCohomologyCharts.lean
section Source0474
-- Modified in this edition: unused plain lemmas removed; see reduction.json.
/-
Modification notice for the LogTwo project.
Derived from openai/math (Apache-2.0), revision adc7f1241b42e322a6451854ab7e4b4c146bf78a.
Original source: lean/OAI/NumberTheory/PiExponent/Cohomology/PencilCohomologyCharts.lean
Changes: Convert module/import declarations to the Lean 4.34 public module format.
See ../THIRD_PARTY_NOTICES.txt for provenance and the recorded changes.
-/

namespace OAI

noncomputable section

namespace PiExponentSeshadri.Geometry.BaseSections

section
open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite
variable {K : Type} [CommRing K] {X Y : Scheme.{0}}

def Sections (_k : K →+* Γ(X,⊤)) (M : X.Modules) (U : X.Opens) := OpenSections M U
instance (k : K →+* Γ(X,⊤)) (M : X.Modules) (U : X.Opens) :
    AddCommGroup (Sections k M U) := inferInstanceAs (AddCommGroup (OpenSections M U))
instance globalModule (k : K →+* Γ(X,⊤)) (M : X.Modules) (U : X.Opens) :
    Module Γ(X,⊤) (Sections k M U) := inferInstanceAs (Module Γ(X,⊤) (OpenSections M U))
instance baseModule (k : K →+* Γ(X,⊤)) (M : X.Modules) (U : X.Opens) :
    Module K (Sections k M U) := Module.compHom (OpenSections M U) k

def res (k : K →+* Γ(X,⊤)) (M : X.Modules) {U V : X.Opens} (h : U ≤ V) :
    Sections k M V →ₗ[K] Sections k M U where
  toFun := openRestriction M h
  map_add' := map_add _
  map_smul' r m := (openRestriction M h).map_smul (k r) m

def congr (k : K →+* Γ(X,⊤)) (M : X.Modules) {U V : X.Opens} (h : U = V) :
    Sections k M U ≃ₗ[K] Sections k M V := by
  subst V
  exact LinearEquiv.refl K _

lemma congr_naturality (k : K →+* Γ(X,⊤)) (M : X.Modules)
    {U V U' V' : X.Opens} (eU : U = U') (eV : V = V')
    (h : U ≤ V) (h' : U' ≤ V') (m : Sections k M V) :
    congr k M eU (res k M h m) = res k M h' (congr k M eV m) := by
  subst U' V'
  rfl

def restrictEquiv (k : K →+* Γ(X,⊤)) (M : X.Modules)
    (f : Y ⟶ X) [IsOpenImmersion f] (U : Y.Opens) :
    Sections (f.appTop.hom.comp k) (M.restrict f) U ≃ₗ[K]
      Sections k M (f ''ᵁ U) where
  toFun := fun x => x
  invFun := fun x => x
  left_inv := fun _ => rfl
  right_inv := fun _ => rfl
  map_add' := fun _ _ => rfl
  map_smul' r m := (restrictedOpenSections M f U).map_smul (k r) m

lemma restrictEquiv_res (k : K →+* Γ(X,⊤)) (M : X.Modules)
    (f : Y ⟶ X) [IsOpenImmersion f] {U V : Y.Opens} (h : U ≤ V)
    (m : Sections (f.appTop.hom.comp k) (M.restrict f) V) :
    restrictEquiv k M f U (res _ _ h m) =
      res k M (f.image_mono h) (restrictEquiv k M f V m) := rfl

lemma chart_image_top (U : X.Opens) : U.ι ''ᵁ (⊤ : U.toScheme.Opens) = U := by
  rw [Scheme.Hom.image_top_eq_opensRange, Scheme.Opens.opensRange_ι]

lemma chart_image_preimage (U V : X.Opens) : U.ι ''ᵁ U.ι ⁻¹ᵁ V = U ⊓ V := by
  rw [Scheme.Hom.image_preimage_eq_opensRange_inf, Scheme.Opens.opensRange_ι]

def chartTop (k : K →+* Γ(X,⊤)) (M : X.Modules) (U : X.Opens) :
    Sections (U.ι.appTop.hom.comp k) (M.restrict U.ι) ⊤ ≃ₗ[K] Sections k M U :=
  (restrictEquiv k M U.ι ⊤).trans (congr k M (chart_image_top U))

def chartOverlap (k : K →+* Γ(X,⊤)) (M : X.Modules) (U V : X.Opens) :
    Sections (U.ι.appTop.hom.comp k) (M.restrict U.ι) (U.ι ⁻¹ᵁ V) ≃ₗ[K]
      Sections k M (U ⊓ V) :=
  (restrictEquiv k M U.ι (U.ι ⁻¹ᵁ V)).trans
    (congr k M (chart_image_preimage U V))

lemma chartRestriction (k : K →+* Γ(X,⊤)) (M : X.Modules) (U V : X.Opens)
    (m : Sections (U.ι.appTop.hom.comp k) (M.restrict U.ι) ⊤) :
    chartOverlap k M U V (res _ _ le_top m) =
      res k M (show U ⊓ V ≤ U from inf_le_left) (chartTop k M U m) := by
  change congr k M (chart_image_preimage U V)
    (restrictEquiv k M U.ι (U.ι ⁻¹ᵁ V) (res _ _ le_top m)) = _
  rw [restrictEquiv_res]
  exact congr_naturality k M (chart_image_preimage U V) (chart_image_top U)
    _ _ _

end

open AlgebraicGeometry CategoryTheory TopologicalSpace
open scoped Polynomial
variable {K : Type} [CommRing K] {X : Scheme.{0}}

@[instance_reducible]
def polynomialModule (k : K →+* Γ(X,⊤)) (t : Γ(X,⊤)) (M : X.Modules) (U : X.Opens) :
    Module K[X] (Sections k M U) :=
  Module.compHom (Sections k M U) (Polynomial.eval₂RingHom k t)

theorem polynomialTower (k : K →+* Γ(X,⊤)) (t : Γ(X,⊤)) (M : X.Modules) (U : X.Opens) :
    letI := polynomialModule k t M U
    IsScalarTower K K[X] (Sections k M U) := by
  let := polynomialModule k t M U
  apply IsScalarTower.of_algebraMap_smul
  intro r m
  change (Polynomial.eval₂RingHom k t) (Polynomial.C r) • (m : OpenSections M U) =
    k r • (m : OpenSections M U)
  simp

def polynomialRes (k : K →+* Γ(X,⊤)) (t : Γ(X,⊤)) (M : X.Modules)
    {U V : X.Opens} (h : U ≤ V) :
    letI := polynomialModule k t M U
    letI := polynomialModule k t M V
    Sections k M V →ₗ[K[X]] Sections k M U := by
  letI := polynomialModule k t M U
  letI := polynomialModule k t M V
  exact { toFun := openRestriction M h
          map_add' := map_add _
          map_smul' := fun r m => (openRestriction M h).map_smul _ m }

theorem polynomial_finite [IsAffine X] (k : K →+* Γ(X,⊤))
    (t : Γ(X,⊤)) (L : LineBundle X)
    (h : (Polynomial.eval₂RingHom k t).Finite) :
    letI := polynomialModule k t L.sheaf ⊤
    Module.Finite K[X] (Sections k L.sheaf ⊤) := by
  let : Algebra K[X] Γ(X,⊤) := (Polynomial.eval₂RingHom k t).toAlgebra
  let : Module.Finite K[X] Γ(X,⊤) := h
  let := polynomialModule k t L.sheaf ⊤
  let : Module.Finite Γ(X,⊤) (Sections k L.sheaf ⊤) := L.affine_openSections_finite
  let : IsScalarTower K[X] Γ(X,⊤) (Sections k L.sheaf ⊤) :=
    .of_algebraMap_smul (fun _ _ => rfl)
  exact Module.Finite.trans Γ(X,⊤) (Sections k L.sheaf ⊤)

end PiExponentSeshadri.Geometry.BaseSections

namespace PiExponentSeshadri.Geometry
open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite
variable {X Y : Scheme.{0}}

def chartModuleEquiv (M : X.Modules) (f : Y ⟶ X) [IsOpenImmersion f]
    {N : Y.Modules} (e : M.restrict f ≅ N) :
    letI := Module.compHom (OpenSections (M.restrict f) ⊤) f.appTop.hom
    letI := Module.compHom (OpenSections N ⊤) f.appTop.hom
    OpenSections (M.restrict f) ⊤ ≃ₗ[Γ(X,⊤)] OpenSections N ⊤ := by
  letI := Module.compHom (OpenSections (M.restrict f) ⊤) f.appTop.hom
  letI := Module.compHom (OpenSections N ⊤) f.appTop.hom
  let E := moduleIsoSections e ⊤
  exact { E.toEquiv with
    map_add' := E.map_add
    map_smul' := fun r m => E.map_smul (f.appTop r) m }

def chartModuleMap (M : X.Modules) (f : Y ⟶ X) [IsOpenImmersion f]
    {N : Y.Modules} (e : M.restrict f ≅ N) :
    letI := Module.compHom (OpenSections N ⊤) f.appTop.hom
    OpenSections M ⊤ →ₗ[Γ(X,⊤)] OpenSections N ⊤ := by
  letI := Module.compHom (OpenSections N ⊤) f.appTop.hom
  letI := Module.compHom (OpenSections (M.restrict f) ⊤) f.appTop.hom
  exact (chartModuleEquiv M f e).toLinearMap ∘ₗ openImmersionTop M f

theorem chartModuleMap_localize [IsAffine X] (M : X.Modules) [M.IsQuasicoherent]
    (f : Y ⟶ X) [IsOpenImmersion f] {N : Y.Modules} (e : M.restrict f ≅ N)
    (t : Γ(X,⊤)) (ht : f.opensRange = X.basicOpen t) :
    letI := Module.compHom (OpenSections N ⊤) f.appTop.hom
    IsLocalizedModule.Away t (chartModuleMap M f e) := by
  let := Module.compHom (OpenSections (M.restrict f) ⊤) f.appTop.hom
  let := Module.compHom (OpenSections N ⊤) f.appTop.hom
  let : IsLocalizedModule.Away t (openImmersionTop M f) :=
    openImmersionTop_localize M f t ht
  exact IsLocalizedModule.of_linearEquiv (.powers t) (openImmersionTop M f)
    (chartModuleEquiv M f e)

namespace BaseSections
variable {K : Type} [CommRing K]

def chartMap (kX : K →+* Γ(X,⊤)) (kY : K →+* Γ(Y,⊤))
    (f : Y ⟶ X) [IsOpenImmersion f] (hk : f.appTop.hom.comp kX = kY)
    (M : X.Modules) {N : Y.Modules} (e : M.restrict f ≅ N) :
    Sections kX M ⊤ →ₗ[K] Sections kY N ⊤ := by
  letI := Module.compHom (OpenSections N ⊤) f.appTop.hom
  refine { toFun := chartModuleMap M f e
           map_add' := (chartModuleMap M f e).map_add
           map_smul' := ?_ }
  intro r m
  have h := (chartModuleMap M f e).map_smul (kX r) m
  change _ = (f.appTop (kX r)) • (chartModuleMap M f e m) at h
  exact h.trans (congrArg (fun c : Γ(Y,⊤) => c • chartModuleMap M f e m)
    (RingHom.congr_fun hk r))

lemma chartMap_smul (kX : K →+* Γ(X,⊤)) (kY : K →+* Γ(Y,⊤))
    (f : Y ⟶ X) [IsOpenImmersion f] (hk : f.appTop.hom.comp kX = kY)
    (M : X.Modules) {N : Y.Modules} (e : M.restrict f ≅ N)
    (r : Γ(X,⊤)) (m : Sections kX M ⊤) :
    chartMap kX kY f hk M e (r • m) = f.appTop r • chartMap kX kY f hk M e m := by
  let := Module.compHom (OpenSections N ⊤) f.appTop.hom
  exact (chartModuleMap M f e).map_smul r m

end BaseSections
end PiExponentSeshadri.Geometry

namespace PiExponentSeshadri.Geometry.BaseSections
open AlgebraicGeometry CategoryTheory TopologicalSpace
open scoped Polynomial
variable {K : Type} [CommRing K] {X Y : Scheme.{0}}

lemma eval_transport (kX : K →+* Γ(X,⊤)) (kY : K →+* Γ(Y,⊤))
    (f : Y ⟶ X) (hk : f.appTop.hom.comp kX = kY) (t : Γ(X,⊤))
    (p : K[X]) : f.appTop ((Polynomial.eval₂RingHom kX t) p) =
      (Polynomial.eval₂RingHom kY (f.appTop t)) p := by
  have h : f.appTop.hom.comp (Polynomial.eval₂RingHom kX t) =
      Polynomial.eval₂RingHom kY (f.appTop t) := by
    apply Polynomial.ringHom_ext
    · intro r
      simpa using RingHom.congr_fun hk r
    · simp
  exact RingHom.congr_fun h p

def chartPolynomialMap (kX : K →+* Γ(X,⊤)) (kY : K →+* Γ(Y,⊤))
    (f : Y ⟶ X) [IsOpenImmersion f] (hk : f.appTop.hom.comp kX = kY)
    (M : X.Modules) {N : Y.Modules} (e : M.restrict f ≅ N) (t : Γ(X,⊤)) :
    letI := polynomialModule kX t M ⊤
    letI := polynomialModule kY (f.appTop t) N ⊤
    Sections kX M ⊤ →ₗ[K[X]] Sections kY N ⊤ := by
  letI := polynomialModule kX t M ⊤
  letI := polynomialModule kY (f.appTop t) N ⊤
  refine { toFun := chartMap kX kY f hk M e
           map_add' := (chartMap kX kY f hk M e).map_add
           map_smul' := ?_ }
  intro p m
  change chartMap kX kY f hk M e ((Polynomial.eval₂RingHom kX t) p • m) =
    (Polynomial.eval₂RingHom kY (f.appTop t)) p • chartMap kX kY f hk M e m
  rw [chartMap_smul, eval_transport kX kY f hk]

theorem chartPolynomialMap_localize [IsAffine X]
    (kX : K →+* Γ(X,⊤)) (kY : K →+* Γ(Y,⊤))
    (f : Y ⟶ X) [IsOpenImmersion f] (hk : f.appTop.hom.comp kX = kY)
    (M : X.Modules) [M.IsQuasicoherent] {N : Y.Modules} (e : M.restrict f ≅ N)
    (t : Γ(X,⊤)) (ht : f.opensRange = X.basicOpen t) :
    letI := polynomialModule kX t M ⊤
    letI := polynomialModule kY (f.appTop t) N ⊤
    IsLocalizedModule.Away (Polynomial.X : K[X])
      (chartPolynomialMap kX kY f hk M e t) := by
  let : Algebra K[X] Γ(X,⊤) := (Polynomial.eval₂RingHom kX t).toAlgebra
  let := polynomialModule kX t M ⊤
  let := polynomialModule kY (f.appTop t) N ⊤
  let : Module Γ(X,⊤) (Sections kY N ⊤) :=
    Module.compHom (OpenSections N ⊤) f.appTop.hom
  let : IsScalarTower K[X] Γ(X,⊤) (Sections kX M ⊤) :=
    .of_algebraMap_smul (fun _ _ => rfl)
  let : IsScalarTower K[X] Γ(X,⊤) (Sections kY N ⊤) :=
    .of_algebraMap_smul (fun p m => by
      change f.appTop ((Polynomial.eval₂RingHom kX t) p) • (m : OpenSections N ⊤) =
        (Polynomial.eval₂RingHom kY (f.appTop t)) p • (m : OpenSections N ⊤)
      rw [eval_transport kX kY f hk])
  let F : Sections kX M ⊤ →ₗ[Γ(X,⊤)] Sections kY N ⊤ := chartModuleMap M f e
  have he : algebraMap K[X] Γ(X,⊤) Polynomial.X = t := by
    change (Polynomial.eval₂RingHom kX t) Polynomial.X = t
    simp
  let : IsLocalizedModule (.powers (algebraMap K[X] Γ(X,⊤) Polynomial.X)) F := by
    rw [he]
    exact chartModuleMap_localize M f e t ht
  have h := IsLocalizedModule.restrictScalars_powers (Polynomial.X : K[X]) F
  exact h
end PiExponentSeshadri.Geometry.BaseSections

end

end OAI
end Source0474

/- Generated rc4 checkpoint for LogTwo.
Modified from the reduced edition: new imports, separate module compilation,
and synchronous elaboration. Original source blocks and notices are retained.
See ../../../THIRD_PARTY_NOTICES.txt and ../../reduction.json.
-/
module
public import LogTwoCheckpoints.Part000
public import LogTwoCheckpoints.Part001
public import LogTwoCheckpoints.Part003
public import LogTwoCheckpoints.Part004
public import LogTwoCheckpoints.Part011
public import LogTwoCheckpoints.Part012
public import LogTwoCheckpoints.Part013
public import LogTwoCheckpoints.Part014
public import LogTwoCheckpoints.Part015
public import LogTwoCheckpoints.Part016
public import LogTwoCheckpoints.Part017
public import LogTwoCheckpoints.Part018
public import LogTwoCheckpoints.Part019
public import LogTwoCheckpoints.Part020
public import LogTwoCheckpoints.Part021
public import LogTwoCheckpoints.Part022
public import LogTwoCheckpoints.Part023
public import Batteries.Logic
public import Mathlib.Algebra.Category.Grp.Zero
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.EpiMono
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.PullbackFree
public import Mathlib.Algebra.Homology.DerivedCategory.Ext.Linear
public import Mathlib.Algebra.Module.Submodule.Union
public import Mathlib.AlgebraicGeometry.Artinian
public import Mathlib.AlgebraicGeometry.FunctionField
public import Mathlib.AlgebraicGeometry.Modules.Tilde
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.AlgebraicGeometry.Morphisms.SchemeTheoreticallyDominant
public import Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Basic
public import Mathlib.Analysis.Complex.Polynomial.Basic
public import Mathlib.Data.Opposite
public import Mathlib.Data.SetLike.Basic
public import Mathlib.RingTheory.Ideal.AssociatedPrime.Finiteness
public import Mathlib.RingTheory.MvPolynomial.Homogeneous
public import Mathlib.Topology.Sheaves.Flasque
public import Mathlib.Topology.Sheaves.LocallySurjective
@[expose] public section
set_option Elab.async false

-- Source: OAI/NumberTheory/PiExponent/Cohomology/AmpleCohomologyFinite.lean
section Source0600
/-
Modification notice for the LogTwo project.
Derived from openai/math (Apache-2.0), revision adc7f1241b42e322a6451854ab7e4b4c146bf78a.
Original source: lean/OAI/NumberTheory/PiExponent/Cohomology/AmpleCohomologyFinite.lean
Changes: Convert module/import declarations to the Lean 4.34 public module format.
See ../THIRD_PARTY_NOTICES.txt for provenance and the recorded changes.
-/

namespace OAI

noncomputable section
namespace PiExponent.AmpleCohomologyFinite
open AlgebraicGeometry CategoryTheory TopologicalSpace
open PiExponentSeshadri.Geometry PiExponentSeshadri.Projective
attribute [local instance] MvPolynomial.gradedAlgebra
variable {X : Scheme.{0}}

theorem projectiveBase_eq_polynomialProjectiveProjection
    {R σ : Type} [CommRing R] :
    projectiveBase (K := R) (σ := σ) = polynomialProjectiveProjection R σ := by
  rfl

theorem cohomology_finite_of_ample [Nonempty X]
    (p : X ⟶ Spec (CommRingCat.of ℂ)) [IsProper p]
    (H : LineBundle X) (hH : H.IsAmple)
    (M : X.Modules) [M.IsFinitePresentation] (q : ℕ) :
    letI := Module.compHom (cohomology M q) (baseScalars p)
    FiniteDimensional ℂ (cohomology M q) := by
  classical
  let : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian p
  let : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace p
  let : IsNoetherian X := ⟨⟩
  obtain ⟨d, hd, σ, hσ, s, hs, hclosed⟩ := H.ample_projective_sections_noetherian p hH
  let : Fintype σ := hσ
  have : Nonempty σ := by
    obtain ⟨x⟩ : Nonempty X := inferInstance
    have hx : x ∈ (⨆ i, PiExponentSeshadri.SectionOpens.isoOpen (s i)) := by
      rw [hs]
      trivial
    obtain ⟨i, -⟩ := Opens.mem_iSup.mp hx
    exact ⟨i⟩
  let k : ℂ →+* Γ(X, ⊤) := baseScalars p
  let i : X ⟶ ProjectiveO1.projectiveSpace ℂ σ := sectionsMorphism k s hs
  have : IsClosedImmersion i := hclosed
  have hover : i ≫ polynomialProjectiveProjection ℂ σ = p := by
    rw [← projectiveBase_eq_polynomialProjectiveProjection]
    exact (sectionsMorphism_over k s hs).trans (toSpec_scalarMap p)
  exact ProjectiveFiniteCoordinates.projectiveOver_cohomology_finite p i hover M q

end PiExponent.AmpleCohomologyFinite

end

end OAI
end Source0600

-- Source: OAI/NumberTheory/PiExponent/Cohomology/CurveTwoAffineVanishing.lean
section Source0601
/-
Modification notice for the LogTwo project.
Derived from openai/math (Apache-2.0), revision adc7f1241b42e322a6451854ab7e4b4c146bf78a.
Original source: lean/OAI/NumberTheory/PiExponent/Cohomology/CurveTwoAffineVanishing.lean
Changes: Convert module/import declarations to the Lean 4.34 public module format.
See ../THIRD_PARTY_NOTICES.txt for provenance and the recorded changes.
-/

namespace OAI

noncomputable section
namespace PiExponent.CurveTwoAffineVanishing
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace
open PiExponentSeshadri.Geometry
variable {X : Scheme.{0}} [IsNoetherian X]
  [IsAffineHom (pullback.diagonal (terminal.from X))]

theorem cohomology_subsingleton (U V : X.Opens) (hU : IsAffineOpen U)
    (hV : IsAffineOpen V) (hcover : U ⊔ V = ⊤)
    (M : X.Modules) [M.IsQuasicoherent] (n : ℕ) (hn : 2 ≤ n) :
    Subsingleton (cohomology M n) := by
  let D : Fin 2 → X.Opens := ![U,V]
  have hD : ∀ i, IsAffineOpen (D i) := by
    intro i
    fin_cases i
    · exact hU
    · exact hV
  have hc : (⨆ i, D i) = ⊤ := by
    calc
      (⨆ i, D i) = U ⊔ V := le_antisymm
        (iSup_le (fun i => by
          fin_cases i
          · exact le_sup_left
          · exact le_sup_right))
        (sup_le (le_iSup D 0) (le_iSup D 1))
      _ = ⊤ := hcover
  exact ⟨fun x y =>
    (SerreVanishing.ext_eq_zero_of_affine_cover 2 (by decide) D hD hc M n hn x).trans
      (SerreVanishing.ext_eq_zero_of_affine_cover 2 (by decide) D hD hc M n hn y).symm⟩

end PiExponent.CurveTwoAffineVanishing

end

end OAI
end Source0601

-- Source: OAI/NumberTheory/PiExponent/Cohomology/CurveFinitePushforwardCohomology.lean
section Source0602
/-
Modification notice for the LogTwo project.
Derived from openai/math (Apache-2.0), revision adc7f1241b42e322a6451854ab7e4b4c146bf78a.
Original source: lean/OAI/NumberTheory/PiExponent/Cohomology/CurveFinitePushforwardCohomology.lean
Changes: Convert module/import declarations to the Lean 4.34 public module format.
See ../THIRD_PARTY_NOTICES.txt for provenance and the recorded changes.
-/

namespace OAI

namespace PiExponent.CurveFinitePushforwardCohomology
noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian TopologicalSpace Opposite
open PiExponentSeshadri.Geometry PiExponentSeshadri.Geometry.BaseSections

variable {K : Type} [Field K] {X Y : Scheme.{0}}

def sectionsEquiv (f : Y ⟶ X) (k : K →+* Γ(X,⊤)) (M : Y.Modules) (U : X.Opens) :
    Sections k ((Scheme.Modules.pushforward f).obj M) U ≃ₗ[K]
      Sections (f.appTop.hom.comp k) M (f ⁻¹ᵁ U) where
  toFun := fun x => x
  invFun := fun x => x
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' r m := by
    change Γ(M,f ⁻¹ᵁ U) at m
    let : Module Γ(Y,f ⁻¹ᵁ U) Γ(M,f ⁻¹ᵁ U) := (M.val.obj (op (f ⁻¹ᵁ U))).isModule
    change f.app U (restrictScalar X U (k r)) • (m : Γ(M,f ⁻¹ᵁ U)) =
      restrictScalar Y (f ⁻¹ᵁ U) (f.appTop (k r)) • m
    congr 1
    exact CategoryTheory.congr_fun (f.naturality (homOfLE le_top).op) (k r)

lemma sectionsEquiv_image (f : Y ⟶ X) (k : K →+* Γ(X,⊤)) (M : Y.Modules)
    (U V : X.Opens) :
    (twoBaseImage k ((Scheme.Modules.pushforward f).obj M) U V).map
        (sectionsEquiv f k M (U ⊓ V)).toLinearMap =
      twoBaseImage (f.appTop.hom.comp k) M (f ⁻¹ᵁ U) (f ⁻¹ᵁ V) := by
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩
    simp only [SetLike.mem_coe, twoBaseImage] at hy ⊢
    obtain ⟨a, ha, b, hb, h⟩ :=
      (Submodule.mem_sup (R := K)
        (M := Sections k ((Scheme.Modules.pushforward f).obj M) (U ⊓ V))).mp hy
    exact (Submodule.mem_sup (R := K)
      (M := Sections (f.appTop.hom.comp k) M ((f ⁻¹ᵁ U) ⊓ (f ⁻¹ᵁ V)))).mpr
      ⟨a, ha, b, hb, h⟩
  · intro hx
    refine ⟨x, ?_, rfl⟩
    simp only [twoBaseImage] at hx ⊢
    obtain ⟨a, ha, b, hb, h⟩ :=
      (Submodule.mem_sup (R := K)
        (M := Sections (f.appTop.hom.comp k) M ((f ⁻¹ᵁ U) ⊓ (f ⁻¹ᵁ V)))).mp hx
    exact (Submodule.mem_sup (R := K)
      (M := Sections k ((Scheme.Modules.pushforward f).obj M) (U ⊓ V))).mpr
      ⟨a, ha, b, hb, h⟩

def cohomologyOneEquiv (f : Y ⟶ X) [IsFinite f]
    [IsNoetherian X] [IsNoetherian Y] (k : K →+* Γ(X,⊤))
    (M : Y.Modules) [M.IsQuasicoherent]
    [((Scheme.Modules.pushforward f).obj M).IsQuasicoherent]
    (U V : X.Opens) (hU : IsAffineOpen U) (hV : IsAffineOpen V)
    (hcover : U ⊔ V = ⊤) :
    letI := Module.compHom (cohomology M 1) (f.appTop.hom.comp k)
    letI := Module.compHom (cohomology ((Scheme.Modules.pushforward f).obj M) 1) k
    cohomology M 1 ≃ₗ[K] cohomology ((Scheme.Modules.pushforward f).obj M) 1 := by
  letI := Module.compHom (cohomology M 1) (f.appTop.hom.comp k)
  letI := Module.compHom (cohomology ((Scheme.Modules.pushforward f).obj M) 1) k
  have hpre : (f ⁻¹ᵁ U) ⊔ (f ⁻¹ᵁ V) = ⊤ := by
    change f ⁻¹ᵁ (U ⊔ V) = ⊤
    rw [hcover, Scheme.Hom.preimage_top]
  let eY := twoBaseCohomologyOne (f.appTop.hom.comp k) M (f ⁻¹ᵁ U) (f ⁻¹ᵁ V)
    (hU.preimage f) (hV.preimage f) hpre
  let eX := twoBaseCohomologyOne k ((Scheme.Modules.pushforward f).obj M) U V hU hV hcover
  let eSections : Sections k ((Scheme.Modules.pushforward f).obj M) (U ⊓ V) ≃ₗ[K]
      Sections (f.appTop.hom.comp k) M ((f ⁻¹ᵁ U) ⊓ (f ⁻¹ᵁ V)) :=
    sectionsEquiv f k M (U ⊓ V)
  let e := Submodule.Quotient.equiv _ _ eSections (sectionsEquiv_image f k M U V)
  exact eY.symm.trans (e.symm.trans eX)

def zeroSections (k : K →+* Γ(X,⊤)) (M : X.Modules) :
    letI := Module.compHom (cohomology M 0) k
    cohomology M 0 ≃ₗ[K] Sections k M ⊤ := by
  letI := Module.compHom (cohomology M 0) k
  let e := (Ext.linearEquiv₀ (R := Γ(X,⊤)) (X := structureSheaf X) (Y := M)).trans
    (globalHomLinearEquiv M)
  refine { toFun := e
           invFun := e.symm
           left_inv := e.left_inv
           right_inv := e.right_inv
           map_add' := e.map_add
           map_smul' := ?_ }
  intro r m
  change e (k r • m) = restrictScalar X ⊤ (k r) • e m
  rw [e.map_smul]
  congr 1
  change k r = X.presheaf.map (𝟙 (op ⊤)) (k r)
  rw [X.presheaf.map_id]
  rfl

def cohomologyZeroEquiv (f : Y ⟶ X) (k : K →+* Γ(X,⊤)) (M : Y.Modules) :
    letI := Module.compHom (cohomology M 0) (f.appTop.hom.comp k)
    letI := Module.compHom (cohomology ((Scheme.Modules.pushforward f).obj M) 0) k
    cohomology M 0 ≃ₗ[K] cohomology ((Scheme.Modules.pushforward f).obj M) 0 := by
  letI := Module.compHom (cohomology M 0) (f.appTop.hom.comp k)
  letI := Module.compHom (cohomology ((Scheme.Modules.pushforward f).obj M) 0) k
  let e := (sectionsEquiv f k M ⊤).trans
    (BaseSections.congr (f.appTop.hom.comp k) M (Scheme.Hom.preimage_top f))
  exact (zeroSections (f.appTop.hom.comp k) M).trans
    (e.symm.trans (zeroSections k ((Scheme.Modules.pushforward f).obj M)).symm)

def cohomologyLowEquiv (f : Y ⟶ X) [IsFinite f]
    [IsNoetherian X] [IsNoetherian Y] (k : K →+* Γ(X,⊤))
    (M : Y.Modules) [M.IsQuasicoherent]
    [((Scheme.Modules.pushforward f).obj M).IsQuasicoherent]
    (U V : X.Opens) (hU : IsAffineOpen U) (hV : IsAffineOpen V)
    (hcover : U ⊔ V = ⊤) (n : ℕ) (hn : n ≤ 1) :
    letI := Module.compHom (cohomology M n) (f.appTop.hom.comp k)
    letI := Module.compHom (cohomology ((Scheme.Modules.pushforward f).obj M) n) k
    cohomology M n ≃ₗ[K] cohomology ((Scheme.Modules.pushforward f).obj M) n := by
  by_cases hn0 : n = 0
  · subst n
    exact cohomologyZeroEquiv f k M
  · have hn1 : n = 1 := by omega
    subst n
    exact cohomologyOneEquiv f k M U V hU hV hcover

theorem finiteDimensional_of_pushforward (f : Y ⟶ X) [IsFinite f]
    [IsNoetherian X] [IsNoetherian Y] (k : K →+* Γ(X,⊤))
    (M : Y.Modules) [M.IsQuasicoherent]
    [((Scheme.Modules.pushforward f).obj M).IsQuasicoherent]
    (U V : X.Opens) (hU : IsAffineOpen U) (hV : IsAffineOpen V)
    (hcover : U ⊔ V = ⊤) (n : ℕ) (hn : n ≤ 1)
    (hfinite : letI := Module.compHom (cohomology ((Scheme.Modules.pushforward f).obj M) n) k
      FiniteDimensional K (cohomology ((Scheme.Modules.pushforward f).obj M) n)) :
    let := Module.compHom (cohomology M n) (f.appTop.hom.comp k)
    FiniteDimensional K (cohomology M n) := by
  let := Module.compHom (cohomology M n) (f.appTop.hom.comp k)
  let := Module.compHom (cohomology ((Scheme.Modules.pushforward f).obj M) n) k
  have := hfinite
  let e := cohomologyLowEquiv f k M U V hU hV hcover n hn
  exact FiniteDimensional.of_injective e.toLinearMap e.injective

theorem finiteDimensional_pushforward (f : Y ⟶ X) [IsFinite f]
    [IsNoetherian X] [IsNoetherian Y] (k : K →+* Γ(X,⊤))
    (M : Y.Modules) [M.IsQuasicoherent]
    [((Scheme.Modules.pushforward f).obj M).IsQuasicoherent]
    (U V : X.Opens) (hU : IsAffineOpen U) (hV : IsAffineOpen V)
    (hcover : U ⊔ V = ⊤) (n : ℕ) (hn : n ≤ 1)
    (hfinite : letI := Module.compHom (cohomology M n) (f.appTop.hom.comp k)
      FiniteDimensional K (cohomology M n)) :
    let := Module.compHom (cohomology ((Scheme.Modules.pushforward f).obj M) n) k
    FiniteDimensional K (cohomology ((Scheme.Modules.pushforward f).obj M) n) := by
  let := Module.compHom (cohomology M n) (f.appTop.hom.comp k)
  let := Module.compHom (cohomology ((Scheme.Modules.pushforward f).obj M) n) k
  have := hfinite
  let e := cohomologyLowEquiv f k M U V hU hV hcover n hn
  exact FiniteDimensional.of_injective e.symm.toLinearMap e.symm.injective

lemma baseScalars_comp (f : Y ⟶ X) (p : X ⟶ Spec (CommRingCat.of ℂ)) :
    baseScalars (f ≫ p) = f.appTop.hom.comp (baseScalars p) := by
  ext c
  simp only [baseScalars, Scheme.Hom.comp_appTop, CommRingCat.hom_comp,
    RingHom.comp_apply]

theorem cohomologyDimension_pushforward (f : Y ⟶ X) [IsFinite f]
    [IsNoetherian X] [IsNoetherian Y] (p : X ⟶ Spec (CommRingCat.of ℂ))
    (M : Y.Modules) [M.IsQuasicoherent]
    [((Scheme.Modules.pushforward f).obj M).IsQuasicoherent]
    (U V : X.Opens) (hU : IsAffineOpen U) (hV : IsAffineOpen V)
    (hcover : U ⊔ V = ⊤) (n : ℕ) (hn : n ≤ 1) :
    cohomologyDimension p ((Scheme.Modules.pushforward f).obj M) n =
      cohomologyDimension (f ≫ p) M n := by
  unfold cohomologyDimension
  rw [baseScalars_comp]
  let := Module.compHom (cohomology M n) (f.appTop.hom.comp (baseScalars p))
  let := Module.compHom (cohomology ((Scheme.Modules.pushforward f).obj M) n) (baseScalars p)
  exact (cohomologyLowEquiv f (baseScalars p) M U V hU hV hcover n hn).finrank_eq.symm

theorem euler_one_pushforward (f : Y ⟶ X) [IsFinite f]
    [IsNoetherian X] [IsNoetherian Y] (p : X ⟶ Spec (CommRingCat.of ℂ))
    (M : Y.Modules) [M.IsQuasicoherent]
    [((Scheme.Modules.pushforward f).obj M).IsQuasicoherent]
    (U V : X.Opens) (hU : IsAffineOpen U) (hV : IsAffineOpen V)
    (hcover : U ⊔ V = ⊤) :
    eulerCharacteristic p 1 ((Scheme.Modules.pushforward f).obj M) =
      eulerCharacteristic (f ≫ p) 1 M := by
  apply Finset.sum_congr rfl
  intro n hn
  have hn' : n ≤ 1 := by
    have h := Finset.mem_range.mp hn
    omega
  rw [cohomologyDimension_pushforward f p M U V hU hV hcover n hn']

end
end PiExponent.CurveFinitePushforwardCohomology

end OAI
end Source0602

-- Source: OAI/NumberTheory/PiExponent/Approximation/ProjectionFormula.lean
section Source0603
/-
Modification notice for the LogTwo project.
Derived from openai/math (Apache-2.0), revision adc7f1241b42e322a6451854ab7e4b4c146bf78a.
Original source: lean/OAI/NumberTheory/PiExponent/Approximation/ProjectionFormula.lean
Changes: Convert module/import declarations to the Lean 4.34 public module format.
See ../THIRD_PARTY_NOTICES.txt for provenance and the recorded changes.
-/

namespace OAI

namespace PiExponent.ProjectionFormula
noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite
open PiExponentSeshadri.Geometry PiExponentSeshadri.TensorPure
variable {X Y : Scheme.{0}} (f : X ⟶ Y)

def hom (M : X.Modules) (L : Y.Modules) :
    moduleTensor Y ((Scheme.Modules.pushforward f).obj M) L ⟶
      (Scheme.Modules.pushforward f).obj
        (moduleTensor X M ((Scheme.Modules.pullback f).obj L)) :=
  moduleTensorMap (𝟙 _) ((Scheme.Modules.pullbackPushforwardAdjunction f).unit.app L) ≫
    PiExponentSeshadri.PushforwardTensor.hom f _ _

lemma hom_pure (M : X.Modules) (L : Y.Modules) (U : Y.Opens)
    (m : M.val.obj (op (f ⁻¹ᵁ U))) (s : L.val.obj (op U)) :
    (hom f M L).app U (pure ((Scheme.Modules.pushforward f).obj M) L U m s) =
      pure M ((Scheme.Modules.pullback f).obj L) (f ⁻¹ᵁ U) m
        (((Scheme.Modules.pullbackPushforwardAdjunction f).unit.app L).app U s) := by
  have ht := map_pure (𝟙 ((Scheme.Modules.pushforward f).obj M))
    ((Scheme.Modules.pullbackPushforwardAdjunction f).unit.app L) U m s
  have hp := PiExponentSeshadri.PushforwardTensor.hom_pure f M
    ((Scheme.Modules.pullback f).obj L) U m
    (((Scheme.Modules.pullbackPushforwardAdjunction f).unit.app L).app U s)
  exact (congrArg (fun z => (PiExponentSeshadri.PushforwardTensor.hom f M
    ((Scheme.Modules.pullback f).obj L)).app U z) ht).trans hp

@[reassoc] lemma naturality {M N : X.Modules} {L K : Y.Modules}
    (a : M ⟶ N) (b : L ⟶ K) :
    moduleTensorMap ((Scheme.Modules.pushforward f).map a) b ≫ hom f N K =
      hom f M L ≫ (Scheme.Modules.pushforward f).map
        (moduleTensorMap a ((Scheme.Modules.pullback f).map b)) := by
  unfold hom
  rw [← Category.assoc, ← moduleTensorMap_comp]
  rw [Category.comp_id, ← (Scheme.Modules.pullbackPushforwardAdjunction f).unit_naturality]
  have ht := moduleTensorMap_comp (𝟙 _) ((Scheme.Modules.pushforward f).map a)
    ((Scheme.Modules.pullbackPushforwardAdjunction f).unit.app L)
    ((Scheme.Modules.pushforward f).map ((Scheme.Modules.pullback f).map b))
  simp only [Category.id_comp] at ht
  rw [ht, Category.assoc, PiExponentSeshadri.PushforwardTensor.naturality]
  simp only [Category.assoc]

lemma pullback_unit_apply (U : Y.Opens) (a : Γ(Y,U)) :
    (pullbackUnitIso f).hom.app (f ⁻¹ᵁ U)
      (((Scheme.Modules.pullbackPushforwardAdjunction f).unit.app (structureSheaf Y)).app U a) =
    (f.app U) a := by
  have hu := congrArg (fun q => q.app U a) (pullbackUnit_adjunction f)
  exact hu

lemma unit_compatibility (M : X.Modules) :
    hom f M (structureSheaf Y) ≫
      (Scheme.Modules.pushforward f).map
        (moduleTensorMap (𝟙 M) (pullbackUnitIso f).hom ≫ (moduleTensorRightUnit M).hom) =
      (moduleTensorRightUnit ((Scheme.Modules.pushforward f).obj M)).hom := by
  apply PiExponentSeshadri.TensorPure.hom_ext
  intro U m a
  change Γ(M, f ⁻¹ᵁ U) at m
  change Γ(Y,U) at a
  let b : ((Scheme.Modules.pullback f).obj (structureSheaf Y)).val.obj (op (f ⁻¹ᵁ U)) :=
    ((Scheme.Modules.pullbackPushforwardAdjunction f).unit.app (structureSheaf Y)).app U a
  have hp := hom_pure f M (structureSheaf Y) U m a
  have ht := map_pure (𝟙 M) (pullbackUnitIso f).hom (f ⁻¹ᵁ U) m b
  have hu := right_unit_pure M (f ⁻¹ᵁ U) m ((pullbackUnitIso f).hom.app (f ⁻¹ᵁ U) b)
  have hv := right_unit_pure ((Scheme.Modules.pushforward f).obj M) U m a
  have hs := congrArg (fun r : Γ(X, f ⁻¹ᵁ U) => r • m) (pullback_unit_apply f U a)
  exact (congrArg (fun z => (moduleTensorRightUnit M).hom.app (f ⁻¹ᵁ U)
    ((moduleTensorMap (𝟙 M) (pullbackUnitIso f).hom).app (f ⁻¹ᵁ U) z)) hp).trans
    ((congrArg (fun z => (moduleTensorRightUnit M).hom.app (f ⁻¹ᵁ U) z) ht).trans
      (hu.trans (hs.trans hv.symm)))

instance unit_isIso (M : X.Modules) : IsIso (hom f M (structureSheaf Y)) := by
  let e : moduleTensor X M ((Scheme.Modules.pullback f).obj (structureSheaf Y)) ≅ M :=
    moduleTensorIso (Iso.refl M) (pullbackUnitIso f) ≪≫ moduleTensorRightUnit M
  have hi : IsIso (hom f M (structureSheaf Y) ≫
      (Scheme.Modules.pushforward f).map
        (moduleTensorMap (𝟙 M) (pullbackUnitIso f).hom ≫ (moduleTensorRightUnit M).hom)) := by
    rw [unit_compatibility]
    infer_instance
  exact (isIso_comp_right_iff (C := Y.Modules) (hom f M (structureSheaf Y))
    ((Scheme.Modules.pushforward f).mapIso e).hom).mp hi

lemma framed_isIso (M : X.Modules) (L : Y.Modules) (e : L ≅ structureSheaf Y) :
    IsIso (hom f M L) := by
  have hn := naturality f (𝟙 M) e.hom
  have hi : IsIso (moduleTensorMap ((Scheme.Modules.pushforward f).map (𝟙 M)) e.hom ≫
      hom f M (structureSheaf Y)) := by
    infer_instance
  have hj : IsIso (hom f M L ≫ (Scheme.Modules.pushforward f).map
      (moduleTensorMap (𝟙 M) ((Scheme.Modules.pullback f).map e.hom))) := by
    rw [← hn]
    exact hi
  exact (isIso_comp_right_iff _ _).mp hj

lemma restrict_compatibility (U : Y.Opens) (M : X.Modules) (L : Y.Modules) :
    (Scheme.Modules.restrictFunctor U.ι).map (hom f M L) ≫
      (PiExponentSeshadri.OpenBaseChange.iso f U
        (moduleTensor X M ((Scheme.Modules.pullback f).obj L))).hom ≫
      (Scheme.Modules.pushforward (f ∣_ U)).map
        (moduleTensorRestrict (f ⁻¹ᵁ U) M ((Scheme.Modules.pullback f).obj L)).hom =
    (moduleTensorRestrict U ((Scheme.Modules.pushforward f).obj M) L).hom ≫
      moduleTensorMap (PiExponentSeshadri.OpenBaseChange.iso f U M).hom (𝟙 _) ≫
      hom (f ∣_ U) (M.restrict (f ⁻¹ᵁ U).ι) (L.restrict U.ι) ≫
      (Scheme.Modules.pushforward (f ∣_ U)).map
        (moduleTensorMap (𝟙 _) ((PiExponentSeshadri.OpenBaseChange.leftSquare f U).hom.app L)) := by
  unfold hom
  rw [Functor.map_comp]
  simp only [Category.assoc]
  rw [PiExponentSeshadri.OpenBaseChange.tensor_square]
  rw [← Category.assoc, ← Category.assoc]
  erw [PiExponentSeshadri.TensorPure.restrict_map U (𝟙 ((Scheme.Modules.pushforward f).obj M))
    ((Scheme.Modules.pullbackPushforwardAdjunction f).unit.app L)]
  simp only [Category.assoc]
  rw [← moduleTensorMap_comp_assoc]
  erw [(Scheme.Modules.restrictFunctor U.ι).map_id]
  rw [Category.id_comp, PiExponentSeshadri.OpenBaseChange.unit_compatibility]
  have ht := moduleTensorMap_comp
    (PiExponentSeshadri.OpenBaseChange.iso f U M).hom (𝟙 _)
    ((Scheme.Modules.pullbackPushforwardAdjunction (f ∣_ U)).unit.app (L.restrict U.ι))
    ((Scheme.Modules.pushforward (f ∣_ U)).map
      ((PiExponentSeshadri.OpenBaseChange.leftSquare f U).hom.app L))
  simp only [Category.comp_id] at ht
  rw [ht]
  simp only [Category.assoc]
  have hn := PiExponentSeshadri.PushforwardTensor.naturality (f ∣_ U)
    (𝟙 (M.restrict (f ⁻¹ᵁ U).ι))
    ((PiExponentSeshadri.OpenBaseChange.leftSquare f U).hom.app L)
  erw [(Scheme.Modules.pushforward (f ∣_ U)).map_id] at hn
  erw [hn]
  rw [← moduleTensorMap_comp_assoc, Category.comp_id, Category.id_comp]
  rfl

instance line_isIso (M : X.Modules) (L : LineBundle Y) : IsIso (hom f M L.sheaf) := by
  apply PiExponentSeshadri.SectionOpens.isIso_of_locally_isIso
  intro y
  obtain ⟨U, hy, ⟨e⟩⟩ := L.locallyRankOne y
  refine ⟨U, hy, ?_⟩
  let : IsIso (hom (f ∣_ U) (M.restrict (f ⁻¹ᵁ U).ι) (L.sheaf.restrict U.ι)) :=
    framed_isIso (f ∣_ U) _ _ e
  have hi : IsIso ((Scheme.Modules.restrictFunctor U.ι).map (hom f M L.sheaf) ≫
      (PiExponentSeshadri.OpenBaseChange.iso f U
        (moduleTensor X M ((Scheme.Modules.pullback f).obj L.sheaf))).hom ≫
      (Scheme.Modules.pushforward (f ∣_ U)).map
        (moduleTensorRestrict (f ⁻¹ᵁ U) M ((Scheme.Modules.pullback f).obj L.sheaf)).hom) := by
    rw [restrict_compatibility]
    infer_instance
  exact (isIso_comp_right_iff _ _).mp hi

def iso (M : X.Modules) (L : LineBundle Y) :
    moduleTensor Y ((Scheme.Modules.pushforward f).obj M) L.sheaf ≅
      (Scheme.Modules.pushforward f).obj (moduleTensor X M (L.pullback f).sheaf) :=
  @asIso Y.Modules _ _ _ (hom f M L.sheaf) (line_isIso f M L)

def twistIso (M : X.Modules) (L : LineBundle Y) : ∀ n : ℕ,
    (Scheme.Modules.pushforward f).obj ((moduleTwistFunctor (L.pullback f) n).obj M) ≅
      (moduleTwistFunctor L n).obj ((Scheme.Modules.pushforward f).obj M)
  | 0 => Iso.refl _
  | n+1 => (iso f ((moduleTwistFunctor (L.pullback f) n).obj M) L).symm ≪≫
      moduleTensorIso (twistIso M L n) (Iso.refl _)

end
end PiExponent.ProjectionFormula

end OAI
end Source0603

-- Source: OAI/NumberTheory/PiExponent/Geometry/SupportedSheaf.lean
section Source0604
-- Modified in this edition: unused plain lemmas removed; see reduction.json.
/-
Modification notice for the LogTwo project.
Derived from openai/math (Apache-2.0), revision adc7f1241b42e322a6451854ab7e4b4c146bf78a.
Original source: lean/OAI/NumberTheory/PiExponent/Geometry/SupportedSheaf.lean
Changes: Convert module/import declarations to the Lean 4.34 public module format.
See ../THIRD_PARTY_NOTICES.txt for provenance and the recorded changes.
-/

namespace OAI

namespace PiExponentSeshadri.FiniteSupport
noncomputable section
open CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite AlgebraicGeometry
variable {X : TopCat.{0}}

lemma sections_subsingleton_of_stalks (F : X.Sheaf AddCommGrpCat.{0})
    (U : Opens X) (h : ∀ x ∈ U, Subsingleton (F.presheaf.stalk x)) :
    Subsingleton (F.obj.obj (op U)) := by
  constructor
  intro s t
  apply TopCat.Presheaf.section_ext F U s t
  intro x hx
  let := h x hx
  exact Subsingleton.elim _ _

lemma finite_closed_support_restriction_surjective
    (F : X.Sheaf AddCommGrpCat.{0}) (S : Set X) (hfin : S.Finite)
    (hclosed : ∀ x ∈ S, IsClosed ({x} : Set X))
    (hsupp : ∀ x ∉ S, Subsingleton (F.presheaf.stalk x))
    {U V : Opens X} (i : V ⟶ U) : Function.Surjective (F.obj.map i.op) := by
  classical
  intro s
  have hcS : IsClosed (S ∩ V) := by
    rw [← Set.biUnion_of_singleton (S ∩ (V : Set X))]
    exact (hfin.subset Set.inter_subset_left).isClosed_biUnion
      (fun x hx => hclosed x hx.1)
  let W : Opens X := U ⊓ ⟨(S ∩ V)ᶜ,hcS.isOpen_compl⟩
  let D : Bool → Opens X := fun b => if b then V else W
  let e : ∀ b, D b ⟶ U := fun b => homOfLE (by
    cases b
    · exact inf_le_left
    · exact i.le)
  have hcover : U ≤ ⨆ b, D b := by
    intro x hx
    by_cases hv : x ∈ V
    · exact Opens.mem_iSup.mpr ⟨true,hv⟩
    · exact Opens.mem_iSup.mpr ⟨false,hx,fun h => hv h.2⟩
  let t : ∀ b, F.obj.obj (op (D b)) := fun b => match b with
    | true => s
    | false => 0
  have hz : ∀ b c, b ≠ c → Subsingleton (F.obj.obj (op (D b ⊓ D c))) := by
    intro b c hbc
    apply sections_subsingleton_of_stalks
    intro x hx
    apply hsupp
    intro hs
    cases b <;> cases c
    · exact hbc rfl
    · exact hx.1.2 ⟨hs,hx.2⟩
    · exact hx.2.2 ⟨hs,hx.1⟩
    · exact hbc rfl
  have hcomp : TopCat.Presheaf.IsCompatible F.obj D t := by
    intro b c
    by_cases he : b = c
    · subst c; rfl
    · let := hz b c he
      exact Subsingleton.elim _ _
  obtain ⟨a,ha,_⟩ := F.existsUnique_gluing' D U e hcover t hcomp
  exact ⟨a,ha true⟩

lemma finite_closed_support_flasque (F : X.Sheaf AddCommGrpCat.{0})
    (S : Set X) (hfin : S.Finite)
    (hclosed : ∀ x ∈ S, IsClosed ({x} : Set X))
    (hsupp : ∀ x ∉ S, Subsingleton (F.presheaf.stalk x)) : F.IsFlasque where
  epi i := (AddCommGrpCat.epi_iff_surjective _).mpr
    (finite_closed_support_restriction_surjective F S hfin hclosed hsupp i.unop)

end
end PiExponentSeshadri.FiniteSupport

end OAI
end Source0604

-- Source: OAI/NumberTheory/PiExponent/LocalAlgebra/FiniteSupportLocalIso.lean
section Source0605
/-
Modification notice for the LogTwo project.
Derived from openai/math (Apache-2.0), revision adc7f1241b42e322a6451854ab7e4b4c146bf78a.
Original source: lean/OAI/NumberTheory/PiExponent/LocalAlgebra/FiniteSupportLocalIso.lean
Changes: Convert module/import declarations to the Lean 4.34 public module format.
See ../THIRD_PARTY_NOTICES.txt for provenance and the recorded changes.
-/

namespace OAI

namespace PiExponentSeshadri.Geometry
noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite
open PiExponentSeshadri.Frames PiExponentSeshadri.SectionOpens
variable {X : Scheme.{0}}

def openSectionModule (M : X.Modules) (U : X.Opens) : ModuleCat Γ(X,⊤) := by
  letI := Module.compHom Γ(M,U) (X.presheaf.map (homOfLE (show U ≤ ⊤ from le_top)).op).hom
  exact ModuleCat.of Γ(X,⊤) Γ(M,U)

def openSectionRestriction (M : X.Modules) (U : X.Opens) :
    Γ(M,⊤) →ₗ[Γ(X,⊤)] openSectionModule M U where
  toFun := M.presheaf.map (homOfLE (show U ≤ ⊤ from le_top)).op
  map_add' := map_add _
  map_smul' := fun r s => M.map_smul _ r s

def disjointSupportCoverEquiv (M : X.Modules) {ι : Type*} (D : ι → X.Opens)
    (hcover : ⊤ ≤ ⨆ i, D i)
    (hz : ∀ i j, i ≠ j → Subsingleton Γ(M,D i ⊓ D j)) :
    Γ(M,⊤) ≃ₗ[Γ(X,⊤)] ((i : ι) → openSectionModule M (D i)) := by
  let F : (X : TopCat).Sheaf AddCommGrpCat :=
    (SheafOfModules.toSheaf X.ringCatSheaf).obj M
  let f := LinearMap.pi (fun i => openSectionRestriction M (D i))
  apply LinearEquiv.ofBijective f
  constructor
  · intro s t h
    apply F.eq_of_locally_eq' D ⊤ (fun _ => homOfLE le_top) hcover s t
    intro i
    exact congrFun h i
  · intro s
    have hc : TopCat.Presheaf.IsCompatible F.obj D s := by
      intro i j
      by_cases h : i = j
      · subst j; rfl
      · let : Subsingleton (F.obj.obj (op (D i ⊓ D j))) := hz i j h
        exact Subsingleton.elim _ _
    obtain ⟨t,ht,_⟩ := F.existsUnique_gluing' D ⊤ (fun _ => homOfLE le_top) hcover s hc
    exact ⟨t,funext ht⟩

def openSectionIso (M N : X.Modules) (U : X.Opens)
    (e : M.restrict U.ι ≅ N.restrict U.ι) :
    openSectionModule M U ≃ₗ[Γ(X,⊤)] openSectionModule N U := by
  let etop := ((Scheme.Modules.toPresheaf U.toScheme).mapIso e).app (op ⊤)
  let a := (M.restrictAppIso U.ι ⊤).symm ≪≫ etop ≪≫ N.restrictAppIso U.ι ⊤
  have E : openSectionModule M (U.ι ''ᵁ ⊤) ≃ₗ[Γ(X,⊤)]
      openSectionModule N (U.ι ''ᵁ ⊤) := by
    refine { toFun := fun x => a.hom x
             invFun := fun x => a.inv x
             left_inv := by intro s; exact ConcreteCategory.congr_hom a.hom_inv_id s
             right_inv := by intro s; exact ConcreteCategory.congr_hom a.inv_hom_id s
             map_add' := map_add _
             map_smul' := ?_ }
    intro r s
    change Γ(M,U.ι ''ᵁ ⊤) at s
    change (N.restrictAppIso U.ι ⊤).hom
        (e.hom.app ⊤ ((M.restrictAppIso U.ι ⊤).inv
          ((X.presheaf.map (homOfLE (show U.ι ''ᵁ ⊤ ≤ ⊤ from le_top)).op r) • s))) =
      (X.presheaf.map (homOfLE (show U.ι ''ᵁ ⊤ ≤ ⊤ from le_top)).op r) • a.hom s
    rw [Scheme.Modules.smul_restrictAppIso_inv_apply,e.hom.app_smul,
      Scheme.Modules.smul_restrictAppIso_hom_apply]
    simp only [← ConcreteCategory.comp_apply, Category.assoc, Iso.hom_inv_id, Category.comp_id]
    rfl
  have htop : U.ι ''ᵁ (⊤ : U.toScheme.Opens) = U := by
    rw [Scheme.Hom.image_top_eq_opensRange,Scheme.Opens.opensRange_ι]
  exact htop ▸ E

def finiteSupportLocallyIsoGlobal (M N : X.Modules) (S : Set X)
    (hfin : S.Finite) (hclosed : ∀ x ∈ S, IsClosed ({x} : Set X))
    (hM : ∀ x ∉ S, Subsingleton (M.presheaf.stalk x))
    (hN : ∀ x ∉ S, Subsingleton (N.presheaf.stalk x))
    (hloc : ∀ x ∈ S, ∃ U : X.Opens, x ∈ U ∧ Nonempty (M.restrict U.ι ≅ N.restrict U.ι)) :
    Γ(M,⊤) ≃ₗ[Γ(X,⊤)] Γ(N,⊤) := by
  classical
  choose U hx he using fun x : S => hloc x x.property
  let e : ∀ x : S, M.restrict (U x).ι ≅ N.restrict (U x).ι := fun x => (he x).some
  have hc : IsClosed S := by
    rw [← Set.biUnion_of_singleton S]
    exact hfin.isClosed_biUnion hclosed
  have hcx (x : S) : IsClosed (S \ {x.val}) := by
    rw [← Set.biUnion_of_singleton (S \ {x.val})]
    exact (hfin.subset Set.sdiff_subset).isClosed_biUnion (fun y hy => hclosed y hy.1)
  let V : S → X.Opens := fun x => U x ⊓ ⟨(S \ {x.val})ᶜ,(hcx x).isOpen_compl⟩
  let D : Option S → X.Opens := fun x => match x with
    | none => ⟨Sᶜ,hc.isOpen_compl⟩
    | some x => V x
  have hV (x : S) : x.val ∈ V x := ⟨hx x,fun h => h.2 rfl⟩
  have hcover : ⊤ ≤ ⨆ i, D i := by
    intro x _
    by_cases hs : x ∈ S
    · exact Opens.mem_iSup.mpr ⟨some ⟨x,hs⟩,hV ⟨x,hs⟩⟩
    · exact Opens.mem_iSup.mpr ⟨none,hs⟩
  have honly (x : X) (hs : x ∈ S) (i : Option S) (hi : x ∈ D i) :
      i = some ⟨x,hs⟩ := by
    cases i with
    | none => exact (hi hs).elim
    | some y =>
      congr 1
      apply Subtype.ext
      by_contra hne
      exact hi.2 ⟨hs,fun h => hne h.symm⟩
  have hz (P : X.Modules) (hP : ∀ x ∉ S, Subsingleton (P.presheaf.stalk x)) :
      ∀ i j, i ≠ j → Subsingleton Γ(P,D i ⊓ D j) := by
    intro i j hij
    apply FiniteSupport.sections_subsingleton_of_stalks
      ((SheafOfModules.toSheaf X.ringCatSheaf).obj P)
    intro x hx
    apply hP
    intro hs
    exact hij ((honly x hs i hx.1).trans (honly x hs j hx.2).symm)
  have eD (i : Option S) : openSectionModule M (D i) ≃ₗ[Γ(X,⊤)] openSectionModule N (D i) := by
    cases i with
    | none =>
      letI : Subsingleton (openSectionModule M (D none)) := by
        change Subsingleton Γ(M,D none)
        exact FiniteSupport.sections_subsingleton_of_stalks
          ((SheafOfModules.toSheaf X.ringCatSheaf).obj M) _ (fun x hx => hM x hx)
      letI : Subsingleton (openSectionModule N (D none)) := by
        change Subsingleton Γ(N,D none)
        exact FiniteSupport.sections_subsingleton_of_stalks
          ((SheafOfModules.toSheaf X.ringCatSheaf).obj N) _ (fun x hx => hN x hx)
      exact LinearEquiv.ofSubsingleton _ _
    | some x =>
      let hVu : V x ≤ U x := inf_le_left
      let nest (P : X.Modules) : (P.restrict (U x).ι).restrict (X.homOfLE hVu) ≅ P.restrict (V x).ι :=
        ((Scheme.Modules.restrictFunctorComp (X.homOfLE hVu) (U x).ι).app P).symm ≪≫
          (Scheme.Modules.restrictFunctorCongr (X.homOfLE_ι hVu)).app P
      exact openSectionIso M N (V x) ((nest M).symm ≪≫
        (Scheme.Modules.restrictFunctor (X.homOfLE hVu)).mapIso (e x) ≪≫ nest N)
  exact (disjointSupportCoverEquiv M D hcover (hz M hM)).trans
    ((LinearEquiv.piCongrRight eD).trans (disjointSupportCoverEquiv N D hcover (hz N hN)).symm)

end
end PiExponentSeshadri.Geometry

end OAI
end Source0605

-- Source: OAI/NumberTheory/PiExponent/Geometry/CurveNormalizationDegree.lean
section Source0606
/-
Modification notice for the LogTwo project.
Derived from openai/math (Apache-2.0), revision adc7f1241b42e322a6451854ab7e4b4c146bf78a.
Original source: lean/OAI/NumberTheory/PiExponent/Geometry/CurveNormalizationDegree.lean
Changes: Convert module/import declarations to the Lean 4.34 public module format.
See ../THIRD_PARTY_NOTICES.txt for provenance and the recorded changes.
-/

namespace OAI

noncomputable section
namespace PiExponent.CurveNormalizationDegree
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite
open PiExponentSeshadri.Geometry PiExponentSeshadri.SectionOpens
variable {X : Scheme.{0}}

lemma cokernel_stalk_subsingleton {M N : X.Modules} (s : M ⟶ N) (x : X)
    (hx : x ∈ isoOpen s) :
    Subsingleton ((cokernel s).presheaf.stalk x) := by
  let F := SheafOfModules.toSheaf X.ringCatSheaf ⋙
    TopCat.Sheaf.forget AddCommGrpCat X ⋙ TopCat.Presheaf.stalkFunctor AddCommGrpCat x
  let : F.PreservesZeroMorphisms := by
    constructor
    intro M N
    change (TopCat.Presheaf.stalkFunctor AddCommGrpCat x).map
      ((SheafOfModules.toSheaf X.ringCatSheaf).map (0 : M ⟶ N)).hom = 0
    rw [Functor.map_zero]
    change (TopCat.Presheaf.stalkFunctor AddCommGrpCat x).map 0 = 0
    exact (TopCat.Presheaf.stalkFunctor AddCommGrpCat x).map_zero _ _
  let : PreservesColimitsOfSize.{0,0} F := by
    refine @comp_preservesColimits _ _ _ _ _ _ _ _ ?_ ?_
    · exact PiExponentSeshadri.ModuleSheafExact.toSheafPreservesColimits X.ringCatSheaf
    · exact inferInstanceAs (PreservesColimitsOfSize.{0,0}
        (TopCat.Sheaf.forget AddCommGrpCat.{0} (X : TopCat) ⋙
          TopCat.Presheaf.stalkFunctor AddCommGrpCat.{0} x))
  obtain ⟨U,hx,hU⟩ := (mem_isoOpen_iff s x).mp hx
  let := hU
  let : IsIso (F.map s) := stalk_isIso_of_restrict s U.ι ⟨x,hx⟩
  have hz : IsZero (F.obj (cokernel s)) :=
    (isZero_cokernel_of_epi (F.map s)).of_iso (PreservesCokernel.iso F s)
  exact AddCommGrpCat.subsingleton_of_isZero hz

theorem finite_closed_complement [IsIntegral X] [IsNoetherian X]
    (hd : topologicalKrullDim X ≤ 1) (U : X.Opens) (hU : U ≠ ⊥) :
    ((U : Set X)ᶜ).Finite ∧ ∀ x ∉ U, IsClosed ({x} : Set X) := by
  have hproper : (U : Set X)ᶜ ≠ Set.univ := by
    intro he
    apply hU
    apply SetLike.coe_injective
    simpa using he
  refine ⟨proper_closed_finite_of_dimension_one hd U.isOpen.isClosed_compl hproper, ?_⟩
  intro x hx
  have hc : closure ({x} : Set X) ⊆ (U : Set X)ᶜ :=
    closure_minimal (Set.singleton_subset_iff.mpr hx) U.isOpen.isClosed_compl
  have hsub : (closure ({x} : Set X)).Subsingleton :=
    proper_irreducible_closed_subsingleton hd isClosed_closure
      isIrreducible_singleton.closure (fun he => hproper (Set.eq_univ_of_univ_subset (he ▸ hc)))
  have he : closure ({x} : Set X) = {x} := by
    apply Set.Subset.antisymm
    · intro y hy
      exact hsub hy (subset_closure (Set.mem_singleton x))
    · exact subset_closure
  exact he ▸ isClosed_closure

theorem stalk_subsingleton_of_localIso (M N : X.Modules) (x : X)
    (U : X.Opens) (hx : x ∈ U) (e : M.restrict U.ι ≅ N.restrict U.ι)
    [Subsingleton (N.presheaf.stalk x)] : Subsingleton (M.presheaf.stalk x) := by
  let a := (Scheme.Modules.restrictStalkNatIso U.ι ⟨x,hx⟩).app M
  let b := (Scheme.Modules.restrictStalkNatIso U.ι ⟨x,hx⟩).app N
  let d := (Scheme.Modules.toPresheaf U.toScheme ⋙
    TopCat.Presheaf.stalkFunctor Ab (⟨x,hx⟩ : U.toScheme)).mapIso e
  let c := a.symm ≪≫ d ≪≫ b
  constructor
  intro s t
  apply (ConcreteCategory.bijective_of_isIso c.hom).injective
  exact Subsingleton.elim (α := N.presheaf.stalk x) _ _

theorem tensor_stalk_subsingleton (M : X.Modules) (L : LineBundle X) (x : X)
    [Subsingleton (M.presheaf.stalk x)] :
    Subsingleton ((moduleTensor X M L.sheaf).presheaf.stalk x) := by
  obtain ⟨U,hx,⟨e⟩⟩ := L.locallyRankOne x
  exact stalk_subsingleton_of_localIso _ M x U hx
    ((moduleTensorRestrictFrame U L.sheaf e).app M)

theorem finite_support_euler (p : X ⟶ Spec (.of ℂ)) (M : X.Modules)
    (S : Set X) (hfin : S.Finite)
    (hclosed : ∀ x ∈ S, IsClosed ({x} : Set X))
    (hsupp : ∀ x ∉ S, Subsingleton (M.presheaf.stalk x)) (d : ℕ) :
    eulerCharacteristic p d M =
      letI := Module.compHom Γ(M,⊤) (baseScalars p)
      (Module.finrank ℂ Γ(M,⊤) : ℤ) := by
  let : TopCat.Sheaf.IsFlasque ((SheafOfModules.toSheaf X.ringCatSheaf).obj M) :=
    PiExponentSeshadri.FiniteSupport.finite_closed_support_flasque _ S hfin hclosed hsupp
  unfold eulerCharacteristic
  rw [Finset.sum_eq_single 0]
  · simp only [pow_zero, one_mul, cohomologyDimension_zero]
  · intro n hn hn0
    obtain ⟨j,rfl⟩ := Nat.exists_eq_succ_of_ne_zero hn0
    let : Subsingleton (cohomology M (j+1)) := ⟨fun x y =>
      (PiExponentSeshadri.FlasqueCohomology.flasque_ext_zero X.ringCatSheaf j M x).trans
        (PiExponentSeshadri.FlasqueCohomology.flasque_ext_zero X.ringCatSheaf j M y).symm⟩
    simp [cohomologyDimension, Module.finrank_zero_of_subsingleton]
  · simp

theorem finite_support_tensor_euler (p : X ⟶ Spec (.of ℂ)) (M : X.Modules)
    (L : LineBundle X) (S : Set X) (hfin : S.Finite)
    (hclosed : ∀ x ∈ S, IsClosed ({x} : Set X))
    (hsupp : ∀ x ∉ S, Subsingleton (M.presheaf.stalk x)) (d : ℕ) :
    eulerCharacteristic p d (moduleTensor X M L.sheaf) = eulerCharacteristic p d M := by
  have ht (x : X) (hx : x ∉ S) :
      Subsingleton ((moduleTensor X M L.sheaf).presheaf.stalk x) := by
    let := hsupp x hx
    exact tensor_stalk_subsingleton M L x
  let e := finiteSupportLocallyIsoGlobal (moduleTensor X M L.sheaf) M S hfin hclosed ht hsupp
    (fun x _ => by
      obtain ⟨U,hx,⟨e⟩⟩ := L.locallyRankOne x
      exact ⟨U,hx,⟨(moduleTensorRestrictFrame U L.sheaf e).app M⟩⟩)
  let := Module.compHom Γ(moduleTensor X M L.sheaf,⊤) (baseScalars p)
  let := Module.compHom Γ(M,⊤) (baseScalars p)
  let ec : Γ(moduleTensor X M L.sheaf,⊤) ≃ₗ[ℂ] Γ(M,⊤) :=
    { e.toAddEquiv with
      map_smul' := fun r x => e.map_smul (baseScalars p r) x }
  rw [finite_support_euler p _ S hfin hclosed ht,
    finite_support_euler p M S hfin hclosed hsupp]
  exact_mod_cast ec.finrank_eq

theorem cokernel_tensor_euler [IsIntegral X] [IsNoetherian X]
    (p : X ⟶ Spec (.of ℂ)) (hd : topologicalKrullDim X ≤ 1)
    {M N : X.Modules} (u : M ⟶ N) (hu : isoOpen u ≠ ⊥) (L : LineBundle X) (d : ℕ) :
    eulerCharacteristic p d (moduleTensor X (cokernel u) L.sheaf) =
      eulerCharacteristic p d (cokernel u) := by
  obtain ⟨hfin,hclosed⟩ := finite_closed_complement hd (isoOpen u) hu
  exact finite_support_tensor_euler p _ L (isoOpen u : Set X)ᶜ hfin hclosed
    (fun x hx => cokernel_stalk_subsingleton u x (not_not.mp hx)) d

end PiExponent.CurveNormalizationDegree

end

end OAI
end Source0606

-- Source: OAI/NumberTheory/PiExponent/Cohomology/CurveNormalizationEuler.lean
section Source0607
/-
Modification notice for the LogTwo project.
Derived from openai/math (Apache-2.0), revision adc7f1241b42e322a6451854ab7e4b4c146bf78a.
Original source: lean/OAI/NumberTheory/PiExponent/Cohomology/CurveNormalizationEuler.lean
Changes: Convert module/import declarations to the Lean 4.34 public module format.
See ../THIRD_PARTY_NOTICES.txt for provenance and the recorded changes.
-/

namespace OAI

noncomputable section
namespace PiExponent.CurveNormalizationDegree
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian
open TopologicalSpace Opposite PiExponentSeshadri.Geometry PiExponentSeshadri.SectionOpens
variable {X : Scheme.{0}}

def LowCohomologyFinite (p : X ⟶ Spec (.of ℂ)) (M : X.Modules) : Prop :=
  ∀ n ≤ 1, letI := Module.compHom (cohomology M n) (baseScalars p)
    FiniteDimensional ℂ (cohomology M n)

theorem lowCohomologyFinite_of_iso (p : X ⟶ Spec (.of ℂ))
    {M N : X.Modules} (e : M ≅ N) (h : LowCohomologyFinite p N) :
    LowCohomologyFinite p M := by
  intro n hn
  let := Module.compHom (cohomology M n) (baseScalars p)
  let := Module.compHom (cohomology N n) (baseScalars p)
  let := h n hn
  exact Module.Finite.of_surjective (cohomologyIso p e n).symm.toLinearMap
    (cohomologyIso p e n).symm.surjective

theorem finite_support_positive_cohomology (M : X.Modules)
    (S : Set X) (hfin : S.Finite) (hclosed : ∀ x ∈ S, IsClosed ({x} : Set X))
    (hsupp : ∀ x ∉ S, Subsingleton (M.presheaf.stalk x)) (n : ℕ) :
    Subsingleton (cohomology M (n+1)) := by
  let : TopCat.Sheaf.IsFlasque ((SheafOfModules.toSheaf X.ringCatSheaf).obj M) :=
    PiExponentSeshadri.FiniteSupport.finite_closed_support_flasque _ S hfin hclosed hsupp
  exact ⟨fun x y =>
    (PiExponentSeshadri.FlasqueCohomology.flasque_ext_zero X.ringCatSheaf n M x).trans
      (PiExponentSeshadri.FlasqueCohomology.flasque_ext_zero X.ringCatSheaf n M y).symm⟩

private theorem finite_middle {K U V W : Type*} [Field K]
    [AddCommGroup U] [Module K U] [AddCommGroup V] [Module K V]
    [AddCommGroup W] [Module K W] [Module.Finite K U] [Module.Finite K W]
    (f : U →ₗ[K] V) (g : V →ₗ[K] W) (h : Function.Exact f g) :
    Module.Finite K V := by
  have he : Function.Exact f g.rangeRestrict := by
    intro x
    rw [Subtype.ext_iff]
    exact h x
  exact Module.Finite.of_exact he g.surjective_rangeRestrict

theorem finite_supported_quotient (p : X ⟶ Spec (.of ℂ))
    (T : ShortComplex X.Modules) (hT : T.ShortExact)
    (h₁ : LowCohomologyFinite p T.X₁) (h₂ : LowCohomologyFinite p T.X₂)
    (S : Set X) (hfin : S.Finite) (hclosed : ∀ x ∈ S, IsClosed ({x} : Set X))
    (hsupp : ∀ x ∉ S, Subsingleton (T.X₃.presheaf.stalk x)) :
    LowCohomologyFinite p T.X₃ := by
  intro n hn
  let := Module.compHom (cohomology T.X₃ n) (baseScalars p)
  cases n with
  | succ n =>
      let := finite_support_positive_cohomology T.X₃ S hfin hclosed hsupp n
      infer_instance
  | zero =>
      let := sheafComplexLinear p
      let : Module.Finite ℂ (Ext (structureSheaf X) T.X₂ 0) := by
        change @Module.Finite ℂ (cohomology T.X₂ 0) _ _ (complexExtModule p T.X₂ 0)
        rw [complexExtModule_eq]
        exact h₂ 0 (by omega)
      let : Module.Finite ℂ (Ext (structureSheaf X) T.X₁ (0+1)) := by
        change @Module.Finite ℂ (cohomology T.X₁ 1) _ _ (complexExtModule p T.X₁ 1)
        rw [complexExtModule_eq]
        exact h₁ 1 le_rfl
      have he := finite_middle
        (PiExponentSeshadri.Cohomology.cohomologyMap₂ (K := ℂ) (structureSheaf X) (S := T) 0)
        (PiExponentSeshadri.Cohomology.cohomologyBoundary (K := ℂ) (structureSheaf X) hT 0)
        (PiExponentSeshadri.Cohomology.cohomology_exact₃ (K := ℂ) (structureSheaf X) hT 0)
      change @Module.Finite ℂ (cohomology T.X₃ 0) _ _ (complexExtModule p T.X₃ 0) at he
      rw [complexExtModule_eq] at he
      exact he

theorem generic_extension_tensor_euler [IsIntegral X] [IsNoetherian X]
    (p : X ⟶ Spec (.of ℂ)) (hd : topologicalKrullDim X ≤ 1)
    (B : X.Modules) (u : structureSheaf X ⟶ B) [Mono u]
    (hu : isoOpen u ≠ ⊥) (L : LineBundle X)
    (hO : LowCohomologyFinite p (structureSheaf X))
    (hB : LowCohomologyFinite p B) (hL : LowCohomologyFinite p L.sheaf)
    (hBL : LowCohomologyFinite p (moduleTensor X B L.sheaf))
    [Subsingleton (cohomology (structureSheaf X) 2)]
    [Subsingleton (cohomology L.sheaf 2)] :
    eulerCharacteristic p 1 (moduleTensor X B L.sheaf) - eulerCharacteristic p 1 B =
      eulerCharacteristic p 1 L.sheaf - eulerCharacteristic p 1 (structureSheaf X) := by
  let T := ShortComplex.mk u (cokernel.π u) (cokernel.condition u)
  have hT : T.ShortExact :=
    { exact := ShortComplex.exact_of_g_is_cokernel T (cokernelIsCokernel u) }
  let TL := T.map (moduleTensorRightFunctor L.sheaf)
  have hTL : TL.ShortExact := moduleTensorRightFunctor_shortExact L T hT
  let S : Set X := (isoOpen u : Set X)ᶜ
  obtain ⟨hfin,hclosed⟩ := finite_closed_complement hd (isoOpen u) hu
  have hsupp (x : X) (hx : x ∉ S) : Subsingleton ((cokernel u).presheaf.stalk x) :=
    cokernel_stalk_subsingleton u x (not_not.mp hx)
  have hsuppt (x : X) (hx : x ∉ S) :
      Subsingleton ((moduleTensor X (cokernel u) L.sheaf).presheaf.stalk x) := by
    let := hsupp x hx
    exact tensor_stalk_subsingleton _ L x
  have hOL := lowCohomologyFinite_of_iso p (moduleTensorUnit L.sheaf) hL
  have hQ := finite_supported_quotient p T hT hO hB S hfin hclosed hsupp
  have hQL := finite_supported_quotient p TL hTL hOL hBL S hfin hclosed hsuppt
  let : Subsingleton (cohomology (moduleTensor X (structureSheaf X) L.sheaf) 2) := by
    let := Module.compHom (cohomology (moduleTensor X (structureSheaf X) L.sheaf) 2) (baseScalars p)
    let := Module.compHom (cohomology L.sheaf 2) (baseScalars p)
    exact (cohomologyIso p (moduleTensorUnit L.sheaf) 2).injective.subsingleton
  let : Subsingleton (cohomology TL.X₁ (1+1)) := by
    change Subsingleton (cohomology (moduleTensor X (structureSheaf X) L.sheaf) 2)
    infer_instance
  have h₀ := eulerCharacteristic_add p hT 1 hO hB hQ
  have h₁ := eulerCharacteristic_add p hTL 1 hOL hBL hQL
  change eulerCharacteristic p 1 B = eulerCharacteristic p 1 (structureSheaf X) +
    eulerCharacteristic p 1 (cokernel u) at h₀
  change eulerCharacteristic p 1 (moduleTensor X B L.sheaf) =
    eulerCharacteristic p 1 (moduleTensor X (structureSheaf X) L.sheaf) +
    eulerCharacteristic p 1 (moduleTensor X (cokernel u) L.sheaf) at h₁
  rw [eulerCharacteristic_iso p (moduleTensorUnit L.sheaf),
    cokernel_tensor_euler p hd u hu L 1] at h₁
  omega

end PiExponent.CurveNormalizationDegree

end

end OAI
end Source0607

-- Source: OAI/NumberTheory/PiExponent/Geometry/CurveFinitePushforwardCoherent.lean
section Source0608
/-
Modification notice for the LogTwo project.
Derived from openai/math (Apache-2.0), revision adc7f1241b42e322a6451854ab7e4b4c146bf78a.
Original source: lean/OAI/NumberTheory/PiExponent/Geometry/CurveFinitePushforwardCoherent.lean
Changes: Convert module/import declarations to the Lean 4.34 public module format.
Expose private helpers and adjust helper names where needed for module compatibility.
See ../THIRD_PARTY_NOTICES.txt for provenance and the recorded changes.
-/

namespace OAI

namespace PiExponent.CurveFinitePushforwardCoherent
noncomputable section
open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite
open CoherentAffineFinite FiniteGlobalPresentation ClosedPushforwardAffine
variable {X Y : Scheme.{0}}

def presentationOfIso (X : Scheme.{0})
    {M N : SheafOfModules X.ringCatSheaf} (e : M ≅ N)
    (P : M.Presentation) : N.Presentation := by
  let : IsIso e.hom := e.isIso_hom
  exact P.ofIsIso e.hom

theorem affine_pushforward_sections_finite [IsAffine X] [IsAffine Y]
    (f : X ⟶ Y) [IsFinite f] (M : X.Modules) [M.IsQuasicoherent]
    (hM : LocallyFinitelyGenerated M) :
    Module.Finite Γ(Y,⊤) Γ((Scheme.Modules.pushforward f).obj M,⊤) := by
  have hfin : Module.Finite Γ(X,f ⁻¹ᵁ (⊤ : Y.Opens)) Γ(M,f ⁻¹ᵁ (⊤ : Y.Opens)) := by
    simpa only [Scheme.Hom.preimage_top] using! affine_sections_finite_of_localGenerators M hM
  let σ : Γ(Y,⊤) →+* Γ(X,f ⁻¹ᵁ (⊤ : Y.Opens)) := (f.app ⊤).hom
  let : Algebra Γ(Y,⊤) Γ(X,f ⁻¹ᵁ (⊤ : Y.Opens)) := σ.toAlgebra
  let : Module.Finite Γ(Y,⊤) Γ(X,f ⁻¹ᵁ (⊤ : Y.Opens)) :=
    f.finite_app ⊤ (isAffineOpen_top Y)
  let : Module Γ(Y,⊤) Γ(M,f ⁻¹ᵁ (⊤ : Y.Opens)) := Module.compHom _ σ
  let : IsScalarTower Γ(Y,⊤) Γ(X,f ⁻¹ᵁ (⊤ : Y.Opens)) Γ(M,f ⁻¹ᵁ (⊤ : Y.Opens)) :=
    IsScalarTower.of_compHom _ _ _
  have h := Module.Finite.trans (R := Γ(Y,⊤))
    Γ(X,f ⁻¹ᵁ (⊤ : Y.Opens)) Γ(M,f ⁻¹ᵁ (⊤ : Y.Opens))
  exact h

theorem affine_pushforward_exists_finitePresentation [IsAffine X] [IsAffine Y]
    [IsLocallyNoetherian Y] (f : X ⟶ Y) [IsFinite f]
    (M : X.Modules) [M.IsQuasicoherent] (hM : LocallyFinitelyGenerated M) :
    ∃ P : ((Scheme.Modules.pushforward f).obj M).Presentation, P.IsFinite := by
  have := affine_pushforward_quasicoherent f M
  have := affine_pushforward_sections_finite f M hM
  exact affine_exists_finitePresentation_of_sections ((Scheme.Modules.pushforward f).obj M)

instance pushforward_isFinitePresentation (f : X ⟶ Y) [IsFinite f]
    [IsLocallyNoetherian Y] (M : X.Modules) [M.IsFinitePresentation] :
    ((Scheme.Modules.pushforward f).obj M).IsFinitePresentation := by
  let : M.IsQuasicoherent :=
    (SheafOfModules.IsFinitePresentation.exists_quasicoherentData M).choose.isQuasicoherent
  apply isFinitePresentation_of_affine_presentations
  intro U
  have : IsAffine U.1.toScheme := U.2
  have : IsAffine (f ⁻¹ᵁ U.1).toScheme := U.2.preimage f
  have hM := (locallyFinitelyGenerated_of_finitePresentation M).restrict (f ⁻¹ᵁ U.1).ι
  let : (M.restrict (f ⁻¹ᵁ U.1).ι).IsQuasicoherent :=
    Scheme.Modules.isQuasicoherent_restrictFunctor (f ⁻¹ᵁ U.1).ι M
  obtain ⟨P,hP⟩ := affine_pushforward_exists_finitePresentation (f ∣_ U.1)
    (M.restrict (f ⁻¹ᵁ U.1).ι) hM
  exact ⟨presentationOfIso U.1.toScheme
    (PiExponentSeshadri.OpenBaseChange.iso f U.1 M).symm P,
    ⟨⟨hP.isFiniteType_generators.finite⟩, ⟨hP.isFiniteType_relations.finite⟩⟩⟩

end
end PiExponent.CurveFinitePushforwardCoherent

end OAI
end Source0608

-- Source: OAI/NumberTheory/PiExponent/Geometry/CurveNormalizationUnit.lean
section Source0609
/-
Modification notice for the LogTwo project.
Derived from openai/math (Apache-2.0), revision adc7f1241b42e322a6451854ab7e4b4c146bf78a.
Original source: lean/OAI/NumberTheory/PiExponent/Geometry/CurveNormalizationUnit.lean
Changes: Convert module/import declarations to the Lean 4.34 public module format.
See ../THIRD_PARTY_NOTICES.txt for provenance and the recorded changes.
-/

namespace OAI

noncomputable section
namespace PiExponent.CurveNormalizationDegree
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite
open PiExponentSeshadri.Geometry PiExponentSeshadri.SectionOpens
variable {X Y : Scheme.{0}}

def unitMap (f : Y ⟶ X) : structureSheaf X ⟶
    (Scheme.Modules.pushforward f).obj (structureSheaf Y) :=
  SheafOfModules.unitToPushforwardObjUnit f.toRingCatSheafHom

theorem unitMap_mono (f : Y ⟶ X) [IsReduced X] [QuasiCompact f] [IsDominant f] :
    Mono (unitMap f) := by
  let : IsSchemeTheoreticallyDominant f := IsSchemeTheoreticallyDominant.of_isDominant f
  have h : Mono (unitMap f).val := by
    apply PresheafOfModules.mono_of_injective
    intro U
    exact f.app_injective U.unop
  exact (SheafOfModules.forget X.ringCatSheaf).mono_of_mono_map h

theorem dominant_of_iso_restrict [IsIntegral X] (f : Y ⟶ X)
    (U : X.Opens) (hU : U ≠ ⊥) [IsIso (f ∣_ U)] : IsDominant f := by
  have hne : (U : Set X).Nonempty := by
    by_contra hn
    apply hU
    apply SetLike.coe_injective
    exact Set.not_nonempty_iff_eq_empty.mp hn
  let : IsDominant U.ι := Opens.isDominant_ι (U.isOpen.dense hne)
  have : IsDominant ((f ⁻¹ᵁ U).ι ≫ f) := by
    rw [← morphismRestrict_ι]
    infer_instance
  exact IsDominant.of_comp (f ⁻¹ᵁ U).ι f

theorem unitMap_restrict_isIso (f : Y ⟶ X) (U : X.Opens) [IsIso (f ∣_ U)] :
    IsIso ((Scheme.Modules.restrictFunctor U.ι).map (unitMap f)) := by
  apply Scheme.Modules.Hom.isIso_iff_isIso_app.mpr
  intro V
  have h := morphismRestrict_app f U V
  have hiso : IsIso ((f ∣_ U).app V) := by infer_instance
  have : IsIso (f.app (U.ι ''ᵁ V) ≫
      Y.presheaf.map (eqToHom (image_morphismRestrict_preimage f U V)).op) := by
    rw [← h]
    exact hiso
  have : IsIso (f.app (U.ι ''ᵁ V)) :=
    (isIso_comp_right_iff (f.app (U.ι ''ᵁ V))
      (Y.presheaf.map (eqToHom (image_morphismRestrict_preimage f U V)).op)).mp inferInstance
  apply (ConcreteCategory.isIso_iff_bijective _).mpr
  exact ConcreteCategory.bijective_of_isIso (f.app (U.ι ''ᵁ V))

theorem unitMap_isoOpen_ne_bot (f : Y ⟶ X) (U : X.Opens)
    (hU : U ≠ ⊥) [IsIso (f ∣_ U)] : isoOpen (unitMap f) ≠ ⊥ := by
  have hle : U ≤ isoOpen (unitMap f) := by
    intro x hx
    exact (mem_isoOpen_iff _ x).mpr ⟨U,hx,unitMap_restrict_isIso f U⟩
  intro h
  exact hU (le_antisymm (h ▸ hle) bot_le)

def pushforwardPullbackIso (f : Y ⟶ X) (L : LineBundle X) :
    moduleTensor X ((Scheme.Modules.pushforward f).obj (structureSheaf Y)) L.sheaf ≅
      (Scheme.Modules.pushforward f).obj (L.pullback f).sheaf :=
  ProjectionFormula.iso f (structureSheaf Y) L ≪≫
    (Scheme.Modules.pushforward f).mapIso (moduleTensorUnit (L.pullback f).sheaf)

end PiExponent.CurveNormalizationDegree

end

end OAI
end Source0609

-- Source: OAI/NumberTheory/PiExponent/Geometry/CurveNormalizationInvariance.lean
section Source0610
-- Modified in this edition: unused plain lemmas removed; see reduction.json.
/-
Modification notice for the LogTwo project.
Derived from openai/math (Apache-2.0), revision adc7f1241b42e322a6451854ab7e4b4c146bf78a.
Original source: lean/OAI/NumberTheory/PiExponent/Geometry/CurveNormalizationInvariance.lean
Changes: Convert module/import declarations to the Lean 4.34 public module format.
See ../THIRD_PARTY_NOTICES.txt for provenance and the recorded changes.
-/

namespace OAI

noncomputable section
namespace PiExponent.CurveNormalizationDegree
open AlgebraicGeometry CategoryTheory TopologicalSpace
open PiExponentSeshadri.Geometry
variable {X Y : Scheme.{0}}

theorem lowCohomologyFinite_pushforward (f : Y ⟶ X) [IsFinite f]
    [IsNoetherian X] [IsNoetherian Y] (p : X ⟶ Spec (.of ℂ))
    (M : Y.Modules) [M.IsFinitePresentation]
    (U V : X.Opens) (hU : IsAffineOpen U) (hV : IsAffineOpen V)
    (hcover : U ⊔ V = ⊤) (hM : LowCohomologyFinite (f ≫ p) M) :
    LowCohomologyFinite p ((Scheme.Modules.pushforward f).obj M) := by
  let : M.IsQuasicoherent :=
    (SheafOfModules.IsFinitePresentation.exists_quasicoherentData M).choose.isQuasicoherent
  let : ((Scheme.Modules.pushforward f).obj M).IsQuasicoherent :=
    (SheafOfModules.IsFinitePresentation.exists_quasicoherentData
      ((Scheme.Modules.pushforward f).obj M)).choose.isQuasicoherent
  intro n hn
  apply CurveFinitePushforwardCohomology.finiteDimensional_pushforward
    f (baseScalars p) M U V hU hV hcover n hn
  have hm := hM n hn
  rw [CurveFinitePushforwardCohomology.baseScalars_comp] at hm
  exact hm

theorem pullback_euler_degree_of_open_iso [IsIntegral X]
    [IsNoetherian X] [IsNoetherian Y] (f : Y ⟶ X) [IsFinite f]
    (p : X ⟶ Spec (.of ℂ)) (hd : topologicalKrullDim X ≤ 1)
    (W : X.Opens) (hW : W ≠ ⊥) [IsIso (f ∣_ W)]
    (U V : X.Opens) (hU : IsAffineOpen U) (hV : IsAffineOpen V)
    (hcover : U ⊔ V = ⊤) (L : LineBundle X)
    (hO : LowCohomologyFinite p (structureSheaf X))
    (hL : LowCohomologyFinite p L.sheaf)
    (hOY : LowCohomologyFinite (f ≫ p) (structureSheaf Y))
    (hLY : LowCohomologyFinite (f ≫ p) (L.pullback f).sheaf)
    [Subsingleton (cohomology (structureSheaf X) 2)]
    [Subsingleton (cohomology L.sheaf 2)] :
    eulerCharacteristic (f ≫ p) 1 (L.pullback f).sheaf -
        eulerCharacteristic (f ≫ p) 1 (structureSheaf Y) =
      eulerCharacteristic p 1 L.sheaf - eulerCharacteristic p 1 (structureSheaf X) := by
  let : IsDominant f := dominant_of_iso_restrict f W hW
  let : Mono (unitMap f) := unitMap_mono f
  let : (structureSheaf Y).IsFinitePresentation :=
    GeometrySupport.LineBundleCoherent.structureSheaf_isFinitePresentation
  let : (L.pullback f).sheaf.IsFinitePresentation :=
    GeometrySupport.LineBundleCoherent.lineBundle_isFinitePresentation (L.pullback f)
  let : (structureSheaf Y).IsQuasicoherent :=
    (SheafOfModules.IsFinitePresentation.exists_quasicoherentData
      (structureSheaf Y)).choose.isQuasicoherent
  let : ((Scheme.Modules.pushforward f).obj (structureSheaf Y)).IsQuasicoherent :=
    (SheafOfModules.IsFinitePresentation.exists_quasicoherentData
      ((Scheme.Modules.pushforward f).obj (structureSheaf Y))).choose.isQuasicoherent
  let : ((Scheme.Modules.pushforward f).obj (L.pullback f).sheaf).IsQuasicoherent :=
    (SheafOfModules.IsFinitePresentation.exists_quasicoherentData
      ((Scheme.Modules.pushforward f).obj (L.pullback f).sheaf)).choose.isQuasicoherent
  have hB := lowCohomologyFinite_pushforward f p (structureSheaf Y) U V hU hV hcover hOY
  have hPL := lowCohomologyFinite_pushforward f p (L.pullback f).sheaf U V hU hV hcover hLY
  have hBL := lowCohomologyFinite_of_iso p (pushforwardPullbackIso f L) hPL
  have h := generic_extension_tensor_euler p hd
    ((Scheme.Modules.pushforward f).obj (structureSheaf Y)) (unitMap f)
    (unitMap_isoOpen_ne_bot f W hW) L hO hB hL hBL
  rw [eulerCharacteristic_iso p (pushforwardPullbackIso f L)] at h
  rw [CurveFinitePushforwardCohomology.euler_one_pushforward f p
    (L.pullback f).sheaf U V hU hV hcover,
    CurveFinitePushforwardCohomology.euler_one_pushforward f p
      (structureSheaf Y) U V hU hV hcover] at h
  exact h

end PiExponent.CurveNormalizationDegree

end

end OAI
end Source0610

-- Source: OAI/NumberTheory/PiExponent/Geometry/ProjectiveCurveTwoAffine.lean
section Source0611
/-
Modification notice for the LogTwo project.
Derived from openai/math (Apache-2.0), revision adc7f1241b42e322a6451854ab7e4b4c146bf78a.
Original source: lean/OAI/NumberTheory/PiExponent/Geometry/ProjectiveCurveTwoAffine.lean
Changes: Convert module/import declarations to the Lean 4.34 public module format.
See ../THIRD_PARTY_NOTICES.txt for provenance and the recorded changes.
-/

namespace OAI

namespace PiExponent.ProjectiveCurveTwoAffine
noncomputable section
open AlgebraicGeometry CategoryTheory TopologicalSpace MvPolynomial
open PiExponentSeshadri.Projective PiExponentSeshadri.Geometry
attribute [local instance] MvPolynomial.gradedAlgebra

variable {K σ : Type} [CommRing K] [Fintype σ]

def linearEquation (v : σ → K) : MvPolynomial σ K := ∑ i, C (v i) * X i

theorem linearEquation_homogeneous (v : σ → K) :
    linearEquation v ∈ PolyGrade K σ 1 :=
  IsHomogeneous.sum _ _ _ (fun _i _ => isHomogeneous_C_mul_X _ _)

def linearEquationLinear : (σ → K) →ₗ[K] MvPolynomial σ K where
  toFun := linearEquation
  map_add' v w := by simp [linearEquation, add_mul, Finset.sum_add_distrib]
  map_smul' c v := by
    simp [linearEquation, Algebra.smul_def, Finset.mul_sum, mul_assoc]

theorem linearEquation_single_one [DecidableEq σ] (i : σ) :
    linearEquation (Pi.single i (1 : K)) = X i := by
  classical
  simp [linearEquation, Pi.single_apply, apply_ite, ite_mul]

theorem exists_hyperplane_avoiding {K σ ι : Type} [Field K] [Infinite K]
    [Fintype σ] [Finite ι] (x : ι → Proj (PolyGrade K σ)) :
    ∃ v : σ → K, ∀ i, x i ∈ Proj.basicOpen (PolyGrade K σ) (linearEquation v) := by
  classical
  let bad (i : ι) : Submodule K (σ → K) :=
    ((x i).asHomogeneousIdeal.toIdeal.restrictScalars K).comap
      (linearEquationLinear (K := K) (σ := σ))
  have hbad (i : ι) : bad i ≠ ⊤ := by
    intro h
    have hx : x i ∈ ⨆ j : σ, Proj.basicOpen (PolyGrade K σ) (X j) := by
      rw [standardChart_cover]
      trivial
    obtain ⟨j, hj⟩ := Opens.mem_iSup.mp hx
    have hm : Pi.single j (1 : K) ∈ bad i := h ▸ Submodule.mem_top
    change linearEquation (Pi.single j (1 : K)) ∈ (x i).asHomogeneousIdeal at hm
    rw [linearEquation_single_one] at hm
    exact hj hm
  obtain ⟨v, hv⟩ := Submodule.exists_forall_notMem_of_forall_ne_top bad hbad
  exact ⟨v, hv⟩

theorem two_affine_cover_of_affine_projective_map
    {K σ : Type} [Field K] [Infinite K] [Fintype σ]
    {Y : Scheme.{0}} [IsIntegral Y] [NoetherianSpace Y]
    (j : Y ⟶ Proj (PolyGrade K σ)) [IsAffineHom j]
    (hd : topologicalKrullDim Y ≤ 1) :
    ∃ U V : Y.Opens, IsAffineOpen U ∧ IsAffineOpen V ∧ U ⊔ V = ⊤ := by
  classical
  obtain ⟨y⟩ : Nonempty Y := inferInstance
  have hy : j y ∈ ⨆ i : σ, Proj.basicOpen (PolyGrade K σ) (X i) := by
    rw [standardChart_cover]
    trivial
  obtain ⟨i, hi⟩ := Opens.mem_iSup.mp hy
  let U := j ⁻¹ᵁ Proj.basicOpen (PolyGrade K σ) (X i)
  have hU : IsAffineOpen U := (standardChart_isAffineOpen i).preimage j
  let Z : Set Y := (U : Set Y)ᶜ
  have hZ : Z.Finite := proper_closed_finite_of_dimension_one hd U.isOpen.isClosed_compl (by
    intro h
    have hyZ : y ∈ Z := h ▸ Set.mem_univ y
    exact hyZ hi)
  let : Finite Z := hZ.to_subtype
  obtain ⟨v, hv⟩ := exists_hyperplane_avoiding (fun z : Z => j z.val)
  let V := j ⁻¹ᵁ Proj.basicOpen (PolyGrade K σ) (linearEquation v)
  have hV : IsAffineOpen V :=
    (Proj.isAffineOpen_basicOpen _ _ (linearEquation_homogeneous v) (by decide)).preimage j
  refine ⟨U, V, hU, hV, top_unique ?_⟩
  intro z _
  by_cases hz : z ∈ U
  · exact Or.inl hz
  · exact Or.inr (hv ⟨z, hz⟩)

theorem two_affine_cover_of_closed_embedding
    {K σ : Type} [Field K] [Infinite K] [Fintype σ]
    {Y : Scheme.{0}} [IsIntegral Y] [IsNoetherian Y]
    (j : Y ⟶ Proj (PolyGrade K σ)) [IsClosedImmersion j]
    (hd : topologicalKrullDim Y ≤ 1) :
    ∃ U V : Y.Opens, IsAffineOpen U ∧ IsAffineOpen V ∧ U ⊔ V = ⊤ :=
  two_affine_cover_of_affine_projective_map j hd

end
end PiExponent.ProjectiveCurveTwoAffine

end OAI
end Source0611

-- Source: OAI/NumberTheory/PiExponent/Geometry/CurveNormalizationProjective.lean
section Source0612
-- Modified in this edition: unused plain lemmas removed; see reduction.json.
/-
Modification notice for the LogTwo project.
Derived from openai/math (Apache-2.0), revision adc7f1241b42e322a6451854ab7e4b4c146bf78a.
Original source: lean/OAI/NumberTheory/PiExponent/Geometry/CurveNormalizationProjective.lean
Changes: Convert module/import declarations to the Lean 4.34 public module format.
See ../THIRD_PARTY_NOTICES.txt for provenance and the recorded changes.
-/

namespace OAI

noncomputable section
namespace PiExponent.CurveNormalizationDegree
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace
open PiExponentSeshadri.Geometry PiExponentSeshadri.Projective
open CurveNormalizationModel

variable {X : Scheme.{0}} [IsIntegral X]
variable {σ : Type} [Finite σ] [Nonempty σ]
variable {E : Type} [Field E] [Algebra ℂ E]

theorem parameterCurve_pullback_euler_degree
    (p : X ⟶ Spec (.of ℂ)) [IsProper p]
    (j : X ⟶ ProjectiveO1.projectiveSpace ℂ σ) [IsClosedImmersion j]
    (hj : j ≫ polynomialProjectiveProjection ℂ σ = p)
    (hd : topologicalKrullDim X ≤ 1)
    (f : E) (hf : Transcendental ℂ f)
    [FiniteDimensional (IntermediateField.adjoin ℂ {f}) E]
    (g : parameterCurve f hf ⟶ X) [IsFinite g]
    (hg : g ≫ p = parameterCurveStructureMap f hf)
    (W : X.Opens) (hW : W ≠ ⊥) [IsIso (g ∣_ W)] (L : LineBundle X) :
    eulerCharacteristic (parameterCurveStructureMap f hf) 1 (L.pullback g).sheaf -
        eulerCharacteristic (parameterCurveStructureMap f hf) 1
          (structureSheaf (parameterCurve f hf)) =
      eulerCharacteristic p 1 L.sheaf - eulerCharacteristic p 1 (structureSheaf X) := by
  let : Fintype σ := Fintype.ofFinite σ
  let : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian p
  let : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace p
  let : IsNoetherian X := {}
  let : X.IsSeparated := by
    rw [Scheme.isSeparated_iff, ← terminal.comp_from p]
    infer_instance
  let : (structureSheaf X).IsFinitePresentation :=
    GeometrySupport.LineBundleCoherent.structureSheaf_isFinitePresentation
  let : (structureSheaf X).IsQuasicoherent :=
    (SheafOfModules.IsFinitePresentation.exists_quasicoherentData
      (structureSheaf X)).choose.isQuasicoherent
  let : L.sheaf.IsFinitePresentation :=
    GeometrySupport.LineBundleCoherent.lineBundle_isFinitePresentation L
  obtain ⟨U,V,hU,hV,hcover⟩ :=
    ProjectiveCurveTwoAffine.two_affine_cover_of_closed_embedding j hd
  let : Subsingleton (cohomology (structureSheaf X) 2) :=
    CurveTwoAffineVanishing.cohomology_subsingleton U V hU hV hcover _ 2 le_rfl
  let : Subsingleton (cohomology L.sheaf 2) :=
    CurveTwoAffineVanishing.cohomology_subsingleton U V hU hV hcover _ 2 le_rfl
  have hO : LowCohomologyFinite p (structureSheaf X) := fun n _ =>
    ProjectiveFiniteCoordinates.projectiveOver_cohomology_finite p j hj _ n
  have hL : LowCohomologyFinite p L.sheaf := fun n _ =>
    ProjectiveFiniteCoordinates.projectiveOver_cohomology_finite p j hj _ n
  have hOY : LowCohomologyFinite (g ≫ p) (structureSheaf (parameterCurve f hf)) := by
    rw [hg]
    exact parameterCurve_finiteLineCohomology f hf ((parameterCurvePolarization f hf).pow 0)
  have hLY : LowCohomologyFinite (g ≫ p) (L.pullback g).sheaf := by
    rw [hg]
    exact parameterCurve_finiteLineCohomology f hf (L.pullback g)
  simpa only [hg] using
    pullback_euler_degree_of_open_iso g p hd W hW U V hU hV hcover L hO hL hOY hLY

theorem parameterCurve_pullback_euler_degree_of_ample
    (p : X ⟶ Spec (.of ℂ)) [IsProper p]
    (H : LineBundle X) (hH : H.IsAmple) (hd : topologicalKrullDim X ≤ 1)
    (f : E) (hf : Transcendental ℂ f)
    [FiniteDimensional (IntermediateField.adjoin ℂ {f}) E]
    (g : parameterCurve f hf ⟶ X) [IsFinite g]
    (hg : g ≫ p = parameterCurveStructureMap f hf)
    (W : X.Opens) (hW : W ≠ ⊥) [IsIso (g ∣_ W)] (L : LineBundle X) :
    eulerCharacteristic (parameterCurveStructureMap f hf) 1 (L.pullback g).sheaf -
        eulerCharacteristic (parameterCurveStructureMap f hf) 1
          (structureSheaf (parameterCurve f hf)) =
      eulerCharacteristic p 1 L.sheaf - eulerCharacteristic p 1 (structureSheaf X) := by
  classical
  let : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian p
  let : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace p
  let : IsNoetherian X := ⟨⟩
  obtain ⟨n,hn,τ,hτ,s,hs,hclosed⟩ := H.ample_projective_sections_noetherian p hH
  let : Fintype τ := hτ
  have : Nonempty τ := by
    have hx : genericPoint X ∈ (⨆ i, PiExponentSeshadri.SectionOpens.isoOpen (s i)) := by
      rw [hs]
      trivial
    obtain ⟨i,-⟩ := Opens.mem_iSup.mp hx
    exact ⟨i⟩
  let j : X ⟶ ProjectiveO1.projectiveSpace ℂ τ := sectionsMorphism (baseScalars p) s hs
  have : IsClosedImmersion j := hclosed
  have hj : j ≫ polynomialProjectiveProjection ℂ τ = p := by
    rw [← AmpleCohomologyFinite.projectiveBase_eq_polynomialProjectiveProjection]
    exact (sectionsMorphism_over (baseScalars p) s hs).trans (toSpec_scalarMap p)
  exact parameterCurve_pullback_euler_degree p j hj hd f hf g hg W hW L

end PiExponent.CurveNormalizationDegree

end

end OAI
end Source0612

-- Source: OAI/NumberTheory/PiExponent/Geometry/CurveNormalizedDegreeTransfer.lean
section Source0613
-- Modified in this edition: unused plain lemmas removed; see reduction.json.
/-
Modification notice for the LogTwo project.
Derived from openai/math (Apache-2.0), revision adc7f1241b42e322a6451854ab7e4b4c146bf78a.
Original source: lean/OAI/NumberTheory/PiExponent/Geometry/CurveNormalizedDegreeTransfer.lean
Changes: Convert module/import declarations to the Lean 4.34 public module format.
See ../THIRD_PARTY_NOTICES.txt for provenance and the recorded changes.
-/

namespace OAI

noncomputable section
namespace PiExponent.CurveNormalizedDegreeTransfer
open AlgebraicGeometry CategoryTheory
open PiExponentSeshadri.Geometry
open NumericalAmpleness CurveNormalizationModel
variable {B X : Scheme.{0}} {E : Type} [Field E] [Algebra ℂ E]

theorem curveDegree_eq_normalized
    (p : B ⟶ Spec (.of ℂ)) [IsProper p]
    (H : LineBundle B) (hH : H.IsAmple) (C : IntegralCurve B)
    (f : E) (hf : Transcendental ℂ f)
    [FiniteDimensional (IntermediateField.adjoin ℂ {f}) E]
    (g : parameterCurve f hf ⟶ C.scheme) [IsFinite g]
    (hg : g ≫ C.embedding ≫ p = parameterCurveStructureMap f hf)
    (W : C.scheme.Opens) (hW : W ≠ ⊥) [IsIso (g ∣_ W)] (L : LineBundle B) :
    curveDegree p L C =
      eulerCharacteristic (parameterCurveStructureMap f hf) 1
          (L.pullback (g ≫ C.embedding)).sheaf -
        eulerCharacteristic (parameterCurveStructureMap f hf) 1
          (structureSheaf (parameterCurve f hf)) := by
  have h := CurveNormalizationDegree.parameterCurve_pullback_euler_degree_of_ample
    (C.embedding ≫ p) (H.pullback C.embedding)
    (LineBundle.IsAmple.pullback_closedImmersion H hH C.embedding)
    C.dimension.le f hf g hg W hW (L.pullback C.embedding)
  have he := eulerCharacteristic_iso (parameterCurveStructureMap f hf)
    ((Scheme.Modules.pullbackComp g C.embedding).app L.sheaf) 1
  change eulerCharacteristic (parameterCurveStructureMap f hf) 1
    ((L.pullback C.embedding).pullback g).sheaf = _ at he
  rw [he] at h
  exact h.symm

end PiExponent.CurveNormalizedDegreeTransfer

end

end OAI
end Source0613

-- Source: LogTwo/Geometry/IntegralCurveDegree.lean
section Source0614
-- Modified in this edition: unused plain lemmas removed; see reduction.json.
/-! Actual curve degrees on the blowup. The noncontracted curve meeting the
affine chart supplies its own function field, generating coordinates and
normalization; none is postulated. Contracted and outside-chart curves and
the ampleness of A tensor J are separate later steps. -/
namespace LogTwo.Geometry.MatrixBlowup
open OAI PiExponent AlgebraicGeometry CategoryTheory
open PiExponentSeshadri.Geometry NumericalAmpleness
open LogTwo.Interpolation LogTwo.Parameters LogTwo.Arithmetic
noncomputable section

/-- Finite birational normalization preserves the actual curve degree. -/
theorem curveDegree_eq_modelDegree {m K : ℕ} (w : Weights m) (y : Fin K → ℂ)
    (hy0 : ∀ j, y j ≠ 0) (a : Fin K → Fin m → ℂ) (T : Fin m → ℕ)
    (C : IntegralCurve (space w y a T)) (r : CurveModel.ModelData w y a T C)
    (L : LineBundle (space w y a T)) :
    letI := r.field
    letI := r.algebra
    letI := r.parameterFinite
    (curveDegree (structureMap w y a T) L C : ℝ) =
      normalizationDegree r.parameter r.parameter_transcendental
        (r.normalization ≫ C.embedding) L := by
  let := r.field
  let := r.algebra
  let := r.parameterFinite
  let := r.normalizationFinite
  let := r.chartIso
  unfold normalizationDegree
  exact congrArg (fun d : ℤ => (d : ℝ)) <|
    CurveNormalizedDegreeTransfer.curveDegree_eq_normalized
    (structureMap w y a T) (H w y hy0 a T) (H_ample w y hy0 a T) C
    r.parameter r.parameter_transcendental r.normalization r.normalization_over
    r.chart r.chart_nonempty L

/-- The degree inequality on every noncontracted integral curve meeting the
actual affine chart, with its normalization data constructed internally. -/
theorem chosenWeights_integralCurve_degree_nonnegative
    (n : ℕ) (hn : 1 ≤ n) (m : ℕ) (q : ℕ → ℕ) (hq : ∀ i, 2 ≤ q i)
    (hgrowth : ∀ i, i < m →
      denominatorSeparationFactor n m (chosenComparisonConstant n m) *
        (∏ j : Fin i, (ceilLogWeight (q j) : ℝ)) < (ceilLogWeight (q i) : ℝ)) :
    let w := chosenWeights n hn m (fun i => q i) (fun i => hq i)
    ∀ (y : Fin w.K → ℂ), (∀ j, y j ≠ 0) → Function.Injective y →
      ∀ (a : Fin w.K → Fin m → ℂ) (F : ℚ), 1 / w.theta < F →
      ∀ (C : IntegralCurve (space w y a (truncationOrders w F))),
      (¬ ∃ x : MatrixCompactification.space w,
        Set.range (C.embedding ≫ projection w y a (truncationOrders w F)) ⊆ {x}) →
      (∃ p : C.scheme, (C.embedding ≫ projection w y a (truncationOrders w F)) p ∈
        (MatrixCompactification.affineChart w).opensRange) →
      0 ≤ (curveDegree (structureMap w y a (truncationOrders w F))
          (A w y a (truncationOrders w F)) C : ℝ) +
        (1 + (curveSigma w.theta m : ℝ)) *
          (curveDegree (structureMap w y a (truncationOrders w F))
            (J w y a (truncationOrders w F)) C : ℝ) := by
  dsimp only
  intro y hy0 hy a F hF C hnc hm
  let w := chosenWeights n hn m (fun i => q i) (fun i => hq i)
  obtain ⟨r⟩ := CurveModel.existsModelData w y a (truncationOrders w F) C hnc hm
  let := r.field
  let := r.algebra
  let := r.essFiniteType
  let := r.parameterFinite
  rw [curveDegree_eq_modelDegree w y hy0 a _ C r (A w y a _),
    curveDegree_eq_modelDegree w y hy0 a _ C r (J w y a _)]
  exact chosenWeights_degree_nonnegative r.parameter r.parameter_transcendental
    n hn m q hq hgrowth r.coordinates r.coordinates_generate r.trdeg_one y hy0 hy a F hF
    (r.normalization ≫ C.embedding) (by simpa only [Category.assoc] using r.generic_coordinates)

end
end LogTwo.Geometry.MatrixBlowup
end Source0614

-- Source: OAI/NumberTheory/PiExponent/Approximation/SectionImageSupport.lean
section Source0615
/-
Modification notice for the LogTwo project.
Derived from openai/math (Apache-2.0), revision adc7f1241b42e322a6451854ab7e4b4c146bf78a.
Original source: lean/OAI/NumberTheory/PiExponent/Approximation/SectionImageSupport.lean
Changes: Convert module/import declarations to the Lean 4.34 public module format.
See ../THIRD_PARTY_NOTICES.txt for provenance and the recorded changes.
-/

namespace OAI

namespace PiExponent.SectionImageSupport
noncomputable section
open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite
open PiExponentSeshadri PiExponentSeshadri.Geometry PiExponentSeshadri.Frames
open PiExponent.SectionImageIdeal

variable {X : Scheme.{0}} {M : X.Modules}

lemma isoOpen_preimage_on_frame (φ : M ⟶ structureSheaf X) (U : X.Opens)
    (e : M.restrict U.ι ≅ structureSheaf U.toScheme) :
    U.ι ⁻¹ᵁ SectionOpens.isoOpen φ = U.toScheme.basicOpen
      (endValue (e.inv ≫ (Scheme.Modules.restrictFunctor U.ι).map φ ≫
        (Scheme.Modules.restrictUnitIso U.ι).hom)) := by
  rw [← SectionOpens.isoOpen_restrict φ U.ι]
  let ψ := (Scheme.Modules.restrictFunctor U.ι).map φ
  calc
    SectionOpens.isoOpen ψ = SectionOpens.isoOpen
        (ψ ≫ (Scheme.Modules.restrictUnitIso U.ι).hom) :=
      (SectionOpens.isoOpen_postcomp ψ (Scheme.Modules.restrictUnitIso U.ι)).symm
    _ = SectionOpens.isoOpen (e.inv ≫ ψ ≫ (Scheme.Modules.restrictUnitIso U.ι).hom) :=
      (SectionOpens.isoOpen_precomp e.symm _).symm
    _ = _ := by
      simpa only [coefficient, Iso.refl_hom, Category.comp_id] using!
        (isoOpen_eq_basicOpen (Iso.refl (O U.toScheme))
          (e.inv ≫ ψ ≫ (Scheme.Modules.restrictUnitIso U.ι).hom))

lemma preimage_basicOpen_topIso_hom (U : X.Opens) (a : Γ(U.toScheme,⊤)) :
    U.ι ⁻¹ᵁ X.basicOpen (U.topIso.hom a) = U.toScheme.basicOpen a := by
  rw [← U.ι_image_basicOpen_topIso_inv (U.topIso.hom a), U.ι.preimage_image_eq]
  rw [Iso.hom_inv_id_apply]

theorem imageIdealSheaf_support (L : LineBundle X)
    (φ : L.sheaf ⟶ structureSheaf X) :
    letI := PiExponent.GeometrySupport.LineBundleCoherent.lineBundle_isFinitePresentation L
    letI : SheafOfModules.IsQuasicoherent L.sheaf :=
      (SheafOfModules.IsFinitePresentation.exists_quasicoherentData L.sheaf).choose.isQuasicoherent
    ((imageIdealSheaf φ).support : Set X) = (SectionOpens.isoOpen φ : Set X)ᶜ := by
  let := PiExponent.GeometrySupport.LineBundleCoherent.lineBundle_isFinitePresentation L
  let : SheafOfModules.IsQuasicoherent L.sheaf :=
    (SheafOfModules.IsFinitePresentation.exists_quasicoherentData L.sheaf).choose.isQuasicoherent
  ext x
  obtain ⟨V, hxV, ⟨eV⟩⟩ := L.locallyRankOne x
  obtain ⟨W, hW, hxW, hWV⟩ := exists_isAffineOpen_mem_and_subset hxV
  let A : X.affineOpens := ⟨W, hW⟩
  let e : L.sheaf.restrict W.ι ≅ structureSheaf W.toScheme := restrictOpenFrame hWV eV
  change x ∈ (imageIdealSheaf φ).support ↔ x ∉ SectionOpens.isoOpen φ
  rw [Scheme.IdealSheafData.mem_support_iff_of_mem (U := A) hxW,
    imageIdealSheaf_on_frame φ A e, X.zeroLocus_span, X.zeroLocus_singleton]
  apply not_congr
  change (⟨x, hxW⟩ : W.toScheme) ∈ W.ι ⁻¹ᵁ X.basicOpen
      (W.topIso.hom (endValue (e.inv ≫ (Scheme.Modules.restrictFunctor W.ι).map φ ≫
        (Scheme.Modules.restrictUnitIso W.ι).hom))) ↔
    (⟨x, hxW⟩ : W.toScheme) ∈ W.ι ⁻¹ᵁ SectionOpens.isoOpen φ
  rw [preimage_basicOpen_topIso_hom, isoOpen_preimage_on_frame φ W e]

end
end PiExponent.SectionImageSupport

end OAI
end Source0615

-- Source: OAI/NumberTheory/PiExponent/Approximation/SectionZeroSupport.lean
section Source0616
/-
Modification notice for the LogTwo project.
Derived from openai/math (Apache-2.0), revision adc7f1241b42e322a6451854ab7e4b4c146bf78a.
Original source: lean/OAI/NumberTheory/PiExponent/Approximation/SectionZeroSupport.lean
Changes: Convert module/import declarations to the Lean 4.34 public module format.
See ../THIRD_PARTY_NOTICES.txt for provenance and the recorded changes.
-/

namespace OAI

namespace PiExponent.SectionZeroIdeal
noncomputable section
open AlgebraicGeometry CategoryTheory TopologicalSpace
open PiExponentSeshadri.Geometry PiExponentSeshadri.Frames
open PiExponent.InverseFrames PiExponent.SectionImageSupport
variable {X : Scheme.{0}}

theorem dualSection_isoOpen (L : LineBundle X) (s : GlobalSections X L.sheaf) :
    PiExponentSeshadri.SectionOpens.isoOpen (L.dualSection s) = sectionOpen X s := by
  ext x
  obtain ⟨U,hx,⟨e⟩⟩ := L.locallyRankOne x
  change (⟨x,hx⟩ : U.toScheme) ∈ U.ι ⁻¹ᵁ PiExponentSeshadri.SectionOpens.isoOpen (L.dualSection s) ↔
    (⟨x,hx⟩ : U.toScheme) ∈ U.ι ⁻¹ᵁ PiExponentSeshadri.SectionOpens.isoOpen s
  erw [isoOpen_preimage_on_frame (L.dualSection s) U
    (inverseOpenFrame (lineTensorInverseIso L) U e), dualSection_restrict_coefficient,
    preimage_isoOpen s U.ι e]

theorem zeroIdeal_support (L : LineBundle X) (s : GlobalSections X L.sheaf) :
    ((zeroIdeal L s).support : Set X) = (sectionOpen X s : Set X)ᶜ := by
  let := PiExponent.GeometrySupport.LineBundleCoherent.lineBundle_isFinitePresentation L.inverse
  let : SheafOfModules.IsQuasicoherent L.inverse.sheaf :=
    (SheafOfModules.IsFinitePresentation.exists_quasicoherentData L.inverse.sheaf).choose.isQuasicoherent
  change ((PiExponent.SectionImageIdeal.imageIdealSheaf (L.dualSection s)).support : Set X) = _
  rw [imageIdealSheaf_support, dualSection_isoOpen]

end
end PiExponent.SectionZeroIdeal

end OAI
end Source0616

-- Source: OAI/NumberTheory/PiExponent/Ampleness/LineAmpleOperations.lean
section Source0617
/-
Modification notice for the LogTwo project.
Derived from openai/math (Apache-2.0), revision adc7f1241b42e322a6451854ab7e4b4c146bf78a.
Original source: lean/OAI/NumberTheory/PiExponent/Ampleness/LineAmpleOperations.lean
Changes: Convert module/import declarations to the Lean 4.34 public module format.
See ../THIRD_PARTY_NOTICES.txt for provenance and the recorded changes.
-/

namespace OAI

noncomputable section
namespace PiExponentSeshadri.Geometry
open AlgebraicGeometry CategoryTheory TopologicalSpace
open PiExponentSeshadri.Frames PiExponentSeshadri.TensorPure
variable {X : Scheme.{0}}

def lineTensorPow (L M : LineBundle X) : ∀ n : ℕ,
    ((L.tensor M).pow n).sheaf ≅ ((L.pow n).tensor (M.pow n)).sheaf
  | 0 => (moduleTensorUnit (structureSheaf X)).symm
  | n+1 =>
    moduleTensorIso (Iso.refl _) (lineTensorPow L M n) ≪≫
    lineTensorAssoc L M ((L.pow n).tensor (M.pow n)) ≪≫
    moduleTensorIso (Iso.refl L.sheaf)
      ((lineTensorAssoc M (L.pow n) (M.pow n)).symm ≪≫
        moduleTensorIso (moduleTensorComm M.sheaf (L.pow n).sheaf) (Iso.refl _) ≪≫
        lineTensorAssoc (L.pow n) M (M.pow n)) ≪≫
    (lineTensorAssoc L (L.pow n) (M.pow (n+1))).symm

theorem LineBundle.IsAmple.pow {L : LineBundle X} (hL : L.IsAmple) (d : ℕ) (hd : 0 < d) :
    (L.pow d).IsAmple := by
  intro x V hx
  obtain ⟨n,hn,s,hs,hsub,ha⟩ := hL x V hx
  let e : ((L.pow n).pow d).sheaf ≅ ((L.pow d).pow n).sheaf :=
    linePowerMul L n d ≪≫ eqToIso (congrArg (fun j => (L.pow j).sheaf) (Nat.mul_comm n d)) ≪≫
      (linePowerMul L d n).symm
  let t := powerSection s d ≫ e.hom
  have ht : sectionOpen X t = sectionOpen X s := by
    exact (PiExponent.AmpleIso.sectionOpen_postcomp_iso (powerSection s d) e).trans
      ((L.pow n).sectionOpen_power s hd)
  exact ⟨n, hn, t, ht.symm ▸ hs, ht.le.trans hsub, ht.symm ▸ ha⟩

theorem LineBundle.IsAmple.tensor {L M : LineBundle X}
    (hL : L.IsAmple) (hM : M.IsAmple) : (L.tensor M).IsAmple := by
  intro x V hx
  obtain ⟨n, hn, s, hxs, hsV, _⟩ := hL x V hx
  obtain ⟨m, hm, t, hxt, hts, hta⟩ := hM x (sectionOpen X s) hxs
  let e : ((M.pow m).pow n).sheaf ≅ (M.pow (n*m)).sheaf :=
    linePowerMul M m n ≪≫ eqToIso (congrArg (fun j => (M.pow j).sheaf) (Nat.mul_comm m n))
  let a : structureSheaf X ⟶ (L.pow (n*m)).sheaf :=
    powerSection s m ≫ (linePowerMul L n m).hom
  let b : structureSheaf X ⟶ (M.pow (n*m)).sheaf := powerSection t n ≫ e.hom
  have ha : sectionOpen X a = sectionOpen X s := by
    exact (PiExponent.AmpleIso.sectionOpen_postcomp_iso
      (powerSection s m) (linePowerMul L n m)).trans ((L.pow n).sectionOpen_power s hm)
  have hb : sectionOpen X b = sectionOpen X t := by
    exact (PiExponent.AmpleIso.sectionOpen_postcomp_iso (powerSection t n) e).trans
      ((M.pow m).sectionOpen_power t hn)
  let q := tensorSection a b ≫ (lineTensorPow L M (n*m)).inv
  have hq : sectionOpen X q = sectionOpen X t := by
    exact (PiExponent.AmpleIso.sectionOpen_postcomp_iso
      (tensorSection a b) (lineTensorPow L M (n*m)).symm).trans
        ((section_open (L.pow (n*m)) (M.pow (n*m)) a b).trans
          ((congrArg₂ (fun U V : X.Opens => U ⊓ V) ha hb).trans (inf_eq_right.mpr hts)))
  exact ⟨n*m, Nat.mul_pos hn hm, q, hq.symm ▸ hxt,
    hq.le.trans (hts.trans hsV), hq.symm ▸ hta⟩

end PiExponentSeshadri.Geometry

end

end OAI
end Source0617

-- Source: OAI/NumberTheory/PiExponent/Ampleness/ZeroDimensionalAmple.lean
section Source0618
/-
Modification notice for the LogTwo project.
Derived from openai/math (Apache-2.0), revision adc7f1241b42e322a6451854ab7e4b4c146bf78a.
Original source: lean/OAI/NumberTheory/PiExponent/Ampleness/ZeroDimensionalAmple.lean
Changes: Convert module/import declarations to the Lean 4.34 public module format.
See ../THIRD_PARTY_NOTICES.txt for provenance and the recorded changes.
-/

namespace OAI

namespace PiExponent.NumericalAmpleness
noncomputable section
open AlgebraicGeometry CategoryTheory TopologicalSpace
open PiExponentSeshadri.Geometry PiExponentSeshadri.Frames
variable {X : Scheme.{0}}

theorem isAmple_of_global_frame_affine [IsAffine X] (L : LineBundle X)
    (e : L.sheaf ≅ structureSheaf X) : L.IsAmple := by
  intro x V hx
  obtain ⟨r,hr,hxr⟩ := (isAffineOpen_top X).exists_basicOpen_le ⟨x,hx⟩ (by trivial)
  let E := globalPowerFrame e 1
  let s : GlobalSections X (L.pow 1).sheaf := scalarEnd r ≫ E.inv
  have he : coefficient E s = r := by
    have hcomp : (scalarEnd r ≫ E.inv) ≫ E.hom = scalarEnd r := by
      exact (Category.assoc (scalarEnd r) E.inv E.hom).trans
        ((congrArg (fun g : structureSheaf X ⟶ structureSheaf X => scalarEnd r ≫ g)
          E.inv_hom_id).trans (Category.comp_id (scalarEnd r)))
    exact (congrArg (fun f : structureSheaf X ⟶ structureSheaf X => endValue f)
      hcomp).trans (endValue_scalarEnd r)
  have hopen : sectionOpen X s = X.basicOpen r := by
    change PiExponentSeshadri.SectionOpens.isoOpen s = _
    exact (isoOpen_eq_basicOpen E s).trans (congrArg X.basicOpen he)
  exact ⟨1,by decide,s,hopen.symm ▸ hxr,hopen.le.trans hr,hopen.symm ▸ (isAffineOpen_top X).basicOpen r⟩

theorem isAmple_of_proper_dimension_zero [IsLocallyNoetherian X]
    (p : X ⟶ Spec (CommRingCat.of ℂ)) [IsProper p]
    (hdim : topologicalKrullDim X ≤ 0) (L : LineBundle X) : L.IsAmple := by
  let : IsLocallyArtinian X := IsLocallyArtinian.of_topologicalKrullDim_le_zero hdim
  let : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace p
  let : Finite X := finite_of_compact_of_discrete
  let : IsAffine X := proper_finite_scheme_isAffine p
  obtain ⟨e⟩ := PiExponentSeshadri.FiniteSupport.lineBundle_trivial L
  exact isAmple_of_global_frame_affine L e

end
end PiExponent.NumericalAmpleness

end OAI
end Source0618

-- Source: OAI/NumberTheory/PiExponent/Ampleness/AmpleAllPowersGeneration.lean
section Source0619
/-
Modification notice for the LogTwo project.
Derived from openai/math (Apache-2.0), revision adc7f1241b42e322a6451854ab7e4b4c146bf78a.
Original source: lean/OAI/NumberTheory/PiExponent/Ampleness/AmpleAllPowersGeneration.lean
Changes: Convert module/import declarations to the Lean 4.34 public module format.
See ../THIRD_PARTY_NOTICES.txt for provenance and the recorded changes.
-/

namespace OAI

namespace PiExponent.AmpleGlobalGeneration
noncomputable section
open AlgebraicGeometry CategoryTheory TopologicalSpace
open PiExponentSeshadri.Geometry
variable {X : Scheme.{0}}

theorem ample_eventual_global_generators [NoetherianSpace X]
    (L : LineBundle X) (hL : L.IsAmple) (M : X.Modules) [M.IsFinitePresentation] :
    ∃ N : ℕ, ∀ n ≥ N,
      ∃ G : ((moduleTwistFunctor L n).obj M).GeneratingSections, G.IsFiniteType := by
  classical
  obtain ⟨d, hd, l, s, hcover, haffine, _⟩ := L.ample_common_degree_cover hL
  have hresidue (r : Fin d) : ∃ N : ℕ, ∀ n ≥ N,
      ∃ G : ((moduleTwistFunctor (L.pow d) n).obj
        ((moduleTwistFunctor L r.val).obj M)).GeneratingSections, G.IsFiniteType := by
    let := PiExponent.FiniteGlobalPresentation.moduleTwist_isFinitePresentation L r.val M
    exact eventual_global_generators_of_section_cover (L.pow d)
      ((moduleTwistFunctor L r.val).obj M) s hcover haffine
  choose N hN using hresidue
  let B := Finset.univ.sup N
  refine ⟨d * B, fun n hn => ?_⟩
  let r : Fin d := ⟨n % d, Nat.mod_lt n hd⟩
  have hB : B ≤ n / d := (Nat.le_div_iff_mul_le hd).mpr (by
    simpa only [Nat.mul_comm] using hn)
  have hr : N r ≤ n / d := (Finset.le_sup (f := N) (Finset.mem_univ r)).trans hB
  obtain ⟨G, hG⟩ := hN r (n / d) hr
  let : G.IsFiniteType := hG
  let e : ((moduleTwistFunctor (L.pow d) (n / d)).obj
      ((moduleTwistFunctor L r.val).obj M)) ≅ (moduleTwistFunctor L n).obj M :=
    moduleTwistPowerMulIso L ((moduleTwistFunctor L r.val).obj M) d (n / d) ≪≫
      eqToIso (by
        change (moduleTwistFunctor L (n % d) ⋙
          moduleTwistFunctor L (d * (n / d))).obj M = _
        rw [← moduleTwistFunctor_add, Nat.mod_add_div])
  exact ⟨SheafOfModules.GeneratingSections.equivOfIso e G, ⟨hG.finite⟩⟩

theorem ample_eventual_power_global_generators [NoetherianSpace X]
    (L : LineBundle X) (hL : L.IsAmple) :
    ∃ N : ℕ, ∀ n ≥ N,
      ∃ G : (modulePow X L.sheaf n).GeneratingSections, G.IsFiniteType := by
  let : (structureSheaf X).IsFinitePresentation :=
    PiExponent.GeometrySupport.LineBundleCoherent.structureSheaf_isFinitePresentation
  obtain ⟨N, hN⟩ := ample_eventual_global_generators L hL (structureSheaf X)
  refine ⟨N, fun n hn => ?_⟩
  obtain ⟨G, hG⟩ := hN n hn
  let : G.IsFiniteType := hG
  exact ⟨SheafOfModules.GeneratingSections.equivOfIso (moduleTwistUnitIso L n) G,
    ⟨hG.finite⟩⟩

end
end PiExponent.AmpleGlobalGeneration

end OAI
end Source0619

-- Source: OAI/NumberTheory/PiExponent/Approximation/GeneratorsSectionCover.lean
section Source0620
/-
Modification notice for the LogTwo project.
Derived from openai/math (Apache-2.0), revision adc7f1241b42e322a6451854ab7e4b4c146bf78a.
Original source: lean/OAI/NumberTheory/PiExponent/Approximation/GeneratorsSectionCover.lean
Changes: Convert module/import declarations to the Lean 4.34 public module format.
Expose private helpers and adjust helper names where needed for module compatibility.
See ../THIRD_PARTY_NOTICES.txt for provenance and the recorded changes.
-/

namespace OAI

namespace PiExponent.GeneratorsSectionCover
noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite
open PiExponentSeshadri.Geometry PiExponentSeshadri.Frames PiExponentSeshadri.SectionOpens
variable {X : Scheme.{0}}

private lemma epi_iso_comp {C : Type*} [Category C] {A B D E : C}
    (i : A ≅ B) (f : B ⟶ D) (e : D ≅ E) [Epi f] :
    Epi (i.hom ≫ f ≫ e.hom) := inferInstance

abbrev schemeFree (X : Scheme.{0}) (ι : Type) : X.Modules :=
  SheafOfModules.free ι

abbrev schemeInclusion {X : Scheme.{0}} {ι : Type} (i : ι) :
    O X ⟶ schemeFree X ι := SheafOfModules.ιFree i

def freeProjection {ι : Type} [DecidableEq ι] (i : ι) :
    schemeFree X ι ⟶ O X :=
  Sigma.desc (C := X.Modules) (f := fun _ : ι => O X) (fun j => if j = i then 𝟙 _ else 0)

@[simp] theorem free_inclusion_projection {ι : Type} [DecidableEq ι] (i j : ι) :
    schemeInclusion j ≫ freeProjection (X := X) i = if j = i then 𝟙 _ else 0 := by
  exact Sigma.ι_comp_desc (C := X.Modules) (f := fun _ : ι => O X) _ _

theorem free_sum_projection_inclusion {ι : Type} [Fintype ι] [DecidableEq ι] :
    (∑ i : ι, freeProjection (X := X) i ≫ schemeInclusion i) =
      𝟙 (schemeFree X ι) := by
  apply (SheafOfModules.isColimitFreeCofan ι).hom_ext
  intro j
  change schemeInclusion j.as ≫ _ = schemeInclusion j.as ≫ _
  simp only [Preadditive.comp_sum, ← Category.assoc, free_inclusion_projection]
  simp only [ite_comp, Category.id_comp, zero_comp, Fintype.sum_ite_eq, Category.comp_id]

lemma hom_sum_app {M N : X.Modules} {ι : Type} (S : Finset ι)
    (f : ι → (M ⟶ N)) (V : X.Opens) (z : Γ(M,V)) :
    (∑ i ∈ S, f i).app V z = ∑ i ∈ S, (f i).app V z := by
  classical
  induction S using Finset.induction_on with
  | empty => rfl
  | @insert a S ha ih =>
    simp only [Finset.sum_insert ha, Scheme.Modules.Hom.add_app]
    change (f a).app V z + (∑ i ∈ S, f i).app V z = _
    rw [ih]

theorem unit_epimorphism_cover {ι : Type} [Finite ι]
    (f : schemeFree X ι ⟶ O X) [Epi f] :
    (⨆ i : ι, isoOpen (schemeInclusion i ≫ f)) = ⊤ := by
  classical
  let : Fintype ι := Fintype.ofFinite ι
  apply top_unique
  intro x _
  let F : X.Modules ⥤ _ := SheafOfModules.toSheaf X.ringCatSheaf
  have : F.PreservesEpimorphisms :=
    inferInstanceAs (SheafOfModules.toSheaf X.ringCatSheaf).PreservesEpimorphisms
  have hFf : Epi (F.map f) := F.map_epi f
  have hloc : TopCat.Presheaf.IsLocallySurjective (F.map f).hom :=
    (TopCat.Sheaf.isLocallySurjective_iff_epi _).mpr hFf
  obtain ⟨V, hV, ⟨z, hz⟩, hxV⟩ :=
    (TopCat.Presheaf.isLocallySurjective_iff _).mp hloc ⊤ (1 : Γ(X,⊤)) x trivial
  change Scheme.Modules.Hom.app f V z = X.presheaf.map (homOfLE hV).op (1 : Γ(X,⊤)) at hz
  rw [map_one] at hz
  have he : (∑ i : ι, freeProjection (X := X) i ≫ (schemeInclusion i ≫ f)) = f := by
    simp only [← Category.assoc]
    rw [← Preadditive.sum_comp, free_sum_projection_inclusion, Category.id_comp]
  have hsum : (∑ i : ι, Scheme.Modules.Hom.app (schemeInclusion i ≫ f) V
      (Scheme.Modules.Hom.app (freeProjection (X := X) i) V z)) = (1 : Γ(X,V)) := by
    exact (hom_sum_app Finset.univ
      (fun i => freeProjection (X := X) i ≫ (schemeInclusion i ≫ f)) V z).symm.trans
      ((congrArg (fun q : (schemeFree X ι : X.Modules) ⟶ O X =>
        Scheme.Modules.Hom.app q V z) he).trans hz)
  have hsum' : (∑ i : ι, X.presheaf.germ V x hxV
      (Scheme.Modules.Hom.app (schemeInclusion i ≫ f) V (Scheme.Modules.Hom.app (freeProjection (X := X) i) V z))) = 1 := by
    exact (map_sum (X.presheaf.germ V x hxV).hom _ _).symm.trans
      ((congrArg (X.presheaf.germ V x hxV) hsum).trans (X.presheaf.germ V x hxV).hom.map_one)
  obtain ⟨i, _, hi⟩ := IsLocalRing.exists_of_isUnit_sum (hsum' ▸ isUnit_one)
  have hc : IsUnit (X.presheaf.germ ⊤ x trivial
      (endValue (schemeInclusion i ≫ f))) := by
    let si : O X ⟶ O X := schemeInclusion i ≫ f
    let a : Γ(X,V) := Scheme.Modules.Hom.app (freeProjection (X := X) i) V z
    have ht := end_apply si V a
    have hi' : IsUnit (X.presheaf.germ V x hxV
        (a * (show Γ(X,V) from si.app V (1 : Γ(X,V))))) := ht ▸ hi
    have hc' : IsUnit (X.presheaf.germ V x hxV
        (show Γ(X,V) from si.app V (1 : Γ(X,V)))) := by
      rw [map_mul] at hi'
      exact isUnit_of_mul_isUnit_right hi'
    have hcoeff := congrArg (fun z : Γ(X,V) => X.presheaf.germ V x hxV z)
      (end_naturality si V)
    rw [X.presheaf.germ_res_apply] at hcoeff
    exact hcoeff ▸ hc'
  apply Opens.mem_iSup.mpr
  refine ⟨i, ?_⟩
  erw [isoOpen_eq_basicOpen (Iso.refl (O X))]
  change x ∈ X.basicOpen (endValue (schemeInclusion i ≫ f))
  exact (X.mem_basicOpen (endValue (schemeInclusion i ≫ f)) x (show x ∈ (⊤ : X.Opens) from trivial)).mpr hc

def generatorSection (L : LineBundle X) (G : L.sheaf.GeneratingSections) (i : G.I) :
    GlobalSections X L.sheaf := schemeInclusion i ≫ G.π

theorem generators_sectionOpen_cover (L : LineBundle X)
    (G : L.sheaf.GeneratingSections) [G.IsFiniteType] :
    (⨆ i : G.I, sectionOpen X (generatorSection L G i)) = ⊤ := by
  apply top_unique
  intro x _
  obtain ⟨U, hx, ⟨e⟩⟩ := L.locallyRankOne x
  let F : SheafOfModules X.ringCatSheaf ⥤ SheafOfModules U.toScheme.ringCatSheaf :=
    Scheme.Modules.restrictFunctor U.ι
  have : PreservesColimitsOfSize.{0,0} F :=
    inferInstanceAs (PreservesColimitsOfSize.{0,0} (Scheme.Modules.restrictFunctor U.ι))
  let η := (Scheme.Modules.restrictUnitIso U.ι).symm
  let f : schemeFree U.toScheme G.I ⟶ O U.toScheme :=
    (SheafOfModules.mapFreeIso F G.I η).hom ≫ F.map G.π ≫ e.hom
  have hπ : Epi (F.map G.π) := @Functor.map_epi _ _ _ _ F _ _ _ G.π G.epi
  have : Epi f := @epi_iso_comp _ _ _ _ _ _
    (SheafOfModules.mapFreeIso F G.I η) (F.map G.π) e hπ
  let : Finite G.I := (inferInstance : G.IsFiniteType).finite
  have hf := unit_epimorphism_cover f
  obtain ⟨i, hi⟩ := Opens.mem_iSup.mp
    (show (⟨x,hx⟩ : U.toScheme) ∈ ⨆ i : G.I, isoOpen (schemeInclusion i ≫ f) by
      rw [hf]; trivial)
  have he : schemeInclusion i ≫ f =
      restrictSection U.ι (generatorSection L G i) ≫ e.hom := by
    dsimp only [f, generatorSection, restrictSection]
    erw [← Category.assoc, ← Category.assoc, SheafOfModules.ιFree_mapFreeIso_hom]
    erw [F.map_comp]
    exact Category.assoc _ _ _
  erw [he, isoOpen_postcomp, isoOpen_restrictSection] at hi
  exact Opens.mem_iSup.mpr ⟨i, hi⟩

theorem exists_fin_section_cover (L : LineBundle X)
    (G : L.sheaf.GeneratingSections) [G.IsFiniteType] :
    ∃ k : ℕ, ∃ s : Fin k → GlobalSections X L.sheaf,
      (⨆ i, sectionOpen X (s i)) = ⊤ := by
  let : Finite G.I := (inferInstance : G.IsFiniteType).finite
  let : Fintype G.I := Fintype.ofFinite G.I
  let e := (Fintype.equivFin G.I).symm
  exact ⟨Fintype.card G.I, fun i => generatorSection L G (e i),
    (e.iSup_comp (g := fun i => sectionOpen X (generatorSection L G i))).trans
      (generators_sectionOpen_cover L G)⟩

theorem ample_eventual_fin_section_cover [NoetherianSpace X]
    (L : LineBundle X) (hL : L.IsAmple) :
    ∃ N : ℕ, ∀ n ≥ N, ∃ k : ℕ,
      ∃ s : Fin k → GlobalSections X (modulePow X L.sheaf n),
        (⨆ i, sectionOpen X (s i)) = ⊤ := by
  obtain ⟨N, hN⟩ := AmpleGlobalGeneration.ample_eventual_power_global_generators L hL
  refine ⟨N, fun n hn => ?_⟩
  obtain ⟨G, hG⟩ := hN n hn
  let : G.IsFiniteType := hG
  exact @exists_fin_section_cover X (L.pow n) G hG

end
end PiExponent.GeneratorsSectionCover

end OAI
end Source0620

-- Source: OAI/NumberTheory/PiExponent/Approximation/RegularSectionMono.lean
section Source0621
/-
Modification notice for the LogTwo project.
Derived from openai/math (Apache-2.0), revision adc7f1241b42e322a6451854ab7e4b4c146bf78a.
Original source: lean/OAI/NumberTheory/PiExponent/Approximation/RegularSectionMono.lean
Changes: Convert module/import declarations to the Lean 4.34 public module format.
See ../THIRD_PARTY_NOTICES.txt for provenance and the recorded changes.
-/

namespace OAI

namespace PiExponent.NumericalAmpleness
noncomputable section
open AlgebraicGeometry CategoryTheory TopologicalSpace
open PiExponentSeshadri.Geometry PiExponentSeshadri.Frames
variable {X : Scheme.{0}}

theorem affine_scalar_regular_on_open [IsAffine X] (r : Γ(X, ⊤))
    (hr : r ∈ nonZeroDivisors Γ(X, ⊤)) (U : X.Opens) :
    Function.Injective (fun a : Γ(X, U) =>
      X.presheaf.map (homOfLE (show U ≤ ⊤ from le_top)).op r * a) := by
  intro a b hab
  apply TopCat.Presheaf.section_ext X.sheaf U a b
  intro x hx
  let : Algebra Γ(X, ⊤) (X.presheaf.stalk x) :=
    TopCat.Presheaf.algebra_section_stalk X.presheaf (⟨x, trivial⟩ : (⊤ : X.Opens))
  have : IsLocalization.AtPrime (X.presheaf.stalk x)
      ((isAffineOpen_top X).primeIdealOf ⟨x, trivial⟩).asIdeal :=
    (isAffineOpen_top X).isLocalization_stalk ⟨x, trivial⟩
  have hreg : X.presheaf.germ ⊤ x trivial r ∈ nonZeroDivisors (X.presheaf.stalk x) :=
    IsLocalization.nonZeroDivisors_le_comap
      (((isAffineOpen_top X).primeIdealOf ⟨x, trivial⟩).asIdeal.primeCompl) (X.presheaf.stalk x) hr
  have h := congrArg (fun v : Γ(X, U) => X.presheaf.germ U x hx v) hab
  simp only [map_mul, TopCat.Presheaf.germ_res_apply] at h
  exact (isRegular_iff_mem_nonZeroDivisors.mpr hreg).left h

theorem scalarEnd_mono_of_regular [IsAffine X] (r : Γ(X, ⊤))
    (hr : r ∈ nonZeroDivisors Γ(X, ⊤)) : Mono (scalarEnd r) := by
  have hm : Mono (scalarEnd r).val := by
    apply PresheafOfModules.mono_of_injective
    intro U
    exact affine_scalar_regular_on_open r hr U.unop
  exact (SheafOfModules.forget X.ringCatSheaf).mono_of_mono_map hm

theorem framed_section_mono_of_regular [IsAffine X] {M : X.Modules}
    (e : M ≅ O X) (s : O X ⟶ M)
    (hr : coefficient e s ∈ nonZeroDivisors Γ(X, ⊤)) : Mono s := by
  have he : s ≫ e.hom = scalarEnd (coefficient e s) := by
    apply endValue_injective
    rw [endValue_scalarEnd]
    rfl
  have hm : Mono (s ≫ e.hom) := by
    rw [he]
    exact scalarEnd_mono_of_regular _ hr
  exact (mono_comp_iff_of_mono s e.hom).mp hm

theorem section_mono_of_regular_affine_frames (L : LineBundle X)
    (s : GlobalSections X L.sheaf)
    (H : ∀ x : X, ∃ U : X.affineOpens, x ∈ U.1 ∧
      ∃ e : L.sheaf.restrict U.1.ι ≅ O U.1.toScheme,
        coefficient e (restrictSection U.1.ι s) ∈
          nonZeroDivisors Γ(U.1.toScheme, ⊤)) : Mono s := by
  apply CoherentTwist.mono_of_local
  intro x
  obtain ⟨U, hx, e, he⟩ := H x
  have : IsAffine U.1.toScheme := U.2
  have hm : Mono (restrictSection U.1.ι s) := framed_section_mono_of_regular e _ he
  refine ⟨U.1, hx, ?_⟩
  let : IsIso (Scheme.Modules.restrictUnitIso U.1.ι).inv :=
    (Scheme.Modules.restrictUnitIso U.1.ι).isIso_inv
  exact (mono_comp_iff_of_isIso (Scheme.Modules.restrictUnitIso U.1.ι).inv _).mp hm

end
end PiExponent.NumericalAmpleness

end OAI
end Source0621

-- Source: OAI/NumberTheory/PiExponent/LocalAlgebra/AssociatedPrimeAvoidance.lean
section Source0622
/-
Modification notice for the LogTwo project.
Derived from openai/math (Apache-2.0), revision adc7f1241b42e322a6451854ab7e4b4c146bf78a.
Original source: lean/OAI/NumberTheory/PiExponent/LocalAlgebra/AssociatedPrimeAvoidance.lean
Changes: Convert module/import declarations to the Lean 4.34 public module format.
See ../THIRD_PARTY_NOTICES.txt for provenance and the recorded changes.
-/

namespace OAI

namespace PiExponent.GeometrySupport.AssociatedPrimeAvoidance
noncomputable section
open scoped BigOperators

theorem exists_regular_combination
    {K ι J : Type*} [Field K] [Infinite K] [Finite ι] [Fintype J]
    (R : ι → Type*) [∀ i, CommRing (R i)] [∀ i, Algebra K (R i)]
    [∀ i, IsNoetherianRing (R i)] (a : ∀ i, J → R i)
    (hspan : ∀ i, Ideal.span (Set.range (a i)) = ⊤) :
    ∃ c : J → K, ∀ i, (∑ j, c j • a i j) ∈ nonZeroDivisors (R i) := by
  classical
  let : Fintype ι := Fintype.ofFinite ι
  let (i : ι) : Fintype (associatedPrimes (R i) (R i)) :=
    (associatedPrimes.finite (R i) (R i)).fintype
  let B := (i : ι) × associatedPrimes (R i) (R i)
  let L (i : ι) : (J → K) →ₗ[K] R i := Fintype.linearCombination K (a i)
  let bad (b : B) : Submodule K (J → K) :=
    (b.2.val.restrictScalars K).comap (L b.1)
  have hbad : ∀ b : B, bad b ≠ ⊤ := by
    intro b hb
    apply b.2.property.isPrime.ne_top
    apply top_unique
    rw [← hspan b.1]
    apply Ideal.span_le.mpr
    rintro _ ⟨j, rfl⟩
    have hm : Pi.single j (1 : K) ∈ bad b := by
      rw [hb]
      trivial
    change Fintype.linearCombination K (a b.1) (Pi.single j 1) ∈ b.2.val at hm
    rw [Fintype.linearCombination_apply_single, one_smul] at hm
    exact hm
  obtain ⟨c, hc⟩ := Submodule.exists_forall_notMem_of_forall_ne_top bad hbad
  refine ⟨c, fun i => ?_⟩
  by_contra hn
  have hz : (∑ j, c j • a i j) ∈ (nonZeroDivisors (R i) : Set (R i))ᶜ := hn
  rw [← biUnion_associatedPrimes_eq_compl_nonZeroDivisors (R i)] at hz
  obtain ⟨P, hP, hmem⟩ := Set.mem_iUnion₂.mp hz
  apply hc ⟨i, ⟨P, hP⟩⟩
  change (∑ j, c j • a i j) ∈ P
  exact hmem

end
end PiExponent.GeometrySupport.AssociatedPrimeAvoidance

end OAI
end Source0622

-- Source: OAI/NumberTheory/PiExponent/Approximation/RegularSectionChoice.lean
section Source0623
/-
Modification notice for the LogTwo project.
Derived from openai/math (Apache-2.0), revision adc7f1241b42e322a6451854ab7e4b4c146bf78a.
Original source: lean/OAI/NumberTheory/PiExponent/Approximation/RegularSectionChoice.lean
Changes: Convert module/import declarations to the Lean 4.34 public module format.
See ../THIRD_PARTY_NOTICES.txt for provenance and the recorded changes.
-/

namespace OAI

namespace PiExponent.NumericalAmpleness
noncomputable section
open AlgebraicGeometry CategoryTheory TopologicalSpace
open PiExponentSeshadri.Geometry PiExponentSeshadri.Frames
variable {X : Scheme.{0}}

theorem finite_affine_frame_cover [CompactSpace X] (L : LineBundle X) :
    ∃ l : ℕ, ∃ U : Fin l → X.affineOpens,
      (⨆ i, (U i).1) = ⊤ ∧
      Nonempty (∀ i, L.sheaf.restrict (U i).1.ι ≅ O (U i).1.toScheme) := by
  classical
  have h (x : X) : ∃ U : X.affineOpens, x ∈ U.1 ∧
      Nonempty (L.sheaf.restrict U.1.ι ≅ O U.1.toScheme) := by
    obtain ⟨U, hx, he, _⟩ := common_affine_frames L L x
    exact ⟨U, hx, he⟩
  choose U hx e using h
  obtain ⟨I,hI⟩ := isCompact_univ.elim_finite_subcover
    (fun x => ((U x).1 : Set X)) (fun x => (U x).1.isOpen)
    (by intro x _; exact Set.mem_iUnion.mpr ⟨x,hx x⟩)
  let E := (Fintype.equivFin I).symm
  refine ⟨Fintype.card I, fun j => U (E j).val, ?_, ?_⟩
  · apply top_unique
    intro x _
    obtain ⟨i,hi⟩ := Set.mem_iUnion.mp (hI (show x ∈ Set.univ from trivial))
    obtain ⟨hi,hx⟩ := Set.mem_iUnion.mp hi
    apply Opens.mem_iSup.mpr
    refine ⟨E.symm ⟨i,hi⟩,?_⟩
    change x ∈ (U (E (E.symm ⟨i,hi⟩)).val).1
    rw [Equiv.apply_symm_apply]
    exact hx
  · exact ⟨fun j => (e (E j).val).some⟩

theorem coefficients_span_top_of_section_cover (L : LineBundle X) {k : ℕ}
    (s : Fin k → GlobalSections X L.sheaf)
    (hs : (⨆ j, sectionOpen X (s j)) = ⊤)
    (U : X.affineOpens) (e : L.sheaf.restrict U.1.ι ≅ O U.1.toScheme) :
    Ideal.span (Set.range (fun j => coefficient e (restrictSection U.1.ι (s j)))) = ⊤ := by
  have : IsAffine U.1.toScheme := U.2
  have hc : (⨆ j, U.1.toScheme.basicOpen (coefficient e (restrictSection U.1.ι (s j)))) = ⊤ := by
    exact (iSup_congr fun j => (preimage_isoOpen (s j) U.1.ι e).symm).trans
      (U.1.ι.iSup_preimage_eq_top hs)
  apply (isAffineOpen_top U.1.toScheme).iSup_basicOpen_eq_self_iff.mp
  apply top_unique
  intro x _
  obtain ⟨j, hj⟩ := Opens.mem_iSup.mp (show x ∈ ⨆ j,
    U.1.toScheme.basicOpen (coefficient e (restrictSection U.1.ι (s j))) by rw [hc]; trivial)
  exact Opens.mem_iSup.mpr ⟨⟨_, Set.mem_range_self j⟩, hj⟩

def localCoefficientAddHom (L : LineBundle X) (U : X.Opens)
    (e : L.sheaf.restrict U.ι ≅ O U.toScheme) :
    GlobalSections X L.sheaf →+ Γ(U.toScheme, ⊤) where
  toFun s := coefficient e (restrictSection U.ι s)
  map_zero' := by
    exact (congrArg (coefficient e) (restrictSection_zero U.ι)).trans (coefficient_zero e)
  map_add' s t := by
    simp only [coefficient, restrictSection]
    erw [(Scheme.Modules.restrictFunctor U.ι).map_add (f := s) (g := t),
      Preadditive.comp_add, Preadditive.add_comp]
    rfl

private theorem iso_inv_map_comp {C D : Type*} [Category C] [Category D]
    (F : C ⥤ D) {A B : C} {T : D} (e : F.obj A ≅ T) (f : A ⟶ A) (s : A ⟶ B) :
    e.inv ≫ F.map (f ≫ s) = ((e.inv ≫ F.map f) ≫ e.hom) ≫ e.inv ≫ F.map s := by
  simp only [Functor.map_comp, Category.assoc, Iso.hom_inv_id_assoc]

theorem localCoefficient_scalar (L : LineBundle X) (U : X.Opens)
    (e : L.sheaf.restrict U.ι ≅ O U.toScheme)
    (r : Γ(X, ⊤)) (s : GlobalSections X L.sheaf) :
    coefficient e (restrictSection U.ι (scalarEnd r ≫ s)) =
      U.ι.appTop r * coefficient e (restrictSection U.ι s) := by
  have hscalar : restrictSection U.ι (scalarEnd r) ≫
      (Scheme.Modules.restrictUnitIso U.ι).hom = scalarEnd (U.ι.appTop r) := by
    apply endValue_injective
    erw [endValue_restrict U.ι (scalarEnd r), endValue_scalarEnd, endValue_scalarEnd]
  have hrestrict : restrictSection U.ι (scalarEnd r ≫ s) =
      scalarEnd (U.ι.appTop r) ≫ restrictSection U.ι s := by
    rw [← hscalar]
    exact iso_inv_map_comp (Scheme.Modules.restrictFunctor U.ι)
      (Scheme.Modules.restrictUnitIso U.ι) (scalarEnd r) s
  rw [hrestrict]
  change endValue (scalarEnd (U.ι.appTop r) ≫ restrictSection U.ι s ≫ e.hom) = _
  rw [endValue_comp, endValue_scalarEnd]
  rfl

def sectionLinearCombination (L : LineBundle X) {k : ℕ}
    (a : ℂ →+* Γ(X, ⊤)) (s : Fin k → GlobalSections X L.sheaf) (c : Fin k → ℂ) :
    GlobalSections X L.sheaf := ∑ j, scalarEnd (a (c j)) ≫ s j

theorem localCoefficient_linearCombination (L : LineBundle X) {k : ℕ}
    (a : ℂ →+* Γ(X, ⊤)) (s : Fin k → GlobalSections X L.sheaf) (c : Fin k → ℂ)
    (U : X.Opens) (e : L.sheaf.restrict U.ι ≅ O U.toScheme) :
    coefficient e (restrictSection U.ι (sectionLinearCombination L a s c)) =
      ∑ j, U.ι.appTop (a (c j)) * coefficient e (restrictSection U.ι (s j)) := by
  change localCoefficientAddHom L U e (∑ j, scalarEnd (a (c j)) ≫ s j) = _
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro j _
  exact localCoefficient_scalar L U e _ _

theorem exists_mono_linearCombination_of_finite_cover [IsNoetherian X]
    (L : LineBundle X) {k : ℕ} (a : ℂ →+* Γ(X, ⊤))
    (s : Fin k → GlobalSections X L.sheaf)
    (hs : (⨆ j, sectionOpen X (s j)) = ⊤) :
    ∃ c : Fin k → ℂ, Mono (sectionLinearCombination L a s c) := by
  classical
  obtain ⟨l, U, hU, ⟨e⟩⟩ := finite_affine_frame_cover L
  let R (i : Fin l) : Type := Γ((U i).1.toScheme, ⊤)
  have hAff (i : Fin l) : IsAffine (U i).1.toScheme := (U i).2
  let alg (i : Fin l) : Algebra ℂ (R i) := ((U i).1.ι.appTop.hom.comp a).toAlgebra
  let (i : Fin l) : Algebra ℂ (R i) := alg i
  have hNoeth (i : Fin l) : IsNoetherianRing (R i) :=
    IsLocallyNoetherian.component_noetherian ⟨⊤, isAffineOpen_top (U i).1.toScheme⟩
  let b (i : Fin l) (j : Fin k) : R i := coefficient (e i) (restrictSection (U i).1.ι (s j))
  have hb (i : Fin l) : Ideal.span (Set.range (b i)) = ⊤ :=
    coefficients_span_top_of_section_cover L s hs (U i) (e i)
  obtain ⟨c, hc⟩ := GeometrySupport.AssociatedPrimeAvoidance.exists_regular_combination (K := ℂ) (ι := Fin l) (J := Fin k) R b hb
  refine ⟨c, section_mono_of_regular_affine_frames L _ ?_⟩
  intro x
  obtain ⟨i, hi⟩ := Opens.mem_iSup.mp (show x ∈ ⨆ i, (U i).1 by rw [hU]; trivial)
  refine ⟨U i, hi, e i, ?_⟩
  rw [localCoefficient_linearCombination]
  simpa only [R, b, Algebra.smul_def, RingHom.algebraMap_toAlgebra, RingHom.comp_apply] using hc i

theorem exists_mono_section_of_finite_cover [IsNoetherian X]
    (p : X ⟶ Spec (CommRingCat.of ℂ)) (L : LineBundle X) {k : ℕ}
    (s : Fin k → GlobalSections X L.sheaf)
    (hs : (⨆ j, sectionOpen X (s j)) = ⊤) :
    ∃ t : GlobalSections X L.sheaf, Mono t := by
  obtain ⟨c, hc⟩ := exists_mono_linearCombination_of_finite_cover L (baseScalars p) s hs
  exact ⟨sectionLinearCombination L (baseScalars p) s c, hc⟩

end
end PiExponent.NumericalAmpleness

end OAI
end Source0623

-- Source: OAI/NumberTheory/PiExponent/Cohomology/CartierEulerDifference.lean
section Source0624
/-
Modification notice for the LogTwo project.
Derived from openai/math (Apache-2.0), revision adc7f1241b42e322a6451854ab7e4b4c146bf78a.
Original source: lean/OAI/NumberTheory/PiExponent/Cohomology/CartierEulerDifference.lean
Changes: Convert module/import declarations to the Lean 4.34 public module format.
See ../THIRD_PARTY_NOTICES.txt for provenance and the recorded changes.
-/

namespace OAI

namespace PiExponent.NumericalAmpleness

noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian
open PiExponentSeshadri.Geometry PiExponentSeshadri.Frames

variable {X : Scheme.{0}}

theorem eulerCharacteristic_eq_pred_of_cohomology_zero
    (p : X ⟶ Spec (CommRingCat.of ℂ)) (M : X.Modules) (d : ℕ)
    (hzero : ∀ z : cohomology M d, z = 0) :
    eulerCharacteristic p d M = eulerCharacteristic p (d-1) M := by
  have : Subsingleton (cohomology M d) :=
    ⟨fun a b => (hzero a).trans (hzero b).symm⟩
  have hdim : cohomologyDimension p M d = 0 := by
    let := Module.compHom (cohomology M d) (baseScalars p)
    exact Module.finrank_zero_of_subsingleton
  cases d with
  | zero => rfl
  | succ d =>
    simp only [Nat.add_sub_cancel, eulerCharacteristic, Finset.sum_range_succ,
      hdim, Nat.cast_zero, mul_zero, add_zero]

theorem cartier_euler_difference
    (p : X ⟶ Spec (CommRingCat.of ℂ))
    (M N : LineBundle X) (φ : M.sheaf ⟶ N.sheaf) [Mono φ]
    (I : X.IdealSheafData)
    (heq : ∀ x : X, ∃ U : X.affineOpens, x ∈ U.1 ∧
      ∃ e : M.sheaf.restrict U.1.ι ≅ O U.1.toScheme,
      ∃ e' : N.sheaf.restrict U.1.ι ≅ O U.1.toScheme,
        I.ideal U = Ideal.span {(U.1.topIso.hom
          (endValue (e.inv ≫ (Scheme.Modules.restrictFunctor U.1.ι).map φ ≫ e'.hom)))})
    (d : ℕ)
    (hfiniteM : ∀ q ≤ d, letI := Module.compHom (cohomology M.sheaf q) (baseScalars p)
      FiniteDimensional ℂ (cohomology M.sheaf q))
    (hfiniteN : ∀ q ≤ d, letI := Module.compHom (cohomology N.sheaf q) (baseScalars p)
      FiniteDimensional ℂ (cohomology N.sheaf q))
    (hfiniteRestricted : ∀ q ≤ d,
      letI := Module.compHom
        (cohomology ((Scheme.Modules.pullback I.subschemeι).obj N.sheaf) q)
        (baseScalars (I.subschemeι ≫ p))
      FiniteDimensional ℂ (cohomology ((Scheme.Modules.pullback I.subschemeι).obj N.sheaf) q))
    (hzeroM : ∀ z : cohomology M.sheaf (d+1), z = 0)
    (hzeroRestricted : ∀ z : cohomology ((Scheme.Modules.pullback I.subschemeι).obj N.sheaf) d,
      z = 0) :
    eulerCharacteristic p d N.sheaf - eulerCharacteristic p d M.sheaf =
      eulerCharacteristic (I.subschemeι ≫ p) (d-1)
        ((Scheme.Modules.pullback I.subschemeι).obj N.sheaf) := by
  obtain ⟨hz,hS⟩ := PiExponentSeshadri.CartierSequence.exact p M N φ I heq
  have : Subsingleton (cohomology M.sheaf (d+1)) :=
    ⟨fun a b => (hzeroM a).trans (hzeroM b).symm⟩
  have hfinitePushforward (q : ℕ) (hq : q ≤ d) :
      letI := Module.compHom
        (cohomology ((Scheme.Modules.pushforward I.subschemeι).obj
          ((Scheme.Modules.pullback I.subschemeι).obj N.sheaf)) q) (baseScalars p)
      FiniteDimensional ℂ
        (cohomology ((Scheme.Modules.pushforward I.subschemeι).obj
          ((Scheme.Modules.pullback I.subschemeι).obj N.sheaf)) q) := by
    let := Module.compHom
      (cohomology ((Scheme.Modules.pullback I.subschemeι).obj N.sheaf) q)
      (baseScalars (I.subschemeι ≫ p))
    let := Module.compHom
      (cohomology ((Scheme.Modules.pushforward I.subschemeι).obj
        ((Scheme.Modules.pullback I.subschemeι).obj N.sheaf)) q) (baseScalars p)
    have := hfiniteRestricted q hq
    let e := ClosedImmersionSerreTransfer.cohomologyLinearEquiv I.subschemeι p
      ((Scheme.Modules.pullback I.subschemeι).obj N.sheaf) q
    exact FiniteDimensional.of_surjective e.toLinearMap e.surjective
  have hEuler := eulerCharacteristic_add p hS d hfiniteM hfiniteN hfinitePushforward
  change eulerCharacteristic p d N.sheaf = eulerCharacteristic p d M.sheaf +
    eulerCharacteristic p d ((Scheme.Modules.pushforward I.subschemeι).obj
      ((Scheme.Modules.pullback I.subschemeι).obj N.sheaf)) at hEuler
  rw [ClosedImmersionSerreTransfer.euler_pushforward,
    eulerCharacteristic_eq_pred_of_cohomology_zero (I.subschemeι ≫ p)
      ((Scheme.Modules.pullback I.subschemeι).obj N.sheaf) d hzeroRestricted] at hEuler
  exact sub_eq_iff_eq_add.mpr (by simpa only [add_comm] using hEuler)

end
end PiExponent.NumericalAmpleness

end OAI
end Source0624

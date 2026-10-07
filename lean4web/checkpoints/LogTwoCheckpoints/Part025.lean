/- Generated rc4 checkpoint for LogTwo.
Modified from the reduced edition: new imports, separate module compilation,
and synchronous elaboration. Original source blocks and notices are retained.
See ../../../THIRD_PARTY_NOTICES.txt and ../../reduction.json.
-/
module
public import LogTwoCheckpoints.Part000
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
public import LogTwoCheckpoints.Part024
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.EpiMono
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Quasicoherent
public import Mathlib.Algebra.Group.ForwardDiff
public import Mathlib.Algebra.Homology.DerivedCategory.Ext.ExactSequences
public import Mathlib.AlgebraicGeometry.Artinian
public import Mathlib.AlgebraicGeometry.IdealSheaf.Functorial
public import Mathlib.AlgebraicGeometry.Modules.Sheaf
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Basic
public import Mathlib.Analysis.Complex.Polynomial.Basic
public import Mathlib.Data.Opposite
public import Mathlib.RingTheory.MvPolynomial.Ideal
@[expose] public section
set_option Elab.async false

-- Source: OAI/NumberTheory/PiExponent/Geometry/SectionCartierPower.lean
section Source0625
-- Modified in this edition: unused plain lemmas removed; see reduction.json.
/-
Modification notice for the LogTwo project.
Derived from openai/math (Apache-2.0), revision adc7f1241b42e322a6451854ab7e4b4c146bf78a.
Original source: lean/OAI/NumberTheory/PiExponent/Geometry/SectionCartierPower.lean
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

theorem cartierPower_zeroIdeal_frames (L : LineBundle X) (s : GlobalSections X L.sheaf)
    (n : ℕ) : ∀ x : X, ∃ U : X.affineOpens, x ∈ U.1 ∧
      ∃ e : (L.pow n).sheaf.restrict U.1.ι ≅ O U.1.toScheme,
      ∃ e' : (L.pow (n+1)).sheaf.restrict U.1.ι ≅ O U.1.toScheme,
        (zeroIdeal L s).ideal U = Ideal.span {(U.1.topIso.hom
          (endValue (e.inv ≫ (Scheme.Modules.restrictFunctor U.1.ι).map
            (cartierPowerMultiply L s n) ≫ e'.hom)))} := by
  intro x
  obtain ⟨V,hxV,⟨eV⟩⟩ := L.locallyRankOne x
  obtain ⟨U,hU,hxU,hUV⟩ := exists_isAffineOpen_mem_and_subset hxV
  let e := restrictOpenFrame hUV eV
  refine ⟨⟨U,hU⟩,hxU,modulePowFrame U e n,modulePowFrame U e (n+1),?_⟩
  exact (zeroIdeal_on_frame L s ⟨U, hU⟩ e).trans
    (cartierPowerMultiply_ideal L s n ⟨U, hU⟩ e).symm

theorem cartierPower_restriction_shortExact [IsIntegral X]
    (p : X ⟶ Spec (CommRingCat.of ℂ)) (L : LineBundle X)
    (s : GlobalSections X L.sheaf) (hs : s ≠ 0) (n : ℕ) :
    ∃ hz : cartierPowerMultiply L s n ≫
        PiExponentSeshadri.LineClosedUnit.map (zeroIdeal L s).subschemeι (L.pow (n+1)) = 0,
      (ShortComplex.mk (cartierPowerMultiply L s n)
        (PiExponentSeshadri.LineClosedUnit.map (zeroIdeal L s).subschemeι (L.pow (n+1))) hz).ShortExact := by
  exact @PiExponentSeshadri.CartierSequence.exact X p (L.pow n) (L.pow (n+1))
    (cartierPowerMultiply L s n) (cartierPowerMultiply_mono L s hs n)
    (zeroIdeal L s) (cartierPower_zeroIdeal_frames L s n)

def cartierPowerQuotientIso [IsIntegral X]
    (p : X ⟶ Spec (CommRingCat.of ℂ)) (L : LineBundle X)
    (s : GlobalSections X L.sheaf) (hs : s ≠ 0) (n : ℕ) :
    cartierPowerQuotient L s n ≅
      (Scheme.Modules.pushforward (zeroIdeal L s).subschemeι).obj
        ((Scheme.Modules.pullback (zeroIdeal L s).subschemeι).obj (L.pow (n+1)).sheaf) := by
  let h := cartierPower_restriction_shortExact p L s hs n
  let hz := h.choose
  have hS := h.choose_spec
  letI := hS.epi_g
  exact (colimit.isColimit _).coconePointUniqueUpToIso hS.exact.gIsCokernel

end
end PiExponent.NumericalAmpleness

end OAI
end Source0625

-- Source: OAI/NumberTheory/PiExponent/Geometry/SectionCartierRegular.lean
section Source0626
-- Modified in this edition: unused plain lemmas removed; see reduction.json.
/-
Modification notice for the LogTwo project.
Derived from openai/math (Apache-2.0), revision adc7f1241b42e322a6451854ab7e4b4c146bf78a.
Original source: lean/OAI/NumberTheory/PiExponent/Geometry/SectionCartierRegular.lean
Changes: Convert module/import declarations to the Lean 4.34 public module format.
See ../THIRD_PARTY_NOTICES.txt for provenance and the recorded changes.
-/

namespace OAI

namespace PiExponent.NumericalAmpleness
noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open PiExponentSeshadri.Geometry
open PiExponent.SectionZeroIdeal
variable {X : Scheme.{0}}

private lemma sectionCartier_mono_iso_inv_comp {C : Type*} [Category C] {A B D : C}
    (e : A ≅ B) (f : A ⟶ D) [Mono f] : Mono (e.inv ≫ f) := inferInstance

theorem cartierPowerMultiply_mono_of_mono (L : LineBundle X)
    (s : GlobalSections X L.sheaf) [Mono s] (n : ℕ) :
    Mono (cartierPowerMultiply L s n) := by
  have hm : Mono (moduleTensorMap s (𝟙 (modulePow X L.sheaf n))) :=
    moduleTensorMap_mono s (L.pow n)
  exact @sectionCartier_mono_iso_inv_comp X.Modules _ _ _ _
    (moduleTensorUnit (modulePow X L.sheaf n)) _ hm

theorem regular_cartierPower_restriction_shortExact
    (p : X ⟶ Spec (CommRingCat.of ℂ)) (L : LineBundle X)
    (s : GlobalSections X L.sheaf) [Mono s] (n : ℕ) :
    ∃ hz : cartierPowerMultiply L s n ≫
        PiExponentSeshadri.LineClosedUnit.map (zeroIdeal L s).subschemeι (L.pow (n+1)) = 0,
      (ShortComplex.mk (cartierPowerMultiply L s n)
        (PiExponentSeshadri.LineClosedUnit.map (zeroIdeal L s).subschemeι (L.pow (n+1))) hz).ShortExact := by
  exact @PiExponentSeshadri.CartierSequence.exact X p (L.pow n) (L.pow (n+1))
    (cartierPowerMultiply L s n) (cartierPowerMultiply_mono_of_mono L s n)
    (zeroIdeal L s) (cartierPower_zeroIdeal_frames L s n)

def regular_cartierPowerQuotientIso
    (p : X ⟶ Spec (CommRingCat.of ℂ)) (L : LineBundle X)
    (s : GlobalSections X L.sheaf) [Mono s] (n : ℕ) :
    cartierPowerQuotient L s n ≅
      (Scheme.Modules.pushforward (zeroIdeal L s).subschemeι).obj
        ((Scheme.Modules.pullback (zeroIdeal L s).subschemeι).obj (L.pow (n+1)).sheaf) := by
  let h := regular_cartierPower_restriction_shortExact p L s n
  let hz := h.choose
  have hS := h.choose_spec
  letI := hS.epi_g
  exact (colimit.isColimit _).coconePointUniqueUpToIso hS.exact.gIsCokernel

end
end PiExponent.NumericalAmpleness

end OAI
end Source0626

-- Source: OAI/NumberTheory/PiExponent/Cohomology/CartierMixedEuler.lean
section Source0627
-- Modified in this edition: unused plain lemmas removed; see reduction.json.
/-
Modification notice for the LogTwo project.
Derived from openai/math (Apache-2.0), revision adc7f1241b42e322a6451854ab7e4b4c146bf78a.
Original source: lean/OAI/NumberTheory/PiExponent/Cohomology/CartierMixedEuler.lean
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

private lemma framed_map {C : Type*} [Category C] {A B P Q T O : C}
    (r : A ≅ P) (r' : B ≅ Q) (e : P ≅ T) (e' : Q ≅ T) (u : T ≅ O)
    (m : A ⟶ B) (p : P ⟶ Q) (b : T ⟶ T) (a : O ⟶ O)
    (hn : m ≫ r'.hom = r.hom ≫ p) (ht : p ≫ e'.hom = e.hom ≫ b)
    (hs : b ≫ u.hom = u.hom ≫ a) :
    (r ≪≫ e ≪≫ u).inv ≫ m ≫ (r' ≪≫ e' ≪≫ u).hom = a := by
  simp only [Iso.trans_hom, Iso.trans_inv, Category.assoc]
  rw [← Category.assoc m r'.hom, hn]
  simp only [Category.assoc]
  rw [← Category.assoc p e'.hom, ht]
  simp only [Category.assoc]
  rw [hs]
  simp

lemma tensorMap_framed (A B M : X.Modules) (φ : A ⟶ B) (U : X.Opens)
    (e : A.restrict U.ι ≅ O U.toScheme)
    (e' : B.restrict U.ι ≅ O U.toScheme)
    (f : M.restrict U.ι ≅ O U.toScheme) :
    (tensorFrame A M U e f).inv ≫
      (Scheme.Modules.restrictFunctor U.ι).map (moduleTensorMap φ (𝟙 M)) ≫
        (tensorFrame B M U e' f).hom =
      e.inv ≫ (Scheme.Modules.restrictFunctor U.ι).map φ ≫ e'.hom := by
  let F := Scheme.Modules.restrictFunctor U.ι
  let R := moduleTensorRestrict U A M
  let R' := moduleTensorRestrict U B M
  let E := moduleTensorIso e f
  let E' := moduleTensorIso e' f
  let T := moduleTensorUnit (O U.toScheme)
  let c := e.inv ≫ F.map φ ≫ e'.hom
  let p := moduleTensorMap (F.map φ) (𝟙 (M.restrict U.ι))
  have he : F.map φ ≫ e'.hom = e.hom ≫ c := by
    simp [c]
  have hn : F.map (moduleTensorMap φ (𝟙 M)) ≫ R'.hom = R.hom ≫ p :=
    (moduleTensorRestrict_natural U φ (𝟙 M)).trans
      (congrArg (fun q => R.hom ≫ moduleTensorMap (F.map φ) q) (F.map_id M))
  have h₁ := (moduleTensorMap_comp (F.map φ) e'.hom (𝟙 (M.restrict U.ι)) f.hom).symm.trans
    (congrArg (moduleTensorMap (F.map φ ≫ e'.hom)) (Category.id_comp f.hom))
  have h₂ := (moduleTensorMap_comp e.hom c f.hom (𝟙 (O U.toScheme))).symm.trans
    (congrArg (moduleTensorMap (e.hom ≫ c)) (Category.comp_id f.hom))
  have ht : p ≫ E'.hom = E.hom ≫ moduleTensorMap c (𝟙 (O U.toScheme)) :=
    h₁.trans ((congrArg (fun q : F.obj A ⟶ O U.toScheme => moduleTensorMap q f.hom)
      he).trans h₂.symm)
  have hs : moduleTensorMap c (𝟙 (O U.toScheme)) ≫ T.hom = T.hom ≫ c :=
    (moduleTensorUnit_scalar (X := U.toScheme) c (𝟙 (O U.toScheme))).trans
      (congrArg (fun q => T.hom ≫ q) (Category.comp_id c))
  simpa only [OAI.PiExponent.CartierPowerFrames.tensorFrame] using!
    framed_map R R' E E' T (F.map (moduleTensorMap φ (𝟙 M))) p _ c hn ht hs

def mixedCartierPowerMultiply (L M : LineBundle X)
    (s : GlobalSections X L.sheaf) (n : ℕ) :
    ((L.pow n).tensor M).sheaf ⟶ ((L.pow (n+1)).tensor M).sheaf :=
  moduleTensorMap (cartierPowerMultiply L s n) (𝟙 M.sheaf)

theorem mixedCartierPowerMultiply_mono (L M : LineBundle X)
    (s : GlobalSections X L.sheaf) [Mono s] (n : ℕ) :
    Mono (mixedCartierPowerMultiply L M s n) := by
  let := cartierPowerMultiply_mono_of_mono L s n
  exact moduleTensorMap_mono (cartierPowerMultiply L s n) M

theorem mixedCartierPower_zeroIdeal_frames (L M : LineBundle X)
    (s : GlobalSections X L.sheaf) (n : ℕ) :
    ∀ x : X, ∃ U : X.affineOpens, x ∈ U.1 ∧
      ∃ e : ((L.pow n).tensor M).sheaf.restrict U.1.ι ≅ O U.1.toScheme,
      ∃ e' : ((L.pow (n+1)).tensor M).sheaf.restrict U.1.ι ≅ O U.1.toScheme,
        (zeroIdeal L s).ideal U = Ideal.span {(U.1.topIso.hom
          (endValue (e.inv ≫ (Scheme.Modules.restrictFunctor U.1.ι).map
            (mixedCartierPowerMultiply L M s n) ≫ e'.hom)))} := by
  intro x
  obtain ⟨U, hx, ⟨e⟩, ⟨f⟩⟩ := common_affine_frames L M x
  refine ⟨U, hx,
    tensorFrame (L.pow n).sheaf M.sheaf U.1 (modulePowFrame U.1 e n) f,
    tensorFrame (L.pow (n+1)).sheaf M.sheaf U.1 (modulePowFrame U.1 e (n+1)) f, ?_⟩
  simp only [mixedCartierPowerMultiply]
  have hframe := tensorMap_framed (L.pow n).sheaf (L.pow (n+1)).sheaf M.sheaf
    (cartierPowerMultiply L s n) U.1 (modulePowFrame U.1 e n)
    (modulePowFrame U.1 e (n+1)) f
  exact ((zeroIdeal_on_frame L s U e).trans (cartierPowerMultiply_ideal L s n U e).symm).trans
    (congrArg (fun g : O U.1.toScheme ⟶ O U.1.toScheme =>
      Ideal.span {U.1.topIso.hom (endValue g)}) hframe.symm)

theorem regular_mixedCartierPower_restriction_shortExact
    (p : X ⟶ Spec (CommRingCat.of ℂ)) (L M : LineBundle X)
    (s : GlobalSections X L.sheaf) [Mono s] (n : ℕ) :
    ∃ hz : mixedCartierPowerMultiply L M s n ≫
        PiExponentSeshadri.LineClosedUnit.map (zeroIdeal L s).subschemeι ((L.pow (n+1)).tensor M) = 0,
      (ShortComplex.mk (mixedCartierPowerMultiply L M s n)
        (PiExponentSeshadri.LineClosedUnit.map (zeroIdeal L s).subschemeι
          ((L.pow (n+1)).tensor M)) hz).ShortExact := by
  let := mixedCartierPowerMultiply_mono L M s n
  exact PiExponentSeshadri.CartierSequence.exact p ((L.pow n).tensor M) ((L.pow (n+1)).tensor M)
    (mixedCartierPowerMultiply L M s n) (zeroIdeal L s)
    (mixedCartierPower_zeroIdeal_frames L M s n)

theorem regular_mixedCartierPower_euler_difference
    (p : X ⟶ Spec (CommRingCat.of ℂ)) (L M : LineBundle X)
    (s : GlobalSections X L.sheaf) [Mono s] (n d : ℕ)
    (hfiniteSource : ∀ q ≤ d,
      letI := Module.compHom (cohomology ((L.pow n).tensor M).sheaf q) (baseScalars p)
      FiniteDimensional ℂ (cohomology ((L.pow n).tensor M).sheaf q))
    (hfiniteTarget : ∀ q ≤ d,
      letI := Module.compHom (cohomology ((L.pow (n+1)).tensor M).sheaf q) (baseScalars p)
      FiniteDimensional ℂ (cohomology ((L.pow (n+1)).tensor M).sheaf q))
    (hfiniteRestricted : ∀ q ≤ d,
      letI := Module.compHom
        (cohomology ((Scheme.Modules.pullback (zeroIdeal L s).subschemeι).obj
          ((L.pow (n+1)).tensor M).sheaf) q)
        (baseScalars ((zeroIdeal L s).subschemeι ≫ p))
      FiniteDimensional ℂ
        (cohomology ((Scheme.Modules.pullback (zeroIdeal L s).subschemeι).obj
          ((L.pow (n+1)).tensor M).sheaf) q))
    (hzeroSource : ∀ z : cohomology ((L.pow n).tensor M).sheaf (d+1), z = 0)
    (hzeroRestricted : ∀ z :
      cohomology ((Scheme.Modules.pullback (zeroIdeal L s).subschemeι).obj
        ((L.pow (n+1)).tensor M).sheaf) d, z = 0) :
    eulerCharacteristic p d ((L.pow (n+1)).tensor M).sheaf -
        eulerCharacteristic p d ((L.pow n).tensor M).sheaf =
      eulerCharacteristic ((zeroIdeal L s).subschemeι ≫ p) (d-1)
        ((Scheme.Modules.pullback (zeroIdeal L s).subschemeι).obj
          ((L.pow (n+1)).tensor M).sheaf) := by
  let := mixedCartierPowerMultiply_mono L M s n
  exact cartier_euler_difference p ((L.pow n).tensor M) ((L.pow (n+1)).tensor M)
    (mixedCartierPowerMultiply L M s n) (zeroIdeal L s)
    (mixedCartierPower_zeroIdeal_frames L M s n) d hfiniteSource hfiniteTarget
    hfiniteRestricted hzeroSource hzeroRestricted

end
end PiExponent.NumericalAmpleness

end OAI
end Source0627

-- Source: OAI/NumberTheory/PiExponent/Cohomology/EulerZeroDimensional.lean
section Source0628
-- Modified in this edition: unused plain lemmas removed; see reduction.json.
/-
Modification notice for the LogTwo project.
Derived from openai/math (Apache-2.0), revision adc7f1241b42e322a6451854ab7e4b4c146bf78a.
Original source: lean/OAI/NumberTheory/PiExponent/Cohomology/EulerZeroDimensional.lean
Changes: Convert module/import declarations to the Lean 4.34 public module format.
See ../THIRD_PARTY_NOTICES.txt for provenance and the recorded changes.
-/

namespace OAI

namespace PiExponent.NumericalAmpleness
noncomputable section
open AlgebraicGeometry CategoryTheory TopologicalSpace
open PiExponentSeshadri.Geometry
variable {X : Scheme.{0}}

theorem discreteTopology_of_dim_le_zero [IsLocallyNoetherian X]
    (hdim : topologicalKrullDim X ≤ 0) : DiscreteTopology X := by
  let : IsLocallyArtinian X := IsLocallyArtinian.of_topologicalKrullDim_le_zero hdim
  infer_instance

theorem finite_of_dim_le_zero [IsNoetherian X]
    (hdim : topologicalKrullDim X ≤ 0) : Finite X := by
  let : DiscreteTopology X := discreteTopology_of_dim_le_zero hdim
  exact finite_of_compact_of_discrete

theorem lineBundle_trivial_of_dim_le_zero [IsLocallyNoetherian X]
    (hdim : topologicalKrullDim X ≤ 0) (L : LineBundle X) :
    Nonempty (L.sheaf ≅ structureSheaf X) := by
  let : DiscreteTopology X := discreteTopology_of_dim_le_zero hdim
  exact PiExponentSeshadri.FiniteSupport.lineBundle_trivial L

end
end PiExponent.NumericalAmpleness

end OAI
end Source0628

-- Source: OAI/NumberTheory/PiExponent/Approximation/SerrePowerDescent.lean
section Source0629
/-
Modification notice for the LogTwo project.
Derived from openai/math (Apache-2.0), revision adc7f1241b42e322a6451854ab7e4b4c146bf78a.
Original source: lean/OAI/NumberTheory/PiExponent/Approximation/SerrePowerDescent.lean
Changes: Convert module/import declarations to the Lean 4.34 public module format.
See ../THIRD_PARTY_NOTICES.txt for provenance and the recorded changes.
-/

namespace OAI

namespace PiExponent.GeometrySupport.SerrePowerDescent
noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Abelian
open PiExponentSeshadri.Geometry

variable {X : Scheme.{0}}

theorem ext_zero_of_iso {M N : X.Modules} (e : M ≅ N) (q : ℕ)
    (h : ∀ x : Ext.{1} (structureSheaf X) M q, x = 0) :
    ∀ x : Ext.{1} (structureSheaf X) N q, x = 0 := by
  let E := (extFunctorObj (structureSheaf X) q).mapIso e
  intro x
  obtain ⟨y, rfl⟩ := (ConcreteCategory.bijective_of_isIso E.hom).surjective x
  exact (congrArg E.hom (h y)).trans E.hom.hom.map_zero

def moduleTwistLineIso {L N : LineBundle X} (e : L.sheaf ≅ N.sheaf) (M : X.Modules) :
    ∀ n : ℕ, (moduleTwistFunctor L n).obj M ≅ (moduleTwistFunctor N n).obj M
  | 0 => Iso.refl M
  | n + 1 => moduleTensorIso (moduleTwistLineIso e M n) e

theorem eventual_twist_ext_zero_of_lineIso {L N : LineBundle X}
    (e : L.sheaf ≅ N.sheaf) (M : X.Modules)
    (hN : ∃ B, ∀ n, B ≤ n → ∀ q, 0 < q →
      ∀ x : Ext.{1} (structureSheaf X) ((moduleTwistFunctor N n).obj M) q, x = 0) :
    ∃ B, ∀ n, B ≤ n → ∀ q, 0 < q →
      ∀ x : Ext.{1} (structureSheaf X) ((moduleTwistFunctor L n).obj M) q, x = 0 := by
  obtain ⟨B, hB⟩ := hN
  refine ⟨B, fun n hn q hq => ?_⟩
  exact ext_zero_of_iso (moduleTwistLineIso e M n).symm q (hB n hn q hq)

def residueTwistIso (L : LineBundle X) (M : X.Modules) (d n r : ℕ) :
    (moduleTwistFunctor (L.pow d) n).obj ((moduleTwistFunctor L r).obj M) ≅
      (moduleTwistFunctor L (d * n + r)).obj M :=
  moduleTwistPowerMulIso L ((moduleTwistFunctor L r).obj M) d n ≪≫
    eqToIso (by
      rw [Nat.add_comm (d * n) r, moduleTwistFunctor_add]
      rfl)

theorem eventual_twist_ext_zero_of_power (L : LineBundle X) (d : ℕ) (hd : 0 < d)
    (hpower : ∀ (A : X.Modules) [A.IsFinitePresentation],
      ∃ N, ∀ n, N ≤ n → ∀ q, 0 < q →
        ∀ x : Ext.{1} (structureSheaf X) ((moduleTwistFunctor (L.pow d) n).obj A) q,
          x = 0)
    (M : X.Modules) [M.IsFinitePresentation] :
    ∃ N, ∀ n, N ≤ n → ∀ q, 0 < q →
      ∀ x : Ext.{1} (structureSheaf X) ((moduleTwistFunctor L n).obj M) q,
        x = 0 := by
  classical
  have hresidue (r : Fin d) : ∃ N, ∀ n, N ≤ n → ∀ q, 0 < q →
      ∀ x : Ext.{1} (structureSheaf X)
        ((moduleTwistFunctor (L.pow d) n).obj ((moduleTwistFunctor L r.val).obj M)) q,
        x = 0 := by
    let : ((moduleTwistFunctor L r.val).obj M).IsFinitePresentation :=
      FiniteGlobalPresentation.moduleTwist_isFinitePresentation L r.val M
    exact hpower ((moduleTwistFunctor L r.val).obj M)
  choose N hN using hresidue
  let B : ℕ := Finset.univ.sup N
  refine ⟨d * B, ?_⟩
  intro n hn q hq
  let r : Fin d := ⟨n % d, Nat.mod_lt n hd⟩
  have hNB : N r ≤ B := Finset.le_sup (Finset.mem_univ r)
  have hBn : B ≤ n / d := (Nat.le_div_iff_mul_le hd).mpr (by
    simpa only [Nat.mul_comm] using hn)
  have he : d * (n / d) + r.val = n := Nat.div_add_mod n d
  let e := residueTwistIso L M d (n / d) r.val ≪≫
    eqToIso (congrArg (fun a => (moduleTwistFunctor L a).obj M) he)
  exact ext_zero_of_iso e q (hN r (n / d) (hNB.trans hBn) q hq)

end
end PiExponent.GeometrySupport.SerrePowerDescent

end OAI
end Source0629

-- Source: OAI/NumberTheory/PiExponent/Approximation/CoordinateFrameIdentification.lean
section Source0630
/-
Modification notice for the LogTwo project.
Derived from openai/math (Apache-2.0), revision adc7f1241b42e322a6451854ab7e4b4c146bf78a.
Original source: lean/OAI/NumberTheory/PiExponent/Approximation/CoordinateFrameIdentification.lean
Changes: Convert module/import declarations to the Lean 4.34 public module format.
See ../THIRD_PARTY_NOTICES.txt for provenance and the recorded changes.
-/

namespace OAI

namespace PiExponentSeshadri.LineBundleFrameCocycle
noncomputable section
open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite
open PiExponentSeshadri.Geometry PiExponentSeshadri.Frames
variable {X : Scheme} {ι : Type} {U : ι → X.Opens}

lemma cocycle_ext {c d : LineBundleGluing.Cocycle U}
    (h : c.transition = d.transition) : c = d := by
  cases c
  cases d
  cases h
  rfl

def isoOfCoordinateCoefficients (M N : X.Modules)
    (e : ∀ i, M.restrict (U i).ι ≅ O (U i).toScheme)
    (f : ∀ i, N.restrict (U i).ι ≅ O (U i).toScheme)
    (s : ι → (O X ⟶ M)) (t : ι → (O X ⟶ N))
    (hnorm : ∀ i, coefficient (e i) (restrictSection (U i).ι (s i)) = 1)
    (hcoeff : ∀ i j, coefficient (f i) (restrictSection (U i).ι (t j)) =
      coefficient (e i) (restrictSection (U i).ι (s j)))
    (hcover : ⊤ ≤ ⨆ i, U i) : M ≅ N := by
  have hnorm' (i : ι) : coefficient (f i) (restrictSection (U i).ι (t i)) = 1 :=
    (hcoeff i i).trans (hnorm i)
  have hc : ofFrames M U e = ofFrames N U f := by
    apply cocycle_ext
    funext i j W hi hj
    apply Units.ext
    change W.topIso.hom
      (frameChange (restrictOpenFrame hj (e j)) (restrictOpenFrame hi (e i)) : Γ(W.toScheme,⊤)) =
      W.topIso.hom
        (frameChange (restrictOpenFrame hj (f j)) (restrictOpenFrame hi (f i)) : Γ(W.toScheme,⊤))
    rw [frameChange_restrictOpenFrame hj hi (e j) (e i) (s j) (hnorm j),
      frameChange_restrictOpenFrame hj hi (f j) (f i) (t j) (hnorm' j), hcoeff i j]
  exact isoSheaf M U e hcover ≪≫ eqToIso (congrArg LineBundleGluing.sheaf hc) ≪≫
    (isoSheaf N U f hcover).symm

end
end PiExponentSeshadri.LineBundleFrameCocycle

end OAI
end Source0630

-- Source: OAI/NumberTheory/PiExponent/Geometry/ProjectiveCoordinateChartMap.lean
section Source0631
/-
Modification notice for the LogTwo project.
Derived from openai/math (Apache-2.0), revision adc7f1241b42e322a6451854ab7e4b4c146bf78a.
Original source: lean/OAI/NumberTheory/PiExponent/Geometry/ProjectiveCoordinateChartMap.lean
Changes: Convert module/import declarations to the Lean 4.34 public module format.
See ../THIRD_PARTY_NOTICES.txt for provenance and the recorded changes.
-/

namespace OAI

namespace PiExponentSeshadri.Projective
noncomputable section
open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite
open PiExponentSeshadri.Frames PiExponentSeshadri.Geometry
attribute [local instance] MvPolynomial.gradedAlgebra
variable {X : Scheme} {K σ : Type} [CommRing K]
variable {M : X.Modules} (k : K →+* Γ(X,⊤)) (s : σ → (O X ⟶ M))
variable (hc : (⨆i,SectionOpens.isoOpen (s i))=⊤)

def coordinateChartMap (i : σ) : (SectionOpens.isoOpen (s i)).toScheme ⟶
    (PiExponent.ProjectiveO1.coordinateOpen (R := K) i).toScheme :=
  (X.isoOfEq (sectionsMorphism_preimage k s hc i).symm).hom ≫
    (sectionsMorphism k s hc ∣_ PiExponent.ProjectiveO1.coordinateOpen i)

lemma coordinateChartMap_factor (i : σ) :
    coordinateChartMap k s hc i ≫ (PiExponent.ProjectiveO1.coordinateOpen (R := K) i).ι =
      (SectionOpens.isoOpen (s i)).ι ≫ sectionsMorphism k s hc := by
  simp only [coordinateChartMap, Category.assoc, morphismRestrict_ι,
    Scheme.isoOfEq_hom_ι_assoc]

lemma coordinateChartMap_ratio (i j : σ) :
    (coordinateChartMap k s hc i).appTop
      (PiExponent.ProjectiveO1.chartRatios (R := K) i j) =
    coefficient (sectionFrame (s i))
      (restrictSection (SectionOpens.isoOpen (s i)).ι (s j)) := by
  let g := coordinateChartMap k s hc i
  let a := Proj.basicOpenIsoSpec (PolyGrade K σ) (MvPolynomial.X i) (poly_X_mem i) (by decide)
  have hg : (SectionOpens.isoOpen (s i)).ι ≫ sectionsMorphism k s hc =
      (g ≫ a.hom) ≫ Proj.awayι (PolyGrade K σ) (MvPolynomial.X i) (poly_X_mem i) (by decide) := by
    simpa only [Proj.awayι, a, Category.assoc, Iso.hom_inv_id_assoc] using
      (coordinateChartMap_factor k s hc i).symm
  have h := sectionFrame_coordinate i k s hc (g ≫ a.hom) hg j
  rw [Scheme.Hom.comp_appTop, ← Category.assoc,
    PiExponent.ProjectiveO1.coordinateOpen_pullback] at h
  change _ = g.appTop ((PiExponent.ProjectiveO1.coordinateOpen (R := K) i).topIso.inv
    (Proj.awayToSection (PolyGrade K σ) (MvPolynomial.X i) (chartCoordinate (R := K) i j))) at h
  rw [PiExponent.ProjectiveO1.awayToSection_coordinate] at h
  exact h.symm

end
end PiExponentSeshadri.Projective

end OAI
end Source0631

-- Source: OAI/NumberTheory/PiExponent/Geometry/ProjectiveCoordinatePullback.lean
section Source0632
/-
Modification notice for the LogTwo project.
Derived from openai/math (Apache-2.0), revision adc7f1241b42e322a6451854ab7e4b4c146bf78a.
Original source: lean/OAI/NumberTheory/PiExponent/Geometry/ProjectiveCoordinatePullback.lean
Changes: Convert module/import declarations to the Lean 4.34 public module format.
See ../THIRD_PARTY_NOTICES.txt for provenance and the recorded changes.
-/

namespace OAI

namespace PiExponentSeshadri.Projective
noncomputable section
open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite
open PiExponentSeshadri.Frames PiExponentSeshadri.Geometry
attribute [local instance] MvPolynomial.gradedAlgebra
variable {X : Scheme} {K σ : Type} [CommRing K]
variable {M : X.Modules} (k : K →+* Γ(X,⊤)) (s : σ → (O X ⟶ M))
variable (hc : (⨆i,SectionOpens.isoOpen (s i))=⊤)

def coordinatePullbackModule : X.Modules :=
  (Scheme.Modules.pullback (sectionsMorphism k s hc)).obj
    (PiExponent.ProjectiveO1.lineBundle (R := K) (σ := σ)).sheaf

def coordinatePullbackSection (i : σ) : O X ⟶ coordinatePullbackModule k s hc :=
  pullbackSection (sectionsMorphism k s hc) (PiExponent.ProjectiveO1.coordinateSection i)

def coordinatePullbackFrame (i : σ) :
    (coordinatePullbackModule k s hc).restrict (SectionOpens.isoOpen (s i)).ι ≅
      O (SectionOpens.isoOpen (s i)).toScheme :=
  restrictedPullbackFrame (sectionsMorphism k s hc)
    (PiExponent.ProjectiveO1.coordinateOpen i) (SectionOpens.isoOpen (s i))
    (coordinateChartMap k s hc i) (coordinateChartMap_factor k s hc i).symm
    (LineBundleGluing.openFrame PiExponent.ProjectiveO1.coordinateCocycle i
      (PiExponent.ProjectiveO1.coordinateOpen i) le_rfl)

lemma coordinatePullbackFrame_coefficient (i j : σ) :
    coefficient (coordinatePullbackFrame k s hc i)
      (restrictSection (SectionOpens.isoOpen (s i)).ι (coordinatePullbackSection k s hc j)) =
    coefficient (sectionFrame (s i))
      (restrictSection (SectionOpens.isoOpen (s i)).ι (s j)) := by
  have h := restrictedPullbackFrame_coefficient (sectionsMorphism k s hc)
    (PiExponent.ProjectiveO1.coordinateOpen i) (SectionOpens.isoOpen (s i))
    (coordinateChartMap k s hc i) (coordinateChartMap_factor k s hc i).symm
    (LineBundleGluing.openFrame PiExponent.ProjectiveO1.coordinateCocycle i
      (PiExponent.ProjectiveO1.coordinateOpen i) le_rfl)
    (PiExponent.ProjectiveO1.coordinateSection j)
  change coefficient (coordinatePullbackFrame k s hc i)
      (restrictSection (SectionOpens.isoOpen (s i)).ι (coordinatePullbackSection k s hc j)) = _ at h
  rw [PiExponent.ProjectiveO1.coordinateSection_coefficient_eq] at h
  exact h.trans (coordinateChartMap_ratio k s hc i j)

attribute [local irreducible] coordinatePullbackModule coordinatePullbackFrame coordinatePullbackSection

def coordinatePullbackIso : M ≅ coordinatePullbackModule k s hc :=
  LineBundleFrameCocycle.isoOfCoordinateCoefficients M (coordinatePullbackModule k s hc)
    (fun i => sectionFrame (s i)) (coordinatePullbackFrame k s hc)
    s (coordinatePullbackSection k s hc) (fun i => sectionFrame_normalized (s i))
    (coordinatePullbackFrame_coefficient k s hc) (by rw [hc])

def coordinateLineBundlePullbackIso (L : LineBundle X)
    (k : K →+* Γ(X,⊤)) (s : σ → (O X ⟶ L.sheaf))
    (hc : (⨆i,SectionOpens.isoOpen (s i))=⊤) :
    L.sheaf ≅ ((PiExponent.ProjectiveO1.lineBundle (R := K) (σ := σ)).pullback
      (sectionsMorphism k s hc)).sheaf := by
  simpa only [coordinatePullbackModule, LineBundle.pullback] using coordinatePullbackIso k s hc

end
end PiExponentSeshadri.Projective

end OAI
end Source0632

-- Source: OAI/NumberTheory/PiExponent/Geometry/ProjectiveSerreTransfer.lean
section Source0633
-- Modified in this edition: unused plain lemmas removed; see reduction.json.
/-
Modification notice for the LogTwo project.
Derived from openai/math (Apache-2.0), revision adc7f1241b42e322a6451854ab7e4b4c146bf78a.
Original source: lean/OAI/NumberTheory/PiExponent/Geometry/ProjectiveSerreTransfer.lean
Changes: Convert module/import declarations to the Lean 4.34 public module format.
See ../THIRD_PARTY_NOTICES.txt for provenance and the recorded changes.
-/

namespace OAI

namespace PiExponent.ClosedImmersionSerreTransfer
noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian
open PiExponentSeshadri.Geometry
variable {X Y : Scheme.{0}} (f : X ⟶ Y) [IsClosedImmersion f]
local instance : HasExt.{1} X.Modules := HasExt.standard _
local instance : HasExt.{1} Y.Modules := HasExt.standard _

theorem twist_ext_zero_iff (M : X.Modules) (L : LineBundle Y) (n q : ℕ) :
    (∀ x : Ext.{1} (structureSheaf X)
      ((moduleTwistFunctor (L.pullback f) n).obj M) q, x = 0) ↔
    (∀ x : Ext.{1} (structureSheaf Y)
      ((moduleTwistFunctor L n).obj ((Scheme.Modules.pushforward f).obj M)) q, x = 0) := by
  refine (ext_zero_iff f ((moduleTwistFunctor (L.pullback f) n).obj M) q).trans ?_
  let e := (extFunctorObj (structureSheaf Y) q).mapIso (ProjectionFormula.twistIso f M L n)
  constructor
  · intro h x
    obtain ⟨y, rfl⟩ := (ConcreteCategory.bijective_of_isIso e.hom).surjective x
    exact (congrArg e.hom (h y)).trans e.hom.hom.map_zero
  · intro h x
    apply (ConcreteCategory.bijective_of_isIso e.hom).injective
    exact (h _).trans e.hom.hom.map_zero.symm

theorem eventual_twist_ext_zero_of_ambient [IsLocallyNoetherian Y]
    (L : LineBundle Y)
    (hSerre : ∀ (N : Y.Modules) [N.IsFinitePresentation],
      ∃ N0, ∀ n, N0 ≤ n → ∀ q, 0 < q →
        ∀ x : Ext.{1} (structureSheaf Y) ((moduleTwistFunctor L n).obj N) q, x = 0)
    (M : X.Modules) [M.IsFinitePresentation] :
    ∃ N0, ∀ n, N0 ≤ n → ∀ q, 0 < q →
      ∀ x : Ext.{1} (structureSheaf X)
        ((moduleTwistFunctor (L.pullback f) n).obj M) q, x = 0 := by
  obtain ⟨N0, hN0⟩ := hSerre ((Scheme.Modules.pushforward f).obj M)
  refine ⟨N0, fun n hn q hq => ?_⟩
  exact (twist_ext_zero_iff f M L n q).mpr (hN0 n hn q hq)

end
end PiExponent.ClosedImmersionSerreTransfer

end OAI
end Source0633

-- Source: OAI/NumberTheory/PiExponent/Geometry/ProjectiveSpaceSerre.lean
section Source0634
/-
Modification notice for the LogTwo project.
Derived from openai/math (Apache-2.0), revision adc7f1241b42e322a6451854ab7e4b4c146bf78a.
Original source: lean/OAI/NumberTheory/PiExponent/Geometry/ProjectiveSpaceSerre.lean
Changes: Convert module/import declarations to the Lean 4.34 public module format.
Expose private helpers and adjust helper names where needed for module compatibility.
See ../THIRD_PARTY_NOTICES.txt for provenance and the recorded changes.
-/

namespace OAI

namespace PiExponent.ProjectiveO1
noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Abelian
open PiExponentSeshadri.Geometry

attribute [local irreducible] lineBundle coordinateSection scalars

abbrev schemeUnit (X : Scheme.{0}) : X.Modules := SheafOfModules.unit X.ringCatSheaf

attribute [local instance] PiExponentSeshadri.FiniteCoverCohomology.hasExtScheme'

variable (R σ : Type) [CommRing R] [IsNoetherianRing R] [Fintype σ]

theorem standardPower_ext_eq_zero (n q : ℕ) (hq : 0 < q)
    (x : Ext.{1} (C := (projectiveSpace R σ).Modules) (schemeUnit (projectiveSpace R σ))
      (modulePow (projectiveSpace R σ) (lineBundle (R := R) (σ := σ)).sheaf n) q) :
    x = 0 := by
  exact PiExponent.GeometrySupport.ProjectiveCoordinateAcyclicity.coordinatePower_ext_eq_zero
    (X := projectiveSpace R σ) (K := R) (σ := σ)
    (lineBundle (R := R) (σ := σ)).sheaf
    (coordinateSection (R := R) (σ := σ)) (scalars (R := R) (σ := σ))
    (coordinateSection_cover (R := R) (σ := σ)) (Iso.refl (projectiveSpace R σ))
    (coordinate_sectionsMorphism_identity (R := R) (σ := σ)) n q hq x

theorem serre_vanishing [Nonempty σ]
    (M : (projectiveSpace R σ).Modules) [M.IsFinitePresentation] :
    ∃ N, ∀ n, N ≤ n → ∀ q, 0 < q →
      ∀ x : Ext.{1} (C := (projectiveSpace R σ).Modules) (schemeUnit (projectiveSpace R σ))
        ((moduleTwistFunctor (lineBundle (R := R) (σ := σ)) n).obj M) q, x = 0 := by
  let e := Fintype.equivFin σ
  let s : Fin (Fintype.card σ) →
      (structureSheaf (projectiveSpace R σ) ⟶ (lineBundle (R := R) (σ := σ)).sheaf) :=
    fun i => coordinateSection (e.symm i)
  have hcover : (⨆ i, PiExponentSeshadri.SectionOpens.isoOpen (s i)) = ⊤ := by
    change (⨆ i, PiExponentSeshadri.SectionOpens.isoOpen
      (coordinateSection (R := R) (e.symm i))) = ⊤
    exact (Equiv.iSup_comp
      (g := fun j : σ => PiExponentSeshadri.SectionOpens.isoOpen (coordinateSection (R := R) j))
      e.symm).trans (coordinateSection_cover (R := R) (σ := σ))
  apply PiExponent.GeometrySupport.SerreAssembly.eventual_twist_ext_zero_of_section_cover
    (lineBundle (R := R) (σ := σ)) (Fintype.card σ) Fintype.card_pos s hcover
    (fun i => coordinateSection_isAffineOpen (e.symm i)) _ M
  intro n q hq x
  exact standardPower_ext_eq_zero R σ n q hq x

end
end PiExponent.ProjectiveO1

end OAI
end Source0634

-- Source: OAI/NumberTheory/PiExponent/Cohomology/NoetherianAmpleSerreVanishing.lean
section Source0635
/-
Modification notice for the LogTwo project.
Derived from openai/math (Apache-2.0), revision adc7f1241b42e322a6451854ab7e4b4c146bf78a.
Original source: lean/OAI/NumberTheory/PiExponent/Cohomology/NoetherianAmpleSerreVanishing.lean
Changes: Convert module/import declarations to the Lean 4.34 public module format.
See ../THIRD_PARTY_NOTICES.txt for provenance and the recorded changes.
-/

namespace OAI

namespace PiExponent.GeometrySupport.NoetherianAmpleSerreVanishing
noncomputable section
open AlgebraicGeometry CategoryTheory TopologicalSpace
open PiExponentSeshadri.Geometry PiExponentSeshadri.Projective
variable {X : Scheme.{0}} {R : Type} [CommRing R] [IsNoetherianRing R]

theorem ample_serre_vanishing
    (p : X ⟶ Spec (CommRingCat.of R)) [IsProper p]
    (L : LineBundle X) (hL : LineBundle.IsAmple X L)
    (M : X.Modules) [M.IsFinitePresentation] :
    ∃ N, ∀ n, N ≤ n → ∀ q, 0 < q →
      ∀ x : CategoryTheory.Abelian.Ext.{1} (structureSheaf X)
        ((moduleTwistFunctor L n).obj M) q, x = 0 := by
  classical
  let : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian p
  let : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace p
  let : IsNoetherian X := {}
  cases isEmpty_or_nonempty X with
  | inl hX =>
      let : IsEmpty X := hX
      refine ⟨0, fun n _ q hq => ?_⟩
      let : ((moduleTwistFunctor L n).obj M).IsFinitePresentation :=
        FiniteGlobalPresentation.moduleTwist_isFinitePresentation L n M
      let : ((moduleTwistFunctor L n).obj M).IsQuasicoherent :=
        (SheafOfModules.IsFinitePresentation.exists_quasicoherentData
          ((moduleTwistFunctor L n).obj M)).choose.isQuasicoherent
      obtain ⟨r, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hq)
      exact PiExponentSeshadri.AffineSchemeCohomology.affine_ext_zero X
        ((moduleTwistFunctor L n).obj M) r
  | inr hX =>
      obtain ⟨d, hd, σ, hσ, s, hs, hclosed⟩ := L.ample_projective_sections_noetherian p hL
      let : Fintype σ := hσ
      let : Nonempty σ := by
        obtain ⟨x⟩ := hX
        have hx : x ∈ (⨆ i, PiExponentSeshadri.SectionOpens.isoOpen (s i)) := by
          rw [hs]
          trivial
        obtain ⟨i, _⟩ := Opens.mem_iSup.mp hx
        exact ⟨i⟩
      let k : R →+* Γ(X, ⊤) :=
        p.appTop.hom.comp (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom
      let f : X ⟶ ProjectiveO1.projectiveSpace R σ := sectionsMorphism k s hs
      let : IsClosedImmersion f := hclosed
      let e := coordinateLineBundlePullbackIso (L.pow d) k s hs
      apply SerrePowerDescent.eventual_twist_ext_zero_of_power L d hd _ M
      intro A hA
      apply SerrePowerDescent.eventual_twist_ext_zero_of_lineIso e A
      apply ClosedImmersionSerreTransfer.eventual_twist_ext_zero_of_ambient f
        (ProjectiveO1.lineBundle (R := R) (σ := σ)) _ A
      intro N hN
      exact ProjectiveO1.serre_vanishing R σ N

theorem ample_serre_tensor_vanishing
    (p : X ⟶ Spec (CommRingCat.of R)) [IsProper p]
    (L : LineBundle X) (hL : LineBundle.IsAmple X L)
    (M : X.Modules) [M.IsFinitePresentation] :
    ∃ N, ∀ n, N ≤ n → ∀ q, 0 < q →
      ∀ x : cohomology (moduleTensor X M (modulePow X L.sheaf n)) q, x = 0 := by
  obtain ⟨N, hN⟩ := ample_serre_vanishing p L hL M
  refine ⟨N, fun n hn q hq => ?_⟩
  exact SerrePowerDescent.ext_zero_of_iso (moduleTwistPowerIso L M n) q (hN n hn q hq)

theorem ample_power_cohomology_zero
    (p : X ⟶ Spec (CommRingCat.of R)) [IsProper p]
    (L : LineBundle X) (hL : LineBundle.IsAmple X L) :
    ∃ N, ∀ n, N ≤ n → ∀ q, 0 < q →
      ∀ x : cohomology (modulePow X L.sheaf n) q, x = 0 := by
  let : (structureSheaf X).IsFinitePresentation :=
    LineBundleCoherent.structureSheaf_isFinitePresentation
  obtain ⟨N, hN⟩ := ample_serre_vanishing p L hL (structureSheaf X)
  refine ⟨N, fun n hn q hq => ?_⟩
  exact SerrePowerDescent.ext_zero_of_iso (moduleTwistUnitIso L n) q (hN n hn q hq)

end
end PiExponent.GeometrySupport.NoetherianAmpleSerreVanishing

end OAI
end Source0635

-- Source: OAI/NumberTheory/PiExponent/Cohomology/LineCohomologyDimension.lean
section Source0636
/-
Modification notice for the LogTwo project.
Derived from openai/math (Apache-2.0), revision adc7f1241b42e322a6451854ab7e4b4c146bf78a.
Original source: lean/OAI/NumberTheory/PiExponent/Cohomology/LineCohomologyDimension.lean
Changes: Convert module/import declarations to the Lean 4.34 public module format.
See ../THIRD_PARTY_NOTICES.txt for provenance and the recorded changes.
-/

namespace OAI

namespace PiExponent.NumericalAmpleness
noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace
open PiExponentSeshadri.Geometry
open PiExponent.SectionZeroIdeal

theorem lineBundle_cohomology_zero_of_dimension_le (d : ℕ) :
    ∀ {X : Scheme.{0}} (p : X ⟶ Spec (CommRingCat.of ℂ)) [IsProper p]
      (H : LineBundle X), H.IsAmple → ∀ (M : LineBundle X),
      topologicalKrullDim X ≤ d → ∀ q : ℕ, d < q →
      ∀ z : cohomology M.sheaf q, z = 0 := by
  induction d with
  | zero =>
    intro X p hp H hH M hdim q hq
    let : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian p
    let : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace p
    let : IsNoetherian X := {}
    let : Finite X := finite_of_dim_le_zero hdim
    let : IsAffine X := proper_finite_scheme_isAffine p
    let := PiExponent.GeometrySupport.LineBundleCoherent.lineBundle_isFinitePresentation M
    let : M.sheaf.IsQuasicoherent :=
      (SheafOfModules.IsFinitePresentation.exists_quasicoherentData M.sheaf).choose.isQuasicoherent
    obtain ⟨k,rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hq)
    exact PiExponentSeshadri.AffineSchemeCohomology.affine_ext_zero X M.sheaf k
  | succ d ih =>
    intro X p hp H hH M hdim q hq
    let : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian p
    let : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace p
    let : IsNoetherian X := {}
    obtain ⟨k,rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : q ≠ 0)
    have hk : d < k := by omega
    obtain ⟨N,hN⟩ := GeneratorsSectionCover.ample_eventual_fin_section_cover H hH
    let a := N+1
    obtain ⟨l,t,ht⟩ := hN a (by omega)
    let A := H.pow a
    have hA : A.IsAmple := hH.pow a (by omega)
    obtain ⟨s,hs⟩ := exists_mono_section_of_finite_cover p A t ht
    let : Mono s := hs
    let i := (zeroIdeal A s).subschemeι
    have hdimD : topologicalKrullDim (zeroIdeal A s).subscheme ≤ d :=
      regular_sectionZero_dimension_le A s d (by simpa only [Nat.cast_add,Nat.cast_one] using hdim)
    let F : ℕ → X.Modules := fun n => ((A.pow n).tensor M).sheaf
    let Q : ℕ → X.Modules := fun n => (Scheme.Modules.pushforward i).obj
      ((Scheme.Modules.pullback i).obj ((A.pow (n+1)).tensor M).sheaf)
    have hQ (n j : ℕ) (hj : d < j) : ∀ z : cohomology (Q n) j, z = 0 := by
      have hD := ih (i ≫ p) (H.pullback i) (hH.pullback_closedImmersion H i)
        ((((A.pow (n+1)).tensor M).pullback i)) hdimD j hj
      let e := ClosedImmersionSerreTransfer.cohomologyLinearEquiv i p
        ((Scheme.Modules.pullback i).obj ((A.pow (n+1)).tensor M).sheaf) j
      intro z
      obtain ⟨w,rfl⟩ := e.surjective z
      exact (congrArg e (hD w)).trans e.map_zero
    have hstep (n : ℕ) : Function.Bijective
        (cohomologyMap p (mixedCartierPowerMultiply A M s n) (k+1)) := by
      obtain ⟨hz,hS⟩ := regular_mixedCartierPower_restriction_shortExact p A M s n
      exact cohomologyMap_bijective_of_quotient_vanishing p _ hS k
        (hQ n k hk) (hQ n (k+1) (by omega))
    let := PiExponent.GeometrySupport.LineBundleCoherent.lineBundle_isFinitePresentation M
    obtain ⟨K,hK⟩ := GeometrySupport.NoetherianAmpleSerreVanishing.ample_serre_tensor_vanishing
      p A hA M.sheaf
    have hzeroK : ∀ z : cohomology (F K) (k+1), z = 0 :=
      GeometrySupport.SerrePowerDescent.ext_zero_of_iso
        (moduleTensorComm M.sheaf (A.pow K).sheaf) (k+1) (hK K le_rfl (k+1) (by omega))
    have hback : ∀ n : ℕ, (∀ z : cohomology (F n) (k+1), z = 0) →
        ∀ z : cohomology (F 0) (k+1), z = 0 := by
      intro n
      induction n with
      | zero => exact fun h => h
      | succ n ihn =>
        intro hn
        apply ihn
        intro z
        apply (hstep n).injective
        rw [map_zero]
        exact hn _
    exact GeometrySupport.SerrePowerDescent.ext_zero_of_iso (moduleTensorUnit M.sheaf)
      (k+1) (hback K hzeroK)

end
end PiExponent.NumericalAmpleness

end OAI
end Source0636

-- Source: OAI/NumberTheory/PiExponent/Ampleness/AmpleCurveDegreePositive.lean
section Source0637
/-
Modification notice for the LogTwo project.
Derived from openai/math (Apache-2.0), revision adc7f1241b42e322a6451854ab7e4b4c146bf78a.
Original source: lean/OAI/NumberTheory/PiExponent/Ampleness/AmpleCurveDegreePositive.lean
Changes: Convert module/import declarations to the Lean 4.34 public module format.
See ../THIRD_PARTY_NOTICES.txt for provenance and the recorded changes.
-/

namespace OAI

noncomputable section
namespace PiExponent.CurveDegree
open AlgebraicGeometry CategoryTheory TopologicalSpace
open PiExponentSeshadri.Geometry PiExponentSeshadri.Frames
open PiExponent.SectionZeroIdeal
variable {X : Scheme.{0}}

theorem exists_ample_section_with_zero [IsIntegral X]
    (hdim : topologicalKrullDim X = 1) (L : LineBundle X) (hL : L.IsAmple) :
    ∃ n : ℕ, 0 < n ∧ ∃ s : GlobalSections X (L.pow n).sheaf,
      s ≠ 0 ∧ ∃ y : X, y ∉ sectionOpen X s := by
  classical
  have : Nontrivial X := by
    by_contra h
    have : Subsingleton X := not_nontrivial_iff_subsingleton.mp h
    have hz := topologicalKrullDim_zero_of_discreteTopology X
    rw [hdim] at hz
    norm_num at hz
  obtain ⟨y, hy⟩ := exists_ne (genericPoint X)
  have hclosed := CurveMorphismFinite.isClosed_singleton_of_ne_genericPoint X hdim.le y hy
  let U : X.Opens := ⟨({y} : Set X)ᶜ, hclosed.isOpen_compl⟩
  have hη : genericPoint X ∈ U := by
    change genericPoint X ≠ y
    exact Ne.symm hy
  obtain ⟨n, hn, s, hsη, hsub, -⟩ := hL (genericPoint X) U hη
  refine ⟨n, hn, s, section_ne_zero_of_mem_isoOpen (L.pow n) s (genericPoint X) hsη,
    y, ?_⟩
  intro hys
  exact hsub hys rfl

theorem finite_nonempty_euler_pos [Finite X] [Nonempty X]
    (p : X ⟶ Spec (CommRingCat.of ℂ)) [IsProper p] (d : ℕ) :
    0 < eulerCharacteristic p d (structureSheaf X) := by
  classical
  let : Algebra ℂ Γ(X, ⊤) := (baseScalars p).toAlgebra
  have : FiniteDimensional ℂ Γ(X, ⊤) := proper_finite_functions p
  obtain ⟨x⟩ : Nonempty X := inferInstance
  have : Nontrivial Γ(X, ⊤) := (X.presheaf.germ ⊤ x trivial).hom.domain_nontrivial
  rw [proper_finite_euler]
  change (0 : ℤ) < (Module.finrank ℂ Γ(X, ⊤) : ℤ)
  exact_mod_cast (Module.finrank_pos (R := ℂ) (M := Γ(X, ⊤)))

theorem section_euler_degree_pos [IsIntegral X]
    (p : X ⟶ Spec (CommRingCat.of ℂ)) [IsProper p]
    (hdim : topologicalKrullDim X ≤ 1)
    (L : LineBundle X) (s : GlobalSections X L.sheaf) (hs : s ≠ 0)
    (hzero : ∃ y : X, y ∉ sectionOpen X s)
    (hfiniteO : ∀ n ≤ 1,
      letI := Module.compHom (cohomology (structureSheaf X) n) (baseScalars p)
      FiniteDimensional ℂ (cohomology (structureSheaf X) n))
    (hfiniteL : ∀ n ≤ 1,
      letI := Module.compHom (cohomology L.sheaf n) (baseScalars p)
      FiniteDimensional ℂ (cohomology L.sheaf n))
    [Subsingleton (cohomology (structureSheaf X) 2)] :
    0 < eulerCharacteristic p 1 L.sheaf -
      eulerCharacteristic p 1 (structureSheaf X) := by
  classical
  have hsMono : Mono s := L.mono_section s hs
  let I := zeroIdeal L s
  have hI : I ≠ ⊥ := zeroIdeal_ne_bot L s hs
  let : Finite I.subscheme := finite_subscheme_of_curve p hdim I hI
  let : Fintype I.subscheme := Fintype.ofFinite _
  obtain ⟨y, hy⟩ := hzero
  have hyI : y ∈ I.support := by
    change y ∈ ((zeroIdeal L s).support : Set X)
    rw [zeroIdeal_support]
    exact hy
  have hyrange : y ∈ Set.range I.subschemeι := by
    rw [Scheme.IdealSheafData.range_subschemeι]
    exact hyI
  obtain ⟨z, -⟩ := hyrange
  have : Nonempty I.subscheme := ⟨z⟩
  have heq : ∀ x : X, ∃ U : X.affineOpens, x ∈ U.1 ∧
      ∃ f : (L.pow 0).sheaf.restrict U.1.ι ≅ O U.1.toScheme,
      ∃ e : L.sheaf.restrict U.1.ι ≅ O U.1.toScheme,
        I.ideal U = Ideal.span {(U.1.topIso.hom
          (endValue (f.inv ≫ (Scheme.Modules.restrictFunctor U.1.ι).map s ≫ e.hom)))} := by
    intro x
    obtain ⟨U, hx, ⟨e⟩, -⟩ := common_affine_frames L L x
    refine ⟨U, hx, Scheme.Modules.restrictUnitIso U.1.ι, e, ?_⟩
    simpa only [coefficient, restrictSection, Category.assoc] using! zeroIdeal_on_frame L s U e
  have : Subsingleton (cohomology (L.pow 0).sheaf 2) := by
    change Subsingleton (cohomology (structureSheaf X) 2)
    infer_instance
  have hdegree := @CartierDegreeLength.cartier_euler_difference_eq_sum_local_lengths
    X inferInstance p inferInstance hdim (L.pow 0) L s hsMono I hI heq hfiniteO hfiniteL inferInstance
  change eulerCharacteristic p 1 L.sheaf -
    eulerCharacteristic p 1 (structureSheaf X) = _ at hdegree
  have hsum := proper_finite_euler_eq_sum_stalk_lengths (I.subschemeι ≫ p) 1
  have hpos := finite_nonempty_euler_pos (I.subschemeι ≫ p) 1
  rw [hdegree]
  rwa [hsum] at hpos

theorem ample_euler_degree_pos [IsIntegral X]
    (p : X ⟶ Spec (CommRingCat.of ℂ)) [IsProper p]
    (hdim : topologicalKrullDim X = 1)
    (L : LineBundle X) (hL : L.IsAmple)
    (hfinite : FiniteLineCohomology p) :
    0 < eulerCharacteristic p 1 L.sheaf -
      eulerCharacteristic p 1 (structureSheaf X) := by
  have hH2 : LineCohomologyTwoZero X := by
    intro M
    exact ⟨fun a b =>
      (NumericalAmpleness.lineBundle_cohomology_zero_of_dimension_le 1 p L hL M
        hdim.le 2 (by omega) a).trans
      (NumericalAmpleness.lineBundle_cohomology_zero_of_dimension_le 1 p L hL M
        hdim.le 2 (by omega) b).symm⟩
  obtain ⟨n, hn, s, hs, hzero⟩ := exists_ample_section_with_zero hdim L hL
  have : Subsingleton (cohomology (structureSheaf X) 2) := hH2 (L.pow 0)
  have hpos := section_euler_degree_pos p hdim.le (L.pow n) s hs hzero
    (hfinite (L.pow 0)) (hfinite (L.pow n))
  rw [power_euler p hdim.le L hL hfinite hH2 L n] at hpos
  have hnz : (0 : ℤ) < n := by exact_mod_cast hn
  exact (mul_pos_iff_of_pos_left hnz).mp hpos

theorem finite_line_cohomology_of_ample [IsIntegral X]
    (p : X ⟶ Spec (CommRingCat.of ℂ)) [IsProper p]
    (H : LineBundle X) (hH : H.IsAmple) : FiniteLineCohomology p := by
  intro M q _
  let := GeometrySupport.LineBundleCoherent.lineBundle_isFinitePresentation M
  exact AmpleCohomologyFinite.cohomology_finite_of_ample p H hH M.sheaf q

theorem euler_degree_pos_of_ample [IsIntegral X]
    (p : X ⟶ Spec (CommRingCat.of ℂ)) [IsProper p]
    (hdim : topologicalKrullDim X = 1) (L : LineBundle X) (hL : L.IsAmple) :
    0 < eulerCharacteristic p 1 L.sheaf -
      eulerCharacteristic p 1 (structureSheaf X) :=
  ample_euler_degree_pos p hdim L hL (finite_line_cohomology_of_ample p L hL)

end PiExponent.CurveDegree

namespace PiExponent.NumericalAmpleness
open AlgebraicGeometry CategoryTheory
open PiExponentSeshadri.Geometry

theorem curveDegree_pos_of_ample
    {X : Scheme.{0}} (p : X ⟶ Spec (CommRingCat.of ℂ)) [IsProper p]
    (L : LineBundle X) (hL : L.IsAmple) (C : IntegralCurve X) :
    0 < curveDegree p L C := by
  exact CurveDegree.euler_degree_pos_of_ample (C.embedding ≫ p) C.dimension
    (L.pullback C.embedding) (LineBundle.IsAmple.pullback_closedImmersion L hL C.embedding)

end PiExponent.NumericalAmpleness

end

end OAI
end Source0637

-- Source: OAI/NumberTheory/PiExponent/Ampleness/NefAmple.lean
section Source0638
-- Modified in this edition: unused plain lemmas removed; see reduction.json.
/-
Modification notice for the LogTwo project.
Derived from openai/math (Apache-2.0), revision adc7f1241b42e322a6451854ab7e4b4c146bf78a.
Original source: lean/OAI/NumberTheory/PiExponent/Ampleness/NefAmple.lean
Changes: Convert module/import declarations to the Lean 4.34 public module format.
See ../THIRD_PARTY_NOTICES.txt for provenance and the recorded changes.
-/

namespace OAI

open Set
open scoped Pointwise

namespace PiExponent.NefAmple

variable {E : Type*} [AddCommGroup E] [Module ℝ E] [TopologicalSpace E]
  [IsTopologicalAddGroup E] [ContinuousConstSMul ℝ E]

def nonnegativeCone {ι : Type*} (degree : ι → E →L[ℝ] ℝ) : ConvexCone ℝ E where
  carrier := {x | ∀ i, 0 ≤ degree i x}
  smul_mem' := by
    intro c hc x hx i
    simpa only [map_smul, smul_eq_mul] using mul_nonneg hc.le (hx i)
  add_mem' := by
    intro x hx y hy i
    simpa only [map_add] using add_nonneg (hx i) (hy i)

omit [IsTopologicalAddGroup E] [ContinuousConstSMul ℝ E] in
@[simp] theorem mem_nonnegativeCone {ι : Type*} (degree : ι → E →L[ℝ] ℝ) (x : E) :
    x ∈ nonnegativeCone degree ↔ ∀ i, 0 ≤ degree i x := Iff.rfl

omit [IsTopologicalAddGroup E] [ContinuousConstSMul ℝ E] in
theorem isClosed_nonnegativeCone {ι : Type*} (degree : ι → E →L[ℝ] ℝ) :
    IsClosed (nonnegativeCone degree : Set E) := by
  have heq : (nonnegativeCone degree : Set E) = ⋂ i, {x | 0 ≤ degree i x} := by
    ext x
    simp
  rw [heq]
  exact isClosed_iInter (fun i => isClosed_le continuous_const (degree i).continuous)

omit [IsTopologicalAddGroup E] in

theorem pos_smul_mem_interior (C : ConvexCone ℝ E) {x : E}
    (hx : x ∈ interior (C : Set E)) {c : ℝ} (hc : 0 < c) :
    c • x ∈ interior (C : Set E) := by
  have hs : c • (C : Set E) ⊆ (C : Set E) := by
    rintro _ ⟨y, hy, rfl⟩
    exact C.smul_mem hc hy
  apply interior_mono hs
  rw [interior_smul₀ hc.ne']
  exact smul_mem_smul_set hx

omit [ContinuousConstSMul ℝ E] in

theorem add_mem_interior (C : ConvexCone ℝ E) {x y : E}
    (hx : x ∈ C) (hy : y ∈ interior (C : Set E)) :
    x + y ∈ interior (C : Set E) := by
  have hm : x + y ∈ (C : Set E) + interior (C : Set E) := add_mem_add hx hy
  have hi : x + y ∈ interior ((C : Set E) + (C : Set E)) :=
    subset_interior_add_right hm
  apply interior_mono (s := (C : Set E) + (C : Set E)) ?_ hi
  rintro _ ⟨a, ha, b, hb, rfl⟩
  exact C.add_mem ha hb

theorem combination_denominator_pos {a σ : ℝ} (ha : 1 < a) (hσ : 0 < σ) :
    0 < a * (1 + σ) - 1 := by
  have hp : 0 < a * σ := mul_pos (zero_lt_one.trans ha) hσ
  nlinarith

omit [TopologicalSpace E] [IsTopologicalAddGroup E] [ContinuousConstSMul ℝ E] in

theorem interpolation_divisor_identity (A F : E) {a σ : ℝ}
    (ha : 1 < a) (hσ : 0 < σ) :
    ((a - 1) / (a * (1 + σ) - 1)) • (A - (1 + σ) • F) +
      (σ / (a * (1 + σ) - 1)) • (a • A - F) = A - F := by
  have hd : a * (1 + σ) - 1 ≠ 0 := (combination_denominator_pos ha hσ).ne'
  have hA : (a - 1) / (a * (1 + σ) - 1) +
      σ / (a * (1 + σ) - 1) * a = 1 := by field_simp; ring
  have hF : ((a - 1) / (a * (1 + σ) - 1)) * (1 + σ) +
      σ / (a * (1 + σ) - 1) = 1 := by field_simp; ring
  calc
    _ = ((a - 1) / (a * (1 + σ) - 1) + σ / (a * (1 + σ) - 1) * a) • A -
        (((a - 1) / (a * (1 + σ) - 1)) * (1 + σ) + σ / (a * (1 + σ) - 1)) • F := by
          simp only [smul_sub, smul_smul]
          rw [add_smul, add_smul]
          abel
    _ = A - F := by rw [hA, hF, one_smul, one_smul]

omit [IsTopologicalAddGroup E] [ContinuousConstSMul ℝ E] in

theorem interpolation_degree_margin (degree : E →L[ℝ] ℝ) (A F : E)
    {a σ : ℝ} (ha : 1 < a) (hσ : 0 < σ)
    (hne : 0 ≤ degree (A - (1 + σ) • F)) :
    (σ / (a * (1 + σ) - 1)) * degree (a • A - F) ≤ degree (A - F) := by
  have hcoef : 0 < (a - 1) / (a * (1 + σ) - 1) :=
    div_pos (sub_pos.mpr ha) (combination_denominator_pos ha hσ)
  have he := congrArg degree (interpolation_divisor_identity A F ha hσ)
  simp only [map_add, map_smul, smul_eq_mul] at he
  have hn := mul_nonneg hcoef.le hne
  linarith

omit [IsTopologicalAddGroup E] [ContinuousConstSMul ℝ E] in

theorem interpolation_degree_pos (degree : E →L[ℝ] ℝ) (A F : E)
    {a σ : ℝ} (ha : 1 < a) (hσ : 0 < σ)
    (hne : 0 ≤ degree (A - (1 + σ) • F))
    (hpos : 0 < degree (a • A - F)) : 0 < degree (A - F) :=
  (mul_pos (div_pos hσ (combination_denominator_pos ha hσ)) hpos).trans_le
    (interpolation_degree_margin degree A F ha hσ hne)

end PiExponent.NefAmple

end OAI
end Source0638

-- Source: OAI/NumberTheory/PiExponent/Approximation/ConstantPullbackDegree.lean
section Source0639
-- Modified in this edition: unused plain lemmas removed; see reduction.json.
/-
Modification notice for the LogTwo project.
Derived from openai/math (Apache-2.0), revision adc7f1241b42e322a6451854ab7e4b4c146bf78a.
Original source: lean/OAI/NumberTheory/PiExponent/Approximation/ConstantPullbackDegree.lean
Changes: Convert module/import declarations to the Lean 4.34 public module format.
See ../THIRD_PARTY_NOTICES.txt for provenance and the recorded changes.
-/

namespace OAI

namespace PiExponent.ConstantPullbackDegree
noncomputable section
open AlgebraicGeometry CategoryTheory TopologicalSpace
open PiExponentSeshadri.Geometry PiExponentSeshadri.Frames
variable {X Y : Scheme.{0}}

def pullbackFrame_of_range_subset (K : LineBundle Y) (g : X ⟶ Y)
    (U : Y.Opens) (h : Set.range g ⊆ (U : Set Y))
    (e : K.sheaf.restrict U.ι ≅ structureSheaf U.toScheme) :
    (K.pullback g).sheaf ≅ structureSheaf X := by
  have hr : Set.range g ⊆ Set.range U.ι := by
    rw [Scheme.Opens.range_ι]
    exact h
  let l := IsOpenImmersion.lift U.ι g hr
  have hl : l ≫ U.ι = g := IsOpenImmersion.lift_fac U.ι g hr
  exact (Scheme.Modules.pullbackCongr hl.symm).app K.sheaf ≪≫
    ((Scheme.Modules.pullbackComp l U.ι).app K.sheaf).symm ≪≫
      (Scheme.Modules.pullback l).mapIso ((Scheme.Modules.restrictFunctorIsoPullback U.ι).app
        K.sheaf).symm ≪≫ (Scheme.Modules.pullback l).mapIso e ≪≫ pullbackUnitIso l

def constantPullbackIso (K : LineBundle Y) (g : X ⟶ Y) (y : Y)
    (hg : Set.range g ⊆ ({y} : Set Y)) :
    (K.pullback g).sheaf ≅ structureSheaf X := by
  apply Classical.choice
  obtain ⟨U, hy, ⟨e⟩⟩ := K.locallyRankOne y
  refine ⟨pullbackFrame_of_range_subset K g U ?_ e⟩
  intro z hz
  have hz' : z = y := hg hz
  exact hz'.symm ▸ hy

theorem euler_difference_eq_zero (p : X ⟶ Spec (CommRingCat.of ℂ))
    (K : LineBundle Y) (g : X ⟶ Y) (y : Y)
    (hg : Set.range g ⊆ ({y} : Set Y)) (d : ℕ) :
    eulerCharacteristic p d (K.pullback g).sheaf -
      eulerCharacteristic p d (structureSheaf X) = 0 := by
  rw [eulerCharacteristic_iso p (constantPullbackIso K g y hg) d]
  exact sub_self _

theorem curveDegree_eq_zero_of_contracted
    (p : X ⟶ Spec (CommRingCat.of ℂ)) (K : LineBundle Y)
    (g : X ⟶ Y) (C : NumericalAmpleness.IntegralCurve X) (y : Y)
    (hg : Set.range (C.embedding ≫ g) ⊆ ({y} : Set Y)) :
    NumericalAmpleness.curveDegree p (K.pullback g) C = 0 := by
  have he := eulerCharacteristic_iso (C.embedding ≫ p)
    ((Scheme.Modules.pullbackComp C.embedding g).app K.sheaf) 1
  simp only [CategoryTheory.Functor.comp_obj] at he
  unfold NumericalAmpleness.curveDegree
  change eulerCharacteristic (C.embedding ≫ p) 1
      ((Scheme.Modules.pullback C.embedding).obj ((Scheme.Modules.pullback g).obj K.sheaf)) -
    eulerCharacteristic (C.embedding ≫ p) 1 (structureSheaf C.scheme) = 0
  rw [he]
  exact euler_difference_eq_zero (C.embedding ≫ p) K (C.embedding ≫ g) y hg 1

end
end PiExponent.ConstantPullbackDegree

end OAI
end Source0639

-- Source: OAI/NumberTheory/PiExponent/LocalAlgebra/InvertibleIdealAway.lean
section Source0640
/-
Modification notice for the LogTwo project.
Derived from openai/math (Apache-2.0), revision adc7f1241b42e322a6451854ab7e4b4c146bf78a.
Original source: lean/OAI/NumberTheory/PiExponent/LocalAlgebra/InvertibleIdealAway.lean
Changes: Convert module/import declarations to the Lean 4.34 public module format.
See ../THIRD_PARTY_NOTICES.txt for provenance and the recorded changes.
-/

namespace OAI

noncomputable section
namespace PiExponent.InvertibleIdealAway
open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite
open PiExponentSeshadri.Geometry PiExponentSeshadri.InvertibleLocal
variable {X B C : Scheme.{0}}

private theorem isIso_of_comp_iso_hom {D : Type*} [Category D]
    {A B C : D} (f : A ⟶ B) (e : B ≅ C) (h : IsIso (f ≫ e.hom)) : IsIso f :=
  (isIso_comp_right_iff f e.hom).mp h

theorem restrictedInclusion_isIso_of_unit
    (I : X.IdealSheafData) (p : B ⟶ X)
    (J : LineBundle B) (ι : J.sheaf ⟶ structureSheaf B)
    (hJ : PresentsPullbackIdeal I p J ι)
    (U : B.Opens) (V : X.affineOpens) (hUV : U ≤ p ⁻¹ᵁ V.1)
    (hunit : (I.comap p).comap U.ι = ⊤) :
    IsIso (restrictedInclusion J ι U.ι) := by
  have : Mono ι := hJ.1
  let φ := restrictedInclusion J ι U.ι
  have : Mono φ := inferInstance
  apply PiExponentSeshadri.IdealModule.isIso_of_affine_app
  intro W
  have himage : ((φ.val.app (op W.1)).hom).range = ⊤ := by
    change ((restrictedInclusion J ι U.ι).val.app (op W.1)).hom.range = _
    rw [restricted_image_on_chart J ι hJ U.ι W V
      ((U.ι_image_le W.1).trans hUV), hunit]
    rfl
  apply (ConcreteCategory.isIso_iff_bijective _).mpr
  constructor
  · have : Mono φ.val := inferInstanceAs
      (Mono ((Scheme.Modules.toPresheafOfModules U.toScheme).map φ))
    exact PresheafOfModules.injective_of_mono φ.val (op W.1)
  · intro r
    have hr : r ∈ ((φ.val.app (op W.1)).hom).range := by
      rw [himage]
      trivial
    exact hr

theorem inclusion_isIso_of_comap_top
    (I : X.IdealSheafData) (p : B ⟶ X)
    (J : LineBundle B) (ι : J.sheaf ⟶ structureSheaf B)
    (hJ : PresentsPullbackIdeal I p J ι) (hunit : I.comap p = ⊤) : IsIso ι := by
  apply PiExponentSeshadri.SectionOpens.isIso_of_locally_isIso
  intro b
  obtain ⟨V, hV, hbV, -⟩ := exists_isAffineOpen_mem_and_subset
    (show p b ∈ (⊤ : X.Opens) from trivial)
  let U := p ⁻¹ᵁ V
  have hi : IsIso (restrictedInclusion J ι U.ι) :=
    restrictedInclusion_isIso_of_unit I p J ι hJ U ⟨V, hV⟩ le_rfl (by
      rw [hunit, Scheme.IdealSheafData.comap_top])
  refine ⟨U, hbV, ?_⟩
  exact isIso_of_comp_iso_hom ((Scheme.Modules.restrictFunctor U.ι).map ι)
    (Scheme.Modules.restrictUnitIso U.ι) hi

theorem pullback_map_isIso_of_factors
    {M N : B.Modules} (ι : M ⟶ N) (g : C ⟶ B)
    (U : B.Opens) (h : C ⟶ U.toScheme) (hfac : h ≫ U.ι = g)
    [IsIso ((Scheme.Modules.restrictFunctor U.ι).map ι)] :
    IsIso ((Scheme.Modules.pullback g).map ι) := by
  have : IsIso ((Scheme.Modules.pullback U.ι).map ι) :=
    (NatIso.isIso_map_iff (Scheme.Modules.restrictFunctorIsoPullback U.ι) ι).mp inferInstance
  have : IsIso ((Scheme.Modules.pullback h).map ((Scheme.Modules.pullback U.ι).map ι)) :=
    inferInstance
  have hcomp : IsIso ((Scheme.Modules.pullback (h ≫ U.ι)).map ι) :=
    (NatIso.isIso_map_iff (Scheme.Modules.pullbackComp h U.ι) ι).mp (by
      change IsIso ((Scheme.Modules.pullback h).map ((Scheme.Modules.pullback U.ι).map ι))
      infer_instance)
  exact hfac ▸ hcomp

theorem pullback_inclusion_isIso_of_avoids
    (I : X.IdealSheafData) (p : B ⟶ X)
    (J : LineBundle B) (ι : J.sheaf ⟶ structureSheaf B)
    (hJ : PresentsPullbackIdeal I p J ι) (g : C ⟶ B)
    (havoid : ∀ c, (g ≫ p) c ∉ I.support) :
    IsIso ((Scheme.Modules.pullback g).map ι) := by
  let V : X.Opens := ⟨(I.support : Set X)ᶜ, I.support.isClosed.isOpen_compl⟩
  let U : B.Opens := p ⁻¹ᵁ V
  have hunit : I.comap (U.ι ≫ p) = ⊤ :=
    CompactJetIdeal.restrict_eq_top_of_disjoint I (U.ι ≫ p) (fun u => u.property)
  have hpresent := presents_restrict_general I p J ι hJ U.ι
  have hinc : IsIso (restrictedInclusion J ι U.ι) :=
    inclusion_isIso_of_comap_top I (U.ι ≫ p) (restrictLineBundle J U.ι)
      (restrictedInclusion J ι U.ι) hpresent hunit
  have : IsIso ((Scheme.Modules.restrictFunctor U.ι).map ι) :=
    isIso_of_comp_iso_hom ((Scheme.Modules.restrictFunctor U.ι).map ι)
      (Scheme.Modules.restrictUnitIso U.ι) hinc
  have hrange : Set.range g ⊆ Set.range U.ι := by
    rintro _ ⟨c, rfl⟩
    exact ⟨⟨g c, havoid c⟩, rfl⟩
  let h : C ⟶ U.toScheme := IsOpenImmersion.lift U.ι g hrange
  exact pullback_map_isIso_of_factors ι g U h (IsOpenImmersion.lift_fac _ _ _)

def pullbackInclusion (J : LineBundle B) (ι : J.sheaf ⟶ structureSheaf B)
    (g : C ⟶ B) : (J.pullback g).sheaf ⟶ structureSheaf C :=
  (Scheme.Modules.pullback g).map ι ≫ (pullbackUnitIso g).hom

def pullbackIsoOfAvoids
    (I : X.IdealSheafData) (p : B ⟶ X)
    (J : LineBundle B) (ι : J.sheaf ⟶ structureSheaf B)
    (hJ : PresentsPullbackIdeal I p J ι) (g : C ⟶ B)
    (havoid : ∀ c, (g ≫ p) c ∉ I.support) :
    (J.pullback g).sheaf ≅ structureSheaf C := by
  exact @asIso C.Modules _ _ _ ((Scheme.Modules.pullback g).map ι)
    (pullback_inclusion_isIso_of_avoids I p J ι hJ g havoid) ≪≫ pullbackUnitIso g

def pullbackIsoOfComapTop
    (I : X.IdealSheafData) (p : B ⟶ X)
    (J : LineBundle B) (ι : J.sheaf ⟶ structureSheaf B)
    (hJ : PresentsPullbackIdeal I p J ι) (g : C ⟶ B)
    (hunit : I.comap (g ≫ p) = ⊤) :
    (J.pullback g).sheaf ≅ structureSheaf C := by
  apply pullbackIsoOfAvoids I p J ι hJ g
  intro c hc
  have hm : c ∈ (I.comap (g ≫ p)).support := by
    rw [Scheme.IdealSheafData.support_comap]
    exact hc
  rw [hunit] at hm
  exact hm

end PiExponent.InvertibleIdealAway

end

end OAI
end Source0640

-- Source: LogTwo/Geometry/CurveMarginLemmas.lean
section Source0641
/-
Modification notice for the LogTwo project.
Adapted from openai/math (Apache-2.0), revision adc7f1241b42e322a6451854ab7e4b4c146bf78a.
Changes: Extract generic degree-margin arguments and omit the fixed-center contact bound.
See ../THIRD_PARTY_NOTICES.txt for provenance and the recorded changes.
-/

/-! Scheme-generic degree laws and the three curve cases, adapted from the
first part of openai/math Ampleness/BlowupCurveMargin.lean (Apache-2.0).
The fixed-Y contact inequality and its import are deliberately not included. -/
namespace LogTwo.Geometry.CurveMarginLemmas
noncomputable section
open OAI PiExponent AlgebraicGeometry CategoryTheory
open PiExponentSeshadri.Geometry NumericalAmpleness
variable {B X : Scheme.{0}}

theorem curve_degree_laws (p : B ⟶ Spec (.of ℂ)) [IsProper p]
    (H : LineBundle B) (hH : H.IsAmple) (C : IntegralCurve B) :
    (∀ L M : LineBundle B, curveDegree p (L.tensor M) C =
      curveDegree p L C + curveDegree p M C) ∧
    (∀ (L : LineBundle B) (n : ℕ), curveDegree p (L.pow n) C =
      (n : ℤ) * curveDegree p L C) := by
  let HC := H.pullback C.embedding
  have hHC : HC.IsAmple := LineBundle.IsAmple.pullback_closedImmersion H hH C.embedding
  have hfinite := CurveDegree.finite_line_cohomology_of_ample (C.embedding ≫ p) HC hHC
  have hH2 : CurveDegree.LineCohomologyTwoZero C.scheme := by
    intro M
    exact ⟨fun a b =>
      (lineBundle_cohomology_zero_of_dimension_le 1 (C.embedding ≫ p) HC hHC M
        C.dimension.le 2 (by omega) a).trans
      (lineBundle_cohomology_zero_of_dimension_le 1 (C.embedding ≫ p) HC hHC M
        C.dimension.le 2 (by omega) b).symm⟩
  exact ⟨fun L M => curveDegree_tensor p H hH L M C hfinite hH2,
    fun L n => curveDegree_pow p H hH L C hfinite hH2 n⟩

def marginCoefficient (a : ℕ) (σ : ℝ) : ℝ := σ / ((a : ℝ) * (1 + σ) - 1)

theorem marginCoefficient_pos {a : ℕ} (ha : 1 < a) {σ : ℝ} (hσ : 0 < σ) :
    0 < marginCoefficient a σ := by
  apply div_pos hσ
  exact NefAmple.combination_denominator_pos (by exact_mod_cast ha) hσ

theorem margin_of_nonnegative_degree
    (p : B ⟶ Spec (.of ℂ)) [IsProper p] (A J : LineBundle B)
    (a : ℕ) (ha : 1 < a) (hample : ((A.pow a).tensor J).IsAmple)
    (σ : ℝ) (hσ : 0 < σ) (C : IntegralCurve B)
    (hn : 0 ≤ (curveDegree p A C : ℝ) + (1 + σ) * (curveDegree p J C : ℝ)) :
    marginCoefficient a σ * (curveDegree p ((A.pow a).tensor J) C : ℝ) ≤
      (curveDegree p (A.tensor J) C : ℝ) := by
  obtain ⟨ht,hp⟩ := curve_degree_laws p ((A.pow a).tensor J) hample C
  rw [ht, hp, ht]
  push_cast
  unfold marginCoefficient
  have ha' : 1 < (a : ℝ) := by exact_mod_cast ha
  have hd := NefAmple.combination_denominator_pos ha' hσ
  rw [div_mul_eq_mul_div]
  apply (div_le_iff₀ hd).mpr
  have hn' := mul_nonneg (sub_pos.mpr ha').le hn
  nlinarith

theorem curveDegree_zero_of_frame (p : B ⟶ Spec (.of ℂ))
    (J : LineBundle B) (C : IntegralCurve B)
    (e : (J.pullback C.embedding).sheaf ≅ structureSheaf C.scheme) :
    curveDegree p J C = 0 := by
  unfold curveDegree
  change eulerCharacteristic (C.embedding ≫ p) 1 (J.pullback C.embedding).sheaf - _ = 0
  rw [eulerCharacteristic_iso (C.embedding ≫ p) e 1]
  exact sub_self _

theorem margin_of_exceptional_frame
    (p : B ⟶ Spec (.of ℂ)) [IsProper p] (A J : LineBundle B)
    (a : ℕ) (ha : 1 < a) (hample : ((A.pow a).tensor J).IsAmple)
    (σ : ℝ) (hσ : 0 < σ) (C : IntegralCurve B)
    (e : (J.pullback C.embedding).sheaf ≅ structureSheaf C.scheme) :
    marginCoefficient a σ * (curveDegree p ((A.pow a).tensor J) C : ℝ) ≤
      (curveDegree p (A.tensor J) C : ℝ) := by
  have hj := curveDegree_zero_of_frame p J C e
  have hpos := curveDegree_pos_of_ample p ((A.pow a).tensor J) hample C
  obtain ⟨ht,hp⟩ := curve_degree_laws p ((A.pow a).tensor J) hample C
  rw [ht, hp, hj, add_zero] at hpos
  have ha' : (0 : ℤ) < a := by exact_mod_cast (Nat.zero_lt_of_lt ha)
  have hA := (mul_pos_iff_of_pos_left ha').mp hpos
  apply margin_of_nonnegative_degree p A J a ha hample σ hσ C
  rw [hj]
  simpa using (show (0 : ℝ) ≤ (curveDegree p A C : ℝ) by exact_mod_cast hA.le)

theorem margin_of_avoids_center
    (p : B ⟶ Spec (.of ℂ)) [IsProper p]
    (I : X.IdealSheafData) (π : B ⟶ X) (A J : LineBundle B)
    (ι : J.sheaf ⟶ structureSheaf B) (hJ : PresentsPullbackIdeal I π J ι)
    (a : ℕ) (ha : 1 < a) (hample : ((A.pow a).tensor J).IsAmple)
    (σ : ℝ) (hσ : 0 < σ) (C : IntegralCurve B)
    (havoid : ∀ c : C.scheme, (C.embedding ≫ π) c ∉ I.support) :
    marginCoefficient a σ * (curveDegree p ((A.pow a).tensor J) C : ℝ) ≤
      (curveDegree p (A.tensor J) C : ℝ) :=
  margin_of_exceptional_frame p A J a ha hample σ hσ C
    (InvertibleIdealAway.pullbackIsoOfAvoids I π J ι hJ C.embedding havoid)

theorem margin_of_image_outside_chart
    (p : B ⟶ Spec (.of ℂ)) [IsProper p]
    (I : X.IdealSheafData) (π : B ⟶ X) (A J : LineBundle B)
    (ι : J.sheaf ⟶ structureSheaf B) (hJ : PresentsPullbackIdeal I π J ι)
    (a : ℕ) (ha : 1 < a) (hample : ((A.pow a).tensor J).IsAmple)
    (σ : ℝ) (hσ : 0 < σ) (C : IntegralCurve B)
    (U : X.Opens) (hsupport : (I.support : Set X) ⊆ U)
    (hmiss : ∀ c : C.scheme, (C.embedding ≫ π) c ∉ U) :
    marginCoefficient a σ * (curveDegree p ((A.pow a).tensor J) C : ℝ) ≤
      (curveDegree p (A.tensor J) C : ℝ) :=
  margin_of_avoids_center p I π A J ι hJ a ha hample σ hσ C
    (fun c hc => hmiss c (hsupport hc))

theorem margin_of_contracted
    (p : B ⟶ Spec (.of ℂ)) [IsProper p] (π : B ⟶ X)
    (L : LineBundle X) (J : LineBundle B)
    (a : ℕ) (ha : 1 < a) (hample : (((L.pullback π).pow a).tensor J).IsAmple)
    (σ : ℝ) (hσ : 0 < σ) (C : IntegralCurve B)
    (x : X) (hc : Set.range (C.embedding ≫ π) ⊆ ({x} : Set X)) :
    marginCoefficient a σ * (curveDegree p (((L.pullback π).pow a).tensor J) C : ℝ) ≤
      (curveDegree p ((L.pullback π).tensor J) C : ℝ) := by
  have hA := ConstantPullbackDegree.curveDegree_eq_zero_of_contracted p L π C x hc
  have hpos := curveDegree_pos_of_ample p (((L.pullback π).pow a).tensor J) hample C
  obtain ⟨ht,hp⟩ := curve_degree_laws p (((L.pullback π).pow a).tensor J) hample C
  rw [ht, hp, hA, mul_zero, zero_add] at hpos
  apply margin_of_nonnegative_degree p (L.pullback π) J a ha hample σ hσ C
  rw [hA]
  exact add_nonneg (by norm_num) (mul_nonneg (by linarith)
    (by exact_mod_cast hpos.le))

end
end LogTwo.Geometry.CurveMarginLemmas
end Source0641

-- Source: LogTwo/Geometry/UniformCurveMargin.lean
section Source0642
-- Modified in this edition: unused plain lemmas removed; see reduction.json.
/-
Modification notice for the LogTwo project.
Adapted from openai/math (Apache-2.0), revision adc7f1241b42e322a6451854ab7e4b4c146bf78a.
Changes: Adapt the three-case curve argument to the verified varying-center degree inequality.
See ../THIRD_PARTY_NOTICES.txt for provenance and the recorded changes.
-/

/-! A single positive margin for every integral curve on the actual blowup.
The exponent and margin are chosen before the curve. Contracted curves and
curves missing the affine chart are handled geometrically; the remaining
case uses the proved varying-center contact bound and degree transfer. -/
namespace LogTwo.Geometry.MatrixBlowup
open OAI PiExponent AlgebraicGeometry CategoryTheory
open PiExponentSeshadri.Geometry NumericalAmpleness
open LogTwo.Interpolation LogTwo.Parameters LogTwo.Arithmetic
noncomputable section

variable {m K : ℕ} (w : Weights m) (y : Fin K → ℂ)
variable (hy0 : ∀ j, y j ≠ 0) (a : Fin K → Fin m → ℂ) (T : Fin m → ℕ)

def interpolationBundle : LineBundle (space w y a T) :=
  (A w y a T).tensor (J w y a T)

def degreeMargin : ℝ :=
  CurveMarginLemmas.marginCoefficient (ampleExponent w y hy0 a T) (curveSigma w.theta m)

theorem degreeMargin_pos : 0 < degreeMargin w y hy0 a T := by
  apply CurveMarginLemmas.marginCoefficient_pos (ampleExponent_gt_one w y hy0 a T)
  exact_mod_cast curveSigma_pos w.theta_pos w.theta_lt_one m

theorem contracted_curve_margin (C : IntegralCurve (space w y a T))
    (x : MatrixCompactification.space w)
    (hc : Set.range (C.embedding ≫ projection w y a T) ⊆ {x}) :
    degreeMargin w y hy0 a T * (curveDegree (structureMap w y a T) (H w y hy0 a T) C : ℝ) ≤
      (curveDegree (structureMap w y a T) (interpolationBundle w y a T) C : ℝ) := by
  exact CurveMarginLemmas.margin_of_contracted (structureMap w y a T)
    (projection w y a T) (hyperplane w) (J w y a T)
    (ampleExponent w y hy0 a T) (ampleExponent_gt_one w y hy0 a T)
    (H_ample w y hy0 a T) (curveSigma w.theta m)
    (by exact_mod_cast curveSigma_pos w.theta_pos w.theta_lt_one m) C x hc

theorem outside_chart_curve_margin (C : IntegralCurve (space w y a T))
    (hm : ∀ c : C.scheme,
      (C.embedding ≫ projection w y a T) c ∉ (MatrixCompactification.affineChart w).opensRange) :
    degreeMargin w y hy0 a T * (curveDegree (structureMap w y a T) (H w y hy0 a T) C : ℝ) ≤
      (curveDegree (structureMap w y a T) (interpolationBundle w y a T) C : ℝ) := by
  exact CurveMarginLemmas.margin_of_image_outside_chart (structureMap w y a T)
    (MatrixCompactification.centerIdeal w y a T) (projection w y a T)
    (A w y a T) (J w y a T) (exceptionalInclusion w y a T) (exceptional_presents w y a T)
    (ampleExponent w y hy0 a T) (ampleExponent_gt_one w y hy0 a T)
    (H_ample w y hy0 a T) (curveSigma w.theta m)
    (by exact_mod_cast curveSigma_pos w.theta_pos w.theta_lt_one m) C
    (MatrixCompactification.affineChart w).opensRange
    (MatrixCompactification.centerIdeal_support_subset_chart w y a T) hm

/-- All three curve cases, with the same positive coefficient independent of C. -/
theorem chosenWeights_uniform_curve_margin
    (n : ℕ) (hn : 1 ≤ n) (m : ℕ) (q : ℕ → ℕ) (hq : ∀ i, 2 ≤ q i)
    (hgrowth : ∀ i, i < m →
      denominatorSeparationFactor n m (chosenComparisonConstant n m) *
        (∏ j : Fin i, (ceilLogWeight (q j) : ℝ)) < (ceilLogWeight (q i) : ℝ)) :
    let w := chosenWeights n hn m (fun i => q i) (fun i => hq i)
    ∀ (y : Fin w.K → ℂ) (hy0 : ∀ j, y j ≠ 0), Function.Injective y →
      ∀ (a : Fin w.K → Fin m → ℂ) (F : ℚ), 1 / w.theta < F →
      ∀ C : IntegralCurve (space w y a (truncationOrders w F)),
      degreeMargin w y hy0 a (truncationOrders w F) *
          (curveDegree (structureMap w y a (truncationOrders w F))
            (H w y hy0 a (truncationOrders w F)) C : ℝ) ≤
        (curveDegree (structureMap w y a (truncationOrders w F))
          (interpolationBundle w y a (truncationOrders w F)) C : ℝ) := by
  classical
  dsimp only
  intro y hy0 hy a F hF C
  let w := chosenWeights n hn m (fun i => q i) (fun i => hq i)
  by_cases hc : ∃ x : MatrixCompactification.space w,
      Set.range (C.embedding ≫ projection w y a (truncationOrders w F)) ⊆ {x}
  · obtain ⟨x, hx⟩ := hc
    exact contracted_curve_margin w y hy0 a (truncationOrders w F) C x hx
  · by_cases hm : ∃ c : C.scheme,
        (C.embedding ≫ projection w y a (truncationOrders w F)) c ∈
          (MatrixCompactification.affineChart w).opensRange
    · exact CurveMarginLemmas.margin_of_nonnegative_degree
        (structureMap w y a (truncationOrders w F))
        (A w y a (truncationOrders w F)) (J w y a (truncationOrders w F))
        (ampleExponent w y hy0 a (truncationOrders w F))
        (ampleExponent_gt_one w y hy0 a (truncationOrders w F))
        (H_ample w y hy0 a (truncationOrders w F)) (curveSigma w.theta m)
        (by exact_mod_cast curveSigma_pos w.theta_pos w.theta_lt_one m) C
        (chosenWeights_integralCurve_degree_nonnegative n hn m q hq hgrowth
          y hy0 hy a F hF C hc hm)
    · exact outside_chart_curve_margin w y hy0 a (truncationOrders w F) C
        (fun c hh => hm ⟨c, hh⟩)

end
end LogTwo.Geometry.MatrixBlowup
end Source0642

-- Source: OAI/NumberTheory/PiExponent/Geometry/ProjectiveSectionReindex.lean
section Source0643
/-
Modification notice for the LogTwo project.
Derived from openai/math (Apache-2.0), revision adc7f1241b42e322a6451854ab7e4b4c146bf78a.
Original source: lean/OAI/NumberTheory/PiExponent/Geometry/ProjectiveSectionReindex.lean
Changes: Convert module/import declarations to the Lean 4.34 public module format.
See ../THIRD_PARTY_NOTICES.txt for provenance and the recorded changes.
-/

namespace OAI

noncomputable section

universe u

namespace PiExponentSeshadri.Projective

section
open AlgebraicGeometry CategoryTheory TopologicalSpace MvPolynomial
attribute [local instance] MvPolynomial.gradedAlgebra
variable {K σ : Type u} [CommRing K]

lemma reindex_polynomial_irrelevant_le :
    (HomogeneousIdeal.irrelevant (homogeneousSubmodule σ K)).toIdeal ≤
      Ideal.span (Set.range (MvPolynomial.X (R := K) : σ → MvPolynomial σ K)) := by
  rw [HomogeneousIdeal.toIdeal_irrelevant_le]
  intro n hn p hp
  change p ∈ idealOfVars σ K
  rw [← pow_one (idealOfVars σ K), mem_pow_idealOfVars_iff]
  intro d hd
  change 1 ≤ d.sum fun _ v => v
  rw [Finsupp.sum, ← hp.degree_eq_sum_deg_support hd]
  exact hn

def reindexCoordinateCover : (Proj (homogeneousSubmodule σ K)).AffineOpenCover :=
  Proj.affineOpenCoverOfIrrelevantLESpan _ (X (R := K))
    (m := fun _ => 1) (fun i => isHomogeneous_X K i) (fun _ => by decide)
    reindex_polynomial_irrelevant_le

end

section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace
open scoped AlgebraicGeometry
open PiExponentSeshadri.Frames MvPolynomial
variable {K σ : Type u} [CommRing K] {X : Scheme.{u}}
attribute [local instance] MvPolynomial.gradedAlgebra

theorem sectionsMorphism_isClosedImmersion {M : X.Modules} (k : K →+* Γ(X, ⊤))
    (s : σ → (O X ⟶ M)) (hcover : (⨆ i, SectionOpens.isoOpen (s i)) = ⊤)
    (haff : ∀ i, IsAffine (SectionOpens.isoOpen (s i)).toScheme)
    (hgen : ∀ i, Function.Surjective
      (eval₂Hom (((SectionOpens.isoOpen (s i)).ι.appTop.hom).comp k)
        (fun j => coefficient (sectionFrame (s i))
          (restrictSection (SectionOpens.isoOpen (s i)).ι (s j))))) :
    IsClosedImmersion (sectionsMorphism k s hcover) := by
  let V := reindexCoordinateCover (K := K) (σ := σ)
  apply IsZariskiLocalAtTarget.of_openCover (P := @IsClosedImmersion) V.openCover
  intro i
  change σ at i
  let U := SectionOpens.isoOpen (s i)
  let : IsAffine U.toScheme := haff i
  let k' := U.ι.appTop.hom.comp k
  let a : σ → Γ(U.toScheme, ⊤) := fun j => coefficient (sectionFrame (s i)) (restrictSection U.ι (s j))
  have hi : a i = 1 := sectionFrame_normalized (s i)
  let g : U.toScheme ⟶ Spec (CommRingCat.of
      (HomogeneousLocalization.Away (homogeneousSubmodule σ K) (MvPolynomial.X i))) :=
    U.toScheme.toSpecΓ ≫ Spec.map (CommRingCat.ofHom
    (evalAway (𝒜 := homogeneousSubmodule σ K) (eval₂Hom k' a) (MvPolynomial.X i)
      (by simpa only [eval₂Hom_X', hi] using (isUnit_one : IsUnit (1 : Γ(U.toScheme, ⊤))))))
  have hg : IsClosedImmersion g := normalized_coordinates_closed k' a i hi (hgen i)
  have hV : IsOpenImmersion (V.f i) := by
    exact inferInstanceAs (IsOpenImmersion
      (Proj.awayι (PolyGrade K σ) (MvPolynomial.X i) (poly_X_mem i) (by decide)))
  have H : IsPullback g U.ι (V.f i) (sectionsMorphism k s hcover) := by
    apply @IsOpenImmersion.isPullback _ _ _ _ g U.ι (V.f i)
      (sectionsMorphism k s hcover) (inferInstanceAs (IsOpenImmersion U.ι)) hV
    · exact (sectionsMorphism_local k s hcover i).trans (Category.assoc _ _ _).symm
    · change _ ⁻¹ᵁ (Proj.awayι (homogeneousSubmodule σ K) (MvPolynomial.X i) _ _).opensRange = _
      erw [Proj.opensRange_awayι, sectionsMorphism_preimage, Scheme.Opens.opensRange_ι]
  change IsClosedImmersion (pullback.snd (sectionsMorphism k s hcover) (V.f i))
  have hcomp : IsClosedImmersion (H.flip.isoPullback.inv ≫ g) :=
    @IsClosedImmersion.comp _ _ _ _ _
      (inferInstanceAs (IsClosedImmersion H.flip.isoPullback.inv)) hg
  exact H.flip.isoPullback_inv_snd ▸ hcomp

end

section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace MvPolynomial
open HomogeneousLocalization PiExponentSeshadri.Frames
open scoped AlgebraicGeometry
variable {K R σ : Type u} [CommRing K] [CommRing R]
attribute [local instance] MvPolynomial.gradedAlgebra

lemma normalized_eval₂_of_evalAway (k : K →+* R) (a : σ → R) (i : σ) (hi : a i = 1)
    (h : Function.Surjective (evalAway (𝒜 := homogeneousSubmodule σ K)
      (eval₂Hom k a) (MvPolynomial.X i)
        (by simpa only [eval₂Hom_X', hi] using (isUnit_one : IsUnit (1 : R))))) :
    Function.Surjective (eval₂Hom k a) := by
  intro r
  obtain ⟨x, hx⟩ := h r
  obtain ⟨n, q, hq, rfl⟩ := Away.mk_surjective (homogeneousSubmodule σ K)
    (isHomogeneous_X K i) x
  refine ⟨q, ?_⟩
  have he := evalAway_mk_clear (eval₂Hom k a) (isHomogeneous_X K i)
    (by simpa only [eval₂Hom_X', hi] using (isUnit_one : IsUnit (1 : R))) n q hq
  simpa only [hx, eval₂Hom_X', hi, one_pow, mul_one] using he.symm

lemma affine_evaluation_surjective {Y : Scheme.{u}} (f : R →+* Γ(Y, ⊤))
    [IsClosedImmersion (Y.toSpecΓ ≫ Spec.map (CommRingCat.ofHom f))] :
    Function.Surjective f := by
  let g := Y.toSpecΓ ≫ Spec.map (CommRingCat.ofHom f)
  have hg := (IsClosedImmersion.isAffine_surjective_of_isAffine g).2
  have hEq : (Scheme.ΓSpecIso (CommRingCat.of R)).inv ≫ g.appTop = CommRingCat.ofHom f := by
    simp only [g, Scheme.Hom.comp_appTop, Scheme.toSpecΓ_appTop,
      ← Scheme.ΓSpecIso_inv_naturality_assoc, Iso.inv_hom_id, Category.comp_id]
  have hh := hg.comp (ConcreteCategory.bijective_of_isIso
    (Scheme.ΓSpecIso (CommRingCat.of R)).inv).surjective
  change Function.Surjective ((Scheme.ΓSpecIso (CommRingCat.of R)).inv ≫ g.appTop).hom at hh
  simpa only [hEq, CommRingCat.hom_ofHom] using hh

theorem sectionsMorphism_chart_generators {X : Scheme.{u}} {M : X.Modules}
    (k : K →+* Γ(X, ⊤)) (s : σ → (O X ⟶ M))
    (hs : (⨆ i, SectionOpens.isoOpen (s i)) = ⊤)
    [IsClosedImmersion (sectionsMorphism k s hs)] (i : σ) :
    IsAffine (SectionOpens.isoOpen (s i)).toScheme ∧ Function.Surjective
      (eval₂Hom ((SectionOpens.isoOpen (s i)).ι.appTop.hom.comp k)
        (fun j => coefficient (sectionFrame (s i))
          (restrictSection (SectionOpens.isoOpen (s i)).ι (s j)))) := by
  let V := reindexCoordinateCover (K := K) (σ := σ)
  let U := SectionOpens.isoOpen (s i)
  let k' := U.ι.appTop.hom.comp k
  let a : σ → Γ(U.toScheme, ⊤) := fun j => coefficient (sectionFrame (s i)) (restrictSection U.ι (s j))
  have hi : a i = 1 := sectionFrame_normalized (s i)
  let f := evalAway (𝒜 := homogeneousSubmodule σ K) (eval₂Hom k' a) (MvPolynomial.X i)
    (by simpa only [eval₂Hom_X', hi] using (isUnit_one : IsUnit (1 : Γ(U.toScheme, ⊤))))
  let g : U.toScheme ⟶ Spec (CommRingCat.of
      (HomogeneousLocalization.Away (homogeneousSubmodule σ K) (MvPolynomial.X i))) :=
    U.toScheme.toSpecΓ ≫ Spec.map (CommRingCat.ofHom f)
  have hV : IsOpenImmersion (V.f i) := by
    exact inferInstanceAs (IsOpenImmersion
      (Proj.awayι (PolyGrade K σ) (MvPolynomial.X i) (poly_X_mem i) (by decide)))
  have H : IsPullback g U.ι (V.f i) (sectionsMorphism k s hs) := by
    apply @IsOpenImmersion.isPullback _ _ _ _ g U.ι (V.f i)
      (sectionsMorphism k s hs) (inferInstanceAs (IsOpenImmersion U.ι)) hV
    · exact (sectionsMorphism_local k s hs i).trans (Category.assoc _ _ _).symm
    · change _ ⁻¹ᵁ (Proj.awayι (homogeneousSubmodule σ K) (MvPolynomial.X i) _ _).opensRange = _
      erw [Proj.opensRange_awayι, sectionsMorphism_preimage, Scheme.Opens.opensRange_ι]
  have hg : IsClosedImmersion g :=
    MorphismProperty.of_isPullback H.flip
      (inferInstanceAs (IsClosedImmersion (sectionsMorphism k s hs)))
  refine ⟨(IsClosedImmersion.isAffine_surjective_of_isAffine g).1, ?_⟩
  exact normalized_eval₂_of_evalAway k' a i hi (@affine_evaluation_surjective _ _ U.toScheme f hg)

end

open AlgebraicGeometry CategoryTheory TopologicalSpace MvPolynomial
open PiExponentSeshadri.Frames
open scoped AlgebraicGeometry
variable {K σ τ : Type u} [CommRing K] {X : Scheme.{u}} {M : X.Modules}
attribute [local instance] MvPolynomial.gradedAlgebra

lemma eval₂_surjective_reindex {R : Type u} [CommRing R] (k : K →+* R)
    (a : σ → R) (e : τ ≃ σ) (h : Function.Surjective (eval₂Hom k a)) :
    Function.Surjective (eval₂Hom k (a ∘ e)) := by
  intro r
  obtain ⟨p, hp⟩ := h r
  refine ⟨rename e.symm p, ?_⟩
  change eval₂ k (a ∘ e) (rename e.symm p) = r
  rw [MvPolynomial.eval₂_rename]
  change eval₂ k a p = r at hp
  simpa only [Function.comp_assoc, Equiv.self_comp_symm, Function.comp_id] using hp

theorem sectionsMorphism_reindex_closed (k : K →+* Γ(X, ⊤))
    (s : σ → (O X ⟶ M)) (hs : (⨆ i, SectionOpens.isoOpen (s i)) = ⊤)
    [IsClosedImmersion (sectionsMorphism k s hs)] (e : τ ≃ σ)
    (ht : (⨆ i, SectionOpens.isoOpen (s (e i))) = ⊤) :
    IsClosedImmersion (sectionsMorphism k (s ∘ e) ht) := by
  apply sectionsMorphism_isClosedImmersion
  · intro i
    exact (sectionsMorphism_chart_generators k s hs (e i)).1
  · intro i
    let U := SectionOpens.isoOpen (s (e i))
    let k' : K →+* Γ(U.toScheme, ⊤) := U.ι.appTop.hom.comp k
    let a : σ → Γ(U.toScheme, ⊤) := fun j =>
      coefficient (sectionFrame (s (e i))) (restrictSection U.ι (s j))
    have h : Function.Surjective (eval₂Hom k' a) :=
      (sectionsMorphism_chart_generators k s hs (e i)).2
    change Function.Surjective (eval₂Hom k' (a ∘ e))
    exact eval₂_surjective_reindex k' a e h

end PiExponentSeshadri.Projective

end

end OAI
end Source0643

-- Source: OAI/NumberTheory/PiExponent/Ampleness/AmpleFiniteProjectiveEmbedding.lean
section Source0644
/-
Modification notice for the LogTwo project.
Derived from openai/math (Apache-2.0), revision adc7f1241b42e322a6451854ab7e4b4c146bf78a.
Original source: lean/OAI/NumberTheory/PiExponent/Ampleness/AmpleFiniteProjectiveEmbedding.lean
Changes: Convert module/import declarations to the Lean 4.34 public module format.
See ../THIRD_PARTY_NOTICES.txt for provenance and the recorded changes.
-/

namespace OAI

namespace PiExponent.NumericalAmpleness
noncomputable section
open AlgebraicGeometry CategoryTheory TopologicalSpace
open PiExponentSeshadri.Geometry PiExponentSeshadri.Projective
open PiExponent.ProjectiveO1
variable {X : Scheme.{0}}

theorem ample_finite_projective_embedding [Nonempty X]
    (p : X ⟶ Spec (CommRingCat.of ℂ)) [IsProper p]
    (H : LineBundle X) (hH : H.IsAmple) :
    ∃ r : ℕ, ∃ i : X ⟶ projectiveSpace ℂ (Fin (r+1)),
      IsClosedImmersion i ∧ i ≫ polynomialProjectiveProjection ℂ (Fin (r+1)) = p := by
  classical
  let : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian p
  let : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace p
  let : IsNoetherian X := {}
  obtain ⟨n, _, σ, hσ, s, hs, hc⟩ := H.ample_projective_sections_noetherian p hH
  let : Fintype σ := hσ
  have hne : Nonempty σ := by
    obtain ⟨x⟩ : Nonempty X := inferInstance
    have hx : x ∈ ⨆ i, PiExponentSeshadri.SectionOpens.isoOpen (s i) := by
      rw [hs]
      trivial
    obtain ⟨i, _⟩ := Opens.mem_iSup.mp hx
    exact ⟨i⟩
  have hpos : 0 < Fintype.card σ := Fintype.card_pos_iff.mpr hne
  obtain ⟨r, hr⟩ := Nat.exists_eq_succ_of_ne_zero (ne_of_gt hpos)
  let e : Fin (r+1) ≃ σ := ((Fintype.equivFin σ).trans (finCongr hr)).symm
  let t : Fin (r+1) → GlobalSections X (modulePow X H.sheaf n) := s ∘ e
  have ht : (⨆ i, PiExponentSeshadri.SectionOpens.isoOpen (t i)) = ⊤ :=
    (e.iSup_comp (g := fun j => PiExponentSeshadri.SectionOpens.isoOpen (s j))).trans hs
  let k := baseScalars p
  let : IsClosedImmersion (sectionsMorphism k s hs) := hc
  let i : X ⟶ projectiveSpace ℂ (Fin (r+1)) := sectionsMorphism k t ht
  have hclosed : IsClosedImmersion i := sectionsMorphism_reindex_closed k s hs e ht
  refine ⟨r, i, hclosed, ?_⟩
  rw [← AmpleCohomologyFinite.projectiveBase_eq_polynomialProjectiveProjection]
  exact (sectionsMorphism_over k t ht).trans (toSpec_scalarMap p)

end
end PiExponent.NumericalAmpleness

end OAI
end Source0644

-- Source: OAI/NumberTheory/PiExponent/Approximation/ClosedRestrictionTensor.lean
section Source0645
/-
Modification notice for the LogTwo project.
Derived from openai/math (Apache-2.0), revision adc7f1241b42e322a6451854ab7e4b4c146bf78a.
Original source: lean/OAI/NumberTheory/PiExponent/Approximation/ClosedRestrictionTensor.lean
Changes: Convert module/import declarations to the Lean 4.34 public module format.
See ../THIRD_PARTY_NOTICES.txt for provenance and the recorded changes.
-/

namespace OAI

namespace PiExponent.ClosedRestrictionTensor
noncomputable section
open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite
open PiExponentSeshadri.Geometry PiExponentSeshadri.Frames PiExponentSeshadri.TensorPure

lemma tensor_map_pure_val {Z : Scheme.{0}} {M N P Q : Z.Modules}
    (a : M ⟶ P) (b : N ⟶ Q) (U : Z.Opens)
    (m : M.val.obj (op U)) (n : N.val.obj (op U)) :
    (moduleTensorMap a b).val.app (op U) (pure M N U m n) =
      pure P Q U (a.val.app (op U) m) (b.val.app (op U) n) :=
  map_pure a b U m n

lemma tensor_comm_pure_val {Z : Scheme.{0}} (M N : Z.Modules) (U : Z.Opens)
    (m : M.val.obj (op U)) (n : N.val.obj (op U)) :
    (moduleTensorComm M N).hom.val.app (op U) (pure M N U m n) =
      pure N M U n m := moduleTensorComm_pure M N U m n

lemma projection_hom_pure_val {X Y : Scheme.{0}} (f : X ⟶ Y)
    (M : X.Modules) (L : Y.Modules) (U : Y.Opens)
    (m : M.val.obj (op (f ⁻¹ᵁ U))) (s : L.val.obj (op U)) :
    (ProjectionFormula.hom f M L).val.app (op U)
      (pure ((Scheme.Modules.pushforward f).obj M) L U m s) =
      pure M ((Scheme.Modules.pullback f).obj L) (f ⁻¹ᵁ U) m
        (((Scheme.Modules.pullbackPushforwardAdjunction f).unit.app L).val.app (op U) s) :=
  ProjectionFormula.hom_pure f M L U m s

lemma pushforward_hom_pure_val {X Y : Scheme.{0}} (f : X ⟶ Y)
    (M N : X.Modules) (U : Y.Opens)
    (m : M.val.obj (op (f ⁻¹ᵁ U))) (n : N.val.obj (op (f ⁻¹ᵁ U))) :
    (PiExponentSeshadri.PushforwardTensor.hom f M N).val.app (op U)
      (pure ((Scheme.Modules.pushforward f).obj M) ((Scheme.Modules.pushforward f).obj N) U m n) =
      pure M N (f ⁻¹ᵁ U) m n :=
  PiExponentSeshadri.PushforwardTensor.hom_pure f M N U m n

variable {X Y : Scheme.{0}} (f : X ⟶ Y) (L : LineBundle Y)

def powerProjectionIso (n : ℕ) :
    (moduleTwistFunctor L n).obj ((Scheme.Modules.pushforward f).obj (O X)) ≅
      (Scheme.Modules.pushforward f).obj ((L.pullback f).pow n).sheaf :=
  (ProjectionFormula.twistIso f (O X) L n).symm ≪≫
    (Scheme.Modules.pushforward f).mapIso (moduleTwistUnitIso (L.pullback f) n)

def powerUnit (n : ℕ) : (L.pow n).sheaf ⟶
    (Scheme.Modules.pushforward f).obj ((L.pullback f).pow n).sheaf :=
  (Scheme.Modules.pullbackPushforwardAdjunction f).unit.app (L.pow n).sheaf ≫
    (Scheme.Modules.pushforward f).map (PiExponentSeshadri.PullbackTensor.powIso f L n).hom

lemma powerProjectionIso_succ_pure (n : ℕ) (U : Y.Opens)
    (m : ((moduleTwistFunctor L n).obj ((Scheme.Modules.pushforward f).obj (O X))).val.obj (op U))
    (s : L.sheaf.val.obj (op U)) :
    (powerProjectionIso f L (n+1)).hom.val.app (op U)
      (pure _ L.sheaf U m s) =
      pure (L.pullback f).sheaf ((L.pullback f).pow n).sheaf (f ⁻¹ᵁ U)
        (((Scheme.Modules.pullbackPushforwardAdjunction f).unit.app L.sheaf).val.app (op U) s)
        ((powerProjectionIso f L n).hom.val.app (op U) m) := by
  change (moduleTwistUnitIso (L.pullback f) (n+1)).hom.val.app (op (f ⁻¹ᵁ U))
    ((ProjectionFormula.hom f ((moduleTwistFunctor (L.pullback f) n).obj (O X)) L.sheaf).val.app (op U)
      ((moduleTensorMap (ProjectionFormula.twistIso f (O X) L n).inv (𝟙 L.sheaf)).val.app (op U)
        (pure _ L.sheaf U m s))) = _
  rw [tensor_map_pure_val]
  change (moduleTensorComm ((L.pullback f).pow n).sheaf (L.pullback f).sheaf).hom.val.app (op (f ⁻¹ᵁ U))
    ((moduleTensorMap (moduleTwistUnitIso (L.pullback f) n).hom (𝟙 (L.pullback f).sheaf)).val.app (op (f ⁻¹ᵁ U))
      ((ProjectionFormula.hom f ((moduleTwistFunctor (L.pullback f) n).obj (O X)) L.sheaf).val.app (op U)
        (pure _ L.sheaf U ((ProjectionFormula.twistIso f (O X) L n).inv.val.app (op U) m) s))) = _
  erw [projection_hom_pure_val f ((moduleTwistFunctor (L.pullback f) n).obj (O X))
    L.sheaf U ((ProjectionFormula.twistIso f (O X) L n).inv.val.app (op U) m) s]
  have ht := tensor_map_pure_val (Z := X) (moduleTwistUnitIso (L.pullback f) n).hom
    (𝟙 (L.pullback f).sheaf) (f ⁻¹ᵁ U)
    ((ProjectionFormula.twistIso f (O X) L n).inv.val.app (op U) m)
    (((Scheme.Modules.pullbackPushforwardAdjunction f).unit.app L.sheaf).val.app (op U) s)
  exact (congrArg (fun r => (moduleTensorComm ((L.pullback f).pow n).sheaf
    (L.pullback f).sheaf).hom.val.app (op (f ⁻¹ᵁ U)) r) ht).trans
      (tensor_comm_pure_val _ _ _ _ _)

lemma powerUnit_succ_pure (n : ℕ) (U : Y.Opens)
    (s : L.sheaf.val.obj (op U)) (m : (L.pow n).sheaf.val.obj (op U)) :
    (powerUnit f L (n+1)).val.app (op U) (pure L.sheaf (L.pow n).sheaf U s m) =
      pure (L.pullback f).sheaf ((L.pullback f).pow n).sheaf (f ⁻¹ᵁ U)
        (((Scheme.Modules.pullbackPushforwardAdjunction f).unit.app L.sheaf).val.app (op U) s)
        ((powerUnit f L n).val.app (op U) m) := by
  have h := PiExponentSeshadri.PullbackTensor.unit_hom f L.sheaf (L.pow n).sheaf
  have hp := congrArg (fun q => q.val.app (op U) (pure L.sheaf (L.pow n).sheaf U s m)) h
  change (PiExponentSeshadri.PullbackTensor.hom f L.sheaf (L.pow n).sheaf).val.app (op (f ⁻¹ᵁ U))
      (((Scheme.Modules.pullbackPushforwardAdjunction f).unit.app
        (moduleTensor Y L.sheaf (L.pow n).sheaf)).val.app (op U) (pure L.sheaf (L.pow n).sheaf U s m)) =
    (PiExponentSeshadri.PushforwardTensor.hom f _ _).val.app (op U)
      ((moduleTensorMap ((Scheme.Modules.pullbackPushforwardAdjunction f).unit.app L.sheaf)
        ((Scheme.Modules.pullbackPushforwardAdjunction f).unit.app (L.pow n).sheaf)).val.app (op U)
        (pure L.sheaf (L.pow n).sheaf U s m)) at hp
  have hm := tensor_map_pure_val (Z := Y)
    ((Scheme.Modules.pullbackPushforwardAdjunction f).unit.app L.sheaf)
    ((Scheme.Modules.pullbackPushforwardAdjunction f).unit.app (L.pow n).sheaf) U s m
  have hv := pushforward_hom_pure_val f ((Scheme.Modules.pullback f).obj L.sheaf)
    ((Scheme.Modules.pullback f).obj (L.pow n).sheaf) U
    (((Scheme.Modules.pullbackPushforwardAdjunction f).unit.app L.sheaf).val.app (op U) s)
    (((Scheme.Modules.pullbackPushforwardAdjunction f).unit.app (L.pow n).sheaf).val.app (op U) m)
  have hp' := hp.trans ((congrArg (fun r => (PiExponentSeshadri.PushforwardTensor.hom f
    ((Scheme.Modules.pullback f).obj L.sheaf) ((Scheme.Modules.pullback f).obj (L.pow n).sheaf)).val.app
      (op U) r) hm).trans hv)
  change (moduleTensorMap (𝟙 (L.pullback f).sheaf) (PiExponentSeshadri.PullbackTensor.powIso f L n).hom).app
    (f ⁻¹ᵁ U)
    ((PiExponentSeshadri.PullbackTensor.hom f L.sheaf (L.pow n).sheaf).val.app (op (f ⁻¹ᵁ U))
      (((Scheme.Modules.pullbackPushforwardAdjunction f).unit.app
        (moduleTensor Y L.sheaf (L.pow n).sheaf)).val.app (op U) (pure L.sheaf (L.pow n).sheaf U s m))) = _
  exact (congrArg (fun r => (moduleTensorMap (𝟙 (L.pullback f).sheaf)
    (PiExponentSeshadri.PullbackTensor.powIso f L n).hom).val.app (op (f ⁻¹ᵁ U)) r) hp').trans
      (tensor_map_pure_val (Z := X) (𝟙 (L.pullback f).sheaf)
        (PiExponentSeshadri.PullbackTensor.powIso f L n).hom _ _ _)

theorem twist_structureMap_power (n : ℕ) :
    (moduleTwistFunctor L n).map (PiExponentSeshadri.IdealModule.structureMap f) ≫
        (powerProjectionIso f L n).hom =
      (moduleTwistUnitIso L n).hom ≫ powerUnit f L n := by
  induction n with
  | zero =>
    change PiExponentSeshadri.IdealModule.structureMap f =
      (Scheme.Modules.pullbackPushforwardAdjunction f).unit.app (O Y) ≫
        (Scheme.Modules.pushforward f).map (pullbackUnitIso f).hom
    exact (pullbackUnit_adjunction f).symm
  | succ n ih =>
    apply PiExponentSeshadri.TensorPure.hom_ext
    intro U m s
    change (powerProjectionIso f L (n+1)).hom.val.app (op U)
      ((moduleTensorMap ((moduleTwistFunctor L n).map (PiExponentSeshadri.IdealModule.structureMap f))
        (𝟙 L.sheaf)).val.app (op U) (pure _ L.sheaf U m s)) =
      (powerUnit f L (n+1)).val.app (op U)
        ((moduleTensorComm (L.pow n).sheaf L.sheaf).hom.val.app (op U)
          ((moduleTensorMap (moduleTwistUnitIso L n).hom (𝟙 L.sheaf)).val.app (op U)
            (pure _ L.sheaf U m s)))
    have h1 := tensor_map_pure_val (Z := Y)
      ((moduleTwistFunctor L n).map (PiExponentSeshadri.IdealModule.structureMap f)) (𝟙 L.sheaf) U m s
    have h2 := powerProjectionIso_succ_pure f L n U
      (((moduleTwistFunctor L n).map (PiExponentSeshadri.IdealModule.structureMap f)).val.app (op U) m) s
    have h3 := tensor_map_pure_val (Z := Y) (moduleTwistUnitIso L n).hom (𝟙 L.sheaf) U m s
    have h4 := tensor_comm_pure_val (L.pow n).sheaf L.sheaf U
      ((moduleTwistUnitIso L n).hom.val.app (op U) m) s
    have h5 := powerUnit_succ_pure f L n U s ((moduleTwistUnitIso L n).hom.val.app (op U) m)
    have hleft := (congrArg (fun r => (powerProjectionIso f L (n+1)).hom.val.app (op U) r) h1).trans h2
    have hright := (congrArg (fun r => (powerUnit f L (n+1)).val.app (op U) r)
      ((congrArg (fun r => (moduleTensorComm (L.pow n).sheaf L.sheaf).hom.val.app (op U) r) h3).trans h4)).trans h5
    exact hleft.trans ((congrArg (fun r => pure (L.pullback f).sheaf ((L.pullback f).pow n).sheaf
      (f ⁻¹ᵁ U) (((Scheme.Modules.pullbackPushforwardAdjunction f).unit.app L.sheaf).val.app (op U) s) r)
      (congrArg (fun q => q.val.app (op U) m) ih)).trans hright.symm)

theorem power_restriction_eq (n : ℕ) :
    (moduleTwistUnitIso L n).inv ≫
      (moduleTwistFunctor L n).map (PiExponentSeshadri.IdealModule.structureMap f) ≫
      (ProjectionFormula.twistIso f (O X) L n).inv ≫
      (Scheme.Modules.pushforward f).map (moduleTwistUnitIso (L.pullback f) n).hom =
    (Scheme.Modules.pullbackPushforwardAdjunction f).unit.app (L.pow n).sheaf ≫
      (Scheme.Modules.pushforward f).map (PiExponentSeshadri.PullbackTensor.powIso f L n).hom := by
  change (moduleTwistUnitIso L n).inv ≫
    ((moduleTwistFunctor L n).map (PiExponentSeshadri.IdealModule.structureMap f) ≫
      (powerProjectionIso f L n).hom) = powerUnit f L n
  erw [twist_structureMap_power, Iso.inv_hom_id_assoc]

theorem push_pullbackSection {M : Y.Modules} (s : O Y ⟶ M) :
    PiExponentSeshadri.IdealModule.structureMap f ≫
      (Scheme.Modules.pushforward f).map (pullbackSection f s) =
      s ≫ (Scheme.Modules.pullbackPushforwardAdjunction f).unit.app M := by
  have hu : PiExponentSeshadri.IdealModule.structureMap f =
      (Scheme.Modules.pullbackPushforwardAdjunction f).unit.app (O Y) ≫
        (Scheme.Modules.pushforward f).map (pullbackUnitIso f).hom :=
    (pullbackUnit_adjunction f).symm
  let F := Scheme.Modules.pushforward f
  let P := Scheme.Modules.pullback f
  let e := pullbackUnitIso f
  have h := (F.map_comp e.hom (e.inv ≫ P.map s)).symm.trans
    (congrArg F.map (e.hom_inv_id_assoc (P.map s)))
  calc
    _ = ((Scheme.Modules.pullbackPushforwardAdjunction f).unit.app (O Y) ≫
        F.map e.hom) ≫ F.map (e.inv ≫ P.map s) :=
      congrArg (fun q : O Y ⟶ F.obj (O X) => q ≫ F.map (pullbackSection f s)) hu
    _ = (Scheme.Modules.pullbackPushforwardAdjunction f).unit.app (O Y) ≫ F.map (P.map s) :=
      (Category.assoc _ _ _).trans
        (congrArg (fun q => (Scheme.Modules.pullbackPushforwardAdjunction f).unit.app (O Y) ≫ q) h)
    _ = _ := ((Scheme.Modules.pullbackPushforwardAdjunction f).unit.naturality s).symm

theorem section_restriction_eq (n : ℕ) (s : O Y ⟶ (L.pow n).sheaf) :
    s ≫ (moduleTwistUnitIso L n).inv ≫
      (moduleTwistFunctor L n).map (PiExponentSeshadri.IdealModule.structureMap f) ≫
      (ProjectionFormula.twistIso f (O X) L n).inv ≫
      (Scheme.Modules.pushforward f).map (moduleTwistUnitIso (L.pullback f) n).hom =
    PiExponentSeshadri.IdealModule.structureMap f ≫
      (Scheme.Modules.pushforward f).map (pullbackPowerSection L f n s) := by
  erw [power_restriction_eq]
  symm
  simp only [pullbackPowerSection]
  erw [(Scheme.Modules.pushforward f).map_comp (pullbackSection f s)
    (PiExponentSeshadri.PullbackTensor.powIso f L n).hom, ← Category.assoc,
    push_pullbackSection f s, Category.assoc]

end
end PiExponent.ClosedRestrictionTensor

end OAI
end Source0645

-- Source: OAI/NumberTheory/PiExponent/Approximation/AffineThickeningCriterion.lean
section Source0646
/-
Modification notice for the LogTwo project.
Derived from openai/math (Apache-2.0), revision adc7f1241b42e322a6451854ab7e4b4c146bf78a.
Original source: lean/OAI/NumberTheory/PiExponent/Approximation/AffineThickeningCriterion.lean
Changes: Convert module/import declarations to the Lean 4.34 public module format.
See ../THIRD_PARTY_NOTICES.txt for provenance and the recorded changes.
-/

namespace OAI

namespace PiExponentSeshadri.Geometry
noncomputable section
open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite

variable {X Y : Scheme}

theorem isUnit_of_basicOpen_eq_top (r : Γ(X,⊤)) (hr : X.basicOpen r = ⊤) :
    IsUnit r := by
  apply X.toRingedSpace.isUnit_of_isUnit_germ ⊤ r
  intro x hx
  exact (X.mem_basicOpen_top r x).mp (by rw [hr]; trivial)

theorem appTop_reflects_isUnit (f : Y ⟶ X) (hf : Function.Surjective f)
    (r : Γ(X,⊤)) (hr : IsUnit (f.appTop r)) : IsUnit r := by
  apply isUnit_of_basicOpen_eq_top r
  apply top_unique
  intro x hx
  obtain ⟨y, rfl⟩ := hf x
  have hy : y ∈ f ⁻¹ᵁ X.basicOpen r := by
    rw [Scheme.preimage_basicOpen_top, Y.basicOpen_of_isUnit hr]
    trivial
  exact hy

theorem isAffineOpen_basicOpen_of_le (r : Γ(X,⊤)) (U : X.Opens)
    (hU : IsAffineOpen U) (hr : X.basicOpen r ≤ U) :
    IsAffineOpen (X.basicOpen r) := by
  have h := hU.basicOpen (X.presheaf.map (homOfLE (show U ≤ ⊤ from le_top)).op r)
  rwa [Scheme.basicOpen_res, inf_eq_right.mpr hr] at h

theorem isAffine_of_surjective_appTop (f : Y ⟶ X) [IsAffine Y]
    (hf : Function.Surjective f) (hΓ : Function.Surjective f.appTop) : IsAffine X := by
  let S : Set Γ(X,⊤) := {r | IsAffineOpen (X.basicOpen r)}
  have hcover : (⊤ : Y.Opens) ≤ ⨆ a : (f.appTop '' S), Y.basicOpen a.1 := by
    intro y hy
    obtain ⟨U, hU, hyU, -⟩ := exists_isAffineOpen_mem_and_subset
      (show f y ∈ (⊤ : X.Opens) from trivial)
    obtain ⟨a, haU, hya⟩ := (isAffineOpen_top Y).exists_basicOpen_le
      (⟨y, hyU⟩ : f ⁻¹ᵁ U) (by trivial)
    obtain ⟨r, hr⟩ := hΓ a
    have hrU : X.basicOpen r ≤ U := by
      intro x hx
      obtain ⟨z, rfl⟩ := hf x
      apply haU
      have hz : z ∈ f ⁻¹ᵁ X.basicOpen r := hx
      rwa [Scheme.preimage_basicOpen_top, hr] at hz
    have hrS : r ∈ S := isAffineOpen_basicOpen_of_le r U hU hrU
    exact Opens.mem_iSup.mpr ⟨⟨a, r, hrS, hr⟩, hya⟩
  have hmap : Ideal.map f.appTop.hom (Ideal.span S) = ⊤ := by
    rw [Ideal.map_span]
    exact (isAffineOpen_top Y).self_le_iSup_basicOpen_iff.mp hcover
  obtain ⟨r, hrS, hr⟩ := (Ideal.mem_map_iff_of_surjective f.appTop.hom hΓ).mp
    (show (1 : Γ(Y,⊤)) ∈ Ideal.map f.appTop.hom (Ideal.span S) by rw [hmap]; trivial)
  have hunit : IsUnit r := appTop_reflects_isUnit f hf r (hr ▸ isUnit_one)
  exact isAffine_of_isAffineOpen_basicOpen S
    ((Ideal.span S).eq_top_of_isUnit_mem hrS hunit) (fun r hr => hr)

end
end PiExponentSeshadri.Geometry

end OAI
end Source0646

-- Source: OAI/NumberTheory/PiExponent/Approximation/ClosedThickeningSections.lean
section Source0647
/-
Modification notice for the LogTwo project.
Derived from openai/math (Apache-2.0), revision adc7f1241b42e322a6451854ab7e4b4c146bf78a.
Original source: lean/OAI/NumberTheory/PiExponent/Approximation/ClosedThickeningSections.lean
Changes: Convert module/import declarations to the Lean 4.34 public module format.
See ../THIRD_PARTY_NOTICES.txt for provenance and the recorded changes.
-/

namespace OAI

namespace PiExponentSeshadri.Geometry
noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian
open TopologicalSpace Opposite
open PiExponentSeshadri.Frames
variable {X Y : Scheme.{0}}
local instance (Z : Scheme.{0}) : HasExt.{1} Z.Modules := HasExt.standard _

theorem globalSections_surjective_of_ext_one_zero (S : ShortComplex X.Modules)
    (hS : S.ShortExact)
    (hzero : ∀ x : Abelian.Ext.{1} (structureSheaf X) S.X₁ 1, x = 0) :
    Function.Surjective (fun s : GlobalSections X S.X₂ => s ≫ S.g) := by
  intro s
  obtain ⟨a,ha⟩ := Ext.covariant_sequence_exact₃ (structureSheaf X) hS (Ext.mk₀ s)
    rfl (hzero _)
  refine ⟨Ext.homEquiv₀ a, ?_⟩
  apply (Ext.mk₀_bijective (structureSheaf X) S.X₃).injective
  rw [← Ext.mk₀_comp_mk₀, Ext.mk₀_homEquiv₀_apply]
  exact ha

theorem closed_appTop_surjective_of_ext_one_zero (i : Y ⟶ X) [IsClosedImmersion i]
    (hzero : ∀ x : Abelian.Ext.{1} (structureSheaf X) (IdealModule.idealModule i) 1, x = 0) :
    Function.Surjective i.appTop := by
  let P := (Scheme.Modules.pushforward i).obj (IdealModule.unit Y)
  let S := ShortComplex.mk (IdealModule.inclusion i) (IdealModule.structureMap i)
    (kernel.condition _)
  have hlift := globalSections_surjective_of_ext_one_zero S
    (IdealModule.closedSequence_exact i) hzero
  intro y
  let t : GlobalSections X P := (moduleSectionEquiv P).symm y
  obtain ⟨s, hs⟩ := hlift t
  refine ⟨s.app ⊤ (1 : Γ(X,⊤)), ?_⟩
  have he := congrArg (fun t : GlobalSections X P => t.app ⊤ (1 : Γ(X,⊤))) hs
  exact he.trans ((moduleSectionEquiv P).apply_symm_apply y)

theorem subscheme_surjective_of_fullSupport (I : X.IdealSheafData)
    (hI : I.support = ⊤) : Function.Surjective I.subschemeι := by
  apply Set.range_eq_univ.mp
  rw [I.range_subschemeι, hI]
  rfl

theorem isAffine_of_fullSupport_of_ideal_ext_one_zero (I : X.IdealSheafData)
    (hI : I.support = ⊤) [IsAffine I.subscheme]
    (hzero : ∀ x : Abelian.Ext.{1} (structureSheaf X) (IdealModule.closedModule I) 1, x = 0) :
    IsAffine X :=
  isAffine_of_surjective_appTop I.subschemeι (subscheme_surjective_of_fullSupport I hI)
    (closed_appTop_surjective_of_ext_one_zero I.subschemeι hzero)

end
end PiExponentSeshadri.Geometry

end OAI
end Source0647

-- Source: OAI/NumberTheory/PiExponent/Approximation/ClosedPowerSectionLifting.lean
section Source0648
/-
Modification notice for the LogTwo project.
Derived from openai/math (Apache-2.0), revision adc7f1241b42e322a6451854ab7e4b4c146bf78a.
Original source: lean/OAI/NumberTheory/PiExponent/Approximation/ClosedPowerSectionLifting.lean
Changes: Convert module/import declarations to the Lean 4.34 public module format.
See ../THIRD_PARTY_NOTICES.txt for provenance and the recorded changes.
-/

namespace OAI

namespace PiExponentSeshadri.Geometry
noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian
open PiExponentSeshadri.Frames
variable {X Y : Scheme.{0}}
local instance : HasExt.{1} X.Modules := HasExt.standard _

theorem pullbackPowerSection_surjective_of_ideal_ext_zero (i : Y ⟶ X)
    [IsClosedImmersion i] (L : LineBundle X) (n : ℕ)
    (hzero : ∀ x : Abelian.Ext.{1} (structureSheaf X)
      ((moduleTwistFunctor L n).obj (IdealModule.idealModule i)) 1, x = 0) :
    Function.Surjective (pullbackPowerSection L i n) := by
  let S := ShortComplex.mk (IdealModule.inclusion i) (IdealModule.structureMap i)
    (kernel.condition _)
  have hS := moduleTwistFunctor_shortExact L n S (IdealModule.closedSequence_exact i)
  have hsurj := globalSections_surjective_of_ext_one_zero (S.map (moduleTwistFunctor L n)) hS hzero
  intro σ
  let e := PiExponent.ClosedRestrictionTensor.powerProjectionIso i L n
  let b : GlobalSections X ((Scheme.Modules.pushforward i).obj ((L.pullback i).pow n).sheaf) :=
    IdealModule.structureMap i ≫ (Scheme.Modules.pushforward i).map σ
  obtain ⟨a,ha⟩ := hsurj (b ≫ e.inv)
  let t : GlobalSections X (L.pow n).sheaf := a ≫ (moduleTwistUnitIso L n).hom
  refine ⟨t, ?_⟩
  apply (PiExponent.ClosedImmersionSerreTransfer.globalHom_push_bijective i
    ((L.pullback i).pow n).sheaf).injective
  have ht := PiExponent.ClosedRestrictionTensor.section_restriction_eq i L n t
  change t ≫ (moduleTwistUnitIso L n).inv ≫
    (moduleTwistFunctor L n).map (IdealModule.structureMap i) ≫ e.hom =
      IdealModule.structureMap i ≫ (Scheme.Modules.pushforward i).map
        (pullbackPowerSection L i n t) at ht
  change IdealModule.structureMap i ≫ (Scheme.Modules.pushforward i).map
    (pullbackPowerSection L i n t) = b
  rw [← ht]
  dsimp only [t]
  erw [Category.assoc a (moduleTwistUnitIso L n).hom,
    (moduleTwistUnitIso L n).hom_inv_id_assoc]
  change (a ≫ (moduleTwistFunctor L n).map (IdealModule.structureMap i)) ≫ e.hom = b
  have ha' : a ≫ (moduleTwistFunctor L n).map (IdealModule.structureMap i) = b ≫ e.inv := ha
  exact (congrArg (fun z => z ≫ e.hom) ha').trans (by simp only [Category.assoc,
    Iso.inv_hom_id, Category.comp_id])

end
end PiExponentSeshadri.Geometry

end OAI
end Source0648

-- Source: OAI/NumberTheory/PiExponent/Approximation/ClosedSupportedSerre.lean
section Source0649
/-
Modification notice for the LogTwo project.
Derived from openai/math (Apache-2.0), revision adc7f1241b42e322a6451854ab7e4b4c146bf78a.
Original source: lean/OAI/NumberTheory/PiExponent/Approximation/ClosedSupportedSerre.lean
Changes: Convert module/import declarations to the Lean 4.34 public module format.
See ../THIRD_PARTY_NOTICES.txt for provenance and the recorded changes.
-/

namespace OAI

namespace PiExponentSeshadri.Geometry
noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian
variable {X Y : Scheme.{0}}
local instance (Z : Scheme.{0}) : HasExt.{1} Z.Modules := HasExt.standard _

theorem ext_zero_of_moduleIso {M N : X.Modules} (e : M ≅ N) (q : ℕ)
    (h : ∀ x : Abelian.Ext.{1} (structureSheaf X) N q, x = 0)
    (x : Abelian.Ext.{1} (structureSheaf X) M q) : x = 0 := by
  let E := (extFunctorObj (structureSheaf X) q).mapIso e
  apply (ConcreteCategory.bijective_of_isIso E.hom).injective
  change E.hom x = E.hom 0
  rw [map_zero]
  exact h (E.hom x)

theorem affine_closed_pushforward_ext_zero (i : Y ⟶ X) [IsClosedImmersion i]
    [IsAffine Y] [IsNoetherian Y] (M : X.Modules) (N : Y.Modules)
    [N.IsQuasicoherent] (e : M ≅ (Scheme.Modules.pushforward i).obj N)
    (q : ℕ) (hq : 0 < q) (x : Abelian.Ext.{1} (structureSheaf X) M q) : x = 0 := by
  apply ext_zero_of_moduleIso e q _ x
  apply (PiExponent.ClosedImmersionSerreTransfer.ext_zero_iff i N q).mp
  obtain ⟨k,rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_zero_of_lt hq)
  exact AffineSchemeCohomology.affine_ext_zero Y N k

theorem eventual_twist_ext_zero_of_closed_pushforward
    {R : Type} [CommRing R] [IsNoetherianRing R]
    (p : X ⟶ Spec (CommRingCat.of R)) [IsProper p]
    (i : Y ⟶ X) [IsClosedImmersion i]
    (L : LineBundle X) (hL : (L.pullback i).IsAmple)
    (M : X.Modules) (N : Y.Modules) [N.IsFinitePresentation]
    (e : M ≅ (Scheme.Modules.pushforward i).obj N) :
    ∃ B, ∀ n, B ≤ n → ∀ q, 0 < q →
      ∀ x : Abelian.Ext.{1} (structureSheaf X) ((moduleTwistFunctor L n).obj M) q, x = 0 := by
  obtain ⟨B,hB⟩ := PiExponent.GeometrySupport.NoetherianAmpleSerreVanishing.ample_serre_vanishing
    (i ≫ p) (L.pullback i) hL N
  refine ⟨B, fun n hn q hq x => ?_⟩
  let E := (moduleTwistFunctor L n).mapIso e ≪≫
    (PiExponent.ProjectionFormula.twistIso i N L n).symm
  apply ext_zero_of_moduleIso E q _ x
  exact (PiExponent.ClosedImmersionSerreTransfer.ext_zero_iff i
    ((moduleTwistFunctor (L.pullback i) n).obj N) q).mp (hB n hn q hq)

end
end PiExponentSeshadri.Geometry

end OAI
end Source0649

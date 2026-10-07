/- Generated rc4 checkpoint for LogTwo.
Modified from the reduced edition: new imports, separate module compilation,
and synchronous elaboration. Original source blocks and notices are retained.
See ../../../THIRD_PARTY_NOTICES.txt and ../../reduction.json.
-/
module
public import LogTwoCheckpoints.Part000
public import LogTwoCheckpoints.Part001
public import LogTwoCheckpoints.Part004
public import LogTwoCheckpoints.Part011
public import LogTwoCheckpoints.Part012
public import LogTwoCheckpoints.Part013
public import LogTwoCheckpoints.Part014
public import LogTwoCheckpoints.Part015
public import LogTwoCheckpoints.Part016
public import LogTwoCheckpoints.Part017
public import LogTwoCheckpoints.Part020
public import LogTwoCheckpoints.Part022
public import LogTwoCheckpoints.Part023
public import LogTwoCheckpoints.Part024
public import LogTwoCheckpoints.Part025
public import LogTwoCheckpoints.Part026
public import LogTwoCheckpoints.Part029
public import LogTwoCheckpoints.Part030
public import LogTwoCheckpoints.Part032
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Quasicoherent
public import Mathlib.Algebra.MvPolynomial.Nilpotent
public import Mathlib.AlgebraicGeometry.IdealSheaf.Functorial
public import Mathlib.AlgebraicGeometry.Modules.Sheaf
public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Basic
public import Mathlib.Analysis.Complex.Polynomial.Basic
public import Mathlib.Data.Opposite
@[expose] public section
set_option Elab.async false

-- Source: LogTwo/Geometry/MatrixJetSurjectivity.lean
section Source0825
/-
Modification notice for the LogTwo project.
Adapted from openai/math (Apache-2.0), revision adc7f1241b42e322a6451854ab7e4b4c146bf78a.
Changes: Adapt the blowup/affine-jet strategy to the varying Y-centers.
See ../THIRD_PARTY_NOTICES.txt for provenance and the recorded changes.
-/

/-! Eventual sheaf-jet surjectivity on the actual weighted compactification.
The ampleness input is discharged by the preceding uniform curve argument.
The polynomial degree bound and the determinant estimate are separate steps. -/
namespace LogTwo.Geometry.MatrixBlowup
open OAI PiExponent AlgebraicGeometry CategoryTheory
open PiExponentSeshadri.Geometry BlowupJetSurjectivity
open LogTwo.Interpolation LogTwo.Parameters LogTwo.Arithmetic
noncomputable section

/-- Tensor commutativity matches the proved bundle to the generic blowup API. -/
theorem blowupBundle_ample_of_interpolationBundle
    {m K : ℕ} (w : Weights m) (y : Fin K → ℂ)
    (a : Fin K → Fin m → ℂ) (T : Fin m → ℕ)
    (h : (interpolationBundle w y a T).IsAmple) :
    (blowupBundle (MatrixCompactification.centerIdeal w y a T) (hyperplane w)).IsAmple := by
  exact AmpleIso.isAmple_of_sheaf_iso (interpolationBundle w y a T)
    (blowupBundle (MatrixCompactification.centerIdeal w y a T) (hyperplane w))
    (moduleTensorComm (A w y a T).sheaf (J w y a T).sheaf) h

theorem chosenWeights_eventual_jetRestriction_surjective
    (n : ℕ) (hn : 1 ≤ n) (m : ℕ) (q : ℕ → ℕ) (hq : ∀ i, 2 ≤ q i)
    (hgrowth : ∀ i, i < m →
      denominatorSeparationFactor n m (chosenComparisonConstant n m) *
        (∏ j : Fin i, (ceilLogWeight (q j) : ℝ)) < (ceilLogWeight (q i) : ℝ)) :
    let w := chosenWeights n hn m (fun i => q i) (fun i => hq i)
    ∀ (y : Fin w.K → ℂ), (∀ j, y j ≠ 0) → Function.Injective y →
      ∀ (a : Fin w.K → Fin m → ℂ) (F : ℚ), 1 / w.theta < F →
      ∃ N, ∀ k, N ≤ k → Function.Surjective
        (jetRestriction (MatrixCompactification.centerIdeal w y a (truncationOrders w F))
          (hyperplane w) k) := by
  dsimp only
  intro y hy0 hy a F hF
  let w := chosenWeights n hn m (fun i => q i) (fun i => hq i)
  exact eventual_blowup_jetRestriction_surjective (MatrixCompactification.structureMap w)
    (MatrixCompactification.centerIdeal w y a (truncationOrders w F)) (hyperplane w)
    (blowupBundle_ample_of_interpolationBundle w y a _
      (chosenWeights_interpolationBundle_ample n hn m q hq hgrowth y hy0 hy a F hF))

/-- The centers are exactly (2^j,j*r_i), without any surjectivity hypothesis. -/
theorem logTwo_eventual_jetRestriction_surjective
    (n : ℕ) (hn : 1 ≤ n) (m : ℕ) (q : ℕ → ℕ) (hq : ∀ i, 2 ≤ q i)
    (hgrowth : ∀ i, i < m →
      denominatorSeparationFactor n m (chosenComparisonConstant n m) *
        (∏ j : Fin i, (ceilLogWeight (q j) : ℝ)) < (ceilLogWeight (q i) : ℝ))
    (r : Fin m → ℚ) :
    let w := chosenWeights n hn m (fun i => q i) (fun i => hq i)
    ∀ (F : ℚ), 1 / w.theta < F →
      ∃ N, ∀ k, N ≤ k → Function.Surjective
        (jetRestriction (MatrixCompactification.logTwoIdeal w r (truncationOrders w F))
          (hyperplane w) k) := by
  dsimp only
  exact chosenWeights_eventual_jetRestriction_surjective n hn m q hq hgrowth
    (fun j => 2^j.val) (fun j => pow_ne_zero j.val (by norm_num))
    (complex_centerY_injective.comp Fin.val_injective) (fun j i => (j.val : ℂ) * (r i : ℂ))

end
end LogTwo.Geometry.MatrixBlowup
end Source0825

-- Source: LogTwo/Geometry/WeightedAffineFrame.lean
section Source0826
/-
Modification notice for the LogTwo project.
Adapted from openai/math (Apache-2.0), revision adc7f1241b42e322a6451854ab7e4b4c146bf78a.
Changes: Extract generic weighted-section lemmas, change namespaces/imports and omit fixed-center wrappers.
See ../THIRD_PARTY_NOTICES.txt for provenance and the recorded changes.
-/

/-! Generic weighted-section lemma extracted from the pinned openai/math source.
Fixed-center admissible wrappers are excluded; proof bodies are preserved.
See THIRD_PARTY_NOTICES.txt. -/

namespace LogTwo.Geometry.WeightedAffineFrame
noncomputable section
open OAI PiExponent AlgebraicGeometry CategoryTheory
open PiExponentSeshadri.Geometry PiExponentSeshadri.Projective PiExponentSeshadri.Frames
open PiExponent.WeightedCompactification

theorem frame_nonempty_of_isoOpen_eq {X : Scheme} (M : X.Modules)
    (s : O X ⟶ M) (U : X.Opens) (h : PiExponentSeshadri.SectionOpens.isoOpen s = U) :
    Nonempty (M.restrict U.ι ≅ O U.toScheme) := by
  subst U
  exact ⟨sectionFrame s⟩

variable {R ι σ : Type} [CommRing R]

attribute [local irreducible] WeightedCompactification.lineBundle
  WeightedCompactification.affineChartMap WeightedCompactification.coordinateSection

theorem affineChart_isoOpen (a : σ → ι →₀ ℕ) (z : σ) (hz : a z = 0)
    (coordinate : ι → σ) (hcoordinate : ∀ i, a (coordinate i) = Finsupp.single i 1) :
    PiExponentSeshadri.SectionOpens.isoOpen (coordinateSection (R := R) a z) =
      (affineChartMap (R := R) a z hz coordinate hcoordinate).opensRange := by
  rw [coordinateSection_isoOpen]
  apply TopologicalSpace.Opens.ext
  exact (affineChartMap_range (R := R) a z hz coordinate hcoordinate).symm

theorem affineFrame_nonempty (a : σ → ι →₀ ℕ) (z : σ) (hz : a z = 0)
    (coordinate : ι → σ) (hcoordinate : ∀ i, a (coordinate i) = Finsupp.single i 1) :
    Nonempty ((lineBundle (R := R) a).sheaf.restrict
      (affineChartMap (R := R) a z hz coordinate hcoordinate).opensRange.ι ≅
        O (affineChartMap (R := R) a z hz coordinate hcoordinate).opensRange.toScheme) :=
  frame_nonempty_of_isoOpen_eq (lineBundle (R := R) a).sheaf (coordinateSection (R := R) a z)
    (affineChartMap (R := R) a z hz coordinate hcoordinate).opensRange
    (affineChart_isoOpen (R := R) a z hz coordinate hcoordinate)

end
end LogTwo.Geometry.WeightedAffineFrame
end Source0826

-- Source: OAI/NumberTheory/PiExponent/Approximation/WeightedFrameDegree.lean
section Source0827
/-
Modification notice for the LogTwo project.
Derived from openai/math (Apache-2.0), revision adc7f1241b42e322a6451854ab7e4b4c146bf78a.
Original source: lean/OAI/NumberTheory/PiExponent/Approximation/WeightedFrameDegree.lean
Changes: Convert module/import declarations to the Lean 4.34 public module format.
See ../THIRD_PARTY_NOTICES.txt for provenance and the recorded changes.
-/

namespace OAI

noncomputable section
namespace PiExponent.WeightedFrameDegree
open AlgebraicGeometry CategoryTheory
open PiExponentSeshadri.Frames
open PiExponent.WeightedSliceDegree
variable {K ι : Type} [Field K]

theorem supportBound_unit_mul (ρ : ι → ℝ) (B : ℝ)
    (u p : MvPolynomial ι K) (hu : IsUnit u) (hp : SupportBound ρ B p) :
    SupportBound ρ B (u * p) := by
  obtain ⟨c, _, rfl⟩ := MvPolynomial.isUnit_iff_eq_C_of_isReduced.mp hu
  simpa only [zero_add] using (supportBound_C ρ c).mul hp

theorem coefficient_supportBound (ρ : ι → ℝ) (B : ℝ)
    {M : (Spec (CommRingCat.of (MvPolynomial ι K))).Modules}
    (E F : M ≅ O (Spec (CommRingCat.of (MvPolynomial ι K))))
    (s : O (Spec (CommRingCat.of (MvPolynomial ι K))) ⟶ M)
    (h : SupportBound ρ B
      ((Scheme.ΓSpecIso (CommRingCat.of (MvPolynomial ι K))).hom (coefficient E s))) :
    SupportBound ρ B
      ((Scheme.ΓSpecIso (CommRingCat.of (MvPolynomial ι K))).hom (coefficient F s)) := by
  rw [coefficient_change E F, map_mul]
  apply supportBound_unit_mul ρ B _ _ ?_ h
  exact (frameChange E F).isUnit.map
    (Scheme.ΓSpecIso (CommRingCat.of (MvPolynomial ι K))).hom.hom

end PiExponent.WeightedFrameDegree
end

end OAI
end Source0827

-- Source: OAI/NumberTheory/PiExponent/LocalAlgebra/WeightedChartRingEvaluation.lean
section Source0828
/-
Modification notice for the LogTwo project.
Derived from openai/math (Apache-2.0), revision adc7f1241b42e322a6451854ab7e4b4c146bf78a.
Original source: lean/OAI/NumberTheory/PiExponent/LocalAlgebra/WeightedChartRingEvaluation.lean
Changes: Convert module/import declarations to the Lean 4.34 public module format.
See ../THIRD_PARTY_NOTICES.txt for provenance and the recorded changes.
-/

namespace OAI

namespace PiExponent.WeightedChartRingEvaluation
noncomputable section
open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite MvPolynomial
open PiExponentSeshadri.Geometry PiExponentSeshadri.Projective
open PiExponentSeshadri.Frames PiExponentSeshadri
open PiExponent.WeightedCompactification
attribute [local instance] MvPolynomial.gradedAlgebra

section Generic
variable {X : Scheme} {K σ A : Type} [CommRing K] [CommRing A]
variable (M : X.Modules) (k : K →+* Γ(X,⊤)) (s : σ → (O X ⟶ M))
  (hc : (⨆ i, SectionOpens.isoOpen (s i)) = ⊤)
  (f : X ≅ Proj (PolyGrade K σ)) (hf : sectionsMorphism k s hc = f.hom)
  (i : σ) (v : PolyChart (R := K) i →+* A)
  (g : Spec (CommRingCat.of A) ⟶ (SectionOpens.isoOpen (s i)).toScheme)
  (hg : g ≫ (coordinateSectionChartIso M k s hc f hf i).hom =
    Spec.map (CommRingCat.ofHom v))

include hg

theorem chart_pullback (q : MvPolynomial (ChartVariables i) K) :
    (Scheme.ΓSpecIso (CommRingCat.of A)).hom
      (g.appTop ((SectionOpens.isoOpen (s i)).topIso.inv
        ((coordinateSectionRingEquiv M k s hc f hf i).symm q))) = v (polyToChart i q) := by
  let U := SectionOpens.isoOpen (s i)
  let e := coordinateSectionChartIso M k s hc f hf i
  have hcancel (x : Γ(U.toScheme, ⊤)) : U.topIso.inv (U.topIso.hom x) = x :=
    CategoryTheory.congr_fun U.topIso.hom_inv_id x
  change (Scheme.ΓSpecIso (CommRingCat.of A)).hom
    (g.appTop (U.topIso.inv (U.topIso.hom
      (e.hom.appTop ((Scheme.ΓSpecIso (CommRingCat.of (PolyChart (R := K) i))).inv
        (polyToChart i q)))))) = _
  rw [hcancel]
  change (e.hom.appTop ≫ g.appTop ≫ (Scheme.ΓSpecIso (CommRingCat.of A)).hom)
    ((Scheme.ΓSpecIso (CommRingCat.of (PolyChart (R := K) i))).inv (polyToChart i q)) = _
  rw [← Scheme.Hom.comp_appTop_assoc, hg, Scheme.ΓSpecIso_naturality]
  change v ((Scheme.ΓSpecIso (CommRingCat.of (PolyChart (R := K) i))).hom
    ((Scheme.ΓSpecIso (CommRingCat.of (PolyChart (R := K) i))).inv (polyToChart i q))) = _
  exact congrArg v (CategoryTheory.congr_fun
    (Scheme.ΓSpecIso (CommRingCat.of (PolyChart (R := K) i))).inv_hom_id _)
end Generic

variable {R ι σ : Type} [CommRing R]

theorem evalAway_polyToChart (a : σ → ι →₀ ℕ) (z : σ) (hz : a z = 0)
    (q : MvPolynomial (ChartVariables z) R) :
    evalAway (affineMonomialMap (R := R) a) (X z)
      (by simp [affineMonomialMap, hz])
      (polyToChart z q) =
      eval₂Hom C (fun j : ChartVariables z => monomial (a j.val) (1 : R)) q := by
  have ha : monomial (a z) (1 : R) = (1 : MvPolynomial ι R) := by simp [hz]
  have he :
      (evalAway (affineMonomialMap (R := R) a) (X z)
        (by simp [affineMonomialMap, hz])).comp (polyToChart z) =
      eval₂Hom C (fun j : ChartVariables z => monomial (a j.val) (1 : R)) := by
    apply MvPolynomial.ringHom_ext
    · intro r
      simp only [RingHom.comp_apply, polyToChart, eval₂Hom_C]
      exact evalAway_constants z C (fun j => monomial (a j) (1 : R)) ha r
    · intro j
      simp only [RingHom.comp_apply, polyToChart, eval₂Hom_X']
      exact evalAway_coordinate z C (fun j => monomial (a j) (1 : R)) ha j.val
  exact RingHom.congr_fun he q

abbrev ambientOpen (z : σ) : (ProjectiveO1.projectiveSpace R σ).Opens :=
  SectionOpens.isoOpen (ProjectiveO1.coordinateSection (R := R) z)

def ambientRingEquiv (z : σ) :
    Γ(ProjectiveO1.projectiveSpace R σ, ambientOpen (R := R) z) ≃+*
      MvPolynomial (ChartVariables z) R :=
  coordinateSectionRingEquiv (ProjectiveO1.lineBundle (R := R) (σ := σ)).sheaf
    ProjectiveO1.scalars ProjectiveO1.coordinateSection ProjectiveO1.coordinateSection_cover
    (Iso.refl _) ProjectiveO1.coordinate_sectionsMorphism_identity z

def chartFactor (a : σ → ι →₀ ℕ) (z : σ) (hz : a z = 0)
    (_coordinate : ι → σ) (_hcoordinate : ∀ i, a (_coordinate i) = Finsupp.single i 1) :
    Spec (CommRingCat.of (MvPolynomial ι R)) ⟶ (ambientOpen (R := R) z).toScheme :=
  Spec.map (CommRingCat.ofHom
    (evalAway (𝒜 := PolyGrade R σ) (affineMonomialMap (R := R) a) (X z)
      (by simp [affineMonomialMap, hz]))) ≫
    (coordinateSectionChartIso (ProjectiveO1.lineBundle (R := R) (σ := σ)).sheaf
      ProjectiveO1.scalars ProjectiveO1.coordinateSection ProjectiveO1.coordinateSection_cover
      (Iso.refl _) ProjectiveO1.coordinate_sectionsMorphism_identity z).inv

theorem chartFactor_comp (a : σ → ι →₀ ℕ) (z : σ) (hz : a z = 0)
    (coordinate : ι → σ) (hcoordinate : ∀ i, a (coordinate i) = Finsupp.single i 1) :
    affineChartMap (R := R) a z hz coordinate hcoordinate ≫ projectiveMonomialMap a =
      chartFactor a z hz coordinate hcoordinate ≫ (ambientOpen (R := R) z).ι := by
  have he := coordinateSectionChartIso_hom_away
    (ProjectiveO1.lineBundle (R := R) (σ := σ)).sheaf
    ProjectiveO1.scalars ProjectiveO1.coordinateSection ProjectiveO1.coordinateSection_cover
    (Iso.refl _) ProjectiveO1.coordinate_sectionsMorphism_identity z
  rw [ProjectiveO1.coordinate_sectionsMorphism_identity, Category.comp_id] at he
  rw [affineChartMap_comp_projectiveMonomialMap]
  unfold chartFactor fromUnitCoordinate
  rw [← he]
  simp only [Category.assoc, Iso.inv_hom_id_assoc]

theorem ambient_chart_pullback (a : σ → ι →₀ ℕ) (z : σ) (hz : a z = 0)
    (coordinate : ι → σ) (hcoordinate : ∀ i, a (coordinate i) = Finsupp.single i 1)
    (g : Spec (CommRingCat.of (MvPolynomial ι R)) ⟶ (ambientOpen (R := R) z).toScheme)
    (hg : g ≫ (ambientOpen (R := R) z).ι =
      affineChartMap a z hz coordinate hcoordinate ≫ projectiveMonomialMap a)
    (q : MvPolynomial (ChartVariables z) R) :
    (Scheme.ΓSpecIso (CommRingCat.of (MvPolynomial ι R))).hom
      (g.appTop ((ambientOpen (R := R) z).topIso.inv ((ambientRingEquiv z).symm q))) =
      eval₂Hom C (fun j : ChartVariables z => monomial (a j.val) (1 : R)) q := by
  let v : PolyChart (R := R) z →+* MvPolynomial ι R := evalAway (affineMonomialMap (R := R) a) (X z)
    (show IsUnit (affineMonomialMap (R := R) a (X z)) from by
      simp [affineMonomialMap, hz])
  have hfactor : g ≫
      (coordinateSectionChartIso (ProjectiveO1.lineBundle (R := R) (σ := σ)).sheaf
        ProjectiveO1.scalars ProjectiveO1.coordinateSection ProjectiveO1.coordinateSection_cover
        (Iso.refl _) ProjectiveO1.coordinate_sectionsMorphism_identity z).hom =
      Spec.map (CommRingCat.ofHom v) := by
    apply (cancel_mono (Proj.awayι (PolyGrade R σ) (X z) (poly_X_mem z) (by decide))).mp
    rw [Category.assoc, coordinateSectionChartIso_hom_away,
      ProjectiveO1.coordinate_sectionsMorphism_identity, Category.comp_id, hg,
      affineChartMap_comp_projectiveMonomialMap]
    rfl
  exact (chart_pullback (ProjectiveO1.lineBundle (R := R) (σ := σ)).sheaf
    ProjectiveO1.scalars ProjectiveO1.coordinateSection ProjectiveO1.coordinateSection_cover
    (Iso.refl _) ProjectiveO1.coordinate_sectionsMorphism_identity z v g hfactor q).trans
      (evalAway_polyToChart a z hz q)

theorem chartFactor_pullback (a : σ → ι →₀ ℕ) (z : σ) (hz : a z = 0)
    (coordinate : ι → σ) (hcoordinate : ∀ i, a (coordinate i) = Finsupp.single i 1)
    (q : MvPolynomial (ChartVariables z) R) :
    (Scheme.ΓSpecIso (CommRingCat.of (MvPolynomial ι R))).hom
      ((chartFactor a z hz coordinate hcoordinate).appTop
        ((ambientOpen (R := R) z).topIso.inv ((ambientRingEquiv z).symm q))) =
      eval₂Hom C (fun j : ChartVariables z => monomial (a j.val) (1 : R)) q :=
  ambient_chart_pullback a z hz coordinate hcoordinate
    (chartFactor a z hz coordinate hcoordinate) (chartFactor_comp a z hz coordinate hcoordinate).symm q

end
end PiExponent.WeightedChartRingEvaluation

end OAI
end Source0828

-- Source: OAI/NumberTheory/PiExponent/Approximation/CompositePullbackFrame.lean
section Source0829
/-
Modification notice for the LogTwo project.
Derived from openai/math (Apache-2.0), revision adc7f1241b42e322a6451854ab7e4b4c146bf78a.
Original source: lean/OAI/NumberTheory/PiExponent/Approximation/CompositePullbackFrame.lean
Changes: Convert module/import declarations to the Lean 4.34 public module format.
See ../THIRD_PARTY_NOTICES.txt for provenance and the recorded changes.
-/

namespace OAI

noncomputable section
namespace PiExponent.CompositePullbackFrame
open AlgebraicGeometry CategoryTheory
open PiExponentSeshadri.Geometry PiExponentSeshadri.Frames
variable {X Y Z : Scheme.{0}}

private theorem mapIso_trans_inv_comp {C D : Type*} [Category C] [Category D]
    (F : C ⥤ D) {A B T : C} {U : D} (e : A ≅ B) (u : F.obj B ≅ U)
    (s : A ⟶ T) :
    (F.mapIso e ≪≫ u).inv ≫ F.map s = u.inv ≫ F.map (e.inv ≫ s) := by
  simp only [Iso.trans_inv, Functor.mapIso_inv, Functor.map_comp, Category.assoc]

private theorem map_comp_iso_inv {C D : Type*} [Category C] [Category D]
    (F : C ⥤ D) {A B T : C} {U : D} (u : U ⟶ F.obj A)
    (s : A ⟶ B) (e : B ≅ T) :
    (u ≫ F.map (s ≫ e.hom)) ≫ (F.mapIso e).inv = u ≫ F.map s := by
  simp only [Functor.mapIso_inv, Category.assoc, ← Functor.map_comp,
    Iso.hom_inv_id, Category.comp_id]

theorem exists_frame (f : X ⟶ Y) (φ : Z ⟶ X) [IsOpenImmersion φ]
    (V : Y.Opens) (g : Z ⟶ V.toScheme) (h : φ ≫ f = g ≫ V.ι)
    {M : Y.Modules} (e : M.restrict V.ι ≅ O V.toScheme) :
    ∃ E : ((Scheme.Modules.pullback f).obj M).restrict φ ≅ O Z,
      ∀ s : O Y ⟶ M,
        coefficient E (restrictSection φ (pullbackSection f s)) =
          g.appTop (coefficient e (restrictSection V.ι s)) := by
  let F := Scheme.Modules.pullback f ⋙ Scheme.Modules.restrictFunctor φ
  let G := Scheme.Modules.restrictFunctor V.ι ⋙ Scheme.Modules.pullback g
  let v : F ≅ G :=
    Functor.isoWhiskerLeft (Scheme.Modules.pullback f)
      (Scheme.Modules.restrictFunctorIsoPullback φ) ≪≫
    Scheme.Modules.pullbackComp φ f ≪≫
    Scheme.Modules.pullbackCongr h ≪≫
    (Scheme.Modules.pullbackComp g V.ι).symm ≪≫
    Functor.isoWhiskerRight (Scheme.Modules.restrictFunctorIsoPullback V.ι).symm
      (Scheme.Modules.pullback g)
  let uF : F.obj (O Y) ≅ O Z :=
    (Scheme.Modules.restrictFunctor φ).mapIso (pullbackUnitIso f) ≪≫
      Scheme.Modules.restrictUnitIso φ
  let uG : G.obj (O Y) ≅ O Z :=
    (Scheme.Modules.pullback g).mapIso (Scheme.Modules.restrictUnitIso V.ι) ≪≫
      pullbackUnitIso g
  obtain ⟨E, hE⟩ := PullbackFrameCoefficient.exists_frame_natIso_all F G v uF uG
    (pullbackFrame g e)
  refine ⟨E, fun s => ?_⟩
  have hs : coefficient E (restrictSection φ (pullbackSection f s)) =
      coefficient (pullbackFrame g e) (pullbackSection g (restrictSection V.ι s)) := by
    simp only [restrictSection, pullbackSection]
    exact (congrArg (coefficient E)
      (mapIso_trans_inv_comp (Scheme.Modules.restrictFunctor φ)
        (pullbackUnitIso f) (Scheme.Modules.restrictUnitIso φ)
        ((Scheme.Modules.pullback f).map s)).symm).trans
      ((hE s).trans (congrArg (coefficient (pullbackFrame g e))
        (mapIso_trans_inv_comp (Scheme.Modules.pullback g)
          (Scheme.Modules.restrictUnitIso V.ι) (pullbackUnitIso g)
          ((Scheme.Modules.restrictFunctor V.ι).map s))))
  rw [hs, coefficient_pullback]

theorem exists_power_frame (L : LineBundle Y) (f : X ⟶ Y)
    (φ : Z ⟶ X) [IsOpenImmersion φ] (V : Y.Opens)
    (g : Z ⟶ V.toScheme) (h : φ ≫ f = g ≫ V.ι) (n : ℕ)
    (e : (modulePow Y L.sheaf n).restrict V.ι ≅ O V.toScheme) :
    ∃ E : (modulePow X (L.pullback f).sheaf n).restrict φ ≅ O Z,
      ∀ s : O Y ⟶ modulePow Y L.sheaf n,
        coefficient E (restrictSection φ (pullbackPowerSection L f n s)) =
          g.appTop (coefficient e (restrictSection V.ι s)) := by
  obtain ⟨E, hE⟩ := exists_frame f φ V g h e
  refine ⟨(Scheme.Modules.restrictFunctor φ).mapIso
    (PiExponentSeshadri.PullbackTensor.powIso f L n).symm ≪≫ E, fun s => ?_⟩
  erw [coefficient_transport]
  have hs : restrictSection φ (pullbackPowerSection L f n s) ≫
      ((Scheme.Modules.restrictFunctor φ).mapIso (PiExponentSeshadri.PullbackTensor.powIso f L n).symm).hom =
      restrictSection φ (pullbackSection f s) := by
    simp only [restrictSection, pullbackPowerSection, Functor.mapIso_hom, Iso.symm_hom]
    exact map_comp_iso_inv (Scheme.Modules.restrictFunctor φ)
      (Scheme.Modules.restrictUnitIso φ).inv (pullbackSection f s)
      (PiExponentSeshadri.PullbackTensor.powIso f L n)
  exact (congrArg (coefficient E) hs).trans (hE s)

end PiExponent.CompositePullbackFrame
end

end OAI
end Source0829

-- Source: OAI/NumberTheory/PiExponent/Geometry/ProjectiveGlobalPolynomialAlgebra.lean
section Source0830
/-
Modification notice for the LogTwo project.
Derived from openai/math (Apache-2.0), revision adc7f1241b42e322a6451854ab7e4b4c146bf78a.
Original source: lean/OAI/NumberTheory/PiExponent/Geometry/ProjectiveGlobalPolynomialAlgebra.lean
Changes: Convert module/import declarations to the Lean 4.34 public module format.
See ../THIRD_PARTY_NOTICES.txt for provenance and the recorded changes.
-/

namespace OAI

namespace PiExponent.GeometrySupport.ProjectiveGlobalPolynomialAlgebra
noncomputable section
open scoped BigOperators
open MvPolynomial
open PiExponent.ProjectiveMonomialCech
open PiExponent.GeometrySupport.ProjectiveLaurentVertex
open PiExponentSeshadri.Projective

variable {σ K : Type*} [Fintype σ] [CommRing K]

def chartExponent (i : σ) (b : σ →₀ ℕ) : ChartExponent i :=
  Finsupp.equivFunOnFinite.symm (fun j => b j.val)

@[simp] theorem chartExponent_apply (i : σ) (b : σ →₀ ℕ) (j : ChartVariables i) :
    chartExponent i b j = b j.val := rfl

theorem dehomogenize_monomial (i : σ) (b : σ →₀ ℕ) (r : K) :
    dehomogenize i (MvPolynomial.monomial b r) =
      MvPolynomial.monomial (chartExponent i b) r := by
  classical
  rw [dehomogenize, MvPolynomial.eval₂Hom_monomial, MvPolynomial.monomial_eq]
  congr 1
  rw [Finsupp.prod_fintype, Finsupp.prod_fintype]
  · rw [Fintype.prod_eq_mul_prod_subtype_ne _ i]
    simp
    apply Finset.prod_congr rfl
    intro j _
    simp [j.property]
  · intro j
    simp
  · intro j
    simp

theorem encode_chartExponent (i : σ) (n : ℕ) (b : σ →₀ ℕ) (hb : b.degree = n) :
    ProjectiveLaurentVertex.encode i (n : ℤ) (chartExponent i b) =
      GradedH0.encode n ⟨b, hb⟩ := by
  classical
  apply Subtype.ext
  funext j
  by_cases hj : j = i
  · subst j
    rw [ProjectiveLaurentVertex.encode_self]
    erw [GradedH0.encode_apply]
    have hs : (b i : ℤ) + ∑ j : ChartVariables i, (b j.val : ℤ) = n := by
      rw [← Fintype.sum_eq_add_sum_subtype_ne (fun j => (b j : ℤ)) i,
        ← Nat.cast_sum, ← Finsupp.degree_eq_sum, hb]
    simpa only [chartExponent_apply] using (eq_sub_iff_add_eq.mpr hs).symm
  · change (ProjectiveLaurentVertex.encode i (n : ℤ) (chartExponent i b)).val
      (⟨j, hj⟩ : ChartVariables i) = _
    exact ProjectiveLaurentVertex.encode_other i (n : ℤ) (chartExponent i b) ⟨j, hj⟩

theorem polynomialLaurent_monomial (n : ℕ) (b : σ →₀ ℕ) (hb : b.degree = n) (r : K) :
    GradedH0.polynomialLaurent n ⟨MvPolynomial.monomial b r,
      MvPolynomial.isHomogeneous_monomial r hb⟩ =
      Finsupp.single (GradedH0.encode n ⟨b, hb⟩) r := by
  classical
  simp [GradedH0.polynomialLaurent, GradedH0.homogeneousPolynomialEquiv,
    MvPolynomial.monomial, GradedH0.exponentEquiv,
    AddMonoidAlgebra.supportedEquivFinsupp]
  have hs : (Finsupp.supportedEquivFinsupp (R := K) {b : σ →₀ ℕ | b.degree = n})
      ⟨Finsupp.single b r, Finsupp.single_mem_supported K r hb⟩ =
      Finsupp.single ⟨b, hb⟩ r := by
    apply (Finsupp.supportedEquivFinsupp (R := K) {b : σ →₀ ℕ | b.degree = n}).symm.injective
    apply Subtype.ext
    simp
  change (Finsupp.domLCongr (GradedH0.exponentEquiv n)
    ((Finsupp.supportedEquivFinsupp (R := K) {b : σ →₀ ℕ | b.degree = n})
      ⟨Finsupp.single b r, Finsupp.single_mem_supported K r hb⟩)).extendDomain = _
  rw [hs]
  change (Finsupp.domLCongr (GradedH0.exponentEquiv n)
    (Finsupp.single (⟨b, hb⟩ : GradedH0.PolynomialExponent (ι := σ) n) r)).extendDomain = _
  erw [Finsupp.domLCongr_single, Finsupp.extendDomain_single]
  rfl

theorem vertexLaurent_dehomogenize (i : σ) (n : ℕ)
    (p : MvPolynomial.homogeneousSubmodule σ K n) :
    vertexLaurent i (n : ℤ) (dehomogenize i p.val) = GradedH0.polynomialLaurent n p := by
  rcases p with ⟨p, hp⟩
  induction hp using MvPolynomial.IsWeightedHomogeneous.induction_on with
  | zero =>
    change vertexLaurent i (n : ℤ) (dehomogenize i 0) = GradedH0.polynomialLaurent n 0
    simp only [map_zero]
  | add p q hp hq ihp ihq =>
    change vertexLaurent i (n : ℤ) (dehomogenize i (p + q)) =
      GradedH0.polynomialLaurent n (⟨p, hp⟩ + ⟨q, hq⟩)
    rw [map_add, map_add, map_add, ihp, ihq]
  | monomial b r hb =>
    have hd : b.degree = n := by
      simpa only [Finsupp.degree_eq_weight_one, Pi.one_def] using hb
    rw [dehomogenize_monomial, vertexLaurent_monomial,
      polynomialLaurent_monomial n b hd r, encode_chartExponent i n b hd]

end
end PiExponent.GeometrySupport.ProjectiveGlobalPolynomialAlgebra

end OAI
end Source0830

-- Source: OAI/NumberTheory/PiExponent/Geometry/ProjectiveRepresentedCoefficient.lean
section Source0831
/-
Modification notice for the LogTwo project.
Derived from openai/math (Apache-2.0), revision adc7f1241b42e322a6451854ab7e4b4c146bf78a.
Original source: lean/OAI/NumberTheory/PiExponent/Geometry/ProjectiveRepresentedCoefficient.lean
Changes: Convert module/import declarations to the Lean 4.34 public module format.
See ../THIRD_PARTY_NOTICES.txt for provenance and the recorded changes.
-/

namespace OAI

namespace PiExponentSeshadri.ProjectiveChartSections
noncomputable section
open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite
open PiExponentSeshadri.Geometry ModuleFlasque RestrictionCohomology
open PiExponentSeshadri.FlasqueCohomology FreeOpenUnit Frames

variable {X : Scheme} (U : X.Opens) (M : X.Modules)

theorem freeOpenEquiv_freeTop_comp (b : structureSheaf X ⟶ M) :
    freeOpenEquiv X.ringCatSheaf M ⊤ ((freeTopIso X.ringCatSheaf).hom ≫ b) =
      globalHomEquiv X.ringCatSheaf M b := by
  erw [freeOpenEquiv_comp]
  change b.val.app (op ⊤)
    (freeOpenEquiv X.ringCatSheaf (SheafOfModules.unit X.ringCatSheaf) ⊤
      ((freeOpenEquiv X.ringCatSheaf (SheafOfModules.unit X.ringCatSheaf) ⊤).symm
        (globalHomEquiv X.ringCatSheaf (SheafOfModules.unit X.ringCatSheaf) (𝟙 _)))) = _
  rw [Equiv.apply_symm_apply]
  rfl

theorem framedHomCoefficientsEquiv_globalSection
    (e : M.restrict U.ι ≅ structureSheaf U.toScheme) (b : structureSheaf X ⟶ M) :
    framedHomCoefficientsEquiv U M e
      (freeOpenMap X.ringCatSheaf (homOfLE (show U ≤ ⊤ from le_top)) ≫
        (freeTopIso X.ringCatSheaf).hom ≫ b) =
      U.topIso.hom (coefficient e (restrictSection U.ι b)) := by
  change U.topIso.hom (e.hom.app ⊤ ((restrictionSectionsIso U M).inv
    (freeOpenEquiv X.ringCatSheaf M U
      (freeOpenMap X.ringCatSheaf (homOfLE (show U ≤ ⊤ from le_top)) ≫
        (freeTopIso X.ringCatSheaf).hom ≫ b)))) = _
  erw [freeOpenEquiv_naturality X.ringCatSheaf M
    (homOfLE (show U ≤ ⊤ from le_top)) ((freeTopIso X.ringCatSheaf).hom ≫ b),
    freeOpenEquiv_freeTop_comp]
  apply congrArg U.topIso.hom
  change e.hom.app ⊤
      (M.presheaf.map (eqToHom U.ι_image_top).op
        (M.presheaf.map (homOfLE (show U ≤ ⊤ from le_top)).op (b.app ⊤ (1 : Γ(X, ⊤))))) =
    e.hom.app ⊤ (b.app (U.ι ''ᵁ ⊤) ((U.ι.appIso ⊤).inv (1 : Γ(U.toScheme, ⊤))))
  apply congrArg (e.hom.app ⊤)
  rw [show (U.ι.appIso ⊤).inv (1 : Γ(U.toScheme, ⊤)) =
    (1 : Γ(X, U.ι ''ᵁ ⊤)) from map_one _]
  change (M.presheaf.map _ ≫ M.presheaf.map _) (b.app ⊤ (1 : Γ(X, ⊤))) = _
  rw [← Functor.map_comp]
  rw [show (homOfLE (show U ≤ ⊤ from le_top)).op ≫ (eqToHom U.ι_image_top).op =
    (homOfLE (show U.ι ''ᵁ ⊤ ≤ ⊤ from le_top)).op from Subsingleton.elim _ _]
  have hb := CategoryTheory.congr_fun (b.mapPresheaf.naturality
    (homOfLE (show U.ι ''ᵁ ⊤ ≤ ⊤ from le_top)).op) (1 : Γ(X, ⊤))
  change b.app (U.ι ''ᵁ ⊤)
      (X.presheaf.map (homOfLE (show U.ι ''ᵁ ⊤ ≤ ⊤ from le_top)).op 1) =
    M.presheaf.map (homOfLE (show U.ι ''ᵁ ⊤ ≤ ⊤ from le_top)).op (b.app ⊤ (1 : Γ(X, ⊤))) at hb
  simpa only [map_one] using hb.symm

end
end PiExponentSeshadri.ProjectiveChartSections

end OAI
end Source0831

-- Source: OAI/NumberTheory/PiExponent/Geometry/ProjectiveVertexCompatibility.lean
section Source0832
/-
Modification notice for the LogTwo project.
Derived from openai/math (Apache-2.0), revision adc7f1241b42e322a6451854ab7e4b4c146bf78a.
Original source: lean/OAI/NumberTheory/PiExponent/Geometry/ProjectiveVertexCompatibility.lean
Changes: Convert module/import declarations to the Lean 4.34 public module format.
See ../THIRD_PARTY_NOTICES.txt for provenance and the recorded changes.
-/

namespace OAI

namespace PiExponentSeshadri.Projective
noncomputable section
open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite
open PiExponentSeshadri.Frames PiExponentSeshadri.Geometry ModuleFlasque ProjectiveChartSections
open PiExponent.GeometrySupport.ProjectiveLaurentVertex
open PiExponent.GeometrySupport.ProjectiveTupleCharts

attribute [local instance] MvPolynomial.gradedAlgebra

variable {X : Scheme.{0}} {K σ : Type} [CommRing K] [Fintype σ]
variable (M : X.Modules) (s : σ → (O X ⟶ M)) (k : K →+* Γ(X,⊤))
variable (hc : (⨆ i, SectionOpens.isoOpen (s i)) = ⊤)
variable (f : X ≅ Proj (PolyGrade K σ)) (hf : sectionsMorphism k s hc = f.hom)

lemma coordinatePowerOverlap_restrictVertex (n : ℕ) (i : σ)
    (a : Finset (ChartVariables i))
    (b : freeOpen X.ringCatSheaf (SectionOpens.isoOpen (s i)) ⟶ modulePow X M n) :
    coordinatePowerOverlap M s k hc f hf n i a
      (freeOpenMap X.ringCatSheaf (homOfLE (show coordinateFiniteOpen M s i a ≤
        SectionOpens.isoOpen (s i) from inf_le_left)) ≫ b) =
      coordinatePowerVertex M k s hc f hf n i b := by
  change overlapLaurent i (n : ℤ) a
    (coordinateFiniteRingEquiv M s k hc f hf i a
      (framedHomCoefficientsEquiv _ (modulePow X M n)
        (restrictOpenFrame inf_le_left (coordinatePowerFrame (s i) n))
        (freeOpenMap X.ringCatSheaf (homOfLE _) ≫ b))) =
    vertexLaurent i (n : ℤ) (coordinateSectionRingEquiv M k s hc f hf i
      (framedHomCoefficientsEquiv _ (modulePow X M n) (coordinatePowerFrame (s i) n) b))
  erw [framedHomCoefficientsEquiv_restrict]
  erw [coordinateFiniteRingEquiv_restrict_apply M s k hc f hf i a]
  exact overlapLaurent_base i (n : ℤ) a _

lemma coordinateTupleCoefficient_restrictVertex (n q : ℕ) (t : Fin (q+1) → σ)
    (b : freeOpen X.ringCatSheaf (SectionOpens.isoOpen (s (t 0))) ⟶ modulePow X M n) :
    coordinateTupleCoefficient M s k hc f hf n q t
      (freeOpenMap X.ringCatSheaf (homOfLE
        (iInf_le (fun j => SectionOpens.isoOpen (s (t j))) 0)) ≫ b) =
      coordinatePowerVertex M k s hc f hf n (t 0) b := by
  change coordinatePowerOverlap M s k hc f hf n (t 0) (tupleVariables t 0)
    (freeOpenHomCongr (modulePow X M n) (coordinateFiniteOpen_tuple M s t 0)
      (freeOpenMap X.ringCatSheaf (homOfLE _) ≫ b)) = _
  have h : freeOpenHomCongr (modulePow X M n) (coordinateFiniteOpen_tuple M s t 0)
      (freeOpenMap X.ringCatSheaf (homOfLE
        (iInf_le (fun j => SectionOpens.isoOpen (s (t j))) 0)) ≫ b) =
      freeOpenMap X.ringCatSheaf (homOfLE (show coordinateFiniteOpen M s (t 0)
        (tupleVariables t 0) ≤ SectionOpens.isoOpen (s (t 0)) from inf_le_left)) ≫ b := by
    change freeOpenMap X.ringCatSheaf _ ≫ (freeOpenMap X.ringCatSheaf _ ≫ b) = _
    simp only [freeOpenMap]
    erw [← Functor.map_comp_assoc, ← Functor.map_comp, ← Functor.map_comp]
    rfl
  rw [h]
  exact coordinatePowerOverlap_restrictVertex M s k hc f hf n (t 0) (tupleVariables t 0) b

end
end PiExponentSeshadri.Projective

end OAI
end Source0832

-- Source: OAI/NumberTheory/PiExponent/Geometry/ProjectiveGlobalPolynomials.lean
section Source0833
-- Modified in this edition: unused plain lemmas removed; see reduction.json.
/-
Modification notice for the LogTwo project.
Derived from openai/math (Apache-2.0), revision adc7f1241b42e322a6451854ab7e4b4c146bf78a.
Original source: lean/OAI/NumberTheory/PiExponent/Geometry/ProjectiveGlobalPolynomials.lean
Changes: Convert module/import declarations to the Lean 4.34 public module format.
Expose private helpers and adjust helper names where needed for module compatibility.
See ../THIRD_PARTY_NOTICES.txt for provenance and the recorded changes.
-/

namespace OAI

namespace PiExponent.ProjectiveGlobalPolynomials
noncomputable section
open AlgebraicGeometry CategoryTheory TopologicalSpace
open PiExponentSeshadri.Geometry PiExponentSeshadri.ModuleFlasque
open GeometrySupport ProjectiveTwistCech ProjectiveMonomialCech

variable {X : Scheme.{0}} {σ R : Type} [CommRing R] [Fintype σ]
variable {U : σ → X.Opens} {M : X.Modules} {n : ℕ}

abbrev schemeFreeOpen (X : Scheme.{0}) (V : X.Opens) : X.Modules :=
  freeOpen X.ringCatSheaf V

def globalCochain (U : σ → X.Opens) (M : X.Modules)
    (b : structureSheaf X ⟶ M) : CechHigher.Cochain X.ringCatSheaf U M 0 :=
  CechHigher.augmentation X.ringCatSheaf U M ⊤ (fun _ => le_top)
    ((PiExponentSeshadri.FreeOpenUnit.freeTopIso X.ringCatSheaf).hom ≫ b)

def globalLaurent (P : LaurentCechPresentation (K := R) U M (n : ℤ))
    (b : structureSheaf X ⟶ M) :
    ProjectiveMonomialCechHigher.Cochain σ (Laurent σ R (n : ℤ)) 0 :=
  P.toLaurent (globalCochain U M b)

lemma globalLaurent_closed (P : LaurentCechPresentation (K := R) U M (n : ℤ))
    (b : structureSheaf X ⟶ M) :
    ProjectiveMonomialCechHigher.differential (globalLaurent P b) = 0 := by
  rw [globalLaurent, ← P.toLaurent_differential]
  rw [globalCochain]
  erw [CechHigher.augmentation_closed]
  funext t
  exact map_zero _

theorem existsUnique_polynomial [Nonempty σ] (P : LaurentCechPresentation (K := R) U M (n : ℤ))
    (b : structureSheaf X ⟶ M) :
    ∃! p : MvPolynomial.homogeneousSubmodule σ R n,
      ∀ t, GradedH0.polynomialLaurent n p = globalLaurent P b t := by
  exact GradedH0.zeroth_cocycle_unique_homogeneous_polynomial n (globalLaurent P b)
    (fun t => P.regular 0 t _) (globalLaurent_closed P b)

def representedRestriction (V : X.Opens) (N : X.Modules) (b : structureSheaf X ⟶ N) :
    freeOpen X.ringCatSheaf V ⟶ N :=
  freeOpenMap X.ringCatSheaf (homOfLE (show V ≤ ⊤ from le_top)) ≫
    (PiExponentSeshadri.FreeOpenUnit.freeTopIso X.ringCatSheaf).hom ≫ b

omit [Fintype σ] in
lemma globalCochain_restrict (U : σ → X.Opens) (N : X.Modules)
    (b : structureSheaf X ⟶ N) (t : Fin 1 → σ) :
    globalCochain U N b t = freeOpenMap X.ringCatSheaf
      (homOfLE (iInf_le (fun j => U (t j)) 0)) ≫ representedRestriction (U (t 0)) N b := by
  change freeOpenMap X.ringCatSheaf _ ≫ _ = freeOpenMap X.ringCatSheaf _ ≫
    (freeOpenMap X.ringCatSheaf _ ≫ _)
  simp only [freeOpenMap]
  erw [← Functor.map_comp_assoc, ← Functor.map_comp, ← Functor.map_comp]
  rfl

open PiExponentSeshadri.Projective PiExponentSeshadri.Frames PiExponentSeshadri.ProjectiveChartSections
open GeometrySupport.ProjectiveCoordinateAcyclicity GeometrySupport.ProjectiveTupleCharts
open GeometrySupport.ProjectiveLaurentVertex GeometrySupport.ProjectiveGlobalPolynomialAlgebra
attribute [local instance] MvPolynomial.gradedAlgebra
variable (L : X.Modules) (s : σ → (structureSheaf X ⟶ L)) (k : R →+* Γ(X,⊤))
    (hc : (⨆ i, PiExponentSeshadri.SectionOpens.isoOpen (s i)) = ⊤)
    (f : X ≅ Proj (PolyGrade R σ)) (hf : sectionsMorphism k s hc = f.hom)

def coordinateChartPolynomial (n : ℕ) (i : σ)
    (b : structureSheaf X ⟶ modulePow X L n) : MvPolynomial (ChartVariables i) R :=
  framedHomRingEquiv (PiExponentSeshadri.SectionOpens.isoOpen (s i)) (modulePow X L n)
    (coordinatePowerFrame (s i) n) (coordinateSectionRingEquiv L k s hc f hf i)
    (representedRestriction (PiExponentSeshadri.SectionOpens.isoOpen (s i)) _ b)

omit [Fintype σ] in

lemma coordinateChartPolynomial_coefficient (n : ℕ) (i : σ)
    (b : structureSheaf X ⟶ modulePow X L n) :
    coordinateChartPolynomial L s k hc f hf n i b =
      coordinateSectionRingEquiv L k s hc f hf i
        ((PiExponentSeshadri.SectionOpens.isoOpen (s i)).topIso.hom
          (coefficient (coordinatePowerFrame (s i) n)
            (restrictSection (PiExponentSeshadri.SectionOpens.isoOpen (s i)).ι b))) := by
  change coordinateSectionRingEquiv L k s hc f hf i
    (framedHomCoefficientsEquiv _ _ (coordinatePowerFrame (s i) n)
      (freeOpenMap X.ringCatSheaf (homOfLE le_top) ≫
        (PiExponentSeshadri.FreeOpenUnit.freeTopIso X.ringCatSheaf).hom ≫ b)) = _
  rw [framedHomCoefficientsEquiv_globalSection]

lemma coordinate_globalLaurent_vertex (n : ℕ)
    (b : structureSheaf X ⟶ modulePow X L n) (t : Fin 1 → σ) :
    globalLaurent (coordinateLaurentCechPresentation L s k hc f hf n) b t =
      vertexLaurent (t 0) (n : ℤ) (coordinateChartPolynomial L s k hc f hf n (t 0) b) := by
  change coordinateTupleCoefficient L s k hc f hf n 0 t
    (globalCochain (fun i => PiExponentSeshadri.SectionOpens.isoOpen (s i)) _ b t) = _
  rw [globalCochain_restrict]
  exact coordinateTupleCoefficient_restrictVertex L s k hc f hf n 0 t _

theorem coordinate_existsUnique_polynomial [Nonempty σ] (n : ℕ)
    (b : structureSheaf X ⟶ modulePow X L n) :
    ∃! p : MvPolynomial.homogeneousSubmodule σ R n,
      ∀ i, dehomogenize i p.val = coordinateChartPolynomial L s k hc f hf n i b := by
  obtain ⟨p, hp, hu⟩ := existsUnique_polynomial
    (coordinateLaurentCechPresentation L s k hc f hf n) b
  refine ⟨p, ?_, ?_⟩
  · intro i
    apply vertexLaurent_injective i (n : ℤ)
    rw [vertexLaurent_dehomogenize]
    exact (hp (fun _ => i)).trans (coordinate_globalLaurent_vertex L s k hc f hf n b _)
  · intro q hq
    apply hu q
    intro t
    calc
      GradedH0.polynomialLaurent n q = vertexLaurent (t 0) (n : ℤ)
          (dehomogenize (t 0) q.val) := (vertexLaurent_dehomogenize (t 0) n q).symm
      _ = vertexLaurent (t 0) (n : ℤ)
          (coordinateChartPolynomial L s k hc f hf n (t 0) b) := congrArg _ (hq (t 0))
      _ = _ := (coordinate_globalLaurent_vertex L s k hc f hf n b t).symm

end
end PiExponent.ProjectiveGlobalPolynomials

namespace PiExponent.ProjectiveO1
noncomputable section
open AlgebraicGeometry CategoryTheory
open PiExponentSeshadri.Geometry PiExponentSeshadri.Projective
open ProjectiveGlobalPolynomials
attribute [local irreducible] lineBundle coordinateSection scalars sectionsMorphism
variable {R σ : Type} [CommRing R] [Fintype σ]

def globalSectionChartPolynomial (n : ℕ) (i : σ)
    (b : structureSheaf (projectiveSpace R σ) ⟶
      modulePow (projectiveSpace R σ) (lineBundle (R := R) (σ := σ)).sheaf n) :
    MvPolynomial (ChartVariables i) R :=
  coordinateChartPolynomial (X := projectiveSpace R σ) (R := R) (σ := σ)
    (lineBundle (R := R) (σ := σ)).sheaf (coordinateSection (R := R) (σ := σ))
    (scalars (R := R) (σ := σ)) (coordinateSection_cover (R := R) (σ := σ))
    (Iso.refl (projectiveSpace R σ))
    (coordinate_sectionsMorphism_identity (R := R) (σ := σ)) n i b

theorem globalSection_homogeneous_polynomial [Nonempty σ] (n : ℕ)
    (b : structureSheaf (projectiveSpace R σ) ⟶
      modulePow (projectiveSpace R σ) (lineBundle (R := R) (σ := σ)).sheaf n) :
    ∃! p : MvPolynomial.homogeneousSubmodule σ R n,
      ∀ i, dehomogenize i p.val = globalSectionChartPolynomial n i b := by
  exact coordinate_existsUnique_polynomial (X := projectiveSpace R σ) (R := R) (σ := σ)
    (lineBundle (R := R) (σ := σ)).sheaf (coordinateSection (R := R) (σ := σ))
    (scalars (R := R) (σ := σ)) (coordinateSection_cover (R := R) (σ := σ))
    (Iso.refl (projectiveSpace R σ))
    (coordinate_sectionsMorphism_identity (R := R) (σ := σ)) n b

end
end PiExponent.ProjectiveO1

end OAI
end Source0833

-- Source: OAI/NumberTheory/PiExponent/Polynomials/GlobalPolynomialCoefficientLaw.lean
section Source0834
/-
Modification notice for the LogTwo project.
Derived from openai/math (Apache-2.0), revision adc7f1241b42e322a6451854ab7e4b4c146bf78a.
Original source: lean/OAI/NumberTheory/PiExponent/Polynomials/GlobalPolynomialCoefficientLaw.lean
Changes: Convert module/import declarations to the Lean 4.34 public module format.
See ../THIRD_PARTY_NOTICES.txt for provenance and the recorded changes.
-/

namespace OAI

noncomputable section
namespace PiExponent.GlobalPolynomialCoefficientLaw
open AlgebraicGeometry CategoryTheory
open PiExponentSeshadri.Geometry PiExponentSeshadri.Frames PiExponentSeshadri.Projective
attribute [local instance] MvPolynomial.gradedAlgebra

def CoefficientLaw {Y : Scheme} {M : Y.Modules} {A : Type} [CommRing A]
    (V : Y.Opens) (e : M.restrict V.ι ≅ structureSheaf V.toScheme)
    (E : Γ(Y,V) ≃+* A) (P : (structureSheaf Y ⟶ M) → A) : Prop :=
  ∀ s, P s = E (V.topIso.hom (coefficient e (restrictSection V.ι s)))

theorem coordinate_law {Y : Scheme} {R σ : Type} [CommRing R]
    (M : Y.Modules) (s : σ → (structureSheaf Y ⟶ M)) (k : R →+* Γ(Y,⊤))
    (hc : (⨆i,PiExponentSeshadri.SectionOpens.isoOpen (s i))=⊤)
    (f : Y ≅ Proj (PolyGrade R σ)) (hf : sectionsMorphism k s hc=f.hom)
    (n : ℕ) (z : σ) :
    CoefficientLaw (PiExponentSeshadri.SectionOpens.isoOpen (s z))
      (coordinatePowerFrame (s z) n) (coordinateSectionRingEquiv M k s hc f hf z)
      (ProjectiveGlobalPolynomials.coordinateChartPolynomial M s k hc f hf n z) :=
  fun b => ProjectiveGlobalPolynomials.coordinateChartPolynomial_coefficient M s k hc f hf n z b

theorem exists_power_frame_of_law {X Y : Scheme.{0}} {A B : Type}
    [CommRing A] [CommRing B] (L : LineBundle Y) (f : X ⟶ Y)
    (φ : Spec (CommRingCat.of A) ⟶ X) [IsOpenImmersion φ]
    (V : Y.Opens) (g : Spec (CommRingCat.of A) ⟶ V.toScheme)
    (hg : φ ≫ f = g ≫ V.ι) (n : ℕ)
    (e : (modulePow Y L.sheaf n).restrict V.ι ≅ structureSheaf V.toScheme)
    (E : Γ(Y,V) ≃+* B) (P : (structureSheaf Y ⟶ modulePow Y L.sheaf n) → B)
    (hP : CoefficientLaw V e E P) (ev : B →+* A)
    (hev : ∀ q, (Scheme.ΓSpecIso (CommRingCat.of A)).hom
      (g.appTop (V.topIso.inv (E.symm q))) = ev q) :
    ∃ F : (modulePow X (L.pullback f).sheaf n).restrict φ ≅ O (Spec (CommRingCat.of A)),
      ∀ s, (Scheme.ΓSpecIso (CommRingCat.of A)).hom
        (coefficient F (restrictSection φ (pullbackPowerSection L f n s))) = ev (P s) := by
  obtain ⟨F, hF⟩ := CompositePullbackFrame.exists_power_frame L f φ V g hg n e
  refine ⟨F, fun s => ?_⟩
  erw [hF s]
  have hcoef : V.topIso.inv (E.symm (P s)) = coefficient e (restrictSection V.ι s) := by
    rw [hP s, RingEquiv.symm_apply_apply]
    exact V.topIso.hom_inv_id_apply _
  rw [← hcoef]
  exact hev (P s)

end PiExponent.GlobalPolynomialCoefficientLaw
end

end OAI
end Source0834

-- Source: OAI/NumberTheory/PiExponent/Geometry/ProjectiveIntrinsicCoefficientLaw.lean
section Source0835
/-
Modification notice for the LogTwo project.
Derived from openai/math (Apache-2.0), revision adc7f1241b42e322a6451854ab7e4b4c146bf78a.
Original source: lean/OAI/NumberTheory/PiExponent/Geometry/ProjectiveIntrinsicCoefficientLaw.lean
Changes: Convert module/import declarations to the Lean 4.34 public module format.
See ../THIRD_PARTY_NOTICES.txt for provenance and the recorded changes.
-/

namespace OAI

namespace PiExponent.ProjectiveIntrinsicCoefficientLaw
noncomputable section
open AlgebraicGeometry CategoryTheory
open PiExponentSeshadri.Geometry PiExponentSeshadri.Frames PiExponentSeshadri.Projective
attribute [local instance] MvPolynomial.gradedAlgebra

structure CoordinateData (R σ : Type) [CommRing R] where
  scheme : Scheme.{0}
  sheaf : scheme.Modules
  sections : σ → (structureSheaf scheme ⟶ sheaf)
  scalars : R →+* Γ(scheme,⊤)
  cover : (⨆ i, PiExponentSeshadri.SectionOpens.isoOpen (sections i)) = ⊤
  projectiveIso : scheme ≅ Proj (PolyGrade R σ)
  projective_eq : sectionsMorphism scalars sections cover = projectiveIso.hom

namespace CoordinateData
variable {R σ : Type} [CommRing R] (D : CoordinateData R σ)

def chartOpen (z : σ) : D.scheme.Opens := PiExponentSeshadri.SectionOpens.isoOpen (D.sections z)

def Sections (n : ℕ) : Type := structureSheaf D.scheme ⟶ modulePow D.scheme D.sheaf n

def Frame (n : ℕ) (z : σ) : Type :=
  (modulePow D.scheme D.sheaf n).restrict (D.chartOpen z).ι ≅
    structureSheaf (D.chartOpen z).toScheme

def frame (n : ℕ) (z : σ) : D.Frame n z := coordinatePowerFrame (D.sections z) n

def ringEquiv (z : σ) : Γ(D.scheme,D.chartOpen z) ≃+* MvPolynomial (ChartVariables z) R :=
  coordinateSectionRingEquiv D.sheaf D.scalars D.sections D.cover D.projectiveIso D.projective_eq z

def polynomial (n : ℕ) (z : σ) : D.Sections n → MvPolynomial (ChartVariables z) R :=
  ProjectiveGlobalPolynomials.coordinateChartPolynomial D.sheaf D.sections D.scalars
    D.cover D.projectiveIso D.projective_eq n z

def Law (n : ℕ) (z : σ) : Prop :=
  GlobalPolynomialCoefficientLaw.CoefficientLaw (D.chartOpen z) (D.frame n z)
    (D.ringEquiv z) (D.polynomial n z)

theorem law (n : ℕ) (z : σ) : D.Law n z :=
  GlobalPolynomialCoefficientLaw.coordinate_law D.sheaf D.sections D.scalars
    D.cover D.projectiveIso D.projective_eq n z

end CoordinateData

attribute [local irreducible] ProjectiveO1.lineBundle ProjectiveO1.coordinateSection
  ProjectiveO1.scalars ProjectiveO1.coordinateCocycle sectionsMorphism
  CoordinateAtlas.morphism atlasOfFramedSections
  CoordinateData.chartOpen CoordinateData.Sections CoordinateData.Frame
  CoordinateData.frame CoordinateData.ringEquiv CoordinateData.polynomial CoordinateData.Law

variable {R σ : Type} [CommRing R]

def intrinsicData : CoordinateData R σ where
  scheme := ProjectiveO1.projectiveSpace R σ
  sheaf := (ProjectiveO1.lineBundle (R := R) (σ := σ)).sheaf
  sections := ProjectiveO1.coordinateSection
  scalars := ProjectiveO1.scalars
  cover := ProjectiveO1.coordinateSection_cover
  projectiveIso := Iso.refl (ProjectiveO1.projectiveSpace R σ)
  projective_eq := ProjectiveO1.coordinate_sectionsMorphism_identity

def intrinsicBundle : LineBundle (intrinsicData (R := R) (σ := σ)).scheme :=
  ProjectiveO1.lineBundle (R := R) (σ := σ)

@[simp] theorem intrinsicBundle_sheaf :
    (intrinsicBundle (R := R) (σ := σ)).sheaf = (intrinsicData (R := R) (σ := σ)).sheaf := rfl

attribute [local semireducible] CoordinateData.Sections CoordinateData.chartOpen
  CoordinateData.polynomial CoordinateData.ringEquiv

theorem intrinsic_polynomial (n : ℕ) (z : σ) :
    (intrinsicData (R := R) (σ := σ)).polynomial n z =
      ProjectiveO1.globalSectionChartPolynomial (R := R) (σ := σ) n z := rfl

theorem intrinsic_ringEquiv (z : σ) :
    (intrinsicData (R := R) (σ := σ)).ringEquiv z =
      WeightedChartRingEvaluation.ambientRingEquiv (R := R) z := rfl

attribute [local irreducible] intrinsicData intrinsicBundle
  CoordinateData.Sections CoordinateData.chartOpen CoordinateData.polynomial CoordinateData.ringEquiv

theorem intrinsic_law (n : ℕ) (z : σ) : (intrinsicData (R := R) (σ := σ)).Law n z :=
  CoordinateData.law _ n z

end
end PiExponent.ProjectiveIntrinsicCoefficientLaw

end OAI
end Source0835

-- Source: OAI/NumberTheory/PiExponent/Geometry/ProjectiveSectionExtension.lean
section Source0836
/-
Modification notice for the LogTwo project.
Derived from openai/math (Apache-2.0), revision adc7f1241b42e322a6451854ab7e4b4c146bf78a.
Original source: lean/OAI/NumberTheory/PiExponent/Geometry/ProjectiveSectionExtension.lean
Changes: Convert module/import declarations to the Lean 4.34 public module format.
See ../THIRD_PARTY_NOTICES.txt for provenance and the recorded changes.
-/

namespace OAI

namespace PiExponent.ProjectiveSectionExtension
noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian
open PiExponentSeshadri.Geometry
open GeometrySupport

variable {X Y : Scheme.{0}}

def quotientPowerRestriction (L : LineBundle Y) (f : X ⟶ Y) (n : ℕ)
    (s : GlobalSections Y (modulePow Y L.sheaf n)) :
    GlobalSections Y ((moduleTwistFunctor L n).obj
      ((Scheme.Modules.pushforward f).obj (structureSheaf X))) :=
  s ≫ (moduleTwistUnitIso L n).inv ≫
    (moduleTwistFunctor L n).map (PiExponentSeshadri.IdealModule.structureMap f)

lemma idealModule_isFinitePresentation [IsLocallyNoetherian Y]
    (f : X ⟶ Y) [IsClosedImmersion f] :
    (PiExponentSeshadri.IdealModule.idealModule f).IsFinitePresentation := by
  let : (PiExponentSeshadri.IdealModule.unit X).IsFinitePresentation :=
    LineBundleCoherent.structureSheaf_isFinitePresentation
  let : (PiExponentSeshadri.IdealModule.unit Y).IsFinitePresentation :=
    LineBundleCoherent.structureSheaf_isFinitePresentation
  let : ((Scheme.Modules.pushforward f).obj
      (PiExponentSeshadri.IdealModule.unit X)).IsQuasicoherent :=
    (SheafOfModules.IsFinitePresentation.exists_quasicoherentData
      ((Scheme.Modules.pushforward f).obj
        (PiExponentSeshadri.IdealModule.unit X))).choose.isQuasicoherent
  exact FiniteGlobalPresentation.kernel_isFinitePresentation
    (PiExponentSeshadri.IdealModule.structureMap f)

theorem quotientPowerRestriction_surjective_of_h1_zero
    (L : LineBundle Y) (f : X ⟶ Y) [IsClosedImmersion f] (n : ℕ)
    (hzero : ∀ x : cohomology
      ((moduleTwistFunctor L n).obj (PiExponentSeshadri.IdealModule.idealModule f)) 1, x = 0) :
    Function.Surjective (quotientPowerRestriction L f n) := by
  let S := ShortComplex.mk (PiExponentSeshadri.IdealModule.inclusion f)
    (PiExponentSeshadri.IdealModule.structureMap f) (kernel.condition _)
  have hS : S.ShortExact := PiExponentSeshadri.IdealModule.closedSequence_exact f
  have hsurj := SerreSectionLifting.globalSections_surjective_of_h1_zero
    (S.map (moduleTwistFunctor L n)) (moduleTwistFunctor_shortExact L n S hS) hzero
  intro s
  obtain ⟨t, ht⟩ := hsurj s
  refine ⟨t ≫ (moduleTwistUnitIso L n).hom, ?_⟩
  change t ≫ (moduleTwistFunctor L n).map
    (PiExponentSeshadri.IdealModule.structureMap f) = s at ht
  change (t ≫ (moduleTwistUnitIso L n).hom) ≫ (moduleTwistUnitIso L n).inv ≫ _ = s
  erw [Category.assoc, Iso.hom_inv_id_assoc]
  exact ht

theorem eventual_projective_quotientPowerRestriction_surjective
    {R σ : Type} [CommRing R] [IsNoetherianRing R] [Fintype σ] [Nonempty σ]
    (f : X ⟶ ProjectiveO1.projectiveSpace R σ) [IsClosedImmersion f] :
    ∃ N, ∀ n, N ≤ n → Function.Surjective
      (quotientPowerRestriction (ProjectiveO1.lineBundle (R := R) (σ := σ)) f n) := by
  let := idealModule_isFinitePresentation f
  obtain ⟨N, hN⟩ := ProjectiveO1.serre_vanishing R σ
    (PiExponentSeshadri.IdealModule.idealModule f)
  exact ⟨N, fun n hn => quotientPowerRestriction_surjective_of_h1_zero
    (ProjectiveO1.lineBundle (R := R) (σ := σ)) f n (hN n hn 1 (by decide))⟩

end
end PiExponent.ProjectiveSectionExtension

end OAI
end Source0836

-- Source: OAI/NumberTheory/PiExponent/Geometry/ProjectiveSectionPullback.lean
section Source0837
/-
Modification notice for the LogTwo project.
Derived from openai/math (Apache-2.0), revision adc7f1241b42e322a6451854ab7e4b4c146bf78a.
Original source: lean/OAI/NumberTheory/PiExponent/Geometry/ProjectiveSectionPullback.lean
Changes: Convert module/import declarations to the Lean 4.34 public module format.
See ../THIRD_PARTY_NOTICES.txt for provenance and the recorded changes.
-/

namespace OAI

noncomputable section
namespace PiExponent.ProjectiveSectionExtension
open AlgebraicGeometry CategoryTheory
open PiExponentSeshadri.Geometry
open PiExponent.GeometrySupport
variable {X Y : Scheme.{0}}

def globalPushEquiv (f : X ⟶ Y) (M : X.Modules) :
    GlobalSections X M ≃ GlobalSections Y ((Scheme.Modules.pushforward f).obj M) :=
  Equiv.ofBijective (fun s => PiExponentSeshadri.IdealModule.structureMap f ≫
    (Scheme.Modules.pushforward f).map s)
    (ClosedImmersionSerreTransfer.globalHom_push_bijective f M)

def quotientPowerIso (L : LineBundle Y) (f : X ⟶ Y) (n : ℕ) :
    (moduleTwistFunctor L n).obj ((Scheme.Modules.pushforward f).obj (structureSheaf X)) ≅
      (Scheme.Modules.pushforward f).obj (modulePow X (L.pullback f).sheaf n) :=
  (ProjectionFormula.twistIso f (structureSheaf X) L n).symm ≪≫
    (Scheme.Modules.pushforward f).mapIso (moduleTwistUnitIso (L.pullback f) n)

def quotientSectionsEquiv (L : LineBundle Y) (f : X ⟶ Y) (n : ℕ) :
    GlobalSections Y ((moduleTwistFunctor L n).obj
      ((Scheme.Modules.pushforward f).obj (structureSheaf X))) ≃
    GlobalSections X (modulePow X (L.pullback f).sheaf n) :=
  (Iso.homCongr (Iso.refl (structureSheaf Y)) (quotientPowerIso L f n)).trans
    (globalPushEquiv f _).symm

theorem quotientSectionsEquiv_restriction (L : LineBundle Y) (f : X ⟶ Y)
    (n : ℕ) (s : GlobalSections Y (modulePow Y L.sheaf n)) :
    quotientSectionsEquiv L f n (quotientPowerRestriction L f n s) =
      pullbackPowerSection L f n s := by
  apply (globalPushEquiv f _).injective
  change globalPushEquiv f _ ((globalPushEquiv f _).symm
    (quotientPowerRestriction L f n s ≫ (quotientPowerIso L f n).hom)) = _
  rw [Equiv.apply_symm_apply]
  change (s ≫ (moduleTwistUnitIso L n).inv ≫
    (moduleTwistFunctor L n).map (PiExponentSeshadri.IdealModule.structureMap f)) ≫
      (ProjectionFormula.twistIso f (structureSheaf X) L n).inv ≫
        (Scheme.Modules.pushforward f).map (moduleTwistUnitIso (L.pullback f) n).hom = _
  change _ = PiExponentSeshadri.IdealModule.structureMap f ≫
    (Scheme.Modules.pushforward f).map (pullbackPowerSection L f n s)
  erw [Category.assoc, Category.assoc]
  simpa only [PiExponentSeshadri.Frames.O, structureSheaf,
    PiExponentSeshadri.IdealModule.unit] using! ClosedRestrictionTensor.section_restriction_eq f L n s

theorem eventual_projective_pullbackPowerSection_surjective
    {R σ : Type} [CommRing R] [IsNoetherianRing R] [Fintype σ] [Nonempty σ]
    (f : X ⟶ ProjectiveO1.projectiveSpace R σ) [IsClosedImmersion f] :
    ∃ N, ∀ n, N ≤ n → Function.Surjective
      (pullbackPowerSection (ProjectiveO1.lineBundle (R := R) (σ := σ)) f n) := by
  obtain ⟨N, hN⟩ := eventual_projective_quotientPowerRestriction_surjective f
  refine ⟨N, fun n hn t => ?_⟩
  obtain ⟨s, hs⟩ := hN n hn ((quotientSectionsEquiv _ f n).symm t)
  refine ⟨s, ?_⟩
  rw [← quotientSectionsEquiv_restriction, hs, Equiv.apply_symm_apply]

theorem eventual_projective_homogeneous_extension
    {R σ : Type} [CommRing R] [IsNoetherianRing R] [Fintype σ] [Nonempty σ]
    (f : X ⟶ ProjectiveO1.projectiveSpace R σ) [IsClosedImmersion f] :
    ∃ N, ∀ n, N ≤ n →
      ∀ t : GlobalSections X (modulePow X
        ((ProjectiveO1.lineBundle (R := R) (σ := σ)).pullback f).sheaf n),
      ∃ s : GlobalSections (ProjectiveO1.projectiveSpace R σ)
          (modulePow _ (ProjectiveO1.lineBundle (R := R) (σ := σ)).sheaf n),
        ∃ p : MvPolynomial.homogeneousSubmodule σ R n,
          pullbackPowerSection (ProjectiveO1.lineBundle (R := R) (σ := σ)) f n s = t ∧
          ∀ i, PiExponentSeshadri.Projective.dehomogenize i p.val =
            ProjectiveO1.globalSectionChartPolynomial n i s := by
  obtain ⟨N, hN⟩ := eventual_projective_pullbackPowerSection_surjective f
  refine ⟨N, fun n hn t => ?_⟩
  obtain ⟨s, hs⟩ := hN n hn t
  obtain ⟨p, hp, _⟩ := ProjectiveO1.globalSection_homogeneous_polynomial n s
  exact ⟨s, p, hs, hp⟩

end PiExponent.ProjectiveSectionExtension
end

end OAI
end Source0837

-- Source: OAI/NumberTheory/PiExponent/Jets/AffineJetSupport.lean
section Source0838
/-
Modification notice for the LogTwo project.
Derived from openai/math (Apache-2.0), revision adc7f1241b42e322a6451854ab7e4b4c146bf78a.
Original source: lean/OAI/NumberTheory/PiExponent/Jets/AffineJetSupport.lean
Changes: Convert module/import declarations to the Lean 4.34 public module format.
See ../THIRD_PARTY_NOTICES.txt for provenance and the recorded changes.
-/

namespace OAI

noncomputable section
namespace PiExponent.AffineJetSupport
open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite
open PiExponentSeshadri.Geometry PiExponentSeshadri.Frames
open PiExponent.BlowupJetSurjectivity
variable {X Y : Scheme}

private theorem map_bijective_of_eq {T : Type*} [Category T] [Quiver.IsThin T]
    (F : Tᵒᵖ ⥤ AddCommGrpCat) {U V : T}
    (h : U = V) (i : U ⟶ V) : Function.Bijective (F.map i.op) := by
  subst V
  have hi : i = 𝟙 U := Subsingleton.elim _ _
  subst i
  rw [op_id]
  erw [F.map_id]
  exact Function.bijective_id

theorem restriction_surjective_of_iso {M N : X.Modules} (e : M ≅ N) (U : X.Opens)
    (h : Function.Surjective (N.presheaf.map (homOfLE (le_top : U ≤ ⊤)).op)) :
    Function.Surjective (M.presheaf.map (homOfLE (le_top : U ≤ ⊤)).op) := by
  intro s
  obtain ⟨t, ht⟩ := h (e.hom.app U s)
  obtain ⟨r, hr⟩ := (ConcreteCategory.bijective_of_isIso (e.hom.app ⊤)).surjective t
  refine ⟨r, (ConcreteCategory.bijective_of_isIso (e.hom.app U)).injective ?_⟩
  have hn := CategoryTheory.congr_fun
    (e.hom.mapPresheaf.naturality (homOfLE (le_top : U ≤ ⊤)).op) r
  change e.hom.app U (M.presheaf.map _ r) = N.presheaf.map _ (e.hom.app ⊤ r) at hn
  rw [hn, hr, ht]

theorem pushforward_restriction_bijective (f : Y ⟶ X) (M : Y.Modules) (U : X.Opens)
    (hU : f ⁻¹ᵁ U = ⊤) :
    Function.Bijective (((Scheme.Modules.pushforward f).obj M).presheaf.map
      (homOfLE (le_top : U ≤ ⊤)).op) := by
  rw [Scheme.Modules.pushforward_obj_presheaf_map]
  have he : f ⁻¹ᵁ U = f ⁻¹ᵁ (⊤ : X.Opens) := by simp [hU]
  exact map_bijective_of_eq M.presheaf he _

theorem subscheme_preimage_eq_top (I : X.IdealSheafData) (U : X.Opens)
    (hs : (I.support : Set X) ⊆ U) : I.subschemeι ⁻¹ᵁ U = ⊤ := by
  apply top_unique
  intro x hx
  apply hs
  rw [← I.range_subschemeι]
  exact ⟨x, rfl⟩

theorem twistedQuotient_restriction_surjective (I : X.IdealSheafData)
    (A : LineBundle X) (n : ℕ) (U : X.Opens)
    (hs : (I.support : Set X) ⊆ U) :
    Function.Surjective (((moduleTwistFunctor A n).obj (jetQuotient I)).presheaf.map
      (homOfLE (le_top : U ≤ ⊤)).op) := by
  apply restriction_surjective_of_iso
    (ProjectionFormula.twistIso I.subschemeι (PiExponentSeshadri.IdealModule.unit I.subscheme) A n).symm U
  exact (pushforward_restriction_bijective I.subschemeι _ U
    (subscheme_preimage_eq_top I U hs)).surjective

def restrictionSectionsIso (M : X.Modules) (U : X.Opens) :
    Γ(M.restrict U.ι, ⊤) ≅ Γ(M,U) :=
  M.restrictAppIso U.ι ⊤ ≪≫ M.presheaf.mapIso (eqToIso U.ι_image_top.symm).op

def sectionsIso {M N : X.Modules} (e : M ≅ N) (U : X.Opens) : Γ(M,U) ≅ Γ(N,U) :=
  ((Scheme.Modules.toPresheaf X).mapIso e).app (op U)

def localQuotientEquiv (I : X.IdealSheafData) (A : LineBundle X) (n : ℕ)
    (U : X.affineOpens) (e : A.sheaf.restrict U.1.ι ≅ structureSheaf U.1.toScheme) :
    Γ((moduleTwistFunctor A n).obj (jetQuotient I), U.1) ≃
      (Γ(X,U.1) ⧸ I.ideal U) :=
  (restrictionSectionsIso ((moduleTwistFunctor A n).obj (jetQuotient I)) U.1).symm.addCommGroupIsoToAddEquiv.toEquiv |>.trans
    ((sectionsIso ((moduleTwistRestrictFrame A U.1 e n).app (jetQuotient I)) ⊤).addCommGroupIsoToAddEquiv.toEquiv.trans
      ((restrictionSectionsIso (jetQuotient I) U.1).addCommGroupIsoToAddEquiv.toEquiv.trans
        (I.subschemeObjIso U).commRingCatIsoToRingEquiv.toEquiv))

def globalQuotientValue (I : X.IdealSheafData) (A : LineBundle X) (n : ℕ)
    (U : X.affineOpens) (e : A.sheaf.restrict U.1.ι ≅ structureSheaf U.1.toScheme)
    (s : GlobalSections X ((moduleTwistFunctor A n).obj (jetQuotient I))) :
    Γ(X,U.1) ⧸ I.ideal U :=
  localQuotientEquiv I A n U e
    (((moduleTwistFunctor A n).obj (jetQuotient I)).presheaf.map
      (homOfLE (le_top : U.1 ≤ ⊤)).op
      (moduleSectionEquiv ((moduleTwistFunctor A n).obj (jetQuotient I)) s))

theorem globalQuotientValue_surjective (I : X.IdealSheafData) (A : LineBundle X) (n : ℕ)
    (U : X.affineOpens) (e : A.sheaf.restrict U.1.ι ≅ structureSheaf U.1.toScheme)
    (hs : (I.support : Set X) ⊆ U.1) :
    Function.Surjective (globalQuotientValue I A n U e) :=
  (localQuotientEquiv I A n U e).surjective.comp
    ((twistedQuotient_restriction_surjective I A n U.1 hs).comp
      (moduleSectionEquiv ((moduleTwistFunctor A n).obj (jetQuotient I))).surjective)

end PiExponent.AffineJetSupport
end

end OAI
end Source0838

-- Source: OAI/NumberTheory/PiExponent/Jets/AffineJetQuotient.lean
section Source0839
/-
Modification notice for the LogTwo project.
Derived from openai/math (Apache-2.0), revision adc7f1241b42e322a6451854ab7e4b4c146bf78a.
Original source: lean/OAI/NumberTheory/PiExponent/Jets/AffineJetQuotient.lean
Changes: Convert module/import declarations to the Lean 4.34 public module format.
See ../THIRD_PARTY_NOTICES.txt for provenance and the recorded changes.
-/

namespace OAI

noncomputable section
namespace PiExponent.AffineJetQuotient
open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite
open PiExponentSeshadri.Geometry PiExponentSeshadri.Frames
open PiExponent.BlowupJetSurjectivity PiExponent.AffineJetSupport
variable {X : Scheme}

@[reassoc] theorem restrictionSectionsIso_natural {M N : X.Modules}
    (f : M ⟶ N) (U : X.Opens) :
    ((Scheme.Modules.restrictFunctor U.ι).map f).app ⊤ ≫
        (restrictionSectionsIso N U).hom =
      (restrictionSectionsIso M U).hom ≫ f.app U := by
  change f.app (U.ι ''ᵁ ⊤) ≫ N.presheaf.map (eqToHom U.ι_image_top.symm).op =
    M.presheaf.map (eqToHom U.ι_image_top.symm).op ≫ f.app U
  exact (f.mapPresheaf.naturality (eqToHom U.ι_image_top.symm).op).symm

def untwistSectionsIso (A : LineBundle X) (U : X.Opens)
    (e : A.sheaf.restrict U.ι ≅ structureSheaf U.toScheme) (n : ℕ) (M : X.Modules) :
    Γ((moduleTwistFunctor A n).obj M,U) ≅ Γ(M,U) :=
  (restrictionSectionsIso ((moduleTwistFunctor A n).obj M) U).symm ≪≫
    sectionsIso ((moduleTwistRestrictFrame A U e n).app M) ⊤ ≪≫
    restrictionSectionsIso M U

@[reassoc] theorem untwistSectionsIso_natural (A : LineBundle X) (U : X.Opens)
    (e : A.sheaf.restrict U.ι ≅ structureSheaf U.toScheme) (n : ℕ)
    {M N : X.Modules} (f : M ⟶ N) :
    ((moduleTwistFunctor A n).map f).app U ≫ (untwistSectionsIso A U e n N).hom =
      (untwistSectionsIso A U e n M).hom ≫ f.app U := by
  have hn := congrArg (fun g => g.app ⊤)
    ((moduleTwistRestrictFrame A U e n).hom.naturality f)
  simp only [Scheme.Modules.Hom.comp_app] at hn
  change ((Scheme.Modules.restrictFunctor U.ι).map ((moduleTwistFunctor A n).map f)).app ⊤ ≫
      ((moduleTwistRestrictFrame A U e n).app N).hom.app ⊤ =
    ((moduleTwistRestrictFrame A U e n).app M).hom.app ⊤ ≫
      ((Scheme.Modules.restrictFunctor U.ι).map f).app ⊤ at hn
  apply (cancel_epi (restrictionSectionsIso ((moduleTwistFunctor A n).obj M) U).hom).mp
  simp only [untwistSectionsIso, Iso.trans_hom, Iso.symm_hom, Category.assoc]
  rw [← restrictionSectionsIso_natural_assoc]
  simp only [Iso.hom_inv_id_assoc]
  change _ ≫ ((moduleTwistRestrictFrame A U e n).app N).hom.app ⊤ ≫ _ = _
  rw [← Category.assoc, hn, Category.assoc, restrictionSectionsIso_natural]
  rfl

theorem localQuotientEquiv_apply (I : X.IdealSheafData) (A : LineBundle X) (n : ℕ)
    (U : X.affineOpens) (e : A.sheaf.restrict U.1.ι ≅ structureSheaf U.1.toScheme)
    (s : Γ((moduleTwistFunctor A n).obj (jetQuotient I),U.1)) :
    localQuotientEquiv I A n U e s =
      (I.subschemeObjIso U).hom ((untwistSectionsIso A U.1 e n (jetQuotient I)).hom s) := rfl

def globalSectionCoefficient (A : LineBundle X) (n : ℕ) (U : X.affineOpens)
    (e : A.sheaf.restrict U.1.ι ≅ structureSheaf U.1.toScheme)
    (s : GlobalSections X (modulePow X A.sheaf n)) : Γ(X,U.1) :=
  (untwistSectionsIso A U.1 e n (structureSheaf X)).hom
    ((s ≫ (moduleTwistUnitIso A n).inv).app U.1 (1 : Γ(X,U.1)))

theorem globalQuotientValue_jetRestriction (I : X.IdealSheafData)
    (A : LineBundle X) (n : ℕ) (U : X.affineOpens)
    (e : A.sheaf.restrict U.1.ι ≅ structureSheaf U.1.toScheme)
    (s : GlobalSections X (modulePow X A.sheaf n)) :
    globalQuotientValue (I^n) A n U e (jetRestriction I A n s) =
      Ideal.Quotient.mk ((I^n).ideal U) (globalSectionCoefficient A n U e s) := by
  unfold globalQuotientValue
  erw [moduleSectionEquiv_apply, section_value_natural, localQuotientEquiv_apply]
  let q := PiExponentSeshadri.IdealModule.structureMap (I^n).subschemeι
  let t := s ≫ (moduleTwistUnitIso A n).inv
  change ((I^n).subschemeObjIso U).hom
    ((untwistSectionsIso A U.1 e n (jetQuotient (I^n))).hom
      (((moduleTwistFunctor A n).map q).app U.1 (t.app U.1 (1 : Γ(X,U.1))))) = _
  have hn := CategoryTheory.congr_fun (untwistSectionsIso_natural A U.1 e n q)
    (t.app U.1 (1 : Γ(X,U.1)))
  change (untwistSectionsIso A U.1 e n (jetQuotient (I^n))).hom
      (((moduleTwistFunctor A n).map q).app U.1 (t.app U.1 (1 : Γ(X,U.1)))) =
    q.app U.1 ((untwistSectionsIso A U.1 e n (structureSheaf X)).hom (t.app U.1 (1 : Γ(X,U.1)))) at hn
  rw [hn]
  change ((I^n).subschemeObjIso U).hom
    ((I^n).subschemeι.app U.1 (globalSectionCoefficient A n U e s)) = _
  rw [Scheme.IdealSheafData.subschemeι_app]
  exact ((I^n).subschemeObjIso U).inv_hom_id_apply _

theorem coefficient_quotient_surjective_of_jetRestriction
    (I : X.IdealSheafData) (A : LineBundle X) (n : ℕ) (U : X.affineOpens)
    (e : A.sheaf.restrict U.1.ι ≅ structureSheaf U.1.toScheme)
    (hs : ((I^n).support : Set X) ⊆ U.1)
    (hjet : Function.Surjective (jetRestriction I A n)) :
    Function.Surjective (fun s : GlobalSections X (modulePow X A.sheaf n) =>
      Ideal.Quotient.mk ((I^n).ideal U) (globalSectionCoefficient A n U e s)) := by
  intro q
  obtain ⟨t, ht⟩ := globalQuotientValue_surjective (I^n) A n U e hs q
  obtain ⟨s, rfl⟩ := hjet t
  exact ⟨s, (globalQuotientValue_jetRestriction I A n U e s).symm.trans ht⟩

end PiExponent.AffineJetQuotient
end

end OAI
end Source0839

-- Source: OAI/NumberTheory/PiExponent/Jets/AffineJetPolynomial.lean
section Source0840
/-
Modification notice for the LogTwo project.
Derived from openai/math (Apache-2.0), revision adc7f1241b42e322a6451854ab7e4b4c146bf78a.
Original source: lean/OAI/NumberTheory/PiExponent/Jets/AffineJetPolynomial.lean
Changes: Convert module/import declarations to the Lean 4.34 public module format.
See ../THIRD_PARTY_NOTICES.txt for provenance and the recorded changes.
-/

namespace OAI

noncomputable section
namespace PiExponent.AffineJetPolynomial
open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite
open PiExponentSeshadri.Geometry PiExponentSeshadri.Frames
open PiExponent.BlowupJetSurjectivity PiExponent.AffineJetSupport PiExponent.AffineJetQuotient
open PiExponent.ExceptionalAffineChart
open PiExponentSeshadri.IdealPullback
variable {X : Scheme} {R : Type} [CommRing R]

theorem map_ideal_functionsOnOpenEquiv (I : X.IdealSheafData)
    (j : Spec (CommRingCat.of R) ⟶ X) [IsOpenImmersion j]
    (J : Ideal R) (hJ : I.comap j = specIdeal J) :
    (I.ideal (chartOpen j)).map (functionsOnOpenEquiv j).toRingHom = J := by
  let : IsAffine j.opensRange.toScheme := isAffineOpen_opensRange j
  change (I.ideal (chartOpen j)).map
    ((Scheme.ΓSpecIso (CommRingCat.of R)).hom.hom.comp
      (j.isoOpensRange.hom.appTop.hom.comp (chartOpen j).1.topIso.inv.hom)) = J
  dsimp +instances only [chartOpen]
  rw [← Ideal.map_map, ← Ideal.map_map]
  erw [← comap_ι_top I (chartOpen j)]
  erw [← comap_top (I.comap j.opensRange.ι) j.isoOpensRange.hom]
  rw [← Scheme.IdealSheafData.comap_comp]
  change ((I.comap (j.isoOpensRange.hom ≫ j.opensRange.ι)).ideal
    ⟨⊤, isAffineOpen_top _⟩).map (Scheme.ΓSpecIso (CommRingCat.of R)).hom.hom = J
  rw [j.isoOpensRange_hom_ι, hJ, specIdeal_top, Ideal.map_map]
  have he : (Scheme.ΓSpecIso (CommRingCat.of R)).hom.hom.comp
      (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom = RingHom.id _ := by
    apply RingHom.ext
    intro r
    exact (Scheme.ΓSpecIso (CommRingCat.of R)).inv_hom_id_apply r
  rw [he, Ideal.map_id]

def polynomialCoefficient (j : Spec (CommRingCat.of R) ⟶ X) [IsOpenImmersion j]
    (A : LineBundle X) (n : ℕ)
    (e : A.sheaf.restrict (chartOpen j).1.ι ≅ structureSheaf (chartOpen j).1.toScheme)
    (s : GlobalSections X (modulePow X A.sheaf n)) : R :=
  functionsOnOpenEquiv j (globalSectionCoefficient A n (chartOpen j) e s)

theorem polynomialQuotient_surjective_of_jetRestriction
    (I : X.IdealSheafData) (A : LineBundle X) (n : ℕ)
    (j : Spec (CommRingCat.of R) ⟶ X) [IsOpenImmersion j]
    (e : A.sheaf.restrict (chartOpen j).1.ι ≅ structureSheaf (chartOpen j).1.toScheme)
    (J : Ideal R) (hJ : I.comap j = specIdeal J)
    (hs : ((I^n).support : Set X) ⊆ j.opensRange)
    (hjet : Function.Surjective (jetRestriction I A n)) :
    Function.Surjective (fun s : GlobalSections X (modulePow X A.sheaf n) =>
      Ideal.Quotient.mk (J^n) (polynomialCoefficient j A n e s)) := by
  have hpow : (I^n).comap j = specIdeal (J^n) := by
    rw [comap_pow, hJ, specIdeal_pow]
  have hmap := map_ideal_functionsOnOpenEquiv (I^n) j (J^n) hpow
  have hsource := coefficient_quotient_surjective_of_jetRestriction I A n (chartOpen j) e hs hjet
  intro q
  obtain ⟨P, rfl⟩ := Ideal.Quotient.mk_surjective q
  obtain ⟨s, hs⟩ := hsource (Ideal.Quotient.mk ((I^n).ideal (chartOpen j))
    ((functionsOnOpenEquiv j).symm P))
  refine ⟨s, Ideal.Quotient.eq.mpr ?_⟩
  have hs' := (Ideal.Quotient.eq (R := Γ(X,(chartOpen j).1))
    (I := (I^n).ideal (chartOpen j))).mp hs
  have hm := Ideal.mem_map_of_mem (functionsOnOpenEquiv j).toRingHom hs'
  erw [hmap] at hm
  let c : Γ(X,j.opensRange) := globalSectionCoefficient A n (chartOpen j) e s
  change (functionsOnOpenEquiv j) (c - (functionsOnOpenEquiv j).symm P) ∈ J^n at hm
  rw [(functionsOnOpenEquiv j).map_sub] at hm
  simpa only [RingEquiv.apply_symm_apply, polynomialCoefficient, c] using hm

end PiExponent.AffineJetPolynomial
end

end OAI
end Source0840

-- Source: OAI/NumberTheory/PiExponent/Jets/AffineJetCoefficientInterface.lean
section Source0841
/-
Modification notice for the LogTwo project.
Derived from openai/math (Apache-2.0), revision adc7f1241b42e322a6451854ab7e4b4c146bf78a.
Original source: lean/OAI/NumberTheory/PiExponent/Jets/AffineJetCoefficientInterface.lean
Changes: Convert module/import declarations to the Lean 4.34 public module format.
See ../THIRD_PARTY_NOTICES.txt for provenance and the recorded changes.
-/

namespace OAI

noncomputable section
namespace PiExponent.AffineJetCoefficientInterface
open AlgebraicGeometry CategoryTheory
open PiExponentSeshadri.Geometry
open PiExponent.ExceptionalAffineChart
variable {X : Scheme} {R : Type} [CommRing R]
variable (j : Spec (CommRingCat.of R) ⟶ X) [IsOpenImmersion j]
variable (A : LineBundle X)

def Frame : Type := A.sheaf.restrict (chartOpen j).1.ι ≅ structureSheaf (chartOpen j).1.toScheme

def Sections (n : ℕ) : Type := GlobalSections X (modulePow X A.sheaf n)

def coefficient (n : ℕ) (e : Frame j A) : Sections A n → R :=
  AffineJetPolynomial.polynomialCoefficient j A n e

theorem coefficient_eq (n : ℕ) (e : Frame j A) (s : Sections A n) :
    coefficient j A n e s = AffineJetPolynomial.polynomialCoefficient j A n e s := rfl

end PiExponent.AffineJetCoefficientInterface
end

end OAI
end Source0841

-- Source: OAI/NumberTheory/PiExponent/Geometry/ProjectiveSectionInterface.lean
section Source0842
/-
Modification notice for the LogTwo project.
Derived from openai/math (Apache-2.0), revision adc7f1241b42e322a6451854ab7e4b4c146bf78a.
Original source: lean/OAI/NumberTheory/PiExponent/Geometry/ProjectiveSectionInterface.lean
Changes: Convert module/import declarations to the Lean 4.34 public module format.
See ../THIRD_PARTY_NOTICES.txt for provenance and the recorded changes.
-/

namespace OAI

namespace PiExponent.ProjectiveSectionInterface
noncomputable section
open AlgebraicGeometry CategoryTheory
open PiExponentSeshadri.Geometry
open PiExponent.AffineJetCoefficientInterface

variable {X Y : Scheme.{0}}

def sectionHom (L : LineBundle X) (n : ℕ) :
    Sections L n → GlobalSections X (modulePow X L.sheaf n) := fun s => s

def ofSectionHom (L : LineBundle X) (n : ℕ) :
    GlobalSections X (modulePow X L.sheaf n) → Sections L n := fun s => s

@[simp]
theorem sectionHom_ofSectionHom (L : LineBundle X) (n : ℕ)
    (s : GlobalSections X (modulePow X L.sheaf n)) :
    sectionHom L n (ofSectionHom L n s) = s := rfl

@[simp]
theorem ofSectionHom_sectionHom (L : LineBundle X) (n : ℕ) (s : Sections L n) :
    ofSectionHom L n (sectionHom L n s) = s := rfl

theorem sectionHom_injective (L : LineBundle X) (n : ℕ) :
    Function.Injective (sectionHom L n) := fun _ _ h => h

def pullback (L : LineBundle Y) (f : X ⟶ Y) (n : ℕ) :
    Sections L n → Sections (L.pullback f) n := fun s =>
  ofSectionHom (L.pullback f) n (pullbackPowerSection L f n (sectionHom L n s))

@[simp]
theorem sectionHom_pullback (L : LineBundle Y) (f : X ⟶ Y) (n : ℕ)
    (s : Sections L n) :
    sectionHom (L.pullback f) n (pullback L f n s) =
      pullbackPowerSection L f n (sectionHom L n s) := rfl

attribute [local irreducible] AffineJetCoefficientInterface.Frame
  AffineJetCoefficientInterface.Sections

theorem eventual_homogeneous_extension
    {R σ : Type} [CommRing R] [IsNoetherianRing R] [Fintype σ] [Nonempty σ]
    (f : X ⟶ ProjectiveO1.projectiveSpace R σ) [IsClosedImmersion f] :
    ∃ N, ∀ n, N ≤ n →
      ∀ s : Sections ((ProjectiveO1.lineBundle (R := R) (σ := σ)).pullback f) n,
      ∃ t : Sections (ProjectiveO1.lineBundle (R := R) (σ := σ)) n,
      ∃ p : MvPolynomial.homogeneousSubmodule σ R n,
        pullback (ProjectiveO1.lineBundle (R := R) (σ := σ)) f n t = s ∧
        ∀ z, PiExponentSeshadri.Projective.dehomogenize z p.val =
          ProjectiveO1.globalSectionChartPolynomial n z
            (sectionHom (ProjectiveO1.lineBundle (R := R) (σ := σ)) n t) := by
  obtain ⟨N, hN⟩ := ProjectiveSectionExtension.eventual_projective_homogeneous_extension f
  refine ⟨N, fun n hn s => ?_⟩
  obtain ⟨t, p, ht, hp⟩ := hN n hn
    (sectionHom ((ProjectiveO1.lineBundle (R := R) (σ := σ)).pullback f) n s)
  refine ⟨ofSectionHom (ProjectiveO1.lineBundle (R := R) (σ := σ)) n t, p, ?_, ?_⟩
  · apply sectionHom_injective ((ProjectiveO1.lineBundle (R := R) (σ := σ)).pullback f) n
    rw [sectionHom_pullback, sectionHom_ofSectionHom, ht]
  · simpa only [sectionHom_ofSectionHom] using hp

end
end PiExponent.ProjectiveSectionInterface

end OAI
end Source0842

-- Source: OAI/NumberTheory/PiExponent/Jets/AffineJetCoefficientFrame.lean
section Source0843
/-
Modification notice for the LogTwo project.
Derived from openai/math (Apache-2.0), revision adc7f1241b42e322a6451854ab7e4b4c146bf78a.
Original source: lean/OAI/NumberTheory/PiExponent/Jets/AffineJetCoefficientFrame.lean
Changes: Convert module/import declarations to the Lean 4.34 public module format.
See ../THIRD_PARTY_NOTICES.txt for provenance and the recorded changes.
-/

namespace OAI

noncomputable section
namespace PiExponent.AffineJetCoefficientFrame
open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite
open PiExponentSeshadri.Geometry PiExponentSeshadri.Frames
open PiExponent.AffineJetSupport PiExponent.AffineJetQuotient
variable {X : Scheme}

def untwistPowerFrame (A : LineBundle X) (U : X.Opens)
    (e : A.sheaf.restrict U.ι ≅ structureSheaf U.toScheme) (n : ℕ) :
    (modulePow X A.sheaf n).restrict U.ι ≅ structureSheaf U.toScheme :=
  (Scheme.Modules.restrictFunctor U.ι).mapIso (moduleTwistUnitIso A n).symm ≪≫
    (moduleTwistRestrictFrame A U e n).app (structureSheaf X) ≪≫
    Scheme.Modules.restrictUnitIso U.ι

lemma restrictionSectionsIso_restrict_value {M : X.Modules}
    (s : O X ⟶ M) (U : X.Opens) :
    (restrictionSectionsIso M U).inv (s.app U (1 : Γ(X,U))) =
      (restrictSection U.ι s).app ⊤ (1 : Γ(U.toScheme,⊤)) := by
  have h : (restrictionSectionsIso M U).hom
      ((restrictSection U.ι s).app ⊤ (1 : Γ(U.toScheme,⊤))) =
      s.app U (1 : Γ(X,U)) := openSectionEquiv_restrict s U
  rw [← h]
  exact (restrictionSectionsIso M U).hom_inv_id_apply _

lemma restrictionSectionsIso_unit (U : X.Opens)
    (t : Γ((structureSheaf X).restrict U.ι,⊤)) :
    (restrictionSectionsIso (structureSheaf X) U).hom t =
      U.topIso.hom ((Scheme.Modules.restrictUnitIso U.ι).hom.app ⊤ t) := by
  change U.topIso.hom t = U.topIso.hom ((U.ι.appIso ⊤).hom t)
  rw [U.ι_appIso]
  rfl

theorem globalSectionCoefficient_eq (A : LineBundle X) (n : ℕ) (U : X.affineOpens)
    (e : A.sheaf.restrict U.1.ι ≅ structureSheaf U.1.toScheme)
    (s : GlobalSections X (modulePow X A.sheaf n)) :
    globalSectionCoefficient A n U e s =
      U.1.topIso.hom (coefficient (untwistPowerFrame A U.1 e n)
        (restrictSection U.1.ι s)) := by
  change (restrictionSectionsIso (structureSheaf X) U.1).hom
      (((moduleTwistRestrictFrame A U.1 e n).app (structureSheaf X)).hom.app ⊤
        ((restrictionSectionsIso ((moduleTwistFunctor A n).obj (structureSheaf X)) U.1).inv
          ((s ≫ (moduleTwistUnitIso A n).inv).app U.1 (1 : Γ(X,U.1))))) =
    U.1.topIso.hom ((Scheme.Modules.restrictUnitIso U.1.ι).hom.app ⊤
      (((moduleTwistRestrictFrame A U.1 e n).app (structureSheaf X)).hom.app ⊤
        ((restrictSection U.1.ι (s ≫ (moduleTwistUnitIso A n).inv)).app ⊤
          (1 : Γ(U.1.toScheme,⊤)))))
  exact (congrArg (fun t => (restrictionSectionsIso (structureSheaf X) U.1).hom
      (((moduleTwistRestrictFrame A U.1 e n).app (structureSheaf X)).hom.app ⊤ t))
    (restrictionSectionsIso_restrict_value (s ≫ (moduleTwistUnitIso A n).inv) U.1)).trans
      (restrictionSectionsIso_unit U.1 _)

open PiExponent.ExceptionalAffineChart PiExponent.AffineJetPolynomial
variable {R : Type} [CommRing R]

def polynomialPowerFrame (j : Spec (CommRingCat.of R) ⟶ X) [IsOpenImmersion j]
    (A : LineBundle X) (n : ℕ)
    (e : A.sheaf.restrict (chartOpen j).1.ι ≅ structureSheaf (chartOpen j).1.toScheme) :
    (modulePow X A.sheaf n).restrict j ≅ O (Spec (CommRingCat.of R)) :=
  (Scheme.Modules.restrictFunctorCongr j.isoOpensRange_hom_ι.symm).app _ ≪≫
    (Scheme.Modules.restrictFunctorComp j.isoOpensRange.hom j.opensRange.ι).app _ ≪≫
    restrictFrame j.isoOpensRange.hom (untwistPowerFrame A (chartOpen j).1 e n)

theorem polynomialCoefficient_eq (j : Spec (CommRingCat.of R) ⟶ X) [IsOpenImmersion j]
    (A : LineBundle X) (n : ℕ)
    (e : A.sheaf.restrict (chartOpen j).1.ι ≅ structureSheaf (chartOpen j).1.toScheme)
    (s : GlobalSections X (modulePow X A.sheaf n)) :
    polynomialCoefficient j A n e s =
      (Scheme.ΓSpecIso (CommRingCat.of R)).hom
        (coefficient (polynomialPowerFrame j A n e) (restrictSection j s)) := by
  have hframe : coefficient (polynomialPowerFrame j A n e) (restrictSection j s) =
      j.isoOpensRange.hom.appTop (coefficient (untwistPowerFrame A (chartOpen j).1 e n)
        (restrictSection (chartOpen j).1.ι s)) := by
    rw [polynomialPowerFrame, coefficient_transport]
    exact (congrArg (coefficient
      ((Scheme.Modules.restrictFunctorComp j.isoOpensRange.hom j.opensRange.ι).app
        (modulePow X A.sheaf n) ≪≫
          restrictFrame j.isoOpensRange.hom (untwistPowerFrame A (chartOpen j).1 e n)))
      (restrictSection_congr j.isoOpensRange_hom_ι.symm s)).trans
        (coefficient_restrict_comp j.isoOpensRange.hom j.opensRange.ι _ s)
  unfold polynomialCoefficient
  rw [globalSectionCoefficient_eq]
  change (Scheme.ΓSpecIso (CommRingCat.of R)).hom
      (j.isoOpensRange.hom.appTop ((chartOpen j).1.topIso.inv
        ((chartOpen j).1.topIso.hom _))) = _
  rw [(chartOpen j).1.topIso.hom_inv_id_apply]
  exact congrArg (Scheme.ΓSpecIso (CommRingCat.of R)).hom hframe.symm

end PiExponent.AffineJetCoefficientFrame
end

end OAI
end Source0843

-- Source: OAI/NumberTheory/PiExponent/Polynomials/GlobalPolynomialWeightedBound.lean
section Source0844
/-
Modification notice for the LogTwo project.
Derived from openai/math (Apache-2.0), revision adc7f1241b42e322a6451854ab7e4b4c146bf78a.
Original source: lean/OAI/NumberTheory/PiExponent/Polynomials/GlobalPolynomialWeightedBound.lean
Changes: Convert module/import declarations to the Lean 4.34 public module format.
See ../THIRD_PARTY_NOTICES.txt for provenance and the recorded changes.
-/

namespace OAI

noncomputable section
namespace PiExponent.GlobalPolynomialWeightedBound
open AlgebraicGeometry CategoryTheory
open PiExponentSeshadri.Geometry PiExponentSeshadri.Frames
open PiExponent.WeightedSliceDegree PiExponent.AffineJetCoefficientInterface

theorem coefficient_bound {X Y : Scheme.{0}} {K ι B : Type}
    [Field K] [CommRing B] (L : LineBundle Y) (f : X ⟶ Y)
    (φ : Spec (CommRingCat.of (MvPolynomial ι K)) ⟶ X) [IsOpenImmersion φ]
    (V : Y.Opens) (g : Spec (CommRingCat.of (MvPolynomial ι K)) ⟶ V.toScheme)
    (hg : φ ≫ f = g ≫ V.ι) (n : ℕ)
    (e : (modulePow Y L.sheaf n).restrict V.ι ≅ structureSheaf V.toScheme)
    (E : Γ(Y,V) ≃+* B) (P : (structureSheaf Y ⟶ modulePow Y L.sheaf n) → B)
    (hP : GlobalPolynomialCoefficientLaw.CoefficientLaw V e E P)
    (ev : B →+* MvPolynomial ι K)
    (hev : ∀ q, (Scheme.ΓSpecIso (CommRingCat.of (MvPolynomial ι K))).hom
      (g.appTop (V.topIso.inv (E.symm q))) = ev q)
    (ρ : ι → ℝ) (r : ℝ) (eTarget : Frame φ (L.pullback f)) (s : Sections L n)
    (hbound : SupportBound ρ r (ev (P s))) :
    SupportBound ρ r (AffineJetCoefficientInterface.coefficient φ (L.pullback f) n eTarget
      (pullbackPowerSection L f n s)) := by
  obtain ⟨F, hF⟩ := GlobalPolynomialCoefficientLaw.exists_power_frame_of_law
    L f φ V g hg n e E P hP ev hev
  erw [AffineJetCoefficientInterface.coefficient_eq,
    AffineJetCoefficientFrame.polynomialCoefficient_eq]
  apply WeightedFrameDegree.coefficient_supportBound ρ r F
  exact Eq.mpr (congrArg (SupportBound ρ r) (hF s)) hbound

end PiExponent.GlobalPolynomialWeightedBound
end

end OAI
end Source0844

-- Source: LogTwo/Geometry/WeightedHomogeneousSubstitution.lean
section Source0845
/-
Modification notice for the LogTwo project.
Adapted from openai/math (Apache-2.0), revision adc7f1241b42e322a6451854ab7e4b4c146bf78a.
Changes: Extract generic weighted-section lemmas, change namespaces/imports and omit fixed-center wrappers.
See ../THIRD_PARTY_NOTICES.txt for provenance and the recorded changes.
-/

/-! Generic weighted-section lemma extracted from the pinned openai/math source.
Fixed-center admissible wrappers are excluded; proof bodies are preserved.
See THIRD_PARTY_NOTICES.txt. -/

namespace LogTwo.Geometry.WeightedHomogeneousSubstitution
noncomputable section
open OAI PiExponent
open scoped BigOperators
open MvPolynomial
open WeightedSliceDegree
open PiExponentSeshadri.Projective

variable {σ ι K : Type*}

theorem supportBound_substitution [Field K] (ρ : ι → ℝ) (B : ℝ)
    (a : σ → ι →₀ ℕ) (ha : ∀ j, Finsupp.weight ρ (a j) ≤ B)
    (n : ℕ) (p : MvPolynomial.homogeneousSubmodule σ K n) :
    SupportBound ρ ((n : ℝ) * B)
      (MvPolynomial.aeval (fun j => MvPolynomial.monomial (a j) (1 : K)) p.val) := by
  classical
  refine supportBound_aeval (fun _ : σ => B) ρ
    (fun j => MvPolynomial.monomial (a j) (1 : K)) ?_ ((n : ℝ) * B) p.val ?_
  · intro j b hb
    have he : b = a j := Finset.mem_singleton.mp (MvPolynomial.support_monomial_subset hb)
    simpa only [he] using ha j
  · intro b hb
    have hd : b.degree = n := by
      exact (p.property.degree_eq_sum_deg_support hb).symm
    simp only [Finsupp.weight_apply, Finsupp.sum, nsmul_eq_mul,
      ← Finset.sum_mul, ← Nat.cast_sum, ← Finsupp.degree_apply, hd, le_refl]

theorem dehomogenize_substitution [CommRing K] (a : σ → ι →₀ ℕ)
    (z : σ) (hz : a z = 0) (p : MvPolynomial σ K) :
    MvPolynomial.aeval (fun j : ChartVariables z => MvPolynomial.monomial (a j.val) (1 : K))
      (dehomogenize z p) =
    MvPolynomial.aeval (fun j => MvPolynomial.monomial (a j) (1 : K)) p := by
  classical
  have he :
      (MvPolynomial.aeval (R := K) (fun j : ChartVariables z =>
        MvPolynomial.monomial (a j.val) (1 : K))).toRingHom.comp (dehomogenize (R := K) z) =
      (MvPolynomial.aeval (R := K) (fun j => MvPolynomial.monomial (a j) (1 : K))).toRingHom := by
    apply MvPolynomial.ringHom_ext
    · intro r
      simp [dehomogenize]
    · intro j
      by_cases hj : j = z
      · subst j
        simp [dehomogenize, hz]
      · simp [dehomogenize, hj]
  exact RingHom.congr_fun he p

end
end LogTwo.Geometry.WeightedHomogeneousSubstitution
end Source0845

-- Source: LogTwo/Geometry/WeightedPullbackDegree.lean
section Source0846
/-
Modification notice for the LogTwo project.
Adapted from openai/math (Apache-2.0), revision adc7f1241b42e322a6451854ab7e4b4c146bf78a.
Changes: Extract generic weighted-section lemmas, change namespaces/imports and omit fixed-center wrappers.
See ../THIRD_PARTY_NOTICES.txt for provenance and the recorded changes.
-/

/-! Generic weighted-section lemma extracted from the pinned openai/math source.
Fixed-center admissible wrappers are excluded; proof bodies are preserved.
See THIRD_PARTY_NOTICES.txt. -/

noncomputable section
namespace LogTwo.Geometry.WeightedPullbackDegree
open OAI PiExponent AlgebraicGeometry CategoryTheory
open PiExponentSeshadri.Geometry PiExponentSeshadri.Frames PiExponentSeshadri.Projective
open PiExponent.WeightedCompactification PiExponent.WeightedSliceDegree
open PiExponent.AffineJetPolynomial PiExponent.AffineJetCoefficientFrame
open PiExponent.AffineJetCoefficientInterface
variable {K ι σ : Type} [Field K]
attribute [local irreducible] Frame Sections AffineJetCoefficientInterface.coefficient
  WeightedCompactification.affineChartMap
  ProjectiveO1.lineBundle ProjectiveO1.coordinateSection ProjectiveO1.scalars
  ProjectiveO1.coordinateCocycle PiExponentSeshadri.Projective.sectionsMorphism
  PiExponentSeshadri.Projective.CoordinateAtlas.morphism PiExponentSeshadri.Projective.atlasOfFramedSections
  ProjectiveO1.globalSectionChartPolynomial
  ProjectiveIntrinsicCoefficientLaw.CoordinateData.polynomial
  ProjectiveIntrinsicCoefficientLaw.CoordinateData.frame
  ProjectiveIntrinsicCoefficientLaw.CoordinateData.ringEquiv

theorem pullback_supportBound (a : σ → ι →₀ ℕ) (z : σ) (hz : a z = 0)
    (coordinate : ι → σ) (hcoordinate : ∀ i, a (coordinate i) = Finsupp.single i 1)
    (ρ : ι → ℝ) (B : ℝ) (ha : ∀ j, Finsupp.weight ρ (a j) ≤ B) (n : ℕ)
    (e : Frame (affineChartMap (R := K) a z hz coordinate hcoordinate)
      (OAI.PiExponent.WeightedCompactification.lineBundle (R := K) a))
    (s : Sections (ProjectiveO1.lineBundle (R := K) (σ := σ)) n)
    (p : MvPolynomial.homogeneousSubmodule σ K n)
    (hp : dehomogenize z p.val = ProjectiveO1.globalSectionChartPolynomial (R := K) (σ := σ) n z
      (ProjectiveSectionInterface.sectionHom (ProjectiveO1.lineBundle (R := K) (σ := σ)) n s)) :
    SupportBound ρ ((n : ℝ) * B)
      (AffineJetCoefficientInterface.coefficient (affineChartMap (R := K) a z hz coordinate hcoordinate)
        (OAI.PiExponent.WeightedCompactification.lineBundle (R := K) a) n e
        (ProjectiveSectionInterface.pullback (ProjectiveO1.lineBundle (R := K) (σ := σ))
          (projectiveMonomialMap (R := K) a) n s)) := by
  let D := ProjectiveIntrinsicCoefficientLaw.intrinsicData (R := K) (σ := σ)
  let ev : MvPolynomial (ChartVariables z) K →+* MvPolynomial ι K :=
    (MvPolynomial.aeval (R := K) (fun j : ChartVariables z =>
      MvPolynomial.monomial (a j.val) (1 : K))).toRingHom
  have hbound : SupportBound ρ ((n : ℝ) * B) (ev (D.polynomial n z (ProjectiveSectionInterface.sectionHom
      (ProjectiveO1.lineBundle (R := K) (σ := σ)) n s))) := by
    dsimp only [D]
    rw [ProjectiveIntrinsicCoefficientLaw.intrinsic_polynomial]
    rw [← hp]
    change SupportBound ρ ((n : ℝ) * B)
      (MvPolynomial.aeval (fun j : ChartVariables z =>
        MvPolynomial.monomial (a j.val) (1 : K)) (dehomogenize z p.val))
    rw [LogTwo.Geometry.WeightedHomogeneousSubstitution.dehomogenize_substitution a z hz]
    exact LogTwo.Geometry.WeightedHomogeneousSubstitution.supportBound_substitution ρ B a ha n p
  exact GlobalPolynomialWeightedBound.coefficient_bound
    (X := Proj (imageGrade (R := K) a)) (Y := D.scheme) (K := K) (ι := ι)
    (B := MvPolynomial (ChartVariables z) K)
    (ProjectiveIntrinsicCoefficientLaw.intrinsicBundle (R := K) (σ := σ))
    (projectiveMonomialMap (R := K) a)
    (affineChartMap (R := K) a z hz coordinate hcoordinate)
    (D.chartOpen z) (WeightedChartRingEvaluation.chartFactor (R := K) a z hz coordinate hcoordinate)
    (WeightedChartRingEvaluation.chartFactor_comp (R := K) a z hz coordinate hcoordinate) n
    (D.frame n z) (D.ringEquiv z) (D.polynomial n z)
    (ProjectiveIntrinsicCoefficientLaw.intrinsic_law (R := K) n z) ev
    (by
      intro q
      dsimp only [D]
      rw [ProjectiveIntrinsicCoefficientLaw.intrinsic_ringEquiv]
      exact WeightedChartRingEvaluation.chartFactor_pullback (R := K) a z hz coordinate hcoordinate q)
    ρ ((n : ℝ) * B) e s hbound

end LogTwo.Geometry.WeightedPullbackDegree
end
end Source0846

-- Source: OAI/NumberTheory/PiExponent/Geometry/ProjectiveCoefficientBound.lean
section Source0847
/-
Modification notice for the LogTwo project.
Derived from openai/math (Apache-2.0), revision adc7f1241b42e322a6451854ab7e4b4c146bf78a.
Original source: lean/OAI/NumberTheory/PiExponent/Geometry/ProjectiveCoefficientBound.lean
Changes: Convert module/import declarations to the Lean 4.34 public module format.
See ../THIRD_PARTY_NOTICES.txt for provenance and the recorded changes.
-/

namespace OAI

noncomputable section
namespace PiExponent.ProjectiveCoefficientBound
open AlgebraicGeometry CategoryTheory
open PiExponentSeshadri.Geometry PiExponentSeshadri.Projective
open PiExponent.AffineJetCoefficientInterface PiExponent.WeightedSliceDegree

def EventualBound {X : Scheme} {K ι : Type} [Field K]
    (φ : Spec (CommRingCat.of (MvPolynomial ι K)) ⟶ X) [IsOpenImmersion φ]
    (L : LineBundle X) (ρ : ι → ℝ) (B : ℝ) : Prop :=
  ∃ N, ∀ n, N ≤ n → ∀ e : Frame φ L, ∀ s : Sections L n,
    SupportBound ρ ((n : ℝ) * B) (AffineJetCoefficientInterface.coefficient φ L n e s)

variable {X : Scheme.{0}} {K ι σ : Type} [Field K] [Fintype σ] [Nonempty σ]

def HomogeneousPullbackBound
    (f : X ⟶ ProjectiveO1.projectiveSpace K σ)
    (φ : Spec (CommRingCat.of (MvPolynomial ι K)) ⟶ X) [IsOpenImmersion φ]
    (ρ : ι → ℝ) (B : ℝ) : Prop :=
  ∀ n, ∀ e : Frame φ ((ProjectiveO1.lineBundle (R := K) (σ := σ)).pullback f),
    ∀ t : Sections (ProjectiveO1.lineBundle (R := K) (σ := σ)) n,
    ∀ p : MvPolynomial.homogeneousSubmodule σ K n,
    (∀ z, dehomogenize z p.val = ProjectiveO1.globalSectionChartPolynomial (R := K) n z
      (ProjectiveSectionInterface.sectionHom (ProjectiveO1.lineBundle (R := K) (σ := σ)) n t)) →
    SupportBound ρ ((n : ℝ) * B)
      (AffineJetCoefficientInterface.coefficient φ
        ((ProjectiveO1.lineBundle (R := K) (σ := σ)).pullback f) n e
        (ProjectiveSectionInterface.pullback (ProjectiveO1.lineBundle (R := K) (σ := σ)) f n t))

theorem eventual_of_homogeneous
    (f : X ⟶ ProjectiveO1.projectiveSpace K σ) [IsClosedImmersion f]
    (φ : Spec (CommRingCat.of (MvPolynomial ι K)) ⟶ X) [IsOpenImmersion φ]
    (ρ : ι → ℝ) (B : ℝ) (h : HomogeneousPullbackBound f φ ρ B) :
    EventualBound φ ((ProjectiveO1.lineBundle (R := K) (σ := σ)).pullback f) ρ B := by
  obtain ⟨N, hN⟩ := ProjectiveSectionInterface.eventual_homogeneous_extension f
  refine ⟨N, fun n hn e s => ?_⟩
  obtain ⟨t, p, ht, hp⟩ := hN n hn s
  rw [← ht]
  exact h n e t p hp

end PiExponent.ProjectiveCoefficientBound
end

end OAI
end Source0847

-- Source: LogTwo/Geometry/WeightedGlobalSectionBound.lean
section Source0848
/-
Modification notice for the LogTwo project.
Adapted from openai/math (Apache-2.0), revision adc7f1241b42e322a6451854ab7e4b4c146bf78a.
Changes: Extract generic weighted-section lemmas, change namespaces/imports and omit fixed-center wrappers.
See ../THIRD_PARTY_NOTICES.txt for provenance and the recorded changes.
-/

/-! Generic weighted-section lemma extracted from the pinned openai/math source.
Fixed-center admissible wrappers are excluded; proof bodies are preserved.
See THIRD_PARTY_NOTICES.txt. -/

noncomputable section
namespace LogTwo.Geometry.WeightedGlobalSectionBound
open OAI PiExponent AlgebraicGeometry CategoryTheory
open PiExponentSeshadri.Geometry
open PiExponent.WeightedCompactification PiExponent.WeightedSliceDegree
open PiExponent.AffineJetCoefficientInterface PiExponent.ProjectiveCoefficientBound
variable {K ι σ : Type} [Field K] [Fintype σ]
attribute [local irreducible] Frame Sections AffineJetCoefficientInterface.coefficient
  LineBundle.pullback EventualBound ProjectiveO1.lineBundle
  WeightedCompactification.affineChartMap

theorem eventual_supportBound (a : σ → ι →₀ ℕ) (z : σ) (hz : a z = 0)
    (coordinate : ι → σ) (hcoordinate : ∀ i, a (coordinate i) = Finsupp.single i 1)
    (ρ : ι → ℝ) (B : ℝ) (ha : ∀ j, Finsupp.weight ρ (a j) ≤ B) :
    EventualBound (affineChartMap (R := K) a z hz coordinate hcoordinate)
      (OAI.PiExponent.WeightedCompactification.lineBundle (R := K) a) ρ B := by
  let : Nonempty σ := ⟨z⟩
  apply eventual_of_homogeneous (X := Proj (imageGrade (R := K) a))
    (K := K) (ι := ι) (σ := σ) (projectiveMonomialMap (R := K) a)
    (affineChartMap (R := K) a z hz coordinate hcoordinate) ρ B
  intro n e t p hp
  exact LogTwo.Geometry.WeightedPullbackDegree.pullback_supportBound (K := K) (ι := ι) (σ := σ)
    a z hz coordinate hcoordinate ρ B ha n e t p (hp z)

end LogTwo.Geometry.WeightedGlobalSectionBound
end
end Source0848

-- Source: LogTwo/Geometry/JetPacketSurjectivity.lean
section Source0849
/-
Modification notice for the LogTwo project.
Adapted from openai/math (Apache-2.0), revision adc7f1241b42e322a6451854ab7e4b4c146bf78a.
Changes: Adapt the CRT packet proof using the project scaleYEquiv.
See ../THIRD_PARTY_NOTICES.txt for provenance and the recorded changes.
-/

/-! Formal packets at distinct, nonzero Y centers. CRT is used before degree
bounds; the final quotient-lifting theorem can then receive bounded sections. -/
namespace LogTwo.Geometry
open OAI PiExponent PiExponentApprox JetGeometry
noncomputable section
variable {m : ℕ}

theorem formalJetAt_packet_surjective (y : ℂ) (hy : y ≠ 0) (c : Fin m → ℂ)
    (v : Fin (m+1) → ℚ) (hv : ∀ i, 0 < v i) (H : ℚ) :
    Function.Surjective (fun P : FramePolynomial m =>
      rationalCoefficientPacket v H (formalJetAt y c P)) := by
  intro packet
  obtain ⟨P, hP⟩ := AlgebraicJetPackets.formalJet_packet_surjective c v hv H packet
  obtain ⟨Q, hQ⟩ := (scaleYEquiv y hy).surjective P
  refine ⟨Q, ?_⟩
  change rationalCoefficientPacket v H (FormalLogJet.formalJet c (scaleY y Q)) = packet
  change scaleY y Q = P at hQ
  rw [hQ]
  exact hP

theorem formalJetAt_packet_eq_of_sub_mem_pow (y : ℂ) (c : Fin m → ℂ)
    (T : Fin m → ℕ) (e : Fin (m+1) → ℕ)
    (v : Fin (m+1) → ℚ) (hv : ∀ i, 0 ≤ v i)
    (hT : ∀ i, v i.succ ≤ (T i : ℚ) * v 0)
    (R : ℚ) (he : ∀ i, R ≤ (e i : ℚ) * v i) (n : ℕ)
    (P Q : FramePolynomial m) (hPQ : P - Q ∈ jetIdealAt y c T e ^ n) :
    rationalCoefficientPacket v (n * R) (formalJetAt y c P) =
      rationalCoefficientPacket v (n * R) (formalJetAt y c Q) := by
  apply (FormalLogTruncation.rationalCoefficientPacket_eq_iff v hv (n * R) _ _).mpr
  simpa only [map_sub] using
    formalJetAt_mem_weighted_of_mem_pow y c T e v hv hT R he n (P - Q) hPQ

theorem formalJetAt_packets_surjective {J : Type*} [Fintype J]
    (y : J → ℂ) (hy0 : ∀ j, y j ≠ 0) (hy : Function.Injective y)
    (c : J → Fin m → ℂ) (T : Fin m → ℕ)
    (e : Fin (m+1) → ℕ) (hepos : ∀ i, 0 < e i)
    (v : Fin (m+1) → ℚ) (hv : ∀ i, 0 < v i)
    (hT : ∀ i, v i.succ ≤ (T i : ℚ) * v 0)
    (R : ℚ) (he : ∀ i, R ≤ (e i : ℚ) * v i) (n : ℕ) :
    Function.Surjective (fun P : FramePolynomial m => fun j =>
      rationalCoefficientPacket v (n * R) (formalJetAt (y j) (c j) P)) := by
  intro packets
  choose P hP using fun j => formalJetAt_packet_surjective (y j) (hy0 j) (c j) v hv
    (n * R) (packets j)
  obtain ⟨Q, hQ⟩ := jetIdealAt_residue_surjective y hy c T e hepos n
    (fun j => Ideal.Quotient.mk (jetIdealAt (y j) (c j) T e ^ n) (P j))
  refine ⟨Q, ?_⟩
  funext j
  exact (formalJetAt_packet_eq_of_sub_mem_pow (y j) (c j) T e v (fun i => (hv i).le)
    hT R he n Q (P j) (Ideal.Quotient.eq.mp (congrFun hQ j))).trans (hP j)

theorem formalJetAt_packets_surjective_of_quotient {J α : Type*} [Fintype J]
    (y : J → ℂ) (hy0 : ∀ j, y j ≠ 0) (hy : Function.Injective y)
    (c : J → Fin m → ℂ) (T : Fin m → ℕ)
    (e : Fin (m+1) → ℕ) (hepos : ∀ i, 0 < e i)
    (v : Fin (m+1) → ℚ) (hv : ∀ i, 0 < v i)
    (hT : ∀ i, v i.succ ≤ (T i : ℚ) * v 0)
    (R : ℚ) (he : ∀ i, R ≤ (e i : ℚ) * v i) (n : ℕ)
    (f : α → FramePolynomial m)
    (hf : Function.Surjective (fun a => Ideal.Quotient.mk (jetProductIdeal y c T e ^ n) (f a))) :
    Function.Surjective (fun a => fun j =>
      rationalCoefficientPacket v (n * R) (formalJetAt (y j) (c j) (f a))) := by
  intro packets
  obtain ⟨P, hP⟩ := formalJetAt_packets_surjective y hy0 hy c T e hepos v hv hT R he n packets
  obtain ⟨a, ha⟩ := hf (Ideal.Quotient.mk _ P)
  refine ⟨a, ?_⟩
  funext j
  exact (formalJetAt_packet_eq_of_sub_mem_pow (y j) (c j) T e v (fun i => (hv i).le)
    hT R he n (f a) P (jetProductIdeal_pow_le y c T e n j (Ideal.Quotient.eq.mp ha))).trans
      (congrFun hP j)

end
end LogTwo.Geometry
end Source0849

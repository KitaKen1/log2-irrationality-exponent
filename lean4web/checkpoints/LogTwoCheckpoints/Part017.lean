/- Generated rc4 checkpoint for LogTwo.
Modified from the reduced edition: new imports, separate module compilation,
and synchronous elaboration. Original source blocks and notices are retained.
See ../../../THIRD_PARTY_NOTICES.txt and ../../reduction.json.
-/
module
public import LogTwoCheckpoints.Part001
public import LogTwoCheckpoints.Part012
public import LogTwoCheckpoints.Part013
public import LogTwoCheckpoints.Part014
public import LogTwoCheckpoints.Part015
public import LogTwoCheckpoints.Part016
public import Mathlib.Algebra.Category.Grp.Zero
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.EpiMono
public import Mathlib.Algebra.Homology.DerivedCategory.Ext.ExactSequences
public import Mathlib.Algebra.Homology.DerivedCategory.Ext.Linear
public import Mathlib.AlgebraicGeometry.Modules.Tilde
public import Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Topology
public import Mathlib.AlgebraicGeometry.ZariskisMainTheorem
public import Mathlib.Analysis.Complex.Polynomial.Basic
public import Mathlib.Data.Opposite
public import Mathlib.Data.SetLike.Basic
public import Mathlib.Topology.Sheaves.Flasque
@[expose] public section
set_option Elab.async false

-- Source: OAI/NumberTheory/PiExponent/Geometry/ProjectiveSectionsPullback.lean
section Source0425
/-
Modification notice for the LogTwo project.
Derived from openai/math (Apache-2.0), revision adc7f1241b42e322a6451854ab7e4b4c146bf78a.
Original source: lean/OAI/NumberTheory/PiExponent/Geometry/ProjectiveSectionsPullback.lean
Changes: Convert module/import declarations to the Lean 4.34 public module format.
See ../THIRD_PARTY_NOTICES.txt for provenance and the recorded changes.
-/

namespace OAI

namespace PiExponentSeshadri.Projective
noncomputable section
open AlgebraicGeometry CategoryTheory TopologicalSpace
open PiExponentSeshadri.Frames PiExponentSeshadri.Geometry
attribute [local instance] MvPolynomial.gradedAlgebra
variable {K σ : Type} [CommRing K] {X Y : Scheme.{0}}

lemma sectionsMorphism_frame {M : X.Modules} (k : K →+* Γ(X, ⊤))
    (s : σ → (O X ⟶ M)) (hs : (⨆ i, SectionOpens.isoOpen (s i)) = ⊤)
    (φ : Y ⟶ X) [IsOpenImmersion φ] (e : M.restrict φ ≅ O Y)
    (i : σ) (hi : coefficient e (restrictSection φ (s i)) = 1) :
    φ ≫ sectionsMorphism k s hs =
      coordinatesMap Y (φ.appTop.hom.comp k)
        (fun j => coefficient e (restrictSection φ (s j))) i hi := by
  let U := SectionOpens.isoOpen (s i)
  have hp : φ ⁻¹ᵁ U = ⊤ := by
    rw [show U = SectionOpens.isoOpen (s i) from rfl, preimage_isoOpen (s i) φ e, hi]
    exact (isUnit_iff_basicOpen_top _).mp isUnit_one
  have hr : Set.range φ ⊆ Set.range U.ι := by
    rintro _ ⟨y, rfl⟩
    rw [Scheme.Opens.range_ι]
    have h : y ∈ φ ⁻¹ᵁ U := by rw [hp]; trivial
    exact h
  let l := IsOpenImmersion.lift U.ι φ hr
  have hl : l ≫ U.ι = φ := IsOpenImmersion.lift_fac U.ι φ hr
  let : IsOpenImmersion l := IsOpenImmersion.of_comp l U.ι
  obtain ⟨c, hc⟩ := overlap_coefficients φ U.ι (𝟙 Y) l (by simpa using hl.symm)
    e (sectionFrame (s i))
  have hci : (c : Γ(Y, ⊤)) = 1 := by
    have h := hc (s i)
    simpa only [U, sectionFrame_normalized, map_one, hi, Scheme.Hom.id_appTop,
      CommRingCat.id_apply, mul_one] using h.symm
  have hc' (j : σ) : l.appTop (coefficient (sectionFrame (s i))
      (restrictSection U.ι (s j))) = coefficient e (restrictSection φ (s j)) := by
    simpa only [hci, Scheme.Hom.id_appTop, CommRingCat.id_apply, one_mul] using hc (s j)
  conv_lhs => rw [← hl, Category.assoc, sectionsMorphism_local, coordinatesMap_natural]
  congr 1
  · rw [← RingHom.comp_assoc, ← CommRingCat.hom_comp, ← Scheme.Hom.comp_appTop, hl]
  · exact funext hc'

lemma pullback_isoOpen_le {M : X.Modules} (s : O X ⟶ M) (f : Y ⟶ X) :
    f ⁻¹ᵁ SectionOpens.isoOpen s ≤ SectionOpens.isoOpen (pullbackSection f s) := by
  let U := SectionOpens.isoOpen s
  obtain ⟨e,he⟩ := exists_restricted_pullback_frame_all f U (sectionFrame s)
  have hn : coefficient e (restrictSection (f ⁻¹ᵁ U).ι (pullbackSection f s)) = 1 := by
    rw [he,sectionFrame_normalized,map_one]
  have hp : (f ⁻¹ᵁ U).ι ⁻¹ᵁ SectionOpens.isoOpen (pullbackSection f s) = ⊤ := by
    rw [preimage_isoOpen (pullbackSection f s) (f ⁻¹ᵁ U).ι e, hn]
    exact (isUnit_iff_basicOpen_top _).mp isUnit_one
  intro x hx
  have h : (⟨x,hx⟩ : (f ⁻¹ᵁ U).toScheme) ∈
      (f ⁻¹ᵁ U).ι ⁻¹ᵁ SectionOpens.isoOpen (pullbackSection f s) := by rw [hp]; trivial
  exact h

lemma pullback_sections_cover {M : X.Modules} (s : σ → (O X ⟶ M))
    (hs : (⨆ i, SectionOpens.isoOpen (s i)) = ⊤) (f : Y ⟶ X) :
    (⨆ i, SectionOpens.isoOpen (pullbackSection f (s i))) = ⊤ := by
  apply top_le_iff.mp
  rw [← Scheme.Hom.preimage_top f, ← hs, Scheme.Hom.preimage_iSup]
  exact iSup_mono fun i => pullback_isoOpen_le (s i) f

theorem sectionsMorphism_pullback {M : X.Modules} (k : K →+* Γ(X,⊤))
    (s : σ → (O X ⟶ M)) (hs : (⨆ i, SectionOpens.isoOpen (s i)) = ⊤)
    (f : Y ⟶ X) :
    f ≫ sectionsMorphism k s hs =
      sectionsMorphism (f.appTop.hom.comp k) (fun i => pullbackSection f (s i))
        (pullback_sections_cover s hs f) := by
  let t (i : σ) := pullbackSection f (s i)
  let ht := pullback_sections_cover s hs f
  have hc : (⨆ i, f ⁻¹ᵁ SectionOpens.isoOpen (s i)) = ⊤ := by
    rw [← Scheme.Hom.preimage_iSup,hs,Scheme.Hom.preimage_top]
  apply (Y.openCoverOfIsOpenCover (fun i => f ⁻¹ᵁ SectionOpens.isoOpen (s i)) hc).hom_ext
  intro i
  let U := SectionOpens.isoOpen (s i)
  obtain ⟨e,he⟩ := exists_restricted_pullback_frame_all f U (sectionFrame (s i))
  have hi : coefficient e (restrictSection (f ⁻¹ᵁ U).ι (t i)) = 1 := by
    rw [he,sectionFrame_normalized,map_one]
  change (f ⁻¹ᵁ U).ι ≫ (f ≫ sectionsMorphism k s hs) =
    (f ⁻¹ᵁ U).ι ≫ sectionsMorphism (f.appTop.hom.comp k) t ht
  erw [← Category.assoc, ← morphismRestrict_ι f U, Category.assoc,
    sectionsMorphism_local k s hs i, coordinatesMap_natural,
    sectionsMorphism_frame _ t ht (f ⁻¹ᵁ U).ι e i hi]
  congr 1
  · rw [← RingHom.comp_assoc, ← CommRingCat.hom_comp, ← Scheme.Hom.comp_appTop,
      morphismRestrict_ι f U, Scheme.Hom.comp_appTop]
    rfl
  · exact (funext fun j => he (s j)).symm
end
end PiExponentSeshadri.Projective

end OAI
end Source0425

-- Source: OAI/NumberTheory/PiExponent/Geometry/ProjectiveO1Morphism.lean
section Source0426
/-
Modification notice for the LogTwo project.
Derived from openai/math (Apache-2.0), revision adc7f1241b42e322a6451854ab7e4b4c146bf78a.
Original source: lean/OAI/NumberTheory/PiExponent/Geometry/ProjectiveO1Morphism.lean
Changes: Convert module/import declarations to the Lean 4.34 public module format.
See ../THIRD_PARTY_NOTICES.txt for provenance and the recorded changes.
-/

namespace OAI

noncomputable section

namespace PiExponent.ProjectiveO1

open AlgebraicGeometry CategoryTheory TopologicalSpace
open PiExponentSeshadri.Projective PiExponentSeshadri.Frames PiExponentSeshadri.LineBundleGluing

variable {R σ : Type} [CommRing R]

def coordinateOpenFrame (i : σ) :
    (lineBundle (R := R) (σ := σ)).sheaf.restrict (coordinateOpen i).ι ≅
      O (coordinateOpen (R := R) i).toScheme :=
  openFrame (coordinateCocycle (R := R) (σ := σ)) i (coordinateOpen i) le_rfl

lemma coordinateOpenFrame_normalized (i : σ) :
    coefficient (coordinateOpenFrame (R := R) i)
      (restrictSection (coordinateOpen i).ι (coordinateSection i)) = 1 :=
  coordinateSection_normalized i (coordinateOpen i) le_rfl

lemma coordinateOpenFrame_localMap (i : σ) :
    coordinatesMap (coordinateOpen (R := R) i).toScheme
      ((coordinateOpen i).ι.appTop.hom.comp (scalars (R := R) (σ := σ)))
      (fun j => coefficient (coordinateOpenFrame i)
        (restrictSection (coordinateOpen i).ι (coordinateSection j))) i
      (coordinateOpenFrame_normalized i) = (coordinateOpen i).ι :=
  coordinateSection_localMap i

attribute [local irreducible] coordinateSection lineBundle coordinateCocycle scalars coordinateOpenFrame
  sectionsMorphism CoordinateAtlas.morphism atlasOfFramedSections

theorem coordinate_sectionsMorphism_identity :
    sectionsMorphism (M := (lineBundle (R := R) (σ := σ)).sheaf)
      (scalars (R := R) (σ := σ)) (coordinateSection (R := R) (σ := σ))
      (coordinateSection_cover (R := R) (σ := σ)) = 𝟙 (projectiveSpace R σ) := by
  apply ((projectiveSpace R σ).openCoverOfIsOpenCover
    (coordinateOpen (R := R)) standardChart_cover).hom_ext
  intro i
  change (coordinateOpen (R := R) i).ι ≫ sectionsMorphism _ _ _ =
    (coordinateOpen i).ι ≫ 𝟙 _
  rw [Category.comp_id]
  have hι : IsOpenImmersion (coordinateOpen (R := R) i).ι :=
    IsOpenImmersion.ofRestrict (projectiveSpace R σ) (coordinateOpen (R := R) i).isOpenEmbedding
  exact (@sectionsMorphism_frame R σ _ (projectiveSpace R σ)
    (coordinateOpen (R := R) i).toScheme (lineBundle (R := R) (σ := σ)).sheaf
    (scalars (R := R) (σ := σ)) (coordinateSection (R := R) (σ := σ))
    (coordinateSection_cover (R := R) (σ := σ)) (coordinateOpen i).ι hι
    (coordinateOpenFrame i) i (coordinateOpenFrame_normalized i)).trans
      (coordinateOpenFrame_localMap i)

end PiExponent.ProjectiveO1

end

end OAI
end Source0426

-- Source: OAI/NumberTheory/PiExponent/Geometry/ProjectiveO1Identity.lean
section Source0427
/-
Modification notice for the LogTwo project.
Derived from openai/math (Apache-2.0), revision adc7f1241b42e322a6451854ab7e4b4c146bf78a.
Original source: lean/OAI/NumberTheory/PiExponent/Geometry/ProjectiveO1Identity.lean
Changes: Convert module/import declarations to the Lean 4.34 public module format.
See ../THIRD_PARTY_NOTICES.txt for provenance and the recorded changes.
-/

namespace OAI

noncomputable section

namespace PiExponent.ProjectiveO1

open AlgebraicGeometry CategoryTheory TopologicalSpace
open PiExponentSeshadri.Projective PiExponentSeshadri.Frames PiExponentSeshadri.LineBundleGluing

attribute [local irreducible] lineBundle coordinateSection scalars sectionsMorphism

variable {R σ : Type} [CommRing R]

theorem coordinateSection_isoOpen (i : σ) :
    PiExponentSeshadri.SectionOpens.isoOpen (coordinateSection (R := R) i) = coordinateOpen i := by
  exact identityCoordinateOpen (lineBundle (R := R) (σ := σ)).sheaf
    (scalars (R := R) (σ := σ)) (coordinateSection (R := R) (σ := σ))
    (coordinateSection_cover (R := R) (σ := σ))
    (coordinate_sectionsMorphism_identity (R := R) (σ := σ)) i

theorem coordinateSection_isAffineOpen (i : σ) :
    IsAffineOpen (PiExponentSeshadri.SectionOpens.isoOpen (coordinateSection (R := R) i)) := by
  rw [coordinateSection_isoOpen]
  exact standardChart_isAffineOpen i

end PiExponent.ProjectiveO1

end

end OAI
end Source0427

-- Source: OAI/NumberTheory/PiExponent/Geometry/ProjectiveSpaceIntegral.lean
section Source0428
/-
Modification notice for the LogTwo project.
Derived from openai/math (Apache-2.0), revision adc7f1241b42e322a6451854ab7e4b4c146bf78a.
Original source: lean/OAI/NumberTheory/PiExponent/Geometry/ProjectiveSpaceIntegral.lean
Changes: Convert module/import declarations to the Lean 4.34 public module format.
See ../THIRD_PARTY_NOTICES.txt for provenance and the recorded changes.
-/

namespace OAI

noncomputable section
namespace PiExponent.ProjectiveO1
open AlgebraicGeometry CategoryTheory TopologicalSpace
open PiExponentSeshadri.Projective
attribute [local instance] MvPolynomial.gradedAlgebra
variable (R σ : Type) [CommRing R]

instance projectiveSpace_reduced [IsDomain R] : IsReduced (projectiveSpace R σ) := by
  let U : (projectiveSpace R σ).OpenCover :=
    (projectiveSpace R σ).openCoverOfIsOpenCover (coordinateOpen (R := R))
      (by exact standardChart_cover)
  have h (i : σ) : IsReduced (coordinateOpen (R := R) i).toScheme :=
    isReduced_of_isOpenImmersion (projectiveChartIso (R := R) i).hom
  let : ∀ i, IsReduced (U.X i) := h
  exact IsReduced.of_openCover _ U

instance projectiveSpace_irreducible [IsDomain R] [Nonempty σ] :
    IrreducibleSpace (projectiveSpace R σ) := by
  let i : σ := Classical.choice inferInstance
  let p : projectiveSpace R σ := projectiveGenericPoint (PolyGrade R σ)
    (poly_X_mem i) (by decide) (MvPolynomial.X_ne_zero i)
  have hp : closure ({p} : Set (projectiveSpace R σ)) = Set.univ := by
    apply Set.eq_univ_of_forall
    intro x
    exact (ProjectiveSpectrum.le_iff_mem_closure (PolyGrade R σ) p x).mp
      (show (⊥ : HomogeneousIdeal (PolyGrade R σ)) ≤ x.asHomogeneousIdeal from bot_le)
  apply (irreducibleSpace_def _).mpr
  change IsIrreducible (Set.univ : Set (projectiveSpace R σ))
  rw [← hp]
  exact (isIrreducible_singleton (x := p)).closure

instance projectiveSpace_integral [IsDomain R] [Nonempty σ] :
    IsIntegral (projectiveSpace R σ) :=
  isIntegral_of_irreducibleSpace_of_isReduced _

end PiExponent.ProjectiveO1

end

end OAI
end Source0428

-- Source: OAI/NumberTheory/PiExponent/Ampleness/ProjectiveO1Ample.lean
section Source0429
/-
Modification notice for the LogTwo project.
Derived from openai/math (Apache-2.0), revision adc7f1241b42e322a6451854ab7e4b4c146bf78a.
Original source: lean/OAI/NumberTheory/PiExponent/Ampleness/ProjectiveO1Ample.lean
Changes: Convert module/import declarations to the Lean 4.34 public module format.
See ../THIRD_PARTY_NOTICES.txt for provenance and the recorded changes.
-/

namespace OAI

noncomputable section

namespace PiExponent.ProjectiveO1

open AlgebraicGeometry CategoryTheory
open PiExponentSeshadri.Geometry

variable {R σ : Type} [CommRing R] [IsDomain R] [Finite σ] [Nonempty σ]

theorem lineBundle_ample : (lineBundle (R := R) (σ := σ)).IsAmple := by
  let : CompactSpace (projectiveSpace R σ) :=
    QuasiCompact.compactSpace_of_compactSpace (polynomialProjectiveProjection R σ)
  exact LineBundle.ample_of_affine_section_cover (lineBundle (R := R) (σ := σ))
    coordinateSection coordinateSection_cover coordinateSection_isAffineOpen

end PiExponent.ProjectiveO1

end

end OAI
end Source0429

-- Source: OAI/NumberTheory/PiExponent/Cohomology/SerreVanishing.lean
section Source0430
/-
Modification notice for the LogTwo project.
Derived from openai/math (Apache-2.0), revision adc7f1241b42e322a6451854ab7e4b4c146bf78a.
Original source: lean/OAI/NumberTheory/PiExponent/Cohomology/SerreVanishing.lean
Changes: Convert module/import declarations to the Lean 4.34 public module format.
Expose private helpers and adjust helper names where needed for module compatibility.
See ../THIRD_PARTY_NOTICES.txt for provenance and the recorded changes.
-/

namespace OAI

namespace PiExponent.SerreVanishing

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Abelian

universe u

variable {X : Scheme.{u}} [IsNoetherian X]
  [IsAffineHom (pullback.diagonal (terminal.from X))]

attribute [local instance] PiExponentSeshadri.FiniteCoverCohomology.hasExtScheme'

abbrev schemeUnit (Y : Scheme.{u}) : Y.Modules :=
  SheafOfModules.unit Y.ringCatSheaf

theorem ext_eq_zero_of_affine_cover (l : ℕ) (hl : 0 < l)
    (U : Fin l → X.Opens) (hU : ∀ i, IsAffineOpen (U i))
    (hcover : (⨆ i, U i) = ⊤) (M : X.Modules) [M.IsQuasicoherent]
    (q : ℕ) (hq : l ≤ q)
    (x : Abelian.Ext.{u+1} (C := X.Modules) (schemeUnit X) M q) : x = 0 := by
  cases l with
  | zero => exact False.elim (Nat.not_lt_zero 0 hl)
  | succ l =>
      have he : l + (q - (l + 1)) + 1 = q := by omega
      revert x
      clear hq
      rw [← he]
      exact PiExponentSeshadri.FiniteCoverCohomology.cover_ext_zero
        l U hU hcover M _

end

end PiExponent.SerreVanishing

end OAI
end Source0430

-- Source: OAI/NumberTheory/PiExponent/Cohomology/CurveNormalizationCohomology.lean
section Source0431
/-
Modification notice for the LogTwo project.
Derived from openai/math (Apache-2.0), revision adc7f1241b42e322a6451854ab7e4b4c146bf78a.
Original source: lean/OAI/NumberTheory/PiExponent/Cohomology/CurveNormalizationCohomology.lean
Changes: Convert module/import declarations to the Lean 4.34 public module format.
Expose private helpers and adjust helper names where needed for module compatibility.
See ../THIRD_PARTY_NOTICES.txt for provenance and the recorded changes.
-/

namespace OAI

noncomputable section
namespace PiExponent.CurveNormalizationModel
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian
open PiExponent.CurveZeroPole
open PiExponentSeshadri.Geometry

variable {F E : Type} [Field F] [Field E] [Algebra F E]
variable (f : E) (hf : Transcendental F f)
variable [CharZero F] [FiniteDimensional (IntermediateField.adjoin F {f}) E]

local instance : HasExt.{1} (parameterCurve f hf).Modules := HasExt.standard _

def parameterCurveUnit : (parameterCurve f hf).Modules :=
  SheafOfModules.unit (parameterCurve f hf).ringCatSheaf

instance parameterCurve_isSeparated : (parameterCurve f hf).IsSeparated := by
  rw [Scheme.isSeparated_iff]
  rw [← terminal.comp_from (parameterCurveStructureMap f hf)]
  infer_instance

def parameterCurveAffineOpens (i : Fin 2) : (parameterCurve f hf).Opens :=
  if i = 0 then (zeroChartInclusion f hf).opensRange
  else (infinityChartInclusion f hf).opensRange

omit [CharZero F] [FiniteDimensional (IntermediateField.adjoin F {f}) E] in
theorem parameterCurveAffineOpens_affine (i : Fin 2) :
    IsAffineOpen (parameterCurveAffineOpens f hf i) := by
  unfold parameterCurveAffineOpens
  split <;> exact isAffineOpen_opensRange _

omit [CharZero F] [FiniteDimensional (IntermediateField.adjoin F {f}) E] in
theorem parameterCurveAffineOpens_cover :
    (⨆ i, parameterCurveAffineOpens f hf i) = ⊤ := by
  apply top_le_iff.mp
  intro x _
  rcases parameterCurve_twoChartCover f hf x with ⟨q, rfl⟩ | ⟨q, rfl⟩
  · apply TopologicalSpace.Opens.mem_iSup.mpr
    exact ⟨0, by simp [parameterCurveAffineOpens, Scheme.Hom.mem_opensRange]⟩
  · apply TopologicalSpace.Opens.mem_iSup.mpr
    exact ⟨1, by simp [parameterCurveAffineOpens, Scheme.Hom.mem_opensRange]⟩

theorem parameterCurve_ext_zero
    (M : (parameterCurve f hf).Modules) [M.IsQuasicoherent]
    (q : ℕ) (hq : 2 ≤ q)
    (x : Ext.{1} (C := (parameterCurve f hf).Modules)
      (parameterCurveUnit f hf) M q) : x = 0 := by
  exact PiExponent.SerreVanishing.ext_eq_zero_of_affine_cover 2 (by omega)
    (parameterCurveAffineOpens f hf) (parameterCurveAffineOpens_affine f hf)
    (parameterCurveAffineOpens_cover f hf) M q hq x

theorem parameterCurve_lineBundle_ext_zero
    (L : LineBundle (parameterCurve f hf)) (q : ℕ) (hq : 2 ≤ q)
    (x : Ext.{1} (C := (parameterCurve f hf).Modules)
      (parameterCurveUnit f hf) L.sheaf q) :
    x = 0 := by
  let : L.sheaf.IsFinitePresentation :=
    PiExponent.GeometrySupport.LineBundleCoherent.lineBundle_isFinitePresentation L
  let : L.sheaf.IsQuasicoherent :=
    (SheafOfModules.IsFinitePresentation.exists_quasicoherentData L.sheaf).choose.isQuasicoherent
  exact parameterCurve_ext_zero f hf L.sheaf q hq x

end PiExponent.CurveNormalizationModel

end

end OAI
end Source0431

-- Source: OAI/NumberTheory/PiExponent/Ampleness/NumericalAmpleness.lean
section Source0432
-- Modified in this edition: unused plain lemmas removed; see reduction.json.
/-
Modification notice for the LogTwo project.
Derived from openai/math (Apache-2.0), revision adc7f1241b42e322a6451854ab7e4b4c146bf78a.
Original source: lean/OAI/NumberTheory/PiExponent/Ampleness/NumericalAmpleness.lean
Changes: Convert module/import declarations to the Lean 4.34 public module format.
See ../THIRD_PARTY_NOTICES.txt for provenance and the recorded changes.
-/

namespace OAI

namespace PiExponent.NumericalAmpleness
noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace
open PiExponentSeshadri.Geometry PiExponentSeshadri.Frames
open scoped AlgebraicGeometry

structure IntegralCurve (X : Scheme) where
  scheme : Scheme
  embedding : scheme ⟶ X
  closedImmersion : IsClosedImmersion embedding
  integral : IsIntegral scheme
  dimension : topologicalKrullDim scheme = 1

attribute [instance] IntegralCurve.closedImmersion IntegralCurve.integral

end
end PiExponent.NumericalAmpleness

end OAI
end Source0432

-- Source: OAI/NumberTheory/PiExponent/Cohomology/CurveEuler.lean
section Source0433
/-
Modification notice for the LogTwo project.
Derived from openai/math (Apache-2.0), revision adc7f1241b42e322a6451854ab7e4b4c146bf78a.
Original source: lean/OAI/NumberTheory/PiExponent/Cohomology/CurveEuler.lean
Changes: Convert module/import declarations to the Lean 4.34 public module format.
See ../THIRD_PARTY_NOTICES.txt for provenance and the recorded changes.
-/

namespace OAI

noncomputable section

namespace PiExponentSeshadri.Geometry

section
open CategoryTheory AlgebraicGeometry TopologicalSpace
open scoped AlgebraicGeometry
variable (X : Scheme)

def restrictScalar (U : X.Opens) : Γ(X, ⊤) →+* Γ(X, U) :=
  (X.presheaf.map (homOfLE le_top).op).hom

lemma restrictScalar_naturality {U V : X.Opens} (i : U ⟶ V) (r : Γ(X, ⊤)) :
    X.presheaf.map i.op (restrictScalar X V r) = restrictScalar X U r := by
  change (X.presheaf.map (homOfLE le_top).op ≫ X.presheaf.map i.op) r = _
  rw [← X.presheaf.map_comp]
  rfl

def sheafHomSMul {M N : X.Modules} (r : Γ(X, ⊤)) (f : M ⟶ N) : M ⟶ N where
  val := {
    app U := by
      letI : Module Γ(X, U.unop) (M.val.obj U) := (M.val.obj U).isModule
      letI : Module Γ(X, U.unop) (N.val.obj U) := (N.val.obj U).isModule
      let g : M.val.obj U →ₗ[Γ(X, U.unop)] N.val.obj U := (f.val.app U).hom
      exact ModuleCat.ofHom ((restrictScalar X U.unop r) • g)
    naturality {U V} g := by
      let : Module (X.presheaf.obj V) (N.presheaf.obj V) := (N.val.obj V).isModule
      ext m
      change restrictScalar X V.unop r • f.app V.unop (M.presheaf.map g m) =
        N.presheaf.map g (restrictScalar X U.unop r • f.app U.unop m)
      have hn := CategoryTheory.congr_fun (f.mapPresheaf.naturality g) m
      change f.app V.unop (M.presheaf.map g m) =
        N.presheaf.map g (f.app U.unop m) at hn
      rw [hn]
      calc
        _ = X.presheaf.map g (restrictScalar X U.unop r) •
            N.presheaf.map g (f.app U.unop m) := by
              exact congrArg (fun a : X.presheaf.obj V =>
                a • N.presheaf.map g (f.app U.unop m))
                (restrictScalar_naturality X g.unop r).symm
        _ = _ := (N.map_smul g.unop (restrictScalar X U.unop r) (f.app U.unop m)).symm }

instance sheafHomModule (M N : X.Modules) : Module Γ(X, ⊤) (M ⟶ N) where
  smul := sheafHomSMul X
  one_smul f := by
    ext U m
    change restrictScalar X U 1 • f.app U m = f.app U m
    simp
  mul_smul r s f := by
    ext U m
    change restrictScalar X U (r * s) • f.app U m =
      restrictScalar X U r • (restrictScalar X U s • f.app U m)
    simp [mul_smul]
  smul_zero r := by
    ext U m
    change restrictScalar X U r • (0 : Γ(N, U)) = 0
    exact smul_zero _
  smul_add r f g := by
    ext U m
    change restrictScalar X U r • (f.app U m + g.app U m) =
      restrictScalar X U r • f.app U m + restrictScalar X U r • g.app U m
    exact smul_add _ _ _
  zero_smul f := by
    ext U m
    change restrictScalar X U 0 • f.app U m = 0
    simp
  add_smul r s f := by
    ext U m
    change restrictScalar X U (r + s) • f.app U m =
      restrictScalar X U r • f.app U m + restrictScalar X U s • f.app U m
    simp [add_smul]

instance sheafLinear : Linear Γ(X, ⊤) X.Modules where
  smul_comp M N P r f g := by
    ext U m
    change g.app U (restrictScalar X U r • f.app U m) =
      restrictScalar X U r • g.app U (f.app U m)
    exact g.app_smul _ _
  comp_smul M N P f r g := by
    ext U m
    rfl

end

section
open CategoryTheory AlgebraicGeometry TopologicalSpace
open scoped AlgebraicGeometry

variable {X : Scheme.{0}}

instance schemeHasExt : HasExt.{1} X.Modules := HasExt.standard X.Modules

def baseScalars (f : X ⟶ Spec (CommRingCat.of ℂ)) : ℂ →+* Γ(X, ⊤) :=
  f.appTop.hom.comp (Scheme.ΓSpecIso (CommRingCat.of ℂ)).inv.hom

abbrev complexSectionModule (f : X ⟶ Spec (CommRingCat.of ℂ)) (M : X.Modules) :
    Module ℂ (GlobalSections X M) :=
  Module.compHom _ (baseScalars f)

abbrev cohomology (M : X.Modules) (n : ℕ) : Type 1 :=
  Abelian.Ext.{1} (C := X.Modules) (structureSheaf X) M n

def cohomologyDimension (f : X ⟶ Spec (CommRingCat.of ℂ))
    (M : X.Modules) (n : ℕ) : ℕ :=
  letI : Module ℂ (cohomology M n) :=
    Module.compHom (cohomology M n) (baseScalars f)
  Module.finrank ℂ (cohomology M n)

def eulerCharacteristic (f : X ⟶ Spec (CommRingCat.of ℂ)) (d : ℕ)
    (M : X.Modules) : ℤ :=
  ∑ n ∈ Finset.range (d + 1), (-1 : ℤ) ^ n * (cohomologyDimension f M n : ℤ)

end

open AlgebraicGeometry CategoryTheory TopologicalSpace Abelian Opposite
variable {X : Scheme}

def globalHomLinearEquiv (M : X.Modules) :
    GlobalSections X M ≃ₗ[Γ(X,⊤)] Γ(M,⊤) where
  toEquiv := FlasqueCohomology.globalHomEquiv X.ringCatSheaf M
  map_add' := by intro f g; rfl
  map_smul' := by
    intro r f
    change restrictScalar X ⊤ r • f.app ⊤ (1 : Γ(X,⊤)) = r • f.app ⊤ (1 : Γ(X,⊤))
    congr 1
    change (X.presheaf.map (𝟙 (op ⊤))) r = r
    rw [X.presheaf.map_id]
    rfl

def cohomologyZeroSections (f : X ⟶ Spec (CommRingCat.of ℂ)) (M : X.Modules) :
    let _ : Module ℂ (cohomology M 0) := Module.compHom _ (baseScalars f)
    let _ : Module ℂ Γ(M,⊤) := Module.compHom _ (baseScalars f)
    cohomology M 0 ≃ₗ[ℂ] Γ(M,⊤) := by
  dsimp only
  letI : Module ℂ (cohomology M 0) := Module.compHom _ (baseScalars f)
  letI : Module ℂ Γ(M,⊤) := Module.compHom _ (baseScalars f)
  let e := (Ext.linearEquiv₀ (R := Γ(X,⊤)) (X := structureSheaf X) (Y := M)).trans
    (globalHomLinearEquiv M)
  exact { e.toAddEquiv with map_smul' := fun r x => e.map_smul (baseScalars f r) x }

lemma cohomologyDimension_zero (f : X ⟶ Spec (CommRingCat.of ℂ)) (M : X.Modules) :
    cohomologyDimension f M 0 =
      let _ : Module ℂ Γ(M,⊤) := Module.compHom _ (baseScalars f)
      Module.finrank ℂ Γ(M,⊤) := by
  let : Module ℂ (cohomology M 0) := Module.compHom _ (baseScalars f)
  let : Module ℂ Γ(M,⊤) := Module.compHom _ (baseScalars f)
  exact (cohomologyZeroSections f M).finrank_eq

theorem affine_eulerCharacteristic (f : X ⟶ Spec (CommRingCat.of ℂ))
    [IsAffine X] [IsNoetherian X] (M : X.Modules) [M.IsQuasicoherent] (d : ℕ) :
    eulerCharacteristic f d M =
      let _ : Module ℂ Γ(M,⊤) := Module.compHom _ (baseScalars f)
      (Module.finrank ℂ Γ(M,⊤) : ℤ) := by
  unfold eulerCharacteristic
  rw [Finset.sum_eq_single 0]
  · simp only [pow_zero, one_mul, cohomologyDimension_zero]
  · intro n hn hn0
    obtain ⟨m,rfl⟩ := Nat.exists_eq_succ_of_ne_zero hn0
    have : Subsingleton (cohomology M (m+1)) :=
      ⟨fun x y => (AffineSchemeCohomology.affine_ext_zero X M m x).trans
        (AffineSchemeCohomology.affine_ext_zero X M m y).symm⟩
    simp [cohomologyDimension, Module.finrank_zero_of_subsingleton]
  · simp

end PiExponentSeshadri.Geometry

end

end OAI
end Source0433

-- Source: OAI/NumberTheory/PiExponent/Cohomology/CohomologyIso.lean
section Source0434
/-
Modification notice for the LogTwo project.
Derived from openai/math (Apache-2.0), revision adc7f1241b42e322a6451854ab7e4b4c146bf78a.
Original source: lean/OAI/NumberTheory/PiExponent/Cohomology/CohomologyIso.lean
Changes: Convert module/import declarations to the Lean 4.34 public module format.
See ../THIRD_PARTY_NOTICES.txt for provenance and the recorded changes.
-/

namespace OAI

namespace PiExponentSeshadri.Geometry
noncomputable section
open CategoryTheory CategoryTheory.Abelian AlgebraicGeometry
variable {X : Scheme.{0}}

def cohomologyIso (f : X ⟶ Spec (CommRingCat.of ℂ))
    {M N : X.Modules} (e : M ≅ N) (n : ℕ) :
    let _ := Module.compHom (cohomology M n) (baseScalars f)
    let _ := Module.compHom (cohomology N n) (baseScalars f)
    cohomology M n ≃ₗ[ℂ] cohomology N n := by
  dsimp only
  letI := Module.compHom (cohomology M n) (baseScalars f)
  letI := Module.compHom (cohomology N n) (baseScalars f)
  let g := (Ext.mk₀ e.hom).postcompOfLinear Γ(X,⊤) (structureSheaf X) (add_zero n)
  let h := (Ext.mk₀ e.inv).postcompOfLinear Γ(X,⊤) (structureSheaf X) (add_zero n)
  refine
    { toFun := g
      invFun := h
      map_add' := g.map_add
      map_smul' := fun r x => g.map_smul (baseScalars f r) x
      left_inv := ?_
      right_inv := ?_ }
  · intro x
    change (x.comp (Ext.mk₀ e.hom) (add_zero n)).comp (Ext.mk₀ e.inv) (add_zero n) = x
    rw [Ext.comp_assoc_of_second_deg_zero, Ext.mk₀_comp_mk₀,
      e.hom_inv_id, Ext.comp_mk₀_id]
  · intro x
    change (x.comp (Ext.mk₀ e.inv) (add_zero n)).comp (Ext.mk₀ e.hom) (add_zero n) = x
    rw [Ext.comp_assoc_of_second_deg_zero, Ext.mk₀_comp_mk₀,
      e.inv_hom_id, Ext.comp_mk₀_id]

lemma eulerCharacteristic_iso (f : X ⟶ Spec (CommRingCat.of ℂ))
    {M N : X.Modules} (e : M ≅ N) (d : ℕ) :
    eulerCharacteristic f d M = eulerCharacteristic f d N := by
  apply Finset.sum_congr rfl
  intro n _
  congr 2
  let := Module.compHom (cohomology M n) (baseScalars f)
  let := Module.compHom (cohomology N n) (baseScalars f)
  exact (cohomologyIso f e n).finrank_eq

end
end PiExponentSeshadri.Geometry

end OAI
end Source0434

-- Source: OAI/NumberTheory/PiExponent/Approximation/NumericalMarginRestriction.lean
section Source0435
-- Modified in this edition: unused plain lemmas removed; see reduction.json.
/-
Modification notice for the LogTwo project.
Derived from openai/math (Apache-2.0), revision adc7f1241b42e322a6451854ab7e4b4c146bf78a.
Original source: lean/OAI/NumberTheory/PiExponent/Approximation/NumericalMarginRestriction.lean
Changes: Convert module/import declarations to the Lean 4.34 public module format.
See ../THIRD_PARTY_NOTICES.txt for provenance and the recorded changes.
-/

namespace OAI

namespace PiExponent.NumericalAmpleness
noncomputable section
open CategoryTheory AlgebraicGeometry TopologicalSpace
open PiExponentSeshadri.Geometry

def curveDegree {X : Scheme.{0}} (p : X ⟶ Spec (CommRingCat.of ℂ))
    (L : LineBundle X) (C : IntegralCurve X) : ℤ :=
  eulerCharacteristic (C.embedding ≫ p) 1
    ((Scheme.Modules.pullback C.embedding).obj L.sheaf) -
  eulerCharacteristic (C.embedding ≫ p) 1 (structureSheaf C.scheme)

def IntegralCurve.mapClosed {X Y : Scheme.{0}} (C : IntegralCurve Y)
    (i : Y ⟶ X) [IsClosedImmersion i] : IntegralCurve X where
  scheme := C.scheme
  embedding := C.embedding ≫ i
  closedImmersion := inferInstance
  integral := C.integral
  dimension := C.dimension

theorem curveDegree_mapClosed {X Y : Scheme.{0}} (p : X ⟶ Spec (CommRingCat.of ℂ))
    (L : LineBundle X) (i : Y ⟶ X) [IsClosedImmersion i] (C : IntegralCurve Y) :
    curveDegree p L (C.mapClosed i) = curveDegree (i ≫ p) (L.pullback i) C := by
  unfold curveDegree IntegralCurve.mapClosed LineBundle.pullback
  simp only [Category.assoc]
  congr 1
  exact eulerCharacteristic_iso (C.embedding ≫ i ≫ p)
    ((Scheme.Modules.pullbackComp C.embedding i).app L.sheaf).symm 1

theorem uniform_curve_margin_restrict {X Y : Scheme.{0}}
    (p : X ⟶ Spec (CommRingCat.of ℂ)) (L H : LineBundle X) (ε : ℝ)
    (hmargin : ∀ C : IntegralCurve X,
      ε * (curveDegree p H C : ℝ) ≤ (curveDegree p L C : ℝ))
    (i : Y ⟶ X) [IsClosedImmersion i] :
    ∀ C : IntegralCurve Y,
      ε * (curveDegree (i ≫ p) (H.pullback i) C : ℝ) ≤
        (curveDegree (i ≫ p) (L.pullback i) C : ℝ) := by
  intro C
  simpa only [curveDegree_mapClosed] using hmargin (C.mapClosed i)

end
end PiExponent.NumericalAmpleness

end OAI
end Source0435

-- Source: OAI/NumberTheory/PiExponent/Cohomology/EulerExact.lean
section Source0436
-- Modified in this edition: unused plain lemmas removed; see reduction.json.
/-
Modification notice for the LogTwo project.
Derived from openai/math (Apache-2.0), revision adc7f1241b42e322a6451854ab7e4b4c146bf78a.
Original source: lean/OAI/NumberTheory/PiExponent/Cohomology/EulerExact.lean
Changes: Convert module/import declarations to the Lean 4.34 public module format.
See ../THIRD_PARTY_NOTICES.txt for provenance and the recorded changes.
-/

namespace OAI

noncomputable section

namespace PiExponentSeshadri

namespace Cohomology
open CategoryTheory CategoryTheory.Abelian

def alternatingTrunc (a : ℕ → ℤ) (d : ℕ) : ℤ :=
  ∑ i ∈ Finset.range (d+1), (-1 : ℤ)^i * a i

lemma alternatingTrunc_succ (a : ℕ → ℤ) (d : ℕ) :
    alternatingTrunc a (d+1) = alternatingTrunc a d + (-1 : ℤ)^(d+1) * a (d+1) := by
  exact Finset.sum_range_succ _ _

lemma finrank_middle_of_exact {K U V W : Type*} [Field K]
    [AddCommGroup U] [Module K U] [AddCommGroup V] [Module K V]
    [AddCommGroup W] [Module K W] [FiniteDimensional K V]
    (f : U →ₗ[K] V) (g : V →ₗ[K] W) (hfg : Function.Exact f g) :
    Module.finrank K V = Module.finrank K f.range + Module.finrank K g.range := by
  have hh := LinearMap.finrank_range_add_finrank_ker g
  rw [hfg.linearMap_ker_eq] at hh
  omega

universe w v u t
variable {K : Type t} [Field K] {C : Type u} [Category.{v} C] [Abelian C]
  [Linear K C] [HasExt.{w} C]

def extEuler (E M : C) (d : ℕ) : ℤ :=
  alternatingTrunc (fun n => Module.finrank K (Ext E M n)) d

variable (E : C) {S : ShortComplex C} (hS : S.ShortExact)

def cohomologyMap₁ (n : ℕ) : Ext E S.X₁ n →ₗ[K] Ext E S.X₂ n :=
  (Ext.mk₀ S.f).postcompOfLinear K E (add_zero n)

def cohomologyMap₂ (n : ℕ) : Ext E S.X₂ n →ₗ[K] Ext E S.X₃ n :=
  (Ext.mk₀ S.g).postcompOfLinear K E (add_zero n)

def cohomologyBoundary (n : ℕ) : Ext E S.X₃ n →ₗ[K] Ext E S.X₁ (n+1) :=
  hS.extClass.postcompOfLinear K E rfl

include hS in
lemma cohomology_exact₂ (n : ℕ) :
    Function.Exact (cohomologyMap₁ (K := K) E (S := S) n)
      (cohomologyMap₂ (K := K) E (S := S) n) := by
  intro x
  constructor
  · exact Ext.covariant_sequence_exact₂ E hS x
  · rintro ⟨y, rfl⟩
    change (y.comp (Ext.mk₀ S.f) (add_zero n)).comp (Ext.mk₀ S.g) (add_zero n) = 0
    simp [Ext.mk₀_comp_mk₀]

lemma cohomology_exact₃ (n : ℕ) :
    Function.Exact (cohomologyMap₂ (K := K) E (S := S) n)
      (cohomologyBoundary (K := K) E hS n) := by
  intro x
  constructor
  · exact Ext.covariant_sequence_exact₃ E hS x rfl
  · rintro ⟨y, rfl⟩
    change (y.comp (Ext.mk₀ S.g) (add_zero n)).comp hS.extClass rfl = 0
    rw [Ext.comp_assoc_of_second_deg_zero, hS.comp_extClass, Ext.comp_zero]

lemma cohomology_exact₁ (n : ℕ) :
    Function.Exact (cohomologyBoundary (K := K) E hS n)
      (cohomologyMap₁ (K := K) E (S := S) (n+1)) := by
  intro x
  constructor
  · exact fun hx => Ext.covariant_sequence_exact₁ E hS x hx rfl
  · rintro ⟨y, rfl⟩
    change (y.comp hS.extClass rfl).comp (Ext.mk₀ S.f) (add_zero (n+1)) = 0
    rw [Ext.comp_assoc_of_third_deg_zero, hS.extClass_comp, Ext.comp_zero]

theorem extEuler_add_of_boundary_zero (d : ℕ)
    (hfinite₁ : ∀ n ≤ d, FiniteDimensional K (Ext E S.X₁ n))
    (hfinite₂ : ∀ n ≤ d, FiniteDimensional K (Ext E S.X₂ n))
    (hfinite₃ : ∀ n ≤ d, FiniteDimensional K (Ext E S.X₃ n))
    (hvan : cohomologyBoundary (K := K) E hS d = 0) :
    extEuler (K := K) E S.X₂ d =
      extEuler (K := K) E S.X₁ d + extEuler (K := K) E S.X₃ d := by
  classical
  let a (n : ℕ) : ℤ := Module.finrank K (Ext E S.X₁ n)
  let b (n : ℕ) : ℤ := Module.finrank K (Ext E S.X₂ n)
  let c (n : ℕ) : ℤ := Module.finrank K (Ext E S.X₃ n)
  let f (n : ℕ) : ℤ := Module.finrank K (cohomologyMap₁ (K := K) E (S := S) n).range
  let g (n : ℕ) : ℤ := Module.finrank K (cohomologyMap₂ (K := K) E (S := S) n).range
  let h (n : ℕ) : ℤ := Module.finrank K (cohomologyBoundary (K := K) E hS n).range
  have hB (n : ℕ) (hn : n ≤ d) : b n = f n + g n := by
    let := hfinite₂ n hn
    dsimp only [b, f, g]
    exact_mod_cast finrank_middle_of_exact _ _ (cohomology_exact₂ (K := K) E hS n)
  have hC (n : ℕ) (hn : n ≤ d) : c n = g n + h n := by
    let := hfinite₃ n hn
    dsimp only [c, g, h]
    exact_mod_cast finrank_middle_of_exact _ _ (cohomology_exact₃ (K := K) E hS n)
  have hA0 : a 0 = f 0 := by
    have : Mono S.f := hS.mono_f
    dsimp only [a, f]
    exact_mod_cast (LinearMap.finrank_range_of_inj
      (f := cohomologyMap₁ (K := K) E (S := S) 0)
      (Ext.postcomp_mk₀_injective_of_mono E S.f)).symm
  have hA (n : ℕ) (hn : n+1 ≤ d) : a (n+1) = h n + f (n+1) := by
    let := hfinite₁ (n+1) hn
    dsimp only [a, h, f]
    exact_mod_cast finrank_middle_of_exact _ _ (cohomology_exact₁ (K := K) E hS n)
  have hind (n : ℕ) (hn : n ≤ d) :
      alternatingTrunc b n - alternatingTrunc a n - alternatingTrunc c n =
        (-1 : ℤ)^(n+1) * h n := by
    induction n with
    | zero => simp [alternatingTrunc, hB 0 hn, hC 0 hn, hA0]
    | succ n ih =>
      have hi := ih (by omega)
      simp only [alternatingTrunc_succ]
      calc
        _ = (alternatingTrunc b n - alternatingTrunc a n - alternatingTrunc c n) +
          (-1 : ℤ)^(n+1) * (b (n+1) - a (n+1) - c (n+1)) := by ring
        _ = _ := by rw [hi, hB (n+1) hn, hC (n+1) hn, hA n hn, pow_succ _ (n+1)]; ring
  have hd : h d = 0 := by
    dsimp only [h]
    rw [hvan, LinearMap.range_zero]
    rw [finrank_bot]
    rfl
  have hh := hind d le_rfl
  rw [hd, mul_zero] at hh
  change alternatingTrunc b d = alternatingTrunc a d + alternatingTrunc c d
  omega

include hS in

theorem extEuler_add (d : ℕ)
    (hfinite₁ : ∀ n ≤ d, FiniteDimensional K (Ext E S.X₁ n))
    (hfinite₂ : ∀ n ≤ d, FiniteDimensional K (Ext E S.X₂ n))
    (hfinite₃ : ∀ n ≤ d, FiniteDimensional K (Ext E S.X₃ n))
    [Subsingleton (Ext E S.X₁ (d+1))] :
    extEuler (K := K) E S.X₂ d =
      extEuler (K := K) E S.X₁ d + extEuler (K := K) E S.X₃ d :=
  extEuler_add_of_boundary_zero E hS d hfinite₁ hfinite₂ hfinite₃ (Subsingleton.elim _ _)

end Cohomology

namespace Geometry
open CategoryTheory CategoryTheory.Abelian AlgebraicGeometry
open scoped AlgebraicGeometry
variable {X : Scheme.{0}} (f : X ⟶ Spec (CommRingCat.of ℂ))

@[instance_reducible]
def sheafComplexLinear : Linear ℂ X.Modules where
  homModule M N := Module.compHom _ (baseScalars f)
  smul_comp M N P r g h := by
    change ((baseScalars f r) • g) ≫ h = (baseScalars f r) • (g ≫ h)
    exact Linear.smul_comp _ _ _ _ _ _
  comp_smul M N P g r h := by
    change g ≫ ((baseScalars f r) • h) = (baseScalars f r) • (g ≫ h)
    exact Linear.comp_smul _ _ _ _ _ _

@[instance_reducible]
def complexExtModule (M : X.Modules) (n : ℕ) : Module ℂ (cohomology M n) :=
  letI := sheafComplexLinear f
  inferInstance

lemma complexExtModule_eq (M : X.Modules) (n : ℕ) :
    complexExtModule f M n = Module.compHom (cohomology M n) (baseScalars f) := by
  apply Module.ext'
  intro r x
  let := sheafComplexLinear f
  change r • x = (baseScalars f r) • x
  rw [Ext.smul_eq_comp_mk₀ (R := ℂ), Ext.smul_eq_comp_mk₀ (R := Γ(X, ⊤))]
  rfl

lemma eulerCharacteristic_eq_extEuler (M : X.Modules) (d : ℕ) :
    eulerCharacteristic f d M =
      letI := sheafComplexLinear f
      Cohomology.extEuler (K := ℂ) (structureSheaf X) M d := by
  unfold eulerCharacteristic Cohomology.extEuler Cohomology.alternatingTrunc
  apply Finset.sum_congr rfl
  intro n hn
  have hh := complexExtModule_eq f M n
  unfold cohomologyDimension
  rw [← hh]

theorem eulerCharacteristic_add {S : ShortComplex X.Modules} (hS : S.ShortExact)
    (d : ℕ)
    (hfinite₁ : ∀ n ≤ d, letI := Module.compHom (cohomology S.X₁ n) (baseScalars f)
      FiniteDimensional ℂ (cohomology S.X₁ n))
    (hfinite₂ : ∀ n ≤ d, letI := Module.compHom (cohomology S.X₂ n) (baseScalars f)
      FiniteDimensional ℂ (cohomology S.X₂ n))
    (hfinite₃ : ∀ n ≤ d, letI := Module.compHom (cohomology S.X₃ n) (baseScalars f)
      FiniteDimensional ℂ (cohomology S.X₃ n))
    [Subsingleton (cohomology S.X₁ (d+1))] :
    eulerCharacteristic f d S.X₂ =
      eulerCharacteristic f d S.X₁ + eulerCharacteristic f d S.X₃ := by
  let := sheafComplexLinear f
  rw [eulerCharacteristic_eq_extEuler, eulerCharacteristic_eq_extEuler,
    eulerCharacteristic_eq_extEuler]
  apply Cohomology.extEuler_add (K := ℂ) (structureSheaf X) hS d
  · intro n hn
    have hh := complexExtModule_eq f S.X₁ n
    change @FiniteDimensional ℂ (cohomology S.X₁ n) _ _ (complexExtModule f S.X₁ n)
    rw [hh]
    exact hfinite₁ n hn
  · intro n hn
    have hh := complexExtModule_eq f S.X₂ n
    change @FiniteDimensional ℂ (cohomology S.X₂ n) _ _ (complexExtModule f S.X₂ n)
    rw [hh]
    exact hfinite₂ n hn
  · intro n hn
    have hh := complexExtModule_eq f S.X₃ n
    change @FiniteDimensional ℂ (cohomology S.X₃ n) _ _ (complexExtModule f S.X₃ n)
    rw [hh]
    exact hfinite₃ n hn

end Geometry

end PiExponentSeshadri

end

end OAI
end Source0436

-- Source: OAI/NumberTheory/PiExponent/Cohomology/CurveZeroEuler.lean
section Source0437
-- Modified in this edition: unused plain lemmas removed; see reduction.json.
/-
Modification notice for the LogTwo project.
Derived from openai/math (Apache-2.0), revision adc7f1241b42e322a6451854ab7e4b4c146bf78a.
Original source: lean/OAI/NumberTheory/PiExponent/Cohomology/CurveZeroEuler.lean
Changes: Convert module/import declarations to the Lean 4.34 public module format.
See ../THIRD_PARTY_NOTICES.txt for provenance and the recorded changes.
-/

namespace OAI

noncomputable section
open CategoryTheory AlgebraicGeometry
open PiExponentSeshadri.Geometry

namespace PiExponent.CurveZeroEuler

def algebraStructureMap (B : Type) [CommRing B] [Algebra ℂ B] :
    Spec (CommRingCat.of B) ⟶ Spec (CommRingCat.of ℂ) :=
  Spec.map (CommRingCat.ofHom (algebraMap ℂ B))

def specStructureSectionsEquiv (B : Type) [CommRing B] [Algebra ℂ B] :
    letI : Module ℂ Γ(structureSheaf (Spec (CommRingCat.of B)), ⊤) :=
      Module.compHom _ (baseScalars (algebraStructureMap B))
    Γ(structureSheaf (Spec (CommRingCat.of B)), ⊤) ≃ₗ[ℂ] B := by
  letI : Module ℂ Γ(structureSheaf (Spec (CommRingCat.of B)), ⊤) :=
    Module.compHom _ (baseScalars (algebraStructureMap B))
  refine { ((Scheme.ΓSpecIso (CommRingCat.of B)).commRingCatIsoToRingEquiv).toAddEquiv with
    map_smul' := ?_ }
  intro c x
  change Γ(Spec (CommRingCat.of B), ⊤) at x
  change (Scheme.ΓSpecIso (CommRingCat.of B)).hom
    (baseScalars (algebraStructureMap B) c * x) =
      c • (Scheme.ΓSpecIso (CommRingCat.of B)).hom x
  rw [Algebra.smul_def]
  rw [map_mul]
  congr 1
  change ((Spec.map (CommRingCat.ofHom (algebraMap ℂ B))).appTop ≫
    (Scheme.ΓSpecIso (CommRingCat.of B)).hom)
      ((Scheme.ΓSpecIso (CommRingCat.of ℂ)).inv c) = _
  rw [Scheme.ΓSpecIso_naturality]
  simp

end PiExponent.CurveZeroEuler

end

end OAI
end Source0437

-- Source: OAI/NumberTheory/PiExponent/Cohomology/FiniteZeroEuler.lean
section Source0438
-- Modified in this edition: unused plain lemmas removed; see reduction.json.
/-
Modification notice for the LogTwo project.
Derived from openai/math (Apache-2.0), revision adc7f1241b42e322a6451854ab7e4b4c146bf78a.
Original source: lean/OAI/NumberTheory/PiExponent/Cohomology/FiniteZeroEuler.lean
Changes: Convert module/import declarations to the Lean 4.34 public module format.
See ../THIRD_PARTY_NOTICES.txt for provenance and the recorded changes.
-/

namespace OAI

noncomputable section
open scoped BigOperators
open AlgebraicGeometry PiExponentSeshadri.Geometry

namespace PiExponent.FiniteZeroEuler

theorem finrank_eq_sum_localizations
    (B : Type*) [CommRing B] [IsArtinianRing B]
    (F : Type*) [Field F] [Algebra F B] [Module.Finite F B]
    [Fintype (MaximalSpectrum B)] :
    Module.finrank F B = ∑ m : MaximalSpectrum B,
      Module.finrank F (Localization.AtPrime m.asIdeal) := by
  let : ∀ m : MaximalSpectrum B, Module.Finite F (Localization.AtPrime m.asIdeal) :=
    fun m => Module.Finite.of_surjective (IsScalarTower.toAlgHom F B
      (Localization.AtPrime m.asIdeal)).toLinearMap
      (IsArtinianRing.localization_surjective m.asIdeal.primeCompl _)
  have e := (MaximalSpectrum.toPiLocalizationEquiv B).restrictScalars F
  rw [e.toLinearEquiv.finrank_eq, Module.finrank_pi_fintype]

end PiExponent.FiniteZeroEuler

end

end OAI
end Source0438

-- Source: OAI/NumberTheory/PiExponent/Geometry/FiniteCurveZeros.lean
section Source0439
-- Modified in this edition: unused plain lemmas removed; see reduction.json.
/-
Modification notice for the LogTwo project.
Derived from openai/math (Apache-2.0), revision adc7f1241b42e322a6451854ab7e4b4c146bf78a.
Original source: lean/OAI/NumberTheory/PiExponent/Geometry/FiniteCurveZeros.lean
Changes: Convert module/import declarations to the Lean 4.34 public module format.
See ../THIRD_PARTY_NOTICES.txt for provenance and the recorded changes.
-/

namespace OAI

noncomputable section

namespace PiExponentSeshadri.Geometry

section
open AlgebraicGeometry CategoryTheory TopologicalSpace
variable {K : Type} [Field K] {X Y : Scheme}

lemma proper_finite_scheme_isFinite (f : X ⟶ Y) [IsProper f] [Finite X] : IsFinite f := by
  let : LocallyQuasiFinite f := .of_finite_preimage_singleton f (fun _ => Set.toFinite _)
  exact .of_isProper_of_locallyQuasiFinite f

lemma proper_finite_scheme_isAffine (f : X ⟶ Spec (CommRingCat.of K))
    [IsProper f] [Finite X] : IsAffine X := by
  let : IsFinite f := proper_finite_scheme_isFinite f
  exact isAffine_of_isAffineHom f

lemma proper_finite_functions (f : X ⟶ Spec (CommRingCat.of K))
    [IsProper f] [Finite X] :
    let _ : Algebra K Γ(X,⊤) :=
      (f.appTop.hom.comp (Scheme.ΓSpecIso (CommRingCat.of K)).inv.hom).toAlgebra
    FiniteDimensional K Γ(X,⊤) := by
  let : IsFinite f := proper_finite_scheme_isFinite f
  dsimp only
  exact f.finite_appTop.comp (RingHom.Finite.of_surjective
    (Scheme.ΓSpecIso (CommRingCat.of K)).inv.hom (by
      exact (Scheme.ΓSpecIso (CommRingCat.of K)).symm.commRingCatIsoToRingEquiv.surjective))

lemma proper_finite_germ_surjective (f : X ⟶ Spec (CommRingCat.of K))
    [IsProper f] [Finite X] (x : X) :
    Function.Surjective (X.presheaf.germ ⊤ x trivial) := by
  let : IsAffine X := proper_finite_scheme_isAffine f
  let : Algebra K Γ(X,⊤) :=
    (f.appTop.hom.comp (Scheme.ΓSpecIso (CommRingCat.of K)).inv.hom).toAlgebra
  let : FiniteDimensional K Γ(X,⊤) := proper_finite_functions f
  let : IsArtinianRing Γ(X,⊤) := IsArtinianRing.of_finite K Γ(X,⊤)
  let : Algebra Γ(X,⊤) (X.presheaf.stalk x) :=
    TopCat.Presheaf.algebra_section_stalk X.presheaf (⟨x,trivial⟩ : (⊤ : X.Opens))
  let p : PrimeSpectrum Γ(X,⊤) := (isAffineOpen_top X).isoSpec.hom ⟨x,trivial⟩
  let : IsLocalization.AtPrime (X.presheaf.stalk x) p.asIdeal :=
    (isAffineOpen_top X).isLocalization_stalk ⟨x,trivial⟩
  exact IsArtinianRing.localization_surjective p.asIdeal.primeCompl (X.presheaf.stalk x)

end

section
open TopologicalSpace Set

variable {X : Type*} [TopologicalSpace X] [T0Space X] [IrreducibleSpace X]

lemma proper_irreducible_closed_subsingleton
    (hd : topologicalKrullDim X ≤ 1) {Z : Set X} (hZ : IsClosed Z)
    (hi : IsIrreducible Z) (hp : Z ≠ Set.univ) : Z.Subsingleton := by
  let C : IrreducibleCloseds X := ⟨Z, hi, hZ⟩
  let T : IrreducibleCloseds X := ⟨Set.univ, IrreducibleSpace.isIrreducible_univ X, isClosed_univ⟩
  have hmin : IsMin C := by
    rcases Order.krullDim_le_one_iff.mp hd C with hm | hm
    · exact hm
    · have he : C = T := le_antisymm (Set.subset_univ _) (hm (Set.subset_univ _))
      exact (hp (congrArg SetLike.coe he)).elim
  have hg (x : X) (hx : x ∈ Z) : IsGenericPoint x Z := by
    let D : IrreducibleCloseds X :=
      ⟨closure {x}, isIrreducible_singleton.closure, isClosed_closure⟩
    have hle : D ≤ C := closure_minimal (Set.singleton_subset_iff.mpr hx) hZ
    have he : D = C := le_antisymm hle (hmin hle)
    exact congrArg SetLike.coe he
  intro x hx y hy
  exact (hg x hx).eq (hg y hy)

theorem proper_closed_finite_of_dimension_one [NoetherianSpace X]
    (hd : topologicalKrullDim X ≤ 1) {Z : Set X} (hZ : IsClosed Z)
    (hp : Z ≠ Set.univ) : Z.Finite := by
  obtain ⟨F, hF, hFc, hFi, hZF⟩ :=
    NoetherianSpace.exists_finite_set_isClosed_irreducible hZ
  rw [hZF]
  apply hF.sUnion
  intro C hC
  apply Set.Subsingleton.finite
  apply proper_irreducible_closed_subsingleton hd (hFc C hC) (hFi C hC)
  intro hc
  apply hp
  apply Set.eq_univ_of_univ_subset
  rw [hZF]
  exact hc ▸ Set.subset_sUnion_of_mem hC

open AlgebraicGeometry in

theorem integral_curve_proper_closed_finite (C : Scheme)
    [IsIntegral C] [IsNoetherian C] (hd : topologicalKrullDim C = 1)
    {Z : Set C} (hZ : IsClosed Z) (hp : Z ≠ Set.univ) : Z.Finite :=
  proper_closed_finite_of_dimension_one hd.le hZ hp

end

section
open AlgebraicGeometry CategoryTheory TopologicalSpace
variable {K : Type} [Field K] {X : Scheme}

theorem finite_subscheme_of_curve [IsIntegral X]
    (f : X ⟶ Spec (CommRingCat.of K)) [IsProper f]
    (hd : topologicalKrullDim X ≤ 1) (I : X.IdealSheafData) (hI : I ≠ ⊥) :
    Finite I.subscheme := by
  let : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace f
  let : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian f
  let : IsNoetherian X := ⟨⟩
  have hp : (I.support : Set X) ≠ Set.univ := by
    intro he
    apply hI
    exact Scheme.IdealSheafData.support_eq_top_iff.mp (SetLike.coe_injective he)
  have hf := proper_closed_finite_of_dimension_one hd I.support.isClosed hp
  have hr : (Set.range I.subschemeι).Finite := I.range_subschemeι ▸ hf
  let : Finite (Set.range I.subschemeι) := hr.to_subtype
  exact Finite.of_injective (fun x : I.subscheme =>
    (⟨I.subschemeι x, ⟨x,rfl⟩⟩ : Set.range I.subschemeι))
    (fun a b h => I.subschemeι.isEmbedding.injective (congrArg (fun z : Set.range I.subschemeι => (z : X)) h))

abbrev structuralStalkAlgebra (f : X ⟶ Spec (CommRingCat.of K)) (x : X) :
    Algebra K (X.presheaf.stalk x) :=
  ((X.presheaf.germ ⊤ x trivial).hom.comp
    (f.appTop.hom.comp (Scheme.ΓSpecIso (CommRingCat.of K)).inv.hom)).toAlgebra

theorem proper_finite_finrank_eq_sum_stalks (f : X ⟶ Spec (CommRingCat.of K))
    [IsProper f] [Fintype X] :
    let _ : Algebra K Γ(X,⊤) :=
      (f.appTop.hom.comp (Scheme.ΓSpecIso (CommRingCat.of K)).inv.hom).toAlgebra
    Module.finrank K Γ(X,⊤) = ∑ x : X,
      let _ := structuralStalkAlgebra f x
      Module.finrank K (X.presheaf.stalk x) := by
  classical
  dsimp only
  let : IsAffine X := proper_finite_scheme_isAffine f
  let : Algebra K Γ(X,⊤) :=
    (f.appTop.hom.comp (Scheme.ΓSpecIso (CommRingCat.of K)).inv.hom).toAlgebra
  let : FiniteDimensional K Γ(X,⊤) := proper_finite_functions f
  let : IsArtinianRing Γ(X,⊤) := IsArtinianRing.of_finite K Γ(X,⊤)
  let : Fintype (MaximalSpectrum Γ(X,⊤)) := Fintype.ofFinite _
  let e : X ≃ MaximalSpectrum Γ(X,⊤) :=
    (Equiv.Set.univ X).symm.trans ((isAffineOpen_top X).isoSpec.hom.homeomorph.toEquiv.trans
      IsArtinianRing.primeSpectrumEquivMaximalSpectrum)
  rw [PiExponent.FiniteZeroEuler.finrank_eq_sum_localizations Γ(X,⊤) K, ← e.sum_comp]
  apply Finset.sum_congr rfl
  intro x _
  let : Algebra Γ(X,⊤) (X.presheaf.stalk x) :=
    TopCat.Presheaf.algebra_section_stalk X.presheaf (⟨x,trivial⟩ : (⊤ : X.Opens))
  let : Algebra K (X.presheaf.stalk x) := structuralStalkAlgebra f x
  let : IsScalarTower K Γ(X,⊤) (X.presheaf.stalk x) := IsScalarTower.of_algebraMap_eq' rfl
  let : IsLocalization.AtPrime (X.presheaf.stalk x) (e x).asIdeal :=
    (isAffineOpen_top X).isLocalization_stalk ⟨x,trivial⟩
  exact ((IsLocalization.algEquiv (e x).asIdeal.primeCompl
    (Localization.AtPrime (e x).asIdeal) (X.presheaf.stalk x)).restrictScalars K).toLinearEquiv.finrank_eq

end

open AlgebraicGeometry CategoryTheory
variable {X : Scheme.{0}}

theorem proper_finite_euler (f : X ⟶ Spec (CommRingCat.of ℂ))
    [IsProper f] [Finite X] (d : ℕ) :
    eulerCharacteristic f d (structureSheaf X) =
      let _ : Algebra ℂ Γ(X,⊤) := (baseScalars f).toAlgebra
      (Module.finrank ℂ Γ(X,⊤) : ℤ) := by
  let : IsAffine X := proper_finite_scheme_isAffine f
  let : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian f
  let : IsNoetherian X := ⟨⟩
  let L : LineBundle X := ⟨structureSheaf X, fun x =>
    ⟨⊤, trivial, ⟨Scheme.Modules.restrictUnitIso (⊤ : X.Opens).ι⟩⟩⟩
  let : (structureSheaf X).IsQuasicoherent :=
    PiExponent.GeometrySupport.LineBundleCoherent.modulePow_isQuasicoherent L 0
  exact affine_eulerCharacteristic f (structureSheaf X) d

theorem proper_finite_euler_eq_sum_stalk_finrank
    (f : X ⟶ Spec (CommRingCat.of ℂ)) [IsProper f] [Fintype X] (d : ℕ) :
    eulerCharacteristic f d (structureSheaf X) = ∑ x : X,
      letI := structuralStalkAlgebra f x
      (Module.finrank ℂ (X.presheaf.stalk x) : ℤ) := by
  rw [proper_finite_euler]
  dsimp only
  have h := proper_finite_finrank_eq_sum_stalks f
  dsimp only at h
  exact_mod_cast h

theorem proper_finite_euler_eq_sum_stalk_lengths
    (f : X ⟶ Spec (CommRingCat.of ℂ)) [IsProper f] [Fintype X] (d : ℕ) :
    eulerCharacteristic f d (structureSheaf X) = ∑ x : X,
      ((Module.length (X.presheaf.stalk x) (X.presheaf.stalk x)).toNat : ℤ) := by
  rw [proper_finite_euler_eq_sum_stalk_finrank]
  apply Finset.sum_congr rfl
  intro x _
  let : Algebra ℂ Γ(X, ⊤) := (baseScalars f).toAlgebra
  let : Algebra Γ(X, ⊤) (X.presheaf.stalk x) :=
    TopCat.Presheaf.algebra_section_stalk X.presheaf (⟨x, trivial⟩ : (⊤ : X.Opens))
  let : Algebra ℂ (X.presheaf.stalk x) := structuralStalkAlgebra f x
  let : IsScalarTower ℂ Γ(X, ⊤) (X.presheaf.stalk x) :=
    IsScalarTower.of_algebraMap_eq' rfl
  let : Module.Finite ℂ Γ(X, ⊤) := proper_finite_functions f
  let φ := (IsScalarTower.toAlgHom ℂ Γ(X, ⊤) (X.presheaf.stalk x)).toLinearMap
  let : Module.Finite ℂ (X.presheaf.stalk x) :=
    Module.Finite.of_surjective φ (proper_finite_germ_surjective f x)
  have h := PiExponentJets.W24.ring_length_eq_finrank_of_augmentation
    (PiExponent.CurveLocalOrder.residueAugmentation ℂ (X.presheaf.stalk x))
    (PiExponent.CurveLocalOrder.residueAugmentation_algebraMap ℂ (X.presheaf.stalk x))
  rw [h]
  simp

end PiExponentSeshadri.Geometry

end

end OAI
end Source0439

-- Source: OAI/NumberTheory/PiExponent/Cohomology/FiniteSupportCohomology.lean
section Source0440
-- Modified in this edition: unused plain lemmas removed; see reduction.json.
/-
Modification notice for the LogTwo project.
Derived from openai/math (Apache-2.0), revision adc7f1241b42e322a6451854ab7e4b4c146bf78a.
Original source: lean/OAI/NumberTheory/PiExponent/Cohomology/FiniteSupportCohomology.lean
Changes: Convert module/import declarations to the Lean 4.34 public module format.
See ../THIRD_PARTY_NOTICES.txt for provenance and the recorded changes.
-/

namespace OAI

noncomputable section

namespace PiExponentSeshadri.FiniteSupport

section
open CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite AlgebraicGeometry
lemma discrete_restriction_surjective {X : TopCat.{0}} [DiscreteTopology X]
    (F : X.Sheaf AddCommGrpCat.{0}) {U V : Opens X} (i : V ⟶ U) :
    Function.Surjective (F.obj.map i.op) := by
  classical
  intro s
  let W : Opens X := ⟨(U : Set X) \ V, isOpen_discrete _⟩
  let D : Bool → Opens X := fun b => if b then V else W
  let e : ∀ b, D b ⟶ U := fun b => homOfLE (by
    cases b
    · exact fun x hx => hx.1
    · exact i.le)
  have hcover : U ≤ ⨆ b, D b := by
    intro x hx
    by_cases hV : x ∈ V
    · exact Opens.mem_iSup.mpr ⟨true,hV⟩
    · exact Opens.mem_iSup.mpr ⟨false,hx,hV⟩
  let t : ∀ b, F.obj.obj (op (D b)) := fun b => match b with
    | true => s
    | false => 0
  have hc : TopCat.Presheaf.IsCompatible F.obj D t := by
    intro b c
    cases b <;> cases c
    · rfl
    · have h : D false ⊓ D true = ⊥ := by
        ext x
        change ((x ∈ U ∧ x ∉ V) ∧ x ∈ V) ↔ False
        tauto
      let : Subsingleton (F.obj.obj (op (D false ⊓ D true))) :=
        AddCommGrpCat.subsingleton_of_isZero (F.isTerminalOfEqEmpty h).isZero
      exact Subsingleton.elim _ _
    · have h : D true ⊓ D false = ⊥ := by
        ext x
        change (x ∈ V ∧ x ∈ U ∧ x ∉ V) ↔ False
        tauto
      let : Subsingleton (F.obj.obj (op (D true ⊓ D false))) :=
        AddCommGrpCat.subsingleton_of_isZero (F.isTerminalOfEqEmpty h).isZero
      exact Subsingleton.elim _ _
    · rfl
  obtain ⟨a,ha,_⟩ := F.existsUnique_gluing' D U e hcover t hc
  exact ⟨a,ha true⟩

variable {X Y : Scheme.{0}}

lemma proper_finite_discrete (p : X ⟶ Spec (CommRingCat.of ℂ))
    [IsProper p] [Finite X] : DiscreteTopology X := by
  let : IsFinite p := Geometry.proper_finite_scheme_isFinite p
  have he : p ⁻¹' ({⟨⊥, Ideal.isPrime_bot⟩} : Set (Spec (CommRingCat.of ℂ))) = Set.univ := by
    ext x
    simp only [Set.mem_preimage, Set.mem_univ, iff_true]
    exact Subsingleton.elim _ _
  have h := p.isDiscrete_preimage_singleton (⟨⊥, Ideal.isPrime_bot⟩ : PrimeSpectrum ℂ)
  rw [he] at h
  exact isDiscrete_univ_iff.mp h

lemma pushforward_flasque (f : X ⟶ Y) [DiscreteTopology X] (M : X.Modules) :
    TopCat.Sheaf.IsFlasque ((SheafOfModules.toSheaf Y.ringCatSheaf).obj
      ((Scheme.Modules.pushforward f).obj M)) where
  epi i := by
    apply (AddCommGrpCat.epi_iff_surjective _).mpr
    exact discrete_restriction_surjective
      ((SheafOfModules.toSheaf X.ringCatSheaf).obj M)
      ((Opens.map f.base).map i.unop)

theorem finite_pushforward_ext_zero (p : X ⟶ Spec (CommRingCat.of ℂ))
    [IsProper p] [Finite X] (f : X ⟶ Y) (M : X.Modules) (n : ℕ)
    (z : Geometry.cohomology ((Scheme.Modules.pushforward f).obj M) (n+1)) : z = 0 := by
  let : DiscreteTopology X := proper_finite_discrete p
  let := pushforward_flasque f M
  exact FlasqueCohomology.flasque_ext_zero Y.ringCatSheaf n _ z

def pushforwardUnitSections (f : X ⟶ Y) (g : Y ⟶ Spec (CommRingCat.of ℂ)) :
    let _ : Module ℂ Γ((Scheme.Modules.pushforward f).obj (Geometry.structureSheaf X),⊤) :=
      Module.compHom _ (Geometry.baseScalars g)
    let _ : Algebra ℂ Γ(X,⊤) := (Geometry.baseScalars (f ≫ g)).toAlgebra
    Γ((Scheme.Modules.pushforward f).obj (Geometry.structureSheaf X),⊤) ≃ₗ[ℂ] Γ(X,⊤) := by
  dsimp only
  letI : Module ℂ Γ((Scheme.Modules.pushforward f).obj (Geometry.structureSheaf X),⊤) :=
    Module.compHom _ (Geometry.baseScalars g)
  letI : Algebra ℂ Γ(X,⊤) := (Geometry.baseScalars (f ≫ g)).toAlgebra
  refine { Equiv.refl _ with map_add' := fun _ _ => rfl, map_smul' := ?_ }
  intro r a
  change Γ(X,⊤) at a
  change (f.appTop) (Geometry.baseScalars g r) * a = Geometry.baseScalars (f ≫ g) r * a
  congr 1

theorem finite_pushforward_euler (f : X ⟶ Y) (g : Y ⟶ Spec (CommRingCat.of ℂ))
    [IsProper (f ≫ g)] [Finite X] (d : ℕ) :
    Geometry.eulerCharacteristic g d
      ((Scheme.Modules.pushforward f).obj (Geometry.structureSheaf X)) =
      let _ : Algebra ℂ Γ(X,⊤) := (Geometry.baseScalars (f ≫ g)).toAlgebra
      (Module.finrank ℂ Γ(X,⊤) : ℤ) := by
  let M := (Scheme.Modules.pushforward f).obj (Geometry.structureSheaf X)
  unfold Geometry.eulerCharacteristic
  rw [Finset.sum_eq_single 0]
  · simp only [pow_zero, one_mul, Geometry.cohomologyDimension_zero]
    let : Module ℂ Γ(M,⊤) := Module.compHom _ (Geometry.baseScalars g)
    let : Algebra ℂ Γ(X,⊤) := (Geometry.baseScalars (f ≫ g)).toAlgebra
    exact_mod_cast (pushforwardUnitSections f g).finrank_eq
  · intro n hn hn0
    obtain ⟨m,rfl⟩ := Nat.exists_eq_succ_of_ne_zero hn0
    have : Subsingleton (Geometry.cohomology M (m+1)) :=
      ⟨fun x y => (finite_pushforward_ext_zero (f ≫ g) f _ m x).trans
        (finite_pushforward_ext_zero (f ≫ g) f _ m y).symm⟩
    simp [Geometry.cohomologyDimension, Module.finrank_zero_of_subsingleton]
  · simp

end

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry PiExponentSeshadri.Geometry
variable {X Y : Scheme.{0}}

theorem finite_pushforward_finiteDimensional (f : X ⟶ Y)
    (g : Y ⟶ Spec (CommRingCat.of ℂ)) [IsProper (f ≫ g)] [Finite X] (n : ℕ) :
    let M := (Scheme.Modules.pushforward f).obj (structureSheaf X)
    let _ := Module.compHom (cohomology M n) (baseScalars g)
    FiniteDimensional ℂ (cohomology M n) := by
  let M := (Scheme.Modules.pushforward f).obj (structureSheaf X)
  let := Module.compHom (cohomology M n) (baseScalars g)
  cases n with
  | zero =>
    let : Module ℂ Γ(M,⊤) := Module.compHom _ (baseScalars g)
    let : Algebra ℂ Γ(X,⊤) := (baseScalars (f ≫ g)).toAlgebra
    let : FiniteDimensional ℂ Γ(X,⊤) := proper_finite_functions (f ≫ g)
    let e := (cohomologyZeroSections g M).trans (pushforwardUnitSections f g)
    exact Module.Finite.of_surjective e.symm.toLinearMap e.symm.surjective
  | succ n =>
    let : Subsingleton (cohomology M (n+1)) :=
      ⟨fun x y => (finite_pushforward_ext_zero (f ≫ g) f _ n x).trans
        (finite_pushforward_ext_zero (f ≫ g) f _ n y).symm⟩
    infer_instance

end PiExponentSeshadri.FiniteSupport

end

end OAI
end Source0440

-- Source: OAI/NumberTheory/PiExponent/Cohomology/FiniteLineEuler.lean
section Source0441
-- Modified in this edition: unused plain lemmas removed; see reduction.json.
/-
Modification notice for the LogTwo project.
Derived from openai/math (Apache-2.0), revision adc7f1241b42e322a6451854ab7e4b4c146bf78a.
Original source: lean/OAI/NumberTheory/PiExponent/Cohomology/FiniteLineEuler.lean
Changes: Convert module/import declarations to the Lean 4.34 public module format.
See ../THIRD_PARTY_NOTICES.txt for provenance and the recorded changes.
-/

namespace OAI

noncomputable section

namespace PiExponentSeshadri.Geometry
open AlgebraicGeometry CategoryTheory TopologicalSpace
variable {X : Scheme.{0}}

def overFrame {M : X.Modules} {U : X.Opens}
    (e : M.restrict U.ι ≅ structureSheaf U.toScheme) :
    M.over U ≅ SheafOfModules.unit (X.ringCatSheaf.over U) :=
  (Scheme.Modules.overEquiv U).fullyFaithfulFunctor.preimageIso
    ((Scheme.Modules.overFunctorEquiv U).app M ≪≫ e ≪≫
      (Opens.sheafOfModulesEquivOverUnit U X.ringCatSheaf).symm)
end PiExponentSeshadri.Geometry

namespace PiExponentSeshadri.FiniteSupport

section
open CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite AlgebraicGeometry
open PiExponentSeshadri.Geometry
variable {X : Scheme.{0}} [DiscreteTopology X]

def pointOpen (x : X) : X.Opens := ⟨{x}, isOpen_discrete _⟩

lemma pointOpen_basis : Opens.IsBasis (Set.range (pointOpen (X := X))) := by
  apply Opens.isBasis_iff_nbhd.mpr
  intro U x hx
  exact ⟨pointOpen x, ⟨x,rfl⟩, rfl, fun y hy => by cases hy; exact hx⟩

def pointFrame (L : LineBundle X) (x : X) :
    L.sheaf.val.obj (op (pointOpen x)) ≅
      (structureSheaf X).val.obj (op (pointOpen x)) := by
  let U := (L.locallyRankOne x).choose
  have hx := (L.locallyRankOne x).choose_spec.1
  let e := (L.locallyRankOne x).choose_spec.2.some
  let h : pointOpen x ≤ U := fun y hy => by cases hy; exact hx
  let e' := overFrame e
  exact (SheafOfModules.evaluation (X.ringCatSheaf.over U) (op (Over.mk (homOfLE h)))).mapIso e'

theorem lineBundle_trivial (L : LineBundle X) : Nonempty (L.sheaf ≅ structureSheaf X) := by
  classical
  let F : TopCat.Sheaf AddCommGrpCat.{0} X.toTopCat :=
    (SheafOfModules.toSheaf.{0} X.ringCatSheaf).obj L.sheaf
  let B := pointOpen (X := X)
  let t : ∀ x, Γ(L.sheaf,B x) := fun x => (pointFrame L x).inv (1 : Γ(X,B x))
  have hc : TopCat.Presheaf.IsCompatible F.obj B t := by
    intro x y
    by_cases h : x = y
    · subst y; rfl
    · have he : B x ⊓ B y = ⊥ := by
        ext z
        change (z = x ∧ z = y) ↔ False
        constructor
        · rintro ⟨rfl,h'⟩; exact h h'
        · tauto
      let : Subsingleton (F.obj.obj (op (B x ⊓ B y))) :=
        AddCommGrpCat.subsingleton_of_isZero (F.isTerminalOfEqEmpty he).isZero
      exact Subsingleton.elim _ _
  have hcover : (⊤ : X.Opens) ≤ ⨆ x, B x := by
    intro x _
    exact Opens.mem_iSup.mpr ⟨x,rfl⟩
  obtain ⟨a,ha,_⟩ := F.existsUnique_gluing' B ⊤ (fun _ => homOfLE le_top) hcover t hc
  let s : structureSheaf X ⟶ L.sheaf :=
    (FlasqueCohomology.globalHomEquiv X.ringCatSheaf L.sheaf).symm a
  have hs (x : X) : s.val.app (op (B x)) = (pointFrame L x).inv := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro r
    change Γ(X,B x) at r
    have hs1 : s.val.app (op (B x)) (1 : Γ(X,B x)) = t x := by
      have htop : s.app ⊤ (1 : Γ(X,⊤)) = a :=
        (FlasqueCohomology.globalHomEquiv X.ringCatSheaf L.sheaf).apply_symm_apply a
      have hn := CategoryTheory.congr_fun (s.mapPresheaf.naturality
        (homOfLE (show B x ≤ ⊤ from le_top)).op) (1 : Γ(X,⊤))
      change s.app (B x) (X.presheaf.map (homOfLE le_top).op 1) =
        L.sheaf.presheaf.map (homOfLE le_top).op (s.app ⊤ (1 : Γ(X,⊤))) at hn
      have hax : L.sheaf.presheaf.map (homOfLE (show B x ≤ ⊤ from le_top)).op a = t x := ha x
      have hn' : s.app (B x) (1 : Γ(X,B x)) =
          L.sheaf.presheaf.map (homOfLE le_top).op a := by
        simpa only [map_one, htop] using hn
      exact hn'.trans hax
    let : Module Γ(X,B x) (L.sheaf.val.obj (op (B x))) :=
      (L.sheaf.val.obj (op (B x))).isModule
    calc
      s.val.app (op (B x)) r = r • s.val.app (op (B x)) (1 : Γ(X,B x)) := by
        exact (congrArg (s.val.app (op (B x))) (mul_one r).symm).trans
          ((s.val.app (op (B x))).hom.map_smul r (1 : Γ(X,B x)))
      _ = r • (pointFrame L x).inv (1 : Γ(X,B x)) := by rw [hs1]
      _ = (pointFrame L x).inv r := by
        exact ((pointFrame L x).inv.hom.map_smul r (1 : Γ(X,B x))).symm.trans
          (congrArg (pointFrame L x).inv (mul_one r))
  have hiso : IsIso ((SheafOfModules.toSheaf.{0} X.ringCatSheaf).map s) := by
    apply TopCat.Sheaf.isIso_iff_isIso_basis pointOpen_basis
    intro x
    change IsIso ((forget₂ (ModuleCat _) AddCommGrpCat).map (s.val.app (op (B x))))
    rw [hs]
    infer_instance
  let : Mono s := (SheafOfModules.toSheaf.{0} X.ringCatSheaf).mono_of_mono_map inferInstance
  let : Epi s := (SheafOfModules.toSheaf.{0} X.ringCatSheaf).epi_of_epi_map inferInstance
  let : IsIso s := isIso_of_mono_of_epi s
  exact ⟨(asIso s).symm⟩

end

open CategoryTheory AlgebraicGeometry PiExponentSeshadri.Geometry
variable {X Y : Scheme.{0}}

theorem finite_line_pushforward_euler (f : X ⟶ Y)
    (g : Y ⟶ Spec (CommRingCat.of ℂ)) [IsProper (f ≫ g)] [Finite X]
    (L : LineBundle X) (d : ℕ) :
    eulerCharacteristic g d ((Scheme.Modules.pushforward f).obj L.sheaf) =
      let _ : Algebra ℂ Γ(X,⊤) := (baseScalars (f ≫ g)).toAlgebra
      (Module.finrank ℂ Γ(X,⊤) : ℤ) := by
  let : DiscreteTopology X := proper_finite_discrete (f ≫ g)
  obtain ⟨e⟩ := lineBundle_trivial L
  rw [eulerCharacteristic_iso g ((Scheme.Modules.pushforward f).mapIso e) d]
  exact finite_pushforward_euler f g d

theorem finite_line_pushforward_finiteDimensional (f : X ⟶ Y)
    (g : Y ⟶ Spec (CommRingCat.of ℂ)) [IsProper (f ≫ g)] [Finite X]
    (L : LineBundle X) (n : ℕ) :
    let M := (Scheme.Modules.pushforward f).obj L.sheaf
    let _ := Module.compHom (cohomology M n) (baseScalars g)
    FiniteDimensional ℂ (cohomology M n) := by
  let : DiscreteTopology X := proper_finite_discrete (f ≫ g)
  obtain ⟨e⟩ := lineBundle_trivial L
  let M := (Scheme.Modules.pushforward f).obj L.sheaf
  let N := (Scheme.Modules.pushforward f).obj (structureSheaf X)
  let := Module.compHom (cohomology M n) (baseScalars g)
  let := Module.compHom (cohomology N n) (baseScalars g)
  let : FiniteDimensional ℂ (cohomology N n) := finite_pushforward_finiteDimensional f g n
  exact Module.Finite.of_surjective
    (cohomologyIso g ((Scheme.Modules.pushforward f).mapIso e) n).symm.toLinearMap
    (cohomologyIso g ((Scheme.Modules.pushforward f).mapIso e) n).symm.surjective

theorem finite_line_euler_eq_sum_stalk_lengths (f : X ⟶ Y)
    (g : Y ⟶ Spec (CommRingCat.of ℂ)) [IsProper (f ≫ g)] [Fintype X]
    (L : LineBundle X) (d : ℕ) :
    eulerCharacteristic g d ((Scheme.Modules.pushforward f).obj L.sheaf) =
      ∑ x : X, ((Module.length (X.presheaf.stalk x) (X.presheaf.stalk x)).toNat : ℤ) := by
  calc
    _ = eulerCharacteristic (f ≫ g) d (structureSheaf X) :=
      (finite_line_pushforward_euler f g L d).trans (proper_finite_euler (f ≫ g) d).symm
    _ = _ := proper_finite_euler_eq_sum_stalk_lengths (f ≫ g) d

end PiExponentSeshadri.FiniteSupport

end

end OAI
end Source0441

-- Source: OAI/NumberTheory/PiExponent/Approximation/OpenPullbackUnit.lean
section Source0442
/-
Modification notice for the LogTwo project.
Derived from openai/math (Apache-2.0), revision adc7f1241b42e322a6451854ab7e4b4c146bf78a.
Original source: lean/OAI/NumberTheory/PiExponent/Approximation/OpenPullbackUnit.lean
Changes: Convert module/import declarations to the Lean 4.34 public module format.
See ../THIRD_PARTY_NOTICES.txt for provenance and the recorded changes.
-/
end Source0442

-- Source: OAI/NumberTheory/PiExponent/Approximation/LineClosedUnit.lean
section Source0443
/-
Modification notice for the LogTwo project.
Derived from openai/math (Apache-2.0), revision adc7f1241b42e322a6451854ab7e4b4c146bf78a.
Original source: lean/OAI/NumberTheory/PiExponent/Approximation/LineClosedUnit.lean
Changes: Convert module/import declarations to the Lean 4.34 public module format.
See ../THIRD_PARTY_NOTICES.txt for provenance and the recorded changes.
-/

namespace OAI

namespace PiExponentSeshadri.LineClosedUnit
noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite
open PiExponentSeshadri.Geometry PiExponentSeshadri.Frames
variable {X Y : Scheme.{0}} (f : X ⟶ Y)

def map (L : LineBundle Y) : L.sheaf ⟶
    (Scheme.Modules.pushforward f).obj ((Scheme.Modules.pullback f).obj L.sheaf) :=
  (Scheme.Modules.pullbackPushforwardAdjunction f).unit.app L.sheaf

def frame (L : LineBundle Y) (U : Y.Opens) (e : L.sheaf.restrict U.ι ≅ O U.toScheme) :
    ((Scheme.Modules.pushforward f).obj ((Scheme.Modules.pullback f).obj L.sheaf)).restrict U.ι ≅
      (Scheme.Modules.pushforward (f ∣_ U)).obj (O (f ⁻¹ᵁ U).toScheme) :=
  OpenBaseChange.iso f U _ ≪≫
    (Scheme.Modules.pushforward (f ∣_ U)).mapIso
      ((OpenBaseChange.leftSquare f U).app L.sheaf).symm ≪≫
    (Scheme.Modules.pushforward (f ∣_ U)).mapIso (pullbackFrame (f ∣_ U) e)

lemma framed_map (L : LineBundle Y) (U : Y.Opens)
    (e : L.sheaf.restrict U.ι ≅ O U.toScheme) :
    e.inv ≫ (Scheme.Modules.restrictFunctor U.ι).map (map f L) ≫
      (frame f L U e).hom = IdealModule.structureMap (f ∣_ U) := by
  dsimp only [map, IdealModule.structureMap]
  have hu := OpenBaseChange.unit_compatibility f U L.sheaf
  have hn := (Scheme.Modules.pullbackPushforwardAdjunction (f ∣_ U)).unit_naturality e.hom
  have hb := pullbackUnit_adjunction (f ∣_ U)
  rw [Adjunction.homEquiv_unit] at hb
  dsimp only [frame, Iso.trans_hom, Functor.mapIso_hom, Iso.symm_hom]
  simp only [← Category.assoc]
  rw [Category.assoc e.inv, hu]
  simp only [Category.assoc]
  have hec : (OpenBaseChange.leftSquare f U).hom.app L.sheaf ≫
      ((OpenBaseChange.leftSquare f U).app L.sheaf).inv = 𝟙 _ :=
    ((OpenBaseChange.leftSquare f U).app L.sheaf).hom_inv_id
  rw [← Functor.map_comp_assoc, hec]
  erw [CategoryTheory.Functor.map_id, Category.id_comp]
  change e.inv ≫ (Scheme.Modules.pullbackPushforwardAdjunction (f ∣_ U)).unit.app _ ≫
    (Scheme.Modules.pushforward (f ∣_ U)).map
      ((Scheme.Modules.pullback (f ∣_ U)).map e.hom ≫ (pullbackUnitIso (f ∣_ U)).hom) = _
  rw [Functor.map_comp]
  have hn' := congrArg (fun t => e.inv ≫ t ≫
    (Scheme.Modules.pushforward (f ∣_ U)).map (pullbackUnitIso (f ∣_ U)).hom) hn
  simp only [Category.assoc, hb] at hn'
  exact hn'.trans (e.inv_hom_id_assoc _)

theorem epi [IsClosedImmersion f] (L : LineBundle Y) : Epi (map f L) := by
  apply PiExponent.CoherentTwist.epi_of_local
  intro y
  obtain ⟨U,hy,⟨e⟩⟩ := L.locallyRankOne y
  refine ⟨U,hy,?_⟩
  have hg : Epi (IdealModule.structureMap (f ∣_ U)) := IdealModule.structureMap_epi _
  have he := framed_map f L U e
  have : Epi (e.inv ≫ (Scheme.Modules.restrictFunctor U.ι).map (map f L) ≫
    (frame f L U e).hom) := he.symm ▸ hg
  have h1 : Epi ((Scheme.Modules.restrictFunctor U.ι).map (map f L) ≫
      (frame f L U e).hom) := epi_of_epi e.inv _
  exact (epi_comp_iff_of_isIso _ _).mp h1

end
end PiExponentSeshadri.LineClosedUnit

end OAI
end Source0443

-- Source: OAI/NumberTheory/PiExponent/Geometry/PrincipalCartierSequence.lean
section Source0444
/-
Modification notice for the LogTwo project.
Derived from openai/math (Apache-2.0), revision adc7f1241b42e322a6451854ab7e4b4c146bf78a.
Original source: lean/OAI/NumberTheory/PiExponent/Geometry/PrincipalCartierSequence.lean
Changes: Convert module/import declarations to the Lean 4.34 public module format.
See ../THIRD_PARTY_NOTICES.txt for provenance and the recorded changes.
-/

namespace OAI

namespace PiExponentSeshadri.PrincipalSequence
noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite
open PiExponentSeshadri.Geometry PiExponentSeshadri.Frames
variable {X Y : Scheme.{0}}

lemma scalarEnd_eq_multiply (r : Γ(X,⊤)) : scalarEnd r = IdealModule.multiply r := rfl

lemma end_regular_of_mono (a : O X ⟶ O X) [Mono a] : IsLeftRegular (endValue a) := by
  have hinj : Function.Injective (a.val.app (op ⊤)) :=
    PresheafOfModules.injective_of_mono
      ((Scheme.Modules.toPresheafOfModules X).map a) (op ⊤)
  intro r s hrs
  apply hinj
  change a.app ⊤ r = a.app ⊤ s
  rw [end_apply a ⊤ r, end_apply a ⊤ s]
  change r * endValue a = s * endValue a
  simpa only [mul_comm] using hrs

theorem exact [IsAffine Y] (f : X ⟶ Y) [IsClosedImmersion f]
    (a : O Y ⟶ O Y) [Mono a]
    (h : f.ker.ideal ⟨⊤,isAffineOpen_top Y⟩ = Ideal.span {endValue a}) :
    ∃ hz : a ≫ IdealModule.structureMap f = 0,
      (ShortComplex.mk a (IdealModule.structureMap f) hz).ShortExact := by
  let r := endValue a
  have hr : f.appTop r = 0 := by
    change r ∈ RingHom.ker f.appTop.hom
    erw [← Scheme.Hom.ker_apply f ⟨⊤,isAffineOpen_top Y⟩, h]
    exact Ideal.subset_span (Set.mem_singleton r)
  have hreg : IsLeftRegular r := end_regular_of_mono a
  have hprincipal (U : Y.affineOpens) : f.ker.ideal U =
      Ideal.span {Y.presheaf.map (homOfLE (show U.1 ≤ ⊤ from le_top)).op r} := by
    rw [← f.ker.map_ideal (U := U) (V := ⟨⊤,isAffineOpen_top Y⟩) (by change U.1 ≤ ⊤; exact le_top), h]
    simp only [Ideal.map_span, Set.image_singleton]
    rfl
  have hi : IsIso (IdealModule.equationToIdeal f r hr) :=
    IdealModule.isIso_equationToIdeal f r hr hprincipal
      (IdealModule.restriction_regular r hreg)
  have he : a = IdealModule.multiply r := by
    rw [← scalarEnd_eq_multiply]
    apply endValue_injective
    simp [r]
  have hz : a ≫ IdealModule.structureMap f = 0 := by
    rw [he]
    exact IdealModule.multiply_structure_zero f r hr
  refine ⟨hz,?_⟩
  let S := ShortComplex.mk a (IdealModule.structureMap f) hz
  let T := ShortComplex.mk (IdealModule.inclusion f) (IdealModule.structureMap f)
    (kernel.condition (IdealModule.structureMap f))
  let e : S ≅ T := ShortComplex.isoMk (@asIso Y.Modules _ _ _ (IdealModule.equationToIdeal f r hr) hi)
    (Iso.refl _) (Iso.refl _) (by
      change IdealModule.equationToIdeal f r hr ≫ IdealModule.inclusion f = a ≫ 𝟙 _
      exact (IdealModule.equationToIdeal_inclusion f r hr).trans
        (he.symm.trans (Category.comp_id a).symm)) (by exact (Category.id_comp _).trans (Category.comp_id _).symm)
  have hg : Epi (IdealModule.structureMap f) := IdealModule.structureMap_epi f
  exact { exact := ShortComplex.exact_of_iso e.symm (ShortComplex.exact_kernel _), epi_g := hg }

end
end PiExponentSeshadri.PrincipalSequence

end OAI
end Source0444

-- Source: OAI/NumberTheory/PiExponent/Geometry/CartierSequence.lean
section Source0445
/-
Modification notice for the LogTwo project.
Derived from openai/math (Apache-2.0), revision adc7f1241b42e322a6451854ab7e4b4c146bf78a.
Original source: lean/OAI/NumberTheory/PiExponent/Geometry/CartierSequence.lean
Changes: Convert module/import declarations to the Lean 4.34 public module format.
See ../THIRD_PARTY_NOTICES.txt for provenance and the recorded changes.
-/

namespace OAI

namespace PiExponentSeshadri.CartierSequence
noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite
open PiExponentSeshadri.Geometry PiExponentSeshadri.Frames
variable {X : Scheme.{0}}

lemma chart_topIso_naturality {Y : Scheme.{0}} (j : Y ⟶ X) (U : X.Opens) :
    U.topIso.hom ≫ j.app U ≫ (j ⁻¹ᵁ U).topIso.inv = (j ∣_ U).appTop := by
  have H := (arrowResLEAppIso j U (j ⁻¹ᵁ U) le_rfl).hom.w
  change U.topIso.hom ≫ j.appLE U (j ⁻¹ᵁ U) le_rfl =
    (j.resLE U (j ⁻¹ᵁ U) le_rfl).appTop ≫ (j ⁻¹ᵁ U).topIso.hom at H
  rw [Scheme.Hom.resLE_eq_morphismRestrict, Scheme.Hom.appLE_eq_app] at H
  apply (cancel_mono (j ⁻¹ᵁ U).topIso.hom).mp
  simpa only [Category.assoc, Iso.inv_hom_id, Category.comp_id] using H

lemma restriction_principal (_p : X ⟶ Spec (CommRingCat.of ℂ))
    (I : X.IdealSheafData) (U : X.affineOpens) (r : Γ(U.1.toScheme,⊤))
    (hI : I.ideal U = Ideal.span {U.1.topIso.hom r}) :
    (I.subschemeι ∣_ U.1).ker.ideal ⟨⊤,isAffineOpen_top U.1.toScheme⟩ =
      Ideal.span {r} := by
  ext z
  rw [Scheme.Hom.ker_apply,RingHom.mem_ker]
  change (I.subschemeι ∣_ U.1).appTop z = 0 ↔ z ∈ Ideal.span {r}
  have hz : (I.subschemeι ∣_ U.1).appTop z = 0 ↔
      U.1.topIso.hom z ∈ I.ideal U := by
    rw [← chart_topIso_naturality]
    simp only [CommRingCat.comp_apply]
    rw [← I.ker_subschemeι_app U]
    change (I.subschemeι ⁻¹ᵁ U.1).topIso.inv
      (I.subschemeι.app U.1 (U.1.topIso.hom z)) = 0 ↔
      I.subschemeι.app U.1 (U.1.topIso.hom z) = 0
    exact map_eq_zero_iff _ (ConcreteCategory.bijective_of_isIso
      (I.subschemeι ⁻¹ᵁ U.1).topIso.inv).injective
  rw [hz,hI,Ideal.mem_span_singleton,Ideal.mem_span_singleton]
  constructor
  · rintro ⟨a,ha⟩
    refine ⟨U.1.topIso.inv a,?_⟩
    have h := congrArg U.1.topIso.inv ha
    simpa only [map_mul,U.1.topIso.hom_inv_id_apply] using h
  · rintro ⟨a,ha⟩
    refine ⟨U.1.topIso.hom a,?_⟩
    simpa only [map_mul] using congrArg U.1.topIso.hom ha

theorem exact (p : X ⟶ Spec (CommRingCat.of ℂ))
    (M N : LineBundle X) (φ : M.sheaf ⟶ N.sheaf) [Mono φ]
    (I : X.IdealSheafData)
    (heq : ∀ x : X, ∃ U : X.affineOpens, x ∈ U.1 ∧
      ∃ e : M.sheaf.restrict U.1.ι ≅ O U.1.toScheme,
      ∃ d : N.sheaf.restrict U.1.ι ≅ O U.1.toScheme,
        I.ideal U = Ideal.span {(U.1.topIso.hom
          (endValue (e.inv ≫ (Scheme.Modules.restrictFunctor U.1.ι).map φ ≫ d.hom)))}) :
    ∃ hz : φ ≫ LineClosedUnit.map I.subschemeι N = 0,
      (ShortComplex.mk φ (LineClosedUnit.map I.subschemeι N) hz).ShortExact := by
  have local_exact (U : X.affineOpens)
      (e : M.sheaf.restrict U.1.ι ≅ O U.1.toScheme)
      (d : N.sheaf.restrict U.1.ι ≅ O U.1.toScheme)
      (hI : I.ideal U = Ideal.span {(U.1.topIso.hom
        (endValue (e.inv ≫ (Scheme.Modules.restrictFunctor U.1.ι).map φ ≫ d.hom)))}) :=
    PrincipalSequence.exact (I.subschemeι ∣_ U.1)
      (e.inv ≫ (Scheme.Modules.restrictFunctor U.1.ι).map φ ≫ d.hom)
      (restriction_principal p I U _ hI)
  have hz : φ ≫ LineClosedUnit.map I.subschemeι N = 0 := by
    apply PiExponent.CoherentTwist.eq_zero_of_local
    intro x
    obtain ⟨U,hx,e,d,hI⟩ := heq x
    obtain ⟨hzero,hex⟩ := local_exact U e d hI
    refine ⟨U.1,hx,?_⟩
    apply (cancel_epi e.inv).mp
    apply (cancel_mono (LineClosedUnit.frame I.subschemeι N U.1 d).hom).mp
    rw [Functor.map_comp,comp_zero,zero_comp]
    rw [Category.assoc,Category.assoc]
    rw [← d.hom_inv_id_assoc ((Scheme.Modules.restrictFunctor U.1.ι).map
      (LineClosedUnit.map I.subschemeι N))]
    simp only [Category.assoc]
    rw [LineClosedUnit.framed_map]
    simpa only [Category.assoc] using! hzero
  refine ⟨hz,{ exact := ?_, epi_g := LineClosedUnit.epi _ _ }⟩
  apply PiExponent.CoherentTwist.exact_of_local
  intro x
  obtain ⟨U,hx,e,d,hI⟩ := heq x
  obtain ⟨hzero,hex⟩ := local_exact U e d hI
  refine ⟨U.1,hx,?_⟩
  let S := (ShortComplex.mk φ (LineClosedUnit.map I.subschemeι N) hz).map
    (Scheme.Modules.restrictFunctor U.1.ι)
  let T := ShortComplex.mk (e.inv ≫ (Scheme.Modules.restrictFunctor U.1.ι).map φ ≫ d.hom)
    (IdealModule.structureMap (I.subschemeι ∣_ U.1)) hzero
  let ee : S ≅ T := ShortComplex.isoMk e d (LineClosedUnit.frame I.subschemeι N U.1 d)
    (by simp [S,T]) (by
      change d.hom ≫ IdealModule.structureMap (I.subschemeι ∣_ U.1) =
        (Scheme.Modules.restrictFunctor U.1.ι).map (LineClosedUnit.map I.subschemeι N) ≫ _
      rw [← LineClosedUnit.framed_map I.subschemeι N U.1 d]
      exact d.hom_inv_id_assoc _)
  exact ShortComplex.exact_of_iso ee.symm hex.exact

end
end PiExponentSeshadri.CartierSequence

end OAI
end Source0445

-- Source: OAI/NumberTheory/PiExponent/Geometry/CartierDegreeLength.lean
section Source0446
/-
Modification notice for the LogTwo project.
Derived from openai/math (Apache-2.0), revision adc7f1241b42e322a6451854ab7e4b4c146bf78a.
Original source: lean/OAI/NumberTheory/PiExponent/Geometry/CartierDegreeLength.lean
Changes: Convert module/import declarations to the Lean 4.34 public module format.
See ../THIRD_PARTY_NOTICES.txt for provenance and the recorded changes.
-/

namespace OAI

noncomputable section
open CategoryTheory AlgebraicGeometry TopologicalSpace
open PiExponentSeshadri.Geometry PiExponentSeshadri.Frames

namespace PiExponent.CartierDegreeLength

theorem cartier_euler_difference_eq_sum_local_lengths
    {X : Scheme.{0}} [IsIntegral X]
    (p : X ⟶ Spec (CommRingCat.of ℂ)) [IsProper p]
    (hd : topologicalKrullDim X ≤ 1)
    (M N : LineBundle X) (φ : M.sheaf ⟶ N.sheaf) [Mono φ]
    (I : X.IdealSheafData) (hI : I ≠ ⊥)
    (heq : ∀ x : X, ∃ U : X.affineOpens, x ∈ U.1 ∧
      ∃ e : M.sheaf.restrict U.1.ι ≅ O U.1.toScheme,
      ∃ d : N.sheaf.restrict U.1.ι ≅ O U.1.toScheme,
        I.ideal U = Ideal.span {(U.1.topIso.hom
          (endValue (e.inv ≫ (Scheme.Modules.restrictFunctor U.1.ι).map φ ≫ d.hom)))})
    (hfiniteM : ∀ n ≤ 1, letI := Module.compHom (cohomology M.sheaf n) (baseScalars p)
      FiniteDimensional ℂ (cohomology M.sheaf n))
    (hfiniteN : ∀ n ≤ 1, letI := Module.compHom (cohomology N.sheaf n) (baseScalars p)
      FiniteDimensional ℂ (cohomology N.sheaf n))
    [Subsingleton (cohomology M.sheaf 2)] :
    letI : Finite I.subscheme := finite_subscheme_of_curve p hd I hI
    letI : Fintype I.subscheme := Fintype.ofFinite _
    eulerCharacteristic p 1 N.sheaf - eulerCharacteristic p 1 M.sheaf =
      ∑ x : I.subscheme,
        ((Module.length (I.subscheme.presheaf.stalk x)
          (I.subscheme.presheaf.stalk x)).toNat : ℤ) := by
  let : Finite I.subscheme := finite_subscheme_of_curve p hd I hI
  let : Fintype I.subscheme := Fintype.ofFinite _
  obtain ⟨hz, hseq⟩ := PiExponentSeshadri.CartierSequence.exact p M N φ I heq
  have hfiniteZ (n : ℕ) (_hn : n ≤ 1) :=
    PiExponentSeshadri.FiniteSupport.finite_line_pushforward_finiteDimensional
      I.subschemeι p (N.pullback I.subschemeι) n
  have h := eulerCharacteristic_add p hseq 1 hfiniteM hfiniteN hfiniteZ
  have hdiff : eulerCharacteristic p 1 N.sheaf - eulerCharacteristic p 1 M.sheaf =
      eulerCharacteristic p 1
        ((Scheme.Modules.pushforward I.subschemeι).obj
          ((Scheme.Modules.pullback I.subschemeι).obj N.sheaf)) := by
    exact sub_eq_iff_eq_add.mpr (by simpa [add_comm] using h)
  exact hdiff.trans
    (PiExponentSeshadri.FiniteSupport.finite_line_euler_eq_sum_stalk_lengths
      I.subschemeι p (N.pullback I.subschemeι) 1)

end PiExponent.CartierDegreeLength

end

end OAI
end Source0446

-- Source: OAI/NumberTheory/PiExponent/Cohomology/NakaiCohomology.lean
section Source0447
-- Modified in this edition: unused plain lemmas removed; see reduction.json.
/-
Modification notice for the LogTwo project.
Derived from openai/math (Apache-2.0), revision adc7f1241b42e322a6451854ab7e4b4c146bf78a.
Original source: lean/OAI/NumberTheory/PiExponent/Cohomology/NakaiCohomology.lean
Changes: Convert module/import declarations to the Lean 4.34 public module format.
See ../THIRD_PARTY_NOTICES.txt for provenance and the recorded changes.
-/

namespace OAI

namespace PiExponent.NumericalAmpleness
noncomputable section
open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian AlgebraicGeometry
open PiExponentSeshadri.Geometry
variable {X : Scheme.{0}}

def cohomologyMap (p : X ⟶ Spec (CommRingCat.of ℂ)) {M N : X.Modules}
    (f : M ⟶ N) (n : ℕ) :
    let _ := Module.compHom (cohomology M n) (baseScalars p)
    let _ := Module.compHom (cohomology N n) (baseScalars p)
    cohomology M n →ₗ[ℂ] cohomology N n := by
  dsimp only
  letI := Module.compHom (cohomology M n) (baseScalars p)
  letI := Module.compHom (cohomology N n) (baseScalars p)
  let g := (Ext.mk₀ f).postcompOfLinear Γ(X,⊤) (structureSheaf X) (add_zero n)
  exact { g.toAddHom with map_smul' := fun r x => g.map_smul (baseScalars p r) x }

theorem globalSections_surjective_of_h1_stationary
    (p : X ⟶ Spec (CommRingCat.of ℂ)) (S : ShortComplex X.Modules) (hS : S.ShortExact)
    (hfinite₁ : let _ := Module.compHom (cohomology S.X₁ 1) (baseScalars p)
      FiniteDimensional ℂ (cohomology S.X₁ 1))
    (hfinite₂ : let _ := Module.compHom (cohomology S.X₂ 1) (baseScalars p)
      FiniteDimensional ℂ (cohomology S.X₂ 1))
    (hrank : cohomologyDimension p S.X₁ 1 = cohomologyDimension p S.X₂ 1)
    (hzero : ∀ z : cohomology S.X₃ 1, z = 0) :
    Function.Surjective (fun s : GlobalSections X S.X₂ => s ≫ S.g) := by
  let := Module.compHom (cohomology S.X₁ 1) (baseScalars p)
  let := Module.compHom (cohomology S.X₂ 1) (baseScalars p)
  have : FiniteDimensional ℂ (cohomology S.X₁ 1) := hfinite₁
  have : FiniteDimensional ℂ (cohomology S.X₂ 1) := hfinite₂
  let f := cohomologyMap p S.f 1
  have hsurj : Function.Surjective f := by
    intro b
    obtain ⟨a,ha⟩ := Ext.covariant_sequence_exact₂ (structureSheaf X) hS b (hzero _)
    exact ⟨a,ha⟩
  have hinj : Function.Injective f :=
    (LinearMap.injective_iff_surjective_of_finrank_eq_finrank hrank).mpr hsurj
  intro s
  have hboundary : (Ext.mk₀ s).comp hS.extClass rfl = 0 := by
    apply hinj
    change ((Ext.mk₀ s).comp hS.extClass rfl).comp (Ext.mk₀ S.f) (add_zero 1) = f 0
    rw [map_zero]
    rw [Ext.comp_assoc_of_third_deg_zero, hS.extClass_comp, Ext.comp_zero]
  obtain ⟨a,ha⟩ := Ext.covariant_sequence_exact₃ (structureSheaf X) hS (Ext.mk₀ s) rfl hboundary
  refine ⟨Ext.homEquiv₀ a, ?_⟩
  apply (Ext.mk₀_bijective (structureSheaf X) S.X₃).injective
  rw [← Ext.mk₀_comp_mk₀, Ext.mk₀_homEquiv₀_apply]
  exact ha

theorem eventually_constant_of_antitone_nat (a : ℕ → ℕ) (ha : Antitone a) :
    ∃ N, ∀ n, N ≤ n → a n = a N := by
  classical
  have he : ∃ k : ℕ, ∃ n, a n = k := ⟨a 0,0,rfl⟩
  obtain ⟨N,hN⟩ := Nat.find_spec he
  refine ⟨N,fun n hn => le_antisymm (ha hn) ?_⟩
  rw [hN]
  exact Nat.find_min' he ⟨n,rfl⟩

theorem eventual_globalSections_surjective
    (p : X ⟶ Spec (CommRingCat.of ℂ)) (F Q : ℕ → X.Modules)
    (f : ∀ n, F n ⟶ F (n+1)) (g : ∀ n, F (n+1) ⟶ Q n)
    (hcomp : ∀ n, f n ≫ g n = 0)
    (hshort : ∀ n, (ShortComplex.mk (f n) (g n) (hcomp n)).ShortExact)
    (hfinite : ∀ n, let _ := Module.compHom (cohomology (F n) 1) (baseScalars p)
      FiniteDimensional ℂ (cohomology (F n) 1))
    (hzero : ∃ N, ∀ n, N ≤ n → ∀ z : cohomology (Q n) 1, z = 0) :
    ∃ N, ∀ n, N ≤ n →
      Function.Surjective (fun s : GlobalSections X (F (n+1)) => s ≫ g n) := by
  obtain ⟨N₀,hN₀⟩ := hzero
  have hdim (n : ℕ) (hn : N₀ ≤ n) :
      cohomologyDimension p (F (n+1)) 1 ≤ cohomologyDimension p (F n) 1 := by
    let := Module.compHom (cohomology (F n) 1) (baseScalars p)
    let := Module.compHom (cohomology (F (n+1)) 1) (baseScalars p)
    have : FiniteDimensional ℂ (cohomology (F n) 1) := hfinite n
    have hsurj : Function.Surjective (cohomologyMap p (f n) 1) := by
      intro b
      exact Ext.covariant_sequence_exact₂ (structureSheaf X) (hshort n) b (hN₀ n hn _)
    exact LinearMap.finrank_le_finrank_of_surjective hsurj
  let a : ℕ → ℕ := fun n => cohomologyDimension p (F (N₀+n)) 1
  have ha : Antitone a := antitone_nat_of_succ_le (fun n => by
    simpa only [a, Nat.add_assoc] using hdim (N₀+n) (Nat.le_add_right _ _))
  obtain ⟨N,hN⟩ := eventually_constant_of_antitone_nat a ha
  refine ⟨N₀+N,fun n hn => ?_⟩
  have hn₀ : N₀ ≤ n := by omega
  obtain ⟨k,rfl⟩ := Nat.exists_eq_add_of_le hn₀
  have hk : N ≤ k := by omega
  have he : cohomologyDimension p (F (N₀+k)) 1 =
      cohomologyDimension p (F (N₀+k+1)) 1 := by
    exact (hN k hk).trans (by simpa only [a, Nat.add_assoc] using (hN (k+1) (by omega)).symm)
  exact globalSections_surjective_of_h1_stationary p
    (ShortComplex.mk (f (N₀+k)) (g (N₀+k)) (hcomp (N₀+k)))
    (hshort (N₀+k)) (hfinite _) (hfinite _) he (hN₀ _ (by omega))

theorem cohomologyMap_bijective_of_quotient_vanishing
    (p : X ⟶ Spec (CommRingCat.of ℂ)) (S : ShortComplex X.Modules) (hS : S.ShortExact)
    (n : ℕ) (hprev : ∀ z : cohomology S.X₃ n, z = 0)
    (hnext : ∀ z : cohomology S.X₃ (n+1), z = 0) :
    Function.Bijective (cohomologyMap p S.f (n+1)) := by
  let := Module.compHom (cohomology S.X₁ (n+1)) (baseScalars p)
  let := Module.compHom (cohomology S.X₂ (n+1)) (baseScalars p)
  constructor
  · apply (injective_iff_map_eq_zero (cohomologyMap p S.f (n+1))).mpr
    intro a ha
    obtain ⟨b,hb⟩ := Ext.covariant_sequence_exact₁ (structureSheaf X) hS a ha rfl
    rw [hprev b, Ext.zero_comp] at hb
    exact hb.symm
  · intro b
    exact Ext.covariant_sequence_exact₂ (structureSheaf X) hS b (hnext _)

theorem cohomologyDimension_eq_of_quotient_vanishing
    (p : X ⟶ Spec (CommRingCat.of ℂ)) (S : ShortComplex X.Modules) (hS : S.ShortExact)
    (n : ℕ) (hprev : ∀ z : cohomology S.X₃ n, z = 0)
    (hnext : ∀ z : cohomology S.X₃ (n+1), z = 0) :
    cohomologyDimension p S.X₁ (n+1) = cohomologyDimension p S.X₂ (n+1) := by
  let := Module.compHom (cohomology S.X₁ (n+1)) (baseScalars p)
  let := Module.compHom (cohomology S.X₂ (n+1)) (baseScalars p)
  exact (LinearEquiv.ofBijective (cohomologyMap p S.f (n+1))
    (cohomologyMap_bijective_of_quotient_vanishing p S hS n hprev hnext)).finrank_eq

end
end PiExponent.NumericalAmpleness

end OAI
end Source0447

-- Source: OAI/NumberTheory/PiExponent/Cohomology/NakaiEulerGrowth.lean
section Source0448
/-
Modification notice for the LogTwo project.
Derived from openai/math (Apache-2.0), revision adc7f1241b42e322a6451854ab7e4b4c146bf78a.
Original source: lean/OAI/NumberTheory/PiExponent/Cohomology/NakaiEulerGrowth.lean
Changes: Convert module/import declarations to the Lean 4.34 public module format.
See ../THIRD_PARTY_NOTICES.txt for provenance and the recorded changes.
-/

namespace OAI

namespace PiExponent.NumericalAmpleness

noncomputable section

open CategoryTheory CategoryTheory.Abelian AlgebraicGeometry Filter
open PiExponentSeshadri.Geometry
open scoped BigOperators

variable {X : Scheme.{0}}

theorem exists_nonzero_globalSection_of_cohomologyDimension_pos
    (p : X ⟶ Spec (CommRingCat.of ℂ)) (M : X.Modules)
    (hpos : 0 < cohomologyDimension p M 0) :
    ∃ s : GlobalSections X M, s ≠ 0 := by
  let := Module.compHom (cohomology M 0) (baseScalars p)
  have : Nontrivial (cohomology M 0) := Module.nontrivial_of_finrank_pos hpos
  obtain ⟨z,hz⟩ := exists_ne (0 : cohomology M 0)
  refine ⟨Ext.homEquiv₀ z, ?_⟩
  intro hs
  apply hz
  have hzero := congrArg (fun s : GlobalSections X M => Ext.mk₀ s) hs
  simpa only [Ext.mk₀_homEquiv₀_apply, Ext.mk₀_zero] using hzero

theorem eulerCharacteristic_eq_zero_sub_one_add_tail
    (p : X ⟶ Spec (CommRingCat.of ℂ)) (M : X.Modules) (d : ℕ) (hd : 1 ≤ d) :
    eulerCharacteristic p d M =
      (cohomologyDimension p M 0 : ℤ) - (cohomologyDimension p M 1 : ℤ) +
        ∑ i ∈ Finset.range (d - 1),
          (-1 : ℤ) ^ (i + 2) * (cohomologyDimension p M (i + 2) : ℤ) := by
  unfold eulerCharacteristic
  rw [show d + 1 = 2 + (d - 1) by omega, Finset.sum_range_add]
  simp only [Finset.sum_range_succ, Finset.range_zero, Finset.sum_empty,
    pow_zero, one_mul, zero_add, pow_one, neg_one_mul]
  simp only [Nat.add_comm 2, sub_eq_add_neg]

theorem eventually_nonzero_globalSection_of_euler_growth
    (p : X ⟶ Spec (CommRingCat.of ℂ)) (F : ℕ → X.Modules)
    (d : ℕ) (hd : 1 ≤ d)
    (hgrowth : Tendsto (fun n => eulerCharacteristic p d (F n)) atTop atTop)
    (hconstant : ∀ i, 2 ≤ i → i ≤ d →
      ∃ c : ℕ, ∀ᶠ n in atTop, cohomologyDimension p (F n) i = c) :
    ∀ᶠ n in atTop, ∃ s : GlobalSections X (F n), s ≠ 0 := by
  classical
  have hh (i : Fin (d - 1)) :
      ∃ c : ℕ, ∀ᶠ n in atTop, cohomologyDimension p (F n) (i.val + 2) = c := by
    apply hconstant (i.val + 2) (by omega) (by have := i.isLt; omega)
  choose c hc using hh
  let C : ℤ := ∑ i : Fin (d - 1), (-1 : ℤ) ^ (i.val + 2) * (c i : ℤ)
  have hall : ∀ᶠ n in atTop,
      ∀ i : Fin (d - 1), cohomologyDimension p (F n) (i.val + 2) = c i :=
    Filter.eventually_all.mpr hc
  have hlarge : ∀ᶠ n in atTop, C < eulerCharacteristic p d (F n) :=
    hgrowth.eventually (eventually_gt_atTop C)
  filter_upwards [hall, hlarge] with n hn hχ
  apply exists_nonzero_globalSection_of_cohomologyDimension_pos p (F n)
  have htail : (∑ i ∈ Finset.range (d - 1),
      (-1 : ℤ) ^ (i + 2) * (cohomologyDimension p (F n) (i + 2) : ℤ)) = C := by
    rw [← Fin.sum_univ_eq_sum_range]
    apply Finset.sum_congr rfl
    intro i _
    rw [hn i]
  rw [eulerCharacteristic_eq_zero_sub_one_add_tail p (F n) d hd, htail] at hχ
  have hnonneg : (0 : ℤ) ≤ (cohomologyDimension p (F n) 1 : ℤ) := Int.natCast_nonneg _
  omega

theorem eventually_nonzero_globalSection_of_eventually_stationary
    (p : X ⟶ Spec (CommRingCat.of ℂ)) (F : ℕ → X.Modules)
    (d : ℕ) (hd : 1 ≤ d)
    (hgrowth : Tendsto (fun n => eulerCharacteristic p d (F n)) atTop atTop)
    (hstationary : ∀ i, 2 ≤ i → i ≤ d →
      ∃ N, ∀ n, N ≤ n → cohomologyDimension p (F n) i =
        cohomologyDimension p (F N) i) :
    ∀ᶠ n in atTop, ∃ s : GlobalSections X (F n), s ≠ 0 := by
  apply eventually_nonzero_globalSection_of_euler_growth p F d hd hgrowth
  intro i hi hid
  obtain ⟨N,hN⟩ := hstationary i hi hid
  refine ⟨cohomologyDimension p (F N) i, ?_⟩
  filter_upwards [eventually_ge_atTop N] with n hn
  exact hN n hn

end
end PiExponent.NumericalAmpleness

end OAI
end Source0448

-- Source: OAI/NumberTheory/PiExponent/Ampleness/NakaiCartier.lean
section Source0449
-- Modified in this edition: unused plain lemmas removed; see reduction.json.
/-
Modification notice for the LogTwo project.
Derived from openai/math (Apache-2.0), revision adc7f1241b42e322a6451854ab7e4b4c146bf78a.
Original source: lean/OAI/NumberTheory/PiExponent/Ampleness/NakaiCartier.lean
Changes: Convert module/import declarations to the Lean 4.34 public module format.
See ../THIRD_PARTY_NOTICES.txt for provenance and the recorded changes.
-/

namespace OAI

namespace PiExponent.NumericalAmpleness
noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open PiExponentSeshadri.Geometry
variable {X : Scheme.{0}}

private lemma mono_iso_inv_comp {C : Type*} [Category C] {A B D : C}
    (e : A ≅ B) (f : A ⟶ D) [Mono f] : Mono (e.inv ≫ f) := inferInstance

def cartierPowerMultiply (L : LineBundle X) (s : GlobalSections X L.sheaf) (n : ℕ) :
    modulePow X L.sheaf n ⟶ modulePow X L.sheaf (n+1) :=
  (moduleTensorUnit (modulePow X L.sheaf n)).inv ≫
    moduleTensorMap s (𝟙 (modulePow X L.sheaf n))

theorem cartierPowerMultiply_mono [IsIntegral X] (L : LineBundle X)
    (s : GlobalSections X L.sheaf) (hs : s ≠ 0) (n : ℕ) :
    Mono (cartierPowerMultiply L s n) := by
  let := L.mono_section s hs
  have hm : Mono (moduleTensorMap s (𝟙 (modulePow X L.sheaf n))) :=
    moduleTensorMap_mono s (L.pow n)
  exact @mono_iso_inv_comp X.Modules _ _ _ _
    (moduleTensorUnit (modulePow X L.sheaf n)) _ hm

def cartierPowerQuotient (L : LineBundle X) (s : GlobalSections X L.sheaf) (n : ℕ) :
    X.Modules := cokernel (cartierPowerMultiply L s n)

def cartierPowerSequence (L : LineBundle X) (s : GlobalSections X L.sheaf) (n : ℕ) :
    ShortComplex X.Modules :=
  ShortComplex.mk (cartierPowerMultiply L s n) (cokernel.π _) (cokernel.condition _)

end
end PiExponent.NumericalAmpleness

end OAI
end Source0449

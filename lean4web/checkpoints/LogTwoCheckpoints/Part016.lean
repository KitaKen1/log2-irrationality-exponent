/- Generated rc4 checkpoint for LogTwo.
Modified from the reduced edition: new imports, separate module compilation,
and synchronous elaboration. Original source blocks and notices are retained.
See ../../../THIRD_PARTY_NOTICES.txt and ../../reduction.json.
-/
module
public import LogTwoCheckpoints.Part012
public import LogTwoCheckpoints.Part013
public import LogTwoCheckpoints.Part015
public import Mathlib.AlgebraicGeometry.Modules.Sheaf
public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Basic
public import Mathlib.Analysis.Complex.Polynomial.Basic
public import Mathlib.CategoryTheory.Sites.Hypercover.Subcanonical
public import Mathlib.Data.Opposite
public import Mathlib.RingTheory.MvPolynomial.Homogeneous
@[expose] public section
set_option Elab.async false

-- Source: OAI/NumberTheory/PiExponent/Ampleness/ClosedAmpleRestriction.lean
section Source0400
/-
Modification notice for the LogTwo project.
Derived from openai/math (Apache-2.0), revision adc7f1241b42e322a6451854ab7e4b4c146bf78a.
Original source: lean/OAI/NumberTheory/PiExponent/Ampleness/ClosedAmpleRestriction.lean
Changes: Convert module/import declarations to the Lean 4.34 public module format.
See ../THIRD_PARTY_NOTICES.txt for provenance and the recorded changes.
-/

namespace OAI

namespace PiExponentSeshadri.Geometry
noncomputable section
open AlgebraicGeometry CategoryTheory TopologicalSpace
open PiExponentSeshadri.Frames PiExponentSeshadri.SectionOpens
variable {X Y : Scheme.{0}}

theorem pullback_isoOpen_eq (L : LineBundle X) (s : O X ⟶ L.sheaf) (f : Y ⟶ X) :
    isoOpen (pullbackSection f s) = f ⁻¹ᵁ isoOpen s := by
  ext y
  obtain ⟨U,hy,⟨e⟩⟩ := L.locallyRankOne (f y)
  obtain ⟨eF,he⟩ := exists_restricted_pullback_frame f U e s
  calc
    y ∈ isoOpen (pullbackSection f s) ↔
        (⟨y,hy⟩ : (f ⁻¹ᵁ U).toScheme) ∈ (f ⁻¹ᵁ U).toScheme.basicOpen
          (coefficient eF (restrictSection (f ⁻¹ᵁ U).ι (pullbackSection f s))) :=
      (congrArg (fun V => (⟨y,hy⟩ : (f ⁻¹ᵁ U).toScheme) ∈ V)
        (preimage_isoOpen (pullbackSection f s) (f ⁻¹ᵁ U).ι eF)).to_iff
    _ ↔ (⟨f y,hy⟩ : U.toScheme) ∈ U.toScheme.basicOpen
          (coefficient e (restrictSection U.ι s)) := by
      rw [he,← Scheme.preimage_basicOpen_top]
      change (f ∣_ U) ⟨y,hy⟩ ∈ U.toScheme.basicOpen
        (coefficient e (restrictSection U.ι s)) ↔ _
      rw [morphismRestrict_base]
      rfl
    _ ↔ f y ∈ isoOpen s :=
      (congrArg (fun V => (⟨f y,hy⟩ : U.toScheme) ∈ V)
        (preimage_isoOpen s U.ι e)).to_iff.symm

def pullbackPowerSection (L : LineBundle X) (f : Y ⟶ X) (n : ℕ)
    (s : GlobalSections X (modulePow X L.sheaf n)) :
    GlobalSections Y (modulePow Y (L.pullback f).sheaf n) :=
  pullbackSection f s ≫ (PiExponentSeshadri.PullbackTensor.powIso f L n).hom

theorem sectionOpen_pullbackPowerSection (L : LineBundle X) (f : Y ⟶ X) (n : ℕ)
    (s : GlobalSections X (modulePow X L.sheaf n)) :
    sectionOpen Y (pullbackPowerSection L f n s) = f ⁻¹ᵁ sectionOpen X s := by
  unfold pullbackPowerSection
  erw [PiExponent.AmpleIso.sectionOpen_postcomp_iso]
  exact pullback_isoOpen_eq (L.pow n) s f

theorem LineBundle.IsAmple.pullback_closedImmersion (L : LineBundle X) (hL : L.IsAmple)
    (f : Y ⟶ X) [IsClosedImmersion f] : (L.pullback f).IsAmple := by
  intro y V hy
  obtain ⟨W,hW,hWV⟩ := f.isClosedEmbedding.isInducing.isOpen_iff.mp V.isOpen
  let U : X.Opens := ⟨W,hW⟩
  have hfV : f ⁻¹ᵁ U = V := TopologicalSpace.Opens.ext hWV
  have hfy : f y ∈ U := by
    change y ∈ f ⁻¹ᵁ U
    rwa [hfV]
  obtain ⟨n,hn,s,hys,hsU,hsa⟩ := hL (f y) U hfy
  refine ⟨n,hn,pullbackPowerSection L f n s,?_,?_,?_⟩
  · rw [sectionOpen_pullbackPowerSection]
    exact hys
  · rw [sectionOpen_pullbackPowerSection, ← hfV]
    exact (Opens.map f.base).monotone hsU
  · rw [sectionOpen_pullbackPowerSection]
    exact hsa.preimage f

end
end PiExponentSeshadri.Geometry

end OAI
end Source0400

-- Source: OAI/NumberTheory/PiExponent/Ampleness/FinitePullbackAmple.lean
section Source0401
/-
Modification notice for the LogTwo project.
Derived from openai/math (Apache-2.0), revision adc7f1241b42e322a6451854ab7e4b4c146bf78a.
Original source: lean/OAI/NumberTheory/PiExponent/Ampleness/FinitePullbackAmple.lean
Changes: Convert module/import declarations to the Lean 4.34 public module format.
See ../THIRD_PARTY_NOTICES.txt for provenance and the recorded changes.
-/

namespace OAI

noncomputable section
namespace PiExponentSeshadri.Geometry
open AlgebraicGeometry CategoryTheory TopologicalSpace
variable {X Y : Scheme.{0}}

theorem LineBundle.IsAmple.of_pow (L : LineBundle X) {d : ℕ} (hd : 0 < d)
    (hL : (L.pow d).IsAmple) : L.IsAmple := by
  intro x V hx
  obtain ⟨n, hn, s, hxs, hsV, hsa⟩ := hL x V hx
  have he := PiExponent.AmpleIso.sectionOpen_postcomp_iso s (linePowerMul L d n)
  exact ⟨d*n, Nat.mul_pos hd hn, s ≫ (linePowerMul L d n).hom,
    he.symm ▸ hxs, he.le.trans hsV, he.symm ▸ hsa⟩

theorem LineBundle.IsAmple.pullback_finite [CompactSpace X] [IsIntegral Y] [CompactSpace Y]
    (L : LineBundle X) (hL : L.IsAmple) (f : Y ⟶ X) [IsFinite f] :
    (L.pullback f).IsAmple := by
  obtain ⟨d, hd, l, s, hc, ha, _⟩ := L.ample_common_degree_cover hL
  let t (i : Fin l) := pullbackPowerSection L f d (s i)
  have ht (i : Fin l) : sectionOpen Y (t i) = f ⁻¹ᵁ sectionOpen X (s i) :=
    sectionOpen_pullbackPowerSection L f d (s i)
  have htc : (⨆ i, sectionOpen Y (t i)) = ⊤ := by
    apply top_le_iff.mp
    intro y _
    have hy : f y ∈ ⨆ i, sectionOpen X (s i) := by rw [hc]; trivial
    obtain ⟨i, hi⟩ := Opens.mem_iSup.mp hy
    exact Opens.mem_iSup.mpr ⟨i, by rw [ht]; exact hi⟩
  have hta (i : Fin l) : IsAffineOpen (sectionOpen Y (t i)) := by
    rw [ht]
    exact (ha i).preimage f
  exact LineBundle.IsAmple.of_pow (L.pullback f) hd
    (((L.pullback f).pow d).ample_of_affine_section_cover t htc hta)

end PiExponentSeshadri.Geometry

end

end OAI
end Source0401

-- Source: OAI/NumberTheory/PiExponent/Geometry/ProjectiveFramedAtlas.lean
section Source0402
-- Modified in this edition: unused plain lemmas removed; see reduction.json.
/-
Modification notice for the LogTwo project.
Derived from openai/math (Apache-2.0), revision adc7f1241b42e322a6451854ab7e4b4c146bf78a.
Original source: lean/OAI/NumberTheory/PiExponent/Geometry/ProjectiveFramedAtlas.lean
Changes: Convert module/import declarations to the Lean 4.34 public module format.
See ../THIRD_PARTY_NOTICES.txt for provenance and the recorded changes.
-/

namespace OAI

namespace PiExponentSeshadri.Projective
noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace
open PiExponentSeshadri.Frames
attribute [local instance] MvPolynomial.gradedAlgebra

universe u
variable {K σ : Type u} [CommRing K] {X : Scheme.{u}}

theorem coordinatesMap_congr (k : K →+* Γ(X,⊤)) {a b : σ → Γ(X,⊤)} (h : a = b)
    (i : σ) (ha : a i = 1) (hb : b i = 1) :
    coordinatesMap X k a i ha = coordinatesMap X k b i hb := by
  subst b
  rfl

end
end PiExponentSeshadri.Projective

end OAI
end Source0402

-- Source: OAI/NumberTheory/PiExponent/Geometry/ProjectiveChartOverlaps.lean
section Source0403
-- Modified in this edition: unused plain lemmas removed; see reduction.json.
/-
Modification notice for the LogTwo project.
Derived from openai/math (Apache-2.0), revision adc7f1241b42e322a6451854ab7e4b4c146bf78a.
Original source: lean/OAI/NumberTheory/PiExponent/Geometry/ProjectiveChartOverlaps.lean
Changes: Convert module/import declarations to the Lean 4.34 public module format.
See ../THIRD_PARTY_NOTICES.txt for provenance and the recorded changes.
-/

namespace OAI

namespace PiExponentSeshadri.Projective
noncomputable section
open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite MvPolynomial
attribute [local instance] Classical.propDecidable
attribute [local instance] MvPolynomial.gradedAlgebra

variable {R σ : Type*} [CommRing R] (i j : σ)
lemma coordinate_chart_preimage :
    Proj.awayι (PolyGrade R σ) (X i) (poly_X_mem i) (by decide) ⁻¹ᵁ
      Proj.basicOpen (PolyGrade R σ) (X j) =
      PrimeSpectrum.basicOpen (chartCoordinate (R := R) i j) := by
  rw [Proj.awayι_preimage_basicOpen _ _ (by decide) (poly_X_mem j) (by decide)]
  congr 1
  apply HomogeneousLocalization.val_injective _
  simp [HomogeneousLocalization.Away.isLocalizationElem, chartCoordinate,
    HomogeneousLocalization.Away.val_mk]

def chartPairSectionRingEquiv :
    Γ(Proj (PolyGrade R σ),
      Proj.basicOpen (PolyGrade R σ) (X i) ⊓ Proj.basicOpen (PolyGrade R σ) (X j)) ≃+*
      Localization.Away (chartCoordinate (R := R) i j) := by
  let f := Proj.awayι (PolyGrade R σ) (X i) (poly_X_mem i) (by decide)
  have e := IsOpenImmersion.ΓIso f (Proj.basicOpen (PolyGrade R σ) (X j))
  dsimp only [f] at e
  rw [Proj.opensRange_awayι, coordinate_chart_preimage] at e
  letI : Algebra (PolyChart (R := R) i)
      Γ(Spec (CommRingCat.of (PolyChart (R := R) i)),
        PrimeSpectrum.basicOpen (chartCoordinate (R := R) i j)) :=
    AlgebraicGeometry.StructureSheaf.openAlgebra _ _
  letI : IsLocalization.Away (chartCoordinate (R := R) i j)
      Γ(Spec (CommRingCat.of (PolyChart (R := R) i)),
        PrimeSpectrum.basicOpen (chartCoordinate (R := R) i j)) :=
    AlgebraicGeometry.StructureSheaf.IsLocalization.to_basicOpen _ _
  exact e.symm.commRingCatIsoToRingEquiv.trans
    (IsLocalization.algEquiv (Submonoid.powers (chartCoordinate (R := R) i j))
      Γ(Spec (CommRingCat.of (PolyChart (R := R) i)),
        PrimeSpectrum.basicOpen (chartCoordinate (R := R) i j))
      (Localization.Away (chartCoordinate (R := R) i j))).toRingEquiv

lemma coordinate_finset_preimage (s : Finset σ) :
    Proj.awayι (PolyGrade R σ) (X i) (poly_X_mem i) (by decide) ⁻¹ᵁ
      (s.inf fun j => Proj.basicOpen (PolyGrade R σ) (X j)) =
      PrimeSpectrum.basicOpen (∏ j ∈ s, chartCoordinate (R := R) i j) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp; rfl
  | @insert j s hjs ih =>
    simp only [Finset.inf_insert, Finset.prod_insert hjs, Scheme.Hom.preimage_inf, ih,
      coordinate_chart_preimage, PrimeSpectrum.basicOpen_mul]
    rfl

def chartFiniteSectionRingEquiv (s : Finset σ) :
    Γ(Proj (PolyGrade R σ),
      Proj.basicOpen (PolyGrade R σ) (X i) ⊓
        s.inf (fun j => Proj.basicOpen (PolyGrade R σ) (X j))) ≃+*
      Localization.Away (∏ j ∈ s, chartCoordinate (R := R) i j) := by
  let f := Proj.awayι (PolyGrade R σ) (X i) (poly_X_mem i) (by decide)
  have e := IsOpenImmersion.ΓIso f (s.inf fun j => Proj.basicOpen (PolyGrade R σ) (X j))
  dsimp only [f] at e
  rw [Proj.opensRange_awayι, coordinate_finset_preimage] at e
  let z := ∏ j ∈ s, chartCoordinate (R := R) i j
  letI : Algebra (PolyChart (R := R) i)
      Γ(Spec (CommRingCat.of (PolyChart (R := R) i)), PrimeSpectrum.basicOpen z) :=
    AlgebraicGeometry.StructureSheaf.openAlgebra _ _
  letI : IsLocalization.Away z
      Γ(Spec (CommRingCat.of (PolyChart (R := R) i)), PrimeSpectrum.basicOpen z) :=
    AlgebraicGeometry.StructureSheaf.IsLocalization.to_basicOpen _ _
  exact e.symm.commRingCatIsoToRingEquiv.trans
    (IsLocalization.algEquiv (Submonoid.powers z)
      Γ(Spec (CommRingCat.of (PolyChart (R := R) i)), PrimeSpectrum.basicOpen z)
      (Localization.Away z)).toRingEquiv

def chartFinitePolynomialRingEquiv (s : Finset σ) :
    Γ(Proj (PolyGrade R σ),
      Proj.basicOpen (PolyGrade R σ) (X i) ⊓
        s.inf (fun j => Proj.basicOpen (PolyGrade R σ) (X j))) ≃+*
      Localization.Away (∏ j ∈ s, chartToPoly (R := R) i (chartCoordinate i j)) :=
  (chartFiniteSectionRingEquiv i s).trans
    (IsLocalization.ringEquivOfRingEquiv
      (M := Submonoid.powers (∏ j ∈ s, chartCoordinate (R := R) i j))
      (T := Submonoid.powers (∏ j ∈ s, chartToPoly (R := R) i (chartCoordinate i j)))
      (Localization.Away (∏ j ∈ s, chartCoordinate (R := R) i j))
      (Localization.Away (∏ j ∈ s, chartToPoly (R := R) i (chartCoordinate i j)))
      (polynomialChartEquiv i) (by
      rw [Submonoid.map_powers]
      congr 1
      exact map_prod (polynomialChartEquiv i) _ _))

def chartVariableOverlapRingEquiv (s : Finset (ChartVariables i)) :
    Γ(Proj (PolyGrade R σ),
      Proj.basicOpen (PolyGrade R σ) (X i) ⊓
        s.inf (fun j => Proj.basicOpen (PolyGrade R σ) (X j.val))) ≃+*
      Localization.Away (∏ j ∈ s, (X j : MvPolynomial (ChartVariables i) R)) := by
  classical
  have hprod : (∏ j ∈ s.image Subtype.val,
      chartToPoly (R := R) i (chartCoordinate i j)) =
      ∏ j ∈ s, (X j : MvPolynomial (ChartVariables i) R) := by
    rw [Finset.prod_image]
    · apply Finset.prod_congr rfl
      intro j hj
      simp [chartToPoly_coordinate, j.property]
    · intro a ha b hb hab
      exact Subtype.ext hab
  have e := chartFinitePolynomialRingEquiv (R := R) i (s.image Subtype.val)
  rw [hprod, Finset.inf_image] at e
  exact e

end
end PiExponentSeshadri.Projective

end OAI
end Source0403

-- Source: OAI/NumberTheory/PiExponent/Geometry/ProjectiveChartRingNaturalityCore.lean
section Source0404
/-
Modification notice for the LogTwo project.
Derived from openai/math (Apache-2.0), revision adc7f1241b42e322a6451854ab7e4b4c146bf78a.
Original source: lean/OAI/NumberTheory/PiExponent/Geometry/ProjectiveChartRingNaturalityCore.lean
Changes: Convert module/import declarations to the Lean 4.34 public module format.
See ../THIRD_PARTY_NOTICES.txt for provenance and the recorded changes.
-/

namespace OAI

namespace PiExponentSeshadri.Projective
noncomputable section
open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite MvPolynomial
attribute [local instance] Classical.propDecidable
attribute [local instance] MvPolynomial.gradedAlgebra
attribute [local instance] AlgebraicGeometry.StructureSheaf.openAlgebra
variable {R σ : Type*} [CommRing R] (i : σ)

lemma away_chart_preimage_self :
    Proj.awayι (PolyGrade R σ) (X i) (poly_X_mem i) (by decide) ⁻¹ᵁ
      Proj.basicOpen (PolyGrade R σ) (X i) = ⊤ := by
  rw [← Proj.opensRange_awayι _ _ (poly_X_mem i) (by decide)]
  exact Scheme.Hom.preimage_opensRange _

lemma away_chart_appLE_top :
    (Proj.awayι (PolyGrade R σ) (X i) (poly_X_mem i) (by decide)).appLE
      (Proj.basicOpen (PolyGrade R σ) (X i)) ⊤
      (by rw [away_chart_preimage_self]) =
    (Proj.basicOpen (PolyGrade R σ) (X i)).topIso.inv ≫
      (Proj.basicOpenIsoSpec (PolyGrade R σ) (X i) (poly_X_mem i) (by decide)).inv.appTop := by
  change ((Proj.basicOpenIsoSpec (PolyGrade R σ) (X i) (poly_X_mem i) (by decide)).inv ≫
    (Proj.basicOpen (PolyGrade R σ) (X i)).ι).appLE _ _ _ = _
  rw [← Scheme.Hom.appLE_comp_appLE _ _ _ ⊤ ⊤
    (by simp) (by simp)]
  simp only [Scheme.Opens.ι_appLE, Scheme.Opens.topIso_inv]
  congr 1

private lemma chartIso_pullback_top {X : Scheme} (U : X.Opens) (A : CommRingCat)
    (e : U.toScheme ≅ Spec A) (g : A ⟶ Γ(X,U))
    (he : e.hom.appTop = (Scheme.ΓSpecIso A).hom ≫ g ≫ U.topIso.inv) :
    g ≫ U.topIso.inv ≫ e.inv.appTop = (Scheme.ΓSpecIso A).inv := by
  apply (cancel_epi (Scheme.ΓSpecIso A).hom).mp
  rw [Iso.hom_inv_id]
  calc
    _ = e.hom.appTop ≫ e.inv.appTop := by rw [he]; simp only [Category.assoc]
    _ = 𝟙 _ := by rw [← Scheme.Hom.comp_appTop, e.inv_hom_id, Scheme.Hom.id_appTop]

lemma awayToSection_pullback_top :
    Proj.awayToSection (PolyGrade R σ) (X i) ≫
      (Proj.awayι (PolyGrade R σ) (X i) (poly_X_mem i) (by decide)).appLE
        (Proj.basicOpen (PolyGrade R σ) (X i)) ⊤
        (by rw [away_chart_preimage_self]) =
      (Scheme.ΓSpecIso (CommRingCat.of (PolyChart (R := R) i))).inv := by
  rw [away_chart_appLE_top]
  apply chartIso_pullback_top
  exact Proj.basicOpenToSpec_app_top (PolyGrade R σ) (X i)

local instance chartOpenAlgebra
    (V : (Spec (CommRingCat.of (PolyChart (R := R) i))).Opens) :
    Algebra (PolyChart (R := R) i) Γ(Spec (CommRingCat.of (PolyChart (R := R) i)),V) :=
  AlgebraicGeometry.StructureSheaf.openAlgebra _ _

lemma awayToSection_pullback_open (V : (Spec (CommRingCat.of (PolyChart (R := R) i))).Opens)
    (hV : V ≤ Proj.awayι (PolyGrade R σ) (X i) (poly_X_mem i) (by decide) ⁻¹ᵁ
      Proj.basicOpen (PolyGrade R σ) (X i)) :
    Proj.awayToSection (PolyGrade R σ) (X i) ≫
      (Proj.awayι (PolyGrade R σ) (X i) (poly_X_mem i) (by decide)).appLE
        (Proj.basicOpen (PolyGrade R σ) (X i)) V hV =
      CommRingCat.ofHom (algebraMap (PolyChart (R := R) i) Γ(Spec (CommRingCat.of (PolyChart (R := R) i)),V)) := by
  change _ = (Scheme.ΓSpecIso (CommRingCat.of (PolyChart (R := R) i))).inv ≫
    (Spec (CommRingCat.of (PolyChart (R := R) i))).presheaf.map (homOfLE le_top).op
  rw [← awayToSection_pullback_top (R := R) i, Category.assoc]
  congr 1

private def relabeledSectionIso {Y Z : Scheme} (f : Y ⟶ Z) [IsOpenImmersion f]
    (V U : Z.Opens) (W : Y.Opens) (hU : f.opensRange = U) (hW : f ⁻¹ᵁ V = W) :
    Γ(Y,W) ≅ Γ(Z,U ⊓ V) := by
  have e := IsOpenImmersion.ΓIso f V
  rw [hU, hW] at e
  exact e

private lemma relabeledSectionIso_inv {Y Z : Scheme} (f : Y ⟶ Z) [IsOpenImmersion f]
    (V U : Z.Opens) (W : Y.Opens) (hU : f.opensRange = U) (hW : f ⁻¹ᵁ V = W) :
    (relabeledSectionIso f V U W hU hW).inv = f.appLE (U ⊓ V) W (by
      rw [← hU, ← hW, ← f.image_preimage_eq_opensRange_inf, f.preimage_image_eq]) := by
  subst U
  subst W
  exact IsOpenImmersion.ΓIso_inv f V

lemma chartFiniteSectionRingEquiv_restrict (s : Finset σ) (a : PolyChart (R := R) i) :
    chartFiniteSectionRingEquiv i s
      ((Proj (PolyGrade R σ)).presheaf.map (homOfLE inf_le_left).op
        (Proj.awayToSection (PolyGrade R σ) (X i) a)) =
      algebraMap _ _ a := by
  classical
  let z := ∏ j ∈ s, chartCoordinate (R := R) i j
  let : Algebra (PolyChart (R := R) i)
      Γ(Spec (CommRingCat.of (PolyChart (R := R) i)), PrimeSpectrum.basicOpen z) :=
    AlgebraicGeometry.StructureSheaf.openAlgebra _ _
  let : IsLocalization.Away z
      Γ(Spec (CommRingCat.of (PolyChart (R := R) i)), PrimeSpectrum.basicOpen z) :=
    AlgebraicGeometry.StructureSheaf.IsLocalization.to_basicOpen _ _
  let E := IsLocalization.algEquiv (Submonoid.powers z)
    Γ(Spec (CommRingCat.of (PolyChart (R := R) i)), PrimeSpectrum.basicOpen z)
    (Localization.Away z)
  change E ((relabeledSectionIso
    (Proj.awayι (PolyGrade R σ) (X i) (poly_X_mem i) (by decide))
    (s.inf fun j => Proj.basicOpen (PolyGrade R σ) (X j))
    (Proj.basicOpen (PolyGrade R σ) (X i)) (PrimeSpectrum.basicOpen z)
    (Proj.opensRange_awayι _ _ (poly_X_mem i) (by decide))
    (coordinate_finset_preimage i s)).inv
      ((Proj (PolyGrade R σ)).presheaf.map (homOfLE inf_le_left).op
        (Proj.awayToSection (PolyGrade R σ) (X i) a))) = _
  rw [← E.commutes a]
  apply congrArg E
  erw [relabeledSectionIso_inv]
  change (Proj.awayToSection (PolyGrade R σ) (X i) ≫
    (Proj (PolyGrade R σ)).presheaf.map (homOfLE inf_le_left).op ≫
    (Proj.awayι (PolyGrade R σ) (X i) (poly_X_mem i) (by decide)).appLE _ _ _) a = _
  erw [Scheme.Hom.map_appLE]
  exact congrArg (fun f : CommRingCat.of (PolyChart (R := R) i) ⟶
    Γ(Spec (CommRingCat.of (PolyChart (R := R) i)), PrimeSpectrum.basicOpen z) => f a)
    (awayToSection_pullback_open i (PrimeSpectrum.basicOpen z) _)

attribute [local irreducible] chartFiniteSectionRingEquiv

lemma chartFinitePolynomialRingEquiv_restrict (s : Finset σ) (a : PolyChart (R := R) i) :
    chartFinitePolynomialRingEquiv i s
      ((Proj (PolyGrade R σ)).presheaf.map (homOfLE inf_le_left).op
        (Proj.awayToSection (PolyGrade R σ) (X i) a)) =
      algebraMap _ _ (chartToPoly i a) := by
  rw [chartFinitePolynomialRingEquiv, RingEquiv.trans_apply, chartFiniteSectionRingEquiv_restrict]
  exact IsLocalization.ringEquivOfRingEquiv_eq _ _

lemma chartFinitePolynomialRingEquiv_restrict_poly (s : Finset σ)
    (p : MvPolynomial (ChartVariables i) R) :
    chartFinitePolynomialRingEquiv i s
      ((Proj (PolyGrade R σ)).presheaf.map (homOfLE inf_le_left).op
        (Proj.awayToSection (PolyGrade R σ) (X i) (polyToChart i p))) =
      algebraMap _ _ p := by
  rw [chartFinitePolynomialRingEquiv_restrict]
  have h := RingHom.congr_fun (chartToPoly_comp_polyToChart (R := R) i) p
  change chartToPoly i (polyToChart i p) = p at h
  rw [h]

end
end PiExponentSeshadri.Projective

end OAI
end Source0404

-- Source: OAI/NumberTheory/PiExponent/Geometry/ProjectiveChartRingNaturality.lean
section Source0405
-- Modified in this edition: unused plain lemmas removed; see reduction.json.
/-
Modification notice for the LogTwo project.
Derived from openai/math (Apache-2.0), revision adc7f1241b42e322a6451854ab7e4b4c146bf78a.
Original source: lean/OAI/NumberTheory/PiExponent/Geometry/ProjectiveChartRingNaturality.lean
Changes: Convert module/import declarations to the Lean 4.34 public module format.
See ../THIRD_PARTY_NOTICES.txt for provenance and the recorded changes.
-/

namespace OAI

namespace PiExponentSeshadri.Projective
noncomputable section
open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite MvPolynomial
attribute [local instance] Classical.propDecidable
attribute [local instance] MvPolynomial.gradedAlgebra
attribute [local instance] AlgebraicGeometry.StructureSheaf.openAlgebra
variable {R σ : Type*} [CommRing R] (i : σ)

private def relabeledOverlapEquiv {X : Scheme} {A : Type*} [CommRing A]
    (U V V' : X.Opens) (z z' : A)
    (e : Γ(X,U ⊓ V) ≃+* Localization.Away z) (hz : z = z') (hV : V = V') :
    Γ(X,U ⊓ V') ≃+* Localization.Away z' := by
  rw [hz, hV] at e
  exact e

private lemma relabeledOverlapEquiv_restrict {X : Scheme} {A : Type*} [CommRing A]
    (U V V' : X.Opens) (z z' : A)
    (e : Γ(X,U ⊓ V) ≃+* Localization.Away z) (hz : z = z') (hV : V = V')
    (a : Γ(X,U)) (p : A)
    (h : e (X.presheaf.map (homOfLE inf_le_left).op a) = algebraMap _ _ p) :
    relabeledOverlapEquiv U V V' z z' e hz hV
      (X.presheaf.map (homOfLE inf_le_left).op a) = algebraMap _ _ p := by
  subst z'
  subst V'
  exact h

lemma chartVariableOverlapRingEquiv_restrict (s : Finset (ChartVariables i))
    (p : MvPolynomial (ChartVariables i) R) :
    chartVariableOverlapRingEquiv i s
      ((Proj (PolyGrade R σ)).presheaf.map (homOfLE inf_le_left).op
        (Proj.awayToSection (PolyGrade R σ) (X i) (polyToChart i p))) =
      algebraMap _ _ p := by
  classical
  have hprod : (∏ j ∈ s.image Subtype.val,
      chartToPoly (R := R) i (chartCoordinate i j)) =
      ∏ j ∈ s, (X j : MvPolynomial (ChartVariables i) R) := by
    rw [Finset.prod_image]
    · apply Finset.prod_congr rfl
      intro j hj
      simp [chartToPoly_coordinate, j.property]
    · intro a ha b hb hab
      exact Subtype.ext hab
  change relabeledOverlapEquiv
    (Proj.basicOpen (PolyGrade R σ) (X i))
    ((s.image Subtype.val).inf fun j => Proj.basicOpen (PolyGrade R σ) (X j))
    (s.inf fun j => Proj.basicOpen (PolyGrade R σ) (X j.val)) _ _
    (chartFinitePolynomialRingEquiv i (s.image Subtype.val)) hprod
    (by rw [Finset.inf_image]; rfl) _ = _
  apply relabeledOverlapEquiv_restrict
  exact chartFinitePolynomialRingEquiv_restrict_poly i (s.image Subtype.val) p

lemma chartVariableOverlapRingEquiv_restrict_chart (s : Finset (ChartVariables i))
    (a : PolyChart (R := R) i) :
    chartVariableOverlapRingEquiv i s
      ((Proj (PolyGrade R σ)).presheaf.map (homOfLE inf_le_left).op
        (Proj.awayToSection (PolyGrade R σ) (X i) a)) =
      algebraMap _ _ (chartToPoly i a) := by
  have h := chartVariableOverlapRingEquiv_restrict i s (chartToPoly i a)
  have hid := RingHom.congr_fun (polyToChart_comp_chartToPoly (R := R) i) a
  change polyToChart i (chartToPoly i a) = a at hid
  simpa only [hid] using h

@[simp] lemma chartVariableOverlapRingEquiv_restrict_coordinate
    (s : Finset (ChartVariables i)) (j : ChartVariables i) :
    chartVariableOverlapRingEquiv i s
      ((Proj (PolyGrade R σ)).presheaf.map (homOfLE inf_le_left).op
        (Proj.awayToSection (PolyGrade R σ) (X i) (chartCoordinate i j.val))) =
      algebraMap _ _ (X (R := R) j) := by
  rw [chartVariableOverlapRingEquiv_restrict_chart]
  simp [chartToPoly_coordinate, j.property]

@[simp] lemma chartVariableOverlapRingEquiv_restrict_constant
    (s : Finset (ChartVariables i)) (r : R) :
    chartVariableOverlapRingEquiv i s
      ((Proj (PolyGrade R σ)).presheaf.map (homOfLE inf_le_left).op
        (Proj.awayToSection (PolyGrade R σ) (X i) (chartConstants i r))) =
      algebraMap _ _ (C (σ := ChartVariables i) r) := by
  rw [chartVariableOverlapRingEquiv_restrict_chart, chartToPoly_constants]

end
end PiExponentSeshadri.Projective

end OAI
end Source0405

-- Source: OAI/NumberTheory/PiExponent/Geometry/ProjectiveCoordinateValues.lean
section Source0406
-- Modified in this edition: unused plain lemmas removed; see reduction.json.
/-
Modification notice for the LogTwo project.
Derived from openai/math (Apache-2.0), revision adc7f1241b42e322a6451854ab7e4b4c146bf78a.
Original source: lean/OAI/NumberTheory/PiExponent/Geometry/ProjectiveCoordinateValues.lean
Changes: Convert module/import declarations to the Lean 4.34 public module format.
See ../THIRD_PARTY_NOTICES.txt for provenance and the recorded changes.
-/

namespace OAI

noncomputable section

namespace PiExponentSeshadri

namespace Projective
open AlgebraicGeometry CategoryTheory TopologicalSpace MvPolynomial
attribute [local instance] MvPolynomial.gradedAlgebra
variable {K σ : Type} [CommRing K] (i : σ)

lemma evalAway_coordinate {R : Type} [CommRing R]
    (k : K →+* R) (a : σ → R) (hi : a i = 1) (j : σ) :
    evalAway (eval₂Hom k a) (X i)
      (by simpa only [eval₂Hom_X', hi] using (isUnit_one : IsUnit (1 : R)))
      (chartCoordinate (R := K) i j) = a j := by
  have h := evalAway_mk_clear (eval₂Hom k a) (poly_X_mem (R := K) i)
    (by simpa only [eval₂Hom_X', hi] using (isUnit_one : IsUnit (1 : R)))
    1 (X j) (by simpa using poly_X_mem (R := K) j)
  simpa only [chartCoordinate, eval₂Hom_X', hi, one_pow, mul_one] using h

lemma coordinatesMap_pullback_coordinate {Y : Scheme}
    (k : K →+* Γ(Y,⊤)) (a : σ → Γ(Y,⊤)) (hi : a i = 1)
    (g : Y ⟶ Spec (CommRingCat.of (PolyChart (R := K) i)))
    (heq : coordinatesMap Y k a i hi =
      g ≫ Proj.awayι (PolyGrade K σ) (X i) (poly_X_mem i) (by decide))
    (j : σ) :
    a j = ((Scheme.ΓSpecIso (CommRingCat.of (PolyChart (R := K) i))).inv ≫
      g.appTop).hom (chartCoordinate (R := K) i j) := by
  let F := evalAway (𝒜 := PolyGrade K σ) (eval₂Hom k a) (X i)
    (by simpa only [eval₂Hom_X', hi] using (isUnit_one : IsUnit (1 : Γ(Y,⊤))))
  have hfactor : Y.toSpecΓ ≫ Spec.map (CommRingCat.ofHom F) = g := by
    apply (cancel_mono (Proj.awayι (PolyGrade K σ) (X i) (poly_X_mem i) (by decide))).1
    simpa only [coordinatesMap, fromUnitCoordinate, Category.assoc] using heq
  have hf := congrArg (fun g => (Scheme.ΓSpecIso (CommRingCat.of (PolyChart (R := K) i))).inv ≫
    Scheme.Hom.appTop g) hfactor
  simp only [Scheme.Hom.comp_appTop, Scheme.toSpecΓ_appTop,
    ← Scheme.ΓSpecIso_inv_naturality_assoc, Iso.inv_hom_id, Category.comp_id] at hf
  have h := congrArg (fun g : CommRingCat.of (PolyChart (R := K) i) ⟶ _ =>
    g.hom (chartCoordinate (R := K) i j)) hf
  change F (chartCoordinate (R := K) i j) = _ at h
  rw [evalAway_coordinate i k a hi j] at h
  exact h

lemma sectionFrame_coordinate {Y : Scheme} {M : Y.Modules}
    (k : K →+* Γ(Y,⊤)) (s : σ → (PiExponentSeshadri.Frames.O Y ⟶ M))
    (hc : (⨆ a, SectionOpens.isoOpen (s a)) = ⊤)
    (g : (SectionOpens.isoOpen (s i)).toScheme ⟶
      Spec (CommRingCat.of (PolyChart (R := K) i)))
    (hg : (SectionOpens.isoOpen (s i)).ι ≫ sectionsMorphism k s hc =
      g ≫ Proj.awayι (PolyGrade K σ) (X i) (poly_X_mem i) (by decide)) (j : σ) :
    PiExponentSeshadri.Frames.coefficient (sectionFrame (s i))
      (PiExponentSeshadri.Frames.restrictSection (SectionOpens.isoOpen (s i)).ι (s j)) =
    ((Scheme.ΓSpecIso (CommRingCat.of (PolyChart (R := K) i))).inv ≫
      g.appTop).hom (chartCoordinate (R := K) i j) := by
  exact coordinatesMap_pullback_coordinate i
    ((SectionOpens.isoOpen (s i)).ι.appTop.hom.comp k)
    (fun j => PiExponentSeshadri.Frames.coefficient (sectionFrame (s i))
      (PiExponentSeshadri.Frames.restrictSection (SectionOpens.isoOpen (s i)).ι (s j)))
    (sectionFrame_normalized (s i)) g
    ((sectionsMorphism_local k s hc i).symm.trans hg) j

end Projective

namespace Frames
open AlgebraicGeometry CategoryTheory TopologicalSpace
variable {X Y Z W : Scheme}

end Frames

end PiExponentSeshadri

end

end OAI
end Source0406

-- Source: OAI/NumberTheory/PiExponent/Approximation/SectionPowerFrames.lean
section Source0407
-- Modified in this edition: unused plain lemmas removed; see reduction.json.
/-
Modification notice for the LogTwo project.
Derived from openai/math (Apache-2.0), revision adc7f1241b42e322a6451854ab7e4b4c146bf78a.
Original source: lean/OAI/NumberTheory/PiExponent/Approximation/SectionPowerFrames.lean
Changes: Convert module/import declarations to the Lean 4.34 public module format.
See ../THIRD_PARTY_NOTICES.txt for provenance and the recorded changes.
-/

namespace OAI

namespace PiExponentSeshadri.Geometry
noncomputable section
open AlgebraicGeometry CategoryTheory TopologicalSpace
open PiExponentSeshadri.Frames
variable {X : Scheme} {M : X.Modules}

def normalizedPowerFrame (U : X.Opens) (s : structureSheaf X ⟶ M)
    [IsIso ((Scheme.Modules.restrictFunctor U.ι).map s)] (n : ℕ) :
    (modulePow X M n).restrict U.ι ≅ structureSheaf U.toScheme := by
  letI := powerSection_restrict_isIso U s n
  exact (asIso ((Scheme.Modules.restrictFunctor U.ι).map (powerSection s n))).symm ≪≫
    Scheme.Modules.restrictUnitIso U.ι

lemma normalizedPowerFrame_normalized (U : X.Opens) (s : structureSheaf X ⟶ M)
    [IsIso ((Scheme.Modules.restrictFunctor U.ι).map s)] (n : ℕ) :
    coefficient (normalizedPowerFrame U s n) (restrictSection U.ι (powerSection s n)) = 1 := by
  change coefficient (normalizedPowerFrame U s n) (normalizedPowerFrame U s n).inv = 1
  exact coefficient_frame _

lemma normalizedPowerFrame_coefficient (U : X.Opens) (si sj : structureSheaf X ⟶ M)
    [IsIso ((Scheme.Modules.restrictFunctor U.ι).map si)]
    (e : M.restrict U.ι ≅ structureSheaf U.toScheme)
    (hi : coefficient e (restrictSection U.ι si) = 1) (n : ℕ) :
    coefficient (normalizedPowerFrame U si n) (restrictSection U.ι (powerSection sj n)) =
      coefficient e (restrictSection U.ι sj) ^ n := by
  have hc := coefficient_change (localPowerFrame U e n) (normalizedPowerFrame U si n)
    (restrictSection U.ι (powerSection sj n))
  have hbase := coefficient_change (localPowerFrame U e n) (normalizedPowerFrame U si n)
    (restrictSection U.ι (powerSection si n))
  rw [normalizedPowerFrame_normalized, local_powerSection_coefficient, hi,
    one_pow, mul_one] at hbase
  rw [local_powerSection_coefficient, ← mul_assoc, ← hbase, one_mul] at hc
  exact hc

def coordinatePowerFrame (s : structureSheaf X ⟶ M) (n : ℕ) :
    (modulePow X M n).restrict (SectionOpens.isoOpen s).ι ≅
      structureSheaf (SectionOpens.isoOpen s).toScheme := by
  letI := SectionOpens.isIso_restrict_isoOpen s
  exact normalizedPowerFrame _ s n

lemma coordinatePowerFrame_coefficient (si sj : structureSheaf X ⟶ M) (n : ℕ) :
    coefficient (coordinatePowerFrame si n)
      (restrictSection (SectionOpens.isoOpen si).ι (powerSection sj n)) =
    coefficient (PiExponentSeshadri.Projective.sectionFrame si)
      (restrictSection (SectionOpens.isoOpen si).ι sj) ^ n := by
  exact @normalizedPowerFrame_coefficient X M _ si sj
    (SectionOpens.isIso_restrict_isoOpen si) (PiExponentSeshadri.Projective.sectionFrame si)
    (PiExponentSeshadri.Projective.sectionFrame_normalized si) n

@[simp] lemma coordinatePowerFrame_normalized (s : structureSheaf X ⟶ M) (n : ℕ) :
    coefficient (coordinatePowerFrame s n)
      (restrictSection (SectionOpens.isoOpen s).ι (powerSection s n)) = 1 := by
  erw [coordinatePowerFrame_coefficient, PiExponentSeshadri.Projective.sectionFrame_normalized, one_pow]
  rfl

lemma coordinatePowerFrame_frameChange (si sj : structureSheaf X ⟶ M) (n : ℕ)
    {W : X.Opens} (hi : W ≤ SectionOpens.isoOpen si) (hj : W ≤ SectionOpens.isoOpen sj) :
    (frameChange (restrictOpenFrame hi (coordinatePowerFrame si n))
      (restrictOpenFrame hj (coordinatePowerFrame sj n)) : Γ(W.toScheme,⊤)) =
      (X.homOfLE hj).appTop
        (coefficient (PiExponentSeshadri.Projective.sectionFrame sj)
          (restrictSection (SectionOpens.isoOpen sj).ι si)) ^ n := by
  erw [frameChange_restrictOpenFrame hi hj _ _ (powerSection si n)
    (coordinatePowerFrame_normalized si n), coordinatePowerFrame_coefficient, map_pow]
  rfl

end
end PiExponentSeshadri.Geometry

end OAI
end Source0407

-- Source: OAI/NumberTheory/PiExponent/Cohomology/ProjectiveMonomialCech.lean
section Source0408
-- Modified in this edition: unused plain lemmas removed; see reduction.json.
/-
Modification notice for the LogTwo project.
Derived from openai/math (Apache-2.0), revision adc7f1241b42e322a6451854ab7e4b4c146bf78a.
Original source: lean/OAI/NumberTheory/PiExponent/Cohomology/ProjectiveMonomialCech.lean
Changes: Convert module/import declarations to the Lean 4.34 public module format.
See ../THIRD_PARTY_NOTICES.txt for provenance and the recorded changes.
-/

namespace OAI

namespace PiExponent.ProjectiveMonomialCech

noncomputable section

open scoped BigOperators

variable {ι K : Type*} [Fintype ι] [AddCommGroup K]

def Monomial (ι : Type*) [Fintype ι] (d : ℤ) :=
  {a : ι → ℤ // ∑ i, a i = d}

abbrev Laurent (ι K : Type*) [Fintype ι] [Zero K] (d : ℤ) :=
  Monomial ι d →₀ K

def RegularOn {d : ℤ} (s : Set ι) (f : Laurent ι K d) : Prop :=
  ∀ a, f a ≠ 0 → ∀ k, a.val k < 0 → k ∈ s

def overlapSupport {d : ℤ} (c : ι → ι → Laurent ι K d) (i : ι) :
    Finset (Monomial ι d) := by
  classical
  exact Finset.univ.biUnion fun j => (c j i).support

def primitive {d : ℤ} (pivot : Monomial ι d → ι)
    (c : ι → ι → Laurent ι K d) (i : ι) : Laurent ι K d := by
  classical
  exact Finsupp.onFinset (overlapSupport c i)
    (fun a => c (pivot a) i a)
    (fun a ha => Finset.mem_biUnion.mpr
      ⟨pivot a, Finset.mem_univ _, Finsupp.mem_support_iff.mpr ha⟩)

@[simp] theorem primitive_apply {d : ℤ} (pivot : Monomial ι d → ι)
    (c : ι → ι → Laurent ι K d) (i : ι) (a : Monomial ι d) :
    primitive pivot c i a = c (pivot a) i a := rfl

theorem exists_nonnegative_coordinate [Nonempty ι] {d : ℤ}
    (hd : 0 ≤ d) (a : Monomial ι d) : ∃ i, 0 ≤ a.val i := by
  by_contra h
  have hneg : ∀ i, a.val i < 0 := fun i => lt_of_not_ge (fun hi => h ⟨i, hi⟩)
  have htotal : (∑ i, a.val i) < 0 :=
    Finset.sum_neg (fun i _ => hneg i) Finset.univ_nonempty
  rw [a.property] at htotal
  exact (not_lt_of_ge hd) htotal

end
end PiExponent.ProjectiveMonomialCech

end OAI
end Source0408

-- Source: OAI/NumberTheory/PiExponent/Cohomology/ProjectiveLaurentVertex.lean
section Source0409
-- Modified in this edition: unused plain lemmas removed; see reduction.json.
/-
Modification notice for the LogTwo project.
Derived from openai/math (Apache-2.0), revision adc7f1241b42e322a6451854ab7e4b4c146bf78a.
Original source: lean/OAI/NumberTheory/PiExponent/Cohomology/ProjectiveLaurentVertex.lean
Changes: Convert module/import declarations to the Lean 4.34 public module format.
Remove redundant rfl steps after simp closes the goal.
See ../THIRD_PARTY_NOTICES.txt for provenance and the recorded changes.
-/

namespace OAI

noncomputable section

namespace PiExponent.GeometrySupport.ProjectiveLaurentVertex

section

attribute [local instance] Classical.propDecidable
open scoped BigOperators
open PiExponent.ProjectiveMonomialCech

variable {ι : Type*} [Fintype ι]

abbrev ChartExponent (i : ι) := {j : ι // j ≠ i} →₀ ℕ

def VertexMonomialSet (i : ι) (d : ℤ) : Set (Monomial ι d) :=
  {a | ∀ j, j ≠ i → 0 ≤ a.val j}

def encode (i : ι) (d : ℤ) (b : ChartExponent i) : Monomial ι d := by
  classical
  let a : ι → ℤ := fun j => if h : j = i then
    d - ∑ k : {j : ι // j ≠ i}, (b k : ℤ) else (b ⟨j, h⟩ : ℤ)
  have hi : a i = d - ∑ k : {j : ι // j ≠ i}, (b k : ℤ) := by simp [a]
  have ho : ∀ j : {j : ι // j ≠ i}, a j = (b j : ℤ) := by
    intro j
    simp [a, j.property]
  refine ⟨a, ?_⟩
  rw [Fintype.sum_eq_add_sum_subtype_ne _ i, hi]
  simp_rw [ho]
  omega

@[simp] theorem encode_self (i : ι) (d : ℤ) (b : ChartExponent i) :
    (encode i d b).val i = d - ∑ k : {j : ι // j ≠ i}, (b k : ℤ) := by
  classical
  simp [encode]

@[simp] theorem encode_other (i : ι) (d : ℤ) (b : ChartExponent i)
    (j : {j : ι // j ≠ i}) : (encode i d b).val j = (b j : ℤ) := by
  classical
  simp [encode, j.property]

theorem encode_regular (i : ι) (d : ℤ) (b : ChartExponent i) :
    encode i d b ∈ VertexMonomialSet i d := by
  intro j hj
  simpa only [encode_other i d b ⟨j, hj⟩] using Int.natCast_nonneg (b ⟨j, hj⟩)

def decode (i : ι) (d : ℤ) (a : VertexMonomialSet i d) : ChartExponent i :=
  Finsupp.equivFunOnFinite.symm (fun j => (a.val.val j).toNat)

@[simp] theorem decode_apply (i : ι) (d : ℤ) (a : VertexMonomialSet i d)
    (j : {j : ι // j ≠ i}) : decode i d a j = (a.val.val j).toNat := rfl

@[simp] theorem decode_encode (i : ι) (d : ℤ) (b : ChartExponent i) :
    decode i d ⟨encode i d b, encode_regular i d b⟩ = b := by
  ext j
  simp

@[simp] theorem encode_decode (i : ι) (d : ℤ) (a : VertexMonomialSet i d) :
    encode i d (decode i d a) = a.val := by
  classical
  apply Subtype.ext
  funext j
  by_cases hj : j = i
  · subst j
    rw [encode_self]
    have h := a.val.property
    rw [Fintype.sum_eq_add_sum_subtype_ne _ i] at h
    have hs : (∑ k : {j : ι // j ≠ i}, ((decode i d a k : ℕ) : ℤ)) =
        ∑ k : {j : ι // j ≠ i}, a.val.val k := by
      apply Finset.sum_congr rfl
      intro k hk
      exact Int.toNat_of_nonneg (a.property k k.property)
    rw [hs]
    omega
  · change (encode i d (decode i d a)).val (⟨j, hj⟩ : {j : ι // j ≠ i}) = _
    rw [encode_other, decode_apply, Int.toNat_of_nonneg (a.property j hj)]

def exponentEquiv (i : ι) (d : ℤ) : ChartExponent i ≃ VertexMonomialSet i d where
  toFun b := ⟨encode i d b, encode_regular i d b⟩
  invFun := decode i d
  left_inv := decode_encode i d
  right_inv a := Subtype.ext (encode_decode i d a)

variable {R : Type*} [CommRing R]

def vertexPolynomialEquiv (i : ι) (d : ℤ) :
    MvPolynomial {j : ι // j ≠ i} R ≃ₗ[R]
      Finsupp.supported R R (VertexMonomialSet i d) :=
  (AddMonoidAlgebra.coeffLinearEquiv R).trans <|
    (Finsupp.domLCongr (exponentEquiv i d)).trans
      (Finsupp.supportedEquivFinsupp (VertexMonomialSet i d)).symm

def vertexLaurent (i : ι) (d : ℤ) :
    MvPolynomial {j : ι // j ≠ i} R →ₗ[R] Laurent ι R d :=
  (Finsupp.supported R R (VertexMonomialSet i d)).subtype.comp
    (vertexPolynomialEquiv i d).toLinearMap

@[simp] theorem vertexLaurent_monomial (i : ι) (d : ℤ) (b : ChartExponent i) (r : R) :
    vertexLaurent i d (MvPolynomial.monomial b r) = Finsupp.single (encode i d b) r := by
  classical
  simp [vertexLaurent, vertexPolynomialEquiv, MvPolynomial.monomial, exponentEquiv]

@[simp] theorem vertexLaurent_coefficient (i : ι) (d : ℤ) (b : ChartExponent i)
    (p : MvPolynomial {j : ι // j ≠ i} R) :
    vertexLaurent i d p (encode i d b) = p.coeff b := by
  classical
  simp [vertexLaurent, vertexPolynomialEquiv, Finsupp.extendDomain_apply,
    encode_regular, exponentEquiv]

theorem mem_supported_iff_regular (i : ι) (d : ℤ) (p : Laurent ι R d) :
    p ∈ Finsupp.supported R R (VertexMonomialSet i d) ↔ RegularOn {i} p := by
  classical
  rw [Finsupp.mem_supported]
  constructor
  · intro hp a ha j hj
    have h := hp (Finsupp.mem_support_iff.mpr ha)
    by_contra hji
    exact not_lt_of_ge (h j hji) hj
  · intro hp a ha j hj
    by_contra hneg
    exact hj (hp a (Finsupp.mem_support_iff.mp ha) j (lt_of_not_ge hneg))

theorem vertexLaurent_injective (i : ι) (d : ℤ) :
    Function.Injective (vertexLaurent (R := R) i d) :=
  Subtype.val_injective.comp (vertexPolynomialEquiv i d).injective

end

section
attribute [local instance] Classical.propDecidable
open scoped BigOperators
open PiExponent.ProjectiveMonomialCech
variable {ι R : Type*} [Fintype ι] [CommRing R]

def fullEncode (i : ι) (d : ℤ) (b : {j : ι // j ≠ i} → ℤ) : Monomial ι d := by
  classical
  let a : ι → ℤ := fun j => if h : j = i then
    d - ∑ k : {j : ι // j ≠ i}, b k else b ⟨j, h⟩
  have hi : a i = d - ∑ k : {j : ι // j ≠ i}, b k := by simp [a]
  have ho : ∀ j : {j : ι // j ≠ i}, a j = b j := by
    intro j
    simp [a, j.property]
  refine ⟨a, ?_⟩
  rw [Fintype.sum_eq_add_sum_subtype_ne _ i, hi]
  simp_rw [ho]
  omega

@[simp] theorem fullEncode_self (i : ι) (d : ℤ) (b : {j : ι // j ≠ i} → ℤ) :
    (fullEncode i d b).val i = d - ∑ k : {j : ι // j ≠ i}, b k := by
  classical
  simp [fullEncode]

@[simp] theorem fullEncode_other (i : ι) (d : ℤ) (b : {j : ι // j ≠ i} → ℤ)
    (j : {j : ι // j ≠ i}) : (fullEncode i d b).val j = b j := by
  classical
  simp [fullEncode, j.property]

def fullExponentEquiv (i : ι) (d : ℤ) : ({j : ι // j ≠ i} → ℤ) ≃ Monomial ι d where
  toFun := fullEncode i d
  invFun a j := a.val j
  left_inv b := by funext j; simp
  right_inv a := by
    apply Subtype.ext
    funext j
    by_cases hj : j = i
    · subst j
      rw [fullEncode_self]
      have h := a.property
      rw [Fintype.sum_eq_add_sum_subtype_ne _ i] at h
      change d - (∑ k : {j : ι // j ≠ i}, a.val k) = a.val i
      omega
    · exact fullEncode_other i d _ ⟨j, hj⟩

abbrev chartGroupAlgebra (i : ι) := AddMonoidAlgebra R ({j : ι // j ≠ i} → ℤ)

def natExponentHom (i : ι) : ChartExponent i →+ ({j : ι // j ≠ i} → ℤ) where
  toFun b j := b j
  map_zero' := by ext j; simp
  map_add' := by intro a b; ext j; simp

def polynomialToGroupAlgebra (i : ι) :
    MvPolynomial {j : ι // j ≠ i} R →+* chartGroupAlgebra (R := R) i :=
  AddMonoidAlgebra.mapDomainRingHom R (natExponentHom i)

omit [Fintype ι] in
theorem polynomialToGroupAlgebra_injective (i : ι) :
    Function.Injective (polynomialToGroupAlgebra (R := R) i) := by
  apply AddMonoidAlgebra.mapDomain_injective
  intro a b hab
  ext j
  exact Int.natCast_inj.mp (congrFun hab j)

def groupAlgebraToLaurent (i : ι) (d : ℤ) : chartGroupAlgebra (R := R) i ≃+ Laurent ι R d :=
  (AddMonoidAlgebra.coeffAddEquiv).trans (Finsupp.domCongr (fullExponentEquiv i d))

def chartProduct (i : ι) (s : Finset {j : ι // j ≠ i}) : MvPolynomial {j : ι // j ≠ i} R :=
  ∏ j ∈ s, MvPolynomial.X j

omit [Fintype ι] in
theorem groupAlgebra_single_isUnit (i : ι) (a : {j : ι // j ≠ i} → ℤ) :
    IsUnit (AddMonoidAlgebra.single a (1 : R) : chartGroupAlgebra (R := R) i) := by
  apply isUnit_iff_exists_inv.mpr
  refine ⟨AddMonoidAlgebra.single (-a) 1, ?_⟩
  rw [AddMonoidAlgebra.single_mul_single]
  simp only [add_neg_cancel, one_mul]
  rfl

omit [Fintype ι] in
@[simp] theorem polynomialToGroupAlgebra_X (i : ι) (j : {j : ι // j ≠ i}) :
    polynomialToGroupAlgebra (R := R) i (MvPolynomial.X j) =
      AddMonoidAlgebra.single (natExponentHom i (Finsupp.single j 1)) 1 := by
  change AddMonoidAlgebra.mapDomain _ (AddMonoidAlgebra.single _ _) = _
  exact AddMonoidAlgebra.mapDomain_single

omit [Fintype ι] in
theorem groupAlgebra_product_isUnit (i : ι) (s : Finset {j : ι // j ≠ i}) :
    IsUnit (polynomialToGroupAlgebra (R := R) i (chartProduct i s)) := by
  rw [chartProduct, map_prod]
  exact IsUnit.prod_iff.mpr fun j _ => by
    rw [polynomialToGroupAlgebra_X]
    exact groupAlgebra_single_isUnit i _

def overlapToGroupAlgebra (i : ι) (s : Finset {j : ι // j ≠ i}) :
    Localization.Away (chartProduct (R := R) i s) →+* chartGroupAlgebra (R := R) i :=
  Localization.awayLift (polynomialToGroupAlgebra i) (chartProduct i s)
    (groupAlgebra_product_isUnit i s)

omit [Fintype ι] in
@[simp] theorem overlapToGroupAlgebra_base (i : ι) (s : Finset {j : ι // j ≠ i})
    (p : MvPolynomial {j : ι // j ≠ i} R) :
    overlapToGroupAlgebra i s (algebraMap _ _ p) = polynomialToGroupAlgebra i p := by
  exact IsLocalization.Away.lift_eq (chartProduct i s) (groupAlgebra_product_isUnit i s) p

omit [Fintype ι] in
theorem overlapToGroupAlgebra_injective (i : ι) (s : Finset {j : ι // j ≠ i}) :
    Function.Injective (overlapToGroupAlgebra (R := R) i s) := by
  apply (IsLocalization.injective_iff_map_algebraMap_eq
    (Submonoid.powers (chartProduct (R := R) i s)) (overlapToGroupAlgebra i s)).mpr
  intro x y
  constructor
  · exact congrArg _
  · intro h
    rw [overlapToGroupAlgebra_base, overlapToGroupAlgebra_base] at h
    exact congrArg _ (polynomialToGroupAlgebra_injective i h)

def overlapLaurent (i : ι) (d : ℤ) (s : Finset {j : ι // j ≠ i}) :
    Localization.Away (chartProduct (R := R) i s) →+ Laurent ι R d :=
  (groupAlgebraToLaurent i d).toAddMonoidHom.comp (overlapToGroupAlgebra i s).toAddMonoidHom

theorem overlapLaurent_injective (i : ι) (d : ℤ) (s : Finset {j : ι // j ≠ i}) :
    Function.Injective (overlapLaurent (R := R) i d s) :=
  (groupAlgebraToLaurent i d).injective.comp (overlapToGroupAlgebra_injective i s)

def productExponent (i : ι) (s : Finset {j : ι // j ≠ i}) : {j : ι // j ≠ i} → ℤ :=
  ∑ j ∈ s, natExponentHom i (Finsupp.single j 1)

omit [Fintype ι] in
@[simp] theorem polynomialToGroupAlgebra_product (i : ι)
    (s : Finset {j : ι // j ≠ i}) :
    polynomialToGroupAlgebra (R := R) i (chartProduct i s) =
      AddMonoidAlgebra.single (productExponent i s) 1 := by
  classical
  induction s using Finset.induction_on with
  | empty =>
      simp only [chartProduct, productExponent, Finset.prod_empty, Finset.sum_empty, map_one]
      rfl
  | @insert j s hj ih =>
      simp only [chartProduct, Finset.prod_insert hj, map_mul] at *
      rw [polynomialToGroupAlgebra_X, ih, AddMonoidAlgebra.single_mul_single]
      simp [productExponent, hj]

omit [Fintype ι] in
@[simp] theorem productExponent_outside (i : ι) (s : Finset {j : ι // j ≠ i})
    (k : {j : ι // j ≠ i}) (hk : k ∉ s) : productExponent i s k = 0 := by
  classical
  simp only [productExponent, Finset.sum_apply]
  apply Finset.sum_eq_zero
  intro j hj
  have hne : j ≠ k := fun h => hk (h ▸ hj)
  simp [natExponentHom, Ne.symm hne]

omit [Fintype ι] in
theorem polynomialToGroupAlgebra_nonnegative (i : ι)
    (p : MvPolynomial {j : ι // j ≠ i} R) (a : {j : ι // j ≠ i} → ℤ)
    (ha : (polynomialToGroupAlgebra i p).coeff a ≠ 0)
    (k : {j : ι // j ≠ i}) : 0 ≤ a k := by
  obtain ⟨b, rfl⟩ := Finsupp.mem_range_of_mapDomain_ne_zero ha
  exact Int.natCast_nonneg _

omit [Fintype ι] in
theorem overlapToGroupAlgebra_nonnegative (i : ι) (s : Finset {j : ι // j ≠ i})
    (z : Localization.Away (chartProduct (R := R) i s))
    (a : {j : ι // j ≠ i} → ℤ) (ha : (overlapToGroupAlgebra i s z).coeff a ≠ 0)
    (k : {j : ι // j ≠ i}) (hk : k ∉ s) : 0 ≤ a k := by
  obtain ⟨n, p, hp⟩ := IsLocalization.Away.surj (chartProduct (R := R) i s) z
  have h := congrArg (overlapToGroupAlgebra i s) hp
  simp only [map_mul, map_pow, overlapToGroupAlgebra_base,
    polynomialToGroupAlgebra_product, AddMonoidAlgebra.single_pow, one_pow] at h
  have hc := congrArg (fun q : chartGroupAlgebra (R := R) i =>
    q.coeff (a + n • productExponent i s)) h
  simp only [AddMonoidAlgebra.coeff_mul_single_add, mul_one] at hc
  have hn := polynomialToGroupAlgebra_nonnegative i p (a + n • productExponent i s)
    (hc ▸ ha) k
  simpa only [Pi.add_apply, Pi.smul_apply, productExponent_outside i s k hk,
    smul_zero, add_zero] using hn

@[simp] theorem groupAlgebraToLaurent_coefficient (i : ι) (d : ℤ)
    (p : chartGroupAlgebra (R := R) i) (a : Monomial ι d) :
    groupAlgebraToLaurent i d p a = p.coeff (fun j => a.val j) := by
  simp [groupAlgebraToLaurent, fullExponentEquiv]

theorem overlapLaurent_regular (i : ι) (d : ℤ) (s : Finset {j : ι // j ≠ i})
    (z : Localization.Away (chartProduct (R := R) i s)) :
    RegularOn ({i} ∪ (Subtype.val '' (s : Set {j : ι // j ≠ i})))
      (overlapLaurent i d s z) := by
  intro a ha k hk
  by_cases hki : k = i
  · exact Or.inl hki
  · apply Or.inr
    by_contra hks
    have hn : (⟨k, hki⟩ : {j : ι // j ≠ i}) ∉ s := by
      intro hm
      exact hks ⟨⟨k, hki⟩, hm, rfl⟩
    change groupAlgebraToLaurent i d (overlapToGroupAlgebra i s z) a ≠ 0 at ha
    rw [groupAlgebraToLaurent_coefficient] at ha
    exact not_lt_of_ge (overlapToGroupAlgebra_nonnegative i s z _ ha ⟨k, hki⟩ hn) hk

@[simp] theorem fullEncode_nat (i : ι) (d : ℤ) (b : ChartExponent i) :
    fullEncode i d (natExponentHom i b) = encode i d b := rfl

theorem groupAlgebraToLaurent_polynomial (i : ι) (d : ℤ)
    (p : MvPolynomial {j : ι // j ≠ i} R) :
    groupAlgebraToLaurent i d (polynomialToGroupAlgebra i p) = vertexLaurent i d p := by
  induction p using MvPolynomial.induction_on'
  case add a b ha hb =>
    simp only [map_add, ha, hb]
  case monomial b r =>
    rw [vertexLaurent_monomial]
    change groupAlgebraToLaurent i d
      (AddMonoidAlgebra.mapDomain _ (AddMonoidAlgebra.single b r)) = _
    rw [AddMonoidAlgebra.mapDomain_single]
    simp [groupAlgebraToLaurent, fullExponentEquiv]

@[simp] theorem overlapLaurent_base (i : ι) (d : ℤ) (s : Finset {j : ι // j ≠ i})
    (p : MvPolynomial {j : ι // j ≠ i} R) :
    overlapLaurent i d s (algebraMap _ _ p) = vertexLaurent i d p := by
  change groupAlgebraToLaurent i d (overlapToGroupAlgebra i s (algebraMap _ _ p)) = _
  rw [overlapToGroupAlgebra_base, groupAlgebraToLaurent_polynomial]

end

section
variable {ι R : Type*} [Fintype ι] [CommRing R]
end

attribute [local instance] Classical.propDecidable
open scoped BigOperators
open PiExponent.ProjectiveMonomialCech
variable {ι R : Type*} [Fintype ι] [CommRing R]

omit [Fintype ι] in
@[simp] theorem productExponent_inside (i : ι) (s : Finset {j : ι // j ≠ i})
    (k : {j : ι // j ≠ i}) (hk : k ∈ s) : productExponent i s k = 1 := by
  classical
  simp [productExponent, Finset.sum_apply, natExponentHom, Finsupp.single_apply, hk]

theorem exists_cleared_exponent (i : ι) (s : Finset {j : ι // j ≠ i})
    (a : {j : ι // j ≠ i} → ℤ) (ha : ∀ k, k ∉ s → 0 ≤ a k) :
    ∃ (n : ℕ) (b : ChartExponent i), natExponentHom i b = a + n • productExponent i s := by
  classical
  let n : ℕ := ∑ j : {j : ι // j ≠ i}, (-a j).toNat
  have hnn : ∀ k, 0 ≤ a k + (n : ℤ) := by
    intro k
    have hn : (-a k).toNat ≤ n :=
      Finset.single_le_sum (fun j _ => Nat.zero_le ((-a j).toNat)) (Finset.mem_univ k)
    have hn' : ((-a k).toNat : ℤ) ≤ (n : ℤ) := by exact_mod_cast hn
    omega
  have hnonneg : ∀ k, 0 ≤ (a + n • productExponent i s) k := by
    intro k
    by_cases hk : k ∈ s
    · simpa [Pi.add_apply, Pi.smul_apply, nsmul_eq_mul, productExponent_inside i s k hk] using hnn k
    · simpa only [Pi.add_apply, Pi.smul_apply, productExponent_outside i s k hk,
        smul_zero, add_zero] using ha k hk
  refine ⟨n, Finsupp.equivFunOnFinite.symm (fun k => ((a + n • productExponent i s) k).toNat), ?_⟩
  funext k
  exact Int.toNat_of_nonneg (hnonneg k)

theorem groupAlgebra_single_in_overlap_range (i : ι) (s : Finset {j : ι // j ≠ i})
    (a : {j : ι // j ≠ i} → ℤ) (r : R) (ha : ∀ k, k ∉ s → 0 ≤ a k) :
    ∃ z : Localization.Away (chartProduct (R := R) i s),
      overlapToGroupAlgebra i s z = AddMonoidAlgebra.single a r := by
  classical
  obtain ⟨n, b, hb⟩ := exists_cleared_exponent i s a ha
  have hinv : polynomialToGroupAlgebra (R := R) i (chartProduct i s) *
      AddMonoidAlgebra.single (-productExponent i s) 1 = 1 := by
    rw [polynomialToGroupAlgebra_product, AddMonoidAlgebra.single_mul_single]
    simp only [add_neg_cancel, one_mul]
    rfl
  refine ⟨Localization.mk (MvPolynomial.monomial b r) ⟨(chartProduct i s)^n, n, rfl⟩, ?_⟩
  change Localization.awayLift (polynomialToGroupAlgebra i) (chartProduct i s)
    (isUnit_iff_exists_inv.mpr ⟨_, hinv⟩) _ = _
  rw [Localization.awayLift_mk (polynomialToGroupAlgebra i) (chartProduct i s)
    (MvPolynomial.monomial b r) (AddMonoidAlgebra.single (-productExponent i s) 1) hinv n]
  change AddMonoidAlgebra.mapDomain _ (AddMonoidAlgebra.single b r) * _ = _
  rw [AddMonoidAlgebra.mapDomain_single, AddMonoidAlgebra.single_pow,
    AddMonoidAlgebra.single_mul_single, hb]
  simp

theorem laurent_single_in_overlap_range (i : ι) (d : ℤ)
    (s : Finset {j : ι // j ≠ i}) (a : Monomial ι d) (r : R)
    (ha : ∀ k : {j : ι // j ≠ i}, k ∉ s → 0 ≤ a.val k) :
    ∃ z : Localization.Away (chartProduct (R := R) i s),
      overlapLaurent i d s z = Finsupp.single a r := by
  obtain ⟨z, hz⟩ := groupAlgebra_single_in_overlap_range i s (fun j => a.val j) r ha
  refine ⟨z, ?_⟩
  change groupAlgebraToLaurent i d (overlapToGroupAlgebra i s z) = _
  rw [hz]
  change (Finsupp.domCongr (fullExponentEquiv i d))
    (Finsupp.single ((fullExponentEquiv i d).symm a) r) = _
  simp

theorem overlapLaurent_surjective_regular (i : ι) (d : ℤ)
    (s : Finset {j : ι // j ≠ i}) (p : Laurent ι R d)
    (hp : RegularOn ({i} ∪ (Subtype.val '' (s : Set {j : ι // j ≠ i}))) p) :
    ∃ z : Localization.Away (chartProduct (R := R) i s), overlapLaurent i d s z = p := by
  classical
  have hs : ∀ a ∈ p.support, ∃ z : Localization.Away (chartProduct (R := R) i s),
      overlapLaurent i d s z = Finsupp.single a (p a) := by
    intro a ha
    apply laurent_single_in_overlap_range
    intro k hk
    by_contra hn
    have hmem := hp a (Finsupp.mem_support_iff.mp ha) k (lt_of_not_ge hn)
    rcases hmem with hmem | ⟨j, hj, heq⟩
    · exact k.property hmem
    · exact hk ((Subtype.ext heq) ▸ hj)
  choose z hz using hs
  refine ⟨∑ a ∈ p.support, if h : a ∈ p.support then z a h else 0, ?_⟩
  rw [map_sum]
  calc
    _ = ∑ a ∈ p.support, Finsupp.single a (p a) := by
      apply Finset.sum_congr rfl
      intro a ha
      simp only [dite_eq_left ha, hz]
    _ = p := p.sum_single
end PiExponent.GeometrySupport.ProjectiveLaurentVertex

end

end OAI
end Source0409

-- Source: OAI/NumberTheory/PiExponent/Geometry/ProjectiveChartSections.lean
section Source0410
-- Modified in this edition: unused plain lemmas removed; see reduction.json.
/-
Modification notice for the LogTwo project.
Derived from openai/math (Apache-2.0), revision adc7f1241b42e322a6451854ab7e4b4c146bf78a.
Original source: lean/OAI/NumberTheory/PiExponent/Geometry/ProjectiveChartSections.lean
Changes: Convert module/import declarations to the Lean 4.34 public module format.
Expose private helpers and adjust helper names where needed for module compatibility.
See ../THIRD_PARTY_NOTICES.txt for provenance and the recorded changes.
-/

namespace OAI

noncomputable section

namespace PiExponentSeshadri.ProjectiveChartSections

open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite
open PiExponentSeshadri.Geometry ModuleFlasque RestrictionCohomology
abbrev schemeFreeOpen (X : Scheme) (U : X.Opens) : X.Modules :=
  freeOpen X.ringCatSheaf U

variable {X : Scheme} (U : X.Opens) (M : X.Modules)

def framedSectionsEquiv (e : M.restrict U.ι ≅ structureSheaf U.toScheme) :
    Γ(M,U) ≃+ Γ(U.toScheme,⊤) :=
  (restrictionSectionsIso U M).addCommGroupIsoToAddEquiv.symm.trans
    { toFun := fun x => e.hom.val.app (op ⊤) x
      invFun := fun x => e.inv.val.app (op ⊤) x
      left_inv := fun x => by
        have h := congrArg (fun f => f.val.app (op ⊤) x) e.hom_inv_id
        exact h
      right_inv := fun x => by
        have h := congrArg (fun f => f.val.app (op ⊤) x) e.inv_hom_id
        exact h
      map_add' := fun x y => map_add _ _ _ }

def framedCoefficientsEquiv (e : M.restrict U.ι ≅ structureSheaf U.toScheme) :
    Γ(M,U) ≃+ Γ(X,U) :=
  (framedSectionsEquiv U M e).trans U.topIso.commRingCatIsoToRingEquiv.toAddEquiv

def freeOpenAddEquiv : (schemeFreeOpen X U ⟶ M) ≃+ Γ(M,U) :=
  { freeOpenEquiv X.ringCatSheaf M U with
    map_add' := fun f g => by rfl }

def framedHomCoefficientsEquiv (e : M.restrict U.ι ≅ structureSheaf U.toScheme) :
    (schemeFreeOpen X U ⟶ M) ≃+ Γ(X,U) :=
  (freeOpenAddEquiv U M).trans (framedCoefficientsEquiv U M e)

def framedHomRingEquiv {A : Type*} [CommRing A]
    (e : M.restrict U.ι ≅ structureSheaf U.toScheme) (r : Γ(X,U) ≃+* A) :
    (schemeFreeOpen X U ⟶ M) ≃+ A :=
  (framedHomCoefficientsEquiv U M e).trans r.toAddEquiv

open PiExponent.ProjectiveMonomialCech
open PiExponent.GeometrySupport.ProjectiveLaurentVertex
variable {R ι : Type} [CommRing R] [Fintype ι] (i : ι) (d : ℤ)

def framedLaurentVertex (e : M.restrict U.ι ≅ structureSheaf U.toScheme)
    (r : Γ(X,U) ≃+* MvPolynomial {j : ι // j ≠ i} R) :
    (schemeFreeOpen X U ⟶ M) →+ Laurent ι R d :=
  (vertexLaurent i d).toAddMonoidHom.comp (framedHomRingEquiv U M e r).toAddMonoidHom

def powerHomRingEquiv {A : Type*} [CommRing A]
    (e : M.restrict U.ι ≅ structureSheaf U.toScheme) (r : Γ(X,U) ≃+* A) (n : ℕ) :
    (schemeFreeOpen X U ⟶ modulePow X M n) ≃+ A :=
  framedHomRingEquiv U (modulePow X M n) (modulePowFrame U e n) r

def framedLaurentOverlap (s : Finset {j : ι // j ≠ i})
    (e : M.restrict U.ι ≅ structureSheaf U.toScheme)
    (r : Γ(X,U) ≃+* Localization.Away (chartProduct (R := R) i s)) :
    (schemeFreeOpen X U ⟶ M) →+ Laurent ι R d :=
  (overlapLaurent i d s).comp (framedHomRingEquiv U M e r).toAddMonoidHom

theorem framedLaurentOverlap_injective (s : Finset {j : ι // j ≠ i})
    (e : M.restrict U.ι ≅ structureSheaf U.toScheme)
    (r : Γ(X,U) ≃+* Localization.Away (chartProduct (R := R) i s)) :
    Function.Injective (framedLaurentOverlap U M i d s e r) :=
  (overlapLaurent_injective i d s).comp (framedHomRingEquiv U M e r).injective

theorem framedLaurentOverlap_regular (s : Finset {j : ι // j ≠ i})
    (e : M.restrict U.ι ≅ structureSheaf U.toScheme)
    (r : Γ(X,U) ≃+* Localization.Away (chartProduct (R := R) i s))
    (b : schemeFreeOpen X U ⟶ M) :
    RegularOn ({i} ∪ (Subtype.val '' (s : Set {j : ι // j ≠ i})))
      (framedLaurentOverlap U M i d s e r b) :=
  overlapLaurent_regular i d s _

theorem framedLaurentOverlap_surjective_regular (s : Finset {j : ι // j ≠ i})
    (e : M.restrict U.ι ≅ structureSheaf U.toScheme)
    (r : Γ(X,U) ≃+* Localization.Away (chartProduct (R := R) i s))
    (p : Laurent ι R d)
    (hp : RegularOn ({i} ∪ (Subtype.val '' (s : Set {j : ι // j ≠ i}))) p) :
    ∃ b : schemeFreeOpen X U ⟶ M,
      framedLaurentOverlap U M i d s e r b = p := by
  obtain ⟨a, ha⟩ := overlapLaurent_surjective_regular i d s p hp
  refine ⟨(framedHomRingEquiv U M e r).symm a, ?_⟩
  change overlapLaurent i d s ((framedHomRingEquiv U M e r)
    ((framedHomRingEquiv U M e r).symm a)) = p
  rw [AddEquiv.apply_symm_apply, ha]

end PiExponentSeshadri.ProjectiveChartSections

end

end OAI
end Source0410

-- Source: OAI/NumberTheory/PiExponent/Geometry/ProjectiveCoordinateSections.lean
section Source0411
-- Modified in this edition: unused plain lemmas removed; see reduction.json.
/-
Modification notice for the LogTwo project.
Derived from openai/math (Apache-2.0), revision adc7f1241b42e322a6451854ab7e4b4c146bf78a.
Original source: lean/OAI/NumberTheory/PiExponent/Geometry/ProjectiveCoordinateSections.lean
Changes: Convert module/import declarations to the Lean 4.34 public module format.
Expose private helpers and adjust helper names where needed for module compatibility.
See ../THIRD_PARTY_NOTICES.txt for provenance and the recorded changes.
-/

namespace OAI

namespace PiExponentSeshadri.Projective
noncomputable section
open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite MvPolynomial
open PiExponentSeshadri.Frames PiExponentSeshadri.Geometry ModuleFlasque ProjectiveChartSections
open PiExponent.ProjectiveMonomialCech
open PiExponent.GeometrySupport.ProjectiveLaurentVertex
attribute [local instance] MvPolynomial.gradedAlgebra

def schemeIsoGammaEquiv {Y : Scheme} {A : CommRingCat} (g : Y ≅ Spec A) :
    Γ(Y,⊤) ≃+* A :=
  (Scheme.Γ.mapIso g.symm.op ≪≫ Scheme.ΓSpecIso A).commRingCatIsoToRingEquiv

@[simp] lemma schemeIsoGammaEquiv_symm_apply {Y : Scheme} {A : CommRingCat}
    (g : Y ≅ Spec A) (a : A) :
    (schemeIsoGammaEquiv g).symm a = ((Scheme.ΓSpecIso A).inv ≫ g.hom.appTop).hom a := rfl

abbrev schemeFreeOpen (X : Scheme) (U : X.Opens) : X.Modules :=
  freeOpen X.ringCatSheaf U

variable {X : Scheme} {K σ : Type} [CommRing K]
variable (M : X.Modules) (k : K →+* Γ(X,⊤))
variable (s : σ → (O X ⟶ M)) (hc : (⨆ i, SectionOpens.isoOpen (s i)) = ⊤)
variable (f : X ≅ Proj (PolyGrade K σ)) (hf : sectionsMorphism k s hc = f.hom)
include hf

lemma sectionOpen_eq_coordinate_preimage (i : σ) :
    SectionOpens.isoOpen (s i) = f.hom ⁻¹ᵁ Proj.basicOpen (PolyGrade K σ) (MvPolynomial.X i) := by
  rw [← hf]
  exact (sectionsMorphism_preimage k s hc i).symm

def coordinateSectionChartIso (i : σ) :
    (SectionOpens.isoOpen (s i)).toScheme ≅ Spec (CommRingCat.of (PolyChart (R := K) i)) :=
  X.isoOfEq (sectionOpen_eq_coordinate_preimage M k s hc f hf i) ≪≫
    f.hom.preimageIso (Proj.basicOpen (PolyGrade K σ) (MvPolynomial.X i)) ≪≫
      Proj.basicOpenIsoSpec (PolyGrade K σ) (MvPolynomial.X i) (poly_X_mem i) (by decide)

lemma coordinateSectionChartIso_hom_away (i : σ) :
    (coordinateSectionChartIso M k s hc f hf i).hom ≫
      Proj.awayι (PolyGrade K σ) (MvPolynomial.X i) (poly_X_mem i) (by decide) =
    (SectionOpens.isoOpen (s i)).ι ≫ sectionsMorphism k s hc := by
  rw [hf]
  simp only [coordinateSectionChartIso, Iso.trans_hom, Category.assoc, Proj.awayι,
    Iso.hom_inv_id_assoc, Scheme.Hom.preimageIso_hom_ι, Scheme.isoOfEq_hom_ι_assoc]

def coordinateSectionRingEquiv (i : σ) :
    Γ(X,SectionOpens.isoOpen (s i)) ≃+* MvPolynomial (ChartVariables i) K :=
  (SectionOpens.isoOpen (s i)).topIso.commRingCatIsoToRingEquiv.symm.trans
    ((schemeIsoGammaEquiv (coordinateSectionChartIso M k s hc f hf i)).trans
      (polynomialChartEquiv i))

lemma coordinateSectionRingEquiv_coordinate (i j : σ) :
    coordinateSectionRingEquiv M k s hc f hf i
      ((SectionOpens.isoOpen (s i)).topIso.hom
        (coefficient (sectionFrame (s i))
          (restrictSection (SectionOpens.isoOpen (s i)).ι (s j)))) =
      chartToPoly (R := K) i (chartCoordinate i j) := by
  have h := sectionFrame_coordinate i k s hc
    (coordinateSectionChartIso M k s hc f hf i).hom
    (coordinateSectionChartIso_hom_away M k s hc f hf i).symm j
  change coefficient (sectionFrame (s i))
      (restrictSection (SectionOpens.isoOpen (s i)).ι (s j)) =
    (schemeIsoGammaEquiv (coordinateSectionChartIso M k s hc f hf i)).symm
      (chartCoordinate i j) at h
  simp only [coordinateSectionRingEquiv, RingEquiv.trans_apply, h]
  change (polynomialChartEquiv i)
    ((schemeIsoGammaEquiv (coordinateSectionChartIso M k s hc f hf i))
      ((SectionOpens.isoOpen (s i)).topIso.inv
        ((SectionOpens.isoOpen (s i)).topIso.hom
          ((schemeIsoGammaEquiv (coordinateSectionChartIso M k s hc f hf i)).symm
            (chartCoordinate i j))))) = _
  rw [Iso.hom_inv_id_apply, RingEquiv.apply_symm_apply]
  rfl

variable [Fintype σ]

def coordinatePowerVertex (n : ℕ) (i : σ) :
    (schemeFreeOpen X (SectionOpens.isoOpen (s i)) ⟶ modulePow X M n) →+
      Laurent σ K n :=
  framedLaurentVertex _ (modulePow X M n) i n
    (coordinatePowerFrame (s i) n)
    (coordinateSectionRingEquiv M k s hc f hf i)

end
end PiExponentSeshadri.Projective

end OAI
end Source0411

-- Source: OAI/NumberTheory/PiExponent/Geometry/ProjectiveCoordinateFiniteSections.lean
section Source0412
/-
Modification notice for the LogTwo project.
Derived from openai/math (Apache-2.0), revision adc7f1241b42e322a6451854ab7e4b4c146bf78a.
Original source: lean/OAI/NumberTheory/PiExponent/Geometry/ProjectiveCoordinateFiniteSections.lean
Changes: Convert module/import declarations to the Lean 4.34 public module format.
Expose private helpers and adjust helper names where needed for module compatibility.
See ../THIRD_PARTY_NOTICES.txt for provenance and the recorded changes.
-/

namespace OAI

namespace PiExponentSeshadri.Projective
noncomputable section
open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite
open PiExponentSeshadri.Frames PiExponentSeshadri.Geometry ModuleFlasque ProjectiveChartSections
open PiExponent.ProjectiveMonomialCech
open PiExponent.GeometrySupport.ProjectiveLaurentVertex
attribute [local instance] Classical.propDecidable
attribute [local instance] MvPolynomial.gradedAlgebra

def isoPreimageSectionRingEquiv {X Y : Scheme} (f : X ≅ Y) (V : Y.Opens) :
    Γ(X,f.hom ⁻¹ᵁ V) ≃+* Γ(Y,V) :=
  ((IsOpenImmersion.ΓIso f.hom V) ≪≫
    Y.presheaf.mapIso (eqToIso (show V = f.hom.opensRange ⊓ V by rw [Scheme.Hom.opensRange_of_isIso, top_inf_eq])).op).commRingCatIsoToRingEquiv

abbrev schemeFiniteFreeOpen (X : Scheme) (U : X.Opens) : X.Modules :=
  freeOpen X.ringCatSheaf U

variable {X : Scheme} {K σ : Type} [CommRing K]
variable (M : X.Modules) (s : σ → (O X ⟶ M))

def coordinateFiniteOpen (i : σ) (a : Finset (ChartVariables i)) : X.Opens :=
  SectionOpens.isoOpen (s i) ⊓ a.inf (fun j => SectionOpens.isoOpen (s j.val))

variable (k : K →+* Γ(X,⊤)) (hc : (⨆ i, SectionOpens.isoOpen (s i)) = ⊤)
variable (f : X ≅ Proj (PolyGrade K σ)) (hf : sectionsMorphism k s hc = f.hom)
include hf

lemma coordinateFiniteOpen_eq_preimage (i : σ) (a : Finset (ChartVariables i)) :
    coordinateFiniteOpen M s i a = f.hom ⁻¹ᵁ
      (Proj.basicOpen (PolyGrade K σ) (MvPolynomial.X i) ⊓
        a.inf (fun j => Proj.basicOpen (PolyGrade K σ) (MvPolynomial.X j.val))) := by
  classical
  unfold coordinateFiniteOpen
  rw [Scheme.Hom.preimage_inf, ← sectionOpen_eq_coordinate_preimage M k s hc f hf i]
  congr 1
  induction a using Finset.induction_on with
  | empty => simp
  | @insert j a hj ih =>
    rw [Finset.inf_insert, Finset.inf_insert, Scheme.Hom.preimage_inf,
      ← sectionOpen_eq_coordinate_preimage M k s hc f hf j.val, ih]

def coordinateFiniteRingEquiv (i : σ) (a : Finset (ChartVariables i)) :
    Γ(X,coordinateFiniteOpen M s i a) ≃+*
      Localization.Away (chartProduct (R := K) i a) :=
  (X.presheaf.mapIso (eqToIso
    (coordinateFiniteOpen_eq_preimage M s k hc f hf i a).symm).op).commRingCatIsoToRingEquiv.trans
      ((isoPreimageSectionRingEquiv f _).trans (chartVariableOverlapRingEquiv i a))

variable [Fintype σ]

def coordinatePowerOverlap (n : ℕ) (i : σ) (a : Finset (ChartVariables i)) :
    (schemeFiniteFreeOpen X (coordinateFiniteOpen M s i a) ⟶ modulePow X M n) →+
      Laurent σ K n :=
  framedLaurentOverlap _ (modulePow X M n) i n a
    (restrictOpenFrame (show coordinateFiniteOpen M s i a ≤ SectionOpens.isoOpen (s i) from inf_le_left)
      (coordinatePowerFrame (s i) n))
    (coordinateFiniteRingEquiv M s k hc f hf i a)

lemma coordinatePowerOverlap_injective (n : ℕ) (i : σ) (a : Finset (ChartVariables i)) :
    Function.Injective (coordinatePowerOverlap M s k hc f hf n i a) :=
  framedLaurentOverlap_injective _ _ _ _ _ _ _

lemma coordinatePowerOverlap_regular (n : ℕ) (i : σ) (a : Finset (ChartVariables i))
    (b : schemeFiniteFreeOpen X (coordinateFiniteOpen M s i a) ⟶ modulePow X M n) :
    RegularOn ({i} ∪ (Subtype.val '' (a : Set (ChartVariables i))))
      (coordinatePowerOverlap M s k hc f hf n i a b) :=
  framedLaurentOverlap_regular _ _ _ _ _ _ _ b

lemma coordinatePowerOverlap_surjective_regular (n : ℕ) (i : σ) (a : Finset (ChartVariables i))
    (p : Laurent σ K n)
    (hp : RegularOn ({i} ∪ (Subtype.val '' (a : Set (ChartVariables i)))) p) :
    ∃ b, coordinatePowerOverlap M s k hc f hf n i a b = p :=
  framedLaurentOverlap_surjective_regular _ _ _ _ _ _ _ p hp

end
end PiExponentSeshadri.Projective

end OAI
end Source0412

-- Source: OAI/NumberTheory/PiExponent/Geometry/ProjectiveCoordinateRingNaturality.lean
section Source0413
/-
Modification notice for the LogTwo project.
Derived from openai/math (Apache-2.0), revision adc7f1241b42e322a6451854ab7e4b4c146bf78a.
Original source: lean/OAI/NumberTheory/PiExponent/Geometry/ProjectiveCoordinateRingNaturality.lean
Changes: Convert module/import declarations to the Lean 4.34 public module format.
See ../THIRD_PARTY_NOTICES.txt for provenance and the recorded changes.
-/

namespace OAI

namespace PiExponentSeshadri.Projective
noncomputable section
open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite
lemma isoPreimageSectionRingEquiv_symm (X Y : Scheme) (f : X ≅ Y) (V : Y.Opens)
    (a : Γ(Y,V)) :
    (isoPreimageSectionRingEquiv f V).symm a = f.hom.app V a := by
  change (((IsOpenImmersion.ΓIso f.hom V) ≪≫
    Y.presheaf.mapIso (eqToIso (show V = f.hom.opensRange ⊓ V by
      rw [Scheme.Hom.opensRange_of_isIso, top_inf_eq])).op).inv).hom a = _
  simp only [Iso.trans_inv, Functor.mapIso_inv, Iso.op_inv, eqToIso.inv,
    IsOpenImmersion.ΓIso_inv, Scheme.Hom.map_appLE, Scheme.Hom.appLE_eq_app]

lemma isoPreimageSectionRingEquiv_appLE {X Y : Scheme} (f : X ≅ Y)
    (V : Y.Opens) (U : X.Opens) (h : U = f.hom ⁻¹ᵁ V) (a : Γ(Y,V)) :
    (isoPreimageSectionRingEquiv f V)
      (X.presheaf.map (eqToHom h.symm).op (f.hom.appLE V U h.le a)) = a := by
  subst U
  simpa [Scheme.Hom.appLE_eq_app, isoPreimageSectionRingEquiv_symm] using
    (isoPreimageSectionRingEquiv f V).apply_symm_apply a

lemma appLE_restrict_comm {X Y : Scheme} (f : X ⟶ Y)
    {U V : Y.Opens} {U' V' : X.Opens} (h : V ≤ U) (h' : V' ≤ U')
    (eU : U' ≤ f ⁻¹ᵁ U) (eV : V' ≤ f ⁻¹ᵁ V) (x : Γ(Y,U)) :
    X.presheaf.map (homOfLE h').op (f.appLE U U' eU x) =
      f.appLE V V' eV (Y.presheaf.map (homOfLE h).op x) := by
  change (f.appLE U U' eU ≫ X.presheaf.map (homOfLE h').op) x =
    (Y.presheaf.map (homOfLE h).op ≫ f.appLE V V' eV) x
  simp only [Scheme.Hom.appLE_map, Scheme.Hom.map_appLE]

attribute [local instance] MvPolynomial.gradedAlgebra
variable {X : Scheme} {K σ : Type} [CommRing K]
variable (M : X.Modules) (k : K →+* Γ(X,⊤))
variable (s : σ → (PiExponentSeshadri.Frames.O X ⟶ M))
variable (hc : (⨆i,SectionOpens.isoOpen (s i))=⊤)
variable (f : X ≅ Proj (PolyGrade K σ)) (hf : sectionsMorphism k s hc=f.hom)
lemma coordinateSectionChartIso_factor (i : σ) :
    (coordinateSectionChartIso M k s hc f hf i).hom =
      f.hom.resLE (Proj.basicOpen (PolyGrade K σ) (MvPolynomial.X i))
        (SectionOpens.isoOpen (s i))
        (sectionOpen_eq_coordinate_preimage M k s hc f hf i).le ≫
      (Proj.basicOpenIsoSpec (PolyGrade K σ) (MvPolynomial.X i) (poly_X_mem i) (by decide)).hom := by
  apply (cancel_mono (Proj.awayι (PolyGrade K σ) (MvPolynomial.X i)
    (poly_X_mem i) (by decide))).1
  rw [coordinateSectionChartIso_hom_away, hf]
  simp only [Category.assoc, Proj.awayι, Iso.hom_inv_id_assoc,
    Scheme.Hom.resLE_comp_ι]
lemma coordinateSectionChartIso_pullback (i : σ) :
    (Scheme.ΓSpecIso (CommRingCat.of (PolyChart (R := K) i))).inv ≫
      (coordinateSectionChartIso M k s hc f hf i).hom.appTop ≫
        (SectionOpens.isoOpen (s i)).topIso.hom =
    Proj.awayToSection (PolyGrade K σ) (MvPolynomial.X i) ≫
      f.hom.appLE (Proj.basicOpen (PolyGrade K σ) (MvPolynomial.X i))
        (SectionOpens.isoOpen (s i))
        (sectionOpen_eq_coordinate_preimage M k s hc f hf i).le := by
  rw [coordinateSectionChartIso_factor, Scheme.Hom.comp_appTop]
  simp only [Proj.basicOpenIsoSpec_hom, Proj.basicOpenToSpec_app_top,
    Scheme.Hom.resLE_app_top, Category.assoc, Iso.inv_hom_id_assoc,
    Iso.inv_hom_id, Category.comp_id]

lemma coordinateSectionRingEquiv_symm (i : σ) (p : MvPolynomial (ChartVariables i) K) :
    (coordinateSectionRingEquiv M k s hc f hf i).symm p =
      f.hom.appLE (Proj.basicOpen (PolyGrade K σ) (MvPolynomial.X i))
        (SectionOpens.isoOpen (s i))
        (sectionOpen_eq_coordinate_preimage M k s hc f hf i).le
        (Proj.awayToSection (PolyGrade K σ) (MvPolynomial.X i) (polyToChart i p)) := by
  exact congrArg (fun g : CommRingCat.of (PolyChart (R := K) i) ⟶ _ =>
    g.hom (polyToChart i p)) (coordinateSectionChartIso_pullback M k s hc f hf i)

lemma coordinateFiniteRingEquiv_appLE (i : σ) (a : Finset (ChartVariables i))
    (x : Γ(Proj (PolyGrade K σ),
      Proj.basicOpen (PolyGrade K σ) (MvPolynomial.X i) ⊓
        a.inf (fun j => Proj.basicOpen (PolyGrade K σ) (MvPolynomial.X j.val)))) :
    coordinateFiniteRingEquiv M s k hc f hf i a
      (f.hom.appLE _ _ (coordinateFiniteOpen_eq_preimage M s k hc f hf i a).le x) =
      chartVariableOverlapRingEquiv i a x := by
  change chartVariableOverlapRingEquiv i a
    (isoPreimageSectionRingEquiv f _
      (X.presheaf.map (eqToHom (coordinateFiniteOpen_eq_preimage M s k hc f hf i a).symm).op
        (f.hom.appLE _ _ (coordinateFiniteOpen_eq_preimage M s k hc f hf i a).le x))) = _
  rw [isoPreimageSectionRingEquiv_appLE f _ _
    (coordinateFiniteOpen_eq_preimage M s k hc f hf i a)]

lemma coordinateFiniteRingEquiv_restrict (i : σ) (a : Finset (ChartVariables i))
    (p : MvPolynomial (ChartVariables i) K) :
    coordinateFiniteRingEquiv M s k hc f hf i a
      (X.presheaf.map (homOfLE (show coordinateFiniteOpen M s i a ≤
        SectionOpens.isoOpen (s i) from inf_le_left)).op
        ((coordinateSectionRingEquiv M k s hc f hf i).symm p)) =
      algebraMap _ _ p := by
  rw [coordinateSectionRingEquiv_symm]
  have h : X.presheaf.map (homOfLE (show coordinateFiniteOpen M s i a ≤
        SectionOpens.isoOpen (s i) from inf_le_left)).op
      (f.hom.appLE _ _ (sectionOpen_eq_coordinate_preimage M k s hc f hf i).le
        (Proj.awayToSection (PolyGrade K σ) (MvPolynomial.X i) (polyToChart i p))) =
      f.hom.appLE _ _ (coordinateFiniteOpen_eq_preimage M s k hc f hf i a).le
        ((Proj (PolyGrade K σ)).presheaf.map (homOfLE inf_le_left).op
          (Proj.awayToSection (PolyGrade K σ) (MvPolynomial.X i) (polyToChart i p))) := by
    exact appLE_restrict_comm f.hom inf_le_left inf_le_left _ _ _
  rw [h, coordinateFiniteRingEquiv_appLE, chartVariableOverlapRingEquiv_restrict]
  rfl

end

end Projective
end PiExponentSeshadri

end OAI
end Source0413

-- Source: OAI/NumberTheory/PiExponent/Geometry/ProjectiveFrameNaturality.lean
section Source0414
/-
Modification notice for the LogTwo project.
Derived from openai/math (Apache-2.0), revision adc7f1241b42e322a6451854ab7e4b4c146bf78a.
Original source: lean/OAI/NumberTheory/PiExponent/Geometry/ProjectiveFrameNaturality.lean
Changes: Convert module/import declarations to the Lean 4.34 public module format.
See ../THIRD_PARTY_NOTICES.txt for provenance and the recorded changes.
-/

namespace OAI

namespace PiExponentSeshadri.ProjectiveChartSections
noncomputable section
open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite
open PiExponentSeshadri.Geometry ModuleFlasque RestrictionCohomology Frames
variable {X : Scheme} {U V : X.Opens} (M : X.Modules)
lemma framedSectionsEquiv_restrict (h : V ≤ U)
    (e : M.restrict U.ι ≅ structureSheaf U.toScheme) (s : Γ(M,U)) :
    framedSectionsEquiv V M (restrictOpenFrame h e) (M.presheaf.map (homOfLE h).op s) =
      (X.homOfLE h).appTop (framedSectionsEquiv U M e s) := by
  change (restrictOpenFrame h e).hom.app ⊤
    ((restrictionSectionsIso V M).inv (M.presheaf.map (homOfLE h).op s)) =
    (X.homOfLE h).appTop (e.hom.app ⊤ ((restrictionSectionsIso U M).inv s))
  simp only [restrictOpenFrame, Iso.trans_hom, Iso.symm_hom,
    Scheme.Modules.Hom.comp_app, Iso.app_inv, Iso.app_hom,
    Scheme.Modules.restrictFunctorCongr_inv_app_app,
    Scheme.Modules.restrictFunctorComp_hom_app_app,
    restrictionSectionsIso,
    Scheme.Modules.restrictAppIso]
  let φ := X.homOfLE h
  let W := φ ''ᵁ (⊤ : V.toScheme.Opens)
  let y := (restrictionSectionsIso U M).inv s
  have hn : e.hom.app W ((M.restrict U.ι).presheaf.map (homOfLE (show W ≤ ⊤ from le_top)).op y) =
      U.toScheme.presheaf.map (homOfLE (show W ≤ ⊤ from le_top)).op (e.hom.app ⊤ y) :=
    CategoryTheory.congr_fun (e.hom.mapPresheaf.naturality (homOfLE (show W ≤ ⊤ from le_top)).op) y
  calc
    _ = (φ.appIso ⊤).hom (e.hom.app W
        ((M.restrict U.ι).presheaf.map (homOfLE (show W ≤ ⊤ from le_top)).op y)) := by
      change (φ.appIso ⊤).hom (e.hom.app W _) = _
      apply congrArg (φ.appIso ⊤).hom
      apply congrArg (e.hom.app W)
      change (M.presheaf.map _ ≫ M.presheaf.map _ ≫ M.presheaf.map _ ≫ M.presheaf.map _) s =
        (M.presheaf.map _ ≫ M.presheaf.map _) s
      simp only [← Functor.map_comp]
      congr 2
    _ = (φ.appIso ⊤).hom (U.toScheme.presheaf.map
        (homOfLE (show W ≤ ⊤ from le_top)).op (e.hom.app ⊤ y)) := congrArg _ hn
    _ = _ := by
      change (U.toScheme.presheaf.map _ ≫ (φ.appIso ⊤).hom) (e.hom.app ⊤ y) = _
      rw [Scheme.Hom.appIso_hom']
      simp only [φ, Scheme.Hom.appTop, Scheme.homOfLE_app, Scheme.homOfLE_appLE,
        Scheme.Opens.toScheme_presheaf_map]
      erw [← Functor.map_comp]
      congr 2

lemma topIso_hom_restrict (h : V ≤ U) (x : Γ(U.toScheme, ⊤)) :
    V.topIso.hom ((X.homOfLE h).appTop x) =
      X.presheaf.map (homOfLE h).op (U.topIso.hom x) := by
  simp only [Scheme.homOfLE_appTop, Scheme.Opens.topIso_hom]
  change (X.presheaf.map _ ≫ X.presheaf.map _) x =
    (X.presheaf.map _ ≫ X.presheaf.map _) x
  erw [← Functor.map_comp, ← Functor.map_comp]
  congr 2

lemma framedCoefficientsEquiv_restrict (h : V ≤ U)
    (e : M.restrict U.ι ≅ structureSheaf U.toScheme) (s : Γ(M,U)) :
    framedCoefficientsEquiv V M (restrictOpenFrame h e)
      (M.presheaf.map (homOfLE h).op s) =
      X.presheaf.map (homOfLE h).op (framedCoefficientsEquiv U M e s) := by
  change V.topIso.hom (framedSectionsEquiv V M (restrictOpenFrame h e)
    (M.presheaf.map (homOfLE h).op s)) =
    X.presheaf.map (homOfLE h).op (U.topIso.hom (framedSectionsEquiv U M e s))
  erw [framedSectionsEquiv_restrict, topIso_hom_restrict]

lemma framedHomCoefficientsEquiv_restrict (h : V ≤ U)
    (e : M.restrict U.ι ≅ structureSheaf U.toScheme)
    (b : freeOpen X.ringCatSheaf U ⟶ M) :
    framedHomCoefficientsEquiv V M (restrictOpenFrame h e)
      (freeOpenMap X.ringCatSheaf (homOfLE h) ≫ b) =
      X.presheaf.map (homOfLE h).op (framedHomCoefficientsEquiv U M e b) := by
  change framedCoefficientsEquiv V M (restrictOpenFrame h e)
    (freeOpenEquiv X.ringCatSheaf M V
      (freeOpenMap X.ringCatSheaf (homOfLE h) ≫ b)) =
    X.presheaf.map (homOfLE h).op
      (framedCoefficientsEquiv U M e (freeOpenEquiv X.ringCatSheaf M U b))
  erw [freeOpenEquiv_naturality]
  exact framedCoefficientsEquiv_restrict M h e _

end
end PiExponentSeshadri.ProjectiveChartSections

end OAI
end Source0414

-- Source: OAI/NumberTheory/PiExponent/Geometry/ProjectiveCoordinateConstants.lean
section Source0415
/-
Modification notice for the LogTwo project.
Derived from openai/math (Apache-2.0), revision adc7f1241b42e322a6451854ab7e4b4c146bf78a.
Original source: lean/OAI/NumberTheory/PiExponent/Geometry/ProjectiveCoordinateConstants.lean
Changes: Convert module/import declarations to the Lean 4.34 public module format.
See ../THIRD_PARTY_NOTICES.txt for provenance and the recorded changes.
-/

namespace OAI

namespace PiExponentSeshadri.Projective
noncomputable section
open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite MvPolynomial
attribute [local instance] MvPolynomial.gradedAlgebra
variable {K σ : Type} [CommRing K] (i : σ)
lemma evalAway_constants {R : Type} [CommRing R]
    (k : K →+* R) (a : σ → R) (hi : a i = 1) (r : K) :
    evalAway (eval₂Hom k a) (MvPolynomial.X i)
      (by simpa only [eval₂Hom_X', hi] using (isUnit_one : IsUnit (1 : R)))
      (chartConstants i r) = k r := by
  have h := evalAway_mk_clear (eval₂Hom k a) (poly_X_mem (R := K) i)
    (by simpa only [eval₂Hom_X', hi] using (isUnit_one : IsUnit (1 : R)))
    0 (C r) (by simp)
  have he : chartConstants (R := K) i r = HomogeneousLocalization.Away.mk
      (PolyGrade K σ) (poly_X_mem i) 0 (C r) (by simp) := by
    apply HomogeneousLocalization.val_injective _
    simp [chartConstants, HomogeneousLocalization.fromZeroRingHom,
      HomogeneousLocalization.Away.val_mk]
    rfl
  rw [he]
  simpa only [pow_zero, mul_one, eval₂Hom_C] using h
lemma coordinatesMap_pullback_constant {Y : Scheme}
    (k : K →+* Γ(Y,⊤)) (a : σ → Γ(Y,⊤)) (hi : a i = 1)
    (g : Y ⟶ Spec (CommRingCat.of (PolyChart (R := K) i)))
    (heq : coordinatesMap Y k a i hi =
      g ≫ Proj.awayι (PolyGrade K σ) (MvPolynomial.X i) (poly_X_mem i) (by decide))
    (r : K) :
    k r = ((Scheme.ΓSpecIso (CommRingCat.of (PolyChart (R := K) i))).inv ≫
      g.appTop).hom (chartConstants i r) := by
  let F := evalAway (𝒜 := PolyGrade K σ) (eval₂Hom k a) (MvPolynomial.X i)
    (by simpa only [eval₂Hom_X', hi] using (isUnit_one : IsUnit (1 : Γ(Y,⊤))))
  have hfactor : Y.toSpecΓ ≫ Spec.map (CommRingCat.ofHom F) = g := by
    apply (cancel_mono (Proj.awayι (PolyGrade K σ) (MvPolynomial.X i) (poly_X_mem i) (by decide))).1
    simpa only [coordinatesMap, fromUnitCoordinate, Category.assoc] using heq
  have hf := congrArg (fun g => (Scheme.ΓSpecIso (CommRingCat.of (PolyChart (R := K) i))).inv ≫
    Scheme.Hom.appTop g) hfactor
  simp only [Scheme.Hom.comp_appTop, Scheme.toSpecΓ_appTop,
    ← Scheme.ΓSpecIso_inv_naturality_assoc, Iso.inv_hom_id, Category.comp_id] at hf
  have h := congrArg (fun g : CommRingCat.of (PolyChart (R := K) i) ⟶ _ =>
    g.hom (chartConstants i r)) hf
  change F (chartConstants i r) = _ at h
  rw [evalAway_constants i k a hi r] at h
  exact h
variable {X : Scheme} (M : X.Modules) (k : K →+* Γ(X,⊤))
    (s : σ → (PiExponentSeshadri.Frames.O X ⟶ M))
    (hc : (⨆i,SectionOpens.isoOpen (s i))=⊤)
    (f : X ≅ Proj (PolyGrade K σ)) (hf : sectionsMorphism k s hc=f.hom)

lemma coordinateSectionRingEquiv_symm_constant (r : K) :
    (coordinateSectionRingEquiv M k s hc f hf i).symm (C r) =
      X.presheaf.map (homOfLE (show SectionOpens.isoOpen (s i) ≤ ⊤ from le_top)).op (k r) := by
  let U := SectionOpens.isoOpen (s i)
  let g := coordinateSectionChartIso M k s hc f hf i
  have h := coordinatesMap_pullback_constant i (U.ι.appTop.hom.comp k)
    (fun j => PiExponentSeshadri.Frames.coefficient (sectionFrame (s i))
      (PiExponentSeshadri.Frames.restrictSection U.ι (s j)))
    (sectionFrame_normalized (s i)) g.hom
    ((sectionsMorphism_local k s hc i).symm.trans
      (coordinateSectionChartIso_hom_away M k s hc f hf i).symm) r
  have hp : (polynomialChartEquiv (R := K) i).symm (C r) = chartConstants i r := by
    apply (polynomialChartEquiv i).injective
    rw [RingEquiv.apply_symm_apply]
    exact (chartToPoly_constants i r).symm
  change U.topIso.hom ((schemeIsoGammaEquiv g).symm
    ((polynomialChartEquiv i).symm (C r))) = _
  rw [hp]
  change U.ι.appTop (k r) = (schemeIsoGammaEquiv g).symm (chartConstants i r) at h
  rw [← h]
  simp only [Scheme.Opens.ι_appTop, Scheme.Opens.topIso_hom]
  change (X.presheaf.map _ ≫ X.presheaf.map _) (k r) = _
  erw [← Functor.map_comp]
  rfl

lemma coordinateSectionRingEquiv_constant (r : K) :
    coordinateSectionRingEquiv M k s hc f hf i
      (X.presheaf.map (homOfLE (show SectionOpens.isoOpen (s i) ≤ ⊤ from le_top)).op (k r)) = C r := by
  rw [← coordinateSectionRingEquiv_symm_constant i M k s hc f hf r,
    RingEquiv.apply_symm_apply]

end

end Projective
end PiExponentSeshadri

end OAI
end Source0415

-- Source: OAI/NumberTheory/PiExponent/Geometry/LineBundleGluing.lean
section Source0416
-- Modified in this edition: unused plain lemmas removed; see reduction.json.
/-
Modification notice for the LogTwo project.
Derived from openai/math (Apache-2.0), revision adc7f1241b42e322a6451854ab7e4b4c146bf78a.
Original source: lean/OAI/NumberTheory/PiExponent/Geometry/LineBundleGluing.lean
Changes: Convert module/import declarations to the Lean 4.34 public module format.
See ../THIRD_PARTY_NOTICES.txt for provenance and the recorded changes.
-/

namespace OAI

noncomputable section

namespace PiExponentSeshadri.LineBundleGluing

section
open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite
open PiExponentSeshadri.Geometry

variable {X : Scheme} {ι : Type} (U : ι → X.Opens)

structure Cocycle where
  transition (i j : ι) (W : X.Opens) (hi : W ≤ U i) (hj : W ≤ U j) : Γ(X,W)ˣ
  restriction (i j : ι) {V W : X.Opens} (h : V ≤ W) (hi : W ≤ U i) (hj : W ≤ U j) :
    X.presheaf.map (homOfLE h).op (transition i j W hi hj : Γ(X,W)) =
      (transition i j V (h.trans hi) (h.trans hj) : Γ(X,V))
  identity (i : ι) (W : X.Opens) (hi : W ≤ U i) :
    transition i i W hi hi = 1
  cocycle (i j k : ι) (W : X.Opens) (hi : W ≤ U i) (hj : W ≤ U j) (hk : W ≤ U k) :
    transition i j W hi hj * transition j k W hj hk = transition i k W hi hk

def LocalIndex (V : X.Opens) := Σ i : ι, {W : X.Opens // W ≤ V ∧ W ≤ U i}

abbrev Family (V : X.Opens) := ∀ p : LocalIndex U V, Γ(X,p.2.val)

@[instance_reducible]
def localModule (V : X.Opens) (p : LocalIndex U V) :
    Module Γ(X,V) Γ(X,p.2.val) :=
  Module.compHom _ (X.presheaf.map (homOfLE p.2.property.1).op).hom

instance familyModule (V : X.Opens) : Module Γ(X,V) (Family U V) := by
  letI (p : LocalIndex U V) : Module Γ(X,V) Γ(X,p.2.val) := localModule U V p
  exact Pi.module _ _ _

variable {U} (c : Cocycle U)

def sections (V : X.Opens) : Submodule Γ(X,V) (Family U V) where
  carrier := {s | (∀ (i : ι) (W W' : X.Opens) (hW : W ≤ V) (hi : W ≤ U i)
    (h : W' ≤ W), X.presheaf.map (homOfLE h).op (s ⟨i,W,hW,hi⟩) =
      s ⟨i,W',h.trans hW,h.trans hi⟩) ∧
    (∀ (i j : ι) (W : X.Opens) (hW : W ≤ V) (hi : W ≤ U i) (hj : W ≤ U j),
      s ⟨i,W,hW,hi⟩ = (c.transition i j W hi hj : Γ(X,W)) * s ⟨j,W,hW,hj⟩)}
  zero_mem' := by
    constructor
    · intro i W W' hW hi h
      change X.presheaf.map (homOfLE h).op (0 : Γ(X, W)) = 0
      exact map_zero _
    · intro i j W hW hi hj
      change (0 : Γ(X, W)) = (c.transition i j W hi hj : Γ(X, W)) * 0
      simp only [mul_zero]
  add_mem' := by
    intro a b ha hb
    constructor
    · intro i W W' hW hi h
      change X.presheaf.map (homOfLE h).op (a ⟨i,W,hW,hi⟩ + b ⟨i,W,hW,hi⟩) = _
      rw [map_add, ha.1 i W W' hW hi h, hb.1 i W W' hW hi h]
      rfl
    · intro i j W hW hi hj
      change a ⟨i,W,hW,hi⟩ + b ⟨i,W,hW,hi⟩ = _
      rw [ha.2 i j W hW hi hj, hb.2 i j W hW hi hj, ← mul_add]
      rfl
  smul_mem' := by
    intro a s hs
    constructor
    · intro i W W' hW hi h
      change X.presheaf.map (homOfLE h).op
        (X.presheaf.map (homOfLE hW).op a * s ⟨i,W,hW,hi⟩) =
        X.presheaf.map (homOfLE (h.trans hW)).op a * s ⟨i,W',h.trans hW,h.trans hi⟩
      rw [map_mul, hs.1 i W W' hW hi h]
      congr 1
      change (X.presheaf.map _ ≫ X.presheaf.map _) a = _
      rw [← Functor.map_comp]
      rfl
    · intro i j W hW hi hj
      change X.presheaf.map (homOfLE hW).op a * s ⟨i,W,hW,hi⟩ =
        (c.transition i j W hi hj : Γ(X,W)) *
          (X.presheaf.map (homOfLE hW).op a * s ⟨j,W,hW,hj⟩)
      rw [hs.2 i j W hW hi hj]
      ring

def restrict {V W : X.Opens} (h : V ≤ W) : sections c W →+ sections c V where
  toFun s := ⟨fun p => s.val ⟨p.1,p.2.val,p.2.property.1.trans h,p.2.property.2⟩,
    ⟨fun i A B hA hi hBA => s.property.1 i A B (hA.trans h) hi hBA,
     fun i j A hA hi hj => s.property.2 i j A (hA.trans h) hi hj⟩⟩
  map_zero' := rfl
  map_add' _ _ := rfl

lemma restrict_smul {V W : X.Opens} (h : V ≤ W) (a : Γ(X,W)) (s : sections c W) :
    restrict c h (a • s) = X.presheaf.map (homOfLE h).op a • restrict c h s := by
  apply Subtype.ext
  funext p
  change X.presheaf.map (homOfLE (p.2.property.1.trans h)).op a * _ =
    X.presheaf.map (homOfLE p.2.property.1).op
      (X.presheaf.map (homOfLE h).op a) * _
  congr 1
  change _ = (X.presheaf.map _ ≫ X.presheaf.map _) a
  rw [← Functor.map_comp]
  rfl

def presheaf : PresheafOfModules X.ringCatSheaf.obj where
  obj V := ModuleCat.of Γ(X, V.unop) (sections c V.unop)
  map {V W} f := ModuleCat.ofHom
    (Y := (ModuleCat.restrictScalars (X.presheaf.map f).hom).obj
      (ModuleCat.of Γ(X, W.unop) (sections c W.unop)))
    { toFun := restrict c (leOfHom f.unop)
      map_add' := fun a b => (restrict c (leOfHom f.unop)).map_add a b
      map_smul' := fun a s => restrict_smul c _ a s }
  map_id V := by ext; rfl
  map_comp f g := by ext; rfl

def fromChart {V : X.Opens} (i : ι) (hi : V ≤ U i) (a : Γ(X,V)) : sections c V :=
  ⟨fun p => (c.transition p.1 i p.2.val p.2.property.2 (p.2.property.1.trans hi) :
      Γ(X,p.2.val)) * X.presheaf.map (homOfLE p.2.property.1).op a,
    by
      constructor
      · intro j W W' hW hj h
        change X.presheaf.map (homOfLE h).op
          ((c.transition j i W hj (hW.trans hi) : Γ(X,W)) *
            X.presheaf.map (homOfLE hW).op a) = _
        rw [map_mul, c.restriction]
        congr 1
        change (X.presheaf.map _ ≫ X.presheaf.map _) a = _
        rw [← Functor.map_comp]
        rfl
      · intro j k W hW hj hk
        change (c.transition j i W hj (hW.trans hi) : Γ(X,W)) *
            X.presheaf.map (homOfLE hW).op a =
          (c.transition j k W hj hk : Γ(X,W)) *
            ((c.transition k i W hk (hW.trans hi) : Γ(X,W)) *
              X.presheaf.map (homOfLE hW).op a)
        rw [← mul_assoc, ← Units.val_mul, c.cocycle]⟩

def chartEquiv {V : X.Opens} (i : ι) (hi : V ≤ U i) :
    sections c V ≃ₗ[Γ(X,V)] Γ(X,V) where
  toFun s := s.val ⟨i,V,le_rfl,hi⟩
  invFun := fromChart c i hi
  left_inv s := by
    apply Subtype.ext
    funext p
    change (c.transition p.1 i p.2.val p.2.property.2 (p.2.property.1.trans hi) :
      Γ(X,p.2.val)) * X.presheaf.map (homOfLE p.2.property.1).op
        (s.val ⟨i,V,le_rfl,hi⟩) = s.val p
    rw [s.property.1 i V p.2.val le_rfl hi p.2.property.1]
    exact (s.property.2 p.1 i p.2.val p.2.property.1 p.2.property.2
      (p.2.property.1.trans hi)).symm
  right_inv a := by
    change (c.transition i i V hi hi : Γ(X,V)) *
      X.presheaf.map (homOfLE (show V ≤ V from le_rfl)).op a = a
    rw [c.identity]
    simp
  map_add' _ _ := rfl
  map_smul' a s := by
    change X.presheaf.map (homOfLE (show V ≤ V from le_rfl)).op a * _ = a * _
    simp

lemma chartEquiv_restrict {V W : X.Opens} (h : V ≤ W) (i : ι) (hi : W ≤ U i)
    (s : sections c W) :
    chartEquiv c i (h.trans hi) (restrict c h s) =
      X.presheaf.map (homOfLE h).op (chartEquiv c i hi s) :=
  (s.property.1 i W V le_rfl hi h).symm

def openPresheafFrame (i : ι) (W : X.Opens) (hW : W ≤ U i) :
    (modulePresheafRestrict W.ι).obj (presheaf c) ≅
      (SheafOfModules.unit W.toScheme.ringCatSheaf).val :=
  (modulePresheafRestrictOpensIso W).app _ ≪≫
    PresheafOfModules.isoMk
      (fun V => (chartEquiv c i ((W.ι_image_le V.unop).trans hW)).toModuleIso)
      (fun {V V'} f => by
        ext s
        exact chartEquiv_restrict c
          (Scheme.Hom.image_mono W.ι (leOfHom f.unop)) i
          ((W.ι_image_le V.unop).trans hW) s)

def chartPresheafFrame (i : ι) :
    (modulePresheafRestrict (U i).ι).obj (presheaf c) ≅
      (SheafOfModules.unit (U i).toScheme.ringCatSheaf).val :=
  openPresheafFrame c i (U i) le_rfl

def sheaf : X.Modules :=
  (PresheafOfModules.sheafification (𝟙 X.ringCatSheaf.obj)).obj (presheaf c)

def openFrame (i : ι) (W : X.Opens) (hW : W ≤ U i) :
    (sheaf c).restrict W.ι ≅ SheafOfModules.unit W.toScheme.ringCatSheaf :=
  (moduleSheafificationRestrict W.ι).app (presheaf c) ≪≫
    (PresheafOfModules.sheafification (𝟙 W.toScheme.ringCatSheaf.obj)).mapIso
      (openPresheafFrame c i W hW) ≪≫
    (asIso (PresheafOfModules.sheafificationAdjunction (R := W.toScheme.ringCatSheaf)
      (𝟙 W.toScheme.ringCatSheaf.obj)).counit).app
      (SheafOfModules.unit W.toScheme.ringCatSheaf)

def lineBundle (hcover : ⊤ ≤ ⨆ i, U i) : LineBundle X where
  sheaf := sheaf c
  locallyRankOne x := by
    have hx : x ∈ ⨆ i, U i := hcover (show x ∈ (⊤ : X.Opens) from trivial)
    obtain ⟨i, hi⟩ := Opens.mem_iSup.mp hx
    exact ⟨U i,hi,⟨openFrame c i (U i) le_rfl⟩⟩

end

open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite

variable {X : Scheme}

def restrictUnit {V W : X.Opens} (h : V ≤ W) : Γ(X,W)ˣ →* Γ(X,V)ˣ :=
  Units.map (X.presheaf.map (homOfLE h).op).hom.toMonoidHom

@[simp] lemma restrictUnit_val {V W : X.Opens} (h : V ≤ W) (a : Γ(X,W)ˣ) :
    (restrictUnit h a : Γ(X,V)) = X.presheaf.map (homOfLE h).op (a : Γ(X,W)) := rfl

@[simp] lemma restrictUnit_trans {V W Z : X.Opens}
    (h : V ≤ W) (k : W ≤ Z) (a : Γ(X,Z)ˣ) :
    restrictUnit h (restrictUnit k a) = restrictUnit (h.trans k) a := by
  apply Units.ext
  change (X.presheaf.map (homOfLE k).op ≫ X.presheaf.map (homOfLE h).op) _ = _
  rw [← Functor.map_comp]
  rfl

@[simp] lemma restrictUnit_refl (V : X.Opens) (a : Γ(X,V)ˣ) :
    restrictUnit (le_refl V) a = a := by
  apply Units.ext
  simp [restrictUnit]

variable {ι : Type} (U : ι → X.Opens)

structure PairCocycle where
  pair (i j : ι) : Γ(X,U i ⊓ U j)ˣ
  identity (i : ι) :
    restrictUnit (show U i ≤ U i ⊓ U i from le_inf le_rfl le_rfl) (pair i i) = 1
  cocycle (i j k : ι) :
    restrictUnit (show (U i ⊓ U j) ⊓ U k ≤ U i ⊓ U j from inf_le_left) (pair i j) *
      restrictUnit (show (U i ⊓ U j) ⊓ U k ≤ U j ⊓ U k from
        le_inf (inf_le_left.trans inf_le_right) inf_le_right) (pair j k) =
      restrictUnit (show (U i ⊓ U j) ⊓ U k ≤ U i ⊓ U k from
        le_inf (inf_le_left.trans inf_le_left) inf_le_right) (pair i k)

variable {U}

def PairCocycle.toCocycle (g : PairCocycle U) : Cocycle U where
  transition i j W hi hj := restrictUnit (le_inf hi hj) (g.pair i j)
  restriction i j {V W} h hi hj := by
    exact congrArg Units.val (restrictUnit_trans h (le_inf hi hj) (g.pair i j))
  identity i W hi := by
    have h := congrArg (restrictUnit hi) (g.identity i)
    simpa only [map_one, restrictUnit_trans] using h
  cocycle i j k W hi hj hk := by
    have h := congrArg (restrictUnit (le_inf (le_inf hi hj) hk)) (g.cocycle i j k)
    simpa only [map_mul, restrictUnit_trans] using h

@[simp] lemma PairCocycle.toCocycle_transition (g : PairCocycle U)
    (i j : ι) (W : X.Opens) (hi : W ≤ U i) (hj : W ≤ U j) :
    g.toCocycle.transition i j W hi hj = restrictUnit (le_inf hi hj) (g.pair i j) := rfl

def PairCocycle.lineBundle (g : PairCocycle U) (hcover : ⊤ ≤ ⨆ i, U i) :
    PiExponentSeshadri.Geometry.LineBundle X :=
  LineBundleGluing.lineBundle g.toCocycle hcover

end PiExponentSeshadri.LineBundleGluing

end

end OAI
end Source0416

-- Source: OAI/NumberTheory/PiExponent/Geometry/ProjectiveRatioCocycle.lean
section Source0417
/-
Modification notice for the LogTwo project.
Derived from openai/math (Apache-2.0), revision adc7f1241b42e322a6451854ab7e4b4c146bf78a.
Original source: lean/OAI/NumberTheory/PiExponent/Geometry/ProjectiveRatioCocycle.lean
Changes: Convert module/import declarations to the Lean 4.34 public module format.
See ../THIRD_PARTY_NOTICES.txt for provenance and the recorded changes.
-/

namespace OAI

noncomputable section

namespace PiExponent.ProjectiveO1

open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite MvPolynomial
open HomogeneousLocalization PiExponentSeshadri.Projective
open PiExponentSeshadri.LineBundleGluing

variable {R σ : Type} [CommRing R]

attribute [local instance] MvPolynomial.gradedAlgebra

abbrev projectiveSpace (R σ : Type) [CommRing R] := Proj (PolyGrade R σ)
abbrev coordinateOpen (i : σ) : (projectiveSpace R σ).Opens :=
  Proj.basicOpen (PolyGrade R σ) (X i)

def coordinateRatio (i j : σ) (W : (projectiveSpace R σ).Opens)
    (hi : W ≤ coordinateOpen i) : Γ(projectiveSpace R σ, W) :=
  ⟨fun x => HomogeneousLocalization.mk
    ⟨1, ⟨X j, poly_X_mem j⟩, ⟨X i, poly_X_mem i⟩, hi x.2⟩,
   fun x => ⟨W, x.2, 𝟙 _, 1, ⟨X j, poly_X_mem j⟩, ⟨X i, poly_X_mem i⟩,
     (fun y => hi y.2), (fun _ => rfl)⟩⟩

theorem coordinateRatio_restrict (i j : σ) {V W : (projectiveSpace R σ).Opens}
    (h : V ≤ W) (hi : W ≤ coordinateOpen i) :
    (projectiveSpace R σ).presheaf.map (homOfLE h).op (coordinateRatio i j W hi) =
      coordinateRatio i j V (h.trans hi) := by
  apply Subtype.ext
  funext x
  rfl

theorem coordinateRatio_self (i : σ) (W : (projectiveSpace R σ).Opens)
    (hi : W ≤ coordinateOpen i) : coordinateRatio i i W hi = 1 := by
  apply Subtype.ext
  funext x
  let : x.1.asHomogeneousIdeal.toIdeal.IsPrime := x.1.isPrime
  apply HomogeneousLocalization.val_injective
  change (HomogeneousLocalization.mk ⟨1, ⟨X i, poly_X_mem i⟩, ⟨X i, poly_X_mem i⟩, hi x.2⟩).val = (1 : HomogeneousLocalization.AtPrime (PolyGrade R σ) x.1.asHomogeneousIdeal.toIdeal).val
  rw [HomogeneousLocalization.val_mk, HomogeneousLocalization.val_one]
  exact Localization.mk_self (⟨X i, hi x.2⟩ : x.1.asHomogeneousIdeal.toIdeal.primeCompl)

theorem coordinateRatio_mul (i j k : σ) (W : (projectiveSpace R σ).Opens)
    (hi : W ≤ coordinateOpen i) (hj : W ≤ coordinateOpen j) :
    coordinateRatio i j W hi * coordinateRatio j k W hj = coordinateRatio i k W hi := by
  apply Subtype.ext
  funext x
  let : x.1.asHomogeneousIdeal.toIdeal.IsPrime := x.1.isPrime
  apply HomogeneousLocalization.val_injective
  change ((HomogeneousLocalization.mk ⟨1, ⟨X j, poly_X_mem j⟩, ⟨X i, poly_X_mem i⟩, hi x.2⟩ :
      HomogeneousLocalization.AtPrime (PolyGrade R σ) x.1.asHomogeneousIdeal.toIdeal) *
    (HomogeneousLocalization.mk ⟨1, ⟨X k, poly_X_mem k⟩, ⟨X j, poly_X_mem j⟩, hj x.2⟩ :
      HomogeneousLocalization.AtPrime (PolyGrade R σ) x.1.asHomogeneousIdeal.toIdeal)).val =
    (HomogeneousLocalization.mk ⟨1, ⟨X k, poly_X_mem k⟩, ⟨X i, poly_X_mem i⟩, hi x.2⟩ :
      HomogeneousLocalization.AtPrime (PolyGrade R σ) x.1.asHomogeneousIdeal.toIdeal).val
  rw [HomogeneousLocalization.val_mul, HomogeneousLocalization.val_mk, HomogeneousLocalization.val_mk, HomogeneousLocalization.val_mk]
  change Localization.mk (X j) (⟨X i, hi x.2⟩ : x.1.asHomogeneousIdeal.toIdeal.primeCompl) *
    Localization.mk (X k) (⟨X j, hj x.2⟩ : x.1.asHomogeneousIdeal.toIdeal.primeCompl) =
    Localization.mk (X k) (⟨X i, hi x.2⟩ : x.1.asHomogeneousIdeal.toIdeal.primeCompl)
  rw [Localization.mk_mul, Localization.mk_eq_mk_iff, Localization.r_iff_exists]
  refine ⟨1, ?_⟩
  simp only [OneMemClass.coe_one, one_mul, Submonoid.coe_mul]
  ring

def ratioUnit (i j : σ) (W : (projectiveSpace R σ).Opens)
    (hi : W ≤ coordinateOpen i) (hj : W ≤ coordinateOpen j) : Γ(projectiveSpace R σ, W)ˣ where
  val := coordinateRatio i j W hi
  inv := coordinateRatio j i W hj
  val_inv := (coordinateRatio_mul i j i W hi hj).trans (coordinateRatio_self i W hi)
  inv_val := (coordinateRatio_mul j i j W hj hi).trans (coordinateRatio_self j W hj)

def coordinateCocycle : Cocycle (coordinateOpen (R := R) (σ := σ)) where
  transition := ratioUnit
  restriction := fun i j {_ _} h hi _ => coordinateRatio_restrict i j h hi
  identity i W hi := Units.ext (coordinateRatio_self i W hi)
  cocycle i j k W hi hj _ := Units.ext (coordinateRatio_mul i j k W hi hj)

def lineBundle : PiExponentSeshadri.Geometry.LineBundle (projectiveSpace R σ) :=
  PiExponentSeshadri.LineBundleGluing.lineBundle coordinateCocycle
    (by rw [show (⨆ i : σ, coordinateOpen (R := R) i) = ⊤ from standardChart_cover])

end PiExponent.ProjectiveO1

end

end OAI
end Source0417

-- Source: OAI/NumberTheory/PiExponent/Geometry/ProjectiveO1ChartMap.lean
section Source0418
/-
Modification notice for the LogTwo project.
Derived from openai/math (Apache-2.0), revision adc7f1241b42e322a6451854ab7e4b4c146bf78a.
Original source: lean/OAI/NumberTheory/PiExponent/Geometry/ProjectiveO1ChartMap.lean
Changes: Convert module/import declarations to the Lean 4.34 public module format.
See ../THIRD_PARTY_NOTICES.txt for provenance and the recorded changes.
-/

namespace OAI

noncomputable section
namespace PiExponent.ProjectiveO1

open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite MvPolynomial
open HomogeneousLocalization PiExponentSeshadri.Projective

variable {R σ : Type} [CommRing R]
attribute [local instance] MvPolynomial.gradedAlgebra

def scalars : R →+* Γ(projectiveSpace R σ, ⊤) :=
  ((Scheme.ΓSpecIso (CommRingCat.of R)).inv ≫
    (polynomialProjectiveProjection R σ).appTop).hom

theorem away_projection (i : σ) :
    Proj.awayι (PolyGrade R σ) (X i) (poly_X_mem i) (by decide) ≫
      polynomialProjectiveProjection R σ =
        Spec.map (CommRingCat.ofHom (chartConstants (R := R) i)) := by
  rw [polynomialProjectiveProjection, Proj.awayι_toSpecZero_assoc, ← Spec.map_comp]
  apply congrArg Spec.map
  apply CommRingCat.hom_ext
  apply RingHom.ext
  intro r
  rfl

theorem coordinateOpen_projection (i : σ) :
    (coordinateOpen (R := R) i).ι ≫ polynomialProjectiveProjection R σ =
      (Proj.basicOpenIsoSpec (PolyGrade R σ) (X i) (poly_X_mem i) (by decide)).hom ≫
        Spec.map (CommRingCat.ofHom (chartConstants (R := R) i)) := by
  have h := congrArg (fun f =>
    (Proj.basicOpenIsoSpec (PolyGrade R σ) (X i) (poly_X_mem i) (by decide)).hom ≫ f)
    (away_projection (R := R) i)
  simpa only [Proj.awayι, Category.assoc, Iso.hom_inv_id_assoc] using h

theorem awayToSection_coordinate (i j : σ) :
    Proj.awayToSection (PolyGrade R σ) (X i) (chartCoordinate (R := R) i j) =
      coordinateRatio i j (coordinateOpen i) le_rfl := by
  apply Subtype.ext
  funext x
  apply HomogeneousLocalization.val_injective
  change (HomogeneousLocalization.mapId (PolyGrade R σ) _
    (chartCoordinate (R := R) i j)).val = _
  simp only [chartCoordinate, HomogeneousLocalization.mapId, HomogeneousLocalization.map,
    HomogeneousLocalization.Away.mk, pow_one]
  rfl

theorem scalarPullback_factorization {A : Type} [CommRing A]
    {X Y : Scheme} (π : X ⟶ Spec (CommRingCat.of R)) (ι : Y ⟶ X)
    (g : Y ⟶ Spec (CommRingCat.of A)) (f : R →+* A)
    (h : ι ≫ π = g ≫ Spec.map (CommRingCat.ofHom f)) :
    ι.appTop.hom.comp (((Scheme.ΓSpecIso (CommRingCat.of R)).inv ≫ π.appTop).hom) =
      (((Scheme.ΓSpecIso (CommRingCat.of A)).inv ≫ g.appTop).hom).comp f := by
  have hh := congrArg (fun t : Y ⟶ Spec (CommRingCat.of R) =>
    (Scheme.ΓSpecIso (CommRingCat.of R)).inv ≫ t.appTop) h
  simp only [Scheme.Hom.comp_appTop, ← Scheme.ΓSpecIso_inv_naturality_assoc] at hh
  exact congrArg CommRingCat.Hom.hom hh

theorem coordinateOpen_pullback (i : σ) :
    (Scheme.ΓSpecIso (CommRingCat.of (PolyChart (R := R) i))).inv ≫
      (Proj.basicOpenIsoSpec (PolyGrade R σ) (X i) (poly_X_mem i) (by decide)).hom.appTop =
    Proj.awayToSection (PolyGrade R σ) (X i) ≫
      (coordinateOpen (R := R) i).topIso.inv := by
  rw [Proj.basicOpenIsoSpec_hom]
  dsimp only [Scheme.Hom.appTop]
  rw [Proj.basicOpenToSpec_app_top, Iso.inv_hom_id_assoc]

theorem coordinateOpen_scalars (i : σ) :
    (coordinateOpen (R := R) i).ι.appTop.hom.comp (scalars (R := R) (σ := σ)) =
      ((Proj.awayToSection (PolyGrade R σ) (X i) ≫
        (coordinateOpen (R := R) i).topIso.inv).hom).comp (chartConstants i) := by
  have h := scalarPullback_factorization (polynomialProjectiveProjection R σ)
    (coordinateOpen (R := R) i).ι
    (Proj.basicOpenIsoSpec (PolyGrade R σ) (X i) (poly_X_mem i) (by decide)).hom
    (chartConstants i) (coordinateOpen_projection i)
  rw [coordinateOpen_pullback] at h
  exact h

def chartRatios (i : σ) (j : σ) : Γ((coordinateOpen (R := R) i).toScheme, ⊤) :=
  (coordinateOpen (R := R) i).topIso.inv (coordinateRatio i j (coordinateOpen i) le_rfl)

@[simp] theorem chartRatios_self (i : σ) : chartRatios (R := R) i i = 1 := by
  simp [chartRatios, coordinateRatio_self]

theorem evalAway_chartRatios (i : σ) :
    evalAway (eval₂Hom
      ((coordinateOpen (R := R) i).ι.appTop.hom.comp (scalars (R := R) (σ := σ)))
      (chartRatios i)) (X i)
      (by simpa only [eval₂Hom_X', chartRatios_self] using
        (isUnit_one : IsUnit (1 : Γ((coordinateOpen (R := R) i).toScheme, ⊤)))) =
    (Proj.awayToSection (PolyGrade R σ) (X i) ≫
      (coordinateOpen (R := R) i).topIso.inv).hom := by
  let k := (coordinateOpen (R := R) i).ι.appTop.hom.comp (scalars (R := R) (σ := σ))
  let F := evalAway (𝒜 := PolyGrade R σ) (eval₂Hom k (chartRatios i)) (X i)
    (by simpa only [eval₂Hom_X', chartRatios_self] using
      (isUnit_one : IsUnit (1 : Γ((coordinateOpen (R := R) i).toScheme, ⊤))))
  let Q := (Proj.awayToSection (PolyGrade R σ) (X i) ≫
    (coordinateOpen (R := R) i).topIso.inv).hom
  change F = Q
  have hh : F.comp (polyToChart i) = Q.comp (polyToChart i) := by
    apply MvPolynomial.ringHom_ext
    · intro r
      simp only [RingHom.comp_apply, polyToChart, eval₂Hom_C]
      rw [show F (chartConstants i r) = k r from
        evalAway_constants i k (chartRatios i) (chartRatios_self i) r]
      exact RingHom.congr_fun (coordinateOpen_scalars (R := R) i) r
    · intro j
      simp only [RingHom.comp_apply, polyToChart, eval₂Hom_X']
      rw [show F (chartCoordinate i j.val) = chartRatios i j.val from
        evalAway_coordinate i k (chartRatios i) (chartRatios_self i) j.val]
      exact congrArg (coordinateOpen (R := R) i).topIso.inv
        (awayToSection_coordinate i j.val).symm
  apply RingHom.ext
  intro a
  have ha := RingHom.congr_fun hh (chartToPoly i a)
  simpa only [RingHom.comp_apply,
    show polyToChart i (chartToPoly i a) = a from
      RingHom.congr_fun (polyToChart_comp_chartToPoly i) a] using ha

theorem coordinatesMap_chartRatios (i : σ) :
    coordinatesMap (coordinateOpen (R := R) i).toScheme
      ((coordinateOpen (R := R) i).ι.appTop.hom.comp (scalars (R := R) (σ := σ)))
      (chartRatios i) i (chartRatios_self i) = (coordinateOpen (R := R) i).ι := by
  unfold coordinatesMap fromUnitCoordinate
  rw [evalAway_chartRatios]
  change (coordinateOpen (R := R) i).toScheme.toSpecΓ ≫
    Spec.map (Proj.awayToSection (PolyGrade R σ) (X i) ≫
      (coordinateOpen (R := R) i).topIso.inv) ≫ _ = _
  simp only [Spec.map_comp, ← Category.assoc]
  change Proj.basicOpenToSpec (PolyGrade R σ) (X i) ≫ _ = _
  rw [← Proj.basicOpenIsoSpec_hom (PolyGrade R σ) (X i) (poly_X_mem i) (by decide)]
  simp only [Proj.awayι, Iso.hom_inv_id_assoc]

end PiExponent.ProjectiveO1

end

end OAI
end Source0418

-- Source: OAI/NumberTheory/PiExponent/Geometry/LineBundleGluingTransitions.lean
section Source0419
-- Modified in this edition: unused plain lemmas removed; see reduction.json.
/-
Modification notice for the LogTwo project.
Derived from openai/math (Apache-2.0), revision adc7f1241b42e322a6451854ab7e4b4c146bf78a.
Original source: lean/OAI/NumberTheory/PiExponent/Geometry/LineBundleGluingTransitions.lean
Changes: Convert module/import declarations to the Lean 4.34 public module format.
See ../THIRD_PARTY_NOTICES.txt for provenance and the recorded changes.
-/

namespace OAI

namespace PiExponentSeshadri.LineBundleGluing
noncomputable section
open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite
open PiExponentSeshadri.Geometry PiExponentSeshadri.Frames
variable {X : Scheme} {ι : Type} {U : ι → X.Opens}

def multiply (W : X.Opens) (a : Γ(X,W)) :
    SheafOfModules.unit W.toScheme.ringCatSheaf ⟶
      SheafOfModules.unit W.toScheme.ringCatSheaf :=
  (SheafOfModules.unit W.toScheme.ringCatSheaf).unitHomEquiv.symm
    (PresheafOfModules.sectionsMk
      (fun V => X.presheaf.map (homOfLE (W.ι_image_le V.unop)).op a)
      (fun {V V'} f => by
        change (X.presheaf.map _ ≫ X.presheaf.map _) a = _
        erw [← Functor.map_comp]
        rfl))

variable (c : Cocycle U)

end
end PiExponentSeshadri.LineBundleGluing

end OAI
end Source0419

-- Source: OAI/NumberTheory/PiExponent/Geometry/LineBundleGluingSections.lean
section Source0420
-- Modified in this edition: unused plain lemmas removed; see reduction.json.
/-
Modification notice for the LogTwo project.
Derived from openai/math (Apache-2.0), revision adc7f1241b42e322a6451854ab7e4b4c146bf78a.
Original source: lean/OAI/NumberTheory/PiExponent/Geometry/LineBundleGluingSections.lean
Changes: Convert module/import declarations to the Lean 4.34 public module format.
See ../THIRD_PARTY_NOTICES.txt for provenance and the recorded changes.
-/

namespace OAI

namespace PiExponentSeshadri.LineBundleGluing
noncomputable section
open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite
open PiExponentSeshadri.Geometry PiExponentSeshadri.Frames
variable {X : Scheme.{0}} {ι : Type} {U : ι → X.Opens} (c : Cocycle U)

def globalSection (s : sections c ⊤) : O X ⟶ sheaf c :=
  (moduleSectionEquiv (sheaf c)).symm
    ((((PresheafOfModules.sheafificationAdjunction (R := X.ringCatSheaf)
      (𝟙 X.ringCatSheaf.obj)).unit.app (presheaf c)).app (op ⊤)) s)

lemma sheafification_unit_counit_map (Z : Scheme.{0})
    (P : PresheafOfModules Z.ringCatSheaf.obj) (M : Z.Modules) (e : P ⟶ M.val) :
    (TensorPure.adj Z).unit.app P ≫
      ((PresheafOfModules.sheafification (𝟙 Z.ringCatSheaf.obj)).map e).val ≫
      ((TensorPure.adj Z).counit.app M).val = e := by
  let F : PresheafOfModules Z.ringCatSheaf.obj ⥤ Z.Modules :=
    PresheafOfModules.sheafification (𝟙 Z.ringCatSheaf.obj)
  let G : Z.Modules ⥤ PresheafOfModules Z.ringCatSheaf.obj :=
    SheafOfModules.forget Z.ringCatSheaf ⋙
      PresheafOfModules.restrictScalars (𝟙 Z.ringCatSheaf.obj)
  let a : F ⊣ G := TensorPure.adj Z
  have h := (a.unit_comp_map_eq_iff (F.map e ≫ a.counit.app M) e).mpr rfl
  have hm := congrArg (fun q => a.unit.app P ≫ q)
    (G.map_comp (F.map e) (a.counit.app M))
  exact hm.symm.trans h

lemma openFrame_unit (i : ι) (W : X.Opens) (hW : W ≤ U i) :
    (modulePresheafRestrict W.ι).map
        ((PresheafOfModules.sheafificationAdjunction (R := X.ringCatSheaf)
          (𝟙 X.ringCatSheaf.obj)).unit.app (presheaf c)) ≫
      (openFrame c i W hW).hom.val = (openPresheafFrame c i W hW).hom := by
  simp only [openFrame]
  let R := modulePresheafRestrict W.ι
  let F : PresheafOfModules W.toScheme.ringCatSheaf.obj ⥤ W.toScheme.Modules :=
    PresheafOfModules.sheafification (𝟙 W.toScheme.ringCatSheaf.obj)
  let a : (sheaf c).restrict W.ι ⟶ F.obj (R.obj (presheaf c)) :=
    (moduleSheafificationRestrict W.ι).hom.app (presheaf c)
  let b : F.obj (O W.toScheme).val ⟶ O W.toScheme :=
    (TensorPure.adj W.toScheme).counit.app (O W.toScheme)
  let e := (openPresheafFrame c i W hW).hom
  change R.map ((TensorPure.adj X).unit.app (presheaf c)) ≫
    a.val ≫ (F.map e).val ≫ b.val = e
  have h := TensorPure.sheafify_restrict_unit W.ι (presheaf c)
  have h₁ := Category.assoc
    (R.map ((TensorPure.adj X).unit.app (presheaf c))) a.val ((F.map e).val ≫ b.val)
  have h₂ := congrArg (fun q => q ≫ (F.map e).val ≫ b.val) h
  have h₃ := sheafification_unit_counit_map W.toScheme _ (O W.toScheme) e
  exact h₁.symm.trans (h₂.trans h₃)

lemma openFrame_unit_apply (i : ι) (W : X.Opens) (hW : W ≤ U i)
    (V : W.toScheme.Opens) (s : sections c (W.ι ''ᵁ V)) :
    (openFrame c i W hW).hom.app V
      ((((PresheafOfModules.sheafificationAdjunction (R := X.ringCatSheaf)
        (𝟙 X.ringCatSheaf.obj)).unit.app (presheaf c)).app (op (W.ι ''ᵁ V))) s) =
      s.val ⟨i,W.ι ''ᵁ V,le_rfl,(W.ι_image_le V).trans hW⟩ := by
  have h := congrArg (fun q => q.app (op V) s) (openFrame_unit c i W hW)
  exact h

lemma globalSection_app_one (s : sections c ⊤) (V : X.Opens) :
    (globalSection c s).app V (1 : Γ(X,V)) =
      (((PresheafOfModules.sheafificationAdjunction (R := X.ringCatSheaf)
        (𝟙 X.ringCatSheaf.obj)).unit.app (presheaf c)).app (op V)
          (restrict c le_top s)) := by
  have ht := (moduleSectionEquiv (sheaf c)).apply_symm_apply
    ((((PresheafOfModules.sheafificationAdjunction (R := X.ringCatSheaf)
      (𝟙 X.ringCatSheaf.obj)).unit.app (presheaf c)).app (op ⊤)) s)
  change (globalSection c s).app ⊤ (1 : Γ(X,⊤)) = _ at ht
  rw [← section_value_natural (globalSection c s) (homOfLE (show V ≤ ⊤ from le_top)), ht]
  exact (PresheafOfModules.naturality_apply
    ((PresheafOfModules.sheafificationAdjunction (R := X.ringCatSheaf)
      (𝟙 X.ringCatSheaf.obj)).unit.app (presheaf c))
        (homOfLE (show V ≤ ⊤ from le_top)).op s).symm

theorem globalSection_coefficient (s : sections c ⊤) (i : ι)
    (W : X.Opens) (hW : W ≤ U i) :
    W.topIso.hom (coefficient (openFrame c i W hW)
      (restrictSection W.ι (globalSection c s))) = s.val ⟨i,W,le_top,hW⟩ := by
  change W.topIso.hom ((openFrame c i W hW).hom.app ⊤
    ((globalSection c s).app (W.ι ''ᵁ ⊤)
      ((W.ι.appIso ⊤).inv (1 : Γ(W.toScheme,⊤))))) = _
  rw [map_one, globalSection_app_one, openFrame_unit_apply]
  change W.topIso.hom (s.val ⟨i,W.ι ''ᵁ ⊤,le_top,(W.ι_image_le ⊤).trans hW⟩) = _
  rw [← s.property.1 i W (W.ι ''ᵁ ⊤) le_top hW (W.ι_image_le ⊤)]
  simp only [Scheme.Opens.topIso_hom]
  change (X.presheaf.map _ ≫ X.presheaf.map _) (s.val ⟨i,W,le_top,hW⟩) = _
  erw [← Functor.map_comp]
  change X.presheaf.map (𝟙 (op W)) (s.val ⟨i,W,le_top,hW⟩) = _
  exact congrArg (fun q => q (s.val ⟨i,W,le_top,hW⟩)) (X.presheaf.map_id (op W))

end
end PiExponentSeshadri.LineBundleGluing

end OAI
end Source0420

-- Source: OAI/NumberTheory/PiExponent/Geometry/ProjectiveO1Sections.lean
section Source0421
/-
Modification notice for the LogTwo project.
Derived from openai/math (Apache-2.0), revision adc7f1241b42e322a6451854ab7e4b4c146bf78a.
Original source: lean/OAI/NumberTheory/PiExponent/Geometry/ProjectiveO1Sections.lean
Changes: Convert module/import declarations to the Lean 4.34 public module format.
See ../THIRD_PARTY_NOTICES.txt for provenance and the recorded changes.
-/

namespace OAI

noncomputable section

namespace PiExponent.ProjectiveO1

open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite
open PiExponentSeshadri.LineBundleGluing PiExponentSeshadri.Frames

variable {R σ : Type} [CommRing R]

def coordinateCoefficients (k : σ) (V : (projectiveSpace R σ).Opens) :
    sections (coordinateCocycle (R := R) (σ := σ)) V :=
  ⟨fun p => coordinateRatio p.1 k p.2.val p.2.property.2,
   ⟨fun i _ _ _ hi h => coordinateRatio_restrict i k h hi,
    fun i j W _ hi hj => (coordinateRatio_mul i j k W hi hj).symm⟩⟩

def coordinateSection (k : σ) :
    O (projectiveSpace R σ) ⟶ (lineBundle (R := R) (σ := σ)).sheaf :=
  globalSection coordinateCocycle (coordinateCoefficients k ⊤)

theorem coordinateSection_coefficient (i k : σ) (W : (projectiveSpace R σ).Opens)
    (hW : W ≤ coordinateOpen i) :
    W.topIso.hom (coefficient (openFrame coordinateCocycle i W hW)
      (restrictSection W.ι (coordinateSection k))) = coordinateRatio i k W hW := by
  exact globalSection_coefficient coordinateCocycle (coordinateCoefficients k ⊤) i W hW

theorem coordinateSection_coefficient_eq (i k : σ) (W : (projectiveSpace R σ).Opens)
    (hW : W ≤ coordinateOpen i) :
    coefficient (openFrame coordinateCocycle i W hW)
      (restrictSection W.ι (coordinateSection k)) =
        W.topIso.inv (coordinateRatio i k W hW) := by
  apply (ConcreteCategory.bijective_of_isIso W.topIso.hom).1
  rw [coordinateSection_coefficient]
  exact (Iso.inv_hom_id_apply W.topIso (coordinateRatio i k W hW)).symm

theorem coordinateSection_normalized (i : σ) (W : (projectiveSpace R σ).Opens)
    (hW : W ≤ coordinateOpen i) :
    coefficient (openFrame coordinateCocycle i W hW)
      (restrictSection W.ι (coordinateSection i)) = 1 := by
  apply (ConcreteCategory.bijective_of_isIso W.topIso.hom).1
  rw [coordinateSection_coefficient, coordinateRatio_self, map_one]

theorem coordinateOpen_le_isoOpen (i : σ) :
    coordinateOpen (R := R) i ≤ PiExponentSeshadri.SectionOpens.isoOpen (coordinateSection i) := by
  intro x hx
  have h := preimage_isoOpen (coordinateSection (R := R) i) (coordinateOpen i).ι
    (openFrame coordinateCocycle i (coordinateOpen i) le_rfl)
  have hn := coordinateSection_normalized (R := R) i (coordinateOpen i) le_rfl
  have hbasic := congrArg (coordinateOpen (R := R) i).toScheme.basicOpen hn
  have hone := h.trans (hbasic.trans (Scheme.basicOpen_one _))
  have hp : (⟨x,hx⟩ : (coordinateOpen (R := R) i).toScheme) ∈
      (coordinateOpen i).ι ⁻¹ᵁ PiExponentSeshadri.SectionOpens.isoOpen (coordinateSection i) := by
    rw [hone]
    trivial
  exact hp

theorem coordinateSection_cover :
    (⨆ i : σ, PiExponentSeshadri.SectionOpens.isoOpen (coordinateSection (R := R) i)) = ⊤ := by
  apply top_unique
  rw [← show (⨆ i : σ, coordinateOpen (R := R) i) = ⊤ from
    PiExponentSeshadri.Projective.standardChart_cover]
  exact iSup_mono coordinateOpen_le_isoOpen

end PiExponent.ProjectiveO1

end

end OAI
end Source0421

-- Source: OAI/NumberTheory/PiExponent/Geometry/ProjectiveO1LocalIdentity.lean
section Source0422
/-
Modification notice for the LogTwo project.
Derived from openai/math (Apache-2.0), revision adc7f1241b42e322a6451854ab7e4b4c146bf78a.
Original source: lean/OAI/NumberTheory/PiExponent/Geometry/ProjectiveO1LocalIdentity.lean
Changes: Convert module/import declarations to the Lean 4.34 public module format.
See ../THIRD_PARTY_NOTICES.txt for provenance and the recorded changes.
-/

namespace OAI

noncomputable section
namespace PiExponent.ProjectiveO1
open AlgebraicGeometry CategoryTheory TopologicalSpace
open PiExponentSeshadri.Projective PiExponentSeshadri.Frames PiExponentSeshadri.LineBundleGluing
variable {R σ : Type} [CommRing R]

theorem coordinateSection_localMap (i : σ) :
    coordinatesMap (coordinateOpen (R := R) i).toScheme
      ((coordinateOpen i).ι.appTop.hom.comp (scalars (R := R) (σ := σ)))
      (fun j => coefficient (openFrame (coordinateCocycle (R := R) (σ := σ)) i (coordinateOpen i) le_rfl)
        (restrictSection (coordinateOpen i).ι (coordinateSection (R := R) j))) i
      (coordinateSection_normalized i (coordinateOpen i) le_rfl) = (coordinateOpen i).ι := by
  have htuple : (fun j => coefficient
      (openFrame (coordinateCocycle (R := R) (σ := σ)) i (coordinateOpen (R := R) i) le_rfl)
      (restrictSection (coordinateOpen i).ι (coordinateSection (R := R) j))) = chartRatios (R := R) i := by
    funext j
    exact coordinateSection_coefficient_eq i j (coordinateOpen i) le_rfl
  exact (coordinatesMap_congr _ htuple i _ (chartRatios_self i)).trans
    (coordinatesMap_chartRatios (R := R) i)

end PiExponent.ProjectiveO1

end

end OAI
end Source0422

-- Source: OAI/NumberTheory/PiExponent/Polynomials/PullbackFrameCoefficient.lean
section Source0423
/-
Modification notice for the LogTwo project.
Derived from openai/math (Apache-2.0), revision adc7f1241b42e322a6451854ab7e4b4c146bf78a.
Original source: lean/OAI/NumberTheory/PiExponent/Polynomials/PullbackFrameCoefficient.lean
Changes: Convert module/import declarations to the Lean 4.34 public module format.
See ../THIRD_PARTY_NOTICES.txt for provenance and the recorded changes.
-/

namespace OAI

noncomputable section
open CategoryTheory AlgebraicGeometry
open PiExponentSeshadri.Geometry PiExponentSeshadri.Frames

namespace PiExponent.PullbackFrameCoefficient

theorem exists_frame_natIso_all {X Y : Scheme.{0}}
    (F G : X.Modules ⥤ Y.Modules) (v : F ≅ G)
    (uF : F.obj (O X) ≅ O Y) (uG : G.obj (O X) ≅ O Y)
    {M : X.Modules} (e : G.obj M ≅ O Y) :
    ∃ eF : F.obj M ≅ O Y, ∀ s : O X ⟶ M,
      coefficient eF (uF.inv ≫ F.map s) = coefficient e (uG.inv ≫ G.map s) := by
  let b : O Y ≅ O Y := uF.symm ≪≫ v.app (O X) ≪≫ uG
  refine ⟨v.app M ≪≫ e ≪≫ b.symm, ?_⟩
  intro s
  have h : (uF.inv ≫ F.map s) ≫ (v.app M).hom =
      b.hom ≫ (uG.inv ≫ G.map s) := by
    simp only [b, Iso.trans_hom, Iso.symm_hom, Category.assoc]
    simp only [Iso.hom_inv_id_assoc]
    exact congrArg (fun q => uF.inv ≫ q) (v.hom.naturality s)
  change endValue (((uF.inv ≫ F.map s) ≫ (v.app M).hom) ≫ e.hom ≫ b.inv) = _
  rw [h]
  change endValue (b.hom ≫ (uG.inv ≫ G.map s ≫ e.hom) ≫ b.inv) = _
  exact endValue_conjugation b (uG.inv ≫ G.map s ≫ e.hom)

theorem exists_frame_of_factors_through_open {X Y : Scheme.{0}}
    (U : X.Opens) (g : Y ⟶ U.toScheme)
    {M : X.Modules} (e : M.restrict U.ι ≅ O U.toScheme) :
    ∃ eF : (Scheme.Modules.pullback (g ≫ U.ι)).obj M ≅ O Y,
      ∀ s : O X ⟶ M,
      coefficient eF (pullbackSection (g ≫ U.ι) s) =
        g.appTop (coefficient e (restrictSection U.ι s)) := by
  let F : X.Modules ⥤ Y.Modules := Scheme.Modules.pullback (g ≫ U.ι)
  let G : X.Modules ⥤ Y.Modules :=
    Scheme.Modules.restrictFunctor U.ι ⋙ Scheme.Modules.pullback g
  let v : F ≅ G := (Scheme.Modules.pullbackComp g U.ι).symm ≪≫
    Functor.isoWhiskerRight (Scheme.Modules.restrictFunctorIsoPullback U.ι).symm
      (Scheme.Modules.pullback g)
  let uG : G.obj (O X) ≅ O Y :=
    (Scheme.Modules.pullback g).mapIso (Scheme.Modules.restrictUnitIso U.ι) ≪≫
      pullbackUnitIso g
  obtain ⟨eF, he⟩ := exists_frame_natIso_all F G v (pullbackUnitIso (g ≫ U.ι)) uG
    (pullbackFrame g e)
  refine ⟨eF, fun s => ?_⟩
  have hs := he s
  have hs' : coefficient eF (pullbackSection (g ≫ U.ι) s) =
      coefficient (pullbackFrame g e) (pullbackSection g (restrictSection U.ι s)) := by
    let S : X.Modules ⥤ U.toScheme.Modules := Scheme.Modules.restrictFunctor U.ι
    let Q : U.toScheme.Modules ⥤ Y.Modules := Scheme.Modules.pullback g
    let a : S.obj (O X) ≅ O U.toScheme := Scheme.Modules.restrictUnitIso U.ι
    let q : Q.obj (O U.toScheme) ≅ O Y := pullbackUnitIso g
    have hr : pullbackSection g (restrictSection U.ι s) = uG.inv ≫ G.map s := by
      change q.inv ≫ Q.map (a.inv ≫ S.map s) = (q.inv ≫ Q.map a.inv) ≫ Q.map (S.map s)
      exact (congrArg (fun k => q.inv ≫ k) (Q.map_comp a.inv (S.map s))).trans
        (Category.assoc q.inv (Q.map a.inv) (Q.map (S.map s))).symm
    exact hs.trans (congrArg (coefficient (pullbackFrame g e)) hr).symm
  rw [hs', coefficient_pullback]

end PiExponent.PullbackFrameCoefficient

end

end OAI
end Source0423

-- Source: OAI/NumberTheory/PiExponent/Geometry/ProjectivePullbackFrames.lean
section Source0424
/-
Modification notice for the LogTwo project.
Derived from openai/math (Apache-2.0), revision adc7f1241b42e322a6451854ab7e4b4c146bf78a.
Original source: lean/OAI/NumberTheory/PiExponent/Geometry/ProjectivePullbackFrames.lean
Changes: Convert module/import declarations to the Lean 4.34 public module format.
See ../THIRD_PARTY_NOTICES.txt for provenance and the recorded changes.
-/

namespace OAI

namespace PiExponentSeshadri.Geometry
noncomputable section
open AlgebraicGeometry CategoryTheory TopologicalSpace
open PiExponentSeshadri.Frames
variable {X Y : Scheme.{0}}

def pullbackRestrictFactorNatIso (f : Y ⟶ X) (U : X.Opens) (V : Y.Opens)
    (g : V.toScheme ⟶ U.toScheme) (h : V.ι ≫ f = g ≫ U.ι) :
    Scheme.Modules.pullback f ⋙ Scheme.Modules.restrictFunctor V.ι ≅
      Scheme.Modules.restrictFunctor U.ι ⋙ Scheme.Modules.pullback g :=
  Functor.isoWhiskerLeft (Scheme.Modules.pullback f)
    (Scheme.Modules.restrictFunctorIsoPullback V.ι) ≪≫
  Scheme.Modules.pullbackComp V.ι f ≪≫
  Scheme.Modules.pullbackCongr h ≪≫
  (Scheme.Modules.pullbackComp g U.ι).symm ≪≫
  Functor.isoWhiskerRight (Scheme.Modules.restrictFunctorIsoPullback U.ι).symm
    (Scheme.Modules.pullback g)

theorem exists_restricted_pullback_frame_all_of_factor
    (f : Y ⟶ X) (U : X.Opens) (V : Y.Opens)
    (g : V.toScheme ⟶ U.toScheme) (h : V.ι ≫ f = g ≫ U.ι)
    {M : X.Modules} (e : M.restrict U.ι ≅ O U.toScheme) :
    ∃ eF : ((Scheme.Modules.pullback f).obj M).restrict V.ι ≅ O V.toScheme,
      ∀ s : O X ⟶ M,
      coefficient eF (restrictSection V.ι (pullbackSection f s)) =
        g.appTop (coefficient e (restrictSection U.ι s)) := by
  let F : X.Modules ⥤ V.toScheme.Modules :=
    Scheme.Modules.pullback f ⋙ Scheme.Modules.restrictFunctor V.ι
  let G : X.Modules ⥤ V.toScheme.Modules :=
    Scheme.Modules.restrictFunctor U.ι ⋙ Scheme.Modules.pullback g
  let uF : F.obj (O X) ≅ O V.toScheme :=
    (Scheme.Modules.restrictFunctor V.ι).mapIso (pullbackUnitIso f) ≪≫
      Scheme.Modules.restrictUnitIso V.ι
  let uG : G.obj (O X) ≅ O V.toScheme :=
    (Scheme.Modules.pullback g).mapIso (Scheme.Modules.restrictUnitIso U.ι) ≪≫
      pullbackUnitIso g
  obtain ⟨eF, he⟩ := PiExponent.PullbackFrameCoefficient.exists_frame_natIso_all
    F G (pullbackRestrictFactorNatIso f U V g h) uF uG (pullbackFrame g e)
  refine ⟨eF, fun s => ?_⟩
  have hs : coefficient eF (restrictSection V.ι (pullbackSection f s)) =
      coefficient (pullbackFrame g e) (pullbackSection g (restrictSection U.ι s)) := by
    let P : X.Modules ⥤ Y.Modules := Scheme.Modules.pullback f
    let R : Y.Modules ⥤ V.toScheme.Modules :=
      Scheme.Modules.restrictFunctor V.ι
    let S : X.Modules ⥤ U.toScheme.Modules := Scheme.Modules.restrictFunctor U.ι
    let Q : U.toScheme.Modules ⥤ V.toScheme.Modules :=
      Scheme.Modules.pullback g
    let p : P.obj (O X) ≅ O Y := pullbackUnitIso f
    let r : R.obj (O Y) ≅ O V.toScheme :=
      Scheme.Modules.restrictUnitIso V.ι
    let a : S.obj (O X) ≅ O U.toScheme := Scheme.Modules.restrictUnitIso U.ι
    let q : Q.obj (O U.toScheme) ≅ O V.toScheme := pullbackUnitIso g
    have hl : restrictSection V.ι (pullbackSection f s) = uF.inv ≫ F.map s := by
      change r.inv ≫ R.map (p.inv ≫ P.map s) = (r.inv ≫ R.map p.inv) ≫ R.map (P.map s)
      exact (congrArg (fun k => r.inv ≫ k) (R.map_comp p.inv (P.map s))).trans
        (Category.assoc r.inv (R.map p.inv) (R.map (P.map s))).symm
    have hr : pullbackSection g (restrictSection U.ι s) = uG.inv ≫ G.map s := by
      change q.inv ≫ Q.map (a.inv ≫ S.map s) = (q.inv ≫ Q.map a.inv) ≫ Q.map (S.map s)
      exact (congrArg (fun k => q.inv ≫ k) (Q.map_comp a.inv (S.map s))).trans
        (Category.assoc q.inv (Q.map a.inv) (Q.map (S.map s))).symm
    exact (congrArg (coefficient eF) hl).trans
      ((he s).trans (congrArg (coefficient (pullbackFrame g e)) hr).symm)
  rw [hs, coefficient_pullback]

theorem exists_restricted_pullback_frame_all (f : Y ⟶ X) (U : X.Opens)
    {M : X.Modules} (e : M.restrict U.ι ≅ O U.toScheme) :
    ∃ eF : ((Scheme.Modules.pullback f).obj M).restrict (f ⁻¹ᵁ U).ι ≅
        O (f ⁻¹ᵁ U).toScheme,
      ∀ s : O X ⟶ M,
      coefficient eF (restrictSection (f ⁻¹ᵁ U).ι (pullbackSection f s)) =
        (f ∣_ U).appTop (coefficient e (restrictSection U.ι s)) :=
  exists_restricted_pullback_frame_all_of_factor f U (f ⁻¹ᵁ U) (f ∣_ U)
    (morphismRestrict_ι f U).symm e

def restrictedPullbackFrame (f : Y ⟶ X) (U : X.Opens) (V : Y.Opens)
    (g : V.toScheme ⟶ U.toScheme) (h : V.ι ≫ f = g ≫ U.ι)
    {M : X.Modules} (e : M.restrict U.ι ≅ O U.toScheme) :
    ((Scheme.Modules.pullback f).obj M).restrict V.ι ≅ O V.toScheme :=
  (exists_restricted_pullback_frame_all_of_factor f U V g h e).choose

lemma restrictedPullbackFrame_coefficient (f : Y ⟶ X) (U : X.Opens) (V : Y.Opens)
    (g : V.toScheme ⟶ U.toScheme) (h : V.ι ≫ f = g ≫ U.ι)
    {M : X.Modules} (e : M.restrict U.ι ≅ O U.toScheme) (s : O X ⟶ M) :
    coefficient (restrictedPullbackFrame f U V g h e)
      (restrictSection V.ι (pullbackSection f s)) =
      g.appTop (coefficient e (restrictSection U.ι s)) :=
  (exists_restricted_pullback_frame_all_of_factor f U V g h e).choose_spec s

end
end PiExponentSeshadri.Geometry

end OAI
end Source0424

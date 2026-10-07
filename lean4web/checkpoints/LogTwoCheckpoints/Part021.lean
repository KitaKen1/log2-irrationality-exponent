/- Generated rc4 checkpoint for LogTwo.
Modified from the reduced edition: new imports, separate module compilation,
and synchronous elaboration. Original source blocks and notices are retained.
See ../../../THIRD_PARTY_NOTICES.txt and ../../reduction.json.
-/
module
public import LogTwoCheckpoints.Part000
public import LogTwoCheckpoints.Part001
public import LogTwoCheckpoints.Part002
public import LogTwoCheckpoints.Part003
public import LogTwoCheckpoints.Part004
public import LogTwoCheckpoints.Part008
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
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Monoidal
public import Mathlib.AlgebraicGeometry.Modules.Sheaf
public import Mathlib.AlgebraicGeometry.Morphisms.SchemeTheoreticallyDominant
public import Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Basic
public import Mathlib.AlgebraicGeometry.ZariskisMainTheorem
public import Mathlib.Analysis.Complex.Polynomial.Basic
public import Mathlib.Data.ENat.SuccOrder
public import Mathlib.Data.Opposite
public import Mathlib.Data.SetLike.Basic
public import Mathlib.RingTheory.KrullDimension.NonZeroDivisors
@[expose] public section
set_option Elab.async false

-- Source: OAI/NumberTheory/PiExponent/Polynomials/WeightedMonomialFamilyLattice.lean
section Source0525
/-
Modification notice for the LogTwo project.
Derived from openai/math (Apache-2.0), revision adc7f1241b42e322a6451854ab7e4b4c146bf78a.
Original source: lean/OAI/NumberTheory/PiExponent/Polynomials/WeightedMonomialFamilyLattice.lean
Changes: Convert module/import declarations to the Lean 4.34 public module format.
See ../THIRD_PARTY_NOTICES.txt for provenance and the recorded changes.
-/

namespace OAI

noncomputable section
open scoped BigOperators
open PiExponent.CurveValuationCenter PiExponent.WeightedPolynomialPole
open PiExponent.WeightedLocalLattice PiExponent.CurveGlobalMonomialLocal

namespace PiExponent.WeightedMonomialFamilyLattice

theorem exists_generator
    {E ι σ : Type} [Field E] [Algebra ℂ E] [Fintype ι] [Fintype σ]
    (p : NormalizedPlace ℂ E) (a : σ → ι →₀ ℕ) (x : ι → E)
    (z : σ) (hz : a z = 0) (w : ι → ℚ) (hw : ∀ j, 0 < w j)
    {R : ℚ} (hR : 0 < R) (powers : ι → ℕ)
    (hpowers : ∀ j, w j * (powers j : ℚ) = R)
    (pure : ι → σ) (hpure : ∀ j, a (pure j) = Finsupp.single j (powers j))
    (hbudget : ∀ s, (∑ j, w j * (a s j : ℚ)) ≤ R) :
    ∃ i : σ, monomialCoordinates (F := ℂ) a x i ≠ 0 ∧
      (coordinateOrder p.valuation (monomialCoordinates (F := ℂ) a x i) : ℚ) =
        -R * coordinatePole p.valuation x w ∧
      generatedLattice (PlaceValuationRing.ring p) (monomialCoordinates (F := ℂ) a x)
        Finset.univ = Submodule.span (PlaceValuationRing.ring p)
          {monomialCoordinates (F := ℂ) a x i} := by
  classical
  let M : Finset (ι → ℕ) := Finset.univ.image (fun s : σ => fun j => a s j)
  have hzero : 0 ∈ M := by
    apply Finset.mem_image.mpr
    refine ⟨z, Finset.mem_univ z, ?_⟩
    funext j
    simp [hz]
  have hpureM : ∀ j, Pi.single j (powers j) ∈ M := by
    intro j
    apply Finset.mem_image.mpr
    refine ⟨pure j, Finset.mem_univ _, ?_⟩
    ext k
    simp [hpure, Finsupp.single_apply, Pi.single_apply, eq_comm]
  have hbudgetM : ∀ b ∈ M, (∑ j, w j * (b j : ℚ)) ≤ R := by
    intro b hb
    obtain ⟨s, _, rfl⟩ := Finset.mem_image.mp hb
    exact hbudget s
  obtain ⟨b, hb, hbn, hbo, hmin⟩ := WeightedMonomialPole.exists_minimizing_monomial
    p.valuation x w hw hR powers hpowers M hzero hpureM hbudgetM
  obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hb
  have hn : monomialCoordinates (F := ℂ) a x i ≠ 0 := by
    simpa only [monomialCoordinates_eq_prod] using hbn
  refine ⟨i, hn, ?_, ?_⟩
  · simpa only [monomialCoordinates_eq_prod] using hbo
  · apply generatedLattice_eq_span_of_minimum _ Finset.univ i (Finset.mem_univ i) hn
    intro j hj
    rw [← PlaceValuationRing.valuation_eq_fractionAddValuation]
    simpa only [monomialCoordinates_eq_prod] using
      hmin (fun k => a j k) (Finset.mem_image.mpr ⟨j, Finset.mem_univ j, rfl⟩)

end PiExponent.WeightedMonomialFamilyLattice

end

end OAI
end Source0525

-- Source: OAI/NumberTheory/PiExponent/Geometry/WeightedProjectiveCurveDegree.lean
section Source0526
/-
Modification notice for the LogTwo project.
Derived from openai/math (Apache-2.0), revision adc7f1241b42e322a6451854ab7e4b4c146bf78a.
Original source: lean/OAI/NumberTheory/PiExponent/Geometry/WeightedProjectiveCurveDegree.lean
Changes: Convert module/import declarations to the Lean 4.34 public module format.
See ../THIRD_PARTY_NOTICES.txt for provenance and the recorded changes.
-/

namespace OAI

noncomputable section
open AlgebraicGeometry CategoryTheory
open PiExponentSeshadri.Geometry PiExponentSeshadri.Frames
open PiExponent.CurveNormalizationModel PiExponent.CurveValuationCenter
open PiExponent.CurveGlobalMonomialLocal PiExponent.WeightedPolynomialPole
open PiExponent.CurveGlobalCoordinateOrder

namespace PiExponent.WeightedProjectiveCurveDegree

variable {E ι σ : Type} [Field E] [Algebra ℂ E] [Fintype ι] [Fintype σ]
variable (f : E) (hf : Transcendental ℂ f)
variable [FiniteDimensional (IntermediateField.adjoin ℂ {f}) E]

theorem ambient_pullback_degree
    (a : σ → ι →₀ ℕ) (x : ι → E) (z : σ) (hz : a z = 0)
    (g : parameterCurve f hf ⟶ ProjectiveO1.projectiveSpace ℂ σ)
    (hg : parameterCurveGenericPoint f hf ≫ g =
      ProjectiveLocalCoefficients.normalizedMap (algebraMap ℂ E)
        (monomialCoordinates (F := ℂ) a x) z (monomialCoordinates_zero a x z hz))
    (w : ι → ℚ) (hw : ∀ j, 0 < w j) {R : ℚ} (hR : 0 < R)
    (powers : ι → ℕ) (hpowers : ∀ j, w j * (powers j : ℚ) = R)
    (pure : ι → σ) (hpure : ∀ j, a (pure j) = Finsupp.single j (powers j))
    (hbudget : ∀ s, (∑ j, w j * (a s j : ℚ)) ≤ R)
    (hfinite : ∀ q : E, Transcendental ℂ q →
      FiniteDimensional (IntermediateField.adjoin ℂ {q}) E) :
    ((eulerCharacteristic (parameterCurveStructureMap f hf) 1
        ((ProjectiveO1.lineBundle (R := ℂ) (σ := σ)).pullback g).sheaf -
      eulerCharacteristic (parameterCurveStructureMap f hf) 1
        (structureSheaf (parameterCurve f hf)) : ℤ) : ℝ) =
      (R : ℝ) * CurveContactSum.weightedDegree hfinite x w := by
  classical
  let y := monomialCoordinates (F := ℂ) a x
  have hyz : y z = 1 := monomialCoordinates_zero a x z hz
  have hyzn : y z ≠ 0 := hyz ▸ one_ne_zero
  let L := (ProjectiveO1.lineBundle (R := ℂ) (σ := σ)).pullback g
  let s := pullbackSection g (ProjectiveO1.coordinateSection z)
  have hs : s ≠ 0 := coordinateSection_ne_zero f hf g y z hyz hg z hyzn
  let D := CurvePlaceSectionDivisor.divisor f hf L s hs
  let P := CurveContactSum.weightedPoleDivisor hfinite x w
  have hcoeff : ∀ p, (D p : ℝ) = (R : ℝ) * (P p : ℝ) := by
    intro p
    obtain ⟨i, hi, horder, hspan⟩ := WeightedMonomialFamilyLattice.exists_generator
      p a x z hz w hw hR powers hpowers pure hpure hbudget
    have hd := coordinate_divisor_order f hf g y z hyz hg p i hi hspan z hyzn
    have hzero : coordinateOrder p.valuation (y z) = 0 := by
      rw [hyz]
      simp [coordinateOrder]
    rw [hzero, zero_sub] at hd
    have hq : (D p : ℚ) = R * coordinatePole p.valuation x w := by
      have hdq : (D p : ℚ) = -(coordinateOrder p.valuation (y i) : ℚ) := by
        exact_mod_cast hd
      rw [hdq, horder]
      ring
    exact_mod_cast hq
  let T := D.support ∪ P.support
  have hDT : D.support ⊆ T := Finset.subset_union_left
  have hPT : P.support ⊆ T := Finset.subset_union_right
  have hdeg := CurvePlaceSectionDivisor.degree_eq_euler_difference_full f hf L s hs
  change ((eulerCharacteristic (parameterCurveStructureMap f hf) 1 L.sheaf -
    eulerCharacteristic (parameterCurveStructureMap f hf) 1
      (structureSheaf (parameterCurve f hf)) : ℤ) : ℝ) = _
  rw [← hdeg]
  change ((D.sum (fun _ n => (n : ℤ)) : ℤ) : ℝ) = (R : ℝ) * P.sum (fun _ n => (n : ℝ))
  rw [D.sum_of_support_subset hDT (fun _ n => (n : ℤ)) (by simp),
    P.sum_of_support_subset hPT (fun _ n => (n : ℝ)) (by simp)]
  push_cast
  rw [Finset.mul_sum]
  exact Finset.sum_congr rfl (fun p _ => hcoeff p)

theorem weighted_pullback_degree
    (a : σ → ι →₀ ℕ) (x : ι → E) (z : σ) (hz : a z = 0)
    (coordinate : ι → σ) (hcoordinate : ∀ j, a (coordinate j) = Finsupp.single j 1)
    (g : parameterCurve f hf ⟶ Proj (WeightedCompactification.imageGrade (R := ℂ) a))
    (hg : parameterCurveGenericPoint f hf ≫ g =
      CurveMonomialMap.genericMonomialMap a z hz coordinate hcoordinate x)
    (w : ι → ℚ) (hw : ∀ j, 0 < w j) {R : ℚ} (hR : 0 < R)
    (powers : ι → ℕ) (hpowers : ∀ j, w j * (powers j : ℚ) = R)
    (pure : ι → σ) (hpure : ∀ j, a (pure j) = Finsupp.single j (powers j))
    (hbudget : ∀ s, (∑ j, w j * (a s j : ℚ)) ≤ R)
    (hfinite : ∀ q : E, Transcendental ℂ q →
      FiniteDimensional (IntermediateField.adjoin ℂ {q}) E) :
    ((eulerCharacteristic (parameterCurveStructureMap f hf) 1
        ((WeightedCompactification.lineBundle (R := ℂ) a).pullback g).sheaf -
      eulerCharacteristic (parameterCurveStructureMap f hf) 1
        (structureSheaf (parameterCurve f hf)) : ℤ) : ℝ) =
      (R : ℝ) * CurveContactSum.weightedDegree hfinite x w := by
  have he := eulerCharacteristic_iso (parameterCurveStructureMap f hf)
    ((Scheme.Modules.pullbackComp g (WeightedCompactification.projectiveMonomialMap a)).app
      (ProjectiveO1.lineBundle (R := ℂ) (σ := σ)).sheaf) 1
  change eulerCharacteristic (parameterCurveStructureMap f hf) 1
      ((WeightedCompactification.lineBundle (R := ℂ) a).pullback g).sheaf = _ at he
  rw [he]
  apply ambient_pullback_degree f hf a x z hz _ _ w hw hR powers hpowers pure hpure hbudget hfinite
  rw [← Category.assoc, hg]
  exact genericMonomialMap_comp_projectiveMonomialMap a z hz coordinate hcoordinate x

end PiExponent.WeightedProjectiveCurveDegree

end

end OAI
end Source0526

-- Source: LogTwo/Geometry/CurvePolarizationDegree.lean
section Source0527
-- Modified in this edition: unused plain lemmas removed; see reduction.json.
/-! The actual ambient hyperplane degree is the common integer radius times
the function-field weighted pole degree. Pure monomials and the degree
budget are supplied by the already constructed scale, not by new assumptions.
The identity is transported to the pullback A on the concrete blowup. -/
namespace LogTwo.Geometry.MatrixBlowup
open OAI PiExponent AlgebraicGeometry CategoryTheory
open PiExponentSeshadri.Geometry
open LogTwo.Interpolation
open CurveNormalizationModel
noncomputable section
variable {m : ℕ} (w : Weights m)
variable {E : Type} [Field E] [Algebra ℂ E]
variable (f : E) (hf : Transcendental ℂ f)
variable [FiniteDimensional (IntermediateField.adjoin ℂ {f}) E]
variable (hfinite : ∀ t : E, Transcendental ℂ t →
  FiniteDimensional (IntermediateField.adjoin ℂ {t}) E)
variable (z : Fin (m+1) → E)

/-- No injectivity or nonzero assumption on the coordinates is needed for
this degree identity; nonconstancy is used separately for positivity. -/
theorem hyperplane_degree_eq_weightedDegree
    (g : parameterCurve f hf ⟶ MatrixCompactification.space w)
    (hgeneric : parameterCurveGenericPoint f hf ≫ g =
      Spec.map (CommRingCat.ofHom (MvPolynomial.aeval z).toRingHom) ≫
        MatrixCompactification.affineChart w) :
    ((eulerCharacteristic (parameterCurveStructureMap f hf) 1
        ((hyperplane w).pullback g).sheaf -
      eulerCharacteristic (parameterCurveStructureMap f hf) 1
        (structureSheaf (parameterCurve f hf)) : ℤ) : ℝ) =
      (MatrixCompactification.scale w).radius *
        CurveContactSum.weightedDegree hfinite z (rationalColumnWeight w) := by
  apply WeightedProjectiveCurveDegree.weighted_pullback_degree f hf
    (MatrixCompactification.exponents w) z (MatrixCompactification.constantIndex w)
    ((MatrixCompactification.scale w).exponents_constant (rationalColumnWeight_pos w))
    (MatrixCompactification.coordinateIndex w)
    ((MatrixCompactification.scale w).exponents_coordinate (rationalColumnWeight_pos w))
    g hgeneric (rationalColumnWeight w) (rationalColumnWeight_pos w)
    (by exact_mod_cast (MatrixCompactification.scale w).radius_pos)
    (MatrixCompactification.scale w).degreePowers (MatrixCompactification.degree_balance w)
    ((MatrixCompactification.scale w).pureIndex (rationalColumnWeight_pos w))
    ((MatrixCompactification.scale w).exponents_pure (rationalColumnWeight_pos w))
    (MatrixCompactification.monomial_budget w) hfinite

theorem A_degree_eq_weightedDegree {K : ℕ}
    (y : Fin K → ℂ) (c : Fin K → Fin m → ℂ) (T : Fin m → ℕ)
    (g : parameterCurve f hf ⟶ space w y c T)
    (hgeneric : parameterCurveGenericPoint f hf ≫ g ≫ projection w y c T =
      Spec.map (CommRingCat.ofHom (MvPolynomial.aeval z).toRingHom) ≫
        MatrixCompactification.affineChart w) :
    ((eulerCharacteristic (parameterCurveStructureMap f hf) 1
        ((A w y c T).pullback g).sheaf -
      eulerCharacteristic (parameterCurveStructureMap f hf) 1
        (structureSheaf (parameterCurve f hf)) : ℤ) : ℝ) =
      (MatrixCompactification.scale w).radius *
        CurveContactSum.weightedDegree hfinite z (rationalColumnWeight w) := by
  have he := eulerCharacteristic_iso (parameterCurveStructureMap f hf)
    ((Scheme.Modules.pullbackComp g (projection w y c T)).app (hyperplane w).sheaf) 1
  change eulerCharacteristic (parameterCurveStructureMap f hf) 1
    ((A w y c T).pullback g).sheaf =
    eulerCharacteristic (parameterCurveStructureMap f hf) 1
      ((hyperplane w).pullback (g ≫ projection w y c T)).sheaf at he
  rw [he]
  exact hyperplane_degree_eq_weightedDegree w f hf hfinite z (g ≫ projection w y c T) hgeneric

end
end LogTwo.Geometry.MatrixBlowup
end Source0527

-- Source: LogTwo/Geometry/CurveDegreeMargin.lean
section Source0528
-- Modified in this edition: unused plain lemmas removed; see reduction.json.
/-
Modification notice for the LogTwo project.
Adapted from openai/math (Apache-2.0), revision adc7f1241b42e322a6451854ab7e4b4c146bf78a.
Changes: Adapt the degree/contact combination to the intrinsic curve bound.
See ../THIRD_PARTY_NOTICES.txt for provenance and the recorded changes.
-/

/-! Transfer the intrinsic contact inequality to actual Euler degrees on the
constructed blowup, for a supplied normalized-curve map with the stated
generic image. This does not yet construct the normalization of every
integral curve of the blowup or prove ampleness. -/
namespace LogTwo.Geometry.MatrixBlowup
open OAI PiExponent AlgebraicGeometry CategoryTheory
open PiExponentSeshadri.Geometry
open LogTwo.Interpolation LogTwo.Parameters LogTwo.Arithmetic
open CurveNormalizationModel CurveValuationCenter PlaceValuationRing
noncomputable section
variable {E : Type} [Field E] [Algebra ℂ E]
variable (f : E) (hf : Transcendental ℂ f)
variable [FiniteDimensional (IntermediateField.adjoin ℂ {f}) E]

/-- Euler degree on the parameter normalization, as a real number. -/
def normalizationDegree {X : Scheme} (g : parameterCurve f hf ⟶ X)
    (L : LineBundle X) : ℝ :=
  ((eulerCharacteristic (parameterCurveStructureMap f hf) 1 (L.pullback g).sheaf -
    eulerCharacteristic (parameterCurveStructureMap f hf) 1
      (structureSheaf (parameterCurve f hf)) : ℤ) : ℝ)

variable [Algebra.EssFiniteType ℂ E]

/-- Residue integrality, finiteness over every transcendental parameter,
the invertible presentation and both degree comparisons are proved internally.
The chosen normalization still has its explicit finite-extension instance. -/
theorem chosenWeights_degree_nonnegative
    (n : ℕ) (hn : 1 ≤ n) (m : ℕ) (q : ℕ → ℕ) (hq : ∀ i, 2 ≤ q i)
    (hgrowth : ∀ i, i < m →
      denominatorSeparationFactor n m (chosenComparisonConstant n m) *
        (∏ j : Fin i, (ceilLogWeight (q j) : ℝ)) < (ceilLogWeight (q i) : ℝ))
    (z : Fin (m+1) → E)
    (hgen : IntermediateField.adjoin ℂ (Set.range z) = ⊤)
    (htrdeg : Algebra.trdeg ℂ E = 1) :
    let w := chosenWeights n hn m (fun i => q i) (fun i => hq i)
    ∀ (y : Fin w.K → ℂ) (_hy0 : ∀ j, y j ≠ 0), Function.Injective y →
      ∀ (c : Fin w.K → Fin m → ℂ) (F : ℚ), 1 / w.theta < F →
      ∀ (g : parameterCurve f hf ⟶ space w y c (truncationOrders w F)),
      parameterCurveGenericPoint f hf ≫ g ≫ projection w y c (truncationOrders w F) =
        Spec.map (CommRingCat.ofHom (MvPolynomial.aeval z).toRingHom) ≫
          MatrixCompactification.affineChart w →
      0 ≤ normalizationDegree f hf g (A w y c (truncationOrders w F)) +
        (1 + (curveSigma w.theta m : ℝ)) *
          normalizationDegree f hf g (J w y c (truncationOrders w F)) := by
  dsimp only
  intro y hy0 hy c F hF g hgeneric
  let w := chosenWeights n hn m (fun i => q i) (fun i => hq i)
  let hres := PlaceLocalRing.residue_integral htrdeg.le
  let hfinite := CurveParameterFinite.finite_over_every_parameter ℂ E htrdeg
  let hz := nonconstant_coordinates_of_trdeg_one z hgen htrdeg
  have hK : 0 < w.K := centerCount_pos (shape n hn).one_lt_c.le m
  have hA := A_degree_eq_weightedDegree w f hf hfinite z y c (truncationOrders w F)
    g hgeneric
  have hJ := exceptional_degree_eq_neg_contact_sum w y c f hf hfinite z hz
    hres hy hy0 hK F hF g hgeneric
  have hJR : normalizationDegree f hf g (J w y c (truncationOrders w F)) =
      -((MatrixCompactification.scale w).radius : ℝ) *
        ∑ p ∈ ContactFamilyAt.places hfinite z y c hz,
          (ContactFamilyAt.contact hres hfinite z y hy0 c hz hK (jetWeight w) p : ℝ) := by
    unfold normalizationDegree
    exact_mod_cast hJ
  change normalizationDegree f hf g (A w y c (truncationOrders w F)) = _ at hA
  rw [hA, hJR]
  have hc := chosenWeights_intrinsic_contact_bound n hn m q hq hgrowth z hgen htrdeg
    y hy0 hy c
  have hR : (0 : ℝ) ≤ (MatrixCompactification.scale w).radius := by
    exact_mod_cast (MatrixCompactification.scale w).radius_pos.le
  have hbound := mul_le_mul_of_nonneg_left hc hR
  nlinarith only [hbound]

end
end LogTwo.Geometry.MatrixBlowup
end Source0528

-- Source: OAI/NumberTheory/PiExponent/Ampleness/BlowupPresentationRestriction.lean
section Source0529
/-
Modification notice for the LogTwo project.
Derived from openai/math (Apache-2.0), revision adc7f1241b42e322a6451854ab7e4b4c146bf78a.
Original source: lean/OAI/NumberTheory/PiExponent/Ampleness/BlowupPresentationRestriction.lean
Changes: Convert module/import declarations to the Lean 4.34 public module format.
See ../THIRD_PARTY_NOTICES.txt for provenance and the recorded changes.
-/

namespace OAI

namespace PiExponentSeshadri.Geometry
noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace
open PiExponentSeshadri.Frames
variable {X B : Scheme.{0}} {I : X.IdealSheafData} {π : B ⟶ X}

lemma presents_post_toSpec [IsAffine X] (J : LineBundle B)
    (ι : J.sheaf ⟶ O B) (hJ : PresentsPullbackIdeal I π J ι) :
    PresentsPullbackIdeal (IdealPullback.specIdeal (I.ideal ⟨⊤,isAffineOpen_top X⟩))
      (π ≫ X.isoSpec.hom) J ι := by
  refine ⟨hJ.1,?_⟩
  intro U V e
  rw [InvertibleLocal.image_eq_comap I π J ι hJ U,
    ← IdealPullback.comap_ideal _ (π ≫ X.isoSpec.hom) U V e,
      Scheme.IdealSheafData.comap_comp]
  rw [show (IdealPullback.specIdeal (I.ideal ⟨⊤,isAffineOpen_top X⟩)).comap
    X.isoSpec.hom = I from IdealPullback.specIdeal_comap_toSpec I]

lemma presents_morphismRestrict (J : LineBundle B) (ι : J.sheaf ⟶ O B)
    (hJ : PresentsPullbackIdeal I π J ι) (U : X.affineOpens) :
    PresentsPullbackIdeal (I.comap U.1.ι) (π ∣_ U.1)
      (J.restrict (π ⁻¹ᵁ U.1).ι) (InvertibleLocal.restrictedInclusion J ι (π ⁻¹ᵁ U.1).ι) := by
  refine ⟨@InvertibleLocal.restrictedInclusion_mono _ _ J ι
    (π ⁻¹ᵁ U.1).ι inferInstance hJ.1, ?_⟩
  intro V W hVW
  change ((InvertibleLocal.restrictedInclusion J ι (π ⁻¹ᵁ U.1).ι).val.app
    (Opposite.op V.1)).hom.range = _
  rw [InvertibleLocal.restricted_image_on_chart J ι hJ (π ⁻¹ᵁ U.1).ι V U (by
    rintro _ ⟨x,hx,rfl⟩; exact x.property),
    ← Scheme.IdealSheafData.comap_comp,← morphismRestrict_ι π U.1,
      Scheme.IdealSheafData.comap_comp]
  exact IdealPullback.comap_ideal _ (π ∣_ U.1) V W hVW

end
end PiExponentSeshadri.Geometry

end OAI
end Source0529

-- Source: OAI/NumberTheory/PiExponent/Approximation/SectionDivision.lean
section Source0530
/-
Modification notice for the LogTwo project.
Derived from openai/math (Apache-2.0), revision adc7f1241b42e322a6451854ab7e4b4c146bf78a.
Original source: lean/OAI/NumberTheory/PiExponent/Approximation/SectionDivision.lean
Changes: Convert module/import declarations to the Lean 4.34 public module format.
See ../THIRD_PARTY_NOTICES.txt for provenance and the recorded changes.
-/

namespace OAI

namespace PiExponentSeshadri.Geometry
noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite
open PiExponentSeshadri.Frames
variable {X : Scheme.{0}}

lemma section_value_naturality {M : X.Modules} (s : O X ⟶ M)
    {U V : X.Opens} (h : V ≤ U) :
    M.presheaf.map (homOfLE h).op (s.app U (1 : Γ(X,U))) =
      s.app V (1 : Γ(X,V)) := by
  have ht := CategoryTheory.congr_fun (s.mapPresheaf.naturality (homOfLE h).op)
    (1 : Γ(X,U))
  change s.app V (X.presheaf.map (homOfLE h).op (1 : Γ(X,U))) =
    M.presheaf.map (homOfLE h).op (s.app U (1 : Γ(X,U))) at ht
  simpa only [map_one] using ht.symm

lemma section_eq_zero_of_top_value {M : X.Modules} (s : O X ⟶ M)
    (hs : s.app ⊤ (1 : Γ(X,⊤)) = 0) : s = 0 := by
  ext U a
  change Γ(X,U) at a
  change s.app U a = 0
  have h := s.app_smul (r := a) (x := (1 : Γ(X,U)))
  change s.app U (a*1 : Γ(X,U)) = a • s.app U (1 : Γ(X,U)) at h
  rw [mul_one] at h
  rw [h, ← section_value_naturality s (show U ≤ ⊤ from le_top), hs,map_zero,smul_zero]

lemma section_eq_zero_of_local_restrictions {M : X.Modules} (s : O X ⟶ M)
    (hs : ∀ x : X, ∃ U : X.Opens, x ∈ U ∧ restrictSection U.ι s = 0) : s = 0 := by
  apply section_eq_zero_of_top_value
  let F : (X : TopCat).Sheaf AddCommGrpCat := (SheafOfModules.toSheaf X.ringCatSheaf).obj M
  apply TopCat.Presheaf.section_ext F ⊤ (s.app ⊤ (1 : Γ(X,⊤))) 0
  intro x hx
  obtain ⟨U,hxU,hU⟩ := hs x
  have hv : s.app U (1 : Γ(X,U)) = 0 := by
    have ht := congrArg (fun q : O U.toScheme ⟶ M.restrict U.ι =>
      q.app ⊤ (1 : Γ(U.toScheme,⊤))) hU
    change s.app (U.ι ''ᵁ ⊤) ((U.ι.appIso ⊤).inv (1 : Γ(U.toScheme,⊤))) = 0 at ht
    rw [map_one] at ht
    have htop : U.ι ''ᵁ (⊤ : U.toScheme.Opens) = U := by
      rw [Scheme.Hom.image_top_eq_opensRange,Scheme.Opens.opensRange_ι]
    suffices h : ∀ V : X.Opens, V = U → s.app V (1 : Γ(X,V)) = 0 →
        s.app U (1 : Γ(X,U)) = 0 from h _ htop ht
    intro V he ht
    subst V
    exact ht
  change M.presheaf.germ ⊤ x hx (s.app ⊤ (1 : Γ(X,⊤))) =
    M.presheaf.germ ⊤ x hx 0
  rw [← TopCat.Presheaf.germ_res_apply M.presheaf (homOfLE (show U ≤ ⊤ from le_top)) x hxU]
  rw [section_value_naturality s, hv, map_zero, map_zero]

theorem global_division_of_local_lifts {M N : X.Modules} (f : M ⟶ N) [Mono f]
    (s : O X ⟶ N)
    (hs : ∀ x : X, ∃ U : X.Opens, x ∈ U ∧
      ∃ t : O U.toScheme ⟶ M.restrict U.ι,
        t ≫ (Scheme.Modules.restrictFunctor U.ι).map f = restrictSection U.ι s) :
    ∃! t : O X ⟶ M, t ≫ f = s := by
  have hz : s ≫ cokernel.π f = 0 := by
    apply section_eq_zero_of_local_restrictions
    intro x
    obtain ⟨U,hx,t,ht⟩ := hs x
    refine ⟨U,hx,?_⟩
    have hc : restrictSection U.ι (s ≫ cokernel.π f) =
        restrictSection U.ι s ≫ (Scheme.Modules.restrictFunctor U.ι).map (cokernel.π f) := by
      simp only [restrictSection]
      erw [Functor.map_comp, Category.assoc]
    rw [hc, ← ht, Category.assoc, ← Functor.map_comp,cokernel.condition,Functor.map_zero,comp_zero]
  refine ⟨Abelian.monoLift _ s hz,Abelian.monoLift_comp _ s hz,?_⟩
  intro t ht
  apply (cancel_mono f).mp
  rw [ht,Abelian.monoLift_comp]

lemma framed_local_division {M N : X.Modules} (e : M ≅ O X) (d : N ≅ O X)
    (f : M ⟶ N) (s : O X ⟶ N)
    (hs : coefficient d s ∈ Ideal.span {endValue (e.inv ≫ f ≫ d.hom)}) :
    ∃ t : O X ⟶ M, t ≫ f = s := by
  obtain ⟨r,hr⟩ := Ideal.mem_span_singleton.mp hs
  refine ⟨scalarEnd r ≫ e.inv,?_⟩
  apply (cancel_mono d.hom).mp
  apply endValue_injective
  rw [Category.assoc,Category.assoc,endValue_comp,endValue_scalarEnd]
  change r * endValue (e.inv ≫ f ≫ d.hom) = coefficient d s
  rw [mul_comm,← hr]

end
end PiExponentSeshadri.Geometry

end OAI
end Source0530

-- Source: OAI/NumberTheory/PiExponent/Ampleness/ReesRelativeSections.lean
section Source0531
/-
Modification notice for the LogTwo project.
Derived from openai/math (Apache-2.0), revision adc7f1241b42e322a6451854ab7e4b4c146bf78a.
Original source: lean/OAI/NumberTheory/PiExponent/Ampleness/ReesRelativeSections.lean
Changes: Convert module/import declarations to the Lean 4.34 public module format.
See ../THIRD_PARTY_NOTICES.txt for provenance and the recorded changes.
-/

namespace OAI

noncomputable section

namespace PiExponentSeshadri.InvertibleLocal
open CategoryTheory AlgebraicGeometry Opposite
open PiExponentSeshadri.Geometry PiExponentSeshadri.Frames
variable {X Y Z : Scheme.{0}}

lemma frame_ideal [IsAffine X] {I : X.IdealSheafData} {f : Y ⟶ X}
    (J : LineBundle Y) (ι : J.sheaf ⟶ O Y) (h : PresentsPullbackIdeal I f J ι)
    (j : Z ⟶ Y) [IsOpenImmersion j] [IsAffine Z]
    (e : J.sheaf.restrict j ≅ O Z) :
    ((I.comap f).comap j).ideal ⟨⊤,isAffineOpen_top Z⟩ =
      Ideal.span {endValue (e.inv ≫ restrictedInclusion J ι j)} := by
  change _ = Ideal.span {UnitEndomorphism.equation (e.inv ≫ restrictedInclusion J ι j) ⊤}
  rw [← UnitEndomorphism.image_principal _ ⊤, ← restricted_image J ι h j ⟨⊤, isAffineOpen_top Z⟩]
  ext r
  change (∃ s, (restrictedInclusion J ι j).val.app (op ⊤) s = r) ↔
    ∃ s, (restrictedInclusion J ι j).val.app (op ⊤) (e.inv.val.app (op ⊤) s) = r
  constructor
  · rintro ⟨s, hs⟩
    refine ⟨e.hom.val.app (op ⊤) s, ?_⟩
    have ht : e.inv.val.app (op ⊤) (e.hom.val.app (op ⊤) s) = s :=
      congrArg (fun k : J.sheaf.restrict j ⟶ J.sheaf.restrict j => k.val.app (op ⊤) s) e.hom_inv_id
    rw [ht]; exact hs
  · rintro ⟨s, hs⟩
    exact ⟨e.inv.val.app (op ⊤) s, hs⟩
end PiExponentSeshadri.InvertibleLocal

namespace PiExponentSeshadri.ReesGrading
section
open CategoryTheory AlgebraicGeometry TopologicalSpace
open PiExponentSeshadri.Geometry PiExponentSeshadri.Frames PiExponentSeshadri.SpecMaps

private theorem mono_inv_comp {D : Type*} [Category D] {A B C : D}
    (e : A ≅ B) (f : A ⟶ C) (hf : Mono f) : Mono (e.inv ≫ f) := by
  let := hf
  infer_instance

private theorem map_comp_through {C D : Type*} [Category C] [Category D]
    (F : C ⥤ D) {A B T : C} {U V : D}
    (u : U ⟶ F.obj A) (s : A ⟶ B) (t : B ⟶ T) (v : F.obj T ⟶ V) :
    (u ≫ F.map s) ≫ F.map t ≫ v = (u ≫ F.map (s ≫ t)) ≫ v := by
  simp only [Functor.map_comp, Category.assoc]

variable {R : Type} [CommRing R] (I : Ideal R)
variable {B : Scheme.{0}} (f : B ⟶ Spec (.of R))
  (J : LineBundle B) (ι : J.sheaf ⟶ O B)
  (hJ : PresentsPullbackIdeal (IdealPullback.specIdeal I) f J ι)
include hJ

theorem relative_generator_section (a : I) :
    ∃ s : O B ⟶ J.sheaf,
      s ≫ ι = scalarEnd ((coordinate f) a.val) := by
  let : Mono ι := hJ.1
  obtain ⟨s,hs,-⟩ := global_division_of_local_lifts ι
      (scalarEnd ((coordinate f) a.val)) (by
    intro x
    obtain ⟨U,hx,⟨e⟩,-⟩ := common_affine_frames J J x
    let r := endValue (e.inv ≫ InvertibleLocal.restrictedInclusion J ι U.1.ι)
    have hI : I.map (coordinate (U.1.ι ≫ f)).hom = Ideal.span {r} := by
      rw [← IdealPullback.specIdeal_coordinate,Scheme.IdealSheafData.comap_comp]
      exact InvertibleLocal.frame_ideal J ι hJ U.1.ι e
    have hmem : coefficient (Scheme.Modules.restrictUnitIso U.1.ι)
        (restrictSection U.1.ι (scalarEnd ((coordinate f) a.val))) ∈ Ideal.span {r} := by
      rw [← hI]
      have he : coefficient (Scheme.Modules.restrictUnitIso U.1.ι)
          (restrictSection U.1.ι (scalarEnd ((coordinate f) a.val))) =
          coordinate (U.1.ι ≫ f) a.val := by
        erw [coefficient, endValue_restrict, endValue_scalarEnd]
        rw [coordinate_comp]
        rfl
      rw [he]
      exact Ideal.mem_map_of_mem _ a.property
    obtain ⟨t,ht⟩ := framed_local_division e (Scheme.Modules.restrictUnitIso U.1.ι)
      ((Scheme.Modules.restrictFunctor U.1.ι).map ι)
      (restrictSection U.1.ι (scalarEnd ((coordinate f) a.val))) hmem
    exact ⟨U.1,hx,t,ht⟩)
  exact ⟨s,hs⟩

theorem relative_generator_section_open (β : B ⟶ affineBlowup I) (hβ : β ≫ projection I = f) (a : I)
    (s : O B ⟶ J.sheaf)
    (hs : s ≫ ι = scalarEnd ((coordinate f) a.val)) :
    SectionOpens.isoOpen s = β ⁻¹ᵁ Proj.basicOpen (piece I) (generator I a) := by
  let : Mono ι := hJ.1
  ext x
  obtain ⟨U,hx,⟨e⟩,-⟩ := common_affine_frames J J x
  let g := e.inv ≫ InvertibleLocal.restrictedInclusion J ι U.1.ι
  have hg : Mono g := mono_inv_comp e (InvertibleLocal.restrictedInclusion J ι U.1.ι)
    (@InvertibleLocal.restrictedInclusion_mono _ _ J ι U.1.ι inferInstance hJ.1)
  let r := endValue g
  have hr : IsRegular r := @UnitEndomorphism.equation_regular U.1.toScheme g hg ⊤
  have hI : I.map (coordinate (U.1.ι ≫ f)).hom = Ideal.span {r} := by
    rw [← IdealPullback.specIdeal_coordinate,Scheme.IdealSheafData.comap_comp]
    exact InvertibleLocal.frame_ideal J ι hJ U.1.ι e
  let h := principalScheme I U.1.toScheme (coordinate (U.1.ι ≫ f)).hom r hI hr
  have hh : h = U.1.ι ≫ β := by
    apply invertible_unique I h (U.1.ι ≫ β) (U.1.ι ≫ f)
    · exact (principalScheme_projection I U.1.toScheme _ r hI hr).trans (factor _)
    · rw [Category.assoc,hβ]
    · exact InvertibleLocal.invertible_restrict _ _ ⟨J,ι,hJ⟩ U.1.ι
  have hscalar : coefficient e (restrictSection U.1.ι s) * r =
      coordinate (U.1.ι ≫ f) a.val := by
    have hcomp : (restrictSection U.1.ι s ≫ e.hom) ≫ g =
        restrictSection U.1.ι (scalarEnd ((coordinate f) a.val)) ≫
          (Scheme.Modules.restrictUnitIso U.1.ι).hom := by
      dsimp [g,InvertibleLocal.restrictedInclusion]
      simp only [Category.assoc,Iso.hom_inv_id_assoc]
      rw [← hs]
      simp only [restrictSection]
      exact map_comp_through (Scheme.Modules.restrictFunctor U.1.ι)
        (Scheme.Modules.restrictUnitIso U.1.ι).inv s ι
        (Scheme.Modules.restrictUnitIso U.1.ι).hom
    have H := congrArg (endValue (X := U.1.toScheme)) hcomp
    rw [coordinate_comp]
    exact ((endValue_comp (restrictSection U.1.ι s ≫ e.hom) g).symm.trans H).trans
      ((endValue_restrict U.1.ι (scalarEnd ((coordinate f) a.val))).trans
        (congrArg U.1.ι.appTop (endValue_scalarEnd ((coordinate f) a.val))))
  have hc : coefficient e (restrictSection U.1.ι s) =
      BlowupLift.coefficient I (coordinate (U.1.ι ≫ f)).hom r hI a := by
    apply hr.left
    exact (mul_comm _ _).trans (hscalar.trans
      (BlowupLift.mul_coefficient I _ r hI a).symm)
  have hloc : U.1.ι ⁻¹ᵁ SectionOpens.isoOpen s =
      U.1.ι ⁻¹ᵁ β ⁻¹ᵁ Proj.basicOpen (piece I) (generator I a) := by
    rw [preimage_isoOpen s U.1.ι e,hc]
    have H := principalScheme_preimage I U.1.toScheme _ r hI hr a
    change h ⁻¹ᵁ _ = _ at H
    rw [hh] at H
    exact H.symm
  exact SetLike.ext_iff.mp hloc ⟨x,hx⟩

end

open CategoryTheory AlgebraicGeometry TopologicalSpace
open PiExponentSeshadri.Geometry PiExponentSeshadri.Frames PiExponentSeshadri.SpecMaps
variable {R : Type} [CommRing R] (I : Ideal R)
variable {B : Scheme.{0}} (f : B ⟶ Spec (.of R))
  (J : LineBundle B) (ι : J.sheaf ⟶ O B)
  (hJ : PresentsPullbackIdeal (IdealPullback.specIdeal I) f J ι)
include hJ

theorem relative_affine_section_cover (hf : IsBlowup (IdealPullback.specIdeal I) f) :
    ∃ s : I → (O B ⟶ J.sheaf),
      (⨆ a, SectionOpens.isoOpen (s a)) = ⊤ ∧
      ∀ a, IsAffineOpen (SectionOpens.isoOpen (s a)) := by
  classical
  let e : B ≅ affineBlowup I := hf.iso (rees_isBlowup I)
  let : IsIso e.hom := ⟨⟨e.inv,e.hom_inv_id,e.inv_hom_id⟩⟩
  choose s hs using relative_generator_section I f J ι hJ
  have ho a := relative_generator_section_open I f J ι hJ e.hom
    (hf.iso_hom_comp (rees_isBlowup I)) a (s a) (hs a)
  refine ⟨s,?_,fun a => ?_⟩
  · simp only [ho]
    exact e.hom.iSup_preimage_eq_top (iSup_generator_basicOpen I)
  · rw [ho]
    exact @IsAffineOpen.preimage_of_isIso B (affineBlowup I) _
      (Proj.isAffineOpen_basicOpen (piece I) (generator I a) (generator_mem I a)
        (by decide : 0 < (1:ℕ))) e.hom e.isIso_hom
end PiExponentSeshadri.ReesGrading

end

end OAI
end Source0531

-- Source: OAI/NumberTheory/PiExponent/Ampleness/BlowupAffineSections.lean
section Source0532
/-
Modification notice for the LogTwo project.
Derived from openai/math (Apache-2.0), revision adc7f1241b42e322a6451854ab7e4b4c146bf78a.
Original source: lean/OAI/NumberTheory/PiExponent/Ampleness/BlowupAffineSections.lean
Changes: Convert module/import declarations to the Lean 4.34 public module format.
See ../THIRD_PARTY_NOTICES.txt for provenance and the recorded changes.
-/

namespace OAI

namespace PiExponentSeshadri.Geometry
noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace
open PiExponentSeshadri.Frames
variable {X B : Scheme.{0}} {I : X.IdealSheafData} {π : B ⟶ X}

theorem IsBlowup.affine_section_cover [IsAffine X] (hπ : IsBlowup I π)
    (J : LineBundle B) (ι : J.sheaf ⟶ O B) (hJ : PresentsPullbackIdeal I π J ι) :
    ∃ (α : Type) (s : α → (O B ⟶ J.sheaf)),
      (⨆ a, SectionOpens.isoOpen (s a)) = ⊤ ∧
      ∀ a, IsAffineOpen (SectionOpens.isoOpen (s a)) := by
  let A := I.ideal ⟨⊤,isAffineOpen_top X⟩
  have hp := hπ.postIso X.isoSpec (IdealPullback.specIdeal A)
    (IdealPullback.specIdeal_comap_toSpec I)
  obtain ⟨s,hs,ha⟩ := ReesGrading.relative_affine_section_cover A
    (π ≫ X.isoSpec.hom) J ι (presents_post_toSpec J ι hJ) hp
  exact ⟨A,s,hs,ha⟩

end
end PiExponentSeshadri.Geometry

end OAI
end Source0532

-- Source: OAI/NumberTheory/PiExponent/Approximation/MixedSectionExtension.lean
section Source0533
/-
Modification notice for the LogTwo project.
Derived from openai/math (Apache-2.0), revision adc7f1241b42e322a6451854ab7e4b4c146bf78a.
Original source: lean/OAI/NumberTheory/PiExponent/Approximation/MixedSectionExtension.lean
Changes: Convert module/import declarations to the Lean 4.34 public module format.
See ../THIRD_PARTY_NOTICES.txt for provenance and the recorded changes.
-/

namespace OAI

noncomputable section

namespace PiExponentSeshadri.Geometry
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite
open PiExponentSeshadri.Frames PiExponentSeshadri.TensorPure
variable {X : Scheme.{0}}

theorem local_affine_mixed_extension (L M : LineBundle X) (U : X.Opens) [IsAffine U.toScheme]
    (e : L.sheaf.restrict U.ι ≅ O U.toScheme) (d : M.sheaf.restrict U.ι ≅ O U.toScheme)
    (s : O X ⟶ L.sheaf)
    (w : Γ(M.sheaf, U.ι ''ᵁ (U.toScheme.basicOpen (coefficient e (restrictSection U.ι s))))) :
    ∃ N : ℕ, ∀ n ≥ N, ∃ t : O U.toScheme ⟶ (((L.pow n).tensor M).sheaf.restrict U.ι),
      let V := U.toScheme.basicOpen (coefficient e (restrictSection U.ι s))
      (((L.pow n).tensor M).sheaf).presheaf.map (homOfLE (U.ι_image_le V)).op
        (openSectionEquiv _ U t) =
      pure (L.pow n).sheaf M.sheaf (U.ι ''ᵁ V) ((powerSection s n).app (U.ι ''ᵁ V) (1 : Γ(X,U.ι ''ᵁ V))) w := by
  let V := U.toScheme.basicOpen (coefficient e (restrictSection U.ι s))
  let b : Γ(U.toScheme,V) := d.hom.app V w
  let f : Γ(V.toScheme,⊤) := V.topIso.inv b
  obtain ⟨N,hN⟩ := local_affine_power_extension U e s f
  refine ⟨N,fun n hn => ?_⟩
  obtain ⟨t,ht⟩ := hN n hn
  let q : O U.toScheme ⟶ (((L.pow n).tensor M).sheaf.restrict U.ι) :=
    TensorPure.tensorSection t d.inv ≫ (moduleTensorRestrict U (L.pow n).sheaf M.sheaf).inv
  refine ⟨q,?_⟩
  change (((L.pow n).tensor M).sheaf).presheaf.map (homOfLE (U.ι_image_le V)).op
    (openSectionEquiv _ U q) = _
  erw [openSectionEquiv_restrict_value ((L.pow n).tensor M).sheaf U q V]
  have he := congrArg (openSectionEquiv ((L.pow n).sheaf.restrict U.ι) V) ht
  erw [openSectionEquiv_restrict t V,
    openSectionEquiv_scalar ((L.pow n).sheaf.restrict U.ι) V f
      (restrictSection V.ι (restrictSection U.ι (powerSection s n))),
    openSectionEquiv_restrict (restrictSection U.ι (powerSection s n)) V] at he
  have hf : V.topIso.hom f = b := Iso.inv_hom_id_apply _ _
  rw [hf] at he
  have hp : (restrictSection U.ι (powerSection s n)).app V (1 : Γ(U.toScheme,V)) =
      (powerSection s n).app (U.ι ''ᵁ V) (1 : Γ(X,U.ι ''ᵁ V)) := by
    change (powerSection s n).app (U.ι ''ᵁ V) ((U.ι.appIso V).inv (1 : Γ(U.toScheme,V))) = _
    rw [map_one]
  have he := he.trans (congrArg (fun z : Γ((L.pow n).sheaf.restrict U.ι, V) => (b : Γ(U.toScheme,V)) • z) hp)
  apply (ConcreteCategory.bijective_of_isIso
    (((Scheme.Modules.toPresheaf U.toScheme).mapIso
      (moduleTensorRestrict U (L.pow n).sheaf M.sheaf)).app (op V)).hom).injective
  change (moduleTensorRestrict U (L.pow n).sheaf M.sheaf).hom.app V
      ((moduleTensorRestrict U (L.pow n).sheaf M.sheaf).inv.app V
        ((TensorPure.tensorSection t d.inv).app V (1 : Γ(U.toScheme,V)))) = _
  have hc : (moduleTensorRestrict U (L.pow n).sheaf M.sheaf).hom.app V
      ((moduleTensorRestrict U (L.pow n).sheaf M.sheaf).inv.app V
        ((TensorPure.tensorSection t d.inv).app V (1 : Γ(U.toScheme,V)))) = (TensorPure.tensorSection t d.inv).app V (1 : Γ(U.toScheme,V)) := by
    change ((moduleTensorRestrict U (L.pow n).sheaf M.sheaf).inv ≫
      (moduleTensorRestrict U (L.pow n).sheaf M.sheaf).hom).app V _ = _
    rw [Iso.inv_hom_id]
    rfl
  erw [hc,TensorPure.section_apply t d.inv V]
  refine (congrArg (fun z => pure ((L.pow n).sheaf.restrict U.ι) (M.sheaf.restrict U.ι) V
    z (d.inv.app V (1 : Γ(U.toScheme,V)))) he).trans ?_
  erw [pure_smul_left,← pure_smul_right]
  have hd : b • d.inv.app V (1 : Γ(U.toScheme,V)) = w := by
    erw [← d.inv.app_smul b (1 : Γ(U.toScheme,V)),smul_eq_mul,mul_one]
    change d.inv.app V (d.hom.app V w) = w
    change (d.hom ≫ d.inv).app V w = w
    rw [Iso.hom_inv_id]
    rfl
  erw [hd]
  exact (restrict_pure U (L.pow n).sheaf M.sheaf V _ w).symm

theorem LineBundle.finite_cover_mixed_extension [IsIntegral X] (L M : LineBundle X)
    {ι : Type*} [Fintype ι] [Nonempty ι] (U : ι → X.Opens)
    (hcover : (⊤ : X.Opens) ≤ iSup U)
    (haff : ∀ i, IsAffine (U i).toScheme) (hU : ∀ i, (U i : Set X).Nonempty)
    (e : ∀ i, L.sheaf.restrict (U i).ι ≅ O (U i).toScheme)
    (d : ∀ i, M.sheaf.restrict (U i).ι ≅ O (U i).toScheme)
    (s : O X ⟶ L.sheaf) (hD : (sectionOpen X s : Set X).Nonempty)
    (w : Γ(M.sheaf, sectionOpen X s)) :
    ∃ N : ℕ, ∀ n ≥ N, ∃ t : O X ⟶ ((L.pow n).tensor M).sheaf,
      t.app (sectionOpen X s) (1 : Γ(X,sectionOpen X s)) =
        pure (L.pow n).sheaf M.sheaf (sectionOpen X s)
          ((powerSection s n).app (sectionOpen X s) (1 : Γ(X,sectionOpen X s))) w := by
  classical
  let D := sectionOpen X s
  let V (i : ι) := (U i).toScheme.basicOpen (coefficient (e i) (restrictSection (U i).ι s))
  let W (i : ι) := (U i).ι ''ᵁ V i
  have hV (i : ι) : V i = (U i).ι ⁻¹ᵁ D := (preimage_isoOpen s (U i).ι (e i)).symm
  have hW_eq (i : ι) : W i = U i ⊓ D := by
    simp only [W,hV,Scheme.Hom.image_preimage_eq_opensRange_inf,Scheme.Opens.opensRange_ι]
  have hWU (i : ι) : W i ≤ U i := (U i).ι_image_le (V i)
  have hWD (i : ι) : W i ≤ D := (hW_eq i).le.trans inf_le_right
  have hW (i : ι) : (W i : Set X).Nonempty := by
    rw [hW_eq]
    exact nonempty_preirreducible_inter (U i).isOpen D.isOpen (hU i) hD
  let wi (i : ι) : Γ(M.sheaf,W i) := M.sheaf.presheaf.map (homOfLE (hWD i)).op w
  have hh (i : ι) := @local_affine_mixed_extension X L M (U i) (haff i) (e i) (d i) s (wi i)
  choose N hN using hh
  refine ⟨Finset.univ.sup N, fun n hn => ?_⟩
  have hn' (i : ι) : N i ≤ n := (Finset.le_sup (f := N) (Finset.mem_univ i)).trans hn
  choose t ht using fun i => hN i n (hn' i)
  let P := ((L.pow n).tensor M)
  let target : Γ(P.sheaf,D) := pure (L.pow n).sheaf M.sheaf D
    ((powerSection s n).app D (1 : Γ(X,D))) w
  have heq (i : ι) : P.sheaf.presheaf.map (homOfLE (hWU i)).op
      (openSectionEquiv P.sheaf (U i) (t i)) =
      P.sheaf.presheaf.map (homOfLE (hWD i)).op target := by
    refine (ht i).trans ?_
    have hr := pure_restrict (L.pow n).sheaf M.sheaf (homOfLE (hWD i))
      ((powerSection s n).app D (1 : Γ(X,D))) w
    have hp := section_value_natural (powerSection s n) (homOfLE (hWD i))
    exact (congrArg (fun z => pure (L.pow n).sheaf M.sheaf (W i) z (wi i)) hp).symm.trans hr.symm
  obtain ⟨g,hg,-⟩ := P.glue_dense_subopens D U W hcover hWU hWD hW
    (fun i => openSectionEquiv P.sheaf (U i) (t i)) target heq
  refine ⟨(moduleSectionEquiv P.sheaf).symm g,?_⟩
  have H := section_value_natural ((moduleSectionEquiv P.sheaf).symm g)
    (homOfLE (show D ≤ ⊤ from le_top))
  have Htop : ((moduleSectionEquiv P.sheaf).symm g).app ⊤ (1 : Γ(X,⊤)) = g :=
    (moduleSectionEquiv P.sheaf).apply_symm_apply g
  rw [Htop] at H
  exact H.symm.trans hg.2

theorem LineBundle.mixed_extension [IsIntegral X] [CompactSpace X] (L M : LineBundle X)
    (s : O X ⟶ L.sheaf) (hD : (sectionOpen X s : Set X).Nonempty)
    (w : Γ(M.sheaf,sectionOpen X s)) :
    ∃ N : ℕ, ∀ n ≥ N, ∃ t : O X ⟶ ((L.pow n).tensor M).sheaf,
      t.app (sectionOpen X s) (1 : Γ(X,sectionOpen X s)) =
        pure (L.pow n).sheaf M.sheaf (sectionOpen X s)
          ((powerSection s n).app (sectionOpen X s) (1 : Γ(X,sectionOpen X s))) w := by
  classical
  choose U hUx he hd using common_affine_frames L M
  obtain ⟨I,hI⟩ := isCompact_univ.elim_finite_subcover
    (fun x => (U x).1 : X → Set X) (fun x => (U x).1.isOpen)
    (by intro x _; exact Set.mem_iUnion.mpr ⟨x,hUx x⟩)
  have hic (x : X) : ∃ i ∈ I, x ∈ (U i).1 := by
    obtain ⟨i,hi⟩ := Set.mem_iUnion.mp (hI (show x ∈ Set.univ from trivial))
    obtain ⟨hi,hx⟩ := Set.mem_iUnion.mp hi
    exact ⟨i,hi,hx⟩
  have : Nonempty I := by
    obtain ⟨x,-⟩ := hD
    obtain ⟨i,hi,-⟩ := hic x
    exact ⟨⟨i,hi⟩⟩
  exact L.finite_cover_mixed_extension M (fun i : I => (U i.val).1)
    (by intro x _; obtain ⟨i,hi,hx⟩ := hic x; exact Opens.mem_iSup.mpr ⟨⟨i,hi⟩,hx⟩)
    (fun i => (U i.val).2) (fun i => ⟨i.val,hUx i.val⟩)
    (fun i => Classical.choice (he i.val)) (fun i => Classical.choice (hd i.val)) s hD w

end PiExponentSeshadri.Geometry

end

end OAI
end Source0533

-- Source: OAI/NumberTheory/PiExponent/Approximation/TensorMixedSection.lean
section Source0534
/-
Modification notice for the LogTwo project.
Derived from openai/math (Apache-2.0), revision adc7f1241b42e322a6451854ab7e4b4c146bf78a.
Original source: lean/OAI/NumberTheory/PiExponent/Approximation/TensorMixedSection.lean
Changes: Convert module/import declarations to the Lean 4.34 public module format.
See ../THIRD_PARTY_NOTICES.txt for provenance and the recorded changes.
-/

namespace OAI

noncomputable section

namespace PiExponentSeshadri.TensorPure

section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite
open MonoidalCategory
open PiExponentSeshadri.Geometry PiExponentSeshadri.Frames
variable {X : Scheme.{0}}

lemma assoc_pure (L M N : LineBundle X) (U : X.Opens)
    (l : Γ(L.sheaf,U)) (m : Γ(M.sheaf,U)) (n : Γ(N.sheaf,U)) :
    (lineTensorAssoc L M N).hom.val.app (op U)
      (pure (L.tensor M).sheaf N.sheaf U (pure L.sheaf M.sheaf U l m) n) =
      pure L.sheaf (M.tensor N).sheaf U l (pure M.sheaf N.sheaf U m n) := by
  let : MonoidalCategory (PresheafOfModules X.ringCatSheaf.obj) :=
    PresheafOfModulesOfCommRing.monoidalCategory (R := X.presheaf)
  let P := L.sheaf.val ⊗ M.sheaf.val
  let Q := M.sheaf.val ⊗ N.sheaf.val
  let F : PresheafOfModules X.ringCatSheaf.obj ⥤ X.Modules := PresheafOfModules.sheafification (𝟙 X.ringCatSheaf.obj)
  let a := (lineTensorAssoc L M N)
  let v := ((adj X).unit.app (P ⊗ N.sheaf.val)).app (op U)
    ((l ⊗ₜ[Γ(X,U)] m) ⊗ₜ[Γ(X,U)] n)
  have hr : (sheafificationTensorRight P N).hom.val.app (op U) v =
      pure (L.tensor M).sheaf N.sheaf U (pure L.sheaf M.sheaf U l m) n := by
    have h := (adj X).unit.naturality
      (PresheafOfModulesOfCommRing.Monoidal.tensorHom (R := X.presheaf)
        ((adj X).unit.app P) (𝟙 N.sheaf.val))
    exact (congrArg (fun q => q.app (op U) ((l ⊗ₜ[Γ(X,U)] m) ⊗ₜ[Γ(X,U)] n)) h).symm
  have ha : (F.map (α_ L.sheaf.val M.sheaf.val N.sheaf.val).hom).val.app (op U) v =
      ((adj X).unit.app (L.sheaf.val ⊗ Q)).app (op U)
        (l ⊗ₜ[Γ(X,U)] (m ⊗ₜ[Γ(X,U)] n)) := by
    have h := (adj X).unit.naturality (α_ L.sheaf.val M.sheaf.val N.sheaf.val).hom
    exact (congrArg (fun q => q.app (op U) ((l ⊗ₜ[Γ(X,U)] m) ⊗ₜ[Γ(X,U)] n)) h).symm
  have hl : (sheafificationTensorLeft Q L).hom.val.app (op U)
      (((adj X).unit.app (L.sheaf.val ⊗ Q)).app (op U)
        (l ⊗ₜ[Γ(X,U)] (m ⊗ₜ[Γ(X,U)] n))) =
      pure L.sheaf (M.tensor N).sheaf U l (pure M.sheaf N.sheaf U m n) := by
    have h := (adj X).unit.naturality
      (PresheafOfModulesOfCommRing.Monoidal.tensorHom (R := X.presheaf)
        (𝟙 L.sheaf.val) ((adj X).unit.app Q))
    exact (congrArg (fun q => q.app (op U) (l ⊗ₜ[Γ(X,U)] (m ⊗ₜ[Γ(X,U)] n))) h).symm
  change a.hom.val.app (op U) _ = _
  have hc : a.hom.val.app (op U) ((sheafificationTensorRight P N).hom.val.app (op U) v) =
      (sheafificationTensorLeft Q L).hom.val.app (op U)
        ((F.map (α_ L.sheaf.val M.sheaf.val N.sheaf.val).hom).val.app (op U) v) := by
    change ((sheafificationTensorRight P N).hom ≫ a.hom).val.app (op U) v = _
    change ((sheafificationTensorRight P N).hom ≫
      (sheafificationTensorRight P N).inv ≫
      F.map (α_ L.sheaf.val M.sheaf.val N.sheaf.val).hom ≫
      (sheafificationTensorLeft Q L).hom).val.app (op U) v = _
    have hs := (sheafificationTensorRight P N).hom_inv_id_assoc
      (F.map (α_ L.sheaf.val M.sheaf.val N.sheaf.val).hom ≫
        (sheafificationTensorLeft Q L).hom)
    exact congrArg (fun q => q.val.app (op U) v) hs
  exact (congrArg (a.hom.val.app (op U)) hr).symm.trans (hc.trans ((congrArg
    ((sheafificationTensorLeft Q L).hom.val.app (op U)) ha).trans hl))

lemma assoc_inv_pure (L M N : LineBundle X) (U : X.Opens)
    (l : Γ(L.sheaf,U)) (m : Γ(M.sheaf,U)) (n : Γ(N.sheaf,U)) :
    (lineTensorAssoc L M N).inv.app U
      (pure L.sheaf (M.tensor N).sheaf U l (pure M.sheaf N.sheaf U m n)) =
      pure (L.tensor M).sheaf N.sheaf U (pure L.sheaf M.sheaf U l m) n := by
  have h := congrArg ((lineTensorAssoc L M N).inv.app U) (assoc_pure L M N U l m n)
  have hc : (lineTensorAssoc L M N).inv.app U
      ((lineTensorAssoc L M N).hom.val.app (op U)
        (pure (L.tensor M).sheaf N.sheaf U (pure L.sheaf M.sheaf U l m) n)) =
      pure (L.tensor M).sheaf N.sheaf U (pure L.sheaf M.sheaf U l m) n := by
    change ((lineTensorAssoc L M N).hom ≫ (lineTensorAssoc L M N).inv).app U _ = _
    rw [Iso.hom_inv_id]
    rfl
  exact h.symm.trans hc

end

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite
open PiExponentSeshadri.Geometry PiExponentSeshadri.Frames
variable {X : Scheme.{0}}

lemma unit_inv_apply (M : X.Modules) (U : X.Opens) (m : Γ(M,U)) :
    (moduleTensorUnit M).inv.app U m = pure (O X) M U (1 : Γ(X,U)) m := by
  have h := congrArg ((moduleTensorUnit M).inv.app U) (unit_pure M U (1 : Γ(X,U)) m)
  have hc : (moduleTensorUnit M).inv.app U
      ((moduleTensorUnit M).hom.app U (pure (O X) M U (1 : Γ(X,U)) m)) =
      pure (O X) M U (1 : Γ(X,U)) m := by
    change ((moduleTensorUnit M).hom ≫ (moduleTensorUnit M).inv).app U _ = _
    rw [Iso.hom_inv_id]
    rfl
  exact (congrArg ((moduleTensorUnit M).inv.app U) (one_smul Γ(X,U) m)).symm.trans (h.symm.trans hc)

lemma power_succ_apply {M : X.Modules} (s : O X ⟶ M) (n : ℕ) (U : X.Opens) :
    (powerSection s (n+1)).app U (1 : Γ(X,U)) =
      pure M (modulePow X M n) U (s.app U (1 : Γ(X,U)))
        ((powerSection s n).app U (1 : Γ(X,U))) := by
  change (moduleTensorMap s (modulePowMap s n)).app U
    ((moduleTensorUnit (modulePow X (O X) n)).inv.app U
      ((unitPowerIso n).inv.app U (1 : Γ(X,U)))) = _
  exact (congrArg ((moduleTensorMap s (modulePowMap s n)).app U)
    (unit_inv_apply _ U _)).trans (map_pure _ _ U _ _)

lemma openSection_tensor (M N : X.Modules) (U : X.Opens)
    (s : O U.toScheme ⟶ M.restrict U.ι) (t : O U.toScheme ⟶ N.restrict U.ι) :
    openSectionEquiv (moduleTensor X M N) U
      (tensorSection s t ≫ (moduleTensorRestrict U M N).inv) =
    pure M N U (openSectionEquiv M U s) (openSectionEquiv N U t) := by
  change (moduleTensor X M N).presheaf.map (eqToHom U.ι_image_top.symm).op
    ((moduleTensorRestrict U M N).inv.app ⊤ ((tensorSection s t).app ⊤ (1 : Γ(U.toScheme,⊤)))) = _
  have h := (congrArg ((moduleTensorRestrict U M N).inv.app ⊤)
    (section_apply s t ⊤)).trans (restrict_pure_inv U M N ⊤ _ _)
  exact (congrArg ((moduleTensor X M N).presheaf.map (eqToHom U.ι_image_top.symm).op) h).trans
    (pure_restrict M N (eqToHom U.ι_image_top.symm) _ _)

instance tensorSection_isIso {M N : X.Modules} (s : O X ⟶ M) (t : O X ⟶ N)
    [hs : IsIso s] [ht : IsIso t] : IsIso (tensorSection s t) := by
  exact ((moduleTensorUnit (O X)).symm ≪≫
    moduleTensorIso (@asIso _ _ _ _ s hs) (@asIso _ _ _ _ t ht)).isIso_hom

lemma mixed_value_restrict {M N : X.Modules} (U : X.Opens) (a : O X ⟶ M)
    (b : O U.toScheme ⟶ N.restrict U.ι) (t : O X ⟶ moduleTensor X M N)
    (ht : t.app U (1 : Γ(X,U)) = pure M N U (a.app U (1 : Γ(X,U))) (openSectionEquiv N U b)) :
    restrictSection U.ι t = tensorSection (restrictSection U.ι a) b ≫ (moduleTensorRestrict U M N).inv := by
  apply (openSectionEquiv (moduleTensor X M N) U).injective
  rw [openSectionEquiv_restrict,openSection_tensor,openSectionEquiv_restrict]
  exact ht

lemma mixed_value_open {M N : X.Modules} (U : X.Opens) (a : O X ⟶ M)
    (b : O U.toScheme ⟶ N.restrict U.ι) [IsIso (restrictSection U.ι a)] [IsIso b]
    (t : O X ⟶ moduleTensor X M N)
    (ht : t.app U (1 : Γ(X,U)) = pure M N U (a.app U (1 : Γ(X,U))) (openSectionEquiv N U b)) :
    U ≤ SectionOpens.isoOpen t := by
  have hi : IsIso (restrictSection U.ι t) := by
    rw [mixed_value_restrict U a b t ht]
    infer_instance
  intro x hx
  apply (SectionOpens.mem_isoOpen_iff t x).mpr
  refine ⟨U,hx,?_⟩
  let hu : IsIso (C := U.toScheme.Modules) (Scheme.Modules.restrictUnitIso U.ι).inv :=
    (Scheme.Modules.restrictUnitIso U.ι).isIso_inv
  exact (@isIso_comp_left_iff U.toScheme.Modules _ _ _ _ _ _ hu).mp hi

end PiExponentSeshadri.TensorPure

end

end OAI
end Source0534

-- Source: OAI/NumberTheory/PiExponent/Approximation/MixedFrameExtension.lean
section Source0535
/-
Modification notice for the LogTwo project.
Derived from openai/math (Apache-2.0), revision adc7f1241b42e322a6451854ab7e4b4c146bf78a.
Original source: lean/OAI/NumberTheory/PiExponent/Approximation/MixedFrameExtension.lean
Changes: Convert module/import declarations to the Lean 4.34 public module format.
See ../THIRD_PARTY_NOTICES.txt for provenance and the recorded changes.
-/

namespace OAI

namespace PiExponentSeshadri.Geometry
noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite
open PiExponentSeshadri.Frames PiExponentSeshadri.TensorPure
variable {X : Scheme.{0}}

theorem LineBundle.divisible_mixed_extension [IsIntegral X] [CompactSpace X] (L M : LineBundle X)
    (s : O X ⟶ L.sheaf) (hD : (sectionOpen X s : Set X).Nonempty)
    (w : Γ(M.sheaf,sectionOpen X s)) :
    ∃ N : ℕ, ∀ n ≥ N, ∃ t : O X ⟶ ((L.pow (n+1)).tensor M).sheaf,
      sectionOpen X t ≤ sectionOpen X s ∧
      t.app (sectionOpen X s) (1 : Γ(X,sectionOpen X s)) =
        pure (L.pow (n+1)).sheaf M.sheaf (sectionOpen X s)
          ((powerSection s (n+1)).app (sectionOpen X s) (1 : Γ(X,sectionOpen X s))) w := by
  obtain ⟨N,hN⟩ := L.mixed_extension M s hD w
  refine ⟨N,fun n hn => ?_⟩
  obtain ⟨t,ht⟩ := hN n hn
  let q := tensorSection s t ≫ (lineTensorAssoc L (L.pow n) M).inv
  refine ⟨q,?_,?_⟩
  · change SectionOpens.isoOpen (tensorSection s t ≫ (lineTensorAssoc L (L.pow n) M).symm.hom) ≤ _
    erw [SectionOpens.isoOpen_postcomp,section_open L ((L.pow n).tensor M)]
    exact inf_le_left
  · let D := sectionOpen X s
    change (lineTensorAssoc L (L.pow n) M).inv.app D ((tensorSection s t).app D (1 : Γ(X,D))) = _
    have h := (section_apply s t D).trans
      (congrArg (pure L.sheaf ((L.pow n).tensor M).sheaf D (s.app D (1 : Γ(X,D)))) ht)
    exact (congrArg ((lineTensorAssoc L (L.pow n) M).inv.app D) h).trans
      ((assoc_inv_pure L (L.pow n) M D _ _ w).trans
       (congrArg (fun z => pure (L.pow (n+1)).sheaf M.sheaf D z w) (power_succ_apply s n D).symm))

theorem LineBundle.mixed_frame_extension [IsIntegral X] [CompactSpace X] (L M : LineBundle X)
    (s : O X ⟶ L.sheaf) (hD : (sectionOpen X s : Set X).Nonempty)
    (e : M.sheaf.restrict (sectionOpen X s).ι ≅ O (sectionOpen X s).toScheme) :
    ∃ N : ℕ, ∀ n ≥ N, ∃ t : O X ⟶ ((L.pow (n+1)).tensor M).sheaf,
      sectionOpen X t = sectionOpen X s ∧
      t.app (sectionOpen X s) (1 : Γ(X,sectionOpen X s)) =
        pure (L.pow (n+1)).sheaf M.sheaf (sectionOpen X s)
          ((powerSection s (n+1)).app (sectionOpen X s) (1 : Γ(X,sectionOpen X s)))
          (openSectionEquiv M.sheaf (sectionOpen X s) e.inv) := by
  obtain ⟨N,hN⟩ := L.divisible_mixed_extension M s hD
    (openSectionEquiv M.sheaf (sectionOpen X s) e.inv)
  refine ⟨N,fun n hn => ?_⟩
  obtain ⟨t,ht,hv⟩ := hN n hn
  refine ⟨t,le_antisymm ht ?_,hv⟩
  have hi : IsIso (restrictSection (sectionOpen X s).ι (powerSection s (n+1))) := by
    have hs := L.sectionOpen_power s (by omega : 0 < n+1)
    exact isIso_restricted_section _ _ hs
  exact mixed_value_open (sectionOpen X s) (powerSection s (n+1)) e.inv t hv

end
end PiExponentSeshadri.Geometry

end OAI
end Source0535

-- Source: OAI/NumberTheory/PiExponent/Approximation/MixedSectionOpenExtension.lean
section Source0536
/-
Modification notice for the LogTwo project.
Derived from openai/math (Apache-2.0), revision adc7f1241b42e322a6451854ab7e4b4c146bf78a.
Original source: lean/OAI/NumberTheory/PiExponent/Approximation/MixedSectionOpenExtension.lean
Changes: Convert module/import declarations to the Lean 4.34 public module format.
See ../THIRD_PARTY_NOTICES.txt for provenance and the recorded changes.
-/

namespace OAI

namespace PiExponentSeshadri.Geometry
noncomputable section
open AlgebraicGeometry CategoryTheory TopologicalSpace
open PiExponentSeshadri.Frames PiExponentSeshadri.TensorPure PiExponentSeshadri.SectionOpens
variable {X : Scheme.{0}}

theorem LineBundle.mixed_section_open_extension [IsIntegral X] [CompactSpace X]
    (L M : LineBundle X) (s : O X ⟶ L.sheaf)
    (hne : (sectionOpen X s : Set X).Nonempty)
    (w : O (sectionOpen X s).toScheme ⟶ M.sheaf.restrict (sectionOpen X s).ι) :
    ∃ N : ℕ, ∀ n ≥ N, ∃ t : O X ⟶ ((L.pow (n+1)).tensor M).sheaf,
      sectionOpen X t = (sectionOpen X s).ι ''ᵁ isoOpen w := by
  let U := sectionOpen X s
  obtain ⟨N,hN⟩ := L.divisible_mixed_extension M s hne (openSectionEquiv M.sheaf U w)
  refine ⟨N,fun n hn => ?_⟩
  obtain ⟨t,ht,hv⟩ := hN n hn
  have hi : IsIso (restrictSection U.ι (powerSection s (n+1))) :=
    isIso_restricted_section _ _ (L.sectionOpen_power s (by omega))
  have hpre : U.ι ⁻¹ᵁ isoOpen t = isoOpen w := by
    rw [← isoOpen_restrictSection]
    have hval := mixed_value_restrict U (powerSection s (n+1)) w t hv
    have hpost := isoOpen_postcomp (tensorSection (restrictSection U.ι (powerSection s (n+1))) w)
      (moduleTensorRestrict U (L.pow (n+1)).sheaf M.sheaf).symm
    have hopen := section_open ((L.pow (n+1)).restrict U.ι) (M.restrict U.ι)
      (restrictSection U.ι (powerSection s (n+1))) w
    refine (congrArg isoOpen hval).trans (hpost.trans (hopen.trans ?_))
    have he : isoOpen (restrictSection U.ι (powerSection s (n+1))) = ⊤ := by
      apply top_unique
      intro x _
      apply (mem_isoOpen_iff _ x).mpr
      exact ⟨⊤, trivial, by infer_instance⟩
    exact (congrArg (fun V : U.toScheme.Opens => V ⊓ isoOpen w) he).trans (top_inf_eq _)
  refine ⟨t,?_⟩
  change isoOpen t = _
  rw [← hpre,Scheme.Hom.image_preimage_eq_opensRange_inf,Scheme.Opens.opensRange_ι]
  exact (inf_eq_right.mpr ht).symm
end
end PiExponentSeshadri.Geometry

end OAI
end Source0536

-- Source: OAI/NumberTheory/PiExponent/Ampleness/RelativeAffineSectionAmple.lean
section Source0537
/-
Modification notice for the LogTwo project.
Derived from openai/math (Apache-2.0), revision adc7f1241b42e322a6451854ab7e4b4c146bf78a.
Original source: lean/OAI/NumberTheory/PiExponent/Ampleness/RelativeAffineSectionAmple.lean
Changes: Convert module/import declarations to the Lean 4.34 public module format.
See ../THIRD_PARTY_NOTICES.txt for provenance and the recorded changes.
-/

namespace OAI

namespace PiExponentSeshadri.Geometry
noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace
open PiExponentSeshadri.Frames PiExponentSeshadri.SectionOpens PiExponentSeshadri.Projective
variable {X : Scheme.{0}}

theorem LineBundle.eventual_twist_affine_cover [IsIntegral X] [CompactSpace X]
    (P J : LineBundle X) {κ : Type} (t : κ → (O X ⟶ P.sheaf))
    (ht : (⨆ i,isoOpen (t i)) = ⊤)
    (hlocal : ∀ i, ∃ (α : Type)
      (w : α → (O (isoOpen (t i)).toScheme ⟶ J.sheaf.restrict (isoOpen (t i)).ι)),
        (⨆ a,isoOpen (w a)) = ⊤ ∧ ∀ a, IsAffineOpen (isoOpen (w a))) :
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n → ∃ (σ : Type) (_ : Fintype σ)
      (s : σ → (O X ⟶ ((P.pow (n+1)).tensor J).sheaf)),
        (⨆ a,isoOpen (s a)) = ⊤ ∧
        (∀ a, IsAffineOpen (isoOpen (s a))) ∧
        (∀ a, (isoOpen (s a) : Set X).Nonempty) := by
  classical
  choose α w hw hwa using hlocal
  have hex (x : X) : ∃ i, x ∈ isoOpen (t i) := by
    apply Opens.mem_iSup.mp
    rw [ht]; trivial
  choose i hi using hex
  have hex' (x : X) : ∃ a, (⟨x,hi x⟩ : (isoOpen (t (i x))).toScheme) ∈
      isoOpen (w (i x) a) := by
    apply Opens.mem_iSup.mp
    erw [hw]; trivial
  choose a ha using hex'
  let V (x : X) : X.Opens := (isoOpen (t (i x))).ι ''ᵁ isoOpen (w (i x) (a x))
  have hxV (x : X) : x ∈ V x := ⟨⟨x,hi x⟩,ha x,rfl⟩
  obtain ⟨F,hF⟩ := isCompact_univ.elim_finite_subcover (fun x => (V x : Set X))
    (fun x => (V x).isOpen) (by intro x _; exact Set.mem_iUnion.mpr ⟨x,hxV x⟩)
  choose N hN using fun x : F => P.mixed_section_open_extension J (t (i x.val))
    ⟨x.val,hi x.val⟩ (w (i x.val) (a x.val))
  refine ⟨Finset.univ.sup N, fun n hn => ?_⟩
  choose s hs using fun x : F => hN x n ((Finset.le_sup (Finset.mem_univ x)).trans hn)
  refine ⟨F,inferInstance,s,?_,?_,?_⟩
  · apply top_unique
    intro x _
    obtain ⟨y,hy⟩ := Set.mem_iUnion.mp (hF (show x ∈ Set.univ from trivial))
    obtain ⟨hyF,hxy⟩ := Set.mem_iUnion.mp hy
    apply Opens.mem_iSup.mpr
    refine ⟨⟨y,hyF⟩,?_⟩
    rw [show isoOpen (s ⟨y,hyF⟩) = V y from hs ⟨y,hyF⟩]
    exact hxy
  · intro x
    rw [show isoOpen (s x) = V x.val from hs x]
    exact (hwa (i x.val) (a x.val)).image_of_isOpenImmersion _
  · intro x
    rw [show isoOpen (s x) = V x.val from hs x]
    exact ⟨x.val,hxV x.val⟩

end
end PiExponentSeshadri.Geometry

end OAI
end Source0537

-- Source: OAI/NumberTheory/PiExponent/Ampleness/BlowupAmpleTwist.lean
section Source0538
/-
Modification notice for the LogTwo project.
Derived from openai/math (Apache-2.0), revision adc7f1241b42e322a6451854ab7e4b4c146bf78a.
Original source: lean/OAI/NumberTheory/PiExponent/Ampleness/BlowupAmpleTwist.lean
Changes: Convert module/import declarations to the Lean 4.34 public module format.
See ../THIRD_PARTY_NOTICES.txt for provenance and the recorded changes.
-/

namespace OAI

noncomputable section

namespace PiExponentSeshadri.Geometry
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace
open PiExponentSeshadri.Frames PiExponentSeshadri.SectionOpens PiExponentSeshadri.Projective
variable {X : Scheme.{0}}

variable {B : Scheme.{0}} {I : X.IdealSheafData} {π : B ⟶ X}

theorem IsBlowup.eventual_ample_exceptional_twist [IsIntegral B] [CompactSpace B]
    [CompactSpace X] (hπ : IsBlowup I π) (L : LineBundle X) (hL : L.IsAmple)
    (J : LineBundle B) (ι : J.sheaf ⟶ O B) (hJ : PresentsPullbackIdeal I π J ι) :
    ∃ a N : ℕ, 0 < a ∧ ∀ n : ℕ, N ≤ n →
      ((((L.pow a).pullback π).pow (n+1)).tensor J).IsAmple := by
  classical
  obtain ⟨a,ha,l,s,hs,hsa,-⟩ := L.ample_common_degree_cover hL
  let P := (L.pow a).pullback π
  let t (i : Fin l) : O B ⟶ P.sheaf := pullbackSection π (s i)
  have ht i : isoOpen (t i) = π ⁻¹ᵁ isoOpen (s i) := pullback_isoOpen_eq (L.pow a) (s i) π
  have hc : (⨆ i,isoOpen (t i)) = ⊤ := pullback_sections_cover s hs π
  have hloc (i : Fin l) : ∃ (α : Type)
      (w : α → (O (isoOpen (t i)).toScheme ⟶ J.sheaf.restrict (isoOpen (t i)).ι)),
        (⨆ a,isoOpen (w a)) = ⊤ ∧ ∀ a, IsAffineOpen (isoOpen (w a)) := by
    rw [ht]
    let U : X.affineOpens := ⟨isoOpen (s i),hsa i⟩
    let : IsAffine U.1.toScheme := U.2
    exact (hπ.morphismRestrict U.1).affine_section_cover (J.restrict (π ⁻¹ᵁ U.1).ι)
      (InvertibleLocal.restrictedInclusion J ι (π ⁻¹ᵁ U.1).ι)
      (presents_morphismRestrict J ι hJ U)
  obtain ⟨N,hN⟩ := P.eventual_twist_affine_cover J t hc hloc
  refine ⟨a,N,ha,fun n hn => ?_⟩
  obtain ⟨σ,hσ,q,hq,hqa,-⟩ := hN n hn
  exact ((P.pow (n+1)).tensor J).ample_of_affine_section_cover q hq hqa

end

open CategoryTheory AlgebraicGeometry TopologicalSpace
open PiExponentSeshadri.Frames
variable {X B : Scheme.{0}} {I : X.IdealSheafData} {π : B ⟶ X}

theorem IsBlowup.exists_ample_exceptional_power_gt_one
    [IsIntegral B] [CompactSpace B] [CompactSpace X]
    (hπ : IsBlowup I π) (L : LineBundle X) (hL : L.IsAmple)
    (J : LineBundle B) (ι : J.sheaf ⟶ O B) (hJ : PresentsPullbackIdeal I π J ι) :
    ∃ a : ℕ, 1 < a ∧ (((L.pullback π).pow a).tensor J).IsAmple := by
  obtain ⟨a,N,ha,h⟩ := hπ.eventual_ample_exceptional_twist L hL J ι hJ
  refine ⟨a*(N+2), ?_, ?_⟩
  · have hmul := Nat.mul_le_mul_right (N+2) (Nat.succ_le_of_lt ha)
    omega
  · apply PiExponent.AmpleIso.isAmple_of_sheaf_iso _ _ _ (h (N+1) (by omega))
    exact moduleTensorIso
      ((modulePowFunctor (N+2)).mapIso (PullbackTensor.powIso π L a) ≪≫
        linePowerMul (L.pullback π) a (N+2)) (Iso.refl _)

end PiExponentSeshadri.Geometry

namespace PiExponentSeshadri.BlowupGluing
open CategoryTheory AlgebraicGeometry TopologicalSpace
open PiExponentSeshadri.Geometry
variable {X : Scheme.{0}} [IsIntegral X] [IsLocallyNoetherian X] [CompactSpace X]

theorem exists_ample_exceptional_power_gt_one (I : X.IdealSheafData)
    (hI : I.support ≠ ⊤) (L : LineBundle X) (hL : L.IsAmple) :
    ∃ a : ℕ, 1 < a ∧
      (((L.pullback (projection I)).pow a).tensor (exceptionalLineBundle I)).IsAmple := by
  let := scheme_isIntegral I hI
  let : CompactSpace (scheme I) := QuasiCompact.compactSpace_of_compactSpace (projection I)
  exact (isBlowup I).exists_ample_exceptional_power_gt_one L hL
    (exceptionalLineBundle I) (exceptionalInclusion I) (exceptional_presents I)

end PiExponentSeshadri.BlowupGluing

end

end OAI
end Source0538

-- Source: LogTwo/Geometry/BlowupPolarization.lean
section Source0539
/-
Modification notice for the LogTwo project.
Adapted from openai/math (Apache-2.0), revision adc7f1241b42e322a6451854ab7e4b4c146bf78a.
Changes: Adapt the auxiliary ample-bundle construction to the project blowup.
See ../THIRD_PARTY_NOTICES.txt for provenance and the recorded changes.
-/

/-! An actual auxiliary ample bundle A^a tensor J on the varying-center
blowup. This does not assert ampleness of the interpolation bundle A tensor J.
Adapted from openai/math Ampleness/AdmissibleBlowupPolarization.lean
(Apache-2.0), applying its scheme-generic construction. -/
namespace LogTwo.Geometry.MatrixBlowup
open OAI PiExponent AlgebraicGeometry CategoryTheory
open PiExponentSeshadri.Geometry
open LogTwo.Interpolation
noncomputable section
variable {m K : ℕ} (w : Weights m) (y : Fin K → ℂ)
variable (hy0 : ∀ j, y j ≠ 0) (a : Fin K → Fin m → ℂ) (T : Fin m → ℕ)

include hy0 in
theorem exists_ampleExponent : ∃ k : ℕ, 1 < k ∧
    (((A w y a T).pow k).tensor (J w y a T)).IsAmple :=
  PiExponentSeshadri.BlowupGluing.exists_ample_exceptional_power_gt_one
    (MatrixCompactification.centerIdeal w y a T)
    (MatrixCompactification.centerIdeal_support_ne_top w y hy0 a T)
    (hyperplane w) (hyperplane_ample w)

def ampleExponent : ℕ := (exists_ampleExponent w y hy0 a T).choose

theorem ampleExponent_gt_one : 1 < ampleExponent w y hy0 a T :=
  (exists_ampleExponent w y hy0 a T).choose_spec.1

def H : LineBundle (space w y a T) :=
  ((A w y a T).pow (ampleExponent w y hy0 a T)).tensor (J w y a T)

theorem H_ample : (H w y hy0 a T).IsAmple :=
  (exists_ampleExponent w y hy0 a T).choose_spec.2

end
end LogTwo.Geometry.MatrixBlowup
end Source0539

-- Source: OAI/NumberTheory/PiExponent/Ampleness/CurveBlowupImageBase.lean
section Source0540
/-
Modification notice for the LogTwo project.
Derived from openai/math (Apache-2.0), revision adc7f1241b42e322a6451854ab7e4b4c146bf78a.
Original source: lean/OAI/NumberTheory/PiExponent/Ampleness/CurveBlowupImageBase.lean
Changes: Convert module/import declarations to the Lean 4.34 public module format.
See ../THIRD_PARTY_NOTICES.txt for provenance and the recorded changes.
-/

namespace OAI

noncomputable section
open CategoryTheory AlgebraicGeometry TopologicalSpace

namespace PiExponentSeshadri.Geometry
variable {X Y : Scheme.{0}}

theorem integral_scheme_image (f : X ⟶ Y) [QuasiCompact f] [IsIntegral X] : IsIntegral f.image := by
  let hred (U : Y.affineOpens) : _root_.IsReduced (Γ(Y,U.1) ⧸ f.ker.ideal U) := by
    rw [Scheme.Hom.ker_apply]
    exact isReduced_of_injective (RingHom.kerLift (f.app U.1).hom)
      (RingHom.kerLift_injective (f.app U.1).hom)
  let : ∀ U, AlgebraicGeometry.IsReduced (f.ker.subschemeCover.openCover.X U) := by
    intro U
    change IsReduced (Spec (.of (Γ(Y,U.1) ⧸ f.ker.ideal U)))
    exact (affine_isReduced_iff _).mpr (hred U)
  let : IsReduced f.image := IsReduced.of_openCover f.image f.ker.subschemeCover.openCover
  have hi : IsIrreducible (Set.range f.toImage) := by
    simpa only [Set.image_univ] using
      (IrreducibleSpace.isIrreducible_univ (X := X)).image f.toImage
        f.toImage.continuous.continuousOn
  let : IrreducibleSpace f.image := (irreducibleSpace_def _).mpr (by
    change IsIrreducible (Set.univ : Set f.image)
    rw [← f.toImage.denseRange.closure_range]
    exact hi.closure)
  exact isIntegral_of_irreducibleSpace_of_isReduced _

end PiExponentSeshadri.Geometry

namespace PiExponent.CurveBlowupImage
open PiExponentSeshadri.Geometry
variable {C X B : Scheme.{0}}

theorem toImage_isProper (f : C ⟶ X) [IsProper f] : IsProper f.toImage := by
  let : IsProper (f.toImage ≫ f.imageι) := by rw [f.toImage_imageι]; infer_instance
  exact IsProper.of_comp f.toImage f.imageι

theorem toImage_restrict_isIso (f : C ⟶ X) [IsProper f] [IsIntegral C]
    (U : X.Opens) [IsClosedImmersion (f ∣_ U)] :
    IsIso (f.toImage ∣_ (f.imageι ⁻¹ᵁ U)) := by
  let := integral_scheme_image f
  let : IsClosedImmersion
      ((f.toImage ∣_ (f.imageι ⁻¹ᵁ U)) ≫ (f.imageι ∣_ U)) := by
    rw [← morphismRestrict_comp]
    exact Eq.mpr (congrArg (fun k : C ⟶ X => IsClosedImmersion (k ∣_ U))
      f.toImage_imageι) (inferInstance : IsClosedImmersion (f ∣_ U))
  let := IsClosedImmersion.of_comp_isClosedImmersion
    (f.toImage ∣_ (f.imageι ⁻¹ᵁ U)) (f.imageι ∣_ U)
  let : IsDominant (f.toImage ∣_ (f.imageι ⁻¹ᵁ U)) :=
    IsZariskiLocalAtTarget.restrict (inferInstance : IsDominant f.toImage) _
  exact isIso_of_isClosedImmersion_of_surjective _

theorem restricted_curve_isClosedImmersion (π : B ⟶ X)
    (C : NumericalAmpleness.IntegralCurve B) (U : X.Opens) [IsIso (π ∣_ U)] :
    IsClosedImmersion ((C.embedding ≫ π) ∣_ U) := by
  rw [morphismRestrict_comp]
  exact IsClosedImmersion.comp (C.embedding ∣_ π ⁻¹ᵁ U) (π ∣_ U)

theorem genericPoint_eq_of_isDominant (f : C ⟶ X)
    [IsIntegral C] [IsIntegral X] [IsDominant f] :
    f (genericPoint C) = genericPoint X := by
  apply IsGenericPoint.eq _ (genericPoint_spec X)
  simpa only [Set.image_univ, f.denseRange.closure_range] using
    (genericPoint_spec C).image f.continuous

theorem stalkMap_isIso_of_restrict (f : C ⟶ X) (U : X.Opens)
    [IsIso (f ∣_ U)] (x : C) (hx : f x ∈ U) : IsIso (f.stalkMap x) := by
  let q : (f ⁻¹ᵁ U).toScheme := ⟨x, hx⟩
  have hi : IsIso (((f ⁻¹ᵁ U).ι ≫ f).stalkMap q) := by
    rw [← morphismRestrict_ι]
    infer_instance
  rw [Scheme.Hom.stalkMap_comp] at hi
  change IsIso (f.stalkMap x ≫ (f ⁻¹ᵁ U).ι.stalkMap q) at hi
  have hq : IsIso ((f ⁻¹ᵁ U).ι.stalkMap q) :=
    (IsOpenImmersion.iff_isIso_stalkMap.mp
      (inferInstance : IsOpenImmersion (f ⁻¹ᵁ U).ι)).2 q
  exact @IsIso.of_isIso_comp_right CommRingCat _ _ _ _
    (f.stalkMap x) ((f ⁻¹ᵁ U).ι.stalkMap q) hq hi

end PiExponent.CurveBlowupImage

end

end OAI
end Source0540

-- Source: OAI/NumberTheory/PiExponent/Geometry/CurveImageOpenLocus.lean
section Source0541
-- Modified in this edition: unused plain lemmas removed; see reduction.json.
/-
Modification notice for the LogTwo project.
Derived from openai/math (Apache-2.0), revision adc7f1241b42e322a6451854ab7e4b4c146bf78a.
Original source: lean/OAI/NumberTheory/PiExponent/Geometry/CurveImageOpenLocus.lean
Changes: Convert module/import declarations to the Lean 4.34 public module format.
See ../THIRD_PARTY_NOTICES.txt for provenance and the recorded changes.
-/

namespace OAI

noncomputable section
open CategoryTheory AlgebraicGeometry TopologicalSpace

namespace PiExponent.CurveBlowupImage
variable {C X : Scheme.{0}}

theorem exists_image_outside_closed_points [IsIntegral C] (f : C ⟶ X)
    (Z : Set X) (hZ : ∀ x ∈ Z, IsClosed ({x} : Set X))
    (hn : ¬ ∃ x : X, Set.range f ⊆ {x}) : ∃ c : C, f c ∉ Z := by
  by_contra h
  push Not at h
  have hc := hZ (f (genericPoint C)) (h (genericPoint C))
  apply hn
  refine ⟨f (genericPoint C), ?_⟩
  rintro _ ⟨c,rfl⟩
  have hh := ((genericPoint_spec C).specializes (Set.mem_univ c)).map f.continuous
  have hm := hh.mem_closure
  rwa [hc.closure_eq] at hm

end PiExponent.CurveBlowupImage

end

end OAI
end Source0541

-- Source: OAI/NumberTheory/PiExponent/Geometry/CurveMorphismFinite.lean
section Source0542
/-
Modification notice for the LogTwo project.
Derived from openai/math (Apache-2.0), revision adc7f1241b42e322a6451854ab7e4b4c146bf78a.
Original source: lean/OAI/NumberTheory/PiExponent/Geometry/CurveMorphismFinite.lean
Changes: Convert module/import declarations to the Lean 4.34 public module format.
See ../THIRD_PARTY_NOTICES.txt for provenance and the recorded changes.
-/

namespace OAI

noncomputable section
namespace PiExponent.CurveMorphismFinite
open CategoryTheory AlgebraicGeometry TopologicalSpace Set
universe u

attribute [local instance] specializationOrder

theorem isClosed_singleton_of_ne_genericPoint (X : Scheme.{u}) [IsIntegral X]
    (hdim : topologicalKrullDim X ≤ 1) (x : X) (hx : x ≠ genericPoint X) :
    IsClosed ({x} : Set X) := by
  apply closure_subset_iff_isClosed.mp
  intro y hy
  have hyx : y ≤ x := specializes_iff_mem_closure.mpr hy
  by_contra hne
  have hylt : y < x := lt_of_le_of_ne hyx (by simpa using hne)
  have hdim' : Order.krullDim X ≤ 1 := by
    change Order.krullDim (IrreducibleCloseds X) ≤ 1 at hdim
    rwa [Order.krullDim_eq_of_orderIso (irreducibleSetEquivPoints (α := X))] at hdim
  have hyco : Order.coheight y ≤ (1 : ℕ∞) := by
    exact_mod_cast (Order.coheight_le_krullDim y).trans hdim'
  have hxco : Order.coheight x < (1 : ℕ∞) :=
    Order.coheight_le_coe_iff.mp hyco x hylt
  have hxmax : IsMax x := Order.coheight_eq_zero.mp (Order.lt_one_iff.mp hxco)
  exact hx hxmax.eq_top

theorem finite_closed_avoiding_genericPoint (X : Scheme.{u}) [IsIntegral X]
    [NoetherianSpace X] (hdim : topologicalKrullDim X ≤ 1)
    {Z : Set X} (hZ : IsClosed Z) (hη : genericPoint X ∉ Z) : Z.Finite := by
  obtain ⟨S, hS, hclosed, hirr, hcover⟩ :=
    NoetherianSpace.exists_finite_set_isClosed_irreducible hZ
  rw [hcover]
  apply hS.sUnion
  intro C hC
  obtain ⟨x, hx⟩ := QuasiSober.sober (hirr C hC) (hclosed C hC)
  have hxne : x ≠ genericPoint X := by
    intro heq
    apply hη
    rw [hcover, ← heq]
    exact mem_sUnion.mpr ⟨C, hC, hx.mem⟩
  have hxc := isClosed_singleton_of_ne_genericPoint X hdim x hxne
  have heq : C = {x} := hx.def.symm.trans hxc.closure_eq
  rw [heq]
  exact finite_singleton x

theorem finite_fibers {X Y : Scheme.{u}} [IsIntegral X] [NoetherianSpace X]
    [Nontrivial Y] (f : X ⟶ Y) [IsProper f] [IsDominant f]
    (hdim : topologicalKrullDim X ≤ 1) (y : Y) : (f ⁻¹' {y}).Finite := by
  by_cases hy : IsClosed ({y} : Set Y)
  · have hZ : IsClosed (f ⁻¹' {y}) := hy.preimage f.continuous
    apply finite_closed_avoiding_genericPoint X hdim hZ
    intro hη
    have hall : (Set.univ : Set X) ⊆ f ⁻¹' {y} :=
      ((genericPoint_spec X).mem_closed_set_iff hZ).mp hη
    obtain ⟨z, hz⟩ := exists_ne y
    obtain ⟨x, hx⟩ := f.surjective z
    apply hz
    have hh := hall (show x ∈ (Set.univ : Set X) from trivial)
    change f x = y at hh
    exact hx.symm.trans hh
  · apply (finite_singleton (genericPoint X)).subset
    intro x hx
    change f x = y at hx
    by_cases hxe : x = genericPoint X
    · exact hxe
    · exfalso
      apply hy
      have hclosed := f.isClosedMap {x} (isClosed_singleton_of_ne_genericPoint X hdim x hxe)
      simpa only [Set.image_singleton, hx] using hclosed

theorem isFinite_of_proper_dominant {X Y : Scheme.{u}} [IsIntegral X] [NoetherianSpace X]
    [Nontrivial Y] (f : X ⟶ Y) [IsProper f] [IsDominant f]
    (hdim : topologicalKrullDim X ≤ 1) : IsFinite f := by
  let : LocallyQuasiFinite f := LocallyQuasiFinite.of_finite_preimage_singleton f (finite_fibers f hdim)
  exact IsFinite.of_isProper_of_locallyQuasiFinite f

end PiExponent.CurveMorphismFinite

end

end OAI
end Source0542

-- Source: OAI/NumberTheory/PiExponent/Geometry/CurveProperImageDimension.lean
section Source0543
/-
Modification notice for the LogTwo project.
Derived from openai/math (Apache-2.0), revision adc7f1241b42e322a6451854ab7e4b4c146bf78a.
Original source: lean/OAI/NumberTheory/PiExponent/Geometry/CurveProperImageDimension.lean
Changes: Convert module/import declarations to the Lean 4.34 public module format.
See ../THIRD_PARTY_NOTICES.txt for provenance and the recorded changes.
-/

namespace OAI

noncomputable section
namespace PiExponent.CurveProperImageDimension
open CategoryTheory AlgebraicGeometry TopologicalSpace Set
universe u

theorem genericPoint_map {C Y : Scheme.{u}} [IsIntegral C] [IsIntegral Y]
    (f : C ⟶ Y) [IsDominant f] : f (genericPoint C) = genericPoint Y := by
  have h : IsGenericPoint (f (genericPoint C)) (Set.univ : Set Y) := by
    simpa only [Set.image_univ, f.denseRange.closure_range] using
      (genericPoint_spec C).image f.continuous
  exact h.eq (genericPoint_spec Y)

theorem target_nongeneric_isClosed {C Y : Scheme.{u}} [IsIntegral C] [IsIntegral Y]
    (f : C ⟶ Y) [IsProper f] [IsDominant f]
    (hdim : topologicalKrullDim C ≤ 1) (y : Y) (hy : y ≠ genericPoint Y) :
    IsClosed ({y} : Set Y) := by
  obtain ⟨c, rfl⟩ := f.surjective y
  have hc : c ≠ genericPoint C := by
    intro heq
    apply hy
    rw [heq, genericPoint_map f]
  simpa only [Set.image_singleton] using f.isClosedMap {c}
    (CurveMorphismFinite.isClosed_singleton_of_ne_genericPoint C hdim c hc)

theorem dimension_eq_one_of_proper_dominant {C Y : Scheme.{u}}
    [IsIntegral C] [IsIntegral Y] [Nontrivial Y]
    (f : C ⟶ Y) [IsProper f] [IsDominant f]
    (hdim : topologicalKrullDim C ≤ 1) : topologicalKrullDim Y = 1 := by
  let : PartialOrder Y := specializationOrder Y
  change Order.krullDim (IrreducibleCloseds Y) = 1
  rw [Order.krullDim_eq_of_orderIso (irreducibleSetEquivPoints (α := Y))]
  have hle := (Order.krullDim_le_one_iff_forall_isMin (α := Y)).mpr (by
    intro y hy z hzy
    have hclosed := target_nongeneric_isClosed f hdim y hy
    have hz : z ∈ closure ({y} : Set Y) := specializes_iff_mem_closure.mp hzy
    rw [hclosed.closure_eq] at hz
    exact (show z = y from hz).symm.le)
  have hge := (Order.one_le_krullDim_iff (α := Y)).mpr (by
    obtain ⟨y, hy⟩ := exists_ne (⊤ : Y)
    exact ⟨y, ⊤, lt_top_iff_ne_top.mpr hy⟩)
  exact le_antisymm hle hge

theorem image_dimension_eq_one {C X : Scheme.{u}} [IsIntegral C]
    (f : C ⟶ X) [IsProper f] [IsIntegral f.image] [Nontrivial f.image]
    (hdim : topologicalKrullDim C = 1) : topologicalKrullDim f.image = 1 := by
  have : IsProper (f.toImage ≫ f.imageι) := by
    rw [Scheme.Hom.toImage_imageι]
    infer_instance
  let : IsProper f.toImage := IsProper.of_comp f.toImage f.imageι
  exact dimension_eq_one_of_proper_dominant f.toImage hdim.le

theorem image_nontrivial_of_nonconstant {C X : Scheme.{u}} [IsIntegral C]
    (f : C ⟶ X) (hnonconstant : ¬ ∃ x : X, Set.range f ⊆ {x}) : Nontrivial f.image := by
  classical
  by_contra h
  let : Subsingleton f.image := not_nontrivial_iff_subsingleton.mp h
  apply hnonconstant
  refine ⟨f (genericPoint C), ?_⟩
  rintro _ ⟨c, rfl⟩
  change f c = f (genericPoint C)
  have hc : f.toImage c = f.toImage (genericPoint C) := Subsingleton.elim _ _
  have he := congrArg f.imageι hc
  simpa only [← Scheme.Hom.comp_apply, Scheme.Hom.toImage_imageι] using he

theorem image_dimension_eq_one_of_nonconstant {C X : Scheme.{u}} [IsIntegral C]
    (f : C ⟶ X) [IsProper f] [IsIntegral f.image]
    (hdim : topologicalKrullDim C = 1)
    (hnonconstant : ¬ ∃ x : X, Set.range f ⊆ {x}) : topologicalKrullDim f.image = 1 := by
  let : Nontrivial f.image := image_nontrivial_of_nonconstant f hnonconstant
  exact image_dimension_eq_one f hdim

end PiExponent.CurveProperImageDimension

end

end OAI
end Source0543

-- Source: OAI/NumberTheory/PiExponent/LocalAlgebra/OpenIsoFunctionField.lean
section Source0544
-- Modified in this edition: unused plain lemmas removed; see reduction.json.
/-
Modification notice for the LogTwo project.
Derived from openai/math (Apache-2.0), revision adc7f1241b42e322a6451854ab7e4b4c146bf78a.
Original source: lean/OAI/NumberTheory/PiExponent/LocalAlgebra/OpenIsoFunctionField.lean
Changes: Convert module/import declarations to the Lean 4.34 public module format.
See ../THIRD_PARTY_NOTICES.txt for provenance and the recorded changes.
-/

namespace OAI

noncomputable section
open CategoryTheory AlgebraicGeometry TopologicalSpace

namespace PiExponent.CurveBlowupImage
variable {C X : Scheme.{0}} [IsIntegral C] [IsIntegral X]

def functionFieldMap (f : C ⟶ X) [IsDominant f] : X.functionField ⟶ C.functionField :=
  eqToHom (congrArg (fun x => X.presheaf.stalk x)
    (genericPoint_eq_of_isDominant f).symm) ≫ f.stalkMap (genericPoint C)

theorem functionFieldMap_isIso (f : C ⟶ X) [IsDominant f]
    (U : X.Opens) [IsIso (f ∣_ U)] (hU : Nonempty (f ⁻¹ᵁ U)) :
    IsIso (functionFieldMap f) := by
  have hx : f (genericPoint C) ∈ U := by
    apply ((genericPoint_spec C).mem_open_set_iff (f ⁻¹ᵁ U).isOpen).mpr
    obtain ⟨q⟩ := hU
    exact ⟨q.1, trivial, q.2⟩
  let := stalkMap_isIso_of_restrict f U (genericPoint C) hx
  unfold functionFieldMap
  infer_instance

def functionFieldIso (f : C ⟶ X) [IsDominant f]
    (U : X.Opens) [IsIso (f ∣_ U)] (hU : Nonempty (f ⁻¹ᵁ U)) :
    X.functionField ≅ C.functionField :=
  letI := functionFieldMap_isIso f U hU
  asIso (functionFieldMap f)

private theorem eqToHom_fromSpecStalk (X : Scheme.{0}) {x y : X} (h : x = y) :
    Spec.map (eqToHom (congrArg (fun z => X.presheaf.stalk z) h)) ≫
      X.fromSpecStalk x = X.fromSpecStalk y := by
  subst y
  simp

theorem functionFieldMap_fromSpecStalk (f : C ⟶ X) [IsDominant f] :
    Spec.map (functionFieldMap f) ≫ X.fromSpecStalk (genericPoint X) =
      C.fromSpecStalk (genericPoint C) ≫ f := by
  unfold functionFieldMap
  rw [Spec.map_comp, Category.assoc,
    eqToHom_fromSpecStalk X (genericPoint_eq_of_isDominant f).symm]
  exact Scheme.SpecMap_stalkMap_fromSpecStalk f

end PiExponent.CurveBlowupImage

end

end OAI
end Source0544

-- Source: OAI/NumberTheory/PiExponent/Ampleness/CurveBlowupImage.lean
section Source0545
-- Modified in this edition: unused plain lemmas removed; see reduction.json.
/-
Modification notice for the LogTwo project.
Derived from openai/math (Apache-2.0), revision adc7f1241b42e322a6451854ab7e4b4c146bf78a.
Original source: lean/OAI/NumberTheory/PiExponent/Ampleness/CurveBlowupImage.lean
Changes: Convert module/import declarations to the Lean 4.34 public module format.
See ../THIRD_PARTY_NOTICES.txt for provenance and the recorded changes.
-/

namespace OAI

noncomputable section
open CategoryTheory AlgebraicGeometry TopologicalSpace

namespace PiExponent.CurveBlowupImage
open PiExponentSeshadri.Geometry
variable {X B : Scheme.{0}}

def imageCurve (π : B ⟶ X) [IsProper π]
    (C : NumericalAmpleness.IntegralCurve B)
    (hn : ¬ ∃ x : X, Set.range (C.embedding ≫ π) ⊆ {x}) :
    NumericalAmpleness.IntegralCurve X :=
  let f := C.embedding ≫ π
  letI := integral_scheme_image f
  { scheme := f.image
    embedding := f.imageι
    closedImmersion := inferInstance
    integral := inferInstance
    dimension := CurveProperImageDimension.image_dimension_eq_one_of_nonconstant
      f C.dimension hn }

def imageMap (π : B ⟶ X) [IsProper π]
    (C : NumericalAmpleness.IntegralCurve B)
    (hn : ¬ ∃ x : X, Set.range (C.embedding ≫ π) ⊆ {x}) :
    C.scheme ⟶ (imageCurve π C hn).scheme := (C.embedding ≫ π).toImage

@[simp] theorem imageMap_comp (π : B ⟶ X) [IsProper π]
    (C : NumericalAmpleness.IntegralCurve B)
    (hn : ¬ ∃ x : X, Set.range (C.embedding ≫ π) ⊆ {x}) :
    imageMap π C hn ≫ (imageCurve π C hn).embedding = C.embedding ≫ π :=
  (C.embedding ≫ π).toImage_imageι

instance imageMap_isProper (π : B ⟶ X) [IsProper π]
    (C : NumericalAmpleness.IntegralCurve B)
    (hn : ¬ ∃ x : X, Set.range (C.embedding ≫ π) ⊆ {x}) :
    IsProper (imageMap π C hn) := toImage_isProper _

instance imageMap_isDominant (π : B ⟶ X) [IsProper π]
    (C : NumericalAmpleness.IntegralCurve B)
    (hn : ¬ ∃ x : X, Set.range (C.embedding ≫ π) ⊆ {x}) :
    IsDominant (imageMap π C hn) := by
  change IsDominant (C.embedding ≫ π).toImage
  infer_instance

theorem imageMap_restrict_isIso (π : B ⟶ X) [IsProper π]
    (C : NumericalAmpleness.IntegralCurve B)
    (hn : ¬ ∃ x : X, Set.range (C.embedding ≫ π) ⊆ {x})
    (U : X.Opens) [IsIso (π ∣_ U)] :
    IsIso (imageMap π C hn ∣_ ((imageCurve π C hn).embedding ⁻¹ᵁ U)) := by
  let := restricted_curve_isClosedImmersion π C U
  exact toImage_restrict_isIso (C.embedding ≫ π) U

theorem imageMap_preimage_nonempty (π : B ⟶ X) [IsProper π]
    (C : NumericalAmpleness.IntegralCurve B)
    (hn : ¬ ∃ x : X, Set.range (C.embedding ≫ π) ⊆ {x})
    (U : X.Opens) (hU : ∃ c : C.scheme, (C.embedding ≫ π) c ∈ U) :
    Nonempty (imageMap π C hn ⁻¹ᵁ ((imageCurve π C hn).embedding ⁻¹ᵁ U)) := by
  obtain ⟨c, hc⟩ := hU
  refine ⟨⟨c, ?_⟩⟩
  change (imageCurve π C hn).embedding (imageMap π C hn c) ∈ U
  simpa only [← Scheme.Hom.comp_apply, imageMap_comp] using hc

def imageFunctionFieldIso (π : B ⟶ X) [IsProper π]
    (C : NumericalAmpleness.IntegralCurve B)
    (hn : ¬ ∃ x : X, Set.range (C.embedding ≫ π) ⊆ {x})
    (U : X.Opens) [IsIso (π ∣_ U)]
    (hU : ∃ c : C.scheme, (C.embedding ≫ π) c ∈ U) :
    (imageCurve π C hn).scheme.functionField ≅ C.scheme.functionField :=
  letI := imageMap_restrict_isIso π C hn U
  functionFieldIso (imageMap π C hn) ((imageCurve π C hn).embedding ⁻¹ᵁ U)
    (imageMap_preimage_nonempty π C hn U hU)

theorem imageFunctionFieldIso_generic (π : B ⟶ X) [IsProper π]
    (C : NumericalAmpleness.IntegralCurve B)
    (hn : ¬ ∃ x : X, Set.range (C.embedding ≫ π) ⊆ {x})
    (U : X.Opens) [IsIso (π ∣_ U)]
    (hU : ∃ c : C.scheme, (C.embedding ≫ π) c ∈ U) :
    Spec.map (imageFunctionFieldIso π C hn U hU).hom ≫
      (imageCurve π C hn).scheme.fromSpecStalk
        (genericPoint (imageCurve π C hn).scheme) ≫
      (imageCurve π C hn).embedding =
    C.scheme.fromSpecStalk (genericPoint C.scheme) ≫ C.embedding ≫ π := by
  have h := functionFieldMap_fromSpecStalk (imageMap π C hn)
  change Spec.map (functionFieldMap (imageMap π C hn)) ≫ _ ≫ _ = _
  rw [← Category.assoc, h, Category.assoc, imageMap_comp]

theorem blowup_restrict_isIso {I : X.IdealSheafData} {π : B ⟶ X}
    (hπ : IsBlowup I π) : IsIso (π ∣_ I.support.compl) := by
  apply (hπ.morphismRestrict I.support.compl).isIso_of_invertible
  have he : I.comap (Scheme.Opens.ι (X := X) I.support.compl) = ⊤ := by
    apply (Scheme.IdealSheafData.support_eq_bot_iff _).mp
    rw [Scheme.IdealSheafData.support_comap]
    ext x
    change (x.val ∈ I.support ↔ False)
    exact iff_false_intro x.property
  rw [he]
  exact invertible_top _

end PiExponent.CurveBlowupImage

end

end OAI
end Source0545

-- Source: LogTwo/Geometry/BlowupCurveImage.lean
section Source0546
/-
Modification notice for the LogTwo project.
Adapted from openai/math (Apache-2.0), revision adc7f1241b42e322a6451854ab7e4b4c146bf78a.
Changes: Adapt the curve-image construction to the varying-center blowup.
See ../THIRD_PARTY_NOTICES.txt for provenance and the recorded changes.
-/

/-! Actual varying-center curve models, adapted from the corresponding
AdmissibleCurve*.lean wrappers in pinned openai/math (Apache-2.0).
Only scheme-generic APIs are imported; no fixed-Y contact bound is used. -/
namespace LogTwo.Geometry.MatrixBlowup.Image
open OAI PiExponent AlgebraicGeometry CategoryTheory TopologicalSpace
open LogTwo.Geometry.MatrixBlowup CurveBlowupImage
noncomputable section
variable {m K : ℕ} (w : LogTwo.Interpolation.Weights m)
variable (y : Fin K → ℂ) (a : Fin K → Fin m → ℂ) (T : Fin m → ℕ)

theorem center_point_isClosed (x : MatrixCompactification.space w)
    (hx : x ∈ (MatrixCompactification.centerIdeal w y a T).support) : IsClosed ({x} : Set (MatrixCompactification.space w)) := by
  change x ∈ ((MatrixCompactification.centerIdeal w y a T).support : Set (MatrixCompactification.space w)) at hx
  rw [MatrixCompactification.centerIdeal_support w y a T] at hx
  obtain ⟨j, z, rfl⟩ := Set.mem_iUnion.mp hx
  let q := CompactJetIdealAt.point (y j) (a j) ≫ MatrixCompactification.affineChart w
  let : IsClosedImmersion q := CompactJetIdeal.section_isClosedImmersion
    (MatrixCompactification.structureMap w) q (by
      dsimp [q]
      rw [Category.assoc, MatrixCompactification.affineChart_over]
      exact CompactJetIdealAt.point_section (y j) (a j))
  have he : Set.range q = {q z} := by
    ext x
    constructor
    · rintro ⟨z',rfl⟩
      exact congrArg q (Subsingleton.elim z' z)
    · rintro rfl
      exact ⟨z,rfl⟩
  rw [← he]
  exact q.isClosedEmbedding.isClosed_range

theorem meets_center_complement (C : NumericalAmpleness.IntegralCurve (space w y a T))
    (hn : ¬ ∃ x : MatrixCompactification.space w, Set.range (C.embedding ≫ projection w y a T) ⊆ {x}) :
    ∃ c : C.scheme, (C.embedding ≫ projection w y a T) c ∈ (MatrixCompactification.centerIdeal w y a T).support.compl :=
  exists_image_outside_closed_points (C.embedding ≫ projection w y a T)
    (MatrixCompactification.centerIdeal w y a T).support (center_point_isClosed w y a T) hn

instance projection_restrict_isIso :
    IsIso (projection w y a T ∣_ (MatrixCompactification.centerIdeal w y a T).support.compl) :=
  blowup_restrict_isIso (isBlowup w y a T)

abbrev imageCurve (C : NumericalAmpleness.IntegralCurve (space w y a T))
    (hn : ¬ ∃ x : MatrixCompactification.space w, Set.range (C.embedding ≫ projection w y a T) ⊆ {x}) :=
  CurveBlowupImage.imageCurve (projection w y a T) C hn

def functionFieldIso (C : NumericalAmpleness.IntegralCurve (space w y a T))
    (hn : ¬ ∃ x : MatrixCompactification.space w, Set.range (C.embedding ≫ projection w y a T) ⊆ {x}) :
    (imageCurve w y a T C hn).scheme.functionField ≅ C.scheme.functionField :=
  imageFunctionFieldIso (projection w y a T) C hn (MatrixCompactification.centerIdeal w y a T).support.compl
    (meets_center_complement w y a T C hn)

theorem functionFieldIso_generic (C : NumericalAmpleness.IntegralCurve (space w y a T))
    (hn : ¬ ∃ x : MatrixCompactification.space w, Set.range (C.embedding ≫ projection w y a T) ⊆ {x}) :
    Spec.map (functionFieldIso w y a T C hn).hom ≫
      (imageCurve w y a T C hn).scheme.fromSpecStalk (genericPoint (imageCurve w y a T C hn).scheme) ≫
      (imageCurve w y a T C hn).embedding =
    C.scheme.fromSpecStalk (genericPoint C.scheme) ≫ C.embedding ≫ projection w y a T :=
  imageFunctionFieldIso_generic (projection w y a T) C hn (MatrixCompactification.centerIdeal w y a T).support.compl
    (meets_center_complement w y a T C hn)

theorem image_meets_chart (C : NumericalAmpleness.IntegralCurve (space w y a T))
    (hn : ¬ ∃ x : MatrixCompactification.space w, Set.range (C.embedding ≫ projection w y a T) ⊆ {x})
    (hm : ∃ c : C.scheme, (C.embedding ≫ projection w y a T) c ∈ (MatrixCompactification.affineChart w).opensRange) :
    ∃ c : (imageCurve w y a T C hn).scheme,
      (imageCurve w y a T C hn).embedding c ∈ (MatrixCompactification.affineChart w).opensRange := by
  obtain ⟨c,hc⟩ := hm
  refine ⟨CurveBlowupImage.imageMap (projection w y a T) C hn c, ?_⟩
  simpa only [← Scheme.Hom.comp_apply, CurveBlowupImage.imageMap_comp] using hc

end
end LogTwo.Geometry.MatrixBlowup.Image
end Source0546

-- Source: OAI/NumberTheory/PiExponent/Geometry/CurveGeometricFunctionField.lean
section Source0547
-- Modified in this edition: unused plain lemmas removed; see reduction.json.
/-
Modification notice for the LogTwo project.
Derived from openai/math (Apache-2.0), revision adc7f1241b42e322a6451854ab7e4b4c146bf78a.
Original source: lean/OAI/NumberTheory/PiExponent/Geometry/CurveGeometricFunctionField.lean
Changes: Convert module/import declarations to the Lean 4.34 public module format.
See ../THIRD_PARTY_NOTICES.txt for provenance and the recorded changes.
-/

namespace OAI

noncomputable section
namespace PiExponent.CurveGeometricFunctionField

open CategoryTheory AlgebraicGeometry

variable (k A E : Type*) [Field k] [CommRing A] [IsDomain A] [Field E]
  [Algebra k A] [Algebra k E] [Algebra A E] [IsScalarTower k A E]
  [IsFractionRing A E]

omit [IsDomain A] in
theorem fractionField_essFiniteType [Algebra.FiniteType k A] :
    Algebra.EssFiniteType k E := by
  let : Algebra.EssFiniteType A E :=
    Algebra.EssFiniteType.of_isLocalization E (nonZeroDivisors A)
  exact Algebra.EssFiniteType.comp k A E

theorem fractionField_trdeg_eq_one [Algebra.FiniteType k A]
    (hdim : ringKrullDim A = 1) : Algebra.trdeg k E = 1 := by
  let : FaithfulSMul A E :=
    (faithfulSMul_iff_algebraMap_injective A E).mpr (IsFractionRing.injective A E)
  have hd : (Algebra.trdeg k A).toNat = 1 := by
    rw [PiExponentJets.W24.finiteType_domain_krullDim_eq_trdeg k A] at hdim
    exact_mod_cast hdim
  have he := PiExponentJets.W24.localization_trdeg_toNat_eq k A E
    (nonZeroDivisors A)
  exact Cardinal.toNat_eq_one.mp (he.symm.trans hd)

def coordinates {ι : Type*} (φ : MvPolynomial ι k →ₐ[k] A) : ι → E :=
  fun i => algebraMap A E (φ (MvPolynomial.X i))

omit [IsDomain A] in
theorem adjoin_coordinates_eq_top {ι : Type*}
    (φ : MvPolynomial ι k →ₐ[k] A) (hφ : Function.Surjective φ) :
    IntermediateField.adjoin k (Set.range (coordinates k A E φ)) = ⊤ := by
  let x := coordinates k A E φ
  let K := IntermediateField.adjoin k (Set.range x)
  have hψ : (IsScalarTower.toAlgHom k A E).comp φ = MvPolynomial.aeval x := by
    apply MvPolynomial.algHom_ext
    intro i
    simp [x, coordinates]
  have hmem (a : A) : algebraMap A E a ∈ K := by
    obtain ⟨p, rfl⟩ := hφ a
    apply IntermediateField.algebra_adjoin_le_adjoin k (Set.range x)
    rw [← MvPolynomial.aeval_range]
    refine ⟨p, ?_⟩
    exact (congrArg (fun f : MvPolynomial ι k →ₐ[k] E => f p) hψ).symm
  apply top_le_iff.mp
  intro z _
  obtain ⟨a, b, _, rfl⟩ := IsFractionRing.div_surjective A z
  exact K.div_mem (hmem a) (hmem b)

theorem of_surjective_coordinates {ι : Type*} [Finite ι]
    (φ : MvPolynomial ι k →ₐ[k] A) (hφ : Function.Surjective φ)
    (hdim : ringKrullDim A = 1) :
    Algebra.EssFiniteType k E ∧ Algebra.trdeg k E = 1 ∧
      IntermediateField.adjoin k (Set.range (coordinates k A E φ)) = ⊤ := by
  let : Algebra.FiniteType k A := Algebra.FiniteType.of_surjective φ hφ
  exact ⟨fractionField_essFiniteType k A E,
    fractionField_trdeg_eq_one k A E hdim, adjoin_coordinates_eq_top k A E φ hφ⟩

theorem finite_over_every_parameter [Algebra.FiniteType k A]
    (hdim : ringKrullDim A = 1) :
    ∀ f : E, Transcendental k f →
      FiniteDimensional (IntermediateField.adjoin k {f}) E := by
  let := fractionField_essFiniteType k A E
  exact CurveParameterFinite.finite_over_every_parameter k E
    (fractionField_trdeg_eq_one k A E hdim)

omit [IsDomain A] in
theorem ringKrullDim_eq_one_of_affine_iso
    (X : Scheme) (e : X ≅ Spec (.of A)) (hdim : topologicalKrullDim X = 1) :
    ringKrullDim A = 1 := by
  have h := e.hom.homeomorph.isHomeomorph.topologicalKrullDim_eq
  change topologicalKrullDim X = topologicalKrullDim (PrimeSpectrum A) at h
  rw [PrimeSpectrum.topologicalKrullDim_eq_ringKrullDim] at h
  exact h.symm.trans hdim

@[instance_reducible] def intrinsicSectionAlgebra (X : Scheme) [IsIntegral X] :
    Algebra Γ(X, ⊤) X.functionField := by
  letI : Nonempty (⊤ : X.Opens) := ⟨⟨genericPoint X, trivial⟩⟩
  exact (X.germToFunctionField ⊤).hom.toAlgebra

attribute [local instance] intrinsicSectionAlgebra

@[instance_reducible] def intrinsicFunctionFieldAlgebra (k : Type*) [Field k]
    (X : Scheme) [IsIntegral X] [Algebra k Γ(X, ⊤)] :
    Algebra k X.functionField :=
  ((algebraMap Γ(X, ⊤) X.functionField).comp (algebraMap k Γ(X, ⊤))).toAlgebra

end PiExponent.CurveGeometricFunctionField

end

end OAI
end Source0547

-- Source: OAI/NumberTheory/PiExponent/Cohomology/EulerSupportDimension.lean
section Source0548
/-
Modification notice for the LogTwo project.
Derived from openai/math (Apache-2.0), revision adc7f1241b42e322a6451854ab7e4b4c146bf78a.
Original source: lean/OAI/NumberTheory/PiExponent/Cohomology/EulerSupportDimension.lean
Changes: Convert module/import declarations to the Lean 4.34 public module format.
See ../THIRD_PARTY_NOTICES.txt for provenance and the recorded changes.
-/

namespace OAI

namespace PiExponent.NumericalAmpleness
noncomputable section
open AlgebraicGeometry CategoryTheory TopologicalSpace
open PiExponentSeshadri.Geometry PiExponentSeshadri.Frames
open PiExponent.SectionZeroIdeal
open scoped nonZeroDivisors

theorem dimension_le_of_local_bound {T : Type*} [TopologicalSpace T] (d : ℕ)
    (h : ∀ x : T, ∃ U : Opens T, x ∈ U ∧ topologicalKrullDim U ≤ d) :
    topologicalKrullDim T ≤ d := by
  rw [← ENat.WithBot.lt_add_one_iff]
  suffices topologicalKrullDim T < ((d+1 : ℕ) : WithBot ℕ∞) by
    simpa only [Nat.cast_add, Nat.cast_one] using this
  apply Order.krullDim_lt_coe_iff.mpr
  intro c
  obtain ⟨x, hx⟩ := c.head.isIrreducible.nonempty
  obtain ⟨U, hxU, hU⟩ := h x
  let e := IrreducibleCloseds.orderIsoOfIsOpenEmbedding
    (Subtype.val : U → T) U.isOpen.isOpenEmbedding_subtypeVal
  have hm (i : Fin (c.length + 1)) :
      ((Subtype.val : U → T) ⁻¹' (c i : Set T)).Nonempty := by
    refine ⟨⟨x, hxU⟩, ?_⟩
    exact c.strictMono.monotone (Fin.zero_le i) hx
  let c' : LTSeries {Z : IrreducibleCloseds T |
      ((Subtype.val : U → T) ⁻¹' (Z : Set T)).Nonempty} :=
    ⟨c.length, fun i => ⟨c i, hm i⟩, fun i => c.step i⟩
  have hc := (Order.LTSeries.length_le_krullDim (c'.map e.symm e.symm.strictMono)).trans hU
  have hc' : c.length ≤ d := by exact_mod_cast hc
  omega

variable {X : Scheme.{0}}

private theorem mono_comp_iso {C : Type*} [Category C] {A B D : C}
    (g : A ⟶ B) (e : B ≅ D) (hg : Mono g) : Mono (g ≫ e.hom) := by
  let : Mono g := hg
  infer_instance

private theorem eulerSupport_mono_iso_inv_comp {C : Type*} [Category C] {A B D : C}
    (e : A ≅ B) (g : A ⟶ D) (hg : Mono g) : Mono (e.inv ≫ g) := by
  let : Mono g := hg
  infer_instance

theorem section_coefficient_regular (L : LineBundle X)
    (s : GlobalSections X L.sheaf) [Mono s] (U : X.Opens)
    (e : L.sheaf.restrict U.ι ≅ structureSheaf U.toScheme) :
    IsRegular (coefficient e (restrictSection U.ι s)) := by
  let g : PiExponentSeshadri.UnitEndomorphism.unit U.toScheme ⟶
      PiExponentSeshadri.UnitEndomorphism.unit U.toScheme := restrictSection U.ι s ≫ e.hom
  have hmap : Mono ((Scheme.Modules.restrictFunctor U.ι).map s) :=
    @Functor.map_mono _ _ _ _ (Scheme.Modules.restrictFunctor U.ι)
      inferInstance _ _ s ‹Mono s›
  have hrestrict : Mono (restrictSection U.ι s) :=
    eulerSupport_mono_iso_inv_comp (C := U.toScheme.Modules) (Scheme.Modules.restrictUnitIso U.ι)
      ((Scheme.Modules.restrictFunctor U.ι).map s) hmap
  have : Mono g := mono_comp_iso (C := U.toScheme.Modules) (restrictSection U.ι s) e hrestrict
  exact PiExponentSeshadri.UnitEndomorphism.equation_regular g ⊤

theorem section_affine_coefficient_nonZeroDivisor (L : LineBundle X)
    (s : GlobalSections X L.sheaf) [Mono s] (U : X.affineOpens)
    (e : L.sheaf.restrict U.1.ι ≅ structureSheaf U.1.toScheme) :
    U.1.topIso.hom (coefficient e (restrictSection U.1.ι s)) ∈ (Γ(X, U))⁰ := by
  let f := U.1.topIso.commRingCatIsoToRingEquiv
  rw [← MulEquivClass.map_nonZeroDivisors f]
  exact Submonoid.mem_map.mpr ⟨_,
    isRegular_iff_mem_nonZeroDivisors.mp (section_coefficient_regular L s U.1 e), rfl⟩

theorem regular_sectionZero_dimension_le (L : LineBundle X)
    (s : GlobalSections X L.sheaf) [Mono s] (d : ℕ)
    (hdim : topologicalKrullDim X ≤ d + 1) :
    topologicalKrullDim (zeroIdeal L s).subscheme ≤ d := by
  let I := zeroIdeal L s
  apply dimension_le_of_local_bound d
  intro y
  obtain ⟨V, hxV, ⟨eV⟩⟩ := L.locallyRankOne (I.subschemeι y)
  obtain ⟨W, hW, hxW, hWV⟩ := exists_isAffineOpen_mem_and_subset hxV
  let U : X.affineOpens := ⟨W, hW⟩
  let e := restrictOpenFrame hWV eV
  let : IsOpenImmersion (I.subschemeCover.f U) := I.subschemeCover.map_prop U
  let f := I.subschemeCover.f U
  refine ⟨f.opensRange, ?_, ?_⟩
  · change y ∈ (I.subschemeCover.f U).opensRange
    rw [Scheme.IdealSheafData.opensRange_subschemeCover_map]
    exact hxW
  · have hr := section_affine_coefficient_nonZeroDivisor L s U e
    have hdrop := ringKrullDim_quotient_succ_le_of_nonZeroDivisor hr
    rw [← zeroIdeal_on_frame L s U e] at hdrop
    have hring : ringKrullDim Γ(X,U) ≤ d + 1 := by
      rw [← PrimeSpectrum.topologicalKrullDim_eq_ringKrullDim]
      change topologicalKrullDim (Spec Γ(X,U)) ≤ d+1
      rw [← IsHomeomorph.topologicalKrullDim_eq _ U.2.isoSpec.hom.homeomorph.isHomeomorph]
      exact (topologicalKrullDim_subspace_le X U).trans hdim
    have hquot : ringKrullDim (Γ(X,U) ⧸ I.ideal U) ≤ d := by
      have hbound := hdrop.trans hring
      exact ENat.WithBot.add_le_add_one_right_iff.mp hbound
    have hsource : topologicalKrullDim (Spec (I.subschemeCover.X U)) ≤ d := by
      exact (PrimeSpectrum.topologicalKrullDim_eq_ringKrullDim _).le.trans hquot
    change topologicalKrullDim f.opensRange.toScheme ≤ d
    exact (IsHomeomorph.topologicalKrullDim_eq _
      f.isoOpensRange.hom.homeomorph.isHomeomorph).symm.le.trans hsource

end
end PiExponent.NumericalAmpleness

end OAI
end Source0548

-- Source: OAI/NumberTheory/PiExponent/LocalAlgebra/IntegralAffineOpenDimension.lean
section Source0549
/-
Modification notice for the LogTwo project.
Derived from openai/math (Apache-2.0), revision adc7f1241b42e322a6451854ab7e4b4c146bf78a.
Original source: lean/OAI/NumberTheory/PiExponent/LocalAlgebra/IntegralAffineOpenDimension.lean
Changes: Convert module/import declarations to the Lean 4.34 public module format.
See ../THIRD_PARTY_NOTICES.txt for provenance and the recorded changes.
-/

namespace OAI

noncomputable section
namespace PiExponent.IntegralAffineOpenDimension
open CategoryTheory AlgebraicGeometry TopologicalSpace
universe u
variable {k : Type u} [Field k] {X : Scheme.{u}} [IsIntegral X]
variable (p : X ⟶ Spec (.of k))

def chartConstants (U : X.affineOpens) : k →+* Γ(X, U.1) :=
  (Spec.preimage (U.2.fromSpec ≫ p)).hom

@[instance_reducible] def chartAlgebra (U : X.affineOpens) : Algebra k Γ(X, U.1) :=
  (chartConstants p U).toAlgebra

@[instance_reducible] def functionFieldAlgebra : Algebra k X.functionField :=
  (Spec.preimage (X.fromSpecStalk (genericPoint X) ≫ p)).hom.toAlgebra

theorem germToFunctionField_fromSpec (U : X.affineOpens) [Nonempty U.1] :
    Spec.map (X.germToFunctionField U.1) ≫ U.2.fromSpec =
      X.fromSpecStalk (genericPoint X) :=
  U.2.fromSpecStalk_eq_fromSpecStalk _

theorem chart_functionField_scalarTower (U : X.affineOpens) [Nonempty U.1] :
    letI := chartAlgebra p U
    letI := functionFieldAlgebra p
    IsScalarTower k Γ(X, U.1) X.functionField := by
  let := chartAlgebra p U
  let := functionFieldAlgebra p
  have h : Spec.preimage (U.2.fromSpec ≫ p) ≫ X.germToFunctionField U.1 =
      Spec.preimage (X.fromSpecStalk (genericPoint X) ≫ p) := by
    apply Spec.map_injective
    rw [Spec.map_comp, Spec.map_preimage, ← Category.assoc,
      germToFunctionField_fromSpec, Spec.map_preimage]
  exact IsScalarTower.of_algebraMap_eq' (CommRingCat.hom_ext_iff.mp h).symm

omit [IsIntegral X] in
theorem chart_finiteType [LocallyOfFiniteType p] (U : X.affineOpens) :
    letI := chartAlgebra p U
    Algebra.FiniteType k Γ(X, U.1) := by
  let := chartAlgebra p U
  have h : LocallyOfFiniteType (Spec.map (Spec.preimage (U.2.fromSpec ≫ p))) := by
    rw [Spec.map_preimage]
    let hOpen : IsOpenImmersion U.2.fromSpec := U.2.isOpenImmersion_fromSpec
    let : LocallyOfFiniteType U.2.fromSpec :=
      @locallyOfFiniteType_of_isOpenImmersion _ _ U.2.fromSpec hOpen
    exact locallyOfFiniteType_comp U.2.fromSpec p
  have h' : RingHom.FiniteType (chartConstants p U) := HasRingHomProperty.Spec_iff.mp h
  exact RingHom.finiteType_algebraMap.mp h'

theorem chart_ring_dimension [LocallyOfFiniteType p] (U : X.affineOpens) [Nonempty U.1] :
    letI := functionFieldAlgebra p
    ringKrullDim Γ(X, U.1) = ((Algebra.trdeg k X.functionField).toNat : WithBot ℕ∞) := by
  let := chartAlgebra p U
  let := functionFieldAlgebra p
  let := chart_functionField_scalarTower p U
  let := chart_finiteType p U
  let := functionField_isFractionRing_of_isAffineOpen X U.1 U.2
  let : FaithfulSMul Γ(X, U.1) X.functionField :=
    (faithfulSMul_iff_algebraMap_injective _ _).mpr (IsFractionRing.injective _ _)
  rw [PiExponentJets.W24.finiteType_domain_krullDim_eq_trdeg k Γ(X, U.1),
    PiExponentJets.W24.localization_trdeg_toNat_eq k Γ(X, U.1) X.functionField
      (nonZeroDivisors Γ(X, U.1))]

omit [IsIntegral X] in
theorem affine_dimension_eq_ring (U : X.affineOpens) :
    topologicalKrullDim U.1 = ringKrullDim Γ(X, U.1) := by
  have h := U.2.isoSpec.hom.homeomorph.isHomeomorph.topologicalKrullDim_eq
  change topologicalKrullDim U.1 = topologicalKrullDim (PrimeSpectrum Γ(X, U.1)) at h
  exact h.trans (PrimeSpectrum.topologicalKrullDim_eq_ringKrullDim _)

theorem affine_open_dimension_eq [LocallyOfFiniteType p] (U : X.affineOpens) [Nonempty U.1] :
    topologicalKrullDim U.1 = topologicalKrullDim X := by
  let := functionFieldAlgebra p
  have hU : topologicalKrullDim U.1 =
      ((Algebra.trdeg k X.functionField).toNat : WithBot ℕ∞) :=
    (affine_dimension_eq_ring U).trans (chart_ring_dimension p U)
  apply le_antisymm (topologicalKrullDim_subspace_le X U.1)
  change topologicalKrullDim X ≤ topologicalKrullDim U.1
  rw [hU]
  apply PiExponent.NumericalAmpleness.dimension_le_of_local_bound
  intro x
  obtain ⟨V, hV, hxV, _⟩ := exists_isAffineOpen_mem_and_subset (Opens.mem_top x)
  let : Nonempty V := ⟨⟨x, hxV⟩⟩
  exact ⟨V, hxV, ((affine_dimension_eq_ring ⟨V, hV⟩).trans
    (chart_ring_dimension p ⟨V, hV⟩)).le⟩

theorem affine_ring_dimension_eq [LocallyOfFiniteType p] (U : X.affineOpens) [Nonempty U.1] :
    ringKrullDim Γ(X, U.1) = topologicalKrullDim X :=
  (affine_dimension_eq_ring U).symm.trans (affine_open_dimension_eq p U)

end PiExponent.IntegralAffineOpenDimension

end

end OAI
end Source0549

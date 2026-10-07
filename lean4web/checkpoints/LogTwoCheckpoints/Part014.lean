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
public import LogTwoCheckpoints.Part005
public import LogTwoCheckpoints.Part011
public import LogTwoCheckpoints.Part012
public import LogTwoCheckpoints.Part013
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Quasicoherent
public import Mathlib.AlgebraicGeometry.FunctionField
public import Mathlib.AlgebraicGeometry.IdealSheaf.Functorial
public import Mathlib.AlgebraicGeometry.Morphisms.UniversallyInjective
public import Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Proper
public import Mathlib.AlgebraicGeometry.SpreadingOut
public import Mathlib.Analysis.Complex.Polynomial.Basic
public import Mathlib.NumberTheory.FunctionField
public import Mathlib.RingTheory.MvPolynomial.Homogeneous
@[expose] public section
set_option Elab.async false

-- Source: OAI/NumberTheory/PiExponent/Geometry/CurveNormalizationLocalRing.lean
section Source0350
-- Modified in this edition: unused plain lemmas removed; see reduction.json.
/-
Modification notice for the LogTwo project.
Derived from openai/math (Apache-2.0), revision adc7f1241b42e322a6451854ab7e4b4c146bf78a.
Original source: lean/OAI/NumberTheory/PiExponent/Geometry/CurveNormalizationLocalRing.lean
Changes: Convert module/import declarations to the Lean 4.34 public module format.
See ../THIRD_PARTY_NOTICES.txt for provenance and the recorded changes.
-/

namespace OAI

noncomputable section

namespace PiExponent.CurveNormalizationModel
open scoped Polynomial
open AlgebraicGeometry CategoryTheory
open PiExponent.CurveZeroPole

universe u
variable {F E : Type u} [Field F] [Field E] [Algebra F E]
variable (f : E) (hf : Transcendental F f)

def parameterChartProjection : Spec (.of (parameterChart f hf)) ⟶ Spec (.of F[X]) :=
  letI := parameterPolynomialAlgebra f hf
  Spec.map (CommRingCat.ofHom (algebraMap F[X] (parameterChart f hf)))

instance parameterChartProjection_isFinite [CharZero F]
    [FiniteDimensional (IntermediateField.adjoin F {f}) E] :
    IsFinite (parameterChartProjection f hf) := by
  let := parameterAlgebra f hf
  let := parameterPolynomialAlgebra f hf
  let := parameter_scalarTower f hf
  let := parameter_finite f hf
  rw [parameterChartProjection, IsFinite.SpecMap_iff]
  change (algebraMap F[X] (parameterChart f hf)).Finite
  rw [RingHom.finite_algebraMap]
  infer_instance

theorem parameterChart_localDVR [CharZero F]
    [FiniteDimensional (IntermediateField.adjoin F {f}) E]
    (q : PrimeSpectrum (parameterChart f hf)) (hq : q.asIdeal ≠ ⊥) :
    IsDiscreteValuationRing (Localization.AtPrime q.asIdeal) := by
  let := parameterAlgebra f hf
  let := parameterPolynomialAlgebra f hf
  let := parameter_scalarTower f hf
  let := parameter_finite f hf
  exact IsLocalization.AtPrime.isDiscreteValuationRing_of_dedekind_domain
    (parameterChart f hf) hq (Localization.AtPrime q.asIdeal)

theorem zeroChart_stalkDVR [CharZero F]
    [FiniteDimensional (IntermediateField.adjoin F {f}) E]
    (q : PrimeSpectrum (parameterChart f hf)) (hq : q.asIdeal ≠ ⊥) :
    IsDiscreteValuationRing
      ((parameterCurve f hf).presheaf.stalk (zeroChartInclusion f hf q)) := by
  let := parameterChart_localDVR f hf q hq
  exact IsDiscreteValuationRing.RingEquivClass.isDiscreteValuationRing
    (zeroChartStalkIso f hf q).commRingCatIsoToRingEquiv.symm

theorem infinityChart_stalkDVR [CharZero F]
    [FiniteDimensional (IntermediateField.adjoin F {f}) E]
    (q : PrimeSpectrum (parameterChart f⁻¹ (transcendental_inverse f hf)))
    (hq : q.asIdeal ≠ ⊥) :
    IsDiscreteValuationRing
      ((parameterCurve f hf).presheaf.stalk (infinityChartInclusion f hf q)) := by
  let : FiniteDimensional (IntermediateField.adjoin F {f⁻¹}) E :=
    (adjoin_inverse_eq (F := F) f).symm ▸ inferInstance
  let := parameterChart_localDVR f⁻¹ (transcendental_inverse f hf) q hq
  exact IsDiscreteValuationRing.RingEquivClass.isDiscreteValuationRing
    (infinityChartStalkIso f hf q).commRingCatIsoToRingEquiv.symm

theorem parameterCurve_stalkDVR [CharZero F]
    [FiniteDimensional (IntermediateField.adjoin F {f}) E]
    (x : parameterCurve f hf) (hx : x ≠ genericPoint (parameterCurve f hf)) :
    IsDiscreteValuationRing ((parameterCurve f hf).presheaf.stalk x) := by
  rcases parameterCurve_twoChartCover f hf x with ⟨q, rfl⟩ | ⟨q, rfl⟩
  · apply zeroChart_stalkDVR f hf q
    intro hq
    have heq : q = genericPoint (Spec (.of (parameterChart f hf))) := by
      rw [genericPoint_eq_bot_of_affine]
      exact PrimeSpectrum.ext hq
    apply hx
    rw [heq]
    exact genericPoint_eq_of_isOpenImmersion (zeroChartInclusion f hf)
  · apply infinityChart_stalkDVR f hf q
    intro hq
    have heq : q = genericPoint
        (Spec (.of (parameterChart f⁻¹ (transcendental_inverse f hf)))) := by
      rw [genericPoint_eq_bot_of_affine]
      exact PrimeSpectrum.ext hq
    apply hx
    rw [heq]
    exact genericPoint_eq_of_isOpenImmersion (infinityChartInclusion f hf)

end PiExponent.CurveNormalizationModel

end

end OAI
end Source0350

-- Source: OAI/NumberTheory/PiExponent/Geometry/CurveProperExtension.lean
section Source0351
-- Modified in this edition: unused plain lemmas removed; see reduction.json.
/-
Modification notice for the LogTwo project.
Derived from openai/math (Apache-2.0), revision adc7f1241b42e322a6451854ab7e4b4c146bf78a.
Original source: lean/OAI/NumberTheory/PiExponent/Geometry/CurveProperExtension.lean
Changes: Convert module/import declarations to the Lean 4.34 public module format.
See ../THIRD_PARTY_NOTICES.txt for provenance and the recorded changes.
-/

namespace OAI

noncomputable section
universe u
namespace PiExponent.CurveProperExtension
open AlgebraicGeometry CategoryTheory

theorem fractionMap_fromSpecStalk
    (X : Scheme.{u}) [IsIntegral X] (x : X) :
    Spec.map (CommRingCat.ofHom (algebraMap (X.presheaf.stalk x) X.functionField)) ≫
      X.fromSpecStalk x = X.fromSpecStalk (genericPoint X) := by
  change Spec.map (X.presheaf.stalkSpecializes ((genericPoint_spec X).specializes trivial)) ≫
    X.fromSpecStalk x = _
  exact Scheme.SpecMap_stalkSpecializes_fromSpecStalk _

theorem exists_stalk_map
    {X Y S : Scheme.{u}} [IsIntegral X]
    (sX : X ⟶ S) (sY : Y ⟶ S) [IsProper sY]
    (hDVR : ∀ x : X, x ≠ genericPoint X → IsDiscreteValuationRing (X.presheaf.stalk x))
    (η : Spec X.functionField ⟶ Y)
    (hη : η ≫ sY = X.fromSpecStalk (genericPoint X) ≫ sX) (x : X) :
    ∃ φ : Spec (X.presheaf.stalk x) ⟶ Y,
      φ ≫ sY = X.fromSpecStalk x ≫ sX ∧
      Spec.map (CommRingCat.ofHom (algebraMap (X.presheaf.stalk x) X.functionField)) ≫ φ = η := by
  by_cases hx : x = genericPoint X
  · subst x
    refine ⟨η, hη, ?_⟩
    change Spec.map (X.presheaf.stalkSpecializes ((genericPoint_spec X).specializes trivial)) ≫ η = η
    simp
  · let := hDVR x hx
    have hval : ValuativeCriterion sY := by
      have h : IsProper sY := inferInstance
      rw [IsProper.eq_valuativeCriterion] at h
      exact h.1.1.1
    let sq : ValuativeCommSq sY :=
      { R := X.presheaf.stalk x
        commRing := inferInstanceAs (CommRing (X.presheaf.stalk x))
        domain := inferInstanceAs (IsDomain (X.presheaf.stalk x))
        valuationRing := inferInstanceAs (ValuationRing (X.presheaf.stalk x))
        K := X.functionField
        field := inferInstanceAs (Field X.functionField)
        algebra := inferInstanceAs (Algebra (X.presheaf.stalk x) X.functionField)
        isFractionRing := inferInstanceAs (IsFractionRing (X.presheaf.stalk x) X.functionField)
        i₁ := η
        i₂ := X.fromSpecStalk x ≫ sX
        commSq := ⟨by
          rw [hη]
          exact (congrArg (fun g => g ≫ sX) (fractionMap_fromSpecStalk X x)).symm.trans
            (Category.assoc _ _ _)⟩ }
    obtain ⟨φ, hφ, hbase⟩ := (hval.existence sq).exists_lift
    exact ⟨φ, hbase, hφ⟩

end PiExponent.CurveProperExtension

end

end OAI
end Source0351

-- Source: OAI/NumberTheory/PiExponent/Geometry/CurveMonomialMap.lean
section Source0352
-- Modified in this edition: unused plain lemmas removed; see reduction.json.
/-
Modification notice for the LogTwo project.
Derived from openai/math (Apache-2.0), revision adc7f1241b42e322a6451854ab7e4b4c146bf78a.
Original source: lean/OAI/NumberTheory/PiExponent/Geometry/CurveMonomialMap.lean
Changes: Convert module/import declarations to the Lean 4.34 public module format.
See ../THIRD_PARTY_NOTICES.txt for provenance and the recorded changes.
-/

namespace OAI

noncomputable section
universe u
namespace PiExponent.CurveMonomialMap
open AlgebraicGeometry CategoryTheory MvPolynomial
open PiExponentSeshadri.Projective
open WeightedCompactification
attribute [local instance] MvPolynomial.gradedAlgebra

theorem fromUnitCoordinate_projection
    {F E σ : Type u} [CommRing F] [CommRing E]
    (k : F →+* E) (y : σ → E) (z : σ) (hz : y z = 1) :
    fromUnitCoordinate (eval₂Hom k y) (by decide) (poly_X_mem z)
      (by simpa only [eval₂Hom_X', hz] using (isUnit_one : IsUnit (1 : E))) ≫
      polynomialProjectiveProjection F σ = Spec.map (CommRingCat.ofHom k) := by
  simp only [fromUnitCoordinate, polynomialProjectiveProjection, Category.assoc,
    Proj.awayι_toSpecZero_assoc, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
  apply congrArg Spec.map
  apply CommRingCat.hom_ext
  apply RingHom.ext
  intro c
  change IsLocalization.Away.lift (X z)
    (by simpa only [eval₂Hom_X', hz] using (isUnit_one : IsUnit (1 : E)))
    (algebraMap (MvPolynomial σ F) (Localization.Away (X z)) (C c)) = k c
  rw [IsLocalization.Away.lift_eq, eval₂Hom_C]

theorem affineChartMap_projection
    {F ι σ : Type u} [CommRing F]
    (a : σ → ι →₀ ℕ) (z : σ) (hz : a z = 0)
    (coordinate : ι → σ) (hcoordinate : ∀ i, a (coordinate i) = Finsupp.single i 1) :
    affineChartMap (R := F) a z hz coordinate hcoordinate ≫ projection a =
      Spec.map (CommRingCat.ofHom (C : F →+* MvPolynomial ι F)) := by
  rw [projection, ← Category.assoc, affineChartMap_comp_projectiveMonomialMap]
  exact fromUnitCoordinate_projection C (fun s => monomial (a s) 1) z (by rw [hz]; exact MvPolynomial.C_1)

def genericMonomialMap
    {F E ι σ : Type u} [CommRing F] [CommRing E] [Algebra F E]
    (a : σ → ι →₀ ℕ) (z : σ) (hz : a z = 0)
    (coordinate : ι → σ) (hcoordinate : ∀ i, a (coordinate i) = Finsupp.single i 1)
    (x : ι → E) :
    Spec (CommRingCat.of E) ⟶ Proj (imageGrade (R := F) a) :=
  Spec.map (CommRingCat.ofHom (eval₂Hom (algebraMap F E) x)) ≫
    affineChartMap a z hz coordinate hcoordinate

end PiExponent.CurveMonomialMap

end

end OAI
end Source0352

-- Source: LogTwo/Geometry/WeightedCompactification.lean
section Source0353
-- Modified in this edition: unused plain lemmas removed; see reduction.json.
/-
Modification notice for the LogTwo project.
Adapted from openai/math (Apache-2.0), revision adc7f1241b42e322a6451854ab7e4b4c146bf78a.
Changes: Adapt the compactification to rational matrix weights and varying Y-centers.
See ../THIRD_PARTY_NOTICES.txt for provenance and the recorded changes.
-/

/-! The weighted monomial compactification for the actual matrix weights.
Adapted from openai/math, Ampleness/AdmissibleBlowupGeometry.lean at the pinned
commit (Apache-2.0). No fixed-Y center or interpolation theorem is imported.
The finite monomial index is used symbolically, never enumerated computationally.
See THIRD_PARTY_NOTICES.txt. -/
namespace LogTwo.Geometry.MatrixCompactification
open OAI PiExponent AlgebraicGeometry CategoryTheory TopologicalSpace
open LogTwo.Interpolation WeightedGeometryScale
noncomputable section
variable {m : ℕ} (w : Weights m)

def scale : Scale (rationalColumnWeight w) (jetWeight w) :=
  chooseScale _ _ (rationalColumnWeight_pos w) (jetWeight_pos w)

abbrev Index := (scale w).Index
abbrev exponents : Index w → Fin (m+1) →₀ ℕ := (scale w).exponents
abbrev constantIndex : Index w := (scale w).constantIndex (rationalColumnWeight_pos w)
abbrev coordinateIndex : Fin (m+1) → Index w :=
  (scale w).coordinateIndex (rationalColumnWeight_pos w)

instance index_nonempty : Nonempty (Index w) := ⟨constantIndex w⟩

abbrev space : Scheme := Proj (WeightedCompactification.imageGrade (R := ℂ) (exponents w))

def structureMap : space w ⟶ Spec (.of ℂ) :=
  WeightedCompactification.projection (exponents w)

instance structureMap_proper : IsProper (structureMap w) := by
  dsimp [structureMap]
  infer_instance

def affineChart : Spec (.of (MvPolynomial (Fin (m+1)) ℂ)) ⟶ space w :=
  WeightedCompactification.affineChartMap (exponents w) (constantIndex w)
    ((scale w).exponents_constant (rationalColumnWeight_pos w))
    (coordinateIndex w) ((scale w).exponents_coordinate (rationalColumnWeight_pos w))

instance affineChart_isOpenImmersion : IsOpenImmersion (affineChart w) := by
  dsimp [affineChart]
  infer_instance

def origin (_w : Weights m) : Spec (.of (MvPolynomial (Fin (m+1)) ℂ)) :=
  ⟨WeightedBezout.pointIdeal (0 : Fin (m+1) → ℂ), inferInstance⟩

instance space_nonempty : Nonempty (space w) := ⟨affineChart w (origin w)⟩
instance space_isIntegral : IsIntegral (space w) := by infer_instance
instance space_isLocallyNoetherian : IsLocallyNoetherian (space w) :=
  LocallyOfFiniteType.isLocallyNoetherian (structureMap w)
instance space_compact : CompactSpace (space w) :=
  QuasiCompact.compactSpace_of_compactSpace (structureMap w)
instance space_isNoetherian : IsNoetherian (space w) := {}
instance affineChart_quasiCompact : QuasiCompact (affineChart w) := by infer_instance

theorem affineChart_over : affineChart w ≫ structureMap w =
    Spec.map (CommRingCat.ofHom (algebraMap ℂ (MvPolynomial (Fin (m+1)) ℂ))) :=
  CurveMonomialMap.affineChartMap_projection (exponents w) (constantIndex w)
    ((scale w).exponents_constant (rationalColumnWeight_pos w))
    (coordinateIndex w) ((scale w).exponents_coordinate (rationalColumnWeight_pos w))

theorem degree_balance (i : Fin (m+1)) :
    rationalColumnWeight w i * ((scale w).degreePowers i : ℚ) = (scale w).radius :=
  (scale w).degreePowers_eq i

theorem jet_balance (i : Fin (m+1)) :
    jetWeight w i * ((scale w).jetPowers i : ℚ) = (scale w).radius :=
  (scale w).jetPowers_eq i

theorem monomial_budget (i : Index w) :
    (∑ j, rationalColumnWeight w j * ((exponents w i) j : ℚ)) ≤ (scale w).radius :=
  (scale w).budget (rationalColumnWeight_pos w) i

end
end LogTwo.Geometry.MatrixCompactification
end Source0353

-- Source: LogTwo/Geometry/WeightedJetIdeal.lean
section Source0354
-- Modified in this edition: unused plain lemmas removed; see reduction.json.
/-
Modification notice for the LogTwo project.
Adapted from openai/math (Apache-2.0), revision adc7f1241b42e322a6451854ab7e4b4c146bf78a.
Changes: Adapt ideal-support arguments to rational matrix weights and varying Y-centers.
See ../THIRD_PARTY_NOTICES.txt for provenance and the recorded changes.
-/

/-! Varying-center jet ideals on the concrete weighted compactification.
The chart, proper structure morphism, Noetherian hypotheses, and balanced
integer powers are constructed from the matrix weights. This does not yet
identify the global normalization curve's stalk maps or its divisor degrees.
Support arguments adapt openai/math Ampleness/AdmissibleBlowupGeometry.lean
(Apache-2.0); see THIRD_PARTY_NOTICES.txt. -/
namespace LogTwo.Geometry.MatrixCompactification
open OAI PiExponent AlgebraicGeometry CategoryTheory
open LogTwo.Interpolation LogTwo.Arithmetic
open CurveValuationCenter PlaceValuationRing PlaceCenteredBranch CurveCenters
noncomputable section
variable {m : ℕ} (w : Weights m)

def centerIdeal {J : Type*} [Fintype J]
    (y : J → ℂ) (c : J → Fin m → ℂ) (T : Fin m → ℕ) : (space w).IdealSheafData :=
  CompactJetIdealAt.compactIdeal y c T (scale w).jetPowers (affineChart w)

theorem centerIdeal_restrict {J : Type*} [Fintype J]
    (y : J → ℂ) (c : J → Fin m → ℂ) (T : Fin m → ℕ) :
    (centerIdeal w y c T).comap (affineChart w) =
      CompactJetIdealAt.affineIdeal y c T (scale w).jetPowers :=
  CompactJetIdealAt.restrict_compactIdeal _ _ _ _ _

theorem centerIdeal_support {J : Type*} [Fintype J]
    (y : J → ℂ) (c : J → Fin m → ℂ) (T : Fin m → ℕ) :
    ((centerIdeal w y c T).support : Set (space w)) =
      ⋃ j, Set.range (CompactJetIdealAt.point (y j) (c j) ≫ affineChart w) :=
  CompactJetIdealAt.support_compactIdeal _ _ _ _ (scale w).jetPowers_pos _
    (structureMap w) (affineChart_over w)

theorem centerIdeal_support_subset_chart {J : Type*} [Fintype J]
    (y : J → ℂ) (c : J → Fin m → ℂ) (T : Fin m → ℕ) :
    ((centerIdeal w y c T).support : Set (space w)) ⊆ (affineChart w).opensRange := by
  rw [centerIdeal_support]
  intro x hx
  obtain ⟨j,z,rfl⟩ := Set.mem_iUnion.mp hx
  exact ⟨CompactJetIdealAt.point (y j) (c j) z, rfl⟩

theorem centerIdeal_affine_pullback {J : Type*} [Fintype J]
    (y : J → ℂ) (c : J → Fin m → ℂ) (T : Fin m → ℕ)
    {A : Type} [CommRing A] (f : MvPolynomial (Fin (m+1)) ℂ →+* A) :
    (centerIdeal w y c T).comap (Spec.map (CommRingCat.ofHom f) ≫ affineChart w) =
      PiExponentSeshadri.IdealPullback.specIdeal
        ((jetProductIdeal y c T (scale w).jetPowers).map f) :=
  CompactJetIdealAt.comap_compactIdeal_spec _ _ _ _ _ f

theorem origin_ne_center (y : ℂ) (hy : y ≠ 0) (c : Fin m → ℂ) :
    origin w ≠ centerPrime y c := by
  intro h
  have hx : MvPolynomial.X (0 : Fin (m+1)) ∈ (origin w).asIdeal := by
    change MvPolynomial.aeval (0 : Fin (m+1) → ℂ) (MvPolynomial.X 0) = 0
    simp
  rw [h] at hx
  change MvPolynomial.aeval (centerPoint y c) (MvPolynomial.X 0) = 0 at hx
  exact hy (by simpa [centerPoint] using hx)

theorem origin_avoids_centers {J : Type*} [Fintype J]
    (y : J → ℂ) (hy : ∀ j, y j ≠ 0) (c : J → Fin m → ℂ) (T : Fin m → ℕ) :
    affineChart w (origin w) ∉ (centerIdeal w y c T).support := by
  change affineChart w (origin w) ∉ ((centerIdeal w y c T).support : Set (space w))
  rw [centerIdeal_support]
  intro h
  obtain ⟨j,hj⟩ := Set.mem_iUnion.mp h
  obtain ⟨z,hz⟩ := hj
  have he : CompactJetIdealAt.point (y j) (c j) z = origin w :=
    (affineChart w).isOpenEmbedding.injective hz
  have hc : CompactJetIdealAt.point (y j) (c j) z = centerPrime (y j) (c j) := by
    apply Set.mem_singleton_iff.mp
    erw [← CompactJetIdealAt.range_point]
    exact ⟨z,rfl⟩
  exact origin_ne_center w (y j) (hy j) (c j) (he.symm.trans hc)

theorem centerIdeal_support_ne_top {J : Type*} [Fintype J]
    (y : J → ℂ) (hy : ∀ j, y j ≠ 0) (c : J → Fin m → ℂ) (T : Fin m → ℕ) :
    (centerIdeal w y c T).support ≠ ⊤ := by
  intro h
  exact origin_avoids_centers w y hy c T (by rw [h]; trivial)

/-- The manuscript's actual centers; rational r_i are cast only at the geometry boundary. -/
def logTwoIdeal (r : Fin m → ℚ) (T : Fin m → ℕ) : (space w).IdealSheafData :=
  centerIdeal w (fun j : Fin w.K => (2 : ℂ) ^ j.val)
    (fun j i => (j.val : ℂ) * (r i : ℂ)) T

variable {E : Type} [Field E] [Algebra ℂ E]
variable (p : NormalizedPlace ℂ E)

def branchMap {J : Type*} (y : J → ℂ) (c : J → Fin m → ℂ)
    (z : Fin (m+1) → E) (j : J) (hc : Centered z (centerPoint (y j) (c j)) p) :
    Spec (.of (ring p)) ⟶ space w :=
  Spec.map (CommRingCat.ofHom
    (MvPolynomial.aeval (lift p z (centerPoint (y j) (c j)) hc)).toRingHom) ≫ affineChart w

theorem branchMap_generic {J : Type*} (y : J → ℂ) (c : J → Fin m → ℂ)
    (z : Fin (m+1) → E) (j : J) (hc : Centered z (centerPoint (y j) (c j)) p) :
    Spec.map (CommRingCat.ofHom (algebraMap (ring p) E)) ≫ branchMap w p y c z j hc =
      Spec.map (CommRingCat.ofHom (MvPolynomial.aeval z).toRingHom) ≫ affineChart w := by
  have h : (algebraMap (ring p) E).comp
      (MvPolynomial.aeval (lift p z (centerPoint (y j) (c j)) hc)).toRingHom =
      (MvPolynomial.aeval z).toRingHom :=
    RingHom.ext (lift_aeval p z (centerPoint (y j) (c j)) hc)
  rw [branchMap, ← Category.assoc, ← Spec.map_comp, ← CommRingCat.ofHom_comp, h]

theorem centerIdeal_branch_pullback {J : Type*} [Fintype J]
    (y : J → ℂ) (c : J → Fin m → ℂ) (z : Fin (m+1) → E)
    (j : J) (hc : Centered z (centerPoint (y j) (c j)) p) (T : Fin m → ℕ) :
    (centerIdeal w y c T).comap (branchMap w p y c z j hc) =
      PiExponentSeshadri.IdealPullback.specIdeal
        (localJetProductIdeal p y c z j hc T (scale w).jetPowers) :=
  centerIdeal_affine_pullback w y c T _

/-- The actual pulled-back sheaf ideal, expressed in the DVR via its affine
section ring. The computation follows ExceptionalCurveDegree.localIdeal_specIdeal. -/
def branchIdeal {J : Type*} [Fintype J]
    (y : J → ℂ) (c : J → Fin m → ℂ) (z : Fin (m+1) → E)
    (j : J) (hc : Centered z (centerPoint (y j) (c j)) p) (T : Fin m → ℕ) : Ideal (ring p) :=
  (((centerIdeal w y c T).comap (branchMap w p y c z j hc)).ideal
    ⟨⊤, isAffineOpen_top _⟩).map (Scheme.ΓSpecIso (CommRingCat.of (ring p))).hom.hom

theorem branchIdeal_eq {J : Type*} [Fintype J]
    (y : J → ℂ) (c : J → Fin m → ℂ) (z : Fin (m+1) → E)
    (j : J) (hc : Centered z (centerPoint (y j) (c j)) p) (T : Fin m → ℕ) :
    branchIdeal w p y c z j hc T = localJetProductIdeal p y c z j hc T (scale w).jetPowers := by
  rw [branchIdeal, centerIdeal_branch_pullback,
    PiExponentSeshadri.IdealPullback.specIdeal_top, Ideal.map_map]
  have he : (Scheme.ΓSpecIso (CommRingCat.of (ring p))).hom.hom.comp
      (Scheme.ΓSpecIso (CommRingCat.of (ring p))).inv.hom = RingHom.id (ring p) := by
    apply RingHom.ext
    intro a
    exact (Scheme.ΓSpecIso (CommRingCat.of (ring p))).inv_hom_id_apply a
  rw [he, Ideal.map_id]

variable [Algebra.IsIntegral ℂ (IsLocalRing.ResidueField (ring p))]

theorem branch_colength_eq_contact {J : Type*} [Fintype J]
    (y : J → ℂ) (hy : Function.Injective y) (hy0 : ∀ j, y j ≠ 0)
    (c : J → Fin m → ℂ) (z : Fin (m+1) → E) (j : J)
    (hc : Centered z (centerPoint (y j) (c j)) p)
    (hnc : ∃ i, z i ≠ algebraMap ℂ E (centerPoint (y j) (c j) i))
    (F : ℚ) (hF : 1 / w.theta < F) :
    ((Module.length (ring p) ((ring p) ⧸
      branchIdeal w p y c z j hc (truncationOrders w F))).toNat : ℚ) =
      (scale w).radius * logContactAt p (y j) (hy0 j) z (c j) hc hnc (jetWeight w) := by
  rw [branchIdeal_eq]
  exact localJetProductIdeal_colength_eq_contact p y hy hy0 c z j hc hnc (jetWeight w)
    (jetWeight_pos w) _ (truncation_weight_strict w F hF) (scale w).radius
    (scale w).jetPowers (scale w).jetPowers_pos (jet_balance w)

theorem branch_colength_ne_top {J : Type*} [Fintype J]
    (y : J → ℂ) (hy : Function.Injective y) (hy0 : ∀ j, y j ≠ 0)
    (c : J → Fin m → ℂ) (z : Fin (m+1) → E) (j : J)
    (hc : Centered z (centerPoint (y j) (c j)) p)
    (hnc : ∃ i, z i ≠ algebraMap ℂ E (centerPoint (y j) (c j) i))
    (F : ℚ) (hF : 1 / w.theta < F) :
    Module.length (ring p) ((ring p) ⧸
      branchIdeal w p y c z j hc (truncationOrders w F)) ≠ ⊤ := by
  rw [branchIdeal_eq]
  exact localJetProductIdeal_colength_ne_top p y hy hy0 c z j hc hnc (jetWeight w)
    (jetWeight_pos w) _ (truncation_weight_strict w F hF) (scale w).radius
    (scale w).jetPowers (scale w).jetPowers_pos (jet_balance w)

end
end LogTwo.Geometry.MatrixCompactification
end Source0354

-- Source: OAI/NumberTheory/PiExponent/Geometry/CurveFunctionFieldCompatibility.lean
section Source0355
-- Modified in this edition: unused plain lemmas removed; see reduction.json.
/-
Modification notice for the LogTwo project.
Derived from openai/math (Apache-2.0), revision adc7f1241b42e322a6451854ab7e4b4c146bf78a.
Original source: lean/OAI/NumberTheory/PiExponent/Geometry/CurveFunctionFieldCompatibility.lean
Changes: Convert module/import declarations to the Lean 4.34 public module format.
See ../THIRD_PARTY_NOTICES.txt for provenance and the recorded changes.
-/

namespace OAI

noncomputable section
namespace PiExponent.CurveNormalizationModel
open CategoryTheory AlgebraicGeometry
universe u

def functionFieldRestriction {U X : Scheme.{u}} [IsIntegral U] [IsIntegral X]
    (i : U ⟶ X) [IsOpenImmersion i] : X.functionField ⟶ U.functionField :=
  eqToHom (congrArg (fun x => X.presheaf.stalk x)
    (genericPoint_eq_of_isOpenImmersion i).symm) ≫ i.stalkMap (genericPoint U)

private theorem stalkSpecializes_eqToHom (X : Scheme.{u}) {x y : X} (h : x = y) :
    X.presheaf.stalkSpecializes (Inseparable.of_eq h).specializes =
      eqToHom (congrArg (fun z => X.presheaf.stalk z) h.symm) := by
  subst y
  simp

private theorem stalkMap_eqToHom {U X : Scheme.{u}} (i : U ⟶ X)
    (x y : U) (h : x = y) :
    i.stalkMap x ≫ eqToHom (congrArg (fun z => U.presheaf.stalk z) h) =
      eqToHom (congrArg (fun z => X.presheaf.stalk (i z)) h) ≫ i.stalkMap y := by
  subst y
  simp

theorem functionFieldRestriction_comp {V U X : Scheme.{u}}
    [IsIntegral V] [IsIntegral U] [IsIntegral X]
    (j : V ⟶ U) (i : U ⟶ X) [IsOpenImmersion j] [IsOpenImmersion i] :
    functionFieldRestriction (j ≫ i) = functionFieldRestriction i ≫ functionFieldRestriction j := by
  symm
  unfold functionFieldRestriction
  rw [Scheme.Hom.stalkMap_comp]
  simp only [Category.assoc]
  rw [← Category.assoc (i.stalkMap (genericPoint U)),
    stalkMap_eqToHom i (genericPoint U) (j (genericPoint V))
      (genericPoint_eq_of_isOpenImmersion j).symm]
  simp

private theorem toStalk_eqToHom (A : CommRingCat.{u})
    (x y : PrimeSpectrum A) (h : x = y) :
    StructureSheaf.toStalk A x ≫ eqToHom (congrArg
      (fun z => (Spec A).presheaf.stalk z) h) = StructureSheaf.toStalk A y := by
  subst y
  exact Category.comp_id _

theorem functionFieldRestriction_toStalk {A B : CommRingCat.{u}} [IsDomain A] [IsDomain B]
    (f : A ⟶ B) [IsOpenImmersion (Spec.map f)] :
    StructureSheaf.toStalk A (genericPoint (Spec A)) ≫
      functionFieldRestriction (Spec.map f) =
      f ≫ StructureSheaf.toStalk B (genericPoint (Spec B)) := by
  unfold functionFieldRestriction
  erw [← Category.assoc, toStalk_eqToHom A _ _
    (genericPoint_eq_of_isOpenImmersion (Spec.map f)).symm]
  exact AlgebraicGeometry.stalkMap_toStalk f _

end PiExponent.CurveNormalizationModel

end

end OAI
end Source0355

-- Source: OAI/NumberTheory/PiExponent/Ampleness/AffineFunctionFieldCompatibility.lean
section Source0356
-- Modified in this edition: unused plain lemmas removed; see reduction.json.
/-
Modification notice for the LogTwo project.
Derived from openai/math (Apache-2.0), revision adc7f1241b42e322a6451854ab7e4b4c146bf78a.
Original source: lean/OAI/NumberTheory/PiExponent/Ampleness/AffineFunctionFieldCompatibility.lean
Changes: Convert module/import declarations to the Lean 4.34 public module format.
See ../THIRD_PARTY_NOTICES.txt for provenance and the recorded changes.
-/

namespace OAI

noncomputable section
namespace PiExponent.CurveNormalizationModel
open CategoryTheory AlgebraicGeometry
universe u
variable (A E : Type u) [CommRing A] [IsDomain A] [Field E]
  [Algebra A E] [IsFractionRing A E]

theorem isFractionRing_of_intermediate_domain
    (B : Type u) [CommRing B] [IsDomain B] [Algebra A B]
    [Algebra B E] [IsScalarTower A B E]
    (hB : Function.Injective (algebraMap B E)) : IsFractionRing B E where
  map_units b := isUnit_iff_ne_zero.mpr (by
    intro h
    exact (mem_nonZeroDivisors_iff_ne_zero.mp b.2) (hB (by simpa using h)))
  surj z := by
    obtain ⟨⟨a, s⟩, hs⟩ := IsLocalization.surj (nonZeroDivisors A) z
    have hn : algebraMap A B s ≠ 0 := by
      intro he
      have he' : algebraMap A E s = 0 := by
        rw [IsScalarTower.algebraMap_apply A B E, he, map_zero]
      exact (mem_nonZeroDivisors_iff_ne_zero.mp s.2)
        ((IsFractionRing.injective A E) (by simp at he'))
    refine ⟨⟨algebraMap A B a, ⟨algebraMap A B s, mem_nonZeroDivisors_iff_ne_zero.mpr hn⟩⟩, ?_⟩
    simpa only [← IsScalarTower.algebraMap_apply A B E] using hs
  exists_of_eq {a b} h := ⟨1, by simpa using hB h⟩

def affineFunctionFieldEquiv : (Spec (.of A)).functionField ≃+* E := by
  letI : Algebra A (Spec (.of A)).functionField :=
    AlgebraicGeometry.instAlgebraCarrierFunctionFieldSpec (.of A)
  letI : IsFractionRing A (Spec (.of A)).functionField :=
    functionField_isFractionRing_of_affine (.of A)
  exact (IsLocalization.algEquiv (nonZeroDivisors A) (Spec (.of A)).functionField E).toRingEquiv

@[simp] theorem affineFunctionFieldEquiv_toStalk (a : A) :
    affineFunctionFieldEquiv A E (StructureSheaf.toStalk A
      (genericPoint (Spec (.of A))) a) = algebraMap A E a := by
  let : Algebra A (Spec (.of A)).functionField :=
    AlgebraicGeometry.instAlgebraCarrierFunctionFieldSpec (.of A)
  let : IsFractionRing A (Spec (.of A)).functionField :=
    functionField_isFractionRing_of_affine (.of A)
  exact (IsLocalization.algEquiv (nonZeroDivisors A)
    (Spec (.of A)).functionField E).commutes a

theorem affineFunctionFieldEquiv_naturality
    (B : Type u) [CommRing B] [IsDomain B] [Algebra A B]
    [Algebra B E] [IsFractionRing B E] [IsScalarTower A B E]
    [IsOpenImmersion (Spec.map (CommRingCat.ofHom (algebraMap A B)))] :
    (affineFunctionFieldEquiv B E).toRingHom.comp
      (functionFieldRestriction (Spec.map (CommRingCat.ofHom (algebraMap A B)))).hom =
      (affineFunctionFieldEquiv A E).toRingHom := by
  let : Algebra A (Spec (.of A)).functionField :=
    AlgebraicGeometry.instAlgebraCarrierFunctionFieldSpec (.of A)
  let : IsFractionRing A (Spec (.of A)).functionField :=
    functionField_isFractionRing_of_affine (.of A)
  apply IsLocalization.ringHom_ext (nonZeroDivisors A)
  apply RingHom.ext
  intro a
  change affineFunctionFieldEquiv B E
    (functionFieldRestriction (Spec.map (CommRingCat.ofHom (algebraMap A B)))
      (StructureSheaf.toStalk A (genericPoint (Spec (.of A))) a)) =
    affineFunctionFieldEquiv A E
      (StructureSheaf.toStalk A (genericPoint (Spec (.of A))) a)
  have h := congrArg (fun h => h a)
    (functionFieldRestriction_toStalk (CommRingCat.ofHom (algebraMap A B)))
  change functionFieldRestriction (Spec.map (CommRingCat.ofHom (algebraMap A B)))
    (StructureSheaf.toStalk A (genericPoint (Spec (.of A))) a) =
    StructureSheaf.toStalk B (genericPoint (Spec (.of B))) (algebraMap A B a) at h
  rw [h, affineFunctionFieldEquiv_toStalk, affineFunctionFieldEquiv_toStalk]
  exact (IsScalarTower.algebraMap_apply A B E a).symm

end PiExponent.CurveNormalizationModel

end

end OAI
end Source0356

-- Source: OAI/NumberTheory/PiExponent/Geometry/CurveNormalizationOverlap.lean
section Source0357
/-
Modification notice for the LogTwo project.
Derived from openai/math (Apache-2.0), revision adc7f1241b42e322a6451854ab7e4b4c146bf78a.
Original source: lean/OAI/NumberTheory/PiExponent/Geometry/CurveNormalizationOverlap.lean
Changes: Convert module/import declarations to the Lean 4.34 public module format.
See ../THIRD_PARTY_NOTICES.txt for provenance and the recorded changes.
-/

namespace OAI

noncomputable section
namespace PiExponent.CurveNormalizationModel
open scoped Polynomial
open AlgebraicGeometry CategoryTheory
open PiExponent.CurveZeroPole
universe u
variable {F E : Type u} [Field F] [Field E] [Algebra F E]
variable (f : E) (hf : Transcendental F f)

theorem zeroOverlap_range :
    letI := parameterPolynomialAlgebra f hf
    Set.range (zeroOverlap f hf) =
      (PrimeSpectrum.basicOpen (algebraMap F[X] (parameterChart f hf) Polynomial.X) :
        Set (PrimeSpectrum (parameterChart f hf))) := by
  let := parameterPolynomialAlgebra f hf
  let := parameterLaurentAlgebra f hf
  let := parameterLaurent_scalarTower f hf
  let : Algebra (parameterChart f hf) (parameterLaurentChart f hf) :=
    (parameterChartOverlapHom f hf).toAlgebra
  have hX : algebraMap F[X] E Polynomial.X = f := by
    rw [parameterPolynomialAlgebra_map]; simp
  have : IsLocalization.Away f E := IsLocalization.of_le_isUnit (by
    rintro x ⟨n, rfl⟩
    exact (isUnit_iff_ne_zero.mpr hf.ne_zero).pow n)
  have : IsLocalization.Away (algebraMap F[X] E Polynomial.X) E := by
    simpa only [hX] using (inferInstance : IsLocalization.Away f E)
  have : IsLocalization.Away (algebraMap F[X] (parameterChart f hf) Polynomial.X)
      (parameterLaurentChart f hf) :=
    integralClosureTower_isLocalizationAway (S := LaurentPolynomial F) (E := E) Polynomial.X
  exact PrimeSpectrum.localization_away_comap_range _ _

theorem infinityOverlap_range :
    letI := parameterPolynomialAlgebra f⁻¹ (transcendental_inverse f hf)
    Set.range (infinityOverlap f hf) =
      (PrimeSpectrum.basicOpen
        (algebraMap F[X] (parameterChart f⁻¹ (transcendental_inverse f hf)) Polynomial.X) :
        Set (PrimeSpectrum (parameterChart f⁻¹ (transcendental_inverse f hf)))) := by
  let e := (reciprocalLaurentChartEquiv f hf).symm
  have : IsIso (CommRingCat.ofHom e.toRingHom) :=
    inferInstanceAs (IsIso e.toCommRingCatIso.hom)
  let g := Spec.map (CommRingCat.ofHom e.toRingHom)
  have : IsIso g :=
    inferInstanceAs (IsIso (Scheme.Spec.mapIso e.toCommRingCatIso.op).hom)
  have hfac : infinityOverlap f hf =
      g ≫ zeroOverlap f⁻¹ (transcendental_inverse f hf) := by
    unfold infinityOverlap zeroOverlap
    rw [CommRingCat.ofHom_comp, Spec.map_comp]
  have hrange : Set.range (infinityOverlap f hf) =
      Set.range (zeroOverlap f⁻¹ (transcendental_inverse f hf)) := by
    rw [hfac]
    ext x
    constructor
    · rintro ⟨z, rfl⟩
      exact ⟨g z, rfl⟩
    · rintro ⟨z, rfl⟩
      obtain ⟨w, rfl⟩ := g.surjective z
      exact ⟨w, rfl⟩
  exact hrange.trans (zeroOverlap_range f⁻¹ (transcendental_inverse f hf))

theorem infinityChart_mem_zero_iff
    (x : Spec (.of (parameterChart f⁻¹ (transcendental_inverse f hf)))) :
    infinityChartInclusion f hf x ∈ Set.range (zeroChartInclusion f hf) ↔
      x ∈ Set.range (infinityOverlap f hf) := by
  constructor
  · rintro ⟨y, hy⟩
    obtain ⟨k, fi, fj, z, hzi, hzj⟩ :=
      (Scheme.IsLocallyDirected.ι_eq_ι_iff
        (Limits.span (zeroOverlap f hf) (infinityOverlap f hf))).mp hy
    cases k with
    | none =>
      refine ⟨z, ?_⟩
      have he : fj = Limits.WalkingSpan.Hom.snd := Subsingleton.elim _ _
      simpa only [he, Limits.span_map_snd] using hzj
    | some k =>
      cases k with
      | left =>
        cases (show Limits.WidePushoutShape.Hom
          (some Limits.WalkingPair.left) (some Limits.WalkingPair.right) from fj)
      | right =>
        cases (show Limits.WidePushoutShape.Hom
          (some Limits.WalkingPair.right) (some Limits.WalkingPair.left) from fi)
  · rintro ⟨z, rfl⟩
    refine ⟨zeroOverlap f hf z, ?_⟩
    exact congrArg (fun g => g z) (parameterCurve_overlap_compatibility f hf)

theorem zeroChart_mem_infinity_iff
    (x : Spec (.of (parameterChart f hf))) :
    zeroChartInclusion f hf x ∈ Set.range (infinityChartInclusion f hf) ↔
      x ∈ Set.range (zeroOverlap f hf) := by
  constructor
  · rintro ⟨y, hy⟩
    obtain ⟨k, fi, fj, z, hzi, hzj⟩ :=
      (Scheme.IsLocallyDirected.ι_eq_ι_iff
        (Limits.span (zeroOverlap f hf) (infinityOverlap f hf))).mp hy.symm
    cases k with
    | none =>
      refine ⟨z, ?_⟩
      have he : fi = Limits.WalkingSpan.Hom.fst := Subsingleton.elim _ _
      simpa only [he, Limits.span_map_fst] using hzi
    | some k =>
      cases k with
      | left =>
        cases (show Limits.WidePushoutShape.Hom
          (some Limits.WalkingPair.left) (some Limits.WalkingPair.right) from fj)
      | right =>
        cases (show Limits.WidePushoutShape.Hom
          (some Limits.WalkingPair.right) (some Limits.WalkingPair.left) from fi)
  · rintro ⟨z, rfl⟩
    refine ⟨infinityOverlap f hf z, ?_⟩
    exact congrArg (fun g => g z) (parameterCurve_overlap_compatibility f hf).symm

end PiExponent.CurveNormalizationModel

end

end OAI
end Source0357

-- Source: OAI/NumberTheory/PiExponent/Cohomology/ProjectiveLineLaurent.lean
section Source0358
-- Modified in this edition: unused plain lemmas removed; see reduction.json.
/-
Modification notice for the LogTwo project.
Derived from openai/math (Apache-2.0), revision adc7f1241b42e322a6451854ab7e4b4c146bf78a.
Original source: lean/OAI/NumberTheory/PiExponent/Cohomology/ProjectiveLineLaurent.lean
Changes: Convert module/import declarations to the Lean 4.34 public module format.
See ../THIRD_PARTY_NOTICES.txt for provenance and the recorded changes.
-/

namespace OAI

noncomputable section
namespace PiExponent.ProjectiveLine

open CategoryTheory AlgebraicGeometry
universe u
variable (F : Type u) [CommRing F]

def zeroPolynomialMap : Polynomial F →+* LaurentPolynomial F :=
  Polynomial.toLaurent

def infinityPolynomialMap : Polynomial F →+* LaurentPolynomial F :=
  Polynomial.eval₂RingHom LaurentPolynomial.C (LaurentPolynomial.T (-1))

@[simp] theorem zeroPolynomialMap_C (r : F) :
    zeroPolynomialMap F (Polynomial.C r) = LaurentPolynomial.C r := by
  simp [zeroPolynomialMap]

@[simp] theorem zeroPolynomialMap_X :
    zeroPolynomialMap F Polynomial.X = LaurentPolynomial.T 1 := by
  simp [zeroPolynomialMap]

@[simp] theorem infinityPolynomialMap_C (r : F) :
    infinityPolynomialMap F (Polynomial.C r) = LaurentPolynomial.C r := by
  simp [infinityPolynomialMap]

@[simp] theorem infinityPolynomialMap_X :
    infinityPolynomialMap F Polynomial.X = LaurentPolynomial.T (-1) := by
  simp [infinityPolynomialMap]

theorem infinityPolynomialMap_eq_invert_comp :
    infinityPolynomialMap F =
      (LaurentPolynomial.invert (R := F)).toRingHom.comp (zeroPolynomialMap F) := by
  apply Polynomial.ringHom_ext
  · intro r
    simp
  · simp

def laurentInversion :
    Spec (CommRingCat.of (LaurentPolynomial F)) ⟶
      Spec (CommRingCat.of (LaurentPolynomial F)) :=
  Spec.map (CommRingCat.ofHom (LaurentPolynomial.invert (R := F)).toRingHom)

instance laurentInversion_isIso : IsIso (laurentInversion F) := by
  have : IsIso (CommRingCat.ofHom (LaurentPolynomial.invert (R := F)).toRingHom) :=
    (LaurentPolynomial.invert (R := F)).toRingEquiv.toCommRingCatIso.isIso_hom
  unfold laurentInversion
  infer_instance

def zeroChartOverlap :
    Spec (CommRingCat.of (LaurentPolynomial F)) ⟶ Spec (CommRingCat.of (Polynomial F)) :=
  Spec.map (CommRingCat.ofHom (zeroPolynomialMap F))

def infinityChartOverlap :
    Spec (CommRingCat.of (LaurentPolynomial F)) ⟶ Spec (CommRingCat.of (Polynomial F)) :=
  Spec.map (CommRingCat.ofHom (infinityPolynomialMap F))

theorem infinityChartOverlap_eq :
    infinityChartOverlap F = laurentInversion F ≫ zeroChartOverlap F := by
  unfold infinityChartOverlap laurentInversion zeroChartOverlap
  rw [infinityPolynomialMap_eq_invert_comp, CommRingCat.ofHom_comp, Spec.map_comp]

instance zeroChartOverlap_isOpenImmersion : IsOpenImmersion (zeroChartOverlap F) :=
  IsOpenImmersion.of_isLocalization (S := LaurentPolynomial F) (Polynomial.X : Polynomial F)

instance infinityChartOverlap_isOpenImmersion : IsOpenImmersion (infinityChartOverlap F) := by
  rw [infinityChartOverlap_eq]
  infer_instance

end PiExponent.ProjectiveLine

end

end OAI
end Source0358

-- Source: OAI/NumberTheory/PiExponent/Geometry/ProjectiveLineProper.lean
section Source0359
/-
Modification notice for the LogTwo project.
Derived from openai/math (Apache-2.0), revision adc7f1241b42e322a6451854ab7e4b4c146bf78a.
Original source: lean/OAI/NumberTheory/PiExponent/Geometry/ProjectiveLineProper.lean
Changes: Convert module/import declarations to the Lean 4.34 public module format.
See ../THIRD_PARTY_NOTICES.txt for provenance and the recorded changes.
-/

namespace OAI

noncomputable section
namespace PiExponent.ProjectiveLine

open CategoryTheory AlgebraicGeometry
attribute [local instance] MvPolynomial.gradedAlgebra
universe u

abbrev projectiveLine (F : Type u) [CommRing F] : Scheme.{u} :=
  Proj (MvPolynomial.homogeneousSubmodule Bool F)

def constantsInDegreeZero (F : Type u) [CommRing F] :
    F →+* (MvPolynomial.homogeneousSubmodule Bool F 0) where
  toFun r := ⟨MvPolynomial.C r, MvPolynomial.isHomogeneous_C _ r⟩
  map_one' := Subtype.ext MvPolynomial.C_1
  map_mul' a b := Subtype.ext (MvPolynomial.C_mul (a := a) (a' := b))
  map_zero' := Subtype.ext MvPolynomial.C_0
  map_add' a b := Subtype.ext (MvPolynomial.C_add (a := a) (a' := b))

theorem constantsInDegreeZero_bijective (F : Type u) [CommRing F] :
    Function.Bijective (constantsInDegreeZero F) := by
  constructor
  · intro a b h
    exact MvPolynomial.C_injective _ _ (congrArg Subtype.val h)
  · intro p
    have h : p.val.totalDegree = 0 :=
      (MvPolynomial.totalDegree_zero_iff_isHomogeneous _).mpr p.property
    refine ⟨p.val.coeff 0, ?_⟩
    apply Subtype.ext
    exact (MvPolynomial.totalDegree_eq_zero_iff_eq_C.mp h).symm

def degreeZeroEquiv (F : Type u) [CommRing F] :
    F ≃+* (MvPolynomial.homogeneousSubmodule Bool F 0) :=
  RingEquiv.ofBijective (constantsInDegreeZero F) (constantsInDegreeZero_bijective F)

instance constantsInDegreeZero_isIso (F : Type u) [CommRing F] :
    IsIso (CommRingCat.ofHom (constantsInDegreeZero F)) :=
  (degreeZeroEquiv F).toCommRingCatIso.isIso_hom

def structureMap (F : Type u) [CommRing F] :
    projectiveLine F ⟶ Spec (CommRingCat.of F) :=
  Proj.toSpecZero (MvPolynomial.homogeneousSubmodule Bool F) ≫
    Spec.map (CommRingCat.ofHom (constantsInDegreeZero F))

instance structureMap_isProper (F : Type u) [CommRing F] :
    IsProper (structureMap F) := by
  let A := MvPolynomial Bool F
  let 𝒜 := MvPolynomial.homogeneousSubmodule Bool F
  let : Algebra F (𝒜 0) := SetLike.GradeZero.instAlgebra 𝒜
  let : IsScalarTower F (𝒜 0) A := ⟨fun a b c => by
    change (a • (b : A)) * c = a • ((b : A) * c)
    exact smul_mul_assoc a (b : A) c⟩
  let : Algebra.FiniteType (𝒜 0) A :=
    Algebra.FiniteType.of_restrictScalars_finiteType F (𝒜 0) A
  have hp : IsProper (Proj.toSpecZero 𝒜) := inferInstance
  have : IsIso (Spec.map (CommRingCat.ofHom (constantsInDegreeZero F))) := inferInstance
  unfold structureMap
  exact IsProper.stableUnderComposition.comp_mem _ _ hp inferInstance

end PiExponent.ProjectiveLine

end

end OAI
end Source0359

-- Source: OAI/NumberTheory/PiExponent/Geometry/ProjectiveLineCharts.lean
section Source0360
/-
Modification notice for the LogTwo project.
Derived from openai/math (Apache-2.0), revision adc7f1241b42e322a6451854ab7e4b4c146bf78a.
Original source: lean/OAI/NumberTheory/PiExponent/Geometry/ProjectiveLineCharts.lean
Changes: Convert module/import declarations to the Lean 4.34 public module format.
See ../THIRD_PARTY_NOTICES.txt for provenance and the recorded changes.
-/

namespace OAI

noncomputable section
namespace PiExponent.ProjectiveLine

open CategoryTheory AlgebraicGeometry HomogeneousLocalization
open PiExponentSeshadri.Projective
attribute [local instance] MvPolynomial.gradedAlgebra
universe u
variable (F : Type u) [CommRing F]

instance boolChartVariablesUnique (i : Bool) : Unique (ChartVariables i) where
  default := ⟨!i, by cases i <;> decide⟩
  uniq j := by
    apply Subtype.ext
    rcases j with ⟨j, hj⟩
    cases i <;> cases j <;> simp_all

def lineEvaluation (i : Bool) : MvPolynomial Bool F →+* Polynomial F :=
  MvPolynomial.eval₂Hom Polynomial.C (fun j => if j = i then 1 else Polynomial.X)

@[simp] theorem lineEvaluation_X (i j : Bool) :
    lineEvaluation F i (MvPolynomial.X j) = if j = i then 1 else Polynomial.X := by
  simp [lineEvaluation]

@[simp] theorem lineEvaluation_C (i : Bool) (r : F) :
    lineEvaluation F i (MvPolynomial.C r) = Polynomial.C r := by
  simp [lineEvaluation]

def chartRingEquiv (i : Bool) : PolyChart (R := F) i ≃+* Polynomial F :=
  (polynomialChartEquiv i).trans
    (MvPolynomial.uniqueAlgEquiv F (ChartVariables i)).toRingEquiv

lemma unique_dehomogenize (i : Bool) :
    (MvPolynomial.uniqueAlgEquiv F (ChartVariables i)).toRingHom.comp
      (dehomogenize (R := F) i) = lineEvaluation F i := by
  apply MvPolynomial.ringHom_ext
  · intro r
    simp [dehomogenize, MvPolynomial.uniqueAlgEquiv_apply]
  · intro j
    by_cases h : j = i
    · subst j
      simp
    · simp [dehomogenize, h, MvPolynomial.uniqueAlgEquiv_apply]

lemma chartRingEquiv_eq_evalAway (i : Bool) :
    (chartRingEquiv F i).toRingHom =
      evalAway (𝒜 := PolyGrade F Bool) (lineEvaluation F i) (MvPolynomial.X i)
        (by simp) := by
  apply RingHom.ext
  intro x
  obtain ⟨n, p, hp, rfl⟩ := Away.mk_surjective _ (poly_X_mem (R := F) i) x
  change (MvPolynomial.uniqueAlgEquiv F (ChartVariables i))
    (chartToPoly i (Away.mk _ (poly_X_mem (R := F) i) n p hp)) = _
  rw [chartToPoly_mk]
  have h := RingHom.congr_fun (unique_dehomogenize F i) p
  change (MvPolynomial.uniqueAlgEquiv F (ChartVariables i)) (dehomogenize i p) = _ at h
  rw [h]
  symm
  simpa using evalAway_mk_clear (lineEvaluation F i) (poly_X_mem (R := F) i)
    (by simp) n p hp

def chartMap (i : Bool) : Spec (CommRingCat.of (Polynomial F)) ⟶ projectiveLine F :=
  Spec.map (CommRingCat.ofHom (chartRingEquiv F i).toRingHom) ≫
    Proj.awayι (PolyGrade F Bool) (MvPolynomial.X i) (poly_X_mem i) (by decide)

instance chartRingEquiv_isIso (i : Bool) :
    IsIso (CommRingCat.ofHom (chartRingEquiv F i).toRingHom) :=
  (chartRingEquiv F i).toCommRingCatIso.isIso_hom

instance chartMap_isOpenImmersion (i : Bool) : IsOpenImmersion (chartMap F i) := by
  unfold chartMap
  infer_instance

lemma chartMap_eq_fromUnitCoordinate (i : Bool) :
    chartMap F i = fromUnitCoordinate (𝒜 := PolyGrade F Bool)
      (lineEvaluation F i) (by decide) (poly_X_mem i) (by simp) := by
  unfold chartMap fromUnitCoordinate
  rw [chartRingEquiv_eq_evalAway]

@[simp] lemma chartMap_opensRange (i : Bool) :
    (chartMap F i).opensRange = Proj.basicOpen (PolyGrade F Bool) (MvPolynomial.X i) := by
  unfold chartMap
  rw [Scheme.Hom.opensRange_comp_of_isIso, Proj.opensRange_awayι]

lemma chartMap_cover : (⨆ i : Bool, (chartMap F i).opensRange) = ⊤ := by
  simp only [chartMap_opensRange]
  exact standardChart_cover

lemma chartMap_preimage (i j : Bool) :
    chartMap F i ⁻¹ᵁ Proj.basicOpen (PolyGrade F Bool) (MvPolynomial.X j) =
      PrimeSpectrum.basicOpen (if j = i then (1 : Polynomial F) else Polynomial.X) := by
  rw [chartMap_eq_fromUnitCoordinate, fromUnitCoordinate_preimage _ (poly_X_mem i)
    (by simp) (by simp) (by decide) (poly_X_mem j), lineEvaluation_X]

lemma chartMap_preimage_other (i : Bool) :
    chartMap F i ⁻¹ᵁ (chartMap F (!i)).opensRange =
      PrimeSpectrum.basicOpen (Polynomial.X : Polynomial F) := by
  rw [chartMap_opensRange, chartMap_preimage]
  cases i <;> simp <;> rfl

@[reassoc] lemma chartMap_structureMap (i : Bool) :
    chartMap F i ≫ structureMap F = Spec.map (CommRingCat.ofHom Polynomial.C) := by
  unfold chartMap structureMap
  rw [Category.assoc, Proj.awayι_toSpecZero_assoc]
  rw [← Spec.map_comp, ← Spec.map_comp]
  congr 1
  apply CommRingCat.hom_ext
  apply RingHom.ext
  intro r
  change (chartRingEquiv F i) (chartConstants i r) = Polynomial.C r
  change (MvPolynomial.uniqueAlgEquiv F (ChartVariables i))
    (chartToPoly i (chartConstants i r)) = _
  simp [MvPolynomial.uniqueAlgEquiv_apply]

end PiExponent.ProjectiveLine

end

end OAI
end Source0360

-- Source: OAI/NumberTheory/PiExponent/Geometry/ProjectiveLineReciprocal.lean
section Source0361
-- Modified in this edition: unused plain lemmas removed; see reduction.json.
/-
Modification notice for the LogTwo project.
Derived from openai/math (Apache-2.0), revision adc7f1241b42e322a6451854ab7e4b4c146bf78a.
Original source: lean/OAI/NumberTheory/PiExponent/Geometry/ProjectiveLineReciprocal.lean
Changes: Convert module/import declarations to the Lean 4.34 public module format.
See ../THIRD_PARTY_NOTICES.txt for provenance and the recorded changes.
-/

namespace OAI

noncomputable section
namespace PiExponent.ProjectiveLine

open CategoryTheory AlgebraicGeometry HomogeneousLocalization
open PiExponentSeshadri.Projective
attribute [local instance] MvPolynomial.gradedAlgebra
universe u
variable (F : Type u) [CommRing F]

private def inverseCoordinateUnit : (LaurentPolynomial F)ˣ where
  val := LaurentPolynomial.T (-1)
  inv := LaurentPolynomial.T 1
  val_inv := by rw [← LaurentPolynomial.T_add]; norm_num
  inv_val := by rw [← LaurentPolynomial.T_add]; norm_num

private lemma zeroEvaluation_eq :
    (zeroPolynomialMap F).comp (lineEvaluation F false) =
      MvPolynomial.eval₂Hom LaurentPolynomial.C
        (fun j : Bool => if j = false then 1 else LaurentPolynomial.T 1) := by
  apply MvPolynomial.ringHom_ext
  · intro r
    simp [zeroPolynomialMap]
  · intro j
    cases j <;> simp [zeroPolynomialMap]

private lemma infinityEvaluation_eq :
    (infinityPolynomialMap F).comp (lineEvaluation F true) =
      MvPolynomial.eval₂Hom LaurentPolynomial.C
        (fun j : Bool => LaurentPolynomial.T (-1) *
          (if j = false then 1 else LaurentPolynomial.T 1)) := by
  apply MvPolynomial.ringHom_ext
  · intro r
    simp only [RingHom.comp_apply, lineEvaluation_C, infinityPolynomialMap_C, MvPolynomial.eval₂Hom_C]
  · intro j
    simp only [RingHom.comp_apply, lineEvaluation_X, MvPolynomial.eval₂Hom_X']
    cases j with
    | false =>
      change infinityPolynomialMap F Polynomial.X = LaurentPolynomial.T (-1) * 1
      rw [infinityPolynomialMap_X, mul_one]
    | true =>
      change infinityPolynomialMap F 1 = LaurentPolynomial.T (-1) * LaurentPolynomial.T 1
      rw [map_one, ← LaurentPolynomial.T_add]
      norm_num

@[reassoc] theorem reciprocalChart_compatibility :
    zeroChartOverlap F ≫ chartMap F false =
      infinityChartOverlap F ≫ chartMap F true := by
  unfold zeroChartOverlap infinityChartOverlap
  rw [chartMap_eq_fromUnitCoordinate, chartMap_eq_fromUnitCoordinate,
    fromUnitCoordinate_natural, fromUnitCoordinate_natural]
  let f := (zeroPolynomialMap F).comp (lineEvaluation F false)
  let g := (infinityPolynomialMap F).comp (lineEvaluation F true)
  have hf : IsUnit (f (MvPolynomial.X false)) := by simp [f, zeroPolynomialMap]
  have hg : IsUnit (g (MvPolynomial.X false)) := by
    simpa [g, infinityPolynomialMap] using LaurentPolynomial.isUnit_T (R := F) (-1)
  have hg' : IsUnit (g (MvPolynomial.X true)) := by simp [g, infinityPolynomialMap]
  have H : ∀ n p, p ∈ PolyGrade F Bool n →
      g p = (inverseCoordinateUnit F : LaurentPolynomial F) ^ n * f p := by
    intro n p hp
    change ((infinityPolynomialMap F).comp (lineEvaluation F true)) p = _
    rw [infinityEvaluation_eq]
    change MvPolynomial.eval₂ _ _ p = _
    rw [homogeneous_eval₂_scale hp]
    congr 1
    exact (RingHom.congr_fun (zeroEvaluation_eq F) p).symm
  exact (fromUnitCoordinate_scale (𝒜 := PolyGrade F Bool) f (by decide)
    (poly_X_mem false) hf g hg (inverseCoordinateUnit F) H).trans
      (fromUnitCoordinate_eq (𝒜 := PolyGrade F Bool) g (by decide) (by decide)
        (poly_X_mem false) (poly_X_mem true) hg hg')

def affineChartCover : (projectiveLine F).OpenCover where
  I₀ := Bool
  X _ := Spec (CommRingCat.of (Polynomial F))
  f := chartMap F
  mem₀ := by
    rw [Scheme.presieve₀_mem_precoverage_iff]
    refine ⟨?_, fun i => inferInstance⟩
    intro x
    have hx : x ∈ (⨆ i : Bool, (chartMap F i).opensRange) := by
      rw [chartMap_cover]
      trivial
    rcases TopologicalSpace.Opens.mem_iSup.mp hx with ⟨i, hi⟩
    exact ⟨i, hi⟩

end PiExponent.ProjectiveLine

end

end OAI
end Source0361

-- Source: OAI/NumberTheory/PiExponent/Geometry/CurveNormalizationProper.lean
section Source0362
/-
Modification notice for the LogTwo project.
Derived from openai/math (Apache-2.0), revision adc7f1241b42e322a6451854ab7e4b4c146bf78a.
Original source: lean/OAI/NumberTheory/PiExponent/Geometry/CurveNormalizationProper.lean
Changes: Convert module/import declarations to the Lean 4.34 public module format.
See ../THIRD_PARTY_NOTICES.txt for provenance and the recorded changes.
-/

namespace OAI

noncomputable section
namespace PiExponent.CurveNormalizationModel
open scoped Polynomial
open AlgebraicGeometry CategoryTheory
open PiExponent.CurveZeroPole
universe u
variable {F E : Type u} [Field F] [Field E] [Algebra F E]
variable (f : E) (hf : Transcendental F f)

def parameterOverlapProjection : Spec (.of (parameterLaurentChart f hf)) ⟶
    Spec (.of (LaurentPolynomial F)) :=
  letI := parameterLaurentAlgebra f hf
  Spec.map (CommRingCat.ofHom (algebraMap (LaurentPolynomial F) (parameterLaurentChart f hf)))

@[reassoc] theorem zeroOverlap_projection :
    zeroOverlap f hf ≫ parameterChartProjection f hf =
      parameterOverlapProjection f hf ≫ ProjectiveLine.zeroChartOverlap F := by
  let := parameterPolynomialAlgebra f hf
  let := parameterLaurentAlgebra f hf
  let := parameterLaurent_scalarTower f hf
  unfold zeroOverlap parameterChartProjection parameterOverlapProjection
    ProjectiveLine.zeroChartOverlap
  rw [← Spec.map_comp, ← Spec.map_comp]
  congr 1
  apply CommRingCat.hom_ext
  apply RingHom.ext
  intro p
  apply Subtype.ext
  exact IsScalarTower.algebraMap_apply F[X] (LaurentPolynomial F) E p

@[reassoc] theorem infinityOverlap_projection :
    infinityOverlap f hf ≫ parameterChartProjection f⁻¹ (transcendental_inverse f hf) =
      parameterOverlapProjection f hf ≫ ProjectiveLine.infinityChartOverlap F := by
  let := parameterPolynomialAlgebra f⁻¹ (transcendental_inverse f hf)
  let := parameterLaurentAlgebra f hf
  unfold infinityOverlap parameterChartProjection parameterOverlapProjection
    ProjectiveLine.infinityChartOverlap
  rw [← Spec.map_comp, ← Spec.map_comp]
  congr 1
  apply CommRingCat.hom_ext
  apply Polynomial.ringHom_ext
  · intro c
    apply Subtype.ext
    change algebraMap F[X] E (Polynomial.C c) =
      parameterLaurentMap f hf (ProjectiveLine.infinityPolynomialMap F (Polynomial.C c))
    rw [parameterPolynomialAlgebra_map]
    simp [parameterLaurentMap, LaurentPolynomial.eval₂_C]
  · apply Subtype.ext
    change algebraMap F[X] E Polynomial.X =
      parameterLaurentMap f hf (ProjectiveLine.infinityPolynomialMap F Polynomial.X)
    rw [parameterPolynomialAlgebra_map]
    simp

def parameterCurveProjection : parameterCurve f hf ⟶ ProjectiveLine.projectiveLine F :=
  Limits.pushout.desc
    (parameterChartProjection f hf ≫ ProjectiveLine.chartMap F false)
    (parameterChartProjection f⁻¹ (transcendental_inverse f hf) ≫
      ProjectiveLine.chartMap F true) (by
      rw [zeroOverlap_projection_assoc, infinityOverlap_projection_assoc]
      rw [ProjectiveLine.reciprocalChart_compatibility])

@[reassoc] theorem zeroChart_projection :
    zeroChartInclusion f hf ≫ parameterCurveProjection f hf =
      parameterChartProjection f hf ≫ ProjectiveLine.chartMap F false :=
  Limits.pushout.inl_desc _ _ _

@[reassoc] theorem infinityChart_projection :
    infinityChartInclusion f hf ≫ parameterCurveProjection f hf =
      parameterChartProjection f⁻¹ (transcendental_inverse f hf) ≫
        ProjectiveLine.chartMap F true :=
  Limits.pushout.inr_desc _ _ _

theorem parameterCurveProjection_preimage_zero :
    parameterCurveProjection f hf ⁻¹ᵁ (ProjectiveLine.chartMap F false).opensRange =
      (zeroChartInclusion f hf).opensRange := by
  ext x
  rcases parameterCurve_twoChartCover f hf x with ⟨q, rfl⟩ | ⟨q, rfl⟩
  · change parameterCurveProjection f hf (zeroChartInclusion f hf q) ∈
      (ProjectiveLine.chartMap F false).opensRange ↔
        zeroChartInclusion f hf q ∈ Set.range (zeroChartInclusion f hf)
    rw [← Scheme.Hom.comp_apply, zeroChart_projection, Scheme.Hom.comp_apply]
    exact iff_of_true ⟨_, rfl⟩ ⟨q, rfl⟩
  · change parameterCurveProjection f hf (infinityChartInclusion f hf q) ∈
      (ProjectiveLine.chartMap F false).opensRange ↔
        infinityChartInclusion f hf q ∈ Set.range (zeroChartInclusion f hf)
    rw [← Scheme.Hom.comp_apply, infinityChart_projection, Scheme.Hom.comp_apply,
      infinityChart_mem_zero_iff]
    change parameterChartProjection f⁻¹ (transcendental_inverse f hf) q ∈
      (ProjectiveLine.chartMap F true ⁻¹ᵁ (ProjectiveLine.chartMap F (!true)).opensRange) ↔ _
    rw [ProjectiveLine.chartMap_preimage_other]
    let := parameterPolynomialAlgebra f⁻¹ (transcendental_inverse f hf)
    change q ∈ PrimeSpectrum.basicOpen
      (algebraMap F[X] (parameterChart f⁻¹ (transcendental_inverse f hf)) Polynomial.X) ↔ _
    rw [infinityOverlap_range]
    rfl

theorem parameterCurveProjection_preimage_infinity :
    parameterCurveProjection f hf ⁻¹ᵁ (ProjectiveLine.chartMap F true).opensRange =
      (infinityChartInclusion f hf).opensRange := by
  ext x
  rcases parameterCurve_twoChartCover f hf x with ⟨q, rfl⟩ | ⟨q, rfl⟩
  · change parameterCurveProjection f hf (zeroChartInclusion f hf q) ∈
      (ProjectiveLine.chartMap F true).opensRange ↔
        zeroChartInclusion f hf q ∈ Set.range (infinityChartInclusion f hf)
    rw [← Scheme.Hom.comp_apply, zeroChart_projection, Scheme.Hom.comp_apply,
      zeroChart_mem_infinity_iff]
    change parameterChartProjection f hf q ∈
      (ProjectiveLine.chartMap F false ⁻¹ᵁ (ProjectiveLine.chartMap F (!false)).opensRange) ↔ _
    rw [ProjectiveLine.chartMap_preimage_other]
    let := parameterPolynomialAlgebra f hf
    change q ∈ PrimeSpectrum.basicOpen
      (algebraMap F[X] (parameterChart f hf) Polynomial.X) ↔ _
    rw [zeroOverlap_range]
    rfl
  · change parameterCurveProjection f hf (infinityChartInclusion f hf q) ∈
      (ProjectiveLine.chartMap F true).opensRange ↔
        infinityChartInclusion f hf q ∈ Set.range (infinityChartInclusion f hf)
    rw [← Scheme.Hom.comp_apply, infinityChart_projection, Scheme.Hom.comp_apply]
    exact iff_of_true ⟨_, rfl⟩ ⟨q, rfl⟩

theorem zeroChartProjection_isPullback :
    IsPullback (zeroChartInclusion f hf) (parameterChartProjection f hf)
      (parameterCurveProjection f hf) (ProjectiveLine.chartMap F false) :=
  (IsOpenImmersion.isPullback _ _ _ _ (zeroChart_projection f hf)
    (parameterCurveProjection_preimage_zero f hf)).flip

theorem infinityChartProjection_isPullback :
    IsPullback (infinityChartInclusion f hf)
      (parameterChartProjection f⁻¹ (transcendental_inverse f hf))
      (parameterCurveProjection f hf) (ProjectiveLine.chartMap F true) :=
  (IsOpenImmersion.isPullback _ _ _ _ (infinityChart_projection f hf)
    (parameterCurveProjection_preimage_infinity f hf)).flip

instance parameterCurveProjection_isFinite [CharZero F]
    [FiniteDimensional (IntermediateField.adjoin F {f}) E] :
    IsFinite (parameterCurveProjection f hf) := by
  let : FiniteDimensional (IntermediateField.adjoin F {f⁻¹}) E :=
    (adjoin_inverse_eq (F := F) f).symm ▸ inferInstance
  let hAffine := AlgebraicGeometry.IsFinite.instHasAffinePropertyAndIsAffineFiniteCarrierObjOppositeOpensCarrierCarrierCommRingCatPresheafOpOpensTopHomAppTop.{u}
  let : IsZariskiLocalAtTarget (@AlgebraicGeometry.IsFinite.{u}) :=
    @HasAffineProperty.instIsZariskiLocalAtTarget _ _ hAffine
  apply IsZariskiLocalAtTarget.of_openCover (P := @AlgebraicGeometry.IsFinite.{u})
    (ProjectiveLine.affineChartCover F)
  intro i
  cases i
  · change IsFinite (Limits.pullback.snd (parameterCurveProjection f hf)
      (ProjectiveLine.chartMap F false))
    rw [← (zeroChartProjection_isPullback f hf).isoPullback_inv_snd]
    infer_instance
  · change IsFinite (Limits.pullback.snd (parameterCurveProjection f hf)
      (ProjectiveLine.chartMap F true))
    rw [← (infinityChartProjection_isPullback f hf).isoPullback_inv_snd]
    infer_instance

def parameterCurveStructureMap : parameterCurve f hf ⟶ Spec (.of F) :=
  parameterCurveProjection f hf ≫ ProjectiveLine.structureMap F

instance parameterCurveStructureMap_isProper [CharZero F]
    [FiniteDimensional (IntermediateField.adjoin F {f}) E] :
    IsProper (parameterCurveStructureMap f hf) := by
  unfold parameterCurveStructureMap
  infer_instance

end PiExponent.CurveNormalizationModel

end

end OAI
end Source0362

-- Source: OAI/NumberTheory/PiExponent/Geometry/CurveModelGenericPoint.lean
section Source0363
/-
Modification notice for the LogTwo project.
Derived from openai/math (Apache-2.0), revision adc7f1241b42e322a6451854ab7e4b4c146bf78a.
Original source: lean/OAI/NumberTheory/PiExponent/Geometry/CurveModelGenericPoint.lean
Changes: Convert module/import declarations to the Lean 4.34 public module format.
See ../THIRD_PARTY_NOTICES.txt for provenance and the recorded changes.
-/

namespace OAI

noncomputable section
namespace PiExponent.CurveNormalizationModel
open CategoryTheory AlgebraicGeometry
open scoped Polynomial
open PiExponent.CurveZeroPole
universe u

private theorem eqToHom_fromSpecStalk (X : Scheme.{u}) {x y : X} (h : x = y) :
    Spec.map (eqToHom (congrArg (fun z => X.presheaf.stalk z) h)) ≫
      X.fromSpecStalk x = X.fromSpecStalk y := by
  subst y
  simp

theorem functionFieldRestriction_fromSpecStalk {U X : Scheme.{u}}
    [IsIntegral U] [IsIntegral X] (i : U ⟶ X) [IsOpenImmersion i] :
    Spec.map (functionFieldRestriction i) ≫ X.fromSpecStalk (genericPoint X) =
      U.fromSpecStalk (genericPoint U) ≫ i := by
  unfold functionFieldRestriction
  rw [Spec.map_comp, Category.assoc,
    eqToHom_fromSpecStalk X (genericPoint_eq_of_isOpenImmersion i).symm]
  exact Scheme.SpecMap_stalkMap_fromSpecStalk i

theorem affineFunctionFieldEquiv_fromSpecStalk
    (A E : Type u) [CommRing A] [IsDomain A] [Field E]
    [Algebra A E] [IsFractionRing A E] :
    Spec.map (CommRingCat.ofHom (affineFunctionFieldEquiv A E).toRingHom) ≫
      (Spec (.of A)).fromSpecStalk (genericPoint (Spec (.of A))) =
      Spec.map (CommRingCat.ofHom (algebraMap A E)) := by
  erw [Spec.fromSpecStalk_eq', ← Spec.map_comp]
  congr 1
  apply CommRingCat.hom_ext
  apply RingHom.ext
  exact affineFunctionFieldEquiv_toStalk A E

private theorem affineRestriction_fromSpecStalk
    (A E : Type u) [CommRing A] [IsDomain A] [Field E]
    [Algebra A E] [IsFractionRing A E] {X : Scheme.{u}} [IsIntegral X]
    (i : Spec (.of A) ⟶ X) [IsOpenImmersion i] :
    Spec.map (functionFieldRestriction i ≫
      CommRingCat.ofHom (affineFunctionFieldEquiv A E).toRingHom) ≫
      X.fromSpecStalk (genericPoint X) =
      Spec.map (CommRingCat.ofHom (algebraMap A E)) ≫ i := by
  let e := Spec.map (CommRingCat.ofHom (affineFunctionFieldEquiv A E).toRingHom)
  let r := Spec.map (functionFieldRestriction i)
  let q := X.fromSpecStalk (genericPoint X)
  have hmap := congrArg (fun k => k ≫ q)
    (Spec.map_comp (functionFieldRestriction i)
      (CommRingCat.ofHom (affineFunctionFieldEquiv A E).toRingHom))
  have hrestrict := congrArg (fun k => e ≫ k) (functionFieldRestriction_fromSpecStalk i)
  have haffine := congrArg (fun k => k ≫ i) (affineFunctionFieldEquiv_fromSpecStalk A E)
  have hassoc := Category.assoc e
    ((Spec (.of A)).fromSpecStalk (genericPoint (Spec (.of A)))) i
  exact hmap.trans ((Category.assoc e r q).trans
    (hrestrict.trans (hassoc.symm.trans haffine)))

variable {F E : Type u} [Field F] [Field E] [Algebra F E]
variable (f : E) (hf : Transcendental F f)

def parameterChartConstantMap : F →+* parameterChart f hf :=
  letI := parameterPolynomialAlgebra f hf
  (algebraMap F[X] (parameterChart f hf)).comp Polynomial.C

theorem parameterChartConstantMap_toField :
    (algebraMap (parameterChart f hf) E).comp (parameterChartConstantMap f hf) =
      algebraMap F E := by
  let := parameterPolynomialAlgebra f hf
  apply RingHom.ext
  intro c
  change algebraMap F[X] E (Polynomial.C c) = algebraMap F E c
  rw [parameterPolynomialAlgebra_map]
  simp

@[reassoc] theorem zeroChart_structureMap :
    zeroChartInclusion f hf ≫ parameterCurveStructureMap f hf =
      Spec.map (CommRingCat.ofHom (parameterChartConstantMap f hf)) := by
  unfold parameterCurveStructureMap
  rw [zeroChart_projection_assoc, ProjectiveLine.chartMap_structureMap,
    parameterChartProjection, ← Spec.map_comp]
  rfl

variable [FiniteDimensional (IntermediateField.adjoin F {f}) E]

def parameterCurveGenericPoint : Spec (.of E) ⟶ parameterCurve f hf :=
  Spec.map (CommRingCat.ofHom (parameterCurveFunctionFieldEquiv f hf).toRingHom) ≫
    (parameterCurve f hf).fromSpecStalk (genericPoint (parameterCurve f hf))

theorem parameterCurveGenericPoint_eq_zeroChart :
    parameterCurveGenericPoint f hf =
      Spec.map (CommRingCat.ofHom (algebraMap (parameterChart f hf) E)) ≫
        zeroChartInclusion f hf := by
  let := parameterAlgebra f hf
  let := parameterPolynomialAlgebra f hf
  let := parameter_scalarTower f hf
  let := parameter_finite f hf
  change Spec.map (functionFieldRestriction (zeroChartInclusion f hf) ≫
      CommRingCat.ofHom (affineFunctionFieldEquiv (parameterChart f hf) E).toRingHom) ≫
      (parameterCurve f hf).fromSpecStalk (genericPoint (parameterCurve f hf)) = _
  exact affineRestriction_fromSpecStalk (parameterChart f hf) E (zeroChartInclusion f hf)

@[reassoc] theorem parameterCurveGenericPoint_over_base :
    parameterCurveGenericPoint f hf ≫ parameterCurveStructureMap f hf =
      Spec.map (CommRingCat.ofHom (algebraMap F E)) := by
  rw [parameterCurveGenericPoint_eq_zeroChart, Category.assoc,
    zeroChart_structureMap, ← Spec.map_comp]
  congr 1
  apply CommRingCat.hom_ext
  exact parameterChartConstantMap_toField f hf

end PiExponent.CurveNormalizationModel

end

end OAI
end Source0363

-- Source: OAI/NumberTheory/PiExponent/Geometry/CurveStalkGluing.lean
section Source0364
/-
Modification notice for the LogTwo project.
Derived from openai/math (Apache-2.0), revision adc7f1241b42e322a6451854ab7e4b4c146bf78a.
Original source: lean/OAI/NumberTheory/PiExponent/Geometry/CurveStalkGluing.lean
Changes: Convert module/import declarations to the Lean 4.34 public module format.
See ../THIRD_PARTY_NOTICES.txt for provenance and the recorded changes.
-/

namespace OAI

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace

namespace PiExponent.CurveStalkGluing

universe u

variable {X Y S : Scheme.{u}} [IsIntegral X]

@[reassoc]
theorem specMap_stalkFunctionField_fromSpecStalk (x : X) :
    Spec.map (CommRingCat.ofHom
      (algebraMap (X.presheaf.stalk x) X.functionField)) ≫ X.fromSpecStalk x =
      X.fromSpecStalk (genericPoint X) := by
  change Spec.map (X.presheaf.stalkSpecializes
    ((genericPoint_spec X).specializes trivial)) ≫ X.fromSpecStalk x = _
  exact Scheme.SpecMap_stalkSpecializes_fromSpecStalk _

theorem isDominant_fromSpecFunctionField :
    IsDominant (X.fromSpecStalk (genericPoint X)) := by
  constructor
  rw [denseRange_iff_closure_range]
  apply Set.eq_univ_of_univ_subset
  rw [← genericPoint_closure X]
  apply closure_mono
  rw [Set.singleton_subset_iff]
  exact ⟨IsLocalRing.closedPoint (X.presheaf.stalk (genericPoint X)), by simp⟩

theorem genericPoint_mem (U : X.Opens) (x : X) (hx : x ∈ U) :
    genericPoint X ∈ U :=
  (genericPoint_specializes x).mem_open U.isOpen hx

@[reassoc]
theorem specMap_stalkFunctionField_fromSpecStalkOfMem
    (U : X.Opens) (x : X) (hx : x ∈ U) :
    Spec.map (CommRingCat.ofHom
      (algebraMap (X.presheaf.stalk x) X.functionField)) ≫
        U.fromSpecStalkOfMem x hx =
      U.fromSpecStalkOfMem (genericPoint X) (genericPoint_mem U x hx) := by
  apply (cancel_mono U.ι).mp
  simp only [Category.assoc, Scheme.Opens.fromSpecStalkOfMem_ι,
    specMap_stalkFunctionField_fromSpecStalk]

theorem overlap_eq (sX : X ⟶ S) (sY : Y ⟶ S) [IsSeparated sY]
    (η : Spec X.functionField ⟶ Y) (U V : X.Opens)
    (hU : genericPoint X ∈ U) (hV : genericPoint X ∈ V)
    (f : U.toScheme ⟶ Y) (g : V.toScheme ⟶ Y)
    (hf : f ≫ sY = U.ι ≫ sX) (hg : g ≫ sY = V.ι ≫ sX)
    (hfη : U.fromSpecStalkOfMem (genericPoint X) hU ≫ f = η)
    (hgη : V.fromSpecStalkOfMem (genericPoint X) hV ≫ g = η) :
    pullback.fst U.ι V.ι ≫ f = pullback.snd U.ι V.ι ≫ g := by
  let a := U.fromSpecStalkOfMem (genericPoint X) hU
  let b := V.fromSpecStalkOfMem (genericPoint X) hV
  have hab : a ≫ U.ι = b ≫ V.ι := by simp [a, b]
  let k : Spec X.functionField ⟶ pullback U.ι V.ι := pullback.lift a b hab
  let q : pullback U.ι V.ι ⟶ X := pullback.fst U.ι V.ι ≫ U.ι
  have hkq : k ≫ q = X.fromSpecStalk (genericPoint X) := by
    dsimp only [k, q]
    rw [← Category.assoc, pullback.lift_fst]
    exact Scheme.Opens.fromSpecStalkOfMem_ι U _ hU
  have : IsReduced (pullback U.ι V.ι) := isReduced_of_isOpenImmersion q
  have : IsDominant (k ≫ q) := by
    rw [hkq]
    exact isDominant_fromSpecFunctionField
  have : IsDominant k := IsDominant.of_comp_of_isOpenImmersion k q
  have hover : (pullback.fst U.ι V.ι ≫ f) ≫ sY =
      (pullback.snd U.ι V.ι ≫ g) ≫ sY := by
    rw [Category.assoc, hf, Category.assoc, hg]
    exact pullback.condition_assoc (f := U.ι) (g := V.ι) sX
  have hgeneric : k ≫ (pullback.fst U.ι V.ι ≫ f) =
      k ≫ (pullback.snd U.ι V.ι ≫ g) := by
    dsimp only [k]
    rw [pullback.lift_fst_assoc, pullback.lift_snd_assoc]
    exact hfη.trans hgη.symm
  exact ext_of_isDominant_of_isSeparated sY hover k hgeneric

theorem exists_morphism_of_stalk_maps
    (sX : X ⟶ S) (sY : Y ⟶ S) [LocallyOfFiniteType sY] [IsSeparated sY]
    (η : Spec X.functionField ⟶ Y)
    (H : ∀ x : X, ∃ φ : Spec (X.presheaf.stalk x) ⟶ Y,
      φ ≫ sY = X.fromSpecStalk x ≫ sX ∧
      Spec.map (CommRingCat.ofHom
        (algebraMap (X.presheaf.stalk x) X.functionField)) ≫ φ = η) :
    ∃ g : X ⟶ Y, g ≫ sY = sX ∧ X.fromSpecStalk (genericPoint X) ≫ g = η := by
  classical
  choose φ hφover hφη using H
  have hspread (x : X) :=
    spread_out_of_isGermInjective' sX sY (φ x) (hφover x)
  choose U hx f hφ hf using hspread
  have hgen (x : X) : genericPoint X ∈ U x := genericPoint_mem (U x) x (hx x)
  have hfη (x : X) : (U x).fromSpecStalkOfMem (genericPoint X) (hgen x) ≫ f x = η := by
    rw [← specMap_stalkFunctionField_fromSpecStalkOfMem (U x) x (hx x),
      Category.assoc, ← hφ x]
    exact hφη x
  have hcover : IsOpenCover U := by
    change (⨆ x, U x) = ⊤
    apply top_unique
    intro x _
    exact Opens.mem_iSup.mpr ⟨x, hx x⟩
  let 𝒰 := X.openCoverOfIsOpenCover U hcover
  have hcompat (x y : X) :
      pullback.fst (U x).ι (U y).ι ≫ f x =
        pullback.snd (U x).ι (U y).ι ≫ f y :=
    overlap_eq sX sY η (U x) (U y) (hgen x) (hgen y)
      (f x) (f y) (hf x) (hf y) (hfη x) (hfη y)
  let g : X ⟶ Y := 𝒰.glueMorphisms f hcompat
  have hg (x : X) : (U x).ι ≫ g = f x := 𝒰.ι_glueMorphisms f hcompat x
  refine ⟨g, ?_, ?_⟩
  · apply 𝒰.hom_ext
    intro x
    change X at x
    change (U x).ι ≫ g ≫ sY = (U x).ι ≫ sX
    rw [← Category.assoc, hg, hf]
  · let x : X := genericPoint X
    rw [← Scheme.Opens.fromSpecStalkOfMem_ι (U x) (genericPoint X) (hgen x),
      Category.assoc, hg]
    exact hfη x

end PiExponent.CurveStalkGluing

end OAI
end Source0364

-- Source: OAI/NumberTheory/PiExponent/Geometry/CurveGlobalMonomial.lean
section Source0365
-- Modified in this edition: unused plain lemmas removed; see reduction.json.
/-
Modification notice for the LogTwo project.
Derived from openai/math (Apache-2.0), revision adc7f1241b42e322a6451854ab7e4b4c146bf78a.
Original source: lean/OAI/NumberTheory/PiExponent/Geometry/CurveGlobalMonomial.lean
Changes: Convert module/import declarations to the Lean 4.34 public module format.
See ../THIRD_PARTY_NOTICES.txt for provenance and the recorded changes.
-/

namespace OAI

noncomputable section
universe u
namespace PiExponent.CurveGlobalMonomial
open AlgebraicGeometry CategoryTheory
open CurveNormalizationModel CurveProperExtension CurveMonomialMap WeightedCompactification

theorem exists_extension
    {X Y S : Scheme.{u}} [IsIntegral X]
    (sX : X ⟶ S) (sY : Y ⟶ S) [IsProper sY]
    (hDVR : ∀ x : X, x ≠ genericPoint X → IsDiscreteValuationRing (X.presheaf.stalk x))
    (η : Spec X.functionField ⟶ Y)
    (hη : η ≫ sY = X.fromSpecStalk (genericPoint X) ≫ sX) :
    ∃ g : X ⟶ Y, g ≫ sY = sX ∧ X.fromSpecStalk (genericPoint X) ≫ g = η :=
  CurveStalkGluing.exists_morphism_of_stalk_maps sX sY η
    (exists_stalk_map sX sY hDVR η hη)

theorem exists_parameterCurve_extension
    {F E : Type u} [Field F] [CharZero F] [Field E] [Algebra F E]
    (f : E) (hf : Transcendental F f)
    [FiniteDimensional (IntermediateField.adjoin F {f}) E]
    {Y : Scheme.{u}} (sY : Y ⟶ Spec (CommRingCat.of F)) [IsProper sY]
    (ηE : Spec (CommRingCat.of E) ⟶ Y)
    (hηE : ηE ≫ sY = Spec.map (CommRingCat.ofHom (algebraMap F E))) :
    ∃ g : parameterCurve f hf ⟶ Y,
      g ≫ sY = parameterCurveStructureMap f hf ∧ parameterCurveGenericPoint f hf ≫ g = ηE := by
  let e := parameterCurveFunctionFieldEquiv f hf
  let eSpec : Spec (CommRingCat.of E) ≅ Spec (parameterCurve f hf).functionField :=
    Scheme.Spec.mapIso e.toCommRingCatIso.op
  let η := eSpec.inv ≫ ηE
  have hη : η ≫ sY = (parameterCurve f hf).fromSpecStalk
      (genericPoint (parameterCurve f hf)) ≫ parameterCurveStructureMap f hf := by
    apply (cancel_epi eSpec.hom).mp
    change eSpec.hom ≫ (eSpec.inv ≫ ηE) ≫ sY = _
    rw [← Category.assoc, eSpec.hom_inv_id_assoc, hηE]
    exact (parameterCurveGenericPoint_over_base f hf).symm
  obtain ⟨g, hbase, hgeneric⟩ := exists_extension (parameterCurveStructureMap f hf) sY
    (parameterCurve_stalkDVR f hf) η hη
  refine ⟨g, hbase, ?_⟩
  change (eSpec.hom ≫ (parameterCurve f hf).fromSpecStalk
    (genericPoint (parameterCurve f hf))) ≫ g = ηE
  rw [Category.assoc, hgeneric]
  exact eSpec.hom_inv_id_assoc ηE

end PiExponent.CurveGlobalMonomial

end

end OAI
end Source0365

-- Source: OAI/NumberTheory/PiExponent/Geometry/BirationalValuationStalk.lean
section Source0366
/-
Modification notice for the LogTwo project.
Derived from openai/math (Apache-2.0), revision adc7f1241b42e322a6451854ab7e4b4c146bf78a.
Original source: lean/OAI/NumberTheory/PiExponent/Geometry/BirationalValuationStalk.lean
Changes: Convert module/import declarations to the Lean 4.34 public module format.
See ../THIRD_PARTY_NOTICES.txt for provenance and the recorded changes.
-/

namespace OAI

noncomputable section
namespace PiExponent.BirationalValuationStalk
open CategoryTheory AlgebraicGeometry

private theorem comp_eq_of_comp_eq {C : Type*} [Category C] {W X Y Z : C}
    (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z) (k : X ⟶ Z) (hcomp : g ≫ h = k) :
    (f ≫ g) ≫ h = f ≫ k :=
  (Category.assoc f g h).trans (congrArg (fun t => f ≫ t) hcomp)

universe u
variable {X : Scheme.{u}} [IsIntegral X]
variable {A E : Type u} [CommRing A] [IsLocalRing A]
  [Field E] [Algebra A E] [IsFractionRing A E]
variable (g : Spec (.of A) ⟶ X) (e : X.functionField ≃+* E)
variable (hgeneric : Spec.map (CommRingCat.ofHom (algebraMap A E)) ≫ g =
  Spec.map (CommRingCat.ofHom e.toRingHom) ≫ X.fromSpecStalk (genericPoint X))

include hgeneric

omit [IsFractionRing A E] in
theorem stalkClosedPointTo_field_compatibility :
    (algebraMap A E).comp (Scheme.stalkClosedPointTo g).hom =
      e.toRingHom.comp
        (algebraMap (X.presheaf.stalk (g (IsLocalRing.closedPoint A))) X.functionField) := by
  have h : Scheme.stalkClosedPointTo g ≫ CommRingCat.ofHom (algebraMap A E) =
      X.presheaf.stalkSpecializes (genericPoint_specializes (g (IsLocalRing.closedPoint A))) ≫
        CommRingCat.ofHom e.toRingHom := by
    apply Spec.map_injective
    apply (cancel_mono (X.fromSpecStalk (g (IsLocalRing.closedPoint A)))).mp
    let q := X.fromSpecStalk (g (IsLocalRing.closedPoint A))
    have hleft := comp_eq_of_comp_eq
      (Spec.map (CommRingCat.ofHom (algebraMap A E)))
      (Spec.map (Scheme.stalkClosedPointTo g)) q g
      (Scheme.Spec_stalkClosedPointTo_fromSpecStalk g)
    have hright := comp_eq_of_comp_eq
      (Spec.map (CommRingCat.ofHom e.toRingHom))
      (Spec.map (X.presheaf.stalkSpecializes
        (genericPoint_specializes (g (IsLocalRing.closedPoint A))))) q
      (X.fromSpecStalk (genericPoint X))
      (X.SpecMap_stalkSpecializes_fromSpecStalk
        (genericPoint_specializes (g (IsLocalRing.closedPoint A))))
    have hmapLeft := congrArg (fun k => k ≫ q)
      (Spec.map_comp (Scheme.stalkClosedPointTo g) (CommRingCat.ofHom (algebraMap A E)))
    have hmapRight := congrArg (fun k => k ≫ q)
      (Spec.map_comp (X.presheaf.stalkSpecializes
        (genericPoint_specializes (g (IsLocalRing.closedPoint A))))
        (CommRingCat.ofHom e.toRingHom))
    exact hmapLeft.trans (hleft.trans (hgeneric.trans (hright.symm.trans hmapRight.symm)))
  exact CommRingCat.hom_ext_iff.mp h

theorem stalkClosedPointTo_bijective
    [ValuationRing (X.presheaf.stalk (g (IsLocalRing.closedPoint A)))] :
    Function.Bijective (Scheme.stalkClosedPointTo g).hom := by
  let α := (Scheme.stalkClosedPointTo g).hom
  let β := e.symm.toRingHom.comp (algebraMap A E)
  have hcomp : β.comp α =
      algebraMap (X.presheaf.stalk (g (IsLocalRing.closedPoint A))) X.functionField := by
    apply RingHom.ext
    intro a
    apply e.injective
    have h := RingHom.congr_fun (stalkClosedPointTo_field_compatibility g e hgeneric) a
    change e (e.symm ((algebraMap A E) (α a))) =
      e ((algebraMap (X.presheaf.stalk (g (IsLocalRing.closedPoint A))) X.functionField) a)
    rw [e.apply_symm_apply]
    exact h
  have hβ : Function.Injective β := e.symm.injective.comp (IsFractionRing.injective A E)
  have hbij := bijective_rangeRestrict_comp_of_valuationRing α β hcomp
  refine ⟨fun a b hab => hbij.1 (congrArg β.rangeRestrict hab), ?_⟩
  intro a
  obtain ⟨b, hb⟩ := hbij.2 (β.rangeRestrict a)
  refine ⟨b, hβ ?_⟩
  exact congrArg Subtype.val hb

theorem stalkMap_isIso
    [ValuationRing (X.presheaf.stalk (g (IsLocalRing.closedPoint A)))] :
    IsIso (g.stalkMap (IsLocalRing.closedPoint A)) := by
  have : IsIso (Scheme.stalkClosedPointTo g) :=
    (ConcreteCategory.isIso_iff_bijective _).mpr (stalkClosedPointTo_bijective g e hgeneric)
  change IsIso (g.stalkMap _ ≫ (stalkClosedPointIso (.of A)).hom) at this
  exact IsIso.of_isIso_comp_right _ (stalkClosedPointIso (.of A)).hom

end PiExponent.BirationalValuationStalk

end

end OAI
end Source0366

-- Source: OAI/NumberTheory/PiExponent/Geometry/CurveNormalizationDimension.lean
section Source0367
/-
Modification notice for the LogTwo project.
Derived from openai/math (Apache-2.0), revision adc7f1241b42e322a6451854ab7e4b4c146bf78a.
Original source: lean/OAI/NumberTheory/PiExponent/Geometry/CurveNormalizationDimension.lean
Changes: Convert module/import declarations to the Lean 4.34 public module format.
See ../THIRD_PARTY_NOTICES.txt for provenance and the recorded changes.
-/

namespace OAI

noncomputable section
namespace PiExponent.CurveNormalizationModel
open AlgebraicGeometry CategoryTheory TopologicalSpace
open PiExponent.CurveZeroPole
open scoped Polynomial

universe u
variable {F E : Type u} [Field F] [Field E] [Algebra F E]
variable (f : E) (hf : Transcendental F f)

def parameterCurveOpenCover : (parameterCurve f hf).OpenCover where
  I₀ := Bool
  X b := if b then Spec (.of (parameterChart f⁻¹ (transcendental_inverse f hf)))
    else Spec (.of (parameterChart f hf))
  f b := by
    cases b
    · exact zeroChartInclusion f hf
    · exact infinityChartInclusion f hf
  mem₀ := by
    rw [Scheme.presieve₀_mem_precoverage_iff]
    constructor
    · intro x
      rcases parameterCurve_twoChartCover f hf x with ⟨q, rfl⟩ | ⟨q, rfl⟩
      · exact ⟨false, q, rfl⟩
      · exact ⟨true, q, rfl⟩
    · intro b
      cases b <;> infer_instance

instance parameterChart_noetherian [CharZero F]
    [FiniteDimensional (IntermediateField.adjoin F {f}) E] :
    IsNoetherianRing (parameterChart f hf) := by
  let := parameterAlgebra f hf
  let := parameterPolynomialAlgebra f hf
  let := parameter_scalarTower f hf
  let := parameter_finite f hf
  infer_instance

instance parameterCurve_noetherian [CharZero F]
    [FiniteDimensional (IntermediateField.adjoin F {f}) E] :
    IsNoetherian (parameterCurve f hf) := by
  let : FiniteDimensional (IntermediateField.adjoin F {f⁻¹}) E :=
    (adjoin_inverse_eq (F := F) f).symm ▸ inferInstance
  have hlocal : ∀ b, IsLocallyNoetherian ((parameterCurveOpenCover f hf).X b) := by
    intro b
    cases b <;> dsimp [parameterCurveOpenCover] <;> infer_instance
  have : IsLocallyNoetherian (parameterCurve f hf) :=
    (isLocallyNoetherian_iff_openCover (parameterCurveOpenCover f hf)).mpr hlocal
  exact ⟨⟩

attribute [local instance] specializationOrder

theorem parameterCurve_dimension_le_one [CharZero F]
    [FiniteDimensional (IntermediateField.adjoin F {f}) E] :
    topologicalKrullDim (parameterCurve f hf) ≤ 1 := by
  have hs (x : parameterCurve f hf) :
      ringKrullDim ((parameterCurve f hf).presheaf.stalk x) ≤ 1 := by
    by_cases hx : x = genericPoint (parameterCurve f hf)
    · subst x
      change ringKrullDim (parameterCurve f hf).functionField ≤ 1
      have h : Ring.KrullDimLE 1 (parameterCurve f hf).functionField := inferInstance
      exact (Ring.krullDimLE_iff.mp h)
    · let := parameterCurve_stalkDVR f hf x hx
      exact (Ring.krullDimLE_iff.mp (inferInstance :
        Ring.KrullDimLE 1 ((parameterCurve f hf).presheaf.stalk x)))
  change Order.krullDim (IrreducibleCloseds (parameterCurve f hf)) ≤ 1
  rw [Order.krullDim_eq_of_orderIso (irreducibleSetEquivPoints (α := parameterCurve f hf)),
    Order.krullDim_eq_iSup_coheight]
  exact iSup_le fun x => by simpa only [ringKrullDim_stalk_eq_coheight] using hs x

theorem parameterCurve_isClosed_of_ne_generic [CharZero F]
    [FiniteDimensional (IntermediateField.adjoin F {f}) E]
    (x : parameterCurve f hf) (hx : x ≠ genericPoint (parameterCurve f hf)) :
    IsClosed ({x} : Set (parameterCurve f hf)) := by
  apply closure_subset_iff_isClosed.mp
  intro y hy
  have hyx : y ≤ x := specializes_iff_mem_closure.mpr hy
  by_contra hne
  have hylt : y < x := lt_of_le_of_ne hyx (by simpa using hne)
  have hdim : Order.krullDim (parameterCurve f hf) ≤ 1 := by
    have h := parameterCurve_dimension_le_one f hf
    change Order.krullDim (IrreducibleCloseds (parameterCurve f hf)) ≤ 1 at h
    rwa [Order.krullDim_eq_of_orderIso
      (irreducibleSetEquivPoints (α := parameterCurve f hf))] at h
  have hyco : Order.coheight y ≤ (1 : ℕ∞) := by
    exact_mod_cast (Order.coheight_le_krullDim y).trans hdim
  have hxco : Order.coheight x < (1 : ℕ∞) :=
    Order.coheight_le_coe_iff.mp hyco x hylt
  have hxmax : IsMax x := Order.coheight_eq_zero.mp (Order.lt_one_iff.mp hxco)
  exact hx hxmax.eq_top

theorem parameterCurve_exists_nongeneric [CharZero F]
    [FiniteDimensional (IntermediateField.adjoin F {f}) E] :
    ∃ x : parameterCurve f hf, x ≠ genericPoint (parameterCurve f hf) := by
  let := parameterAlgebra f hf
  let := parameterPolynomialAlgebra f hf
  let := parameter_scalarTower f hf
  let := parameter_finite f hf
  let S := parameterChart f hf
  let : Module.IsTorsionFree F[X] S :=
    Module.isTorsionFree_iff_algebraMap_injective.mpr
      (FunctionField.ringOfIntegers.algebraMap_injective F E)
  obtain ⟨q⟩ := (inferInstance : Nonempty ((zeroPrime F).primesOver S))
  let z : PrimeSpectrum S := ⟨q.val, q.property.1⟩
  have hz : z.asIdeal ≠ ⊥ := Ideal.ne_bot_of_mem_primesOver (zeroPrime_ne_bot F) q.property
  refine ⟨zeroChartInclusion f hf z, ?_⟩
  intro heq
  have hgen := genericPoint_eq_of_isOpenImmersion (zeroChartInclusion f hf)
  have he : z = genericPoint (Spec (.of S)) :=
    (zeroChartInclusion f hf).isOpenEmbedding.injective (heq.trans hgen.symm)
  apply hz
  rw [he, genericPoint_eq_bot_of_affine]
  rfl

theorem parameterCurve_isClosed_iff_ne_generic [CharZero F]
    [FiniteDimensional (IntermediateField.adjoin F {f}) E]
    (x : parameterCurve f hf) :
    IsClosed ({x} : Set (parameterCurve f hf)) ↔
      x ≠ genericPoint (parameterCurve f hf) := by
  constructor
  · intro hclosed heq
    subst x
    obtain ⟨y, hy⟩ := parameterCurve_exists_nongeneric f hf
    have hy' : y ∈ closure ({genericPoint (parameterCurve f hf)} :
        Set (parameterCurve f hf)) := by rw [genericPoint_closure]; trivial
    rw [hclosed.closure_eq] at hy'
    exact hy hy'
  · exact parameterCurve_isClosed_of_ne_generic f hf x

end PiExponent.CurveNormalizationModel

end

end OAI
end Source0367

-- Source: OAI/NumberTheory/PiExponent/Geometry/CurveModelPlaces.lean
section Source0368
/-
Modification notice for the LogTwo project.
Derived from openai/math (Apache-2.0), revision adc7f1241b42e322a6451854ab7e4b4c146bf78a.
Original source: lean/OAI/NumberTheory/PiExponent/Geometry/CurveModelPlaces.lean
Changes: Convert module/import declarations to the Lean 4.34 public module format.
See ../THIRD_PARTY_NOTICES.txt for provenance and the recorded changes.
-/

namespace OAI

noncomputable section
open scoped Polynomial nonZeroDivisors
namespace PiExponent.CurveModelPlaces
universe u
open CurveZeroPole CurveValuationCenter WeightedCurveDegree
open CurveNormalizationModel PlaceParameterModel
open AlgebraicGeometry CategoryTheory

theorem parameterValuationCenter_ne_bot
    {F E : Type u} [Field F] [CharZero F] [Field E] [Algebra F E]
    (f : E) (hf : Transcendental F f)
    [FiniteDimensional (IntermediateField.adjoin F {f}) E]
    (p : NormalizedPlace F E) (hp : 0 ≤ p.valuation f) :
    parameterValuationCenter f hf p.valuation p.constants_nonneg hp ≠ ⊥ := by
  let := parameterAlgebra f hf
  let := parameterPolynomialAlgebra f hf
  let := parameter_scalarTower f hf
  let := parameter_finite f hf
  let S := parameterChart f hf
  obtain ⟨a, b, hb, hab⟩ := IsFractionRing.div_surjective S (parameter p)
  have hbE : algebraMap S E b ≠ 0 :=
    (map_ne_zero_iff _ (IsFractionRing.injective S E)).mpr
      (mem_nonZeroDivisors_iff_ne_zero.mp hb)
  have haE : algebraMap S E a ≠ 0 := by
    intro ha
    rw [ha, zero_div] at hab
    exact parameter_nonzero p hab.symm
  have hbval : 0 ≤ p.valuation (algebraMap S E b) :=
    parameterChart_mem_valuationSubring f hf p.valuation p.constants_nonneg hp b
  have hmul : parameter p * algebraMap S E b = algebraMap S E a :=
    (eq_div_iff hbE).mp hab.symm
  have hapos : 0 < p.valuation (algebraMap S E a) := by
    rw [← hmul, p.valuation.map_mul, parameter_value]
    exact lt_of_lt_of_le (by norm_num : (0 : WithTop ℤ) < 1)
      (le_add_of_nonneg_right hbval)
  have hamem : a ∈ parameterValuationCenter f hf p.valuation p.constants_nonneg hp :=
    (mem_parameterValuationCenter_iff f hf p.valuation p.constants_nonneg hp a).mpr hapos
  intro hzero
  rw [hzero, Ideal.mem_bot] at hamem
  exact haE (by rw [hamem, map_zero])

def chartCenter
    {F E : Type u} [Field F] [CharZero F] [Field E] [Algebra F E]
    (f : E) (hf : Transcendental F f)
    [FiniteDimensional (IntermediateField.adjoin F {f}) E]
    (p : NormalizedPlace F E) (hp : 0 ≤ p.valuation f) :
    IsDedekindDomain.HeightOneSpectrum (parameterChart f hf) where
  asIdeal := parameterValuationCenter f hf p.valuation p.constants_nonneg hp
  isPrime := inferInstance
  ne_bot := parameterValuationCenter_ne_bot f hf p hp

def chartValuation
    {F E : Type u} [Field F] [CharZero F] [Field E] [Algebra F E]
    (f : E) (hf : Transcendental F f)
    [FiniteDimensional (IntermediateField.adjoin F {f}) E]
    (q : IsDedekindDomain.HeightOneSpectrum (parameterChart f hf)) :
    AddValuation E (WithTop ℤ) :=
  let := parameterAlgebra f hf
  let := parameterPolynomialAlgebra f hf
  let := parameter_scalarTower f hf
  let := parameter_finite f hf
  let : Module.IsTorsionFree F[X] (FunctionField.ringOfIntegers F E) :=
    Module.isTorsionFree_iff_algebraMap_injective.mpr
      (FunctionField.ringOfIntegers.algebraMap_injective F E)
  primeFieldValuation (parameterChart f hf) E q

theorem valuation_eq_chartCenter
    {F E : Type u} [Field F] [CharZero F] [Field E] [Algebra F E]
    (f : E) (hf : Transcendental F f)
    [FiniteDimensional (IntermediateField.adjoin F {f}) E]
    (p : NormalizedPlace F E) (hp : 0 ≤ p.valuation f) :
    p.valuation = chartValuation f hf (chartCenter f hf p hp) := by
  let := parameterAlgebra f hf
  let := parameterPolynomialAlgebra f hf
  let := parameter_scalarTower f hf
  let := parameter_finite f hf
  let S := parameterChart f hf
  let q := parameterValuationCenter f hf p.valuation p.constants_nonneg hp
  let A := Localization.AtPrime q
  let := IsLocalization.localizationAlgebraOfSubmonoidLe A E
    q.primeCompl S⁰ q.primeCompl_le_nonZeroDivisors
  let := IsLocalization.localization_isScalarTower_of_submonoid_le A E
    q.primeCompl S⁰ q.primeCompl_le_nonZeroDivisors
  let := IsFractionRing.isFractionRing_of_isDomain_of_isLocalization q.primeCompl A E
  let := IsLocalization.AtPrime.isDiscreteValuationRing_of_dedekind_domain S
    (parameterValuationCenter_ne_bot f hf p hp) A
  change p.valuation = CurveLocalOrder.fractionAddValuation A E
  apply DVRValuationUnique.eq_fractionAddValuation p.valuation
  · exact parameterCenterLocal_nonneg f hf p.valuation p.constants_nonneg hp
  · intro a ha _
    exact parameterCenterLocal_positive f hf p.valuation p.constants_nonneg hp a ha
  · exact p.normalized

theorem chartValuation_nonneg
    {F E : Type u} [Field F] [CharZero F] [Field E] [Algebra F E]
    (f : E) (hf : Transcendental F f)
    [FiniteDimensional (IntermediateField.adjoin F {f}) E]
    (q : IsDedekindDomain.HeightOneSpectrum (parameterChart f hf))
    (a : parameterChart f hf) : 0 ≤ chartValuation f hf q (a : E) := by
  let := parameterAlgebra f hf
  let := parameterPolynomialAlgebra f hf
  let := parameter_scalarTower f hf
  let := parameter_finite f hf
  exact primeFieldValuation_algebraMap_nonneg (parameterChart f hf) E q a

theorem chartValuation_positive_iff
    {F E : Type u} [Field F] [CharZero F] [Field E] [Algebra F E]
    (f : E) (hf : Transcendental F f)
    [FiniteDimensional (IntermediateField.adjoin F {f}) E]
    (q : IsDedekindDomain.HeightOneSpectrum (parameterChart f hf))
    (a : parameterChart f hf) : 0 < chartValuation f hf q (a : E) ↔ a ∈ q.asIdeal := by
  let := parameterAlgebra f hf
  let := parameterPolynomialAlgebra f hf
  let := parameter_scalarTower f hf
  let := parameter_finite f hf
  exact primeFieldValuation_positive_iff (parameterChart f hf) E q a

def chartPlace
    {F E : Type u} [Field F] [CharZero F] [Field E] [Algebra F E]
    (f : E) (hf : Transcendental F f)
    [FiniteDimensional (IntermediateField.adjoin F {f}) E]
    (q : IsDedekindDomain.HeightOneSpectrum (parameterChart f hf)) :
    NormalizedPlace F E where
  valuation := chartValuation f hf q
  constants_nonneg c := by
    let := parameterPolynomialAlgebra f hf
    have hmap : ((algebraMap F[X] (parameterChart f hf) (Polynomial.C c)) : E) =
        algebraMap F E c := by
      change algebraMap F[X] E (Polynomial.C c) = _
      rw [parameterPolynomialAlgebra_map, Polynomial.aeval_C]
    rw [← hmap]
    exact chartValuation_nonneg f hf q _
  normalized := by
    let := parameterAlgebra f hf
    let := parameterPolynomialAlgebra f hf
    let := parameter_scalarTower f hf
    let := parameter_finite f hf
    exact primeFieldValuation_normalized (parameterChart f hf) E q

theorem chartPlace_parameter_nonneg
    {F E : Type u} [Field F] [CharZero F] [Field E] [Algebra F E]
    (f : E) (hf : Transcendental F f)
    [FiniteDimensional (IntermediateField.adjoin F {f}) E]
    (q : IsDedekindDomain.HeightOneSpectrum (parameterChart f hf)) :
    0 ≤ (chartPlace f hf q).valuation f := by
  let := parameterPolynomialAlgebra f hf
  have hmap : ((algebraMap F[X] (parameterChart f hf) Polynomial.X) : E) = f := by
    change algebraMap F[X] E Polynomial.X = f
    rw [parameterPolynomialAlgebra_map, Polynomial.aeval_X]
  have hn := chartValuation_nonneg f hf q
    (algebraMap F[X] (parameterChart f hf) Polynomial.X)
  exact (congrArg (fun x : E => 0 ≤ chartValuation f hf q x) hmap).mp hn

@[simp] theorem chartPlace_chartCenter
    {F E : Type u} [Field F] [CharZero F] [Field E] [Algebra F E]
    (f : E) (hf : Transcendental F f)
    [FiniteDimensional (IntermediateField.adjoin F {f}) E]
    (p : NormalizedPlace F E) (hp : 0 ≤ p.valuation f) :
    chartPlace f hf (chartCenter f hf p hp) = p :=
  NormalizedPlace.ext (valuation_eq_chartCenter f hf p hp).symm

@[simp] theorem chartCenter_chartPlace
    {F E : Type u} [Field F] [CharZero F] [Field E] [Algebra F E]
    (f : E) (hf : Transcendental F f)
    [FiniteDimensional (IntermediateField.adjoin F {f}) E]
    (q : IsDedekindDomain.HeightOneSpectrum (parameterChart f hf)) :
    chartCenter f hf (chartPlace f hf q) (chartPlace_parameter_nonneg f hf q) = q := by
  apply IsDedekindDomain.HeightOneSpectrum.ext
  ext a
  exact (mem_parameterValuationCenter_iff f hf (chartPlace f hf q).valuation
    (chartPlace f hf q).constants_nonneg (chartPlace_parameter_nonneg f hf q) a).trans
      (chartValuation_positive_iff f hf q a)

def regularPlacesEquivChartPrimes
    {F E : Type u} [Field F] [CharZero F] [Field E] [Algebra F E]
    (f : E) (hf : Transcendental F f)
    [FiniteDimensional (IntermediateField.adjoin F {f}) E] :
    {p : NormalizedPlace F E // 0 ≤ p.valuation f} ≃
      IsDedekindDomain.HeightOneSpectrum (parameterChart f hf) where
  toFun p := chartCenter f hf p.1 p.2
  invFun q := ⟨chartPlace f hf q, chartPlace_parameter_nonneg f hf q⟩
  left_inv p := Subtype.ext (chartPlace_chartCenter f hf p.1 p.2)
  right_inv q := chartCenter_chartPlace f hf q

theorem parameterLaurentMap_mem
    {F E : Type u} [Field F] [Field E] [Algebra F E]
    (f : E) (hf : Transcendental F f) (p : NormalizedPlace F E)
    (hp : 0 ≤ p.valuation f) (hpinv : 0 ≤ p.valuation f⁻¹)
    (a : LaurentPolynomial F) :
    parameterLaurentMap f hf a ∈ p.valuation.toValuation.valuationSubring := by
  induction a using LaurentPolynomial.induction_on' with
  | add a b ha hb =>
    rw [map_add]
    exact p.valuation.toValuation.valuationSubring.toSubring.add_mem ha hb
  | C_mul_T n c =>
    by_cases hn : 0 ≤ n
    · lift n to ℕ using hn
      rw [parameterLaurentMap, LaurentPolynomial.eval₂_C_mul_T_n]
      exact p.valuation.toValuation.valuationSubring.toSubring.mul_mem
        (p.constants_nonneg c)
        (p.valuation.toValuation.valuationSubring.toSubring.pow_mem hp n)
    · obtain ⟨k, rfl⟩ := Int.exists_eq_neg_ofNat (le_of_not_ge hn)
      rw [parameterLaurentMap, LaurentPolynomial.eval₂_C_mul_T_neg_n]
      exact p.valuation.toValuation.valuationSubring.toSubring.mul_mem
        (p.constants_nonneg c)
        (p.valuation.toValuation.valuationSubring.toSubring.pow_mem hpinv k)

theorem parameterLaurentChart_mem
    {F E : Type u} [Field F] [Field E] [Algebra F E]
    (f : E) (hf : Transcendental F f) (p : NormalizedPlace F E)
    (hp : 0 ≤ p.valuation f) (hpinv : 0 ≤ p.valuation f⁻¹)
    (a : parameterLaurentChart f hf) :
    (a : E) ∈ p.valuation.toValuation.valuationSubring := by
  let := parameterLaurentAlgebra f hf
  exact integral_mem_valuationSubring p.valuation.toValuation
    (parameterLaurentMap_mem f hf p hp hpinv) a.property

def laurentValuationHom
    {F E : Type u} [Field F] [Field E] [Algebra F E]
    (f : E) (hf : Transcendental F f) (p : NormalizedPlace F E)
    (hp : 0 ≤ p.valuation f) (hpinv : 0 ≤ p.valuation f⁻¹) :
    parameterLaurentChart f hf →+* p.valuation.toValuation.valuationSubring where
  toFun a := ⟨a, parameterLaurentChart_mem f hf p hp hpinv a⟩
  map_zero' := rfl
  map_one' := rfl
  map_add' _ _ := rfl
  map_mul' _ _ := rfl

def laurentCenter
    {F E : Type u} [Field F] [Field E] [Algebra F E]
    (f : E) (hf : Transcendental F f) (p : NormalizedPlace F E)
    (hp : 0 ≤ p.valuation f) (hpinv : 0 ≤ p.valuation f⁻¹) :
    PrimeSpectrum (parameterLaurentChart f hf) :=
  ⟨(IsLocalRing.maximalIdeal p.valuation.toValuation.valuationSubring).comap
    (laurentValuationHom f hf p hp hpinv), inferInstance⟩

theorem laurentCenter_zero
    {F E : Type u} [Field F] [Field E] [Algebra F E]
    (f : E) (hf : Transcendental F f) (p : NormalizedPlace F E)
    (hp : 0 ≤ p.valuation f) (hpinv : 0 ≤ p.valuation f⁻¹) :
    zeroOverlap f hf (laurentCenter f hf p hp hpinv) =
      ⟨parameterValuationCenter f hf p.valuation p.constants_nonneg hp, inferInstance⟩ := by
  apply PrimeSpectrum.ext
  ext a
  rfl

theorem laurentCenter_infinity
    {F E : Type u} [Field F] [Field E] [Algebra F E]
    (f : E) (hf : Transcendental F f) (p : NormalizedPlace F E)
    (hp : 0 ≤ p.valuation f) (hpinv : 0 ≤ p.valuation f⁻¹) :
    infinityOverlap f hf (laurentCenter f hf p hp hpinv) =
      ⟨parameterValuationCenter f⁻¹ (transcendental_inverse f hf)
        p.valuation p.constants_nonneg hpinv, inferInstance⟩ := by
  apply PrimeSpectrum.ext
  ext a
  rfl

theorem center_images_eq
    {F E : Type u} [Field F] [Field E] [Algebra F E]
    (f : E) (hf : Transcendental F f) (p : NormalizedPlace F E)
    (hp : 0 ≤ p.valuation f) (hpinv : 0 ≤ p.valuation f⁻¹) :
    zeroChartInclusion f hf
      ⟨parameterValuationCenter f hf p.valuation p.constants_nonneg hp, inferInstance⟩ =
    infinityChartInclusion f hf
      ⟨parameterValuationCenter f⁻¹ (transcendental_inverse f hf)
        p.valuation p.constants_nonneg hpinv, inferInstance⟩ := by
  rw [← laurentCenter_zero f hf p hp hpinv, ← laurentCenter_infinity f hf p hp hpinv]
  exact congrArg (fun g => g (laurentCenter f hf p hp hpinv))
    (parameterCurve_overlap_compatibility f hf)

theorem regular_iff_inverse_not_positive
    {F E : Type u} [Field F] [Field E] [Algebra F E]
    (p : NormalizedPlace F E) (f : E) (hf : f ≠ 0) :
    0 ≤ p.valuation f ↔ ¬ 0 < p.valuation f⁻¹ := by
  let z := Units.mk0 f hf
  change 0 ≤ p.valuation (z : E) ↔ ¬ 0 < p.valuation ((z : E)⁻¹)
  rw [← Units.val_inv_eq_inv_val, ← coe_integerOrder, ← coe_integerOrder, integerOrder_inv]
  change ((0 : ℤ) : WithTop ℤ) ≤ (integerOrder p.valuation z : WithTop ℤ) ↔
    ¬ ((0 : ℤ) : WithTop ℤ) < (-integerOrder p.valuation z : ℤ)
  rw [WithTop.coe_le_coe, WithTop.coe_lt_coe]
  omega

theorem inverse_positive_of_not_regular
    {F E : Type u} [Field F] [Field E] [Algebra F E]
    (p : NormalizedPlace F E) (f : E) (hf : f ≠ 0)
    (hp : ¬ 0 ≤ p.valuation f) : 0 < p.valuation f⁻¹ := by
  exact Classical.not_not.mp ((not_congr (regular_iff_inverse_not_positive p f hf)).mp hp)

def placePoint
    {F E : Type u} [Field F] [Field E] [Algebra F E]
    (f : E) (hf : Transcendental F f) (p : NormalizedPlace F E) : parameterCurve f hf :=
  if hp : 0 ≤ p.valuation f then
    zeroChartInclusion f hf
      ⟨parameterValuationCenter f hf p.valuation p.constants_nonneg hp, inferInstance⟩
  else
    infinityChartInclusion f hf
      ⟨parameterValuationCenter f⁻¹ (transcendental_inverse f hf)
        p.valuation p.constants_nonneg (inverse_positive_of_not_regular p f hf.ne_zero hp).le,
        inferInstance⟩

theorem placePoint_eq_zero
    {F E : Type u} [Field F] [Field E] [Algebra F E]
    (f : E) (hf : Transcendental F f) (p : NormalizedPlace F E)
    (hp : 0 ≤ p.valuation f) :
    placePoint f hf p = zeroChartInclusion f hf
      ⟨parameterValuationCenter f hf p.valuation p.constants_nonneg hp, inferInstance⟩ := by
  simp only [placePoint, dite_eq_left hp]

theorem placePoint_eq_infinity
    {F E : Type u} [Field F] [Field E] [Algebra F E]
    (f : E) (hf : Transcendental F f) (p : NormalizedPlace F E)
    (hp : 0 ≤ p.valuation f⁻¹) :
    placePoint f hf p = infinityChartInclusion f hf
      ⟨parameterValuationCenter f⁻¹ (transcendental_inverse f hf)
        p.valuation p.constants_nonneg hp, inferInstance⟩ := by
  by_cases h : 0 ≤ p.valuation f
  · rw [placePoint_eq_zero f hf p h]
    exact center_images_eq f hf p h hp
  · simp only [placePoint, dite_eq_right h]

theorem placePoint_ne_genericPoint
    {F E : Type u} [Field F] [CharZero F] [Field E] [Algebra F E]
    (f : E) (hf : Transcendental F f)
    [FiniteDimensional (IntermediateField.adjoin F {f}) E]
    (p : NormalizedPlace F E) : placePoint f hf p ≠ genericPoint (parameterCurve f hf) := by
  by_cases hp : 0 ≤ p.valuation f
  · rw [placePoint_eq_zero f hf p hp]
    intro h
    have hq := (zeroChartInclusion f hf).injective
      (h.trans (genericPoint_eq_of_isOpenImmersion (zeroChartInclusion f hf)).symm)
    rw [genericPoint_eq_bot_of_affine] at hq
    exact parameterValuationCenter_ne_bot f hf p hp (congrArg PrimeSpectrum.asIdeal hq)
  · let : FiniteDimensional (IntermediateField.adjoin F {f⁻¹}) E :=
      (adjoin_inverse_eq (F := F) f).symm ▸ inferInstance
    have hi := (inverse_positive_of_not_regular p f hf.ne_zero hp).le
    rw [placePoint_eq_infinity f hf p hi]
    intro h
    have hq := (infinityChartInclusion f hf).injective
      (h.trans (genericPoint_eq_of_isOpenImmersion (infinityChartInclusion f hf)).symm)
    rw [genericPoint_eq_bot_of_affine] at hq
    exact parameterValuationCenter_ne_bot f⁻¹ (transcendental_inverse f hf) p hi
      (congrArg PrimeSpectrum.asIdeal hq)

theorem regular_center_injective
    {F E : Type u} [Field F] [CharZero F] [Field E] [Algebra F E]
    (f : E) (hf : Transcendental F f)
    [FiniteDimensional (IntermediateField.adjoin F {f}) E]
    (p q : NormalizedPlace F E) (hp : 0 ≤ p.valuation f) (hq : 0 ≤ q.valuation f)
    (h : parameterValuationCenter f hf p.valuation p.constants_nonneg hp =
      parameterValuationCenter f hf q.valuation q.constants_nonneg hq) : p = q := by
  have hc : chartCenter f hf p hp = chartCenter f hf q hq :=
    IsDedekindDomain.HeightOneSpectrum.ext h
  calc
    p = chartPlace f hf (chartCenter f hf p hp) := (chartPlace_chartCenter f hf p hp).symm
    _ = chartPlace f hf (chartCenter f hf q hq) := congrArg (chartPlace f hf) hc
    _ = q := chartPlace_chartCenter f hf q hq

theorem placePoint_mem_zero_iff
    {F E : Type u} [Field F] [Field E] [Algebra F E]
    (f : E) (hf : Transcendental F f) (p : NormalizedPlace F E) :
    placePoint f hf p ∈ Set.range (zeroChartInclusion f hf) ↔ 0 ≤ p.valuation f := by
  constructor
  · intro h
    by_contra hp
    have hi := inverse_positive_of_not_regular p f hf.ne_zero hp
    let q : PrimeSpectrum (parameterChart f⁻¹ (transcendental_inverse f hf)) :=
      ⟨parameterValuationCenter f⁻¹ (transcendental_inverse f hf)
        p.valuation p.constants_nonneg hi.le, inferInstance⟩
    have he : placePoint f hf p = infinityChartInclusion f hf q :=
      placePoint_eq_infinity f hf p hi.le
    have hm : infinityChartInclusion f hf q ∈ Set.range (zeroChartInclusion f hf) := he ▸ h
    have ho := (infinityChart_mem_zero_iff f hf q).mp hm
    let := parameterPolynomialAlgebra f⁻¹ (transcendental_inverse f hf)
    have h := (congrArg (fun s => q ∈ s) (infinityOverlap_range f hf)).mp ho
    change algebraMap F[X] (parameterChart f⁻¹ (transcendental_inverse f hf)) Polynomial.X ∉
      parameterValuationCenter f⁻¹ (transcendental_inverse f hf)
        p.valuation p.constants_nonneg hi.le at h
    apply h
    rw [mem_parameterValuationCenter_iff]
    have hmap : ((algebraMap F[X] (parameterChart f⁻¹ (transcendental_inverse f hf))
        Polynomial.X) : E) = f⁻¹ := by
      change algebraMap F[X] E Polynomial.X = f⁻¹
      rw [parameterPolynomialAlgebra_map, Polynomial.aeval_X]
    exact (congrArg (fun a : E => 0 < p.valuation a) hmap).mpr hi
  · intro hp
    rw [placePoint_eq_zero f hf p hp]
    exact ⟨_, rfl⟩

theorem placePoint_injective
    {F E : Type u} [Field F] [CharZero F] [Field E] [Algebra F E]
    (f : E) (hf : Transcendental F f)
    [FiniteDimensional (IntermediateField.adjoin F {f}) E] :
    Function.Injective (placePoint f hf) := by
  intro p q h
  have hreg : (0 ≤ p.valuation f) ↔ (0 ≤ q.valuation f) := by
    rw [← placePoint_mem_zero_iff f hf p, ← placePoint_mem_zero_iff f hf q, h]
  by_cases hp : 0 ≤ p.valuation f
  · have hq := hreg.mp hp
    rw [placePoint_eq_zero f hf p hp, placePoint_eq_zero f hf q hq] at h
    have hc := (zeroChartInclusion f hf).injective h
    exact regular_center_injective f hf p q hp hq (congrArg PrimeSpectrum.asIdeal hc)
  · have hq : ¬ 0 ≤ q.valuation f := fun hq => hp (hreg.mpr hq)
    have hip := (inverse_positive_of_not_regular p f hf.ne_zero hp).le
    have hiq := (inverse_positive_of_not_regular q f hf.ne_zero hq).le
    rw [placePoint_eq_infinity f hf p hip, placePoint_eq_infinity f hf q hiq] at h
    have hc := (infinityChartInclusion f hf).injective h
    let : FiniteDimensional (IntermediateField.adjoin F {f⁻¹}) E :=
      (adjoin_inverse_eq (F := F) f).symm ▸ inferInstance
    exact regular_center_injective f⁻¹ (transcendental_inverse f hf) p q hip hiq
      (congrArg PrimeSpectrum.asIdeal hc)

theorem exists_placePoint_eq
    {F E : Type u} [Field F] [CharZero F] [Field E] [Algebra F E]
    (f : E) (hf : Transcendental F f)
    [FiniteDimensional (IntermediateField.adjoin F {f}) E]
    (x : parameterCurve f hf) (hx : x ≠ genericPoint (parameterCurve f hf)) :
    ∃ p : NormalizedPlace F E, placePoint f hf p = x := by
  rcases parameterCurve_twoChartCover f hf x with ⟨q, rfl⟩ | ⟨q, rfl⟩
  · have hq : q.asIdeal ≠ ⊥ := by
      intro h
      have heq : q = genericPoint (Spec (.of (parameterChart f hf))) := by
        rw [genericPoint_eq_bot_of_affine]
        exact PrimeSpectrum.ext h
      apply hx
      rw [heq]
      exact genericPoint_eq_of_isOpenImmersion (zeroChartInclusion f hf)
    let Q : IsDedekindDomain.HeightOneSpectrum (parameterChart f hf) :=
      ⟨q.asIdeal, q.isPrime, hq⟩
    let p := chartPlace f hf Q
    refine ⟨p, ?_⟩
    rw [placePoint_eq_zero f hf p (chartPlace_parameter_nonneg f hf Q)]
    congr 1
    apply PrimeSpectrum.ext
    exact congrArg IsDedekindDomain.HeightOneSpectrum.asIdeal
      (chartCenter_chartPlace f hf Q)
  · let : FiniteDimensional (IntermediateField.adjoin F {f⁻¹}) E :=
      (adjoin_inverse_eq (F := F) f).symm ▸ inferInstance
    have hq : q.asIdeal ≠ ⊥ := by
      intro h
      have heq : q = genericPoint
          (Spec (.of (parameterChart f⁻¹ (transcendental_inverse f hf)))) := by
        rw [genericPoint_eq_bot_of_affine]
        exact PrimeSpectrum.ext h
      apply hx
      rw [heq]
      exact genericPoint_eq_of_isOpenImmersion (infinityChartInclusion f hf)
    let Q : IsDedekindDomain.HeightOneSpectrum
        (parameterChart f⁻¹ (transcendental_inverse f hf)) := ⟨q.asIdeal, q.isPrime, hq⟩
    let p := chartPlace f⁻¹ (transcendental_inverse f hf) Q
    refine ⟨p, ?_⟩
    rw [placePoint_eq_infinity f hf p
      (chartPlace_parameter_nonneg f⁻¹ (transcendental_inverse f hf) Q)]
    congr 1
    apply PrimeSpectrum.ext
    exact congrArg IsDedekindDomain.HeightOneSpectrum.asIdeal
      (chartCenter_chartPlace f⁻¹ (transcendental_inverse f hf) Q)

def placesEquivNongenericPoints
    {F E : Type u} [Field F] [CharZero F] [Field E] [Algebra F E]
    (f : E) (hf : Transcendental F f)
    [FiniteDimensional (IntermediateField.adjoin F {f}) E] :
    NormalizedPlace F E ≃ {x : parameterCurve f hf // x ≠ genericPoint (parameterCurve f hf)} :=
  Equiv.ofBijective (fun p => ⟨placePoint f hf p, placePoint_ne_genericPoint f hf p⟩) ⟨
    fun _ _ h => placePoint_injective f hf (congrArg Subtype.val h),
    fun x => by
      obtain ⟨p, hp⟩ := exists_placePoint_eq f hf x.1 x.2
      exact ⟨p, Subtype.ext hp⟩⟩

def placesEquivClosedPoints
    {F E : Type u} [Field F] [CharZero F] [Field E] [Algebra F E]
    (f : E) (hf : Transcendental F f)
    [FiniteDimensional (IntermediateField.adjoin F {f}) E] :
    NormalizedPlace F E ≃ {x : parameterCurve f hf // IsClosed ({x} : Set (parameterCurve f hf))} :=
  (placesEquivNongenericPoints f hf).trans
    { toFun := fun x => ⟨x.1, (parameterCurve_isClosed_iff_ne_generic f hf x.1).mpr x.2⟩
      invFun := fun x => ⟨x.1, (parameterCurve_isClosed_iff_ne_generic f hf x.1).mp x.2⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }

end PiExponent.CurveModelPlaces

end

end OAI
end Source0368

-- Source: OAI/NumberTheory/PiExponent/Geometry/CurveModelLocalOrder.lean
section Source0369
-- Modified in this edition: unused plain lemmas removed; see reduction.json.
/-
Modification notice for the LogTwo project.
Derived from openai/math (Apache-2.0), revision adc7f1241b42e322a6451854ab7e4b4c146bf78a.
Original source: lean/OAI/NumberTheory/PiExponent/Geometry/CurveModelLocalOrder.lean
Changes: Convert module/import declarations to the Lean 4.34 public module format.
See ../THIRD_PARTY_NOTICES.txt for provenance and the recorded changes.
-/

namespace OAI

noncomputable section
open scoped Polynomial nonZeroDivisors
namespace PiExponent.CurveModelLocalOrder
universe u
open CurveZeroPole CurveValuationCenter WeightedCurveDegree
open CurveNormalizationModel CurveModelPlaces
open AlgebraicGeometry CategoryTheory

def chartCenterLocalRingEquiv
    {F E : Type u} [Field F] [CharZero F] [Field E] [Algebra F E]
    (f : E) (hf : Transcendental F f)
    [FiniteDimensional (IntermediateField.adjoin F {f}) E]
    (p : NormalizedPlace F E) (hp : 0 ≤ p.valuation f) :
    Localization.AtPrime (parameterValuationCenter f hf p.valuation p.constants_nonneg hp) ≃+*
      PlaceValuationRing.ring p := by
  let := parameterAlgebra f hf
  let := parameterPolynomialAlgebra f hf
  let := parameter_scalarTower f hf
  let := parameter_finite f hf
  let S := parameterChart f hf
  let q := parameterValuationCenter f hf p.valuation p.constants_nonneg hp
  let A := Localization.AtPrime q
  let := IsLocalization.localizationAlgebraOfSubmonoidLe A E
    q.primeCompl S⁰ q.primeCompl_le_nonZeroDivisors
  let := IsLocalization.localization_isScalarTower_of_submonoid_le A E
    q.primeCompl S⁰ q.primeCompl_le_nonZeroDivisors
  let := IsFractionRing.isFractionRing_of_isDomain_of_isLocalization q.primeCompl A E
  let := IsLocalization.AtPrime.isDiscreteValuationRing_of_dedekind_domain S
    (parameterValuationCenter_ne_bot f hf p hp) A
  let φ := parameterCenterLocalHom f hf p.valuation p.constants_nonneg hp
  have he : p.valuation = CurveLocalOrder.fractionAddValuation A E :=
    valuation_eq_chartCenter f hf p hp
  apply RingEquiv.ofBijective φ
  constructor
  · intro a b hab
    apply IsFractionRing.injective A E
    have hh := congrArg (fun x : p.valuation.toValuation.valuationSubring => (x : E)) hab
    simpa only [φ, parameterCenterLocalHom_coe] using hh
  · intro x
    have hx : 0 ≤ CurveLocalOrder.fractionAddValuation A E (x : E) := by
      rw [← he]
      exact x.property
    obtain ⟨a, ha⟩ := (WeightedLocalLattice.exists_local_element_iff_nonnegative_order
      (A := A) (x : E)).mpr hx
    refine ⟨a, ?_⟩
    apply Subtype.ext
    exact (parameterCenterLocalHom_coe f hf p.valuation p.constants_nonneg hp a).trans ha

def chartCenterLocalAlgEquiv
    {F E : Type u} [Field F] [CharZero F] [Field E] [Algebra F E]
    (f : E) (hf : Transcendental F f)
    [FiniteDimensional (IntermediateField.adjoin F {f}) E]
    (p : NormalizedPlace F E) (hp : 0 ≤ p.valuation f) :
    letI := ParameterResidueField.parameterChartConstants f hf
    Localization.AtPrime (parameterValuationCenter f hf p.valuation p.constants_nonneg hp) ≃ₐ[F]
      PlaceValuationRing.ring p := by
  let := ParameterResidueField.parameterChartConstants f hf
  refine { chartCenterLocalRingEquiv f hf p hp with commutes' := ?_ }
  intro c
  apply Subtype.ext
  change (parameterCenterLocalHom f hf p.valuation p.constants_nonneg hp
    (algebraMap F _ c) : E) = algebraMap F E c
  rw [IsScalarTower.algebraMap_apply F (parameterChart f hf)
    (Localization.AtPrime (parameterValuationCenter f hf p.valuation p.constants_nonneg hp))]
  rw [parameterCenterLocalHom_algebraMap]
  let := parameterPolynomialAlgebra f hf
  change (algebraMap F[X] E (Polynomial.C c)) = algebraMap F E c
  rw [parameterPolynomialAlgebra_map f hf, Polynomial.aeval_C]

def placePointStalkRingEquiv
    {F E : Type u} [Field F] [CharZero F] [Field E] [Algebra F E]
    (f : E) (hf : Transcendental F f)
    [FiniteDimensional (IntermediateField.adjoin F {f}) E]
    (p : NormalizedPlace F E) :
    (parameterCurve f hf).presheaf.stalk (placePoint f hf p) ≃+*
      PlaceValuationRing.ring p := by
  by_cases hp : 0 ≤ p.valuation f
  · rw [placePoint_eq_zero f hf p hp]
    exact (zeroChartStalkIso f hf _).commRingCatIsoToRingEquiv.trans
      (chartCenterLocalRingEquiv f hf p hp)
  · letI : FiniteDimensional (IntermediateField.adjoin F {f⁻¹}) E :=
      (adjoin_inverse_eq (F := F) f).symm ▸ inferInstance
    have hi := (inverse_positive_of_not_regular p f hf.ne_zero hp).le
    rw [placePoint_eq_infinity f hf p hi]
    exact (infinityChartStalkIso f hf _).commRingCatIsoToRingEquiv.trans
      (chartCenterLocalRingEquiv f⁻¹ (transcendental_inverse f hf) p hi)

theorem addVal_ringEquiv
    {A B : Type*} [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
    [CommRing B] [IsDomain B] [IsDiscreteValuationRing B]
    (e : A ≃+* B) (a : A) :
    IsDiscreteValuationRing.addVal B (e a) = IsDiscreteValuationRing.addVal A a := by
  by_cases ha : a = 0
  · simp only [ha, map_zero, IsDiscreteValuationRing.addVal_zero]
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_prime A
  obtain ⟨n, u, rfl⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible ha hπ.irreducible
  rw [map_mul, map_pow, IsDiscreteValuationRing.addVal_def' u hπ.irreducible n]
  exact IsDiscreteValuationRing.addVal_def' (Units.map e.toMonoidHom u)
    (hπ.irreducible.map e) n

end PiExponent.CurveModelLocalOrder

end

end OAI
end Source0369

-- Source: OAI/NumberTheory/PiExponent/Geometry/CurveChartFunctionField.lean
section Source0370
-- Modified in this edition: unused plain lemmas removed; see reduction.json.
/-
Modification notice for the LogTwo project.
Derived from openai/math (Apache-2.0), revision adc7f1241b42e322a6451854ab7e4b4c146bf78a.
Original source: lean/OAI/NumberTheory/PiExponent/Geometry/CurveChartFunctionField.lean
Changes: Convert module/import declarations to the Lean 4.34 public module format.
See ../THIRD_PARTY_NOTICES.txt for provenance and the recorded changes.
-/

namespace OAI

noncomputable section
namespace PiExponent.CurveNormalizationModel
open CategoryTheory AlgebraicGeometry
universe u
variable (A E : Type u) [CommRing A] [IsDomain A] [Field E]
  [Algebra A E] [IsFractionRing A E]

def affineChartFunctionFieldMap {X : Scheme.{u}} [IsIntegral X]
    (i : Spec (.of A) ⟶ X) [IsOpenImmersion i] : X.functionField →+* E :=
  (affineFunctionFieldEquiv A E).toRingHom.comp (functionFieldRestriction i).hom

private theorem restriction_congr {U X : Scheme.{u}} [IsIntegral U] [IsIntegral X]
    {i j : U ⟶ X} [IsOpenImmersion i] [IsOpenImmersion j] (h : i = j) :
    functionFieldRestriction i = functionFieldRestriction j := by
  subst j
  rfl

theorem affineChartFunctionFieldMap_eq_of_overlap
    (B G : Type u) [CommRing B] [IsDomain B] [CommRing G] [IsDomain G]
    [Algebra B E] [IsFractionRing B E] [Algebra G E] [IsFractionRing G E]
    [Algebra A G] [Algebra B G] [IsScalarTower A G E] [IsScalarTower B G E]
    {X : Scheme.{u}} [IsIntegral X]
    (iA : Spec (.of A) ⟶ X) (iB : Spec (.of B) ⟶ X)
    [IsOpenImmersion iA] [IsOpenImmersion iB]
    [IsOpenImmersion (Spec.map (CommRingCat.ofHom (algebraMap A G)))]
    [IsOpenImmersion (Spec.map (CommRingCat.ofHom (algebraMap B G)))]
    (h : Spec.map (CommRingCat.ofHom (algebraMap A G)) ≫ iA =
      Spec.map (CommRingCat.ofHom (algebraMap B G)) ≫ iB) :
    affineChartFunctionFieldMap A E iA = affineChartFunctionFieldMap B E iB := by
  have hr : functionFieldRestriction iA ≫
      functionFieldRestriction (Spec.map (CommRingCat.ofHom (algebraMap A G))) =
      functionFieldRestriction iB ≫
      functionFieldRestriction (Spec.map (CommRingCat.ofHom (algebraMap B G))) := by
    rw [← functionFieldRestriction_comp, ← functionFieldRestriction_comp]
    exact restriction_congr h
  apply RingHom.ext
  intro z
  have hz := congrArg (fun g => affineFunctionFieldEquiv G E (g z)) hr
  change affineFunctionFieldEquiv G E
    (functionFieldRestriction (Spec.map (CommRingCat.ofHom (algebraMap A G)))
      (functionFieldRestriction iA z)) =
    affineFunctionFieldEquiv G E
    (functionFieldRestriction (Spec.map (CommRingCat.ofHom (algebraMap B G)))
      (functionFieldRestriction iB z)) at hz
  have hA := RingHom.congr_fun (affineFunctionFieldEquiv_naturality A E G)
    (functionFieldRestriction iA z)
  have hB := RingHom.congr_fun (affineFunctionFieldEquiv_naturality B E G)
    (functionFieldRestriction iB z)
  exact hA.symm.trans (hz.trans hB)

end PiExponent.CurveNormalizationModel

end

end OAI
end Source0370

-- Source: OAI/NumberTheory/PiExponent/Geometry/CurveModelFieldEmbedding.lean
section Source0371
-- Modified in this edition: unused plain lemmas removed; see reduction.json.
/-
Modification notice for the LogTwo project.
Derived from openai/math (Apache-2.0), revision adc7f1241b42e322a6451854ab7e4b4c146bf78a.
Original source: lean/OAI/NumberTheory/PiExponent/Geometry/CurveModelFieldEmbedding.lean
Changes: Convert module/import declarations to the Lean 4.34 public module format.
See ../THIRD_PARTY_NOTICES.txt for provenance and the recorded changes.
-/

namespace OAI

noncomputable section
namespace PiExponent.CurveNormalizationModel
open CategoryTheory AlgebraicGeometry
open scoped Polynomial nonZeroDivisors
open PiExponent.CurveZeroPole
universe u
variable {F E : Type u} [Field F] [Field E] [Algebra F E]
variable (f : E) (hf : Transcendental F f)
variable [FiniteDimensional (IntermediateField.adjoin F {f}) E]

abbrev parameterChartFractionRing : IsFractionRing (parameterChart f hf) E :=
  let := parameterAlgebra f hf
  let := parameterPolynomialAlgebra f hf
  let := parameter_scalarTower f hf
  let := parameter_finite f hf
  inferInstance

abbrev parameterChartLocalAlgebra (q : PrimeSpectrum (parameterChart f hf)) :
    Algebra (Localization.AtPrime q.asIdeal) E :=
  let := parameterChartFractionRing f hf
  IsLocalization.localizationAlgebraOfSubmonoidLe (Localization.AtPrime q.asIdeal) E
    q.asIdeal.primeCompl (nonZeroDivisors (parameterChart f hf))
    q.asIdeal.primeCompl_le_nonZeroDivisors

theorem parameterLaurentChartFractionRing : IsFractionRing (parameterLaurentChart f hf) E := by
  let := parameterChartFractionRing f hf
  let : Algebra (parameterChart f hf) (parameterLaurentChart f hf) :=
    (parameterChartOverlapHom f hf).toAlgebra
  have : IsScalarTower (parameterChart f hf) (parameterLaurentChart f hf) E :=
    IsScalarTower.of_algebraMap_eq' rfl
  exact isFractionRing_of_intermediate_domain (parameterChart f hf) E
    (parameterLaurentChart f hf) Subtype.val_injective

theorem parameterCurveFunctionFieldEquiv_eq_infinity :
    letI : FiniteDimensional (IntermediateField.adjoin F {f⁻¹}) E :=
      (adjoin_inverse_eq (F := F) f).symm ▸ inferInstance
    letI := parameterChartFractionRing f⁻¹ (transcendental_inverse f hf)
    (parameterCurveFunctionFieldEquiv f hf).toRingHom =
      affineChartFunctionFieldMap (parameterChart f⁻¹ (transcendental_inverse f hf)) E
        (infinityChartInclusion f hf) := by
  let : FiniteDimensional (IntermediateField.adjoin F {f⁻¹}) E :=
    (adjoin_inverse_eq (F := F) f).symm ▸ inferInstance
  let := parameterChartFractionRing f hf
  let := parameterChartFractionRing f⁻¹ (transcendental_inverse f hf)
  let := parameterLaurentChartFractionRing f hf
  let : Algebra (parameterChart f hf) (parameterLaurentChart f hf) :=
    (parameterChartOverlapHom f hf).toAlgebra
  let : Algebra (parameterChart f⁻¹ (transcendental_inverse f hf))
      (parameterLaurentChart f hf) :=
    ((reciprocalLaurentChartEquiv f hf).symm.toRingHom.comp
      (parameterChartOverlapHom f⁻¹ (transcendental_inverse f hf))).toAlgebra
  have : IsScalarTower (parameterChart f hf) (parameterLaurentChart f hf) E :=
    IsScalarTower.of_algebraMap_eq' rfl
  have : IsScalarTower (parameterChart f⁻¹ (transcendental_inverse f hf))
      (parameterLaurentChart f hf) E := IsScalarTower.of_algebraMap_eq' rfl
  have : IsOpenImmersion (Spec.map (CommRingCat.ofHom
      (algebraMap (parameterChart f hf) (parameterLaurentChart f hf)))) :=
    zeroOverlap_isOpenImmersion f hf
  have : IsOpenImmersion (Spec.map (CommRingCat.ofHom
      (algebraMap (parameterChart f⁻¹ (transcendental_inverse f hf))
        (parameterLaurentChart f hf)))) := infinityOverlap_isOpenImmersion f hf
  change affineChartFunctionFieldMap (parameterChart f hf) E (zeroChartInclusion f hf) = _
  exact affineChartFunctionFieldMap_eq_of_overlap (parameterChart f hf) E
    (parameterChart f⁻¹ (transcendental_inverse f hf)) (parameterLaurentChart f hf)
    (zeroChartInclusion f hf) (infinityChartInclusion f hf)
    (parameterCurve_overlap_compatibility f hf)

end PiExponent.CurveNormalizationModel

end

end OAI
end Source0371

-- Source: OAI/NumberTheory/PiExponent/Geometry/CurveModelInfinityGenericPoint.lean
section Source0372
/-
Modification notice for the LogTwo project.
Derived from openai/math (Apache-2.0), revision adc7f1241b42e322a6451854ab7e4b4c146bf78a.
Original source: lean/OAI/NumberTheory/PiExponent/Geometry/CurveModelInfinityGenericPoint.lean
Changes: Convert module/import declarations to the Lean 4.34 public module format.
See ../THIRD_PARTY_NOTICES.txt for provenance and the recorded changes.
-/

namespace OAI

noncomputable section
namespace PiExponent.CurveNormalizationModel
open CategoryTheory AlgebraicGeometry PiExponent.CurveZeroPole
universe u
variable {F E : Type u} [Field F] [Field E] [Algebra F E]
variable (f : E) (hf : Transcendental F f)
variable [FiniteDimensional (IntermediateField.adjoin F {f}) E]

theorem parameterCurveGenericPoint_eq_infinityChart :
    parameterCurveGenericPoint f hf =
      Spec.map (CommRingCat.ofHom
        (algebraMap (parameterChart f⁻¹ (transcendental_inverse f hf)) E)) ≫
        infinityChartInclusion f hf := by
  let : FiniteDimensional (IntermediateField.adjoin F {f⁻¹}) E :=
    (adjoin_inverse_eq (F := F) f).symm ▸ inferInstance
  let := parameterChartFractionRing f⁻¹ (transcendental_inverse f hf)
  unfold parameterCurveGenericPoint
  rw [parameterCurveFunctionFieldEquiv_eq_infinity]
  change Spec.map (functionFieldRestriction (infinityChartInclusion f hf) ≫
      CommRingCat.ofHom
        (affineFunctionFieldEquiv (parameterChart f⁻¹ (transcendental_inverse f hf)) E).toRingHom) ≫
      (parameterCurve f hf).fromSpecStalk (genericPoint (parameterCurve f hf)) = _
  let i := infinityChartInclusion f hf
  let e := Spec.map (CommRingCat.ofHom
    (affineFunctionFieldEquiv (parameterChart f⁻¹ (transcendental_inverse f hf)) E).toRingHom)
  let r := Spec.map (functionFieldRestriction i)
  let q := (parameterCurve f hf).fromSpecStalk (genericPoint (parameterCurve f hf))
  have hmap := congrArg (fun k => k ≫ q)
    (Spec.map_comp (functionFieldRestriction i) (CommRingCat.ofHom
      (affineFunctionFieldEquiv (parameterChart f⁻¹ (transcendental_inverse f hf)) E).toRingHom))
  have hrestrict := congrArg (fun k => e ≫ k) (functionFieldRestriction_fromSpecStalk i)
  have haffine := congrArg (fun k => k ≫ i)
    (affineFunctionFieldEquiv_fromSpecStalk (parameterChart f⁻¹ (transcendental_inverse f hf)) E)
  have hassoc := Category.assoc e
    ((Spec (.of (parameterChart f⁻¹ (transcendental_inverse f hf)))).fromSpecStalk
      (genericPoint (Spec (.of (parameterChart f⁻¹ (transcendental_inverse f hf)))))) i
  exact hmap.trans ((Category.assoc e r q).trans
    (hrestrict.trans (hassoc.symm.trans haffine)))

end PiExponent.CurveNormalizationModel

end

end OAI
end Source0372

-- Source: OAI/NumberTheory/PiExponent/Geometry/CurvePlaceCenter.lean
section Source0373
-- Modified in this edition: unused plain lemmas removed; see reduction.json.
/-
Modification notice for the LogTwo project.
Derived from openai/math (Apache-2.0), revision adc7f1241b42e322a6451854ab7e4b4c146bf78a.
Original source: lean/OAI/NumberTheory/PiExponent/Geometry/CurvePlaceCenter.lean
Changes: Convert module/import declarations to the Lean 4.34 public module format.
See ../THIRD_PARTY_NOTICES.txt for provenance and the recorded changes.
-/

namespace OAI

noncomputable section
universe u
namespace PiExponent.CurvePlaceCenter
open AlgebraicGeometry CategoryTheory
open CurveZeroPole CurveValuationCenter CurveNormalizationModel CurveModelPlaces

theorem fractionSpec_isDominant
    (A E : Type u) [CommRing A] [IsDomain A] [Field E] [Algebra A E] [IsFractionRing A E] :
    IsDominant (Spec.map (CommRingCat.ofHom (algebraMap A E))) := by
  constructor
  rw [denseRange_iff_closure_range]
  apply Set.eq_univ_of_univ_subset
  rw [← genericPoint_closure (Spec (CommRingCat.of A))]
  apply closure_mono
  rw [Set.singleton_subset_iff]
  refine ⟨(⊥ : PrimeSpectrum E), ?_⟩
  rw [genericPoint_eq_bot_of_affine]
  apply PrimeSpectrum.ext
  ext a
  change algebraMap A E a = 0 ↔ a = 0
  exact map_eq_zero_iff _ (IsFractionRing.injective A E)

theorem hom_ext_fraction
    (A E : Type u) [CommRing A] [IsDomain A] [Field E] [Algebra A E] [IsFractionRing A E]
    {Y : Scheme.{u}} [Y.IsSeparated] (g h : Spec (CommRingCat.of A) ⟶ Y)
    (heq : Spec.map (CommRingCat.ofHom (algebraMap A E)) ≫ g =
      Spec.map (CommRingCat.ofHom (algebraMap A E)) ≫ h) : g = h := by
  let := fractionSpec_isDominant A E
  exact ext_of_isDominant (Spec.map (CommRingCat.ofHom (algebraMap A E))) heq

def centerMorphism
    {F E : Type u} [Field F] [Field E] [Algebra F E]
    (f : E) (hf : Transcendental F f) (p : NormalizedPlace F E) :
    Spec (CommRingCat.of (PlaceValuationRing.ring p)) ⟶ parameterCurve f hf :=
  if hp : 0 ≤ p.valuation f then
    Spec.map (CommRingCat.ofHom (parameterChartValuationHom f hf p.valuation p.constants_nonneg hp)) ≫
      zeroChartInclusion f hf
  else
    Spec.map (CommRingCat.ofHom (parameterChartValuationHom f⁻¹ (transcendental_inverse f hf)
      p.valuation p.constants_nonneg (inverse_positive_of_not_regular p f hf.ne_zero hp).le)) ≫
      infinityChartInclusion f hf

theorem centerMorphism_closedPoint
    {F E : Type u} [Field F] [Field E] [Algebra F E]
    (f : E) (hf : Transcendental F f) (p : NormalizedPlace F E) :
    centerMorphism f hf p (IsLocalRing.closedPoint (PlaceValuationRing.ring p)) =
      placePoint f hf p := by
  by_cases hp : 0 ≤ p.valuation f
  · simp only [centerMorphism, placePoint, dite_eq_left hp]
    rfl
  · simp only [centerMorphism, placePoint, dite_eq_right hp]
    rfl

theorem centerMorphism_generic_of_regular
    {F E : Type u} [Field F] [Field E] [Algebra F E]
    (f : E) (hf : Transcendental F f)
    [FiniteDimensional (IntermediateField.adjoin F {f}) E]
    (p : NormalizedPlace F E) (hp : 0 ≤ p.valuation f) :
    Spec.map (CommRingCat.ofHom (algebraMap (PlaceValuationRing.ring p) E)) ≫
      centerMorphism f hf p = parameterCurveGenericPoint f hf := by
  rw [centerMorphism, dite_eq_left hp, ← Category.assoc, ← Spec.map_comp,
    ← CommRingCat.ofHom_comp, parameterCurveGenericPoint_eq_zeroChart]
  rfl

theorem centerMorphism_generic
    {F E : Type u} [Field F] [Field E] [Algebra F E]
    (f : E) (hf : Transcendental F f)
    [FiniteDimensional (IntermediateField.adjoin F {f}) E]
    (p : NormalizedPlace F E) :
    Spec.map (CommRingCat.ofHom (algebraMap (PlaceValuationRing.ring p) E)) ≫
      centerMorphism f hf p = parameterCurveGenericPoint f hf := by
  by_cases hp : 0 ≤ p.valuation f
  · exact centerMorphism_generic_of_regular f hf p hp
  · rw [centerMorphism, dite_eq_right hp, ← Category.assoc, ← Spec.map_comp,
      ← CommRingCat.ofHom_comp, parameterCurveGenericPoint_eq_infinityChart]
    rfl

theorem centerMorphism_comp_eq_of_generic
    {F E : Type u} [Field F] [Field E] [Algebra F E]
    (f : E) (hf : Transcendental F f)
    [FiniteDimensional (IntermediateField.adjoin F {f}) E]
    (p : NormalizedPlace F E) {Y : Scheme.{u}} [Y.IsSeparated]
    (g : parameterCurve f hf ⟶ Y)
    (φ : Spec (CommRingCat.of (PlaceValuationRing.ring p)) ⟶ Y)
    (hφ : Spec.map (CommRingCat.ofHom (algebraMap (PlaceValuationRing.ring p) E)) ≫ φ =
      parameterCurveGenericPoint f hf ≫ g) : centerMorphism f hf p ≫ g = φ := by
  apply hom_ext_fraction (PlaceValuationRing.ring p) E
  rw [← Category.assoc, centerMorphism_generic]
  exact hφ.symm

end PiExponent.CurvePlaceCenter

end

end OAI
end Source0373

-- Source: OAI/NumberTheory/PiExponent/Geometry/CurvePlaceCenterStalk.lean
section Source0374
/-
Modification notice for the LogTwo project.
Derived from openai/math (Apache-2.0), revision adc7f1241b42e322a6451854ab7e4b4c146bf78a.
Original source: lean/OAI/NumberTheory/PiExponent/Geometry/CurvePlaceCenterStalk.lean
Changes: Convert module/import declarations to the Lean 4.34 public module format.
See ../THIRD_PARTY_NOTICES.txt for provenance and the recorded changes.
-/

namespace OAI

noncomputable section
namespace PiExponent.CurvePlaceCenter
open CategoryTheory AlgebraicGeometry
open CurveZeroPole CurveValuationCenter CurveNormalizationModel CurveModelPlaces
universe u
variable {F E : Type u} [Field F] [CharZero F] [Field E] [Algebra F E]
variable (f : E) (hf : Transcendental F f)
variable [FiniteDimensional (IntermediateField.adjoin F {f}) E]
variable (p : NormalizedPlace F E)

instance centerMorphism_stalkMap_isIso :
    IsIso ((centerMorphism f hf p).stalkMap (IsLocalRing.closedPoint (PlaceValuationRing.ring p))) := by
  have hx : centerMorphism f hf p (IsLocalRing.closedPoint (PlaceValuationRing.ring p)) ≠
      genericPoint (parameterCurve f hf) := by
    rw [centerMorphism_closedPoint]
    exact placePoint_ne_genericPoint f hf p
  let := parameterCurve_stalkDVR f hf _ hx
  exact BirationalValuationStalk.stalkMap_isIso (centerMorphism f hf p)
    (parameterCurveFunctionFieldEquiv f hf) (centerMorphism_generic f hf p)

instance centerMorphism_stalkClosedPointTo_isIso :
    IsIso (Scheme.stalkClosedPointTo (centerMorphism f hf p)) := by
  unfold Scheme.stalkClosedPointTo
  infer_instance

def centerStalkIso :
    (parameterCurve f hf).presheaf.stalk (placePoint f hf p) ≅
      CommRingCat.of (PlaceValuationRing.ring p) :=
  (parameterCurve f hf).presheaf.stalkCongr
      (.of_eq (centerMorphism_closedPoint f hf p).symm) ≪≫
    asIso (Scheme.stalkClosedPointTo (centerMorphism f hf p))

@[reassoc]
theorem centerStalkIso_hom_eq :
    (centerStalkIso f hf p).hom =
      ((parameterCurve f hf).presheaf.stalkCongr
        (.of_eq (centerMorphism_closedPoint f hf p).symm)).hom ≫
      (centerMorphism f hf p).stalkMap (IsLocalRing.closedPoint (PlaceValuationRing.ring p)) ≫
      (stalkClosedPointIso (.of (PlaceValuationRing.ring p))).hom := rfl

omit [CharZero F] in
theorem centerMorphism_stalkClosedPointTo_field :
    (algebraMap (PlaceValuationRing.ring p) E).comp
        (Scheme.stalkClosedPointTo (centerMorphism f hf p)).hom =
      (parameterCurveFunctionFieldEquiv f hf).toRingHom.comp
        (algebraMap ((parameterCurve f hf).presheaf.stalk
          (centerMorphism f hf p (IsLocalRing.closedPoint (PlaceValuationRing.ring p))))
          (parameterCurve f hf).functionField) :=
  BirationalValuationStalk.stalkClosedPointTo_field_compatibility (centerMorphism f hf p)
    (parameterCurveFunctionFieldEquiv f hf) (centerMorphism_generic f hf p)

end PiExponent.CurvePlaceCenter

end

end OAI
end Source0374

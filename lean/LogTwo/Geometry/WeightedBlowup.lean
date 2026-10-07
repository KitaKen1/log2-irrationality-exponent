/-
Modification notice for the LogTwo project.
Adapted from openai/math (Apache-2.0), revision adc7f1241b42e322a6451854ab7e4b4c146bf78a.
Changes: Adapt the blowup construction to the varying-center ideal.
See ../../../THIRD_PARTY_NOTICES.txt for provenance and the recorded changes.
-/

module

public import LogTwo.Geometry.CurveSectionDegree
public import OAI.NumberTheory.PiExponent.Ampleness.BlowupProperIntegral
public import OAI.NumberTheory.PiExponent.Ampleness.WeightedProjectiveAmple

@[expose] public section

/-! The actual blowup of the varying-center ideal, its exceptional line
bundle and the verified presentation of the pulled-back ideal. The ambient
hyperplane is ample; ampleness of a line bundle on the blowup is not asserted.
Construction adapted from openai/math Ampleness/AdmissibleBlowupGeometry.lean
(Apache-2.0), using only its scheme-generic APIs. -/
namespace LogTwo.Geometry.MatrixBlowup
open OAI PiExponent AlgebraicGeometry CategoryTheory TopologicalSpace
open PiExponentSeshadri.Geometry PiExponentSeshadri.Frames
open LogTwo.Interpolation LogTwo.Arithmetic
open CurveNormalizationModel CurveValuationCenter PlaceValuationRing
noncomputable section
variable {m : ℕ} (w : Weights m)

def hyperplane : LineBundle (MatrixCompactification.space w) :=
  WeightedCompactification.lineBundle (MatrixCompactification.exponents w)

theorem hyperplane_ample : (hyperplane w).IsAmple :=
  WeightedCompactification.lineBundle_ample _

variable {K : ℕ} (y : Fin K → ℂ) (c : Fin K → Fin m → ℂ) (T : Fin m → ℕ)
abbrev space : Scheme :=
  PiExponentSeshadri.BlowupGluing.scheme (MatrixCompactification.centerIdeal w y c T)
abbrev projection : space w y c T ⟶ MatrixCompactification.space w :=
  PiExponentSeshadri.BlowupGluing.projection (MatrixCompactification.centerIdeal w y c T)
def structureMap : space w y c T ⟶ Spec (.of ℂ) :=
  projection w y c T ≫ MatrixCompactification.structureMap w

instance projection_proper : IsProper (projection w y c T) := by infer_instance
instance structureMap_proper : IsProper (structureMap w y c T) := by
  dsimp [structureMap]
  infer_instance

theorem space_isIntegral (hy0 : ∀ j, y j ≠ 0) : IsIntegral (space w y c T) :=
  PiExponentSeshadri.BlowupGluing.scheme_isIntegral _
    (MatrixCompactification.centerIdeal_support_ne_top w y hy0 c T)

instance space_isLocallyNoetherian : IsLocallyNoetherian (space w y c T) :=
  LocallyOfFiniteType.isLocallyNoetherian (structureMap w y c T)
instance space_compact : CompactSpace (space w y c T) :=
  QuasiCompact.compactSpace_of_compactSpace (structureMap w y c T)
instance space_isNoetherian : IsNoetherian (space w y c T) := {}

def A : LineBundle (space w y c T) := (hyperplane w).pullback (projection w y c T)
abbrev J : LineBundle (space w y c T) :=
  PiExponentSeshadri.BlowupGluing.exceptionalLineBundle (MatrixCompactification.centerIdeal w y c T)
abbrev exceptionalInclusion : (J w y c T).sheaf ⟶ O (space w y c T) :=
  PiExponentSeshadri.BlowupGluing.exceptionalInclusion (MatrixCompactification.centerIdeal w y c T)

theorem exceptional_presents :
    PresentsPullbackIdeal (MatrixCompactification.centerIdeal w y c T)
      (projection w y c T) (J w y c T) (exceptionalInclusion w y c T) :=
  PiExponentSeshadri.BlowupGluing.exceptional_presents _

theorem isBlowup :
    IsBlowup (MatrixCompactification.centerIdeal w y c T) (projection w y c T) :=
  PiExponentSeshadri.BlowupGluing.isBlowup _

variable {E : Type} [Field E] [Algebra ℂ E]
variable (f : E) (hf : Transcendental ℂ f)
variable [FiniteDimensional (IntermediateField.adjoin ℂ {f}) E]
variable (hfinite : ∀ t : E, Transcendental ℂ t →
  FiniteDimensional (IntermediateField.adjoin ℂ {t}) E)
variable (z : Fin (m+1) → E) (hz : ∃ i, Transcendental ℂ (z i))
variable (hres : ∀ p : NormalizedPlace ℂ E,
  Algebra.IsIntegral ℂ (IsLocalRing.ResidueField (ring p)))
variable (hy : Function.Injective y) (hy0 : ∀ j, y j ≠ 0) (hK : 0 < K)

include hy in
/-- The presentation is now constructed, not supplied as a theorem argument. -/
theorem exceptional_degree_eq_neg_contact_sum (F : ℚ) (hF : 1 / w.theta < F)
    (g : parameterCurve f hf ⟶ space w y c (truncationOrders w F))
    (hgeneric : parameterCurveGenericPoint f hf ≫ g ≫
        projection w y c (truncationOrders w F) =
      Spec.map (CommRingCat.ofHom (MvPolynomial.aeval z).toRingHom) ≫
        MatrixCompactification.affineChart w) :
    ((eulerCharacteristic (parameterCurveStructureMap f hf) 1
        ((J w y c (truncationOrders w F)).pullback g).sheaf -
      eulerCharacteristic (parameterCurveStructureMap f hf) 1
        (structureSheaf (parameterCurve f hf)) : ℤ) : ℚ) =
      -((MatrixCompactification.scale w).radius : ℚ) *
        ∑ p ∈ ContactFamilyAt.places hfinite z y c hz,
          ContactFamilyAt.contact hres hfinite z y hy0 c hz hK (jetWeight w) p := by
  exact MatrixCompactification.euler_degree_eq_neg_contact_sum w f hf hfinite z y c hz
    (projection w y c (truncationOrders w F)) (J w y c (truncationOrders w F))
    (exceptionalInclusion w y c (truncationOrders w F)) g hgeneric hres hy hy0 hK F hF
    (exceptional_presents w y c (truncationOrders w F))

end
end LogTwo.Geometry.MatrixBlowup

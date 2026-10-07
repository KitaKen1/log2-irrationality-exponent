/-
Modification notice for the LogTwo project.
Adapted from openai/math (Apache-2.0), revision adc7f1241b42e322a6451854ab7e4b4c146bf78a.
Changes: Adapt the compactification to rational matrix weights and varying Y-centers.
See ../../../THIRD_PARTY_NOTICES.txt for provenance and the recorded changes.
-/

module

public import LogTwo.Geometry.GeometricParameters
public import LogTwo.Geometry.IntegralProj
public import LogTwo.Geometry.JetIdealAt
public import OAI.NumberTheory.PiExponent.Approximation.WeightedGeometryScale
public import OAI.NumberTheory.PiExponent.Geometry.CurveMonomialMap

@[expose] public section

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

theorem affineChart_denseRange : DenseRange (affineChart w) :=
  WeightedCompactification.affineChartMap_denseRange (exponents w) (constantIndex w)
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

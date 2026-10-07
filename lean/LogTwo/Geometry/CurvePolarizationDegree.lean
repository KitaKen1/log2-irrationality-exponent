module

public import LogTwo.Geometry.WeightedBlowup
public import OAI.NumberTheory.PiExponent.Geometry.WeightedProjectiveCurveDegree

@[expose] public section

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

theorem curveMap_hyperplane_degree :
    ((eulerCharacteristic (parameterCurveStructureMap f hf) 1
        ((hyperplane w).pullback (MatrixCompactification.curveMap w f hf z)).sheaf -
      eulerCharacteristic (parameterCurveStructureMap f hf) 1
        (structureSheaf (parameterCurve f hf)) : ℤ) : ℝ) =
      (MatrixCompactification.scale w).radius *
        CurveContactSum.weightedDegree hfinite z (rationalColumnWeight w) :=
  hyperplane_degree_eq_weightedDegree w f hf hfinite z _
    (MatrixCompactification.curveMap_generic w f hf z)

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

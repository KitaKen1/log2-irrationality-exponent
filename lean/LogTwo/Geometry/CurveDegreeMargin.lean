/-
Modification notice for the LogTwo project.
Adapted from openai/math (Apache-2.0), revision adc7f1241b42e322a6451854ab7e4b4c146bf78a.
Changes: Adapt the degree/contact combination to the intrinsic curve bound.
See ../../../THIRD_PARTY_NOTICES.txt for provenance and the recorded changes.
-/

module

public import LogTwo.Geometry.CurvePolarizationDegree
public import LogTwo.Geometry.IntrinsicContactBound

@[expose] public section

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

/-- Specialize the degree inequality to the original matrix centers. -/
theorem logTwo_degree_nonnegative
    (n : ℕ) (hn : 1 ≤ n) (m : ℕ) (q : ℕ → ℕ) (hq : ∀ i, 2 ≤ q i)
    (hgrowth : ∀ i, i < m →
      denominatorSeparationFactor n m (chosenComparisonConstant n m) *
        (∏ j : Fin i, (ceilLogWeight (q j) : ℝ)) < (ceilLogWeight (q i) : ℝ))
    (z : Fin (m+1) → E)
    (hgen : IntermediateField.adjoin ℂ (Set.range z) = ⊤)
    (htrdeg : Algebra.trdeg ℂ E = 1) (r : Fin m → ℚ) :
    let w := chosenWeights n hn m (fun i => q i) (fun i => hq i)
    let y : Fin w.K → ℂ := fun j => 2^j.val
    let c : Fin w.K → Fin m → ℂ := fun j i => (j.val : ℂ) * (r i : ℂ)
    ∀ (F : ℚ), 1 / w.theta < F →
      ∀ (g : parameterCurve f hf ⟶ space w y c (truncationOrders w F)),
      parameterCurveGenericPoint f hf ≫ g ≫ projection w y c (truncationOrders w F) =
        Spec.map (CommRingCat.ofHom (MvPolynomial.aeval z).toRingHom) ≫
          MatrixCompactification.affineChart w →
      0 ≤ normalizationDegree f hf g (A w y c (truncationOrders w F)) +
        (1 + (curveSigma w.theta m : ℝ)) *
          normalizationDegree f hf g (J w y c (truncationOrders w F)) := by
  dsimp only
  exact chosenWeights_degree_nonnegative f hf n hn m q hq hgrowth z hgen htrdeg
    (fun j => 2^j.val) (fun j => pow_ne_zero j.val (by norm_num))
    (complex_centerY_injective.comp Fin.val_injective) (fun j i => (j.val : ℂ) * (r i : ℂ))

end
end LogTwo.Geometry.MatrixBlowup

/-
Modification notice for the LogTwo project.
Adapted from openai/math (Apache-2.0), revision adc7f1241b42e322a6451854ab7e4b4c146bf78a.
Changes: Connect varying-center colength cycles and adapt the rational degree-cast calculation.
See ../../../THIRD_PARTY_NOTICES.txt for provenance and the recorded changes.
-/

module

public import LogTwo.Geometry.CurveIdealSupport
public import LogTwo.Geometry.SectionIdealBridge

@[expose] public section

/-! Identify the actual colength cycle with a section divisor, then obtain
its negative Euler degree for an invertible presentation of the pulled-back
ideal. The presentation is an explicit hypothesis; this module does not
construct a blowup or prove ampleness. -/
namespace LogTwo.Geometry.MatrixCompactification
open OAI PiExponent AlgebraicGeometry CategoryTheory TopologicalSpace
open PiExponentSeshadri.Geometry PiExponentSeshadri.Frames
open LogTwo.Interpolation LogTwo.Arithmetic
open CurveNormalizationModel CurvePlaceCenter CurveValuationCenter PlaceValuationRing
open SectionIdealBridge
noncomputable section
variable {m : ℕ} (w : Weights m)
variable {E : Type} [Field E] [Algebra ℂ E]
variable (f : E) (hf : Transcendental ℂ f)
variable [FiniteDimensional (IntermediateField.adjoin ℂ {f}) E]

/-- The generic-point morphism is dominant, so equality there determines
maps from the reduced normalization curve to a separated target. -/
theorem parameterCurveGenericPoint_isDominant :
    IsDominant (parameterCurveGenericPoint f hf) := by
  let X := parameterCurve f hf
  let q := X.fromSpecStalk (genericPoint X)
  have : IsDominant q := by
    constructor
    rw [denseRange_iff_closure_range]
    apply Set.eq_univ_of_univ_subset
    rw [← genericPoint_closure X]
    apply closure_mono
    rw [Set.singleton_subset_iff]
    exact ⟨IsLocalRing.closedPoint _, Scheme.fromSpecStalk_closedPoint⟩
  let e : Spec (CommRingCat.of E) ≅ Spec X.functionField :=
    Scheme.Spec.mapIso (parameterCurveFunctionFieldEquiv f hf).toCommRingCatIso.op
  change IsDominant (e.hom ≫ q)
  infer_instance

theorem curveMap_eq_of_generic (z : Fin (m+1) → E)
    (g : parameterCurve f hf ⟶ space w)
    (hgeneric : parameterCurveGenericPoint f hf ≫ g =
      Spec.map (CommRingCat.ofHom (MvPolynomial.aeval z).toRingHom) ≫ affineChart w) :
    g = curveMap w f hf z := by
  let := parameterCurveGenericPoint_isDominant f hf
  apply ext_of_isDominant (parameterCurveGenericPoint f hf)
  rw [hgeneric, curveMap_generic]

variable {K : ℕ}
variable (hfinite : ∀ t : E, Transcendental ℂ t →
  FiniteDimensional (IntermediateField.adjoin ℂ {t}) E)
variable (z : Fin (m+1) → E) (y : Fin K → ℂ) (c : Fin K → Fin m → ℂ)
variable (hz : ∃ i, Transcendental ℂ (z i))
variable {Y : Scheme.{0}} (π : Y ⟶ space w)
variable (J : LineBundle Y) (ι : J.sheaf ⟶ O Y)
variable (g : parameterCurve f hf ⟶ Y)
variable (hgeneric : parameterCurveGenericPoint f hf ≫ g ≫ π =
  Spec.map (CommRingCat.ofHom (MvPolynomial.aeval z).toRingHom) ≫ affineChart w)

include hz hgeneric in
theorem presented_curveIdeal_ne_bot (T : Fin m → ℕ) :
    (centerIdeal w y c T).comap (g ≫ π) ≠ ⊥ := by
  rw [curveMap_eq_of_generic w f hf z (g ≫ π) hgeneric]
  exact curveIdeal_ne_bot w f hf y c T z hz

theorem presentedDivisor_eq_curveColengthCycle (T : Fin m → ℕ)
    (hJ : PresentsPullbackIdeal (centerIdeal w y c T) π J ι) :
    idealDivisor f hf (centerIdeal w y c T) π J ι hJ g
      (presented_curveIdeal_ne_bot w f hf z y c hz π g hgeneric T) =
        curveColengthCycle w f hf hfinite z y c hz T := by
  ext p
  rw [idealDivisor_apply, curveColengthCycle_apply]
  have hi : localIdeal (centerIdeal w y c T) (centerMorphism f hf p ≫ g ≫ π) =
      curveLocalIdeal w f hf p y c z T := by
    unfold localIdeal curveLocalIdeal
    rw [Scheme.IdealSheafData.comap_comp,
      curveMap_eq_of_generic w f hf z (g ≫ π) hgeneric]
  rw [hi]

include hgeneric in
theorem euler_degree_eq_neg_curveColengthCycle_sum (T : Fin m → ℕ)
    (hJ : PresentsPullbackIdeal (centerIdeal w y c T) π J ι) :
    eulerCharacteristic (parameterCurveStructureMap f hf) 1 (J.pullback g).sheaf -
      eulerCharacteristic (parameterCurveStructureMap f hf) 1
        (structureSheaf (parameterCurve f hf)) =
      -(curveColengthCycle w f hf hfinite z y c hz T).sum (fun _ n => (n : ℤ)) := by
  have hd := degree_eq_neg_idealDivisor_sum f hf (centerIdeal w y c T) π J ι hJ g
    (presented_curveIdeal_ne_bot w f hf z y c hz π g hgeneric T)
  rw [presentedDivisor_eq_curveColengthCycle w f hf hfinite z y c hz π J ι g hgeneric T hJ] at hd
  exact hd

variable (hres : ∀ p : NormalizedPlace ℂ E,
  Algebra.IsIntegral ℂ (IsLocalRing.ResidueField (ring p)))
variable (hy : Function.Injective y) (hy0 : ∀ j, y j ≠ 0) (hK : 0 < K)

include hy hgeneric in
theorem euler_degree_eq_neg_contact_sum (F : ℚ) (hF : 1 / w.theta < F)
    (hJ : PresentsPullbackIdeal (centerIdeal w y c (truncationOrders w F)) π J ι) :
    ((eulerCharacteristic (parameterCurveStructureMap f hf) 1 (J.pullback g).sheaf -
      eulerCharacteristic (parameterCurveStructureMap f hf) 1
        (structureSheaf (parameterCurve f hf)) : ℤ) : ℚ) =
      -((scale w).radius : ℚ) * ∑ p ∈ ContactFamilyAt.places hfinite z y c hz,
        ContactFamilyAt.contact hres hfinite z y hy0 c hz hK (jetWeight w) p := by
  have hd := euler_degree_eq_neg_curveColengthCycle_sum w f hf hfinite z y c hz π J ι g
    hgeneric (truncationOrders w F) hJ
  have hdq : ((eulerCharacteristic (parameterCurveStructureMap f hf) 1 (J.pullback g).sheaf -
      eulerCharacteristic (parameterCurveStructureMap f hf) 1
        (structureSheaf (parameterCurve f hf)) : ℤ) : ℚ) =
      -(curveColengthCycle w f hf hfinite z y c hz (truncationOrders w F)).sum
        (fun _ n => (n : ℚ)) := by
    simpa only [Int.cast_neg, Finsupp.sum, Int.cast_sum, Int.cast_natCast] using
      congrArg (fun a : ℤ => (a : ℚ)) hd
  rw [curveColengthCycle_sum_eq_contact w f hf hfinite z y c hz hres hy hy0 hK F hF] at hdq
  simpa only [neg_mul] using hdq

end
end LogTwo.Geometry.MatrixCompactification

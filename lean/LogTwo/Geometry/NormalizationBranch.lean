/-
Modification notice for the LogTwo project.
Adapted from openai/math (Apache-2.0), revision adc7f1241b42e322a6451854ab7e4b4c146bf78a.
Changes: Adapt centered-map uniqueness to the constructed weighted compactification.
See ../../../THIRD_PARTY_NOTICES.txt for provenance and the recorded changes.
-/

module

public import LogTwo.Geometry.WeightedJetIdeal
public import OAI.NumberTheory.PiExponent.Geometry.CurveGlobalMonomial
public import OAI.NumberTheory.PiExponent.Geometry.CurvePlaceCenterStalk

@[expose] public section

/-! Extend the coordinate map to the normalization curve, then identify its
actual DVR pullback with the previously verified varying-center branch.
The extension is constructed by properness and gluing; it is not an input.
The contact formula still requires the stated centered, nonconstant branch
and residue-integrality hypotheses. Divisor degrees are a separate step.
The uniqueness argument follows openai/math ExceptionalCurveDegree.lean
(Apache-2.0); see THIRD_PARTY_NOTICES.txt. -/
namespace LogTwo.Geometry.MatrixCompactification
open OAI PiExponent AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open LogTwo.Interpolation LogTwo.Arithmetic
open CurveValuationCenter PlaceValuationRing PlaceCenteredBranch CurveCenters
open CurveNormalizationModel CurvePlaceCenter
noncomputable section
variable {m : ℕ} (w : Weights m)

instance space_isSeparated : (space w).IsSeparated := by
  constructor
  rw [← terminal.comp_from (structureMap w)]
  infer_instance

variable {E : Type} [Field E] [Algebra ℂ E]
variable (f : E) (hf : Transcendental ℂ f)
variable [FiniteDimensional (IntermediateField.adjoin ℂ {f}) E]

theorem exists_curveMap (z : Fin (m+1) → E) :
    ∃ g : parameterCurve f hf ⟶ space w,
      g ≫ structureMap w = parameterCurveStructureMap f hf ∧
      parameterCurveGenericPoint f hf ≫ g =
        Spec.map (CommRingCat.ofHom (MvPolynomial.aeval z).toRingHom) ≫ affineChart w := by
  apply CurveGlobalMonomial.exists_parameterCurve_extension f hf (structureMap w)
  rw [Category.assoc, affineChart_over, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
  apply congrArg Spec.map
  apply CommRingCat.hom_ext
  ext a
  simp

def curveMap (z : Fin (m+1) → E) : parameterCurve f hf ⟶ space w :=
  (exists_curveMap w f hf z).choose

theorem curveMap_over (z : Fin (m+1) → E) :
    curveMap w f hf z ≫ structureMap w = parameterCurveStructureMap f hf :=
  (exists_curveMap w f hf z).choose_spec.1

theorem curveMap_generic (z : Fin (m+1) → E) :
    parameterCurveGenericPoint f hf ≫ curveMap w f hf z =
      Spec.map (CommRingCat.ofHom (MvPolynomial.aeval z).toRingHom) ≫ affineChart w :=
  (exists_curveMap w f hf z).choose_spec.2

variable (p : NormalizedPlace ℂ E)

theorem curveMap_center {J : Type*} (y : J → ℂ) (c : J → Fin m → ℂ)
    (z : Fin (m+1) → E) (j : J) (hc : Centered z (centerPoint (y j) (c j)) p) :
    centerMorphism f hf p ≫ curveMap w f hf z = branchMap w p y c z j hc := by
  apply centerMorphism_comp_eq_of_generic f hf p
  rw [branchMap_generic, curveMap_generic]

/-- The normalization stalk map used below is an isomorphism onto the DVR. -/
instance curve_center_stalk_isIso :
    IsIso (Scheme.stalkClosedPointTo (centerMorphism f hf p)) := inferInstance

theorem curveMap_stalk {J : Type*} (y : J → ℂ) (c : J → Fin m → ℂ)
    (z : Fin (m+1) → E) (j : J) (hc : Centered z (centerPoint (y j) (c j)) p) :
    Spec.map (Scheme.stalkClosedPointTo (centerMorphism f hf p)) ≫
      (parameterCurve f hf).fromSpecStalk
        (centerMorphism f hf p (IsLocalRing.closedPoint (ring p))) ≫
      curveMap w f hf z = branchMap w p y c z j hc := by
  rw [← Category.assoc, Scheme.Spec_stalkClosedPointTo_fromSpecStalk]
  exact curveMap_center w f hf p y c z j hc

theorem curveIdeal_center_pullback {J : Type*} [Fintype J]
    (y : J → ℂ) (c : J → Fin m → ℂ) (z : Fin (m+1) → E)
    (j : J) (hc : Centered z (centerPoint (y j) (c j)) p) (T : Fin m → ℕ) :
    ((centerIdeal w y c T).comap (curveMap w f hf z)).comap
      (centerMorphism f hf p) =
      PiExponentSeshadri.IdealPullback.specIdeal
        (localJetProductIdeal p y c z j hc T (scale w).jetPowers) := by
  rw [← Scheme.IdealSheafData.comap_comp, curveMap_center w f hf p y c z j hc]
  exact centerIdeal_branch_pullback w p y c z j hc T

/-- Pull back the actual global curve ideal to the DVR and express it using
the canonical affine section-ring isomorphism. No branch choice is an input. -/
def curveLocalIdeal {J : Type*} [Fintype J]
    (y : J → ℂ) (c : J → Fin m → ℂ) (z : Fin (m+1) → E) (T : Fin m → ℕ) :
    Ideal (ring p) :=
  ((((centerIdeal w y c T).comap (curveMap w f hf z)).comap
    (centerMorphism f hf p)).ideal ⟨⊤, isAffineOpen_top _⟩).map
      (Scheme.ΓSpecIso (CommRingCat.of (ring p))).hom.hom

theorem curveLocalIdeal_eq_branchIdeal {J : Type*} [Fintype J]
    (y : J → ℂ) (c : J → Fin m → ℂ) (z : Fin (m+1) → E)
    (j : J) (hc : Centered z (centerPoint (y j) (c j)) p) (T : Fin m → ℕ) :
    curveLocalIdeal w f hf p y c z T = branchIdeal w p y c z j hc T := by
  rw [curveLocalIdeal, ← Scheme.IdealSheafData.comap_comp,
    curveMap_center w f hf p y c z j hc]
  rfl

variable [Algebra.IsIntegral ℂ (IsLocalRing.ResidueField (ring p))]

theorem curveLocalIdeal_colength_eq_contact {J : Type*} [Fintype J]
    (y : J → ℂ) (hy : Function.Injective y) (hy0 : ∀ j, y j ≠ 0)
    (c : J → Fin m → ℂ) (z : Fin (m+1) → E) (j : J)
    (hc : Centered z (centerPoint (y j) (c j)) p)
    (hnc : ∃ i, z i ≠ algebraMap ℂ E (centerPoint (y j) (c j) i))
    (F : ℚ) (hF : 1 / w.theta < F) :
    ((Module.length (ring p) ((ring p) ⧸
      curveLocalIdeal w f hf p y c z (truncationOrders w F))).toNat : ℚ) =
      (scale w).radius * logContactAt p (y j) (hy0 j) z (c j) hc hnc (jetWeight w) := by
  rw [curveLocalIdeal_eq_branchIdeal w f hf p y c z j hc]
  exact branch_colength_eq_contact w p y hy hy0 c z j hc hnc F hF

theorem curveLocalIdeal_colength_ne_top {J : Type*} [Fintype J]
    (y : J → ℂ) (hy : Function.Injective y) (hy0 : ∀ j, y j ≠ 0)
    (c : J → Fin m → ℂ) (z : Fin (m+1) → E) (j : J)
    (hc : Centered z (centerPoint (y j) (c j)) p)
    (hnc : ∃ i, z i ≠ algebraMap ℂ E (centerPoint (y j) (c j) i))
    (F : ℚ) (hF : 1 / w.theta < F) :
    Module.length (ring p) ((ring p) ⧸
      curveLocalIdeal w f hf p y c z (truncationOrders w F)) ≠ ⊤ := by
  rw [curveLocalIdeal_eq_branchIdeal w f hf p y c z j hc]
  exact branch_colength_ne_top w p y hy hy0 c z j hc hnc F hF

end
end LogTwo.Geometry.MatrixCompactification

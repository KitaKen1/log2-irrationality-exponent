/-
Modification notice for the LogTwo project.
Adapted from openai/math (Apache-2.0), revision adc7f1241b42e322a6451854ab7e4b4c146bf78a.
Changes: Adapt the curve-image construction to the varying-center blowup.
See ../../../THIRD_PARTY_NOTICES.txt for provenance and the recorded changes.
-/

module

public import LogTwo.Geometry.WeightedBlowup
public import OAI.NumberTheory.PiExponent.Ampleness.CurveBlowupImage

@[expose] public section

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

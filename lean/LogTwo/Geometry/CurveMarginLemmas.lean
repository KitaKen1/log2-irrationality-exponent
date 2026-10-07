/-
Modification notice for the LogTwo project.
Adapted from openai/math (Apache-2.0), revision adc7f1241b42e322a6451854ab7e4b4c146bf78a.
Changes: Extract generic degree-margin arguments and omit the fixed-center contact bound.
See ../../../THIRD_PARTY_NOTICES.txt for provenance and the recorded changes.
-/

module

public import OAI.NumberTheory.PiExponent.Ampleness.AmpleCurveDegreePositive
public import OAI.NumberTheory.PiExponent.Ampleness.NefAmple
public import OAI.NumberTheory.PiExponent.Approximation.ConstantPullbackDegree
public import OAI.NumberTheory.PiExponent.LocalAlgebra.InvertibleIdealAway

@[expose] public section

/-! Scheme-generic degree laws and the three curve cases, adapted from the
first part of openai/math Ampleness/BlowupCurveMargin.lean (Apache-2.0).
The fixed-Y contact inequality and its import are deliberately not included. -/
namespace LogTwo.Geometry.CurveMarginLemmas
noncomputable section
open OAI PiExponent AlgebraicGeometry CategoryTheory
open PiExponentSeshadri.Geometry NumericalAmpleness
variable {B X : Scheme.{0}}

theorem curve_degree_laws (p : B ⟶ Spec (.of ℂ)) [IsProper p]
    (H : LineBundle B) (hH : H.IsAmple) (C : IntegralCurve B) :
    (∀ L M : LineBundle B, curveDegree p (L.tensor M) C =
      curveDegree p L C + curveDegree p M C) ∧
    (∀ (L : LineBundle B) (n : ℕ), curveDegree p (L.pow n) C =
      (n : ℤ) * curveDegree p L C) := by
  let HC := H.pullback C.embedding
  have hHC : HC.IsAmple := LineBundle.IsAmple.pullback_closedImmersion H hH C.embedding
  have hfinite := CurveDegree.finite_line_cohomology_of_ample (C.embedding ≫ p) HC hHC
  have hH2 : CurveDegree.LineCohomologyTwoZero C.scheme := by
    intro M
    exact ⟨fun a b =>
      (lineBundle_cohomology_zero_of_dimension_le 1 (C.embedding ≫ p) HC hHC M
        C.dimension.le 2 (by omega) a).trans
      (lineBundle_cohomology_zero_of_dimension_le 1 (C.embedding ≫ p) HC hHC M
        C.dimension.le 2 (by omega) b).symm⟩
  exact ⟨fun L M => curveDegree_tensor p H hH L M C hfinite hH2,
    fun L n => curveDegree_pow p H hH L C hfinite hH2 n⟩

def marginCoefficient (a : ℕ) (σ : ℝ) : ℝ := σ / ((a : ℝ) * (1 + σ) - 1)

theorem marginCoefficient_pos {a : ℕ} (ha : 1 < a) {σ : ℝ} (hσ : 0 < σ) :
    0 < marginCoefficient a σ := by
  apply div_pos hσ
  exact NefAmple.combination_denominator_pos (by exact_mod_cast ha) hσ

theorem margin_of_nonnegative_degree
    (p : B ⟶ Spec (.of ℂ)) [IsProper p] (A J : LineBundle B)
    (a : ℕ) (ha : 1 < a) (hample : ((A.pow a).tensor J).IsAmple)
    (σ : ℝ) (hσ : 0 < σ) (C : IntegralCurve B)
    (hn : 0 ≤ (curveDegree p A C : ℝ) + (1 + σ) * (curveDegree p J C : ℝ)) :
    marginCoefficient a σ * (curveDegree p ((A.pow a).tensor J) C : ℝ) ≤
      (curveDegree p (A.tensor J) C : ℝ) := by
  obtain ⟨ht,hp⟩ := curve_degree_laws p ((A.pow a).tensor J) hample C
  rw [ht, hp, ht]
  push_cast
  unfold marginCoefficient
  have ha' : 1 < (a : ℝ) := by exact_mod_cast ha
  have hd := NefAmple.combination_denominator_pos ha' hσ
  rw [div_mul_eq_mul_div]
  apply (div_le_iff₀ hd).mpr
  have hn' := mul_nonneg (sub_pos.mpr ha').le hn
  nlinarith

theorem curveDegree_zero_of_frame (p : B ⟶ Spec (.of ℂ))
    (J : LineBundle B) (C : IntegralCurve B)
    (e : (J.pullback C.embedding).sheaf ≅ structureSheaf C.scheme) :
    curveDegree p J C = 0 := by
  unfold curveDegree
  change eulerCharacteristic (C.embedding ≫ p) 1 (J.pullback C.embedding).sheaf - _ = 0
  rw [eulerCharacteristic_iso (C.embedding ≫ p) e 1]
  exact sub_self _

theorem margin_of_exceptional_frame
    (p : B ⟶ Spec (.of ℂ)) [IsProper p] (A J : LineBundle B)
    (a : ℕ) (ha : 1 < a) (hample : ((A.pow a).tensor J).IsAmple)
    (σ : ℝ) (hσ : 0 < σ) (C : IntegralCurve B)
    (e : (J.pullback C.embedding).sheaf ≅ structureSheaf C.scheme) :
    marginCoefficient a σ * (curveDegree p ((A.pow a).tensor J) C : ℝ) ≤
      (curveDegree p (A.tensor J) C : ℝ) := by
  have hj := curveDegree_zero_of_frame p J C e
  have hpos := curveDegree_pos_of_ample p ((A.pow a).tensor J) hample C
  obtain ⟨ht,hp⟩ := curve_degree_laws p ((A.pow a).tensor J) hample C
  rw [ht, hp, hj, add_zero] at hpos
  have ha' : (0 : ℤ) < a := by exact_mod_cast (Nat.zero_lt_of_lt ha)
  have hA := (mul_pos_iff_of_pos_left ha').mp hpos
  apply margin_of_nonnegative_degree p A J a ha hample σ hσ C
  rw [hj]
  simpa using (show (0 : ℝ) ≤ (curveDegree p A C : ℝ) by exact_mod_cast hA.le)

theorem margin_of_avoids_center
    (p : B ⟶ Spec (.of ℂ)) [IsProper p]
    (I : X.IdealSheafData) (π : B ⟶ X) (A J : LineBundle B)
    (ι : J.sheaf ⟶ structureSheaf B) (hJ : PresentsPullbackIdeal I π J ι)
    (a : ℕ) (ha : 1 < a) (hample : ((A.pow a).tensor J).IsAmple)
    (σ : ℝ) (hσ : 0 < σ) (C : IntegralCurve B)
    (havoid : ∀ c : C.scheme, (C.embedding ≫ π) c ∉ I.support) :
    marginCoefficient a σ * (curveDegree p ((A.pow a).tensor J) C : ℝ) ≤
      (curveDegree p (A.tensor J) C : ℝ) :=
  margin_of_exceptional_frame p A J a ha hample σ hσ C
    (InvertibleIdealAway.pullbackIsoOfAvoids I π J ι hJ C.embedding havoid)

theorem margin_of_image_outside_chart
    (p : B ⟶ Spec (.of ℂ)) [IsProper p]
    (I : X.IdealSheafData) (π : B ⟶ X) (A J : LineBundle B)
    (ι : J.sheaf ⟶ structureSheaf B) (hJ : PresentsPullbackIdeal I π J ι)
    (a : ℕ) (ha : 1 < a) (hample : ((A.pow a).tensor J).IsAmple)
    (σ : ℝ) (hσ : 0 < σ) (C : IntegralCurve B)
    (U : X.Opens) (hsupport : (I.support : Set X) ⊆ U)
    (hmiss : ∀ c : C.scheme, (C.embedding ≫ π) c ∉ U) :
    marginCoefficient a σ * (curveDegree p ((A.pow a).tensor J) C : ℝ) ≤
      (curveDegree p (A.tensor J) C : ℝ) :=
  margin_of_avoids_center p I π A J ι hJ a ha hample σ hσ C
    (fun c hc => hmiss c (hsupport hc))

theorem margin_of_contracted
    (p : B ⟶ Spec (.of ℂ)) [IsProper p] (π : B ⟶ X)
    (L : LineBundle X) (J : LineBundle B)
    (a : ℕ) (ha : 1 < a) (hample : (((L.pullback π).pow a).tensor J).IsAmple)
    (σ : ℝ) (hσ : 0 < σ) (C : IntegralCurve B)
    (x : X) (hc : Set.range (C.embedding ≫ π) ⊆ ({x} : Set X)) :
    marginCoefficient a σ * (curveDegree p (((L.pullback π).pow a).tensor J) C : ℝ) ≤
      (curveDegree p ((L.pullback π).tensor J) C : ℝ) := by
  have hA := ConstantPullbackDegree.curveDegree_eq_zero_of_contracted p L π C x hc
  have hpos := curveDegree_pos_of_ample p (((L.pullback π).pow a).tensor J) hample C
  obtain ⟨ht,hp⟩ := curve_degree_laws p (((L.pullback π).pow a).tensor J) hample C
  rw [ht, hp, hA, mul_zero, zero_add] at hpos
  apply margin_of_nonnegative_degree p (L.pullback π) J a ha hample σ hσ C
  rw [hA]
  exact add_nonneg (by norm_num) (mul_nonneg (by linarith)
    (by exact_mod_cast hpos.le))

end
end LogTwo.Geometry.CurveMarginLemmas

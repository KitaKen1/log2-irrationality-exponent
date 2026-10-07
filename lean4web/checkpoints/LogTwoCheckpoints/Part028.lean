/- Generated rc4 checkpoint for LogTwo.
Modified from the reduced edition: new imports, separate module compilation,
and synchronous elaboration. Original source blocks and notices are retained.
See ../../../THIRD_PARTY_NOTICES.txt and ../../reduction.json.
-/
module
public import LogTwoCheckpoints.Part008
public import LogTwoCheckpoints.Part009
public import LogTwoCheckpoints.Part012
public import LogTwoCheckpoints.Part013
public import LogTwoCheckpoints.Part015
public import LogTwoCheckpoints.Part016
public import LogTwoCheckpoints.Part017
public import LogTwoCheckpoints.Part018
public import LogTwoCheckpoints.Part019
public import LogTwoCheckpoints.Part021
public import LogTwoCheckpoints.Part023
public import LogTwoCheckpoints.Part024
public import LogTwoCheckpoints.Part025
public import LogTwoCheckpoints.Part026
public import LogTwoCheckpoints.Part027
public import Mathlib.Algebra.Group.ForwardDiff
public import Mathlib.AlgebraicGeometry.Modules.Sheaf
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.Analysis.Complex.Polynomial.Basic
public import Mathlib.RingTheory.Ideal.KrullsHeightTheorem
public import Mathlib.RingTheory.KrullDimension.NonZeroDivisors
public import Mathlib.RingTheory.OrderOfVanishing.Basic
@[expose] public section
set_option Elab.async false

-- Source: OAI/NumberTheory/PiExponent/Geometry/CurveDegreeLaws.lean
section Source0700
-- Modified in this edition: unused plain lemmas removed; see reduction.json.
/-
Modification notice for the LogTwo project.
Derived from openai/math (Apache-2.0), revision adc7f1241b42e322a6451854ab7e4b4c146bf78a.
Original source: lean/OAI/NumberTheory/PiExponent/Geometry/CurveDegreeLaws.lean
Changes: Convert module/import declarations to the Lean 4.34 public module format.
See ../THIRD_PARTY_NOTICES.txt for provenance and the recorded changes.
-/

namespace OAI

namespace PiExponent.NumericalAmpleness
noncomputable section
open AlgebraicGeometry CategoryTheory
open PiExponentSeshadri.Geometry
variable {X : Scheme.{0}}

theorem curveLineCohomologyTwoZero_of_ample
    (p : X ⟶ Spec (CommRingCat.of ℂ)) [IsProper p]
    (H : LineBundle X) (hH : H.IsAmple) (C : IntegralCurve X) :
    CurveDegree.LineCohomologyTwoZero C.scheme := by
  intro M
  have hz := lineBundle_cohomology_zero_of_dimension_le 1 (C.embedding ≫ p)
    (H.pullback C.embedding) (hH.pullback_closedImmersion H C.embedding) M
    C.dimension.le 2 (by omega)
  exact ⟨fun a b => (hz a).trans (hz b).symm⟩

theorem curveDegree_pow_of_ample
    (p : X ⟶ Spec (CommRingCat.of ℂ)) [IsProper p]
    (H : LineBundle X) (hH : H.IsAmple) (L : LineBundle X) (C : IntegralCurve X) (n : ℕ) :
    curveDegree p (L.pow n) C = (n : ℤ) * curveDegree p L C :=
  curveDegree_pow p H hH L C
    (CurveDegree.finite_line_cohomology_of_ample (C.embedding ≫ p) (H.pullback C.embedding)
      (hH.pullback_closedImmersion H C.embedding))
    (curveLineCohomologyTwoZero_of_ample p H hH C) n

theorem curveDegree_tensor_of_ample
    (p : X ⟶ Spec (CommRingCat.of ℂ)) [IsProper p]
    (H : LineBundle X) (hH : H.IsAmple) (L M : LineBundle X) (C : IntegralCurve X) :
    curveDegree p (L.tensor M) C = curveDegree p L C + curveDegree p M C :=
  curveDegree_tensor p H hH L M C
    (CurveDegree.finite_line_cohomology_of_ample (C.embedding ≫ p) (H.pullback C.embedding)
      (hH.pullback_closedImmersion H C.embedding))
    (curveLineCohomologyTwoZero_of_ample p H hH C)

theorem curveDegree_pos_of_uniform_margin
    (p : X ⟶ Spec (CommRingCat.of ℂ)) [IsProper p]
    (H L : LineBundle X) (hH : H.IsAmple) (ε : ℝ) (hε : 0 < ε)
    (hmargin : ∀ C : IntegralCurve X,
      ε * (curveDegree p H C : ℝ) ≤ (curveDegree p L C : ℝ))
    (C : IntegralCurve X) : 0 < curveDegree p L C := by
  have hHpos : (0 : ℝ) < (curveDegree p H C : ℝ) := by
    exact_mod_cast curveDegree_pos_of_ample p H hH C
  have hpos : (0 : ℝ) < (curveDegree p L C : ℝ) := (mul_pos hε hHpos).trans_le (hmargin C)
  exact_mod_cast hpos

theorem uniform_margin_tensor_powers
    (p : X ⟶ Spec (CommRingCat.of ℂ)) [IsProper p]
    (H L : LineBundle X) (hH : H.IsAmple) (ε : ℝ)
    (hmargin : ∀ C : IntegralCurve X,
      ε * (curveDegree p H C : ℝ) ≤ (curveDegree p L C : ℝ))
    (a b : ℕ) (C : IntegralCurve X) :
    ((b:ℝ)*ε+a) * (curveDegree p H C : ℝ) ≤
      (curveDegree p ((L.pow b).tensor (H.pow a)) C : ℝ) := by
  rw [curveDegree_tensor_of_ample p H hH,
    curveDegree_pow_of_ample p H hH L C b, curveDegree_pow_of_ample p H hH H C a]
  push_cast
  have h := mul_le_mul_of_nonneg_left (hmargin C) (Nat.cast_nonneg b : (0:ℝ) ≤ b)
  nlinarith

end
end PiExponent.NumericalAmpleness

end OAI
end Source0700

-- Source: OAI/NumberTheory/PiExponent/Ampleness/NakaiInductionStep.lean
section Source0701
/-
Modification notice for the LogTwo project.
Derived from openai/math (Apache-2.0), revision adc7f1241b42e322a6451854ab7e4b4c146bf78a.
Original source: lean/OAI/NumberTheory/PiExponent/Ampleness/NakaiInductionStep.lean
Changes: Convert module/import declarations to the Lean 4.34 public module format.
See ../THIRD_PARTY_NOTICES.txt for provenance and the recorded changes.
-/

namespace OAI

namespace PiExponent.NumericalAmpleness
noncomputable section
open AlgebraicGeometry CategoryTheory TopologicalSpace Filter
open PiExponentSeshadri.Geometry
variable {X : Scheme.{0}}

theorem isAmple_of_lower_ampleness_of_euler_growth [IsIntegral X]
    (p : X ⟶ Spec (CommRingCat.of ℂ)) [IsProper p]
    (r : ℕ) (i : X ⟶ ProjectiveO1.projectiveSpace ℂ (Fin (r+1))) [IsClosedImmersion i]
    (hi : i ≫ polynomialProjectiveProjection ℂ (Fin (r+1)) = p)
    (H L : LineBundle X) (hH : H.IsAmple) (d : ℕ)
    (hdim : topologicalKrullDim X ≤ d+1)
    (hlower : ∀ I : X.IdealSheafData, topologicalKrullDim I.subscheme ≤ d →
      (L.pullback I.subschemeι).IsAmple)
    (hgrowth : Tendsto (fun n => eulerCharacteristic p (d+1) (L.pow n).sheaf) atTop atTop)
    (hpositive : ∀ C : IntegralCurve X, 0 < curveDegree p L C) : L.IsAmple := by
  obtain ⟨a,ha,k,s,hs⟩ := exists_power_section_cover_of_euler_growth
    p r i hi H L hH d hdim hlower hgrowth
  apply LineBundle.IsAmple.of_pow L ha
  apply isAmple_of_section_cover_of_curveDegree_pos p (L.pow a) (d+1) (by
    simpa only [Nat.cast_add, Nat.cast_one] using hdim) k s hs
  intro C
  rw [curveDegree_pow_of_ample p H hH L C a]
  exact mul_pos (by exact_mod_cast ha) (hpositive C)

theorem isAmple_of_lower_ampleness_of_topEuler_pos [IsIntegral X]
    (p : X ⟶ Spec (CommRingCat.of ℂ)) [IsProper p]
    (r : ℕ) (i : X ⟶ ProjectiveO1.projectiveSpace ℂ (Fin (r+1))) [IsClosedImmersion i]
    (hi : i ≫ polynomialProjectiveProjection ℂ (Fin (r+1)) = p)
    (H L : LineBundle X) (hH : H.IsAmple) (d : ℕ)
    (hdim : topologicalKrullDim X ≤ d+1)
    (hlower : ∀ I : X.IdealSheafData, topologicalKrullDim I.subscheme ≤ d →
      (L.pullback I.subschemeι).IsAmple)
    (htop : 0 < (fwdDiff (1 : ℕ))^[d+1]
      (fun n => eulerCharacteristic p (d+1) (L.pow n).sheaf) 0)
    (hpositive : ∀ C : IntegralCurve X, 0 < curveDegree p L C) : L.IsAmple := by
  let : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian p
  let : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace p
  let : IsNoetherian X := {}
  have hzero := euler_power_dimension_difference_eq_zero p r i hi L (d+1) (by
    simpa only [Nat.cast_add, Nat.cast_one] using hdim)
  have hgrowth := tendsto_atTop_of_forwardDifference_eq_zero
    (fun n => eulerCharacteristic p (d+1) (L.pow n).sheaf) (d+1) (by omega) hzero htop
  exact isAmple_of_lower_ampleness_of_euler_growth p r i hi H L hH d hdim hlower hgrowth hpositive

theorem isAmple_of_lower_ampleness_of_topEuler_pos_of_margin [IsIntegral X]
    (p : X ⟶ Spec (CommRingCat.of ℂ)) [IsProper p]
    (r : ℕ) (i : X ⟶ ProjectiveO1.projectiveSpace ℂ (Fin (r+1))) [IsClosedImmersion i]
    (hi : i ≫ polynomialProjectiveProjection ℂ (Fin (r+1)) = p)
    (H L : LineBundle X) (hH : H.IsAmple) (d : ℕ)
    (hdim : topologicalKrullDim X ≤ d+1)
    (hlower : ∀ I : X.IdealSheafData, topologicalKrullDim I.subscheme ≤ d →
      (L.pullback I.subschemeι).IsAmple)
    (htop : 0 < (fwdDiff (1 : ℕ))^[d+1]
      (fun n => eulerCharacteristic p (d+1) (L.pow n).sheaf) 0)
    (ε : ℝ) (hε : 0 < ε)
    (hmargin : ∀ C : IntegralCurve X,
      ε * (curveDegree p H C : ℝ) ≤ (curveDegree p L C : ℝ)) : L.IsAmple :=
  isAmple_of_lower_ampleness_of_topEuler_pos p r i hi H L hH d hdim hlower htop
    (curveDegree_pos_of_uniform_margin p H L hH ε hε hmargin)

end
end PiExponent.NumericalAmpleness

end OAI
end Source0701

-- Source: OAI/NumberTheory/PiExponent/Approximation/NumericalSlopeInduction.lean
section Source0702
/-
Modification notice for the LogTwo project.
Derived from openai/math (Apache-2.0), revision adc7f1241b42e322a6451854ab7e4b4c146bf78a.
Original source: lean/OAI/NumberTheory/PiExponent/Approximation/NumericalSlopeInduction.lean
Changes: Convert module/import declarations to the Lean 4.34 public module format.
See ../THIRD_PARTY_NOTICES.txt for provenance and the recorded changes.
-/

namespace OAI

namespace PiExponent.NumericalAmpleness
noncomputable section
open AlgebraicGeometry CategoryTheory TopologicalSpace
open PiExponentSeshadri.Geometry
variable {X : Scheme.{0}}

def LowerClosedNumericalCriterion (p : X ⟶ Spec (CommRingCat.of ℂ))
    (H : LineBundle X) (d : ℕ) : Prop :=
  ∀ (I : X.IdealSheafData), topologicalKrullDim I.subscheme ≤ d →
    ∀ (M : LineBundle I.subscheme) (δ : ℝ), 0 < δ →
      (∀ C : IntegralCurve I.subscheme,
        δ * (curveDegree (I.subschemeι ≫ p) (H.pullback I.subschemeι) C : ℝ) ≤
          (curveDegree (I.subschemeι ≫ p) M C : ℝ)) → M.IsAmple

theorem slope_lower_closed_ampleness
    (p : X ⟶ Spec (CommRingCat.of ℂ)) [IsProper p]
    (H L : LineBundle X) (hH : H.IsAmple) (d : ℕ)
    (hlower : LowerClosedNumericalCriterion p H d)
    (ε : ℝ) (hε : 0 < ε)
    (hmargin : ∀ C : IntegralCurve X,
      ε * (curveDegree p H C : ℝ) ≤ (curveDegree p L C : ℝ))
    (a b : ℕ) (hb : 0 < b) :
    ∀ I : X.IdealSheafData, topologicalKrullDim I.subscheme ≤ d →
      ((slopeBundle L H a b).pullback I.subschemeι).IsAmple := by
  intro I hI
  have hδ : (0:ℝ) < (b:ℝ)*ε+a :=
    add_pos_of_pos_of_nonneg (mul_pos (by exact_mod_cast hb) hε) (Nat.cast_nonneg a)
  apply hlower I hI ((slopeBundle L H a b).pullback I.subschemeι) ((b:ℝ)*ε+a) hδ
  exact uniform_curve_margin_restrict p (slopeBundle L H a b) H ((b:ℝ)*ε+a)
    (uniform_margin_tensor_powers p H L hH ε hmargin a b) I.subschemeι

theorem ample_slope_of_topEuler_pos_of_lower_criterion [IsIntegral X]
    (p : X ⟶ Spec (CommRingCat.of ℂ)) [IsProper p]
    (r : ℕ) (i : X ⟶ ProjectiveO1.projectiveSpace ℂ (Fin (r+1))) [IsClosedImmersion i]
    (hi : i ≫ polynomialProjectiveProjection ℂ (Fin (r+1)) = p)
    (H L : LineBundle X) (hH : H.IsAmple) (d : ℕ)
    (hdim : topologicalKrullDim X ≤ d+1)
    (hlower : LowerClosedNumericalCriterion p H d)
    (ε : ℝ) (hε : 0 < ε)
    (hmargin : ∀ C : IntegralCurve X,
      ε * (curveDegree p H C : ℝ) ≤ (curveDegree p L C : ℝ))
    (a b : ℕ) (hb : 0 < b)
    (htop : 0 < (fwdDiff (1:ℕ))^[d+1]
      (fun n => eulerCharacteristic p (d+1) ((slopeBundle L H a b).pow n).sheaf) 0) :
    (slopeBundle L H a b).IsAmple := by
  have hδ : (0:ℝ) < (b:ℝ)*ε+a :=
    add_pos_of_pos_of_nonneg (mul_pos (by exact_mod_cast hb) hε) (Nat.cast_nonneg a)
  exact isAmple_of_lower_ampleness_of_topEuler_pos_of_margin p r i hi H
    (slopeBundle L H a b) hH d hdim
    (slope_lower_closed_ampleness p H L hH d hlower ε hε hmargin a b hb)
    htop ((b:ℝ)*ε+a) hδ (uniform_margin_tensor_powers p H L hH ε hmargin a b)

theorem ample_slope_of_polynomial_pos_of_lower_criterion [IsIntegral X]
    (p : X ⟶ Spec (CommRingCat.of ℂ)) [IsProper p]
    (r : ℕ) (i : X ⟶ ProjectiveO1.projectiveSpace ℂ (Fin (r+1))) [IsClosedImmersion i]
    (hi : i ≫ polynomialProjectiveProjection ℂ (Fin (r+1)) = p)
    (H L : LineBundle X) (hH : H.IsAmple) (d : ℕ)
    (hdim : topologicalKrullDim X ≤ d+1)
    (hlower : LowerClosedNumericalCriterion p H d)
    (ε : ℝ) (hε : 0 < ε)
    (hmargin : ∀ C : IntegralCurve X,
      ε * (curveDegree p H C : ℝ) ≤ (curveDegree p L C : ℝ))
    (P : Polynomial ℝ)
    (hP : ∀ a b : ℕ, 0 < b →
      (((fwdDiff (1:ℕ))^[d+1]
        (fun n => eulerCharacteristic p (d+1) ((slopeBundle L H a b).pow n).sheaf) 0 : ℤ):ℝ) =
        (b:ℝ)^(d+1) * P.eval ((a:ℝ)/b))
    (a b : ℕ) (hb : 0 < b) (hpos : 0 < P.eval ((a:ℝ)/b)) :
    (slopeBundle L H a b).IsAmple := by
  apply ample_slope_of_topEuler_pos_of_lower_criterion p r i hi H L hH d hdim hlower ε hε hmargin a b hb
  have hreal : (0:ℝ) <
      (((fwdDiff (1:ℕ))^[d+1]
        (fun n => eulerCharacteristic p (d+1) ((slopeBundle L H a b).pow n).sheaf) 0 : ℤ):ℝ) := by
    rw [hP a b hb]
    exact mul_pos (pow_pos (by exact_mod_cast hb) _) hpos
  exact_mod_cast hreal

end
end PiExponent.NumericalAmpleness

end OAI
end Source0702

-- Source: OAI/NumberTheory/PiExponent/Approximation/NumericalThresholdStep.lean
section Source0703
/-
Modification notice for the LogTwo project.
Derived from openai/math (Apache-2.0), revision adc7f1241b42e322a6451854ab7e4b4c146bf78a.
Original source: lean/OAI/NumberTheory/PiExponent/Approximation/NumericalThresholdStep.lean
Changes: Convert module/import declarations to the Lean 4.34 public module format.
See ../THIRD_PARTY_NOTICES.txt for provenance and the recorded changes.
-/

namespace OAI

namespace PiExponent.NumericalAmpleness
noncomputable section
open AlgebraicGeometry CategoryTheory TopologicalSpace
open PiExponentSeshadri.Geometry
variable {X : Scheme.{0}}

theorem isAmple_of_lower_criterion_of_euler_slope_polynomial [IsIntegral X]
    (p : X ⟶ Spec (CommRingCat.of ℂ)) [IsProper p]
    (r : ℕ) (i : X ⟶ ProjectiveO1.projectiveSpace ℂ (Fin (r+1))) [IsClosedImmersion i]
    (hi : i ≫ polynomialProjectiveProjection ℂ (Fin (r+1)) = p)
    (H L : LineBundle X) (hH : H.IsAmple) (d : ℕ)
    (hdim : topologicalKrullDim X ≤ d+1)
    (hlower : LowerClosedNumericalCriterion p H d)
    (ε : ℝ) (hε : 0 < ε)
    (hmargin : ∀ C : IntegralCurve X,
      ε * (curveDegree p H C : ℝ) ≤ (curveDegree p L C : ℝ))
    (P : Polynomial ℝ)
    (hP : ∀ a b : ℕ, 0 < b →
      (((fwdDiff (1:ℕ))^[d+1]
        (fun n => eulerCharacteristic p (d+1) ((slopeBundle L H a b).pow n).sheaf) 0 : ℤ):ℝ) =
        (b:ℝ)^(d+1) * P.eval ((a:ℝ)/b))
    (hPample : ∀ a b : ℕ, 0 < b → (slopeBundle L H a b).IsAmple →
      0 < P.eval ((a:ℝ)/b))
    (hPderivative : ∀ a b : ℕ, 0 < b → (slopeBundle L H a b).IsAmple →
      ((a:ℝ)/b+ε) * P.derivative.eval ((a:ℝ)/b) ≤
        ((d+1:ℕ):ℝ) * P.eval ((a:ℝ)/b)) : L.IsAmple := by
  let : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace p
  let t := ampleThreshold L H
  have ht : 0 ≤ t := ampleThreshold_nonneg L H hH
  have hrat (q : ℚ) (hq : t < (q:ℝ)) : ∃ a b : ℕ, 0 < b ∧
      (q:ℝ) = (a:ℝ)/b ∧ (slopeBundle L H a b).IsAmple := by
    have hqnonneg : (0:ℚ) ≤ q := by exact_mod_cast (ht.trans hq.le)
    obtain ⟨a,b,hb,hab⟩ := nonnegative_rat_nat_ratio q hqnonneg
    exact ⟨a,b,hb,hab,ample_of_threshold_lt L H hH a b hb (hab ▸ hq)⟩
  have hpositive : ∀ q : ℚ, t < (q:ℝ) → 0 < P.eval (q:ℝ) := by
    intro q hq
    obtain ⟨a,b,hb,hab,hamp⟩ := hrat q hq
    rw [hab]
    exact hPample a b hb hamp
  have hderivative : ∀ q : ℚ, t < (q:ℝ) →
      ((q:ℝ)+ε) * P.derivative.eval (q:ℝ) ≤ ((d+1:ℕ):ℝ)*P.eval (q:ℝ) := by
    intro q hq
    obtain ⟨a,b,hb,hab,hamp⟩ := hrat q hq
    rw [hab]
    exact hPderivative a b hb hamp
  have hPt : 0 < P.eval t :=
    polynomial_pos_at_boundary_of_rational_margin P (d+1) t ε ht hε hpositive hderivative
  by_cases htzero : t = 0
  · have hpzero : 0 < P.eval ((0:ℝ)/1) := by simpa only [htzero,zero_div] using hPt
    exact (slope_zero_isAmple_iff L H 1 (by decide)).mp
      (ample_slope_of_polynomial_pos_of_lower_criterion p r i hi H L hH d hdim hlower ε hε
        hmargin P hP 0 1 (by decide) (by simpa using hpzero))
  · have htpos : 0 < t := lt_of_le_of_ne ht (Ne.symm htzero)
    obtain ⟨q,hq0,hqt,hPq⟩ := exists_positive_rational_below_of_polynomial_pos P t htpos hPt
    have hqnonneg : (0:ℚ) ≤ q := by exact_mod_cast hq0.le
    obtain ⟨a,b,hb,hab⟩ := nonnegative_rat_nat_ratio q hqnonneg
    have ha : 0 < a := by
      have hnum : (0:ℝ) < a :=
        (div_pos_iff_of_pos_right (by exact_mod_cast hb : (0:ℝ)<b)).mp (hab ▸ hq0)
      exact_mod_cast hnum
    have hamp := ample_slope_of_polynomial_pos_of_lower_criterion p r i hi H L hH d hdim
      hlower ε hε hmargin P hP a b hb (hab ▸ hPq)
    have habove := threshold_lt_of_ample L H a b ha hb hamp
    have hbelow : (a:ℝ)/b < ampleThreshold L H := hab ▸ hqt
    exact False.elim (lt_asymm habove hbelow)

end
end PiExponent.NumericalAmpleness

end OAI
end Source0703

-- Source: OAI/NumberTheory/PiExponent/Ampleness/AmpleDivisorDimensionBase.lean
section Source0704
/-
Modification notice for the LogTwo project.
Derived from openai/math (Apache-2.0), revision adc7f1241b42e322a6451854ab7e4b4c146bf78a.
Original source: lean/OAI/NumberTheory/PiExponent/Ampleness/AmpleDivisorDimensionBase.lean
Changes: Convert module/import declarations to the Lean 4.34 public module format.
See ../THIRD_PARTY_NOTICES.txt for provenance and the recorded changes.
-/

namespace OAI

namespace PiExponent.NumericalAmpleness
noncomputable section
open AlgebraicGeometry CategoryTheory TopologicalSpace Order
open PiExponentSeshadri.Geometry PiExponentSeshadri.Frames PiExponentSeshadri.SectionOpens
open PiExponent.SectionZeroIdeal

theorem exists_irreducibleClosed_full_dimension (T : Type*) [TopologicalSpace T]
    (n : ℕ) (hdim : topologicalKrullDim T = n) :
    ∃ Z : IrreducibleCloseds T, topologicalKrullDim (Z : Set T) = n := by
  have hdim' : Order.krullDim (IrreducibleCloseds T) = n := hdim
  obtain ⟨p, hp⟩ := Order.le_krullDim_iff.mp (le_of_eq hdim'.symm)
  have hlast : (p.length : ℕ∞) = Order.height p.last := by
    apply le_antisymm (Order.length_le_height_last (p := p))
    have hh := Order.height_le_krullDim p.last
    rw [hdim', ← hp] at hh
    exact_mod_cast hh
  refine ⟨p.last, ?_⟩
  rw [topologicalKrullDim_irreducibleClosed, ← hlast, hp]
  rfl

theorem exists_integral_closed_full_dimension (X : Scheme.{0})
    (n : ℕ) (hdim : topologicalKrullDim X = n) :
    ∃ Y : Scheme.{0}, ∃ i : Y ⟶ X,
      IsClosedImmersion i ∧ IsIntegral Y ∧ topologicalKrullDim Y = n := by
  obtain ⟨Z, hZ⟩ := exists_irreducibleClosed_full_dimension X n hdim
  let C : Closeds X := ⟨Z, Z.isClosed⟩
  let I := Scheme.IdealSheafData.vanishingIdeal C
  have hs : (I.support : Set X) = (Z : Set X) := by
    simp only [I, Scheme.IdealSheafData.coe_support_vanishingIdeal]
    rfl
  have : IsReduced I.subscheme := isReduced_vanishingIdeal_subscheme C
  have : IrreducibleSpace I.subscheme := by
    change IrreducibleSpace (I.support : Set X)
    rw [hs]
    exact Subtype.irreducibleSpace Z.isIrreducible
  refine ⟨I.subscheme, I.subschemeι, inferInstance,
    isIntegral_of_irreducibleSpace_of_isReduced _, ?_⟩
  change topologicalKrullDim (I.support : Set X) = n
  rw [hs]
  exact hZ

variable {X : Scheme.{0}}

theorem ample_section_has_zero
    (p : X ⟶ Spec (CommRingCat.of ℂ)) [IsProper p]
    (H : LineBundle X) (hH : H.IsAmple)
    (s : GlobalSections X H.sheaf) (n : ℕ)
    (hdim : topologicalKrullDim X = n) (hn : 0 < n) :
    ∃ y : X, y ∉ sectionOpen X s := by
  by_contra h
  push Not at h
  have : IsIso s := isIso_of_locally_isIso s (by
    intro x
    exact ⟨isoOpen s, h x, isIso_restrict_isoOpen s⟩)
  obtain ⟨C⟩ := nonempty_integralCurve_of_dimension_pos X n hdim hn
  have hpos := curveDegree_pos_of_ample p H hH C
  let e : H.sheaf ≅ structureSheaf X := (asIso s).symm
  have he := eulerCharacteristic_iso (C.embedding ≫ p)
    ((Scheme.Modules.pullback C.embedding).mapIso e ≪≫ pullbackUnitIso C.embedding) 1
  have hz : curveDegree p H C = 0 := by
    unfold curveDegree
    change eulerCharacteristic (C.embedding ≫ p) 1
      ((Scheme.Modules.pullback C.embedding).obj H.sheaf) =
      eulerCharacteristic (C.embedding ≫ p) 1 (structureSheaf C.scheme) at he
    rw [he]
    exact sub_self _
  omega

theorem ample_section_zero_nonempty
    (p : X ⟶ Spec (CommRingCat.of ℂ)) [IsProper p]
    (H : LineBundle X) (hH : H.IsAmple)
    (s : GlobalSections X H.sheaf) (n : ℕ)
    (hdim : topologicalKrullDim X = n) (hn : 0 < n) :
    Nonempty (zeroIdeal H s).subscheme := by
  obtain ⟨y, hy⟩ := ample_section_has_zero p H hH s n hdim hn
  have hm : y ∈ Set.range (zeroIdeal H s).subschemeι := by
    rw [Scheme.IdealSheafData.range_subschemeι, zeroIdeal_support]
    exact hy
  obtain ⟨z, -⟩ := hm
  exact ⟨z⟩

end
end PiExponent.NumericalAmpleness

end OAI
end Source0704

-- Source: OAI/NumberTheory/PiExponent/LocalAlgebra/PrincipalQuotientDimension.lean
section Source0705
-- Modified in this edition: unused plain lemmas removed; see reduction.json.
/-
Modification notice for the LogTwo project.
Derived from openai/math (Apache-2.0), revision adc7f1241b42e322a6451854ab7e4b4c146bf78a.
Original source: lean/OAI/NumberTheory/PiExponent/LocalAlgebra/PrincipalQuotientDimension.lean
Changes: Convert module/import declarations to the Lean 4.34 public module format.
See ../THIRD_PARTY_NOTICES.txt for provenance and the recorded changes.
-/

namespace OAI

namespace PiExponent.GeometrySupport.PrincipalQuotientDimension

variable (k R : Type*) [Field k] [CommRing R] [IsDomain R]
  [Algebra k R] [Algebra.FiniteType k R]

include k

theorem le_quotient_succ (a : R) (hu : ¬ IsUnit a) :
    ringKrullDim R ≤ ringKrullDim (R ⧸ Ideal.span {a}) + 1 := by
  let : IsNoetherianRing R := Algebra.FiniteType.isNoetherianRing k R
  obtain ⟨m, hm, ham⟩ := Ideal.exists_le_maximal (Ideal.span {a})
    (Ideal.span_singleton_ne_top hu)
  let : m.IsMaximal := hm
  rw [← PiExponentJets.W29.affineDomain_maximal_height k R m]
  exact Ideal.height_le_ringKrullDim_quotient_add_one
    (ham (Ideal.subset_span (by simp)))

end PiExponent.GeometrySupport.PrincipalQuotientDimension

end OAI
end Source0705

-- Source: OAI/NumberTheory/PiExponent/Ampleness/AmpleDivisorDimension.lean
section Source0706
/-
Modification notice for the LogTwo project.
Derived from openai/math (Apache-2.0), revision adc7f1241b42e322a6451854ab7e4b4c146bf78a.
Original source: lean/OAI/NumberTheory/PiExponent/Ampleness/AmpleDivisorDimension.lean
Changes: Convert module/import declarations to the Lean 4.34 public module format.
See ../THIRD_PARTY_NOTICES.txt for provenance and the recorded changes.
-/

namespace OAI

namespace PiExponent.NumericalAmpleness
noncomputable section
open AlgebraicGeometry CategoryTheory TopologicalSpace
open PiExponentSeshadri.Geometry PiExponentSeshadri.Frames PiExponentSeshadri.SectionOpens
open PiExponent.SectionZeroIdeal

variable {X Y : Scheme.{0}}

theorem sectionZero_pullback_dimension_le (H : LineBundle X)
    (s : GlobalSections X H.sheaf) (i : Y ⟶ X) [IsClosedImmersion i] :
    topologicalKrullDim (zeroIdeal (H.pullback i) (pullbackSection i s)).subscheme ≤
      topologicalKrullDim (zeroIdeal H s).subscheme := by
  let I := zeroIdeal H s
  let J := zeroIdeal (H.pullback i) (pullbackSection i s)
  have hmap (z : J.subscheme) : i (J.subschemeι z) ∈ (I.support : Set X) := by
    have hz := z.property
    change J.subschemeι z ∈ (J.support : Set Y) at hz
    erw [zeroIdeal_support] at hz ⊢
    change J.subschemeι z ∉ isoOpen (pullbackSection i s) at hz
    rw [pullback_isoOpen_eq H s i] at hz
    exact hz
  have he := (i.isEmbedding.comp J.subschemeι.isEmbedding).codRestrict
    (I.support : Set X) hmap
  exact he.isInducing.topologicalKrullDim_le

theorem sectionZero_dimension_succ_ge_of_zero [IsIntegral X]
    (p : X ⟶ Spec (CommRingCat.of ℂ)) [LocallyOfFiniteType p]
    (H : LineBundle X) (s : GlobalSections X H.sheaf)
    (y : X) (hy : y ∉ sectionOpen X s) :
    topologicalKrullDim X ≤ topologicalKrullDim (zeroIdeal H s).subscheme + 1 := by
  obtain ⟨V, hyV, ⟨eV⟩⟩ := H.locallyRankOne y
  obtain ⟨W, hW, hyW, hWV⟩ := exists_isAffineOpen_mem_and_subset hyV
  let U : X.affineOpens := ⟨W, hW⟩
  let e := restrictOpenFrame hWV eV
  let : Nonempty U.1 := ⟨⟨y, hyW⟩⟩
  let a : Γ(X,U) := U.1.topIso.hom (coefficient e (restrictSection U.1.ι s))
  have ha : ¬ IsUnit a := by
    intro ha
    have hc : IsUnit (coefficient e (restrictSection U.1.ι s)) := by
      have hh := ha.map U.1.topIso.inv.hom
      simpa only [a, ← CommRingCat.comp_apply, Iso.hom_inv_id,
        CommRingCat.id_apply] using hh
    have hopen := preimage_isoOpen s U.1.ι e
    rw [U.1.toScheme.basicOpen_of_isUnit hc] at hopen
    have hm : (⟨y,hyW⟩ : U.1.toScheme) ∈ U.1.ι ⁻¹ᵁ isoOpen s :=
      hopen.ge trivial
    exact hy hm
  let := IntegralAffineOpenDimension.chartAlgebra p U
  let := IntegralAffineOpenDimension.chart_finiteType p U
  have hdrop := GeometrySupport.PrincipalQuotientDimension.le_quotient_succ
    ℂ Γ(X,U) a ha
  rw [← zeroIdeal_on_frame H s U e] at hdrop
  rw [IntegralAffineOpenDimension.affine_ring_dimension_eq p U] at hdrop
  let I := zeroIdeal H s
  have hquot : ringKrullDim (Γ(X,U) ⧸ I.ideal U) ≤
      topologicalKrullDim I.subscheme := by
    rw [← PrimeSpectrum.topologicalKrullDim_eq_ringKrullDim]
    let : IsOpenImmersion (I.subschemeCover.f U) := I.subschemeCover.map_prop U
    exact (I.subschemeCover.f U).isOpenEmbedding.isEmbedding.isInducing.topologicalKrullDim_le
  exact hdrop.trans (add_le_add hquot le_rfl)

theorem regular_ample_sectionZero_dimension
    [IsNoetherian X] [Nonempty X]
    (p : X ⟶ Spec (CommRingCat.of ℂ)) [IsProper p]
    (H : LineBundle X) (hH : H.IsAmple)
    (s : GlobalSections X H.sheaf) [Mono s] (d : ℕ)
    (hdim : topologicalKrullDim X = ((d+1 : ℕ) : WithBot ℕ∞)) :
    Nonempty (zeroIdeal H s).subscheme ∧
      topologicalKrullDim (zeroIdeal H s).subscheme = d := by
  refine ⟨ample_section_zero_nonempty p H hH s (d+1) hdim (Nat.succ_pos d), ?_⟩
  apply le_antisymm
  · apply regular_sectionZero_dimension_le H s d
    simpa only [Nat.cast_add, Nat.cast_one] using hdim.le
  · obtain ⟨Y, i, hi, hY, hdimY⟩ := exists_integral_closed_full_dimension X (d+1) hdim
    let := hi
    let := hY
    have hample := LineBundle.IsAmple.pullback_closedImmersion H hH i
    obtain ⟨y, hy⟩ := ample_section_has_zero (i ≫ p) (H.pullback i) hample
      (pullbackSection i s) (d+1) hdimY (Nat.succ_pos d)
    have hlow := sectionZero_dimension_succ_ge_of_zero (i ≫ p)
      (H.pullback i) (pullbackSection i s) y hy
    rw [hdimY] at hlow
    have hbound := hlow.trans (add_le_add (sectionZero_pullback_dimension_le H s i) le_rfl)
    apply ENat.WithBot.add_le_add_one_right_iff.mp
    simpa only [Nat.cast_add, Nat.cast_one] using hbound

end
end PiExponent.NumericalAmpleness

end OAI
end Source0706

-- Source: OAI/NumberTheory/PiExponent/Cohomology/AmpleLineCohomology.lean
section Source0707
/-
Modification notice for the LogTwo project.
Derived from openai/math (Apache-2.0), revision adc7f1241b42e322a6451854ab7e4b4c146bf78a.
Original source: lean/OAI/NumberTheory/PiExponent/Cohomology/AmpleLineCohomology.lean
Changes: Convert module/import declarations to the Lean 4.34 public module format.
See ../THIRD_PARTY_NOTICES.txt for provenance and the recorded changes.
-/

namespace OAI

namespace PiExponent.NumericalAmpleness
noncomputable section
open AlgebraicGeometry CategoryTheory
open PiExponentSeshadri.Geometry
variable {X : Scheme.{0}}
theorem line_cohomology_finite_of_ample_all
    (p : X ⟶ Spec (CommRingCat.of ℂ)) [IsProper p]
    (H : LineBundle X) (hH : H.IsAmple) (L : LineBundle X) (q : ℕ) :
    letI := Module.compHom (cohomology L.sheaf q) (baseScalars p)
    FiniteDimensional ℂ (cohomology L.sheaf q) := by
  cases isEmpty_or_nonempty X with
  | inr hX =>
    let := hX
    let := GeometrySupport.LineBundleCoherent.lineBundle_isFinitePresentation L
    exact AmpleCohomologyFinite.cohomology_finite_of_ample p H hH L.sheaf q
  | inl hX =>
    let := hX
    let := Module.compHom (cohomology L.sheaf q) (baseScalars p)
    let M := (Scheme.Modules.pushforward (𝟙 X)).obj L.sheaf
    let := Module.compHom (cohomology M q) (baseScalars p)
    let : FiniteDimensional ℂ (cohomology M q) :=
      PiExponentSeshadri.FiniteSupport.finite_line_pushforward_finiteDimensional (𝟙 X) p L q
    let e := PiExponent.ClosedImmersionSerreTransfer.cohomologyLinearEquiv (𝟙 X) p L.sheaf q
    exact FiniteDimensional.of_surjective e.symm.toLinearMap e.symm.surjective
end
end PiExponent.NumericalAmpleness

end OAI
end Source0707

-- Source: OAI/NumberTheory/PiExponent/Cohomology/MixedEulerCartier.lean
section Source0708
-- Modified in this edition: unused plain lemmas removed; see reduction.json.
/-
Modification notice for the LogTwo project.
Derived from openai/math (Apache-2.0), revision adc7f1241b42e322a6451854ab7e4b4c146bf78a.
Original source: lean/OAI/NumberTheory/PiExponent/Cohomology/MixedEulerCartier.lean
Changes: Convert module/import declarations to the Lean 4.34 public module format.
See ../THIRD_PARTY_NOTICES.txt for provenance and the recorded changes.
-/

namespace OAI

namespace PiExponent.NumericalAmpleness
noncomputable section
open AlgebraicGeometry CategoryTheory TopologicalSpace
open PiExponentSeshadri.Geometry PiExponentSeshadri.Projective
open PiExponent.SectionZeroIdeal PiExponent.ProjectiveO1
variable {X : Scheme.{0}}

end
end PiExponent.NumericalAmpleness

end OAI
end Source0708

-- Source: OAI/NumberTheory/PiExponent/Cohomology/MixedEulerCartierAmple.lean
section Source0709
/-
Modification notice for the LogTwo project.
Derived from openai/math (Apache-2.0), revision adc7f1241b42e322a6451854ab7e4b4c146bf78a.
Original source: lean/OAI/NumberTheory/PiExponent/Cohomology/MixedEulerCartierAmple.lean
Changes: Convert module/import declarations to the Lean 4.34 public module format.
See ../THIRD_PARTY_NOTICES.txt for provenance and the recorded changes.
-/

namespace OAI

namespace PiExponent.NumericalAmpleness
noncomputable section
open AlgebraicGeometry CategoryTheory TopologicalSpace
open PiExponentSeshadri.Geometry PiExponentSeshadri.Projective
open PiExponent.SectionZeroIdeal PiExponent.ProjectiveO1
variable {X : Scheme.{0}}

theorem tensor_euler_difference_cartier_pair_of_ample
    (p : X ⟶ Spec (CommRingCat.of ℂ)) [IsProper p]
    (H : LineBundle X) (hH : H.IsAmple) (r : ℕ)
    (hdim : topologicalKrullDim X ≤ r)
    (L B M : LineBundle X)
    (s : GlobalSections X (L.tensor B).sheaf) (t : GlobalSections X B.sheaf)
    [Mono s] [Mono t] :
    eulerCharacteristic p r (L.tensor M).sheaf - eulerCharacteristic p r M.sheaf =
      eulerCharacteristic ((zeroIdeal (L.tensor B) s).subschemeι ≫ p) r
        (((L.tensor B).pullback (zeroIdeal (L.tensor B) s).subschemeι).tensor
          (M.pullback (zeroIdeal (L.tensor B) s).subschemeι)).sheaf -
      eulerCharacteristic ((zeroIdeal B t).subschemeι ≫ p) r
        (((B.tensor L).pullback (zeroIdeal B t).subschemeι).tensor
          (M.pullback (zeroIdeal B t).subschemeι)).sheaf := by
  let D := zeroIdeal (L.tensor B) s
  let E := zeroIdeal B t
  let jD := D.subschemeι
  let jE := E.subschemeι
  have hHD := LineBundle.IsAmple.pullback_closedImmersion H hH jD
  have hHE := LineBundle.IsAmple.pullback_closedImmersion H hH jE
  let e0 : (CartierEulerPair.source L M 0).sheaf ≅ M.sheaf :=
    moduleTensorUnit M.sheaf
  let e1 : (CartierEulerPair.source L M 1).sheaf ≅ (L.tensor M).sheaf :=
    moduleTensorIso (moduleTensorRightUnit L.sheaf) (Iso.refl M.sheaf)
  let em : (CartierEulerPair.middle L B M 0).sheaf ≅
      ((L.tensor B).tensor M).sheaf :=
    moduleTensorIso (Iso.refl _) e0
  let ee : (B.tensor (CartierEulerPair.source L M 1)).sheaf ≅
      ((B.tensor L).tensor M).sheaf :=
    moduleTensorIso (Iso.refl _) e1 ≪≫ (lineTensorAssoc B L M).symm
  have hv := CartierEulerPair.euler_difference p L B M s t 0 r
    (fun q _ => line_cohomology_finite_of_ample_all p H hH (CartierEulerPair.source L M 0) q)
    (fun q _ => line_cohomology_finite_of_ample_all p H hH (CartierEulerPair.source L M 1) q)
    (fun q _ => line_cohomology_finite_of_ample_all p H hH (CartierEulerPair.middle L B M 0) q)
    (fun q _ => line_cohomology_finite_of_ample_all (jD ≫ p) (H.pullback jD) hHD
      ((CartierEulerPair.middle L B M 0).pullback jD) q)
    (fun q _ => line_cohomology_finite_of_ample_all (jE ≫ p) (H.pullback jE) hHE
      ((B.tensor (CartierEulerPair.source L M 1)).pullback jE) q)
    (lineBundle_cohomology_zero_of_dimension_le r p H hH
      (CartierEulerPair.source L M 0) hdim (r+1) (by omega))
    (lineBundle_cohomology_zero_of_dimension_le r p H hH
      (CartierEulerPair.source L M 1) hdim (r+1) (by omega))
  rw [eulerCharacteristic_iso p e0 r, eulerCharacteristic_iso p e1 r] at hv
  have hD := eulerCharacteristic_iso (jD ≫ p)
    ((Scheme.Modules.pullback jD).mapIso em ≪≫
      PiExponentSeshadri.PullbackTensor.iso jD (L.tensor B) M) r
  have hE := eulerCharacteristic_iso (jE ≫ p)
    ((Scheme.Modules.pullback jE).mapIso ee ≪≫
      PiExponentSeshadri.PullbackTensor.iso jE (B.tensor L) M) r
  rw [hD, hE] at hv
  exact hv

end
end PiExponent.NumericalAmpleness

end OAI
end Source0709

-- Source: OAI/NumberTheory/PiExponent/Cohomology/MixedEulerAlgebra.lean
section Source0710
-- Modified in this edition: unused plain lemmas removed; see reduction.json.
/-
Modification notice for the LogTwo project.
Derived from openai/math (Apache-2.0), revision adc7f1241b42e322a6451854ab7e4b4c146bf78a.
Original source: lean/OAI/NumberTheory/PiExponent/Cohomology/MixedEulerAlgebra.lean
Changes: Convert module/import declarations to the Lean 4.34 public module format.
See ../THIRD_PARTY_NOTICES.txt for provenance and the recorded changes.
-/

namespace OAI

namespace PiExponent.NumericalAmpleness
noncomputable section
open AlgebraicGeometry CategoryTheory
open PiExponentSeshadri.Geometry
variable {X Y : Scheme.{0}}

def LineIsoInvariant (f : LineBundle X → ℤ) : Prop :=
  ∀ L M, (L.sheaf ≅ M.sheaf) → f L = f M

def tensorDifference (L : LineBundle X) (f : LineBundle X → ℤ) : LineBundle X → ℤ :=
  fun M => f (L.tensor M) - f M

def mixedDifference : List (LineBundle X) → (LineBundle X → ℤ) → (LineBundle X → ℤ)
  | [], f => f
  | L :: ls, f => tensorDifference L (mixedDifference ls f)

@[simp] theorem mixedDifference_nil (f : LineBundle X → ℤ) : mixedDifference [] f = f := rfl
@[simp] theorem mixedDifference_cons (L : LineBundle X) (ls : List (LineBundle X))
    (f : LineBundle X → ℤ) :
    mixedDifference (L :: ls) f = tensorDifference L (mixedDifference ls f) := rfl

def tensorTwistSwapIso (L B M : LineBundle X) :
    (L.tensor (B.tensor M)).sheaf ≅ (B.tensor (L.tensor M)).sheaf :=
  (lineTensorAssoc L B M).symm ≪≫
    moduleTensorIso (moduleTensorComm L.sheaf B.sheaf) (Iso.refl M.sheaf) ≪≫
      lineTensorAssoc B L M

theorem tensorDifference_sub (L : LineBundle X) (f g : LineBundle X → ℤ) :
    tensorDifference L (f - g) = tensorDifference L f - tensorDifference L g := by
  funext M
  simp only [tensorDifference, Pi.sub_apply]
  ring

theorem mixedDifference_sub (ls : List (LineBundle X)) (f g : LineBundle X → ℤ) :
    mixedDifference ls (f - g) = mixedDifference ls f - mixedDifference ls g := by
  induction ls with
  | nil => rfl
  | cons L ls ih => rw [mixedDifference_cons, ih, tensorDifference_sub]; rfl

@[simp] theorem mixedDifference_zero (ls : List (LineBundle X)) :
    mixedDifference ls (0 : LineBundle X → ℤ) = 0 := by
  induction ls with
  | nil => rfl
  | cons L ls ih =>
      rw [mixedDifference_cons, ih]
      funext M
      exact sub_self _

theorem LineIsoInvariant.tensorDifference {f : LineBundle X → ℤ} (hf : LineIsoInvariant f)
    (L : LineBundle X) : LineIsoInvariant (tensorDifference L f) := by
  intro M N e
  change f (L.tensor M) - f M = f (L.tensor N) - f N
  rw [hf (L.tensor M) (L.tensor N) (moduleTensorIso (Iso.refl L.sheaf) e), hf M N e]

theorem LineIsoInvariant.mixedDifference {f : LineBundle X → ℤ} (hf : LineIsoInvariant f)
    (ls : List (LineBundle X)) : LineIsoInvariant (mixedDifference ls f) := by
  induction ls with
  | nil => exact hf
  | cons L ls ih => exact ih.tensorDifference L

theorem LineIsoInvariant.tensorShift {f : LineBundle X → ℤ} (hf : LineIsoInvariant f)
    (B : LineBundle X) : LineIsoInvariant (fun M => f (B.tensor M)) := by
  intro M N e
  exact hf _ _ (moduleTensorIso (Iso.refl B.sheaf) e)

theorem LineIsoInvariant.pullback {g : LineBundle Y → ℤ} (hg : LineIsoInvariant g)
    (i : Y ⟶ X) : LineIsoInvariant (fun M => g (M.pullback i)) := by
  intro M N e
  exact hg _ _ ((Scheme.Modules.pullback i).mapIso e)

theorem tensorDifference_commute (L B : LineBundle X) (f : LineBundle X → ℤ)
    (hf : LineIsoInvariant f) :
    tensorDifference L (tensorDifference B f) = tensorDifference B (tensorDifference L f) := by
  funext M
  simp only [tensorDifference]
  rw [hf _ _ (tensorTwistSwapIso B L M)]
  ring

theorem mixedDifference_cons_commute (L : LineBundle X) (ls : List (LineBundle X))
    (f : LineBundle X → ℤ) (hf : LineIsoInvariant f) :
    mixedDifference (L :: ls) f = mixedDifference ls (tensorDifference L f) := by
  induction ls with
  | nil => rfl
  | cons B ls ih =>
      change tensorDifference L (tensorDifference B (mixedDifference ls f)) =
        tensorDifference B (mixedDifference ls (tensorDifference L f))
      rw [tensorDifference_commute L B _ (hf.mixedDifference ls)]
      exact congrArg (tensorDifference B) ih

theorem mixedDifference_tensorShift (ls : List (LineBundle X))
    (g : LineBundle X → ℤ) (hg : LineIsoInvariant g) (B M : LineBundle X) :
    mixedDifference ls (fun N => g (B.tensor N)) M = mixedDifference ls g (B.tensor M) := by
  induction ls generalizing M with
  | nil => rfl
  | cons L ls ih =>
      change mixedDifference ls (fun N => g (B.tensor N)) (L.tensor M) -
        mixedDifference ls (fun N => g (B.tensor N)) M =
          mixedDifference ls g (L.tensor (B.tensor M)) - mixedDifference ls g (B.tensor M)
      rw [ih, ih, (hg.mixedDifference ls) _ _ (tensorTwistSwapIso B L M)]

theorem mixedDifference_pullback (ls : List (LineBundle X)) (i : Y ⟶ X)
    (g : LineBundle Y → ℤ) (hg : LineIsoInvariant g) (M : LineBundle X) :
    mixedDifference ls (fun N => g (N.pullback i)) M =
      mixedDifference (ls.map (fun L => L.pullback i)) g (M.pullback i) := by
  induction ls generalizing M with
  | nil => rfl
  | cons L ls ih =>
      change mixedDifference ls (fun N => g (N.pullback i)) (L.tensor M) -
        mixedDifference ls (fun N => g (N.pullback i)) M =
          mixedDifference (ls.map (fun N => N.pullback i)) g
            ((L.pullback i).tensor (M.pullback i)) -
          mixedDifference (ls.map (fun N => N.pullback i)) g (M.pullback i)
      rw [ih, ih, (hg.mixedDifference _) _ _ (PiExponentSeshadri.PullbackTensor.iso i L M)]

theorem tensorDifference_tensor (A B : LineBundle X) (f : LineBundle X → ℤ)
    (hf : LineIsoInvariant f) :
    tensorDifference (A.tensor B) f =
      tensorDifference A f + tensorDifference B f + mixedDifference [A,B] f := by
  funext M
  simp only [tensorDifference, mixedDifference, Pi.add_apply]
  rw [hf ((A.tensor B).tensor M) (A.tensor (B.tensor M)) (lineTensorAssoc A B M),
    hf _ _ (tensorTwistSwapIso A B M)]
  ring

theorem mixedDifference_tensor_cons (A B : LineBundle X) (ls : List (LineBundle X))
    (f : LineBundle X → ℤ) (hf : LineIsoInvariant f) :
    mixedDifference (A.tensor B :: ls) f =
      mixedDifference (A :: ls) f + mixedDifference (B :: ls) f +
        mixedDifference (A :: B :: ls) f :=
  tensorDifference_tensor A B (mixedDifference ls f) (hf.mixedDifference ls)

theorem mixedDifference_tensor_cons_of_next_eq_zero (A B : LineBundle X)
    (ls : List (LineBundle X)) (f : LineBundle X → ℤ) (hf : LineIsoInvariant f)
    (hzero : mixedDifference (A :: B :: ls) f = 0) :
    mixedDifference (A.tensor B :: ls) f =
      mixedDifference (A :: ls) f + mixedDifference (B :: ls) f := by
  rw [mixedDifference_tensor_cons A B ls f hf, hzero, add_zero]

end
end PiExponent.NumericalAmpleness

end OAI
end Source0710

-- Source: OAI/NumberTheory/PiExponent/Cohomology/MixedEulerDimension.lean
section Source0711
-- Modified in this edition: unused plain lemmas removed; see reduction.json.
/-
Modification notice for the LogTwo project.
Derived from openai/math (Apache-2.0), revision adc7f1241b42e322a6451854ab7e4b4c146bf78a.
Original source: lean/OAI/NumberTheory/PiExponent/Cohomology/MixedEulerDimension.lean
Changes: Convert module/import declarations to the Lean 4.34 public module format.
See ../THIRD_PARTY_NOTICES.txt for provenance and the recorded changes.
-/

namespace OAI

namespace PiExponent.NumericalAmpleness
noncomputable section
open AlgebraicGeometry CategoryTheory TopologicalSpace
open PiExponentSeshadri.Geometry PiExponentSeshadri.Projective
open PiExponent.SectionZeroIdeal PiExponent.ProjectiveO1

def lineEuler {X : Scheme.{0}} (p : X ⟶ Spec (CommRingCat.of ℂ)) (r : ℕ)
    (M : LineBundle X) : ℤ := eulerCharacteristic p r M.sheaf

theorem lineEuler_isoInvariant {X : Scheme.{0}}
    (p : X ⟶ Spec (CommRingCat.of ℂ)) (r : ℕ) :
    LineIsoInvariant (lineEuler p r) := by
  intro L M e
  exact eulerCharacteristic_iso p e r

theorem mixedDifference_pullback_tensorShift_zero {X Y : Scheme.{0}}
    (ls : List (LineBundle X)) (i : Y ⟶ X) (g : LineBundle Y → ℤ)
    (hg : LineIsoInvariant g) (B : LineBundle Y)
    (hz : mixedDifference (ls.map (fun L => L.pullback i)) g = 0) :
    mixedDifference ls (fun M => g (B.tensor (M.pullback i))) = 0 := by
  funext M
  rw [mixedDifference_pullback ls i (fun N => g (B.tensor N)) (hg.tensorShift B) M,
    mixedDifference_tensorShift _ g hg B (M.pullback i), hz]
  rfl

end
end PiExponent.NumericalAmpleness

end OAI
end Source0711

-- Source: OAI/NumberTheory/PiExponent/Cohomology/MixedEulerAmpleDimension.lean
section Source0712
/-
Modification notice for the LogTwo project.
Derived from openai/math (Apache-2.0), revision adc7f1241b42e322a6451854ab7e4b4c146bf78a.
Original source: lean/OAI/NumberTheory/PiExponent/Cohomology/MixedEulerAmpleDimension.lean
Changes: Convert module/import declarations to the Lean 4.34 public module format.
See ../THIRD_PARTY_NOTICES.txt for provenance and the recorded changes.
-/

namespace OAI

namespace PiExponent.NumericalAmpleness
noncomputable section
open AlgebraicGeometry CategoryTheory TopologicalSpace
open PiExponentSeshadri.Geometry PiExponentSeshadri.Projective
open PiExponent.SectionZeroIdeal PiExponent.ProjectiveO1

theorem mixedDifference_lineEuler_of_ample_aux (d : ℕ) :
    ∀ {X : Scheme.{0}} [IsNoetherian X]
      (p : X ⟶ Spec (CommRingCat.of ℂ)) [IsProper p]
      (H : LineBundle X), H.IsAmple → ∀ r : ℕ, d ≤ r →
      topologicalKrullDim X ≤ d → ∀ ls : List (LineBundle X), ls.length = d+1 →
      mixedDifference ls (lineEuler p r) = 0 := by
  induction d with
  | zero =>
    intro X _ p _ H hH r hr hdim ls hlen
    cases ls with
    | nil => simp at hlen
    | cons L ls =>
      have hz : ls = [] := List.length_eq_zero_iff.mp (by simpa using hlen)
      subst ls
      funext M
      obtain ⟨e⟩ := lineBundle_trivial_of_dim_le_zero hdim L
      have he := eulerCharacteristic_iso p
        (moduleTensorIso e (Iso.refl M.sheaf) ≪≫ moduleTensorUnit M.sheaf) r
      change eulerCharacteristic p r (L.tensor M).sheaf - eulerCharacteristic p r M.sheaf = 0
      exact sub_eq_zero.mpr he
  | succ d ih =>
    intro X _ p _ H hH r hr hdim ls hlen
    cases ls with
    | nil => simp at hlen
    | cons L ls =>
      have hlen' : ls.length = d+1 := by simpa using hlen
      obtain ⟨B, s, t, hs, ht⟩ := exists_regular_twist_pair p H L hH
      let := hs
      let := ht
      let A := L.tensor B
      let D := zeroIdeal A s
      let E := zeroIdeal B t
      let jD := D.subschemeι
      let jE := E.subschemeι
      let : IsLocallyNoetherian D.subscheme := LocallyOfFiniteType.isLocallyNoetherian jD
      let : CompactSpace D.subscheme := QuasiCompact.compactSpace_of_compactSpace jD
      let : IsNoetherian D.subscheme := {}
      let : IsLocallyNoetherian E.subscheme := LocallyOfFiniteType.isLocallyNoetherian jE
      let : CompactSpace E.subscheme := QuasiCompact.compactSpace_of_compactSpace jE
      let : IsNoetherian E.subscheme := {}
      have hdD : topologicalKrullDim D.subscheme ≤ d :=
        regular_sectionZero_dimension_le A s d (by
          simpa only [Nat.cast_add, Nat.cast_one] using hdim)
      have hdE : topologicalKrullDim E.subscheme ≤ d :=
        regular_sectionZero_dimension_le B t d (by
          simpa only [Nat.cast_add, Nat.cast_one] using hdim)
      let g := lineEuler (jD ≫ p) r
      let h := lineEuler (jE ≫ p) r
      let g' (M : LineBundle D.subscheme) := g ((A.pullback jD).tensor M)
      let h' (M : LineBundle E.subscheme) := h (((B.tensor L).pullback jE).tensor M)
      have hg := lineEuler_isoInvariant (jD ≫ p) r
      have hh := lineEuler_isoInvariant (jE ≫ p) r
      have hDz : mixedDifference (ls.map (fun L => L.pullback jD)) g = 0 :=
        ih (jD ≫ p) (H.pullback jD)
          (LineBundle.IsAmple.pullback_closedImmersion H hH jD) r (by omega) hdD _
          (by simpa using hlen')
      have hEz : mixedDifference (ls.map (fun L => L.pullback jE)) h = 0 :=
        ih (jE ≫ p) (H.pullback jE)
          (LineBundle.IsAmple.pullback_closedImmersion H hH jE) r (by omega) hdE _
          (by simpa using hlen')
      have heq : tensorDifference L (lineEuler p r) =
          (fun M => g' (M.pullback jD)) - fun M => h' (M.pullback jE) := by
        funext M
        exact tensor_euler_difference_cartier_pair_of_ample p H hH r
          (hdim.trans (by exact_mod_cast hr)) L B M s t
      have hDzero := mixedDifference_pullback_tensorShift_zero ls jD g hg (A.pullback jD) hDz
      have hEzero := mixedDifference_pullback_tensorShift_zero ls jE h hh
        ((B.tensor L).pullback jE) hEz
      rw [mixedDifference_cons_commute L ls _ (lineEuler_isoInvariant p r),
        heq, mixedDifference_sub, hDzero, hEzero, sub_self]

theorem mixedDifference_lineEuler_of_ample {X : Scheme.{0}} [IsNoetherian X]
    (p : X ⟶ Spec (CommRingCat.of ℂ)) [IsProper p]
    (H : LineBundle X) (hH : H.IsAmple) (d : ℕ)
    (hdim : topologicalKrullDim X ≤ d)
    (ls : List (LineBundle X)) (hlen : ls.length = d+1) :
    mixedDifference ls (lineEuler p d) = 0 :=
  mixedDifference_lineEuler_of_ample_aux d p H hH d le_rfl hdim ls hlen

end
end PiExponent.NumericalAmpleness

end OAI
end Source0712

-- Source: OAI/NumberTheory/PiExponent/Cohomology/MixedEulerPolarization.lean
section Source0713
-- Modified in this edition: unused plain lemmas removed; see reduction.json.
/-
Modification notice for the LogTwo project.
Derived from openai/math (Apache-2.0), revision adc7f1241b42e322a6451854ab7e4b4c146bf78a.
Original source: lean/OAI/NumberTheory/PiExponent/Cohomology/MixedEulerPolarization.lean
Changes: Convert module/import declarations to the Lean 4.34 public module format.
See ../THIRD_PARTY_NOTICES.txt for provenance and the recorded changes.
-/

namespace OAI

namespace PiExponent.NumericalAmpleness
noncomputable section
open AlgebraicGeometry CategoryTheory
open PiExponentSeshadri.Geometry
variable {X : Scheme.{0}}

def structureLineBundle (X : Scheme.{0}) : LineBundle X where
  sheaf := structureSheaf X
  locallyRankOne _x :=
    ⟨⊤, trivial, ⟨Scheme.Modules.restrictUnitIso (⊤ : X.Opens).ι⟩⟩

def MixedDegreeLE (d : ℕ) (f : LineBundle X → ℤ) : Prop :=
  ∀ ls : List (LineBundle X), ls.length = d+1 → mixedDifference ls f = 0

theorem mixedDifference_perm {ls ks : List (LineBundle X)} (h : ls.Perm ks)
    (f : LineBundle X → ℤ) (hf : LineIsoInvariant f) :
    mixedDifference ls f = mixedDifference ks f := by
  induction h with
  | nil => rfl
  | cons L h ih => exact congrArg (tensorDifference L) ih
  | swap A B ls => exact tensorDifference_commute B A _ (hf.mixedDifference ls)
  | trans h₁ h₂ ih₁ ih₂ => exact ih₁.trans ih₂

theorem mixedDifference_iso_cons (A B : LineBundle X) (e : A.sheaf ≅ B.sheaf)
    (ls : List (LineBundle X)) (f : LineBundle X → ℤ) (hf : LineIsoInvariant f) :
    mixedDifference (A :: ls) f = mixedDifference (B :: ls) f := by
  funext M
  change mixedDifference ls f (A.tensor M) - mixedDifference ls f M =
    mixedDifference ls f (B.tensor M) - mixedDifference ls f M
  rw [(hf.mixedDifference ls) (A.tensor M) (B.tensor M)
    (moduleTensorIso e (Iso.refl M.sheaf))]

theorem mixedDifference_tensor_base_of_degree {d : ℕ} {f : LineBundle X → ℤ}
    (hf : MixedDegreeLE d f) (ls : List (LineBundle X)) (hlen : ls.length = d)
    (A M : LineBundle X) :
    mixedDifference ls f (A.tensor M) = mixedDifference ls f M := by
  have hz := congrFun (hf (A :: ls) (by simp [hlen])) M
  exact sub_eq_zero.mp hz

theorem mixedDifference_eq_structure_of_degree {d : ℕ} {f : LineBundle X → ℤ}
    (hf : LineIsoInvariant f) (hdegree : MixedDegreeLE d f)
    (ls : List (LineBundle X)) (hlen : ls.length = d) (M : LineBundle X) :
    mixedDifference ls f M = mixedDifference ls f (structureLineBundle X) := by
  have he := (hf.mixedDifference ls) (M.tensor (structureLineBundle X)) M
    (moduleTensorRightUnit M.sheaf)
  exact he.symm.trans
    (mixedDifference_tensor_base_of_degree hdegree ls hlen M (structureLineBundle X))

theorem mixedDifference_tensor_cons_of_degree {d : ℕ} {f : LineBundle X → ℤ}
    (hf : LineIsoInvariant f) (hdegree : MixedDegreeLE d f)
    (A B : LineBundle X) (ls : List (LineBundle X)) (hlen : ls.length + 1 = d) :
    mixedDifference (A.tensor B :: ls) f =
      mixedDifference (A :: ls) f + mixedDifference (B :: ls) f := by
  apply mixedDifference_tensor_cons_of_next_eq_zero A B ls f hf
  apply hdegree
  simp only [List.length_cons]
  omega

theorem mixedDifference_pow_zero_cons (L : LineBundle X) (ls : List (LineBundle X))
    (f : LineBundle X → ℤ) (hf : LineIsoInvariant f) :
    mixedDifference (L.pow 0 :: ls) f = 0 := by
  funext M
  change mixedDifference ls f ((L.pow 0).tensor M) - mixedDifference ls f M = 0
  rw [(hf.mixedDifference ls) ((L.pow 0).tensor M) M (moduleTensorUnit M.sheaf)]
  exact sub_self _

theorem mixedDifference_pow_cons_of_degree {d : ℕ} {f : LineBundle X → ℤ}
    (hf : LineIsoInvariant f) (hdegree : MixedDegreeLE d f)
    (L : LineBundle X) (n : ℕ) (ls : List (LineBundle X)) (hlen : ls.length + 1 = d) :
    mixedDifference (L.pow n :: ls) f = n • mixedDifference (L :: ls) f := by
  induction n with
  | zero => simpa only [zero_nsmul] using mixedDifference_pow_zero_cons L ls f hf
  | succ n ih =>
      rw [mixedDifference_iso_cons (L.pow (n+1)) (L.tensor (L.pow n)) (Iso.refl _) ls f hf,
        mixedDifference_tensor_cons_of_degree hf hdegree L (L.pow n) ls hlen, ih]
      rw [add_comm, succ_nsmul]

theorem mixedDifference_replicate_pow (L : LineBundle X) (f : LineBundle X → ℤ)
    (hf : LineIsoInvariant f) (k n : ℕ) :
    mixedDifference (List.replicate k L) f (L.pow n) =
      (fwdDiff (1 : ℕ))^[k] (fun j => f (L.pow j)) n := by
  induction k generalizing n with
  | zero => rfl
  | succ k ih =>
      rw [List.replicate_succ]
      change mixedDifference (List.replicate k L) f (L.tensor (L.pow n)) -
        mixedDifference (List.replicate k L) f (L.pow n) = _
      rw [(hf.mixedDifference _) (L.tensor (L.pow n)) (L.pow (n+1)) (Iso.refl _), ih, ih]
      rw [Function.iterate_succ_apply']
      rfl

def mixedTop (f : LineBundle X → ℤ) (ls : List (LineBundle X)) : ℤ :=
  mixedDifference ls f (structureLineBundle X)

theorem mixedTop_replicate (L : LineBundle X) (f : LineBundle X → ℤ)
    (hf : LineIsoInvariant f) (d : ℕ) :
    mixedTop f (List.replicate d L) =
      (fwdDiff (1 : ℕ))^[d] (fun n => f (L.pow n)) 0 := by
  rw [mixedTop, (hf.mixedDifference _) (structureLineBundle X) (L.pow 0) (Iso.refl _)]
  exact mixedDifference_replicate_pow L f hf d 0

theorem mixedDifference_replicate_tensor_append {d : ℕ} {f : LineBundle X → ℤ}
    (hf : LineIsoInvariant f) (hdegree : MixedDegreeLE d f)
    (A B : LineBundle X) (n : ℕ) (ls : List (LineBundle X))
    (hlen : n + ls.length = d) :
    mixedDifference (List.replicate n (A.tensor B) ++ ls) f =
      ∑ k ∈ Finset.range (n+1), n.choose k •
        mixedDifference (List.replicate k A ++ List.replicate (n-k) B ++ ls) f := by
  induction n generalizing ls with
  | zero => simp
  | succ n ih =>
      have hm (L : LineBundle X) :
          mixedDifference (L :: (List.replicate n (A.tensor B) ++ ls)) f =
            mixedDifference (List.replicate n (A.tensor B) ++ L :: ls) f :=
        mixedDifference_perm List.perm_middle.symm f hf
      rw [List.replicate_succ, List.cons_append,
        mixedDifference_tensor_cons_of_degree hf hdegree A B _ (by
          simp only [List.length_append, List.length_replicate]; omega), hm A, hm B,
        ih (A :: ls) (by simp only [List.length_cons]; omega),
        ih (B :: ls) (by simp only [List.length_cons]; omega)]
      rw [Finset.sum_choose_succ_nsmul
        (fun a b => mixedDifference (List.replicate a A ++ List.replicate b B ++ ls) f) n,
        add_comm]
      congr 1
      · apply Finset.sum_congr rfl
        intro k hk
        have hk' : k ≤ n := Nat.le_of_lt_succ (Finset.mem_range.mp hk)
        have he : n+1-k = (n-k)+1 := by omega
        congr 1
        apply mixedDifference_perm _ f hf
        rw [he, List.replicate_succ]
        simpa only [List.append_assoc, List.cons_append] using
          (List.perm_middle (a := B) (l₁ := List.replicate (n-k) B) (l₂ := ls)).append_left
            (List.replicate k A)
      · apply Finset.sum_congr rfl
        intro k hk
        congr 1
        apply mixedDifference_perm _ f hf
        simpa only [List.replicate_succ, List.cons_append, List.append_assoc] using
          (List.perm_middle (a := A)
            (l₁ := List.replicate k A ++ List.replicate (n-k) B) (l₂ := ls))

theorem mixedTop_tensor_binomial {d : ℕ} {f : LineBundle X → ℤ}
    (hf : LineIsoInvariant f) (hdegree : MixedDegreeLE d f) (A B : LineBundle X) :
    mixedTop f (List.replicate d (A.tensor B)) =
      ∑ k ∈ Finset.range (d+1), (d.choose k : ℤ) *
        mixedTop f (List.replicate k A ++ List.replicate (d-k) B) := by
  have he := congrFun (mixedDifference_replicate_tensor_append hf hdegree A B d [] (by simp))
    (structureLineBundle X)
  simpa only [List.append_nil, Finset.sum_apply, Pi.smul_apply, mixedTop, nsmul_eq_mul, Pi.mul_apply, Pi.natCast_apply] using he

theorem mixedDifference_replicate_pow_append {d : ℕ} {f : LineBundle X → ℤ}
    (hf : LineIsoInvariant f) (hdegree : MixedDegreeLE d f)
    (L : LineBundle X) (n k : ℕ) (ls : List (LineBundle X)) (hlen : k + ls.length = d) :
    mixedDifference (List.replicate k (L.pow n) ++ ls) f =
      n^k • mixedDifference (List.replicate k L ++ ls) f := by
  induction k generalizing ls with
  | zero => simp
  | succ k ih =>
      rw [List.replicate_succ, List.cons_append,
        mixedDifference_pow_cons_of_degree hf hdegree L n _ (by
          simp only [List.length_append, List.length_replicate]; omega)]
      rw [mixedDifference_perm
        (List.perm_middle (a := L) (l₁ := List.replicate k (L.pow n)) (l₂ := ls)).symm f hf,
        ih (L :: ls) (by simp only [List.length_cons]; omega)]
      rw [mixedDifference_perm
        (List.perm_middle (a := L) (l₁ := List.replicate k L) (l₂ := ls)) f hf,
        smul_smul, pow_succ']
      rfl

theorem mixedTop_two_powers {d : ℕ} {f : LineBundle X → ℤ}
    (hf : LineIsoInvariant f) (hdegree : MixedDegreeLE d f)
    (A B : LineBundle X) (a b k l : ℕ) (hlen : k+l=d) :
    mixedTop f (List.replicate k (A.pow a) ++ List.replicate l (B.pow b)) =
      (a : ℤ)^k * (b : ℤ)^l * mixedTop f (List.replicate k A ++ List.replicate l B) := by
  have he : mixedDifference (List.replicate k (A.pow a) ++ List.replicate l (B.pow b)) f =
      (a^k * b^l) • mixedDifference (List.replicate k A ++ List.replicate l B) f := by
    rw [mixedDifference_replicate_pow_append hf hdegree A a k _ (by simpa using hlen),
      mixedDifference_perm List.perm_append_comm f hf,
      mixedDifference_replicate_pow_append hf hdegree B b l _ (by
        simp only [List.length_replicate]; omega),
      mixedDifference_perm List.perm_append_comm f hf, smul_smul]
  have hev := congrFun he (structureLineBundle X)
  simpa only [Pi.smul_apply, mixedTop, nsmul_eq_mul, Pi.mul_apply, Pi.natCast_apply,
    Nat.cast_mul, Nat.cast_pow, mul_assoc] using hev

theorem mixedTop_tensor_powers_binomial {d : ℕ} {f : LineBundle X → ℤ}
    (hf : LineIsoInvariant f) (hdegree : MixedDegreeLE d f)
    (A B : LineBundle X) (a b : ℕ) :
    mixedTop f (List.replicate d ((A.pow a).tensor (B.pow b))) =
      ∑ k ∈ Finset.range (d+1), (d.choose k : ℤ) * (a : ℤ)^k * (b : ℤ)^(d-k) *
        mixedTop f (List.replicate k A ++ List.replicate (d-k) B) := by
  rw [mixedTop_tensor_binomial hf hdegree]
  apply Finset.sum_congr rfl
  intro k hk
  have hk' : k ≤ d := Nat.le_of_lt_succ (Finset.mem_range.mp hk)
  rw [mixedTop_two_powers hf hdegree A B a b k (d-k) (by omega)]
  ring

theorem mixedDifference_two_powers_append {d : ℕ} {f : LineBundle X → ℤ}
    (hf : LineIsoInvariant f) (hdegree : MixedDegreeLE d f)
    (A B : LineBundle X) (a b k l : ℕ) (ls : List (LineBundle X))
    (hlen : k+l+ls.length=d) :
    mixedDifference (List.replicate k (A.pow a) ++ List.replicate l (B.pow b) ++ ls) f =
      (a^k * b^l) • mixedDifference (List.replicate k A ++ List.replicate l B ++ ls) f := by
  have hswap (as bs : List (LineBundle X)) :
      mixedDifference (as ++ bs ++ ls) f = mixedDifference (bs ++ as ++ ls) f :=
    mixedDifference_perm (List.perm_append_comm.append_right ls) f hf
  rw [List.append_assoc,
    mixedDifference_replicate_pow_append hf hdegree A a k _ (by
      simp only [List.length_append, List.length_replicate]; omega),
    ← List.append_assoc, hswap,
    List.append_assoc,
    mixedDifference_replicate_pow_append hf hdegree B b l _ (by
      simp only [List.length_append, List.length_replicate]; omega),
    ← List.append_assoc, hswap, smul_smul]

theorem mixedTop_tensor_powers_binomial_append {d : ℕ} {f : LineBundle X → ℤ}
    (hf : LineIsoInvariant f) (hdegree : MixedDegreeLE d f)
    (A B : LineBundle X) (a b n : ℕ) (ls : List (LineBundle X))
    (hlen : n+ls.length=d) :
    mixedTop f (List.replicate n ((A.pow a).tensor (B.pow b)) ++ ls) =
      ∑ k ∈ Finset.range (n+1), (n.choose k : ℤ) * (a : ℤ)^k * (b : ℤ)^(n-k) *
        mixedTop f (List.replicate k A ++ List.replicate (n-k) B ++ ls) := by
  have hsum := congrFun
    (mixedDifference_replicate_tensor_append hf hdegree (A.pow a) (B.pow b) n ls hlen)
    (structureLineBundle X)
  change mixedDifference _ f (structureLineBundle X) = _
  rw [hsum]
  simp only [Finset.sum_apply]
  apply Finset.sum_congr rfl
  intro k hk
  have hk' : k ≤ n := Nat.le_of_lt_succ (Finset.mem_range.mp hk)
  rw [mixedDifference_two_powers_append hf hdegree A B a b k (n-k) ls (by omega)]
  simp only [Pi.smul_apply, mixedTop, nsmul_eq_mul, Pi.mul_apply, Nat.cast_mul, Nat.cast_pow,
    Pi.pow_apply, Pi.natCast_apply]
  ring

end
end PiExponent.NumericalAmpleness

end OAI
end Source0713

-- Source: OAI/NumberTheory/PiExponent/Cohomology/MixedEulerRestriction.lean
section Source0714
/-
Modification notice for the LogTwo project.
Derived from openai/math (Apache-2.0), revision adc7f1241b42e322a6451854ab7e4b4c146bf78a.
Original source: lean/OAI/NumberTheory/PiExponent/Cohomology/MixedEulerRestriction.lean
Changes: Convert module/import declarations to the Lean 4.34 public module format.
See ../THIRD_PARTY_NOTICES.txt for provenance and the recorded changes.
-/

namespace OAI

namespace PiExponent.NumericalAmpleness
noncomputable section
open AlgebraicGeometry CategoryTheory TopologicalSpace
open PiExponentSeshadri.Geometry
open PiExponent.SectionZeroIdeal
variable {X : Scheme.{0}}

theorem tensor_euler_difference_regular_section
    (p : X ⟶ Spec (CommRingCat.of ℂ)) [IsProper p]
    (H : LineBundle X) (hH : H.IsAmple) (d : ℕ)
    (hdim : topologicalKrullDim X ≤ d+1)
    (A M : LineBundle X) (s : GlobalSections X A.sheaf) [Mono s] :
    lineEuler p (d+1) (A.tensor M) - lineEuler p (d+1) M =
      lineEuler ((zeroIdeal A s).subschemeι ≫ p) d
        ((A.pullback (zeroIdeal A s).subschemeι).tensor
          (M.pullback (zeroIdeal A s).subschemeι)) := by
  let D := zeroIdeal A s
  let j := D.subschemeι
  have hHD := LineBundle.IsAmple.pullback_closedImmersion H hH j
  have hdimD := regular_sectionZero_dimension_le A s d hdim
  let e0 : ((A.pow 0).tensor M).sheaf ≅ M.sheaf := moduleTensorUnit M.sheaf
  let e1 : ((A.pow 1).tensor M).sheaf ≅ (A.tensor M).sheaf :=
    moduleTensorIso (moduleTensorRightUnit A.sheaf) (Iso.refl M.sheaf)
  have he := regular_mixedCartierPower_euler_difference p A M s 0 (d+1)
    (fun q _ => line_cohomology_finite_of_ample_all p H hH ((A.pow 0).tensor M) q)
    (fun q _ => line_cohomology_finite_of_ample_all p H hH ((A.pow 1).tensor M) q)
    (fun q _ => line_cohomology_finite_of_ample_all (j ≫ p) (H.pullback j) hHD
      (((A.pow 1).tensor M).pullback j) q)
    (lineBundle_cohomology_zero_of_dimension_le (d+1) p H hH ((A.pow 0).tensor M)
      (by simpa only [Nat.cast_add, Nat.cast_one] using hdim) (d+1+1) (by omega))
    (lineBundle_cohomology_zero_of_dimension_le d (j ≫ p) (H.pullback j) hHD
      (((A.pow 1).tensor M).pullback j) hdimD (d+1) (by omega))
  rw [eulerCharacteristic_iso p e0 (d+1), eulerCharacteristic_iso p e1 (d+1)] at he
  have hR := eulerCharacteristic_iso (j ≫ p)
    ((Scheme.Modules.pullback j).mapIso e1 ≪≫ PiExponentSeshadri.PullbackTensor.iso j A M) d
  simp only [Nat.add_sub_cancel, Nat.zero_add] at he
  exact he.trans hR

theorem mixedDifference_cartier_restriction
    (p : X ⟶ Spec (CommRingCat.of ℂ)) [IsProper p]
    (H : LineBundle X) (hH : H.IsAmple) (d : ℕ)
    (hdim : topologicalKrullDim X ≤ d+1)
    (A : LineBundle X) (s : GlobalSections X A.sheaf) [Mono s]
    (ls : List (LineBundle X)) (M : LineBundle X) :
    mixedDifference (A :: ls) (lineEuler p (d+1)) M =
      mixedDifference (ls.map (fun L => L.pullback (zeroIdeal A s).subschemeι))
        (lineEuler ((zeroIdeal A s).subschemeι ≫ p) d)
        ((A.pullback (zeroIdeal A s).subschemeι).tensor
          (M.pullback (zeroIdeal A s).subschemeι)) := by
  let j := (zeroIdeal A s).subschemeι
  let g := lineEuler (j ≫ p) d
  have hg := lineEuler_isoInvariant (j ≫ p) d
  have he : tensorDifference A (lineEuler p (d+1)) =
      fun N => g ((A.pullback j).tensor (N.pullback j)) := by
    funext N
    exact tensor_euler_difference_regular_section p H hH d hdim A N s
  rw [mixedDifference_cons_commute A ls _ (lineEuler_isoInvariant p (d+1)), he,
    mixedDifference_pullback ls j _ (hg.tensorShift (A.pullback j)) M,
    mixedDifference_tensorShift _ g hg (A.pullback j) (M.pullback j)]

theorem mixedTop_cartier_restriction [IsNoetherian X]
    (p : X ⟶ Spec (CommRingCat.of ℂ)) [IsProper p]
    (H : LineBundle X) (hH : H.IsAmple) (d : ℕ)
    (hdim : topologicalKrullDim X ≤ d+1)
    (A : LineBundle X) (s : GlobalSections X A.sheaf) [Mono s]
    (ls : List (LineBundle X)) (hlen : ls.length = d) :
    mixedTop (lineEuler p (d+1)) (A :: ls) =
      mixedTop (lineEuler ((zeroIdeal A s).subschemeι ≫ p) d)
        (ls.map (fun L => L.pullback (zeroIdeal A s).subschemeι)) := by
  let D := zeroIdeal A s
  let j := D.subschemeι
  let : IsLocallyNoetherian D.subscheme := LocallyOfFiniteType.isLocallyNoetherian j
  let : CompactSpace D.subscheme := QuasiCompact.compactSpace_of_compactSpace j
  let : IsNoetherian D.subscheme := {}
  have hHD := LineBundle.IsAmple.pullback_closedImmersion H hH j
  have hdimD := regular_sectionZero_dimension_le A s d hdim
  have hdeg : MixedDegreeLE d (lineEuler (j ≫ p) d) :=
    mixedDifference_lineEuler_of_ample (j ≫ p) (H.pullback j) hHD d hdimD
  unfold mixedTop
  rw [mixedDifference_cartier_restriction p H hH d hdim A s ls]
  exact mixedDifference_eq_structure_of_degree (lineEuler_isoInvariant (j ≫ p) d)
    hdeg _ (by simpa using hlen) _

theorem mixedTop_power_cartier_restriction [IsNoetherian X]
    (p : X ⟶ Spec (CommRingCat.of ℂ)) [IsProper p]
    (H : LineBundle X) (hH : H.IsAmple) (d : ℕ)
    (hdim : topologicalKrullDim X ≤ d+1)
    (A : LineBundle X) (n : ℕ) (s : GlobalSections X (A.pow n).sheaf) [Mono s]
    (ls : List (LineBundle X)) (hlen : ls.length = d) :
    (n : ℤ) * mixedTop (lineEuler p (d+1)) (A :: ls) =
      mixedTop (lineEuler ((zeroIdeal (A.pow n) s).subschemeι ≫ p) d)
        (ls.map (fun L => L.pullback (zeroIdeal (A.pow n) s).subschemeι)) := by
  have hdegree : MixedDegreeLE (d+1) (lineEuler p (d+1)) :=
    mixedDifference_lineEuler_of_ample p H hH (d+1)
      (by simpa only [Nat.cast_add, Nat.cast_one] using hdim)
  have he := congrFun (mixedDifference_pow_cons_of_degree (lineEuler_isoInvariant p (d+1))
    hdegree A n ls (by omega)) (structureLineBundle X)
  have hscale : mixedTop (lineEuler p (d+1)) (A.pow n :: ls) =
      (n : ℤ) * mixedTop (lineEuler p (d+1)) (A :: ls) := by
    simpa only [Pi.smul_apply, nsmul_eq_mul, mixedTop, Pi.mul_apply, Pi.natCast_apply] using he
  rw [← hscale]
  exact mixedTop_cartier_restriction p H hH d hdim (A.pow n) s ls hlen

end
end PiExponent.NumericalAmpleness

end OAI
end Source0714

-- Source: OAI/NumberTheory/PiExponent/Cohomology/MixedEulerPositivity.lean
section Source0715
/-
Modification notice for the LogTwo project.
Derived from openai/math (Apache-2.0), revision adc7f1241b42e322a6451854ab7e4b4c146bf78a.
Original source: lean/OAI/NumberTheory/PiExponent/Cohomology/MixedEulerPositivity.lean
Changes: Convert module/import declarations to the Lean 4.34 public module format.
See ../THIRD_PARTY_NOTICES.txt for provenance and the recorded changes.
-/

namespace OAI

namespace PiExponent.NumericalAmpleness
noncomputable section
open AlgebraicGeometry CategoryTheory TopologicalSpace
open PiExponentSeshadri.Geometry
open PiExponent.SectionZeroIdeal

theorem exists_positive_power_regular_section {X : Scheme.{0}} [IsNoetherian X]
    (p : X ⟶ Spec (CommRingCat.of ℂ)) (A : LineBundle X) (hA : A.IsAmple) :
    ∃ n : ℕ, 0 < n ∧ ∃ s : GlobalSections X (A.pow n).sheaf, Mono s := by
  obtain ⟨N, hN⟩ := GeneratorsSectionCover.ample_eventual_fin_section_cover A hA
  obtain ⟨k, s, hs⟩ := hN (N+1) (by omega)
  obtain ⟨t, ht⟩ := exists_mono_section_of_finite_cover p (A.pow (N+1)) s hs
  exact ⟨N+1, by omega, t, ht⟩

theorem mixedTop_pos_of_ample_aux (d : ℕ) :
    ∀ {X : Scheme.{0}} [IsNoetherian X] [Nonempty X]
      (p : X ⟶ Spec (CommRingCat.of ℂ)) [IsProper p]
      (H : LineBundle X), H.IsAmple → topologicalKrullDim X = d →
      ∀ ls : List (LineBundle X), ls.length = d →
      (∀ L ∈ ls, L.IsAmple) → 0 < mixedTop (lineEuler p d) ls := by
  induction d with
  | zero =>
    intro X _ _ p _ H hH hdim ls hlen hamp
    have hz : ls = [] := List.length_eq_zero_iff.mp hlen
    subst ls
    let : Finite X := finite_of_dim_le_zero hdim.le
    exact CurveDegree.finite_nonempty_euler_pos p 0
  | succ d ih =>
    intro X _ _ p _ H hH hdim ls hlen hamp
    cases ls with
    | nil => simp at hlen
    | cons A ls =>
      have hlen' : ls.length = d := by simpa using hlen
      have hA : A.IsAmple := hamp A (by simp)
      obtain ⟨n, hn, s, hs⟩ := exists_positive_power_regular_section p A hA
      let := hs
      have hAn : (A.pow n).IsAmple := hA.pow n hn
      let D := zeroIdeal (A.pow n) s
      let j := D.subschemeι
      have hd := regular_ample_sectionZero_dimension p (A.pow n) hAn s d hdim
      let : Nonempty D.subscheme := hd.1
      let : IsLocallyNoetherian D.subscheme := LocallyOfFiniteType.isLocallyNoetherian j
      let : CompactSpace D.subscheme := QuasiCompact.compactSpace_of_compactSpace j
      let : IsNoetherian D.subscheme := {}
      have hHD := LineBundle.IsAmple.pullback_closedImmersion H hH j
      have hpos := ih (j ≫ p) (H.pullback j) hHD hd.2
        (ls.map (fun L => L.pullback j)) (by simpa using hlen') (by
          intro L hL
          obtain ⟨M, hM, rfl⟩ := List.mem_map.mp hL
          exact LineBundle.IsAmple.pullback_closedImmersion M (hamp M (by simp [hM])) j)
      have hrestrict := mixedTop_cartier_restriction p H hH d
        (by simpa only [Nat.cast_add, Nat.cast_one] using hdim.le)
        (A.pow n) s ls hlen'
      have hdeg : MixedDegreeLE (d+1) (lineEuler p (d+1)) :=
        mixedDifference_lineEuler_of_ample p H hH (d+1) hdim.le
      have hscale := congrFun (mixedDifference_pow_cons_of_degree
        (lineEuler_isoInvariant p (d+1)) hdeg A n ls (by omega)) (structureLineBundle X)
      have he : mixedTop (lineEuler p (d+1)) (A.pow n :: ls) =
          (n : ℤ) * mixedTop (lineEuler p (d+1)) (A :: ls) := by
        simpa only [Pi.smul_apply, nsmul_eq_mul, mixedTop, Pi.mul_apply, Pi.natCast_apply] using hscale
      have hmul : 0 < (n : ℤ) * mixedTop (lineEuler p (d+1)) (A :: ls) := by
        rw [← he, hrestrict]
        exact hpos
      exact (mul_pos_iff_of_pos_left (by exact_mod_cast hn : (0 : ℤ) < n)).mp hmul

theorem mixedTop_pos_of_ample {X : Scheme.{0}} [IsNoetherian X] [Nonempty X]
    (p : X ⟶ Spec (CommRingCat.of ℂ)) [IsProper p]
    (H : LineBundle X) (hH : H.IsAmple) (d : ℕ)
    (hdim : topologicalKrullDim X = d)
    (ls : List (LineBundle X)) (hlen : ls.length = d) (hamp : ∀ L ∈ ls, L.IsAmple) :
    0 < mixedTop (lineEuler p d) ls :=
  mixedTop_pos_of_ample_aux d p H hH hdim ls hlen hamp

theorem topEuler_pos_of_ample {X : Scheme.{0}} [IsNoetherian X] [Nonempty X]
    (p : X ⟶ Spec (CommRingCat.of ℂ)) [IsProper p]
    (A : LineBundle X) (hA : A.IsAmple) (d : ℕ)
    (hdim : topologicalKrullDim X = d) :
    0 < (fwdDiff (1 : ℕ))^[d] (fun n => eulerCharacteristic p d (A.pow n).sheaf) 0 := by
  have h := mixedTop_pos_of_ample p A hA d hdim (List.replicate d A) (by simp)
    (by intro L hL; obtain ⟨_, rfl⟩ := List.mem_replicate.mp hL; exact hA)
  rwa [mixedTop_replicate A _ (lineEuler_isoInvariant p d) d] at h

end
end PiExponent.NumericalAmpleness

end OAI
end Source0715

-- Source: OAI/NumberTheory/PiExponent/Geometry/GeneralCartierDegreeLength.lean
section Source0716
/-
Modification notice for the LogTwo project.
Derived from openai/math (Apache-2.0), revision adc7f1241b42e322a6451854ab7e4b4c146bf78a.
Original source: lean/OAI/NumberTheory/PiExponent/Geometry/GeneralCartierDegreeLength.lean
Changes: Convert module/import declarations to the Lean 4.34 public module format.
See ../THIRD_PARTY_NOTICES.txt for provenance and the recorded changes.
-/

namespace OAI

noncomputable section
open CategoryTheory AlgebraicGeometry TopologicalSpace
open PiExponentSeshadri.Geometry PiExponentSeshadri.Frames

namespace PiExponent.GeneralCartierDegreeLength

theorem cartier_euler_difference_eq_sum_local_lengths
    {X : Scheme.{0}}
    (p : X ⟶ Spec (CommRingCat.of ℂ)) [IsProper p]
    (M N : LineBundle X) (φ : M.sheaf ⟶ N.sheaf) [Mono φ]
    (I : X.IdealSheafData) [Finite I.subscheme]
    (heq : ∀ x : X, ∃ U : X.affineOpens, x ∈ U.1 ∧
      ∃ e : M.sheaf.restrict U.1.ι ≅ O U.1.toScheme,
      ∃ d : N.sheaf.restrict U.1.ι ≅ O U.1.toScheme,
        I.ideal U = Ideal.span {(U.1.topIso.hom
          (endValue (e.inv ≫ (Scheme.Modules.restrictFunctor U.1.ι).map φ ≫ d.hom)))})
    (hfiniteM : ∀ n ≤ 1, letI := Module.compHom (cohomology M.sheaf n) (baseScalars p)
      FiniteDimensional ℂ (cohomology M.sheaf n))
    (hfiniteN : ∀ n ≤ 1, letI := Module.compHom (cohomology N.sheaf n) (baseScalars p)
      FiniteDimensional ℂ (cohomology N.sheaf n))
    [Subsingleton (cohomology M.sheaf 2)] :
    letI : Fintype I.subscheme := Fintype.ofFinite _
    eulerCharacteristic p 1 N.sheaf - eulerCharacteristic p 1 M.sheaf =
      ∑ x : I.subscheme,
        ((Module.length (I.subscheme.presheaf.stalk x)
          (I.subscheme.presheaf.stalk x)).toNat : ℤ) := by
  let : Fintype I.subscheme := Fintype.ofFinite _
  obtain ⟨hz, hseq⟩ := PiExponentSeshadri.CartierSequence.exact p M N φ I heq
  have hfiniteZ (n : ℕ) (_hn : n ≤ 1) :=
    PiExponentSeshadri.FiniteSupport.finite_line_pushforward_finiteDimensional
      I.subschemeι p (N.pullback I.subschemeι) n
  have h := eulerCharacteristic_add p hseq 1 hfiniteM hfiniteN hfiniteZ
  have hdiff : eulerCharacteristic p 1 N.sheaf - eulerCharacteristic p 1 M.sheaf =
      eulerCharacteristic p 1
        ((Scheme.Modules.pushforward I.subschemeι).obj
          ((Scheme.Modules.pullback I.subschemeι).obj N.sheaf)) := by
    exact sub_eq_iff_eq_add.mpr (by simpa [add_comm] using h)
  exact hdiff.trans
    (PiExponentSeshadri.FiniteSupport.finite_line_euler_eq_sum_stalk_lengths
      I.subschemeι p (N.pullback I.subschemeι) 1)

theorem finite_zeroIdeal_of_mono {X : Scheme.{0}}
    (p : X ⟶ Spec (CommRingCat.of ℂ)) [IsProper p]
    (hd : topologicalKrullDim X ≤ 1)
    (L : LineBundle X) (s : GlobalSections X L.sheaf) [Mono s] :
    Finite (PiExponent.SectionZeroIdeal.zeroIdeal L s).subscheme := by
  let I := PiExponent.SectionZeroIdeal.zeroIdeal L s
  let q := I.subschemeι ≫ p
  let : IsLocallyNoetherian I.subscheme := LocallyOfFiniteType.isLocallyNoetherian q
  let : CompactSpace I.subscheme := QuasiCompact.compactSpace_of_compactSpace q
  let : IsNoetherian I.subscheme := {}
  exact PiExponent.NumericalAmpleness.finite_of_dim_le_zero
    (PiExponent.NumericalAmpleness.regular_sectionZero_dimension_le L s 0 (by simpa using hd))

theorem regular_section_tensor_euler_eq_sum_local_lengths {X : Scheme.{0}}
    (p : X ⟶ Spec (CommRingCat.of ℂ)) [IsProper p]
    (hd : topologicalKrullDim X ≤ 1)
    (L M : LineBundle X) (s : GlobalSections X L.sheaf) [Mono s]
    (hfiniteM : ∀ n ≤ 1, letI := Module.compHom (cohomology M.sheaf n) (baseScalars p)
      FiniteDimensional ℂ (cohomology M.sheaf n))
    (hfiniteLM : ∀ n ≤ 1, letI := Module.compHom (cohomology (L.tensor M).sheaf n) (baseScalars p)
      FiniteDimensional ℂ (cohomology (L.tensor M).sheaf n))
    [Subsingleton (cohomology M.sheaf 2)] :
    letI : Finite (PiExponent.SectionZeroIdeal.zeroIdeal L s).subscheme :=
      finite_zeroIdeal_of_mono p hd L s
    letI : Fintype (PiExponent.SectionZeroIdeal.zeroIdeal L s).subscheme := Fintype.ofFinite _
    eulerCharacteristic p 1 (L.tensor M).sheaf - eulerCharacteristic p 1 M.sheaf =
      ∑ x : (PiExponent.SectionZeroIdeal.zeroIdeal L s).subscheme,
        ((Module.length
          ((PiExponent.SectionZeroIdeal.zeroIdeal L s).subscheme.presheaf.stalk x)
          ((PiExponent.SectionZeroIdeal.zeroIdeal L s).subscheme.presheaf.stalk x)).toNat : ℤ) := by
  let I := PiExponent.SectionZeroIdeal.zeroIdeal L s
  let : Finite I.subscheme := finite_zeroIdeal_of_mono p hd L s
  let : Fintype I.subscheme := Fintype.ofFinite _
  let φ := PiExponent.CartierPowerFrames.sectionMultiplyLeft L.sheaf M.sheaf s
  let : Mono (moduleTensorMap s (𝟙 M.sheaf)) := moduleTensorMap_mono s M
  have hmono : Mono φ := mono_comp _ _
  refine @cartier_euler_difference_eq_sum_local_lengths X p inferInstance M (L.tensor M)
    φ hmono I inferInstance ?_ hfiniteM hfiniteLM inferInstance
  intro x
  obtain ⟨U,hx,⟨e⟩,⟨f⟩⟩ := common_affine_frames L M x
  refine ⟨U,hx,f,PiExponent.CartierPowerFrames.tensorFrame L.sheaf M.sheaf U.1 e f,?_⟩
  exact (PiExponent.SectionZeroIdeal.zeroIdeal_on_frame L s U e).trans
    (PiExponent.CartierPowerFrames.tensor_multiply_ideal L.sheaf M.sheaf s U e f).symm

end PiExponent.GeneralCartierDegreeLength

end

end OAI
end Source0716

-- Source: OAI/NumberTheory/PiExponent/Cohomology/CurveRegularEuler.lean
section Source0717
/-
Modification notice for the LogTwo project.
Derived from openai/math (Apache-2.0), revision adc7f1241b42e322a6451854ab7e4b4c146bf78a.
Original source: lean/OAI/NumberTheory/PiExponent/Cohomology/CurveRegularEuler.lean
Changes: Convert module/import declarations to the Lean 4.34 public module format.
See ../THIRD_PARTY_NOTICES.txt for provenance and the recorded changes.
-/

namespace OAI

namespace PiExponent.CurveCycle
noncomputable section
open AlgebraicGeometry CategoryTheory TopologicalSpace
open PiExponentSeshadri.Geometry

theorem regular_section_tensor_euler_eq_lengths {X : Scheme.{0}} [Nonempty X]
    (p : X ⟶ Spec (CommRingCat.of ℂ)) [IsProper p]
    (hd : topologicalKrullDim X ≤ 1)
    (H : LineBundle X) (hH : H.IsAmple)
    (L M : LineBundle X) (s : GlobalSections X L.sheaf) [Mono s] :
    letI : Finite (SectionZeroIdeal.zeroIdeal L s).subscheme :=
      GeneralCartierDegreeLength.finite_zeroIdeal_of_mono p hd L s
    letI : Fintype (SectionZeroIdeal.zeroIdeal L s).subscheme := Fintype.ofFinite _
    eulerCharacteristic p 1 (L.tensor M).sheaf - eulerCharacteristic p 1 M.sheaf =
      ∑ x : (SectionZeroIdeal.zeroIdeal L s).subscheme,
        ((Module.length
          ((SectionZeroIdeal.zeroIdeal L s).subscheme.presheaf.stalk x)
          ((SectionZeroIdeal.zeroIdeal L s).subscheme.presheaf.stalk x)).toNat : ℤ) := by
  let : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian p
  let := GeometrySupport.LineBundleCoherent.lineBundle_isFinitePresentation M
  let := GeometrySupport.LineBundleCoherent.lineBundle_isFinitePresentation (L.tensor M)
  let : Subsingleton (cohomology M.sheaf 2) := ⟨fun a b =>
    (NumericalAmpleness.lineBundle_cohomology_zero_of_dimension_le 1 p H hH M hd
      2 (by omega) a).trans
    (NumericalAmpleness.lineBundle_cohomology_zero_of_dimension_le 1 p H hH M hd
      2 (by omega) b).symm⟩
  exact GeneralCartierDegreeLength.regular_section_tensor_euler_eq_sum_local_lengths
    p hd L M s
    (fun q _ => AmpleCohomologyFinite.cohomology_finite_of_ample p H hH M.sheaf q)
    (fun q _ => AmpleCohomologyFinite.cohomology_finite_of_ample p H hH (L.tensor M).sheaf q)

end
end PiExponent.CurveCycle

end OAI
end Source0717

-- Source: OAI/NumberTheory/PiExponent/Cohomology/CurveTensorEuler.lean
section Source0718
/-
Modification notice for the LogTwo project.
Derived from openai/math (Apache-2.0), revision adc7f1241b42e322a6451854ab7e4b4c146bf78a.
Original source: lean/OAI/NumberTheory/PiExponent/Cohomology/CurveTensorEuler.lean
Changes: Convert module/import declarations to the Lean 4.34 public module format.
See ../THIRD_PARTY_NOTICES.txt for provenance and the recorded changes.
-/

namespace OAI

namespace PiExponent.CurveCycle
noncomputable section
open AlgebraicGeometry CategoryTheory TopologicalSpace
open PiExponentSeshadri.Geometry

theorem regular_tensor_euler_add {X : Scheme.{0}} [Nonempty X]
    (p : X ⟶ Spec (CommRingCat.of ℂ)) [IsProper p]
    (hd : topologicalKrullDim X ≤ 1) (H : LineBundle X) (hH : H.IsAmple)
    (L M : LineBundle X) (s : GlobalSections X L.sheaf) [Mono s] :
    eulerCharacteristic p 1 (L.tensor M).sheaf - eulerCharacteristic p 1 M.sheaf =
      eulerCharacteristic p 1 L.sheaf - eulerCharacteristic p 1 (structureSheaf X) := by
  have hM := regular_section_tensor_euler_eq_lengths p hd H hH L M s
  have hO := regular_section_tensor_euler_eq_lengths p hd H hH L (L.pow 0) s
  have he := eulerCharacteristic_iso p (moduleTensorRightUnit L.sheaf) 1
  change eulerCharacteristic p 1 (L.tensor (L.pow 0)).sheaf =
    eulerCharacteristic p 1 L.sheaf at he
  rw [he] at hO
  exact hM.trans hO.symm

theorem tensor_euler_add {X : Scheme.{0}} [IsNoetherian X] [Nonempty X]
    (p : X ⟶ Spec (CommRingCat.of ℂ)) [IsProper p]
    (hd : topologicalKrullDim X ≤ 1) (H : LineBundle X) (hH : H.IsAmple)
    (L M : LineBundle X) :
    eulerCharacteristic p 1 (L.tensor M).sheaf - eulerCharacteristic p 1 M.sheaf =
      eulerCharacteristic p 1 L.sheaf - eulerCharacteristic p 1 (structureSheaf X) := by
  obtain ⟨B,s,t,hs,ht⟩ := NumericalAmpleness.exists_regular_twist_pair p H L hH
  let : Mono s := hs
  let : Mono t := ht
  have h₁ := regular_tensor_euler_add p hd H hH (L.tensor B) M s
  have h₂ := regular_tensor_euler_add p hd H hH B L t
  have h₃ := regular_tensor_euler_add p hd H hH B (L.tensor M) t
  have hc := eulerCharacteristic_iso p (moduleTensorComm L.sheaf B.sheaf) 1
  change eulerCharacteristic p 1 (L.tensor B).sheaf =
    eulerCharacteristic p 1 (B.tensor L).sheaf at hc
  have ha := eulerCharacteristic_iso p
    (moduleTensorIso (moduleTensorComm L.sheaf B.sheaf) (Iso.refl M.sheaf) ≪≫
      lineTensorAssoc B L M) 1
  change eulerCharacteristic p 1 ((L.tensor B).tensor M).sheaf =
    eulerCharacteristic p 1 (B.tensor (L.tensor M)).sheaf at ha
  omega

end
end PiExponent.CurveCycle

end OAI
end Source0718

-- Source: OAI/NumberTheory/PiExponent/Geometry/CurveLocalAssociativity.lean
section Source0719
/-
Modification notice for the LogTwo project.
Derived from openai/math (Apache-2.0), revision adc7f1241b42e322a6451854ab7e4b4c146bf78a.
Original source: lean/OAI/NumberTheory/PiExponent/Geometry/CurveLocalAssociativity.lean
Changes: Convert module/import declarations to the Lean 4.34 public module format.
See ../THIRD_PARTY_NOTICES.txt for provenance and the recorded changes.
-/

namespace OAI

namespace PiExponent.CurveCycle
noncomputable section
open AlgebraicGeometry CategoryTheory TopologicalSpace
open PiExponentSeshadri.Geometry PiExponentSeshadri.Frames
open PiExponentJets.W28.LocalIntersection
open scoped nonZeroDivisors

theorem stalk_krullDimLE_one (X : Scheme.{0})
    (hd : topologicalKrullDim X ≤ 1) (x : X) :
    Ring.KrullDimLE 1 (X.presheaf.stalk x) := by
  apply Ring.krullDimLE_iff.mpr
  rw [← PrimeSpectrum.topologicalKrullDim_eq_ringKrullDim]
  exact (X.fromSpecStalk x).isEmbedding.isInducing.topologicalKrullDim_le.trans hd

theorem sectionGerm_nonZeroDivisor {X : Scheme.{0}}
    (L : LineBundle X) (s : GlobalSections X L.sheaf) [Mono s]
    (U : X.affineOpens) (e : L.sheaf.restrict U.1.ι ≅ O U.1.toScheme)
    (x : X) (hx : x ∈ U.1) :
    SectionZeroStalk.sectionGerm L s U e x hx ∈ nonZeroDivisors (X.presheaf.stalk x) := by
  let := X.presheaf.algebra_section_stalk (⟨x,hx⟩ : U.1)
  let := U.2.isLocalization_stalk (⟨x,hx⟩ : U.1)
  exact IsLocalization.nonZeroDivisors_le_comap
    ((U.2.primeIdealOf ⟨x,hx⟩).asIdeal.primeCompl) (X.presheaf.stalk x)
    (NumericalAmpleness.section_affine_coefficient_nonZeroDivisor L s U e)

theorem zero_stalk_length_eq_minimalPrimeCutSum {X : Scheme.{0}}
    [IsLocallyNoetherian X] (hd : topologicalKrullDim X ≤ 1)
    (L : LineBundle X) (s : GlobalSections X L.sheaf) [Mono s]
    (U : X.affineOpens) (e : L.sheaf.restrict U.1.ι ≅ O U.1.toScheme)
    (y : (SectionZeroIdeal.zeroIdeal L s).subscheme)
    (hy : (SectionZeroIdeal.zeroIdeal L s).subschemeι y ∈ U.1) :
    Module.length ((SectionZeroIdeal.zeroIdeal L s).subscheme.presheaf.stalk y)
      ((SectionZeroIdeal.zeroIdeal L s).subscheme.presheaf.stalk y) =
    minimalPrimeCutSum (⊥ : Ideal
      (X.presheaf.stalk ((SectionZeroIdeal.zeroIdeal L s).subschemeι y)))
      (SectionZeroStalk.sectionGerm L s U e _ hy) := by
  let x := (SectionZeroIdeal.zeroIdeal L s).subschemeι y
  let A := X.presheaf.stalk x
  let c : A := SectionZeroStalk.sectionGerm L s U e x hy
  let := stalk_krullDimLE_one X hd x
  have hlen := SectionZeroStalk.intrinsic_length_eq_of_ringEquiv
    (SectionZeroStalk.zeroStalkQuotientEquiv L s U e y hy)
  have hsc : Module.length A (A ⧸ Ideal.span {c}) =
      Module.length (A ⧸ Ideal.span {c}) (A ⧸ Ideal.span {c}) :=
    Module.length_eq_of_surjective (M := A ⧸ Ideal.span {c}) Ideal.Quotient.mk_surjective
  exact hlen.symm.trans (hsc.symm.trans
    (regular_ring_onecut_length c (sectionGerm_nonZeroDivisor L s U e x hy)))

theorem zero_stalk_length_ne_top {X : Scheme.{0}} [IsLocallyNoetherian X]
    (hd : topologicalKrullDim X ≤ 1)
    (L : LineBundle X) (s : GlobalSections X L.sheaf) [Mono s]
    (y : (SectionZeroIdeal.zeroIdeal L s).subscheme) :
    Module.length ((SectionZeroIdeal.zeroIdeal L s).subscheme.presheaf.stalk y)
      ((SectionZeroIdeal.zeroIdeal L s).subscheme.presheaf.stalk y) ≠ ⊤ := by
  let x := (SectionZeroIdeal.zeroIdeal L s).subschemeι y
  obtain ⟨V,hxV,⟨eV⟩⟩ := L.locallyRankOne x
  obtain ⟨W,hW,hxW,hWV⟩ := exists_isAffineOpen_mem_and_subset hxV
  let U : X.affineOpens := ⟨W,hW⟩
  let e := restrictOpenFrame hWV eV
  let A := X.presheaf.stalk x
  let c : A := SectionZeroStalk.sectionGerm L s U e x hxW
  let := stalk_krullDimLE_one X hd x
  have hfinite : IsFiniteLength A (A ⧸ Ideal.span {c}) :=
    isFiniteLength_quotient_span_singleton A (sectionGerm_nonZeroDivisor L s U e x hxW)
  have hsc : Module.length A (A ⧸ Ideal.span {c}) =
      Module.length (A ⧸ Ideal.span {c}) (A ⧸ Ideal.span {c}) :=
    Module.length_eq_of_surjective (M := A ⧸ Ideal.span {c}) Ideal.Quotient.mk_surjective
  have hlen := SectionZeroStalk.intrinsic_length_eq_of_ringEquiv
    (SectionZeroStalk.zeroStalkQuotientEquiv L s U e y hxW)
  rw [← hlen,← hsc]
  exact Module.length_ne_top_iff.mpr hfinite

end
end PiExponent.CurveCycle

end OAI
end Source0719

-- Source: OAI/NumberTheory/PiExponent/Geometry/CurveComponentStalks.lean
section Source0720
/-
Modification notice for the LogTwo project.
Derived from openai/math (Apache-2.0), revision adc7f1241b42e322a6451854ab7e4b4c146bf78a.
Original source: lean/OAI/NumberTheory/PiExponent/Geometry/CurveComponentStalks.lean
Changes: Convert module/import declarations to the Lean 4.34 public module format.
See ../THIRD_PARTY_NOTICES.txt for provenance and the recorded changes.
-/

namespace OAI

namespace PiExponent.CurveCycle
noncomputable section
open AlgebraicGeometry CategoryTheory TopologicalSpace Topology

theorem generic_iff_no_proper_generalization {T : Type*} [TopologicalSpace T] [QuasiSober T]
    (x : T) : x ∈ genericPoints T ↔ ∀ y : T, y ⤳ x → x ⤳ y := by
  constructor
  · intro hx y hy
    apply specializes_iff_closure_subset.mpr
    exact hx.2 isIrreducible_singleton.closure hy.closure_subset
  · intro hx
    let C : irreducibleComponents T :=
      ⟨irreducibleComponent x, irreducibleComponent_mem_irreducibleComponents x⟩
    let y := (genericPoints.ofComponent C).val
    have hy : y ⤳ x := (genericPoints.isGenericPoint_ofComponent C).specializes
      mem_irreducibleComponent
    have he : closure ({x} : Set T) = C.val := by
      apply Set.Subset.antisymm
      · exact closure_minimal (Set.singleton_subset_iff.mpr mem_irreducibleComponent)
          (isClosed_of_mem_irreducibleComponents C.val C.property)
      · rw [← (genericPoints.isGenericPoint_ofComponent C).def]
        exact (hx y hy).closure_subset
    change closure ({x} : Set T) ∈ irreducibleComponents T
    rw [he]
    exact C.property

theorem generic_embedding_iff {T S : Type*} [TopologicalSpace T] [QuasiSober T]
    [TopologicalSpace S] [QuasiSober S] {f : S → T} (hf : IsEmbedding f)
    (hstable : ∀ y : S, ∀ x : T, x ⤳ f y → x ∈ Set.range f) (y : S) :
    y ∈ genericPoints S ↔ f y ∈ genericPoints T := by
  rw [generic_iff_no_proper_generalization, generic_iff_no_proper_generalization]
  constructor
  · intro hy x hx
    obtain ⟨z,rfl⟩ := hstable y x hx
    exact (hy z (hf.isInducing.specializes_iff.mp hx)).map hf.continuous
  · intro hy z hz
    exact hf.isInducing.specializes_iff.mp (hy (f z) (hz.map hf.continuous))

def genericPointsEmbeddingEquiv {T S : Type*} [TopologicalSpace T] [QuasiSober T]
    [TopologicalSpace S] [QuasiSober S] {f : S → T} (hf : IsEmbedding f)
    (hstable : ∀ y : S, ∀ x : T, x ⤳ f y → x ∈ Set.range f) :
    genericPoints S ≃ {x : genericPoints T // x.val ∈ Set.range f} := by
  let g : genericPoints S → {x : genericPoints T // x.val ∈ Set.range f} := fun y =>
    ⟨⟨f y.val, (generic_embedding_iff hf hstable y.val).mp y.property⟩, ⟨y.val,rfl⟩⟩
  apply Equiv.ofBijective g
  constructor
  · intro x y h
    exact Subtype.ext (hf.injective (congrArg (fun z => z.val.val) h))
  · intro x
    obtain ⟨y,hy⟩ := x.property
    have hgen : y ∈ genericPoints S :=
      (generic_embedding_iff hf hstable y).mpr (hy ▸ x.val.property)
    exact ⟨⟨y,hgen⟩, Subtype.ext (Subtype.ext hy)⟩

def minimalPrimesGenericEquiv (A : CommRingCat) :
    minimalPrimes A ≃ genericPoints (Spec A) where
  toFun P := ⟨⟨P.val,P.property.1.1⟩, by
    change closure ({⟨P.val,P.property.1.1⟩} : Set (PrimeSpectrum A)) ∈
      irreducibleComponents (PrimeSpectrum A)
    rw [← PrimeSpectrum.vanishingIdeal_mem_minimalPrimes,
      PrimeSpectrum.vanishingIdeal_singleton]
    exact P.property⟩
  invFun y := ⟨y.val.asIdeal, by
    rw [← PrimeSpectrum.vanishingIdeal_singleton y.val]
    exact PrimeSpectrum.vanishingIdeal_mem_minimalPrimes.mpr y.property⟩
  left_inv P := rfl
  right_inv y := by rfl

theorem fromSpecStalk_generizing (X : Scheme.{0}) (x : X)
    (y : Spec (X.presheaf.stalk x)) (z : X) (hz : z ⤳ X.fromSpecStalk x y) :
    z ∈ Set.range (X.fromSpecStalk x) := by
  rw [Scheme.range_fromSpecStalk]
  have hy : X.fromSpecStalk x y ⤳ x := by
    have hmem : X.fromSpecStalk x y ∈ Set.range (X.fromSpecStalk x) := ⟨y,rfl⟩
    rw [Scheme.range_fromSpecStalk] at hmem
    exact hmem
  exact hz.trans hy

def genericPointsThroughEquiv (X : Scheme.{0}) (x : X) :
    {y : genericPoints X // y.val ∈ Set.range (X.fromSpecStalk x)} ≃
      {C : irreducibleComponents X // x ∈ C.val} where
  toFun y := ⟨genericPoints.component y.val, by
    have hmem : y.val.val ⤳ x :=
      (congrArg (fun S : Set X => y.val.val ∈ S)
        (Scheme.range_fromSpecStalk (X := X) (x := x))).mp y.property
    exact hmem.mem_closure⟩
  invFun C := ⟨genericPoints.ofComponent C.val, by
    rw [Scheme.range_fromSpecStalk]
    exact (genericPoints.isGenericPoint_ofComponent C.val).specializes C.property⟩
  left_inv y := by
    apply Subtype.ext
    exact genericPoints.ofComponent_component y.val
  right_inv C := by
    apply Subtype.ext
    exact genericPoints.component_ofComponent C.val

def stalkMinimalPrimesEquivComponentsThrough (X : Scheme.{0}) (x : X) :
    minimalPrimes (X.presheaf.stalk x) ≃
      {C : irreducibleComponents X // x ∈ C.val} :=
  (minimalPrimesGenericEquiv (X.presheaf.stalk x)).trans
    ((genericPointsEmbeddingEquiv (X.fromSpecStalk x).isEmbedding
      (fromSpecStalk_generizing X x)).trans (genericPointsThroughEquiv X x))

theorem stalkMinimalPrimesEquivComponentsThrough_point (X : Scheme.{0}) (x : X)
    (P : minimalPrimes (X.presheaf.stalk x)) :
    X.fromSpecStalk x (⟨P.val,P.property.1.1⟩ : Spec (X.presheaf.stalk x)) =
      (genericPoints.ofComponent
        (stalkMinimalPrimesEquivComponentsThrough X x P).val).val := by
  symm
  exact congrArg Subtype.val (genericPoints.ofComponent_component
    ((genericPointsEmbeddingEquiv (X.fromSpecStalk x).isEmbedding
      (fromSpecStalk_generizing X x))
        (minimalPrimesGenericEquiv (X.presheaf.stalk x) P)).val)

end
end PiExponent.CurveCycle

end OAI
end Source0720

-- Source: OAI/NumberTheory/PiExponent/Geometry/ReducedComponentStalk.lean
section Source0721
/-
Modification notice for the LogTwo project.
Derived from openai/math (Apache-2.0), revision adc7f1241b42e322a6451854ab7e4b4c146bf78a.
Original source: lean/OAI/NumberTheory/PiExponent/Geometry/ReducedComponentStalk.lean
Changes: Convert module/import declarations to the Lean 4.34 public module format.
See ../THIRD_PARTY_NOTICES.txt for provenance and the recorded changes.
-/

namespace OAI

namespace PiExponent.CurveCycle
noncomputable section
open AlgebraicGeometry CategoryTheory TopologicalSpace Topology

theorem reducedComponentι_range (X : Scheme.{0}) (C : irreducibleComponents X) :
    Set.range (reducedComponentι X C) = C.val := by
  let Z : Closeds X := ⟨C.val, isClosed_of_mem_irreducibleComponents C.val C.property⟩
  let I : X.IdealSheafData := Scheme.IdealSheafData.vanishingIdeal Z
  exact I.range_subschemeι.trans (Scheme.IdealSheafData.coe_support_vanishingIdeal Z)

theorem reducedComponentι_mem (X : Scheme.{0}) (C : irreducibleComponents X)
    (z : reducedComponent X C) : reducedComponentι X C z ∈ C.val := by
  rw [← reducedComponentι_range]
  exact ⟨z,rfl⟩

theorem reducedComponentι_genericPoint (X : Scheme.{0}) (C : irreducibleComponents X) :
    reducedComponentι X C (genericPoint (reducedComponent X C)) =
      (genericPoints.ofComponent C).val := by
  have hgen : IsGenericPoint
      (reducedComponentι X C (genericPoint (reducedComponent X C))) C.val := by
    change closure {_} = C.val
    rw [← Set.image_singleton, (reducedComponentι X C).isClosedEmbedding.closure_image_eq,
      genericPoint_closure, Set.image_univ, reducedComponentι_range]
  exact hgen.eq (genericPoints.isGenericPoint_ofComponent C)

theorem fromSpecStalk_bot_eq_genericPoint (Y : Scheme.{0}) [IsIntegral Y] (z : Y) :
    Y.fromSpecStalk z (⟨⊥,inferInstance⟩ : Spec (Y.presheaf.stalk z)) = genericPoint Y := by
  have hbot : (⊥ : Ideal (Y.presheaf.stalk z)) ∈ minimalPrimes (Y.presheaf.stalk z) := by
    rw [IsDomain.minimalPrimes_eq_singleton_bot]
    exact Set.mem_singleton _
  have hgen := (generic_embedding_iff (Y.fromSpecStalk z).isEmbedding
    (fromSpecStalk_generizing Y z) (⟨⊥,inferInstance⟩ : Spec (Y.presheaf.stalk z))).mp
      (minimalPrimesGenericEquiv (Y.presheaf.stalk z) ⟨⊥,hbot⟩).property
  rwa [genericPoints_eq_singleton, Set.mem_singleton_iff] at hgen

def reducedComponentStalkPrime (X : Scheme.{0}) (C : irreducibleComponents X)
    (z : reducedComponent X C) : minimalPrimes (X.presheaf.stalk (reducedComponentι X C z)) :=
  (stalkMinimalPrimesEquivComponentsThrough X (reducedComponentι X C z)).symm
    ⟨C,reducedComponentι_mem X C z⟩

theorem reducedComponentι_stalkMap_ker (X : Scheme.{0}) (C : irreducibleComponents X)
    (z : reducedComponent X C) :
    RingHom.ker ((reducedComponentι X C).stalkMap z).hom =
      (reducedComponentStalkPrime X C z).val := by
  let i := reducedComponentι X C
  let q : Spec (X.presheaf.stalk (i z)) :=
    ⟨RingHom.ker (i.stalkMap z).hom, RingHom.ker_isPrime _⟩
  let P := reducedComponentStalkPrime X C z
  have hq : X.fromSpecStalk (i z) q = (genericPoints.ofComponent C).val := by
    have hnat := congrArg (fun f : Spec ((reducedComponent X C).presheaf.stalk z) ⟶ X =>
      f (⟨⊥,inferInstance⟩ : Spec ((reducedComponent X C).presheaf.stalk z)))
      (Scheme.SpecMap_stalkMap_fromSpecStalk (f := i) (x := z))
    change X.fromSpecStalk (i z) q =
      i ((reducedComponent X C).fromSpecStalk z (⟨⊥,inferInstance⟩ :
        Spec ((reducedComponent X C).presheaf.stalk z))) at hnat
    rw [hnat, fromSpecStalk_bot_eq_genericPoint]
    exact reducedComponentι_genericPoint X C
  have hP : X.fromSpecStalk (i z) (⟨P.val,P.property.1.1⟩ : Spec (X.presheaf.stalk (i z))) =
      (genericPoints.ofComponent C).val := by
    simpa only [P,i,reducedComponentStalkPrime,Equiv.apply_symm_apply] using
      stalkMinimalPrimesEquivComponentsThrough_point X (i z) P
  exact congrArg PrimeSpectrum.asIdeal
    ((X.fromSpecStalk (i z)).isEmbedding.injective (hq.trans hP.symm))

def reducedComponentStalkQuotientEquiv (X : Scheme.{0}) (C : irreducibleComponents X)
    (z : reducedComponent X C) :
    (X.presheaf.stalk (reducedComponentι X C z)) ⧸
      (reducedComponentStalkPrime X C z).val ≃+*
        (reducedComponent X C).presheaf.stalk z :=
  (Ideal.quotEquivOfEq (reducedComponentι_stalkMap_ker X C z).symm).trans
    (((reducedComponentι X C).stalkMap z).hom.quotientKerEquivOfSurjective
      ((reducedComponentι X C).stalkMap_surjective z))

@[simp]
theorem reducedComponentStalkQuotientEquiv_mk (X : Scheme.{0})
    (C : irreducibleComponents X) (z : reducedComponent X C)
    (a : X.presheaf.stalk (reducedComponentι X C z)) :
    reducedComponentStalkQuotientEquiv X C z
      (Ideal.Quotient.mk (reducedComponentStalkPrime X C z).val a) =
        (reducedComponentι X C).stalkMap z a := by
  simp only [reducedComponentStalkQuotientEquiv, RingEquiv.trans_apply,
    Ideal.quotEquivOfEq_mk, RingHom.quotientKerEquivOfSurjective_apply_mk]

theorem reducedComponentι_stalkMap_ne_zero (X : Scheme.{0})
    (C : irreducibleComponents X) (z : reducedComponent X C)
    (a : X.presheaf.stalk (reducedComponentι X C z)) (ha : a ∈ nonZeroDivisors _) :
    (reducedComponentι X C).stalkMap z a ≠ 0 := by
  intro h
  have hmem : a ∈ (reducedComponentStalkPrime X C z).val := by
    rw [← reducedComponentι_stalkMap_ker]
    exact h
  exact notMem_nonZeroDivisors_of_mem_mem_minimalPrimes
    hmem (reducedComponentStalkPrime X C z).property ha

end
end PiExponent.CurveCycle

end OAI
end Source0721

-- Source: OAI/NumberTheory/PiExponent/Approximation/RegularComponentSection.lean
section Source0722
/-
Modification notice for the LogTwo project.
Derived from openai/math (Apache-2.0), revision adc7f1241b42e322a6451854ab7e4b4c146bf78a.
Original source: lean/OAI/NumberTheory/PiExponent/Approximation/RegularComponentSection.lean
Changes: Convert module/import declarations to the Lean 4.34 public module format.
See ../THIRD_PARTY_NOTICES.txt for provenance and the recorded changes.
-/

namespace OAI

namespace PiExponent.CurveCycle
noncomputable section
open AlgebraicGeometry CategoryTheory TopologicalSpace Topology
open PiExponentSeshadri.Geometry PiExponentSeshadri.Frames
open PiExponent.SectionZeroStalk

variable {X Y : Scheme.{0}}

theorem exists_pullback_frame_sectionGerm (f : Y ⟶ X) [IsAffineHom f]
    (L : LineBundle X) (s : GlobalSections X L.sheaf) (U : X.affineOpens)
    (e : L.sheaf.restrict U.1.ι ≅ O U.1.toScheme) :
    ∃ eF : (L.pullback f).sheaf.restrict (f ⁻¹ᵁ U.1).ι ≅ O (f ⁻¹ᵁ U.1).toScheme,
      ∀ (y : Y) (hy : f y ∈ U.1),
        sectionGerm (L.pullback f) (pullbackSection f s)
          ⟨f ⁻¹ᵁ U.1, U.2.preimage f⟩ eF y hy =
        f.stalkMap y (sectionGerm L s U e (f y) hy) := by
  obtain ⟨eF, he⟩ := exists_restricted_pullback_frame f U.1 e s
  refine ⟨eF, ?_⟩
  intro y hy
  have hr (a : Γ(U.1.toScheme, ⊤)) :
      (f ⁻¹ᵁ U.1).topIso.hom ((f ∣_ U.1).appTop a) =
        f.app U.1 (U.1.topIso.hom a) := by
    change (f ⁻¹ᵁ U.1).topIso.hom ((f ∣_ U.1).app ⊤ a) = _
    rw [← Scheme.Hom.resLE_eq_morphismRestrict, Scheme.Hom.resLE_app_top]
    simp only [Scheme.Hom.appLE_eq_app]
    exact CategoryTheory.congr_fun (f ⁻¹ᵁ U.1).topIso.inv_hom_id _
  unfold sectionGerm
  erw [he, hr, Scheme.Hom.germ_stalkMap_apply]

private theorem sectionGerm_zero (L : LineBundle X) (U : X.affineOpens)
    (e : L.sheaf.restrict U.1.ι ≅ O U.1.toScheme) (x : X) (hx : x ∈ U.1) :
    sectionGerm L 0 U e x hx = 0 := by
  simp only [sectionGerm]
  erw [restrictSection_zero, coefficient, CategoryTheory.Limits.zero_comp]
  simp only [endValue]
  change X.presheaf.germ U.1 x hx (U.1.topIso.hom 0) = 0
  simp only [map_zero]

theorem regular_component_section_ne_zero (X : Scheme.{0}) (C : irreducibleComponents X)
    (L : LineBundle X) (s : GlobalSections X L.sheaf) [Mono s] :
    pullbackSection (reducedComponentι X C) s ≠ 0 := by
  let f := reducedComponentι X C
  let z : reducedComponent X C := genericPoint (reducedComponent X C)
  obtain ⟨U, hz, ⟨e⟩, _⟩ := common_affine_frames L L (f z)
  obtain ⟨eF, heF⟩ := exists_pullback_frame_sectionGerm f L s U e
  have hne := reducedComponentι_stalkMap_ne_zero X C z
    (sectionGerm L s U e (f z) hz) (sectionGerm_nonZeroDivisor L s U e (f z) hz)
  intro hs
  apply hne
  rw [← heF z hz, hs]
  exact sectionGerm_zero _ _ _ _ _

theorem regular_component_section_mono (X : Scheme.{0}) (C : irreducibleComponents X)
    (L : LineBundle X) (s : GlobalSections X L.sheaf) [Mono s] :
    Mono (pullbackSection (reducedComponentι X C) s) :=
  (L.pullback (reducedComponentι X C)).mono_section _
    (regular_component_section_ne_zero X C L s)

end
end PiExponent.CurveCycle

end OAI
end Source0722

-- Source: OAI/NumberTheory/PiExponent/Geometry/FromSpecStalkLocalIso.lean
section Source0723
/-
Modification notice for the LogTwo project.
Derived from openai/math (Apache-2.0), revision adc7f1241b42e322a6451854ab7e4b4c146bf78a.
Original source: lean/OAI/NumberTheory/PiExponent/Geometry/FromSpecStalkLocalIso.lean
Changes: Convert module/import declarations to the Lean 4.34 public module format.
See ../THIRD_PARTY_NOTICES.txt for provenance and the recorded changes.
-/

namespace OAI

noncomputable section

open CategoryTheory AlgebraicGeometry

namespace PiExponent

universe u

theorem specMap_stalkMap_isIso_of_isLocalization
    (R S : CommRingCat.{u}) [Algebra R S] (M : Submonoid R)
    [IsLocalization M S] (y : Spec S) :
    IsIso ((Spec.map (CommRingCat.ofHom (algebraMap R S))).stalkMap y) := by
  let e := IsLocalization.algEquiv M (Localization M) S
  have he : IsIso (CommRingCat.ofHom e.toRingHom) :=
    inferInstanceAs (IsIso e.toRingEquiv.toCommRingCatIso.hom)
  have hmap : IsIso (Spec.map (CommRingCat.ofHom e.toRingHom)) := inferInstance
  have hstalk : IsIso ((Spec.map (CommRingCat.ofHom e.toRingHom)).stalkMap y) :=
    inferInstance
  have h : Spec.map (CommRingCat.ofHom (algebraMap R S)) =
      Spec.map (CommRingCat.ofHom e.toRingHom) ≫
        Spec.map (CommRingCat.ofHom (algebraMap R (Localization M))) := by
    rw [← Spec.map_comp]
    congr 1
    apply CommRingCat.hom_ext
    exact e.toAlgHom.comp_algebraMap.symm
  rw [h, Scheme.Hom.stalkMap_comp]
  have hloc : IsIso ((Spec.map (CommRingCat.ofHom
      (algebraMap R (Localization M)))).stalkMap
        (Spec.map (CommRingCat.ofHom e.toRingHom) y)) :=
    isIso_SpecMap_stakMap_localization R M _
  exact (asIso ((Spec.map (CommRingCat.ofHom
      (algebraMap R (Localization M)))).stalkMap
        (Spec.map (CommRingCat.ofHom e.toRingHom) y)) ≪≫
    asIso ((Spec.map (CommRingCat.ofHom e.toRingHom)).stalkMap y)).isIso_hom

instance fromSpecStalk_stalkMap_isIso (X : Scheme.{u}) (x : X)
    (y : Spec (X.presheaf.stalk x)) :
    IsIso ((X.fromSpecStalk x).stalkMap y) := by
  obtain ⟨U, hU, hxU, _⟩ := exists_isAffineOpen_mem_and_subset
    (TopologicalSpace.Opens.mem_top x)
  rw [← hU.fromSpecStalk_eq_fromSpecStalk hxU, IsAffineOpen.fromSpecStalk,
    Scheme.Hom.stalkMap_comp]
  let : Algebra Γ(X, U) (X.presheaf.stalk x) :=
    (X.presheaf.germ U x hxU).hom.toAlgebra
  have := hU.isLocalization_stalk ⟨x, hxU⟩
  have : IsIso ((Spec.map (X.presheaf.germ U x hxU)).stalkMap y) :=
    specMap_stalkMap_isIso_of_isLocalization Γ(X, U) (X.presheaf.stalk x)
      (hU.primeIdealOf ⟨x, hxU⟩).asIdeal.primeCompl y
  exact (asIso (hU.fromSpec.stalkMap ((Spec.map (X.presheaf.germ U x hxU)) y)) ≪≫
    asIso ((Spec.map (X.presheaf.germ U x hxU)).stalkMap y)).isIso_hom

def fromSpecStalkStalkIso (X : Scheme.{u}) (x : X)
    (y : Spec (X.presheaf.stalk x)) :
    X.presheaf.stalk (X.fromSpecStalk x y) ≅
      (Spec (X.presheaf.stalk x)).presheaf.stalk y :=
  asIso ((X.fromSpecStalk x).stalkMap y)

end PiExponent

end

end OAI
end Source0723

-- Source: OAI/NumberTheory/PiExponent/Geometry/CurveLocalMultiplicity.lean
section Source0724
/-
Modification notice for the LogTwo project.
Derived from openai/math (Apache-2.0), revision adc7f1241b42e322a6451854ab7e4b4c146bf78a.
Original source: lean/OAI/NumberTheory/PiExponent/Geometry/CurveLocalMultiplicity.lean
Changes: Convert module/import declarations to the Lean 4.34 public module format.
See ../THIRD_PARTY_NOTICES.txt for provenance and the recorded changes.
-/

namespace OAI

namespace PiExponent.CurveCycle
noncomputable section
open AlgebraicGeometry CategoryTheory TopologicalSpace

theorem componentMultiplicity_cast {X : Scheme.{0}} [IsLocallyNoetherian X]
    (C : irreducibleComponents X) :
    (componentMultiplicity X C : ℕ∞) =
      Module.length (X.presheaf.stalk (genericPoints.ofComponent C).val)
        (X.presheaf.stalk (genericPoints.ofComponent C).val) := by
  let x := (genericPoints.ofComponent C).val
  let : IsArtinianRing (X.presheaf.stalk x) :=
    generic_stalk_isArtinian x (genericPoints.ofComponent C).property
  exact ENat.natCast_toNat Module.length_ne_top

def localMinimalPrimeGenericStalkIso (X : Scheme.{0}) (x : X)
    (P : minimalPrimes (X.presheaf.stalk x)) :
    letI : P.val.IsPrime := P.property.1.1
    X.presheaf.stalk (genericPoints.ofComponent
      (stalkMinimalPrimesEquivComponentsThrough X x P).val).val ≅
      CommRingCat.of (Localization.AtPrime P.val) := by
  let y : Spec (X.presheaf.stalk x) := ⟨P.val,P.property.1.1⟩
  let e := (PiExponent.fromSpecStalkStalkIso X x y) ≪≫
    (Spec.stalkIso (X.presheaf.stalk x) y)
  simpa only [y,stalkMinimalPrimesEquivComponentsThrough_point] using e

theorem localMinimalPrime_length_eq_componentMultiplicity
    {X : Scheme.{0}} [IsLocallyNoetherian X] (x : X)
    (P : minimalPrimes (X.presheaf.stalk x)) :
    letI : P.val.IsPrime := P.property.1.1
    Module.length (Localization.AtPrime P.val) (Localization.AtPrime P.val) =
      (componentMultiplicity X (stalkMinimalPrimesEquivComponentsThrough X x P).val : ℕ∞) := by
  let : P.val.IsPrime := P.property.1.1
  rw [componentMultiplicity_cast]
  exact (SectionZeroStalk.intrinsic_length_eq_of_ringEquiv
    (localMinimalPrimeGenericStalkIso X x P).commRingCatIsoToRingEquiv).symm

end
end PiExponent.CurveCycle

end OAI
end Source0724

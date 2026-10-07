module

public import LogTwo.Geometry.ScaledJet
public import OAI.NumberTheory.PiExponent.Geometry.PlaceCenteredBranch

@[expose] public section

/-! Local logarithmic contact at an arbitrary nonzero Y-coordinate. The old
Y=1 theorem is applied after normalization; the final order is that of the
original polynomial at the original curve coordinates. -/
namespace LogTwo.Geometry

open OAI PiExponent PiExponentApprox
open CurveValuationCenter CurveCenters PlaceValuationRing WeightedPolynomialPole
noncomputable section

variable {E : Type*} [Field E] [Algebra ℂ E]

def centerPoint {m : ℕ} (y : ℂ) (c : Fin m → ℂ) : Fin (m+1) → ℂ := Fin.cases y c

theorem valuation_div_constant (p : NormalizedPlace ℂ E) (y : ℂ) (hy : y ≠ 0) (f : E) :
    p.valuation (f / algebraMap ℂ E y) = p.valuation f := by
  rw [p.valuation.map_div, CurveProductFormula.valuation_constant_eq_zero p y hy, sub_zero]

theorem coordinateOrder_div_constant (p : NormalizedPlace ℂ E) (y : ℂ) (hy : y ≠ 0) (f : E) :
    coordinateOrder p.valuation (f / algebraMap ℂ E y) = coordinateOrder p.valuation f := by
  classical
  have hy' : algebraMap ℂ E y ≠ 0 := (map_ne_zero_iff _ (algebraMap ℂ E).injective).mpr hy
  by_cases hf : f = 0
  · simp [hf, coordinateOrder]
  · simp only [coordinateOrder, dif_neg (div_ne_zero hf hy'), dif_neg hf]
    apply WithTop.coe_injective
    rw [WeightedCurveDegree.coe_integerOrder, WeightedCurveDegree.coe_integerOrder]
    exact valuation_div_constant p y hy f

theorem coordinatePole_normalizeY (p : NormalizedPlace ℂ E) {m : ℕ}
    (y : ℂ) (hy : y ≠ 0) (z : Fin (m+1) → E) (w : Fin (m+1) → ℚ) :
    coordinatePole p.valuation (normalizeY y z) w = coordinatePole p.valuation z w := by
  have he : ∀ i, coordinateOrder p.valuation (normalizeY y z i) = coordinateOrder p.valuation (z i) := by
    intro i
    cases i using Fin.cases with
    | zero => exact coordinateOrder_div_constant p y hy (z 0)
    | succ i => rfl
  simp only [coordinatePole, he]

theorem weightedDegree_normalizeY {m : ℕ}
    (hfinite : ∀ f : E, Transcendental ℂ f →
      FiniteDimensional (IntermediateField.adjoin ℂ {f}) E)
    (y : ℂ) (hy : y ≠ 0) (z : Fin (m+1) → E) (w : Fin (m+1) → ℚ) :
    CurveContactSum.weightedDegree hfinite (normalizeY y z) w =
      CurveContactSum.weightedDegree hfinite z w := by
  have he : CurveContactSum.weightedPoleDivisor hfinite (normalizeY y z) w =
      CurveContactSum.weightedPoleDivisor hfinite z w := by
    ext p
    exact coordinatePole_normalizeY p y hy z w
  unfold CurveContactSum.weightedDegree
  rw [he]

theorem valuation_normalizeY_sub_center (p : NormalizedPlace ℂ E) {m : ℕ}
    (y : ℂ) (hy : y ≠ 0) (z : Fin (m+1) → E) (c : Fin m → ℂ) (i : Fin (m+1)) :
    p.valuation (normalizeY y z i - algebraMap ℂ E (centerPoint 1 c i)) =
      p.valuation (z i - algebraMap ℂ E (centerPoint y c i)) := by
  cases i using Fin.cases with
  | zero =>
    have hy' : algebraMap ℂ E y ≠ 0 := (map_ne_zero_iff _ (algebraMap ℂ E).injective).mpr hy
    have he : normalizeY y z 0 - algebraMap ℂ E (centerPoint 1 c 0) =
        (z 0 - algebraMap ℂ E y) / algebraMap ℂ E y := by
      simp [normalizeY, centerPoint, sub_div, hy']
    rw [he, valuation_div_constant p y hy]
    rfl
  | succ i => rfl

theorem normalized_centered_iff (p : NormalizedPlace ℂ E) {m : ℕ}
    (y : ℂ) (hy : y ≠ 0) (z : Fin (m+1) → E) (c : Fin m → ℂ) :
    Centered (normalizeY y z) (centerPoint 1 c) p ↔ Centered z (centerPoint y c) p := by
  unfold Centered
  simp only [valuation_normalizeY_sub_center p y hy]

theorem normalized_nonconstant {m : ℕ} (y : ℂ) (hy : y ≠ 0)
    (z : Fin (m+1) → E) (c : Fin m → ℂ)
    (hnc : ∃ i, z i ≠ algebraMap ℂ E (centerPoint y c i)) :
    ∃ i, normalizeY y z i ≠ algebraMap ℂ E (centerPoint 1 c i) := by
  obtain ⟨i, hi⟩ := hnc
  refine ⟨i, ?_⟩
  intro he
  apply hi
  cases i using Fin.cases with
  | zero =>
    have hy' : algebraMap ℂ E y ≠ 0 := (map_ne_zero_iff _ (algebraMap ℂ E).injective).mpr hy
    have hd : z 0 / algebraMap ℂ E y = 1 := by simpa [normalizeY, centerPoint] using he
    exact (div_eq_one_iff_eq hy').mp hd
  | succ i => exact he

/-- A constant Y-coordinate forces every centered branch, even at different
places, to belong to the same center when the Y-centers are distinct. -/
theorem center_index_unique_of_constantY {m : ℕ} {J : Type*}
    (y : J → ℂ) (hy : Function.Injective y) (c : J → Fin m → ℂ)
    (z : Fin (m+1) → E) (a : ℂ) (hconst : z 0 = algebraMap ℂ E a)
    (j k : J) (p q : NormalizedPlace ℂ E)
    (hp : Centered z (centerPoint (y j) (c j)) p)
    (hq : Centered z (centerPoint (y k) (c k)) q) : j = k := by
  apply hy
  exact (hp.constant_coordinate 0 a hconst).symm.trans (hq.constant_coordinate 0 a hconst)

variable (p : NormalizedPlace ℂ E)
  [Algebra.IsIntegral ℂ (IsLocalRing.ResidueField (ring p))]

def logContactAt {m : ℕ} (y : ℂ) (hy : y ≠ 0) (z : Fin (m+1) → E) (c : Fin m → ℂ)
    (hc : Centered z (centerPoint y c) p)
    (hnc : ∃ i, z i ≠ algebraMap ℂ E (centerPoint y c i)) (v : Fin (m+1) → ℚ) : ℚ :=
  PlaceCenteredBranch.logContact p (normalizeY y z) c
    ((normalized_centered_iff p y hy z c).mpr hc) (normalized_nonconstant y hy z c hnc) v

theorem logContactAt_pos {m : ℕ} (y : ℂ) (hy : y ≠ 0)
    (z : Fin (m+1) → E) (c : Fin m → ℂ) (hc : Centered z (centerPoint y c) p)
    (hnc : ∃ i, z i ≠ algebraMap ℂ E (centerPoint y c i))
    (v : Fin (m+1) → ℚ) (hv : ∀ i, 0 < v i) : 0 < logContactAt p y hy z c hc hnc v :=
  PlaceCenteredBranch.logContact_pos p _ _ _ _ v hv

/-- The existing local derivative-order estimate, now at Y=y rather than Y=1. -/
theorem logWord_order_lower_at {m : ℕ} (y : ℂ) (hy : y ≠ 0)
    (z : Fin (m+1) → E) (c : Fin m → ℂ) (hc : Centered z (centerPoint y c) p)
    (hnc : ∃ i, z i ≠ algebraMap ℂ E (centerPoint y c i))
    (v : Fin (m+1) → ℚ) (hv : ∀ i, 0 < v i) (H : ℚ) (F : FramePolynomial m)
    (hF : formalJetAt y c F ∈ JetGeometry.rationalWeightedIdeal v (fun i => (hv i).le) H)
    (word : List (Fin (m+1)))
    (hne : MvPolynomial.aeval z (polynomialFrameWord m word F) ≠ 0) :
    logContactAt p y hy z c hc hnc v * (H - (word.map v).sum) ≤
      (coordinateOrder p.valuation (MvPolynomial.aeval z (polynomialFrameWord m word F)) : ℚ) := by
  have hn : MvPolynomial.aeval (normalizeY y z)
      (polynomialFrameWord m word (scaleY y F)) ≠ 0 := by
    rw [aeval_normalizeY_scaled_word y hy]
    exact hne
  have hb := PlaceCenteredBranch.logWord_field_order_lower p (normalizeY y z) c
    ((normalized_centered_iff p y hy z c).mpr hc) (normalized_nonconstant y hy z c hnc)
    v hv H (scaleY y F) hF word hn
  rw [aeval_normalizeY_scaled_word y hy] at hb
  exact hb

theorem normalizeY_fiber {m : ℕ} (y : ℂ) (hy : y ≠ 0) (x : Fin m → E) :
    normalizeY y (Fin.cases (algebraMap ℂ E y) x) = Fin.cases (1 : E) x := by
  have hy' : algebraMap ℂ E y ≠ 0 := (map_ne_zero_iff _ (algebraMap ℂ E).injective).mpr hy
  funext i
  cases i using Fin.cases <;> simp [normalizeY, hy']

theorem fiber_nonconstant_at {m : ℕ} (y : ℂ) (x : Fin m → E) (c : Fin m → ℂ)
    (hnc : ∃ i : Fin (m+1), (Fin.cases (algebraMap ℂ E y) x : Fin (m+1) → E) i ≠
      algebraMap ℂ E (centerPoint y c i)) : ∃ i, x i ≠ algebraMap ℂ E (c i) := by
  obtain ⟨i, hi⟩ := hnc
  cases i using Fin.cases with
  | zero => simp [centerPoint] at hi
  | succ i => exact ⟨i, hi⟩

/-- On the constant Y=y fiber, logarithmic contact is exactly ordinary contact. -/
theorem logContactAt_fiber {m : ℕ} (y : ℂ) (hy : y ≠ 0) (x : Fin m → E) (c : Fin m → ℂ)
    (hc : Centered (Fin.cases (algebraMap ℂ E y) x) (centerPoint y c) p)
    (hnc : ∃ i : Fin (m+1), (Fin.cases (algebraMap ℂ E y) x : Fin (m+1) → E) i ≠
      algebraMap ℂ E (centerPoint y c i)) (v : Fin (m+1) → ℚ) :
    logContactAt p y hy (Fin.cases (algebraMap ℂ E y) x) c hc hnc v =
      PlaceCenteredBranch.ordinaryContact p x c (fun i => hc i.succ)
        (fiber_nonconstant_at y x c hnc) (fun i => v i.succ) := by
  unfold logContactAt
  simp only [normalizeY_fiber y hy]
  exact PlaceCenteredBranch.logContact_one p x c _ _ v

end
end LogTwo.Geometry

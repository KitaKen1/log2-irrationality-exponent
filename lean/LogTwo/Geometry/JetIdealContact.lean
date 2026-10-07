module

public import LogTwo.Geometry.JetIdealAt

@[expose] public section

/-! The polynomial ideal at a varying center, evaluated in a branch DVR,
has colength equal to the normalized logarithmic contact. -/
namespace LogTwo.Geometry
open OAI PiExponent PiExponentApprox
open CurveValuationCenter CurveCenters PlaceValuationRing PlaceCenteredBranch
noncomputable section

variable {E : Type*} [Field E] [Algebra ℂ E]
variable (p : NormalizedPlace ℂ E) {m : ℕ}

theorem lift_normalizeY (y : ℂ) (hy : y ≠ 0) (z : Fin (m+1) → E)
    (c : Fin m → ℂ) (hc : Centered z (centerPoint y c) p) :
    lift p (normalizeY y z) (centerPoint 1 c) ((normalized_centered_iff p y hy z c).mpr hc) =
      Fin.cases (algebraMap ℂ (ring p) y⁻¹ * lift p z (centerPoint y c) hc 0)
        (fun i => lift p z (centerPoint y c) hc i.succ) := by
  funext i
  cases i using Fin.cases with
  | zero =>
    apply Subtype.ext
    change z 0 / algebraMap ℂ E y = algebraMap ℂ E y⁻¹ * z 0
    rw [map_inv₀, div_eq_mul_inv, mul_comm]
  | succ i => rfl

def localJetIdealAt (y : ℂ) (z : Fin (m+1) → E) (c : Fin m → ℂ)
    (hc : Centered z (centerPoint y c) p) (T : Fin m → ℕ) (e : Fin (m+1) → ℕ) :
    Ideal (ring p) :=
  (jetIdealAt y c T e).map (MvPolynomial.aeval (lift p z (centerPoint y c) hc)).toRingHom

theorem localJetIdealAt_eq (y : ℂ) (hy : y ≠ 0) (z : Fin (m+1) → E)
    (c : Fin m → ℂ) (hc : Centered z (centerPoint y c) p)
    (T : Fin m → ℕ) (e : Fin (m+1) → ℕ) :
    localJetIdealAt p y z c hc T e =
      LogarithmicContactIdeal.logarithmicIdeal c
        (lift p (normalizeY y z) (centerPoint 1 c)
          ((normalized_centered_iff p y hy z c).mpr hc) 0)
        (fun i => lift p (normalizeY y z) (centerPoint 1 c)
          ((normalized_centered_iff p y hy z c).mpr hc) i.succ) T e := by
  rw [localJetIdealAt, map_jetIdealAt_aeval y hy, lift_normalizeY p y hy]
  rfl

variable [Algebra.IsIntegral ℂ (IsLocalRing.ResidueField (ring p))]

theorem localJetIdealAt_colength_eq_contact (y : ℂ) (hy : y ≠ 0)
    (z : Fin (m+1) → E) (c : Fin m → ℂ) (hc : Centered z (centerPoint y c) p)
    (hnc : ∃ i, z i ≠ algebraMap ℂ E (centerPoint y c i))
    (v : Fin (m+1) → ℚ) (hv : ∀ i, 0 < v i)
    (T : Fin m → ℕ) (hT : ∀ i, v i.succ < (T i : ℚ) * v 0)
    (R : ℚ) (e : Fin (m+1) → ℕ) (he : ∀ i, v i * (e i : ℚ) = R) :
    ((Module.length (ring p) ((ring p) ⧸ localJetIdealAt p y z c hc T e)).toNat : ℚ) =
      R * logContactAt p y hy z c hc hnc v := by
  rw [localJetIdealAt_eq p y hy]
  let hc' : Centered (normalizeY y z) (Fin.cases 1 c) p :=
    (normalized_centered_iff p y hy z c).mpr hc
  let hnc' := normalized_nonconstant y hy z c hnc
  let u : Fin (m+1) → ring p := lift p (normalizeY y z) (Fin.cases 1 c) hc'
  have hzero : CurveLocalOrder.residueAugmentation ℂ (ring p) (u 0) = 1 :=
    lift_residue p (normalizeY y z) (Fin.cases 1 c) hc' 0
  have hsucc : ∀ i : Fin m, CurveLocalOrder.residueAugmentation ℂ (ring p) (u i.succ) = c i :=
    fun i => lift_residue p (normalizeY y z) (Fin.cases 1 c) hc' i.succ
  have hn : u 0 ≠ 1 ∨ ∃ i, u i.succ ≠ algebraMap ℂ (ring p) (c i) :=
    logLift_nonconstant p (normalizeY y z) c hc' hnc'
  exact LogarithmicContactIdeal.logarithmicIdeal_colength_eq_contact v hv c
    (u 0) (fun i => u i.succ) hzero hsucc hn T hT R e he

theorem localJetIdealAt_colength_ne_top (y : ℂ) (hy : y ≠ 0)
    (z : Fin (m+1) → E) (c : Fin m → ℂ) (hc : Centered z (centerPoint y c) p)
    (hnc : ∃ i, z i ≠ algebraMap ℂ E (centerPoint y c i))
    (v : Fin (m+1) → ℚ) (hv : ∀ i, 0 < v i)
    (T : Fin m → ℕ) (hT : ∀ i, v i.succ < (T i : ℚ) * v 0)
    (R : ℚ) (e : Fin (m+1) → ℕ) (he : ∀ i, v i * (e i : ℚ) = R) :
    Module.length (ring p) ((ring p) ⧸ localJetIdealAt p y z c hc T e) ≠ ⊤ := by
  rw [localJetIdealAt_eq p y hy]
  let hc' : Centered (normalizeY y z) (Fin.cases 1 c) p :=
    (normalized_centered_iff p y hy z c).mpr hc
  let hnc' := normalized_nonconstant y hy z c hnc
  let u : Fin (m+1) → ring p := lift p (normalizeY y z) (Fin.cases 1 c) hc'
  have hzero : CurveLocalOrder.residueAugmentation ℂ (ring p) (u 0) = 1 :=
    lift_residue p (normalizeY y z) (Fin.cases 1 c) hc' 0
  have hsucc : ∀ i : Fin m, CurveLocalOrder.residueAugmentation ℂ (ring p) (u i.succ) = c i :=
    fun i => lift_residue p (normalizeY y z) (Fin.cases 1 c) hc' i.succ
  have hn : u 0 ≠ 1 ∨ ∃ i, u i.succ ≠ algebraMap ℂ (ring p) (c i) :=
    logLift_nonconstant p (normalizeY y z) c hc' hnc'
  exact LogarithmicContactIdeal.logarithmicIdeal_colength_ne_top v hv c
    (u 0) (fun i => u i.succ) hzero hsucc hn T hT R e he

end
end LogTwo.Geometry

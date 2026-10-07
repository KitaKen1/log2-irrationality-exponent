module

public import LogTwo.Geometry.NormalizedContact
public import Mathlib.RingTheory.KrullDimension.Polynomial

@[expose] public section

/-! A short height bound suffices for rigidity. The curve kernel lies strictly
inside the kernel of evaluation at a centered point; prime-chain length then
gives height <= m. No exact dimension formula for a curve quotient is required. -/
namespace LogTwo.Geometry
open OAI PiExponent PiExponentApprox
open CurveValuationCenter CurveCenters PlaceValuationRing PlaceCenteredBranch
noncomputable section
variable {E : Type*} [Field E] [Algebra ℂ E]

def coordinateKernel {n : ℕ} (z : Fin n → E) : Ideal (MvPolynomial (Fin n) ℂ) :=
  RingHom.ker (MvPolynomial.aeval z).toRingHom

instance coordinateKernel_isPrime {n : ℕ} (z : Fin n → E) : (coordinateKernel z).IsPrime :=
  RingHom.ker_isPrime _

@[simp] theorem mem_coordinateKernel {n : ℕ} (z : Fin n → E)
    (F : MvPolynomial (Fin n) ℂ) : F ∈ coordinateKernel z ↔ MvPolynomial.aeval z F = 0 :=
  Iff.rfl

/-- Evaluation at a centered point is the residue of evaluation in its valuation ring. -/
theorem eval_center_eq_zero_of_aeval_eq_zero {n : ℕ}
    (p : NormalizedPlace ℂ E)
    [Algebra.IsIntegral ℂ (IsLocalRing.ResidueField (ring p))]
    (z : Fin n → E) (a : Fin n → ℂ) (hc : Centered z a p)
    (F : MvPolynomial (Fin n) ℂ) (hF : MvPolynomial.aeval z F = 0) :
    MvPolynomial.aeval a F = 0 := by
  have hl : MvPolynomial.aeval (lift p z a hc) F = 0 := by
    apply IsFractionRing.injective (ring p) E
    rw [map_zero, lift_aeval]
    exact hF
  let φ : ring p →ₐ[ℂ] ℂ :=
    { toRingHom := CurveLocalOrder.residueAugmentation ℂ (ring p)
      commutes' := CurveLocalOrder.residueAugmentation_algebraMap ℂ (ring p) }
  have he := MvPolynomial.comp_aeval_apply (f := lift p z a hc) φ F
  have hφ : ∀ i, φ (lift p z a hc i) = a i := lift_residue p z a hc
  simpa only [hφ, hl, map_zero] using he.symm

theorem coordinateKernel_lt_pointKernel {n : ℕ}
    (p : NormalizedPlace ℂ E)
    [Algebra.IsIntegral ℂ (IsLocalRing.ResidueField (ring p))]
    (z : Fin n → E) (a : Fin n → ℂ) (hc : Centered z a p)
    (hnc : ∃ i, z i ≠ algebraMap ℂ E (a i)) :
    coordinateKernel z < coordinateKernel a := by
  apply lt_of_le_of_ne
  · intro F hF
    exact eval_center_eq_zero_of_aeval_eq_zero p z a hc F hF
  · intro he
    obtain ⟨i, hi⟩ := hnc
    have hmem : MvPolynomial.X i - MvPolynomial.C (a i) ∈ coordinateKernel a := by
      simp
    rw [← he] at hmem
    apply hi
    simpa only [mem_coordinateKernel, map_sub, MvPolynomial.aeval_X,
      MvPolynomial.aeval_C, sub_eq_zero] using hmem

/-- The upper bound needed by rigidity follows from one centered nonconstant branch. -/
theorem coordinateKernel_height_le {m : ℕ}
    (p : NormalizedPlace ℂ E)
    [Algebra.IsIntegral ℂ (IsLocalRing.ResidueField (ring p))]
    (z : Fin (m+1) → E) (a : Fin (m+1) → ℂ) (hc : Centered z a p)
    (hnc : ∃ i, z i ≠ algebraMap ℂ E (a i)) :
    (coordinateKernel z).height ≤ (m : ℕ∞) := by
  have hstep := Ideal.height_add_one_le_of_lt_of_isPrime
    (coordinateKernel_lt_pointKernel p z a hc hnc)
  have hdim := Ideal.height_le_ringKrullDim_of_isPrime (I := coordinateKernel a)
  have hpoint : (coordinateKernel a).height ≤ ((m : ℕ∞)+1) := by
    apply WithBot.coe_le_coe.mp
    simpa only [MvPolynomial.ringKrullDim_of_isNoetherianRing,
      ringKrullDim_eq_zero_of_field, zero_add, ENat.card_eq_coe_natCard,
      Nat.card_fin, Nat.cast_add, Nat.cast_one, WithBot.coe_add, WithBot.coe_one,
      WithBot.coe_natCast] using hdim
  exact (ENat.add_le_add_iff_right (by simp : (1 : ℕ∞) ≠ ⊤)).mp (hstep.trans hpoint)

theorem coordinateKernel_X_zero_not_mem {m : ℕ}
    (p : NormalizedPlace ℂ E) (z : Fin (m+1) → E) (a : Fin (m+1) → ℂ)
    (hc : Centered z a p) (ha : a 0 ≠ 0) :
    MvPolynomial.X (0 : Fin (m+1)) ∉ coordinateKernel z := by
  intro hmem
  have hz : z 0 = 0 := by simpa only [mem_coordinateKernel, MvPolynomial.aeval_X] using hmem
  have he := hc.constant_coordinate 0 0 (by simpa using hz)
  exact ha he.symm

end
end LogTwo.Geometry

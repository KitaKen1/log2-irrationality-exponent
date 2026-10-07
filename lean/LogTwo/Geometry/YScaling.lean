module

public import OAI.NumberTheory.PiExponent.Polynomials.PolynomialFrame

@[expose] public section

/-! Polynomial and curve-coordinate normalization, independent of the local curve theory. -/
namespace LogTwo.Geometry
open OAI PiExponentApprox MvPolynomial
noncomputable section

def scaleY {m : ℕ} (y : ℂ) : FramePolynomial m →ₐ[ℂ] FramePolynomial m :=
  MvPolynomial.aeval (Fin.cases (C y * X 0) (fun i => X i.succ))

@[simp] theorem scaleY_C {m : ℕ} (y a : ℂ) : scaleY (m := m) y (C a) = C a := by
  simp [scaleY]

@[simp] theorem scaleY_X_zero {m : ℕ} (y : ℂ) :
    scaleY y (X (0 : Fin (m+1))) = C y * X 0 := by simp [scaleY]

@[simp] theorem scaleY_X_succ {m : ℕ} (y : ℂ) (i : Fin m) :
    scaleY y (X i.succ) = X i.succ := by simp [scaleY]

theorem scaleY_monomial {m : ℕ} (y : ℂ) (d : Fin (m+1) →₀ ℕ) (a : ℂ) :
    scaleY y (monomial d a) = monomial d (a * y ^ d 0) := by
  rw [scaleY, MvPolynomial.aeval_monomial, monomial_eq]
  rw [Finsupp.prod_fintype d _ (by intro i; simp)]
  rw [Finsupp.prod_fintype d _ (by intro i; simp)]
  simp only [Fin.prod_univ_succ, Fin.cases_zero, Fin.cases_succ,
    mul_pow, ← map_pow, map_mul, mul_assoc]
  rfl

theorem coeff_scaleY {m : ℕ} (y : ℂ) (F : FramePolynomial m) (d : Fin (m+1) →₀ ℕ) :
    (scaleY y F).coeff d = F.coeff d * y ^ d 0 := by
  classical
  induction F using MvPolynomial.induction_on' with
  | add F G hF hG => simp [map_add, hF, hG, add_mul]
  | monomial e a =>
    rw [scaleY_monomial]
    by_cases he : e = d
    · subst e; simp
    · simp [MvPolynomial.coeff_monomial, he]

theorem scaleY_preserves_weightedDegree {m : ℕ} (y : ℂ) (w : Fin (m+1) → ℝ)
    (H : ℝ) (F : FramePolynomial m) (hF : HasWeightedDegreeLE w H F) :
    HasWeightedDegreeLE w H (scaleY y F) := by
  intro d hd
  apply hF d
  apply MvPolynomial.mem_support_iff.mpr
  have hn := MvPolynomial.mem_support_iff.mp hd
  rw [coeff_scaleY] at hn
  exact (mul_ne_zero_iff.mp hn).1

theorem scaleY_polynomialFrame_X {m : ℕ} (y : ℂ) (i j : Fin (m+1)) :
    scaleY y (polynomialFrame m i (X j)) = polynomialFrame m i (scaleY y (X j)) := by
  classical
  cases i using Fin.cases with
  | zero =>
    cases j using Fin.cases with
    | zero =>
      simp [polynomialFrame_zero, logarithmicDerivation_apply, mul_comm]
    | succ j =>
      simp [polynomialFrame_zero, logarithmicDerivation_apply, Pi.single_apply]
  | succ i =>
    rw [polynomialFrame_pos m i.succ (Fin.succ_ne_zero i)]
    cases j using Fin.cases with
    | zero => simp
    | succ j =>
      by_cases hij : i = j
      · subst j; simp
      · simp [Ne.symm hij]

/-- Constant scaling of Y commutes with Y∂Y + Σ∂Xi and the ordinary Xi derivatives. -/
theorem scaleY_polynomialFrame {m : ℕ} (y : ℂ) (i : Fin (m+1))
    (F : FramePolynomial m) :
    scaleY y (polynomialFrame m i F) = polynomialFrame m i (scaleY y F) :=
  by
    induction F using MvPolynomial.induction_on with
    | C a => simp [polynomialFrame]
    | add F G hF hG => simp only [map_add, hF, hG]
    | mul_X F j hF =>
      simp only [Derivation.leibniz, smul_eq_mul, map_add, map_mul, hF,
        scaleY_polynomialFrame_X y i j]

theorem scaleY_polynomialFrameWord {m : ℕ} (y : ℂ) (word : List (Fin (m+1)))
    (F : FramePolynomial m) :
    scaleY y (polynomialFrameWord m word F) = polynomialFrameWord m word (scaleY y F) := by
  induction word with
  | nil => rfl
  | cons i word ih => rw [polynomialFrameWord_cons, scaleY_polynomialFrame, ih]; rfl

variable {E : Type*} [Field E] [Algebra ℂ E]

def normalizeY {m : ℕ} (y : ℂ) (z : Fin (m+1) → E) : Fin (m+1) → E :=
  Fin.cases (z 0 / algebraMap ℂ E y) (fun i => z i.succ)

/-- The polynomial scaling and the point normalization cancel exactly. -/
theorem aeval_normalizeY_scaleY {m : ℕ} (y : ℂ) (hy : y ≠ 0)
    (z : Fin (m+1) → E) (F : FramePolynomial m) :
    MvPolynomial.aeval (normalizeY y z) (scaleY y F) = MvPolynomial.aeval z F := by
  have hy' : algebraMap ℂ E y ≠ 0 := (map_ne_zero_iff _ (algebraMap ℂ E).injective).mpr hy
  have he : (MvPolynomial.aeval (normalizeY y z)).comp (scaleY y) = MvPolynomial.aeval z := by
    apply MvPolynomial.algHom_ext
    intro i
    cases i using Fin.cases with
    | zero => simp [normalizeY, hy', mul_div_cancel₀]
    | succ i => simp [normalizeY]
  exact DFunLike.congr_fun he F

theorem aeval_normalizeY_scaled_word {m : ℕ} (y : ℂ) (hy : y ≠ 0)
    (z : Fin (m+1) → E) (word : List (Fin (m+1))) (F : FramePolynomial m) :
    MvPolynomial.aeval (normalizeY y z) (polynomialFrameWord m word (scaleY y F)) =
      MvPolynomial.aeval z (polynomialFrameWord m word F) := by
  rw [← scaleY_polynomialFrameWord, aeval_normalizeY_scaleY y hy]

end
end LogTwo.Geometry

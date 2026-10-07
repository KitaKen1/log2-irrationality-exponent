module

public import LogTwo.Geometry.YScaling
public import OAI.NumberTheory.PiExponent.Jets.FormalLogJet

@[expose] public section

/-! The full formal logarithmic jet at an arbitrary Y-center. -/
namespace LogTwo.Geometry
open OAI PiExponentApprox MvPolynomial
open PiExponent.FormalLogJet PiExponent.FormalJetDerivatives
noncomputable section

def formalJetAt {m : ℕ} (y : ℂ) (c : Fin m → ℂ) :
    FramePolynomial m →ₐ[ℂ] MvPowerSeries (Fin (m+1)) ℂ :=
  (formalJet c).comp (scaleY y)

@[simp] theorem formalJetAt_Y {m : ℕ} (y : ℂ) (c : Fin m → ℂ) :
    formalJetAt y c (X (0 : Fin (m+1))) = MvPowerSeries.C y * (1 + MvPowerSeries.X 0) := by
  simp [formalJetAt, MvPowerSeries.algebraMap_apply]

@[simp] theorem formalJetAt_X {m : ℕ} (y : ℂ) (c : Fin m → ℂ) (i : Fin m) :
    formalJetAt y c (X i.succ) =
      MvPowerSeries.C (c i) + MvPowerSeries.X i.succ + formalLog m := by
  simp [formalJetAt]

def frameMonomial {m : ℕ} (h : ℕ) (α : Fin m → ℕ) : FramePolynomial m :=
  X 0 ^ h * ∏ i, X i.succ ^ α i

theorem formalJetAt_frameMonomial {m : ℕ} (y : ℂ) (c : Fin m → ℂ)
    (h : ℕ) (α : Fin m → ℕ) :
    formalJetAt y c (frameMonomial h α) =
      MvPowerSeries.C (y ^ h) * (1 + MvPowerSeries.X 0) ^ h *
      ∏ i, (MvPowerSeries.C (c i) + formalLog m + MvPowerSeries.X i.succ) ^ α i := by
  simp [frameMonomial, map_mul, map_prod, map_pow, mul_pow, add_comm, add_left_comm]

/-- The Y-center contributes exactly the manuscript's factor 2^(j*h). This is
the full formal series; identification of truncated row coefficients is separate. -/
theorem logTwo_formalJet_frameMonomial {m : ℕ} (j h : ℕ) (r : Fin m → ℚ) (α : Fin m → ℕ) :
    formalJetAt ((2 : ℂ) ^ j) (fun i => (j : ℂ) * (r i : ℂ)) (frameMonomial h α) =
      MvPowerSeries.C ((2 : ℂ) ^ (j * h)) * (1 + MvPowerSeries.X 0) ^ h *
      ∏ i, (MvPowerSeries.C ((j : ℂ) * (r i : ℂ)) + formalLog m +
        MvPowerSeries.X i.succ) ^ α i := by
  simpa only [pow_mul] using formalJetAt_frameMonomial ((2 : ℂ) ^ j)
    (fun i => (j : ℂ) * (r i : ℂ)) h α

theorem formalJetAt_polynomialFrameWord {m : ℕ} (y : ℂ) (c : Fin m → ℂ)
    (word : List (Fin (m+1))) (F : FramePolynomial m) :
    formalJetAt y c (polynomialFrameWord m word F) = jetFrameWord m word (formalJetAt y c F) := by
  change formalJet c (scaleY y (polynomialFrameWord m word F)) = _
  rw [scaleY_polynomialFrameWord, formalJet_polynomialFrameWord]
  rfl

theorem formalJetAt_word_vanishing {m : ℕ} (y : ℂ) (c : Fin m → ℂ)
    (v : Fin (m+1) → ℚ) (hv : ∀ i, 0 ≤ v i) (H : ℚ)
    (F : FramePolynomial m)
    (hF : formalJetAt y c F ∈ PiExponent.JetGeometry.rationalWeightedIdeal v hv H)
    (word : List (Fin (m+1))) :
    formalJetAt y c (polynomialFrameWord m word F) ∈
      PiExponent.JetGeometry.rationalWeightedIdeal v hv (H - (word.map v).sum) := by
  rw [formalJetAt_polynomialFrameWord]
  exact jetFrameWord_mem_rationalWeightedIdeal v hv H _ hF word

end
end LogTwo.Geometry

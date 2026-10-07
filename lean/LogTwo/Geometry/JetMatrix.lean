module

public import LogTwo.Geometry.JetTruncation
public import LogTwo.Matrix

@[expose] public section

/-! The actual rational matrix entries are the coefficients of the truncated
complex jets. Renaming the distinguished variable preserves coefficients. -/
namespace LogTwo.Geometry
open OAI PiExponentApprox
open PiExponent.FormalLogJet PiExponent.FormalLogTruncation
open LogTwo.Interpolation
noncomputable section

/-- Coefficient extension Q -> C, followed by none -> 0 and some i -> i.succ. -/
def rationalJetEmbedding (m : ℕ) :
    MvPolynomial (Option (Fin m)) ℚ →+* MvPowerSeries (Fin (m+1)) ℂ :=
  MvPolynomial.coeToMvPowerSeries.ringHom.comp
    ((MvPolynomial.rename (_root_.finSuccEquiv m).symm).toRingHom.comp
      (MvPolynomial.map (algebraMap ℚ ℂ)))

@[simp] theorem rationalJetEmbedding_C (m : ℕ) (a : ℚ) :
    rationalJetEmbedding m (MvPolynomial.C a) = MvPowerSeries.C (a : ℂ) := by
  simp [rationalJetEmbedding]

@[simp] theorem rationalJetEmbedding_X (m : ℕ) (i : Option (Fin m)) :
    rationalJetEmbedding m (MvPolynomial.X i) =
      MvPowerSeries.X ((_root_.finSuccEquiv m).symm i) := by
  simp [rationalJetEmbedding]

theorem coeff_rationalJetEmbedding {m : ℕ}
    (P : MvPolynomial (Option (Fin m)) ℚ) (d : Option (Fin m) →₀ ℕ) :
    MvPowerSeries.coeff (d.mapDomain (_root_.finSuccEquiv m).symm)
      (rationalJetEmbedding m P) = (P.coeff d : ℂ) := by
  change (MvPolynomial.rename (_root_.finSuccEquiv m).symm
    (MvPolynomial.map (algebraMap ℚ ℂ) P)).coeff _ = _
  rw [MvPolynomial.coeff_rename_mapDomain _ (_root_.finSuccEquiv m).symm.injective]
  exact MvPolynomial.coeff_map _ _ _

/-- The finite sum uses precisely the same cutoff as PowerSeries.trunc. -/
theorem rationalJetEmbedding_truncatedLog (m T : ℕ) :
    rationalJetEmbedding m (truncatedLog T) =
      liftSeries m (PowerSeries.trunc T (PowerSeries.log ℂ) : PowerSeries ℂ) := by
  induction T with
  | zero => simp [truncatedLog]
  | succ T ih =>
    by_cases hT : T = 0
    · subst T
      simp [truncatedLog, PowerSeries.trunc_succ, PowerSeries.coeff_log]
    · have hT1 : 1 ≤ T := Nat.one_le_iff_ne_zero.mpr hT
      have hs : truncatedLog (m := m) (T+1) = truncatedLog T +
          MvPolynomial.C ((-1 : ℚ) ^ (T+1) / T) * MvPolynomial.X none ^ T := by
        exact Finset.sum_Ico_succ_top hT1 _
      rw [hs, map_add, map_mul, map_pow, rationalJetEmbedding_C,
        rationalJetEmbedding_X, _root_.finSuccEquiv_symm_none, ih,
        PowerSeries.trunc_succ]
      simp [PowerSeries.coeff_log, hT, ← Polynomial.C_mul_X_pow_eq_monomial,
        liftSeries_eq_toMvPowerSeries]

theorem truncatedJetAt_frameMonomial {m : ℕ} (y : ℂ) (c : Fin m → ℂ)
    (T : Fin m → ℕ) (h : ℕ) (α : Fin m → ℕ) :
    truncatedJetAt y c T (frameMonomial h α) =
      MvPowerSeries.C (y ^ h) * (1 + MvPowerSeries.X 0) ^ h *
      ∏ i, (MvPowerSeries.C (c i) +
        liftSeries m (PowerSeries.trunc (T i) (PowerSeries.log ℂ) : PowerSeries ℂ) +
        MvPowerSeries.X i.succ) ^ α i := by
  simp [truncatedJetAt, truncatedFormalJet, frameMonomial, scaleY, map_prod,
    mul_pow, MvPowerSeries.algebraMap_apply, add_comm, add_left_comm, add_assoc]

/-- Equality for every column, before any admissibility or interpolation assumptions. -/
theorem rationalJetEmbedding_columnExpansion {m : ℕ}
    (r : Fin m → ℚ) (T : Fin m → ℕ) (j : ℕ) (col : Column m) :
    rationalJetEmbedding m (columnExpansion r T j col) =
      truncatedJetAt ((2 : ℂ)^j) (fun i => (j : ℂ) * (r i : ℂ)) T
        (frameMonomial col.h col.alpha) := by
  rw [truncatedJetAt_frameMonomial]
  simp [columnExpansion, map_prod, rationalJetEmbedding_truncatedLog, pow_mul]

/-- Exact bridge from the manuscript's rational matrix to the geometric jet. -/
theorem coefficientMatrix_eq_truncatedJetAt {m : ℕ}
    (r : Fin m → ℚ) (T : Fin m → ℕ) (row : Row m) (col : Column m) :
    (coefficientMatrix r T row col : ℂ) =
      MvPowerSeries.coeff ((rowExponent row).mapDomain (_root_.finSuccEquiv m).symm)
        (truncatedJetAt ((2 : ℂ)^row.j)
          (fun i => (row.j : ℂ) * (r i : ℂ)) T (frameMonomial col.h col.alpha)) := by
  rw [← rationalJetEmbedding_columnExpansion, coeff_rationalJetEmbedding]
  rfl

end
end LogTwo.Geometry

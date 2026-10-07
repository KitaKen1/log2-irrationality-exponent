/-
Modification notice for the LogTwo project.
Derived from openai/math (Apache-2.0), revision adc7f1241b42e322a6451854ab7e4b4c146bf78a.
Original source: lean/OAI/NumberTheory/PiExponent/Jets/FormalBranchContact.lean
Changes: Convert module/import declarations to the Lean 4.34 public module format.
See ../../../../../THIRD_PARTY_NOTICES.txt for provenance and the recorded changes.
-/

module

public import OAI.NumberTheory.PiExponent.Analysis.FormalLogTailOrder
public import OAI.NumberTheory.PiExponent.Jets.FormalBranchCoordinates

@[expose] public section

namespace OAI

noncomputable section

namespace PiExponent.FormalBranchContact

open FormalBranchEvaluation

theorem composedLogTails_strict_contact {m : ℕ}
    (v : Fin (m+1) → ℚ) (hv : ∀ i, 0 < v i)
    (a : Fin (m+1) → PowerSeries ℂ) (hne : ∃ i, a i ≠ 0)
    (ha : ∀ i, PowerSeries.constantCoeff (a i) = 0)
    (T : Fin m → ℕ) (hT : ∀ i, v i.succ < (T i : ℚ) * v 0) :
    ∀ i (k : ℕ), (composedLogTails a T i).order = (k : ℕ∞) →
      BranchContact.contact v a hne * v i < (k : ℚ) := by
  intro i k hk
  cases i using Fin.cases with
  | zero => simp [composedLogTails] at hk
  | succ i => exact composed_logTail_strict_contact v hv a hne ha T hT i k hk

theorem truncatedBranchCoordinates_not_all_zero {m : ℕ}
    (v : Fin (m+1) → ℚ) (hv : ∀ i, 0 < v i)
    (c : Fin m → ℂ) (y : PowerSeries ℂ) (x : Fin m → PowerSeries ℂ)
    (hy : PowerSeries.constantCoeff y = 1)
    (hx : ∀ i, PowerSeries.constantCoeff (x i) = c i)
    (hne : ∃ i, branchCoordinates c y x i ≠ 0)
    (T : Fin m → ℕ) (hT : ∀ i, v i.succ < (T i : ℚ) * v 0) :
    ∃ i, truncatedBranchCoordinates c y x T i ≠ 0 := by
  rw [truncatedBranchCoordinates_eq_add_tail c y x T hy]
  exact BranchContact.add_not_all_zero v hv _ _ hne
    (composedLogTails_strict_contact v hv _ hne
      (branchCoordinates_constantCoeff c y x hy hx) T hT)

theorem contact_truncatedBranchCoordinates_eq {m : ℕ}
    (v : Fin (m+1) → ℚ) (hv : ∀ i, 0 < v i)
    (c : Fin m → ℂ) (y : PowerSeries ℂ) (x : Fin m → PowerSeries ℂ)
    (hy : PowerSeries.constantCoeff y = 1)
    (hx : ∀ i, PowerSeries.constantCoeff (x i) = c i)
    (hne : ∃ i, branchCoordinates c y x i ≠ 0)
    (T : Fin m → ℕ) (hT : ∀ i, v i.succ < (T i : ℚ) * v 0) :
    BranchContact.contact v (truncatedBranchCoordinates c y x T)
      (truncatedBranchCoordinates_not_all_zero v hv c y x hy hx hne T hT) =
        BranchContact.contact v (branchCoordinates c y x) hne := by
  have hh := BranchContact.contact_add_high_tail v hv
    (branchCoordinates c y x) (composedLogTails (branchCoordinates c y x) T) hne
    (composedLogTails_strict_contact v hv _ hne
      (branchCoordinates_constantCoeff c y x hy hx) T hT)
  simpa only [← truncatedBranchCoordinates_eq_add_tail c y x T hy] using hh

end PiExponent.FormalBranchContact

end

end OAI

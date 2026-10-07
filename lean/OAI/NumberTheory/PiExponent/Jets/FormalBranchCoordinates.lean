/-
Modification notice for the LogTwo project.
Derived from openai/math (Apache-2.0), revision adc7f1241b42e322a6451854ab7e4b4c146bf78a.
Original source: lean/OAI/NumberTheory/PiExponent/Jets/FormalBranchCoordinates.lean
Changes: Convert module/import declarations to the Lean 4.34 public module format.
See ../../../../../THIRD_PARTY_NOTICES.txt for provenance and the recorded changes.
-/

module

public import OAI.NumberTheory.PiExponent.Jets.FormalBranchEvaluation

@[expose] public section

namespace OAI

noncomputable section

namespace PiExponent.FormalBranchContact

open FormalBranchEvaluation FormalLogTruncation

def composedLogTails {m : ℕ} (a : Fin (m+1) → PowerSeries ℂ) (T : Fin m → ℕ) :
    Fin (m+1) → PowerSeries ℂ :=
  Fin.cases 0 (fun i => PowerSeries.subst (a 0) (logTail (T i)))

def truncatedBranchCoordinates {m : ℕ} (c : Fin m → ℂ) (y : PowerSeries ℂ)
    (x : Fin m → PowerSeries ℂ) (T : Fin m → ℕ) : Fin (m+1) → PowerSeries ℂ :=
  Fin.cases (y-1) (fun i => x i - PowerSeries.C (c i) -
    PowerSeries.subst (y-1)
      (PowerSeries.trunc (T i) (PowerSeries.log ℂ) : PowerSeries ℂ))

theorem branchCoordinates_constantCoeff {m : ℕ} (c : Fin m → ℂ) (y : PowerSeries ℂ)
    (x : Fin m → PowerSeries ℂ) (hy : PowerSeries.constantCoeff y = 1)
    (hx : ∀ i, PowerSeries.constantCoeff (x i) = c i) :
    ∀ i, PowerSeries.constantCoeff (branchCoordinates c y x i) = 0 := by
  intro i
  have hh := (branchCoordinates_hasSubst c y x hy hx).const_coeff i
  have hz := isNilpotent_iff_eq_zero.mp hh
  simpa only [PowerSeries.constantCoeff_eq] using hz

theorem truncatedBranchCoordinates_eq_add_tail {m : ℕ}
    (c : Fin m → ℂ) (y : PowerSeries ℂ) (x : Fin m → PowerSeries ℂ)
    (T : Fin m → ℕ) (hy : PowerSeries.constantCoeff y = 1) :
    truncatedBranchCoordinates c y x T =
      fun i => branchCoordinates c y x i + composedLogTails (branchCoordinates c y x) T i := by
  have ht : PowerSeries.constantCoeff (y-1) = 0 := by simp [hy]
  have hs := PowerSeries.HasSubst.of_constantCoeff_zero' ht
  funext i
  cases i using Fin.cases with
  | zero => simp [truncatedBranchCoordinates, branchCoordinates, composedLogTails]
  | succ i =>
    simp only [truncatedBranchCoordinates, branchCoordinates, composedLogTails,
      Fin.cases_succ, Fin.cases_zero, logTail, PowerSeries.subst_sub hs]
    ring

theorem branchCoordinates_not_all_zero {m : ℕ}
    (c : Fin m → ℂ) (y : PowerSeries ℂ) (x : Fin m → PowerSeries ℂ)
    (hne : y ≠ 1 ∨ ∃ i, x i ≠ PowerSeries.C (c i)) :
    ∃ i, branchCoordinates c y x i ≠ 0 := by
  by_cases hy : y = 1
  · obtain ⟨i, hi⟩ := hne.resolve_left (not_not.mpr hy)
    refine ⟨i.succ, ?_⟩
    simpa [branchCoordinates, hy, PowerSeries.subst_zero_of_constantCoeff_zero
      PowerSeries.constantCoeff_log, sub_eq_zero] using hi
  · exact ⟨0, by simpa [branchCoordinates, sub_eq_zero] using hy⟩

end PiExponent.FormalBranchContact

end

end OAI

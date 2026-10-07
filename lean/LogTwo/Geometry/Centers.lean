module

public import Mathlib

@[expose] public section

/-!
Only the elementary constant-Y fibre step is proved here. Establishing that an
exceptional curve has constant Y, and the local contact bound, remain open tasks.
-/
namespace LogTwo.Geometry

def centerY (j : ℕ) : ℚ := 2 ^ j

theorem centerY_strictMono : StrictMono centerY := by
  apply strictMono_nat_of_lt_succ
  intro n
  dsimp [centerY]
  rw [pow_succ]
  nlinarith [pow_pos (by norm_num : (0 : ℚ) < 2) n]

theorem centerY_injective : Function.Injective centerY := centerY_strictMono.injective

theorem complex_centerY_injective : Function.Injective (fun j : ℕ => (2 : ℂ) ^ j) := by
  intro i j hij
  apply centerY_injective
  dsimp [centerY]
  apply Rat.cast_injective (α := ℂ)
  simpa only [Rat.cast_pow, Rat.cast_ofNat] using hij

/-- A fixed Y fibre can contain at most one of a family of distinct centres. -/
theorem constant_fiber_card_le_one {ι κ : Type*} [DecidableEq ι] [DecidableEq κ]
    (s : Finset ι) (y : ι → κ) (hy : Function.Injective y) (t : κ) :
    (s.filter (fun j => y j = t)).card ≤ 1 := by
  apply Finset.card_le_one.mpr
  intro i hi j hj
  exact hy ((Finset.mem_filter.mp hi).2.trans (Finset.mem_filter.mp hj).2.symm)

theorem logTwo_constant_fiber_card_le_one (s : Finset ℕ) (t : ℚ) :
    (s.filter (fun j => centerY j = t)).card ≤ 1 :=
  constant_fiber_card_le_one s centerY centerY_injective t

/-- Abstract summation step. The geometric input is the per-centre bound `hbound`. -/
theorem sum_contact_le_of_constant_fiber {ι κ : Type*} [Fintype ι] [DecidableEq ι]
    (y : ι → κ) (hy : Function.Injective y) (t : κ)
    (contact : ι → ℝ) (B : ℝ) (hB : 0 ≤ B)
    (hsupport : ∀ j, y j ≠ t → contact j = 0)
    (hbound : ∀ j, contact j ≤ B) : ∑ j, contact j ≤ B := by
  classical
  by_cases hex : ∃ j, y j = t
  · obtain ⟨j, hj⟩ := hex
    have hsum : ∑ i, contact i = contact j := by
      apply Finset.sum_eq_single j
      · intro i _ hij
        apply hsupport i
        intro hi
        exact hij (hy (hi.trans hj.symm))
      · simp
    rw [hsum]
    exact hbound j
  · have hzero : ∀ j, contact j = 0 := by
      intro j
      exact hsupport j (by intro hj; exact hex ⟨j, hj⟩)
    simpa [hzero] using hB

end LogTwo.Geometry

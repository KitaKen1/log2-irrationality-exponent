module

public import LogTwo.Matrix
public import Mathlib.Algebra.MvPolynomial.Eval
public import Mathlib.Algebra.GCDMonoid.Finset
public import Mathlib.Data.Nat.Cast.Field
public import Mathlib.Tactic.Ring

@[expose] public section

/-! The exact least common multiple clearing the truncated logarithm. -/
namespace LogTwo.Arithmetic

open MvPolynomial LogTwo.Interpolation
noncomputable section

def lcmBelow (T : ℕ) : ℕ := (Finset.Ico 1 T).lcm id

theorem dvd_lcmBelow {k T : ℕ} (hk : k ∈ Finset.Ico 1 T) : k ∣ lcmBelow T :=
  Finset.dvd_lcm hk

theorem lcmBelow_ne_zero (T : ℕ) : lcmBelow T ≠ 0 := by
  apply Finset.lcm_ne_zero_iff.mpr
  intro k hk
  have := (Finset.mem_Ico.mp hk).1
  dsimp
  omega

theorem lcmBelow_pos (T : ℕ) : 0 < lcmBelow T := Nat.pos_of_ne_zero (lcmBelow_ne_zero T)

def integerLog {m : ℕ} (T : ℕ) : MvPolynomial (Option (Fin m)) ℤ :=
  ∑ k ∈ Finset.Ico 1 T,
    C ((-1 : ℤ) ^ (k + 1) * ((lcmBelow T / k : ℕ) : ℤ)) * X none ^ k

theorem map_integerLog {m : ℕ} (T : ℕ) :
    MvPolynomial.map (Int.castRingHom ℚ) (integerLog (m := m) T) =
      C (lcmBelow T : ℚ) * truncatedLog T := by
  unfold integerLog truncatedLog
  rw [map_sum, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro k hk
  rw [map_mul, MvPolynomial.map_C, map_pow, MvPolynomial.map_X]
  change C (((-1 : ℤ) ^ (k + 1) * ((lcmBelow T / k : ℕ) : ℤ) : ℤ) : ℚ) * X none ^ k = _
  simp only [Int.cast_mul, Int.cast_pow, Int.cast_neg, Int.cast_one,
    Int.cast_natCast]
  rw [Nat.cast_div_charZero (dvd_lcmBelow hk)]
  rw [← mul_assoc, ← map_mul]
  congr 1
  congr 1
  ring

end
end LogTwo.Arithmetic

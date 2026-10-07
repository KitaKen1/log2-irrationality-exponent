module

public import OAI.NumberTheory.PiExponent.Statement

@[expose] public section

/-!
The target concerns the irrationality exponent of the natural logarithm of 2,
not merely its irrationality. We use the comparison project's exact definition.
This file states goals; it does not assert that they have been proved.
-/
namespace LogTwo

open OAI.PiExponent

def SequentialLowerBound (x : ℝ) : Prop :=
  ∀ n : ℕ, 1 ≤ n → ∃ Q : ℕ, 2 ≤ Q ∧
    ∀ p : ℤ, ∀ q : ℕ, Q ≤ q →
      (q : ℝ) ^ (-(2 + 1 / (n : ℝ))) ≤ |x - (p : ℝ) / (q : ℝ)|

def LogTwoLowerBound : Prop := EventualLowerBound (Real.log 2)

def LogTwoExponentTwo : Prop := irrationalityExponent (Real.log 2) = 2

end LogTwo

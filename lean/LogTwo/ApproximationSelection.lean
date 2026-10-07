module

public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Data.Nat.Init

@[expose] public section

/-! Denominators are chosen after the dimension, and may depend on all previous
denominators. No nonzero-numerator assumption is needed. -/
namespace LogTwo

noncomputable section

def UnboundedApproximations (x ν : ℝ) : Prop :=
  ∀ Q : ℕ, ∃ p : ℤ, ∃ q : ℕ, Q ≤ q ∧ |x - (p : ℝ) / q| ≤ (q : ℝ) ^ (-ν)

theorem exists_large_log_approximation {x ν : ℝ}
    (hbad : UnboundedApproximations x ν) (X : ℝ) :
    ∃ p : ℤ, ∃ q : ℕ, 2 ≤ q ∧ X < Real.log q ∧
      |x - (p : ℝ) / q| ≤ (q : ℝ) ^ (-ν) := by
  obtain ⟨N, hN⟩ := exists_nat_gt (Real.exp X)
  obtain ⟨p, q, hq, herr⟩ := hbad (max 2 N)
  have hq2 : 2 ≤ q := (le_max_left _ _).trans hq
  have hNq : N ≤ q := (le_max_right _ _).trans hq
  have hexp : Real.exp X < (q : ℝ) := hN.trans_le (by exact_mod_cast hNq)
  have hlog : X < Real.log q := by
    simpa using Real.log_lt_log (Real.exp_pos X) hexp
  exact ⟨p, q, hq2, hlog, herr⟩

/-- Any threshold depending on the entire finite past can be imposed. This
preserves the quantifier order needed by rapidly separated logarithmic weights. -/
theorem exists_sequential_approximations {x ν : ℝ}
    (hbad : UnboundedApproximations x ν)
    (threshold : (i : ℕ) → (Fin i → ℕ) → ℝ) :
    ∃ p : ℕ → ℤ, ∃ q : ℕ → ℕ, ∀ i : ℕ,
      2 ≤ q i ∧ threshold i (fun j => q j) < Real.log (q i) ∧
      |x - (p i : ℝ) / q i| ≤ (q i : ℝ) ^ (-ν) := by
  choose p₀ q₀ hq₀ hlog₀ herr₀ using exists_large_log_approximation hbad
  let pick (X : ℝ) : ℤ × ℕ := (p₀ X, q₀ X)
  let point : ℕ → ℤ × ℕ := Nat.strongRec fun i previous =>
    pick (threshold i (fun j => (previous j j.isLt).2))
  have heq (i : ℕ) : point i = pick (threshold i (fun j => (point j).2)) := by
    exact Nat.strongRec_eq _ i
  refine ⟨fun i => (point i).1, fun i => (point i).2, ?_⟩
  intro i
  change 2 ≤ (point i).2 ∧ threshold i (fun j => (point j).2) < Real.log (point i).2 ∧
    |x - ((point i).1 : ℝ) / (point i).2| ≤ ((point i).2 : ℝ) ^ (-ν)
  rw [heq i]
  exact ⟨hq₀ _, hlog₀ _, herr₀ _⟩

end
end LogTwo

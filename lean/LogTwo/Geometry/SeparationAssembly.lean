module

public import LogTwo.Geometry.SeparatedWeights

@[expose] public section

/-! Choose genuinely separated matrix weights, while keeping the existing
arithmetic error bound and any additional past-dependent denominator threshold.
The comparison constant is fixed after the dimension and before denominators. -/
namespace LogTwo.Geometry
open OAI PiExponent PiExponentApprox LogTwo.Interpolation LogTwo.Parameters LogTwo.Arithmetic
noncomputable section

def denominatorSeparationFactor (n m : ℕ) (M : ℝ) : ℝ :=
  weightSeparationFactor m M (horizontalWeight (b (delta n)) m)
    (verticalWeight (theta (delta n)) (b (delta n)) (c (delta n)) m)
    (theta (delta n))

theorem chosenWeights_separatedProducts (n : ℕ) (hn : 1 ≤ n) (m : ℕ)
    (q : ℕ → ℕ) (hq : ∀ i, 2 ≤ q i) (M : ℝ) (hM : 0 < M)
    (hgrowth : ∀ i, i < m →
      denominatorSeparationFactor n m M * (∏ j : Fin i, (ceilLogWeight (q j) : ℝ)) <
        (ceilLogWeight (q i) : ℝ)) :
    let w := chosenWeights n hn m (fun i => q i) (fun i => hq i)
    SeparatedProducts (columnWeight w) (fun i => (jetWeight w i : ℝ)) M := by
  dsimp only
  apply separatedProducts_of_growth _ M hM (normalizedLogWeights q) rfl
    (normalizedLogWeights_one_le q hq) (fun _ => rfl)
  intro i hi him
  cases i with
  | zero => omega
  | succ i =>
    change denominatorSeparationFactor n m M *
      (∏ j ∈ Finset.range (i+1), normalizedLogWeights q j) <
        (ceilLogWeight (q i) : ℝ)
    rw [normalizedLogWeights_prod]
    exact hgrowth i (by omega)

/-- The arithmetic small-error construction can also enforce every product
separation inequality; no future center occurs in the denominator threshold. -/
theorem exists_small_arithmetic_separated_parameters (n : ℕ) (hn : 1 ≤ n) {x ν : ℝ}
    (hbad : UnboundedApproximations x ν) (ε : ℝ) (hε : 0 < ε)
    (M : ℕ → ℝ) (hM : ∀ m, 0 < M m)
    (threshold : (m i : ℕ) → (Fin i → ℕ) → ℝ) :
    ∃ (m : ℕ) (p : ℕ → ℤ) (q : ℕ → ℕ) (hq : ∀ i, 2 ≤ q i) (W : ℝ),
      1 ≤ m ∧ 0 < W ∧
      (∀ i, W ≤ (ceilLogWeight (q i) : ℝ)) ∧
      (∀ i, threshold m i (fun j => q j) < Real.log (q i)) ∧
      (∀ i, |x-(p i : ℝ)/q i| ≤ (q i : ℝ)^(-ν)) ∧
      (∀ i, i < m → denominatorSeparationFactor n m (M m) *
        (∏ j : Fin i, (ceilLogWeight (q j) : ℝ)) < (ceilLogWeight (q i) : ℝ)) ∧
      arithmeticError (chosenWeights n hn m (fun i => q i) (fun i => hq i))
        (truncationFactor n) W < ε ∧
      SeparatedProducts
        (columnWeight (chosenWeights n hn m (fun i => q i) (fun i => hq i)))
        (fun i => (jetWeight (chosenWeights n hn m (fun i => q i) (fun i => hq i)) i : ℝ))
        (M m) := by
  obtain ⟨m,p,q,hq,W,hm,hW,hw,ht,happrox,har⟩ :=
    exists_small_arithmetic_parameters n hn hbad ε hε (fun m i previous =>
      max (threshold m i previous)
        (denominatorSeparationFactor n m (M m) *
          (∏ j : Fin i, (ceilLogWeight (previous j) : ℝ))))
  have hgrowth : ∀ i, i < m → denominatorSeparationFactor n m (M m) *
      (∏ j : Fin i, (ceilLogWeight (q j) : ℝ)) < (ceilLogWeight (q i) : ℝ) := by
    intro i _
    exact ((le_max_right _ _).trans_lt (ht i)).trans_le (ceilLogWeight_bounds (q i)).1
  exact ⟨m,p,q,hq,W,hm,hW,hw,
    (fun i => (le_max_left _ _).trans_lt (ht i)),happrox,hgrowth,har,
    chosenWeights_separatedProducts n hn m q hq (M m) (hM m) hgrowth⟩

end
end LogTwo.Geometry

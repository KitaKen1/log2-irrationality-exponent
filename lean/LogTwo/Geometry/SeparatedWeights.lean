/-
Modification notice for the LogTwo project.
Adapted from openai/math (Apache-2.0), revision adc7f1241b42e322a6451854ab7e4b4c146bf78a.
Changes: Adapt the finite-index conversion to the log-two separated weights.
See ../../../THIRD_PARTY_NOTICES.txt for provenance and the recorded changes.
-/

module

public import LogTwo.Geometry.GeometricParameters
public import OAI.NumberTheory.PiExponent.Approximation.WeightSeparation

@[expose] public section

/-! Product separation for the actual matrix weights. The finite-index conversion
adapts Geometry/AdmissibleCurveWeights.lean from pinned openai/math (Apache-2.0).
The growth condition depends only on earlier denominators. -/
namespace LogTwo.Geometry
open OAI PiExponent PiExponentApprox LogTwo.Interpolation
noncomputable section

def SeparatedProducts {m : ℕ} (w cost : Fin (m+1) → ℝ) (M : ℝ) : Prop :=
  ∀ A B : Finset (Fin (m+1)), A.card = B.card →
    ∀ i, i ≠ 0 → i ∈ A → i ∉ B →
    (∀ j, i < j → (j ∈ A ↔ j ∈ B)) →
    M * (∏ j ∈ B, cost j) < ∏ j ∈ A, w j

theorem separatedProducts_of_growth {m : ℕ} (w : Weights m) (M : ℝ) (hM : 0 < M)
    (x : ℕ → ℝ) (hx0 : x 0 = 1) (hx : ∀ i, 1 ≤ x i)
    (hmatch : ∀ i : Fin m, x (i.val+1) = (w.w i : ℝ))
    (hgrowth : SeparatedWeightGrowth m
      (weightSeparationFactor m M w.w0 w.v0 w.theta) x) :
    SeparatedProducts (columnWeight w) (fun i => (jetWeight w i : ℝ)) M := by
  classical
  intro A B hcard i hi hiA hiB hhigh
  let e : Fin (m+1) ↪ ℕ := ⟨Fin.val, Fin.val_injective⟩
  have hbound (S : Finset (Fin (m+1))) : S.map e ⊆ Finset.range (m+1) := by
    intro j hj
    obtain ⟨k, hk, rfl⟩ := Finset.mem_map.mp hj
    exact Finset.mem_range.mpr k.isLt
  have hbelow : ∀ j ∈ B.map e \ A.map e, j < i.val := by
    intro j hj
    obtain ⟨hjB, hjA⟩ := Finset.mem_sdiff.mp hj
    obtain ⟨k, hkB, rfl⟩ := Finset.mem_map.mp hjB
    by_contra hnot
    have hik : i ≤ k := Fin.le_iff_val_le_val.mpr (Nat.le_of_not_gt hnot)
    have hne : i ≠ k := fun h => hiB (h.symm ▸ hkB)
    have hkA := (hhigh k (lt_of_le_of_ne hik hne)).mpr hkB
    exact hjA (Finset.mem_map.mpr ⟨k, hkA, rfl⟩)
  have hn : 0 < i.val := Nat.pos_of_ne_zero (fun h => hi (Fin.ext h))
  have h := geometric_weight_products_separated m M w.w0 w.v0 w.theta x hM
    (by exact_mod_cast w.w0_pos) (by exact_mod_cast w.v0_pos)
    (by exact_mod_cast w.theta_pos) hx0 hx hgrowth (A.map e) (B.map e)
    (by simpa using hcard) (hbound A) (hbound B) i.val hn
    (Finset.mem_map.mpr ⟨i, hiA, rfl⟩)
    (by
      intro hmem
      obtain ⟨a, haB, hai⟩ := Finset.mem_map.mp hmem
      exact hiB ((Fin.ext hai : a = i) ▸ haB)) hbelow
  have hw (j : Fin (m+1)) :
      geometricDegreeWeight w.w0 x j.val = columnWeight w j := by
    refine Fin.cases ?_ (fun k => ?_) j
    · simp [geometricDegreeWeight, columnWeight, InterpolationMatrix.columnWeights]
    · simp [geometricDegreeWeight, columnWeight, InterpolationMatrix.columnWeights, hmatch]
  have hv (j : Fin (m+1)) :
      geometricJetWeight w.v0 w.theta x j.val = (jetWeight w j : ℝ) := by
    refine Fin.cases ?_ (fun k => ?_) j
    · simp [geometricJetWeight, jetWeight]
    · simp [geometricJetWeight, jetWeight, hmatch]
  simpa only [Finset.prod_map, e, Function.Embedding.coeFn_mk, hw, hv] using h

/-- Index zero is the normalized horizontal coordinate; denominator i is at i+1. -/
def normalizedLogWeights (q : ℕ → ℕ) : ℕ → ℝ :=
  fun i => Nat.casesOn i 1 (fun j => (Arithmetic.ceilLogWeight (q j) : ℝ))

theorem normalizedLogWeights_one_le (q : ℕ → ℕ) (hq : ∀ i, 2 ≤ q i) :
    ∀ i, 1 ≤ normalizedLogWeights q i := by
  intro i
  cases i with
  | zero => exact le_rfl
  | succ i =>
    have h := ceilLogWeight_pos (hq i)
    change (0 : ℚ) < (⌈Real.log (q i : ℝ)⌉₊ : ℚ) at h
    have hn : 1 ≤ ⌈Real.log (q i : ℝ)⌉₊ := by exact_mod_cast h
    change (1 : ℝ) ≤ ((⌈Real.log (q i : ℝ)⌉₊ : ℚ) : ℝ)
    exact_mod_cast hn

theorem normalizedLogWeights_prod (q : ℕ → ℕ) (i : ℕ) :
    (∏ j ∈ Finset.range (i+1), normalizedLogWeights q j) =
      ∏ j : Fin i, (Arithmetic.ceilLogWeight (q j) : ℝ) := by
  rw [Finset.prod_range_succ']
  simp [normalizedLogWeights]
  exact (Fin.prod_univ_eq_prod_range _ _).symm

end
end LogTwo.Geometry

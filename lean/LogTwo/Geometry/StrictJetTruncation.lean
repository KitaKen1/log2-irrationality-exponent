module

public import LogTwo.Geometry.WeightedIndices
public import LogTwo.ParameterAssembly

@[expose] public section

/-! The arithmetic matrix's actual truncation orders also satisfy the strict
weight inequality required by the local colength/contact theorem. -/
namespace LogTwo.Geometry
open LogTwo.Arithmetic LogTwo.Parameters LogTwo.Interpolation
noncomputable section

theorem truncation_weight_strict {m : ℕ} (w : Weights m) (F : ℚ)
    (hF : 1 / w.theta < F) (i : Fin m) :
    jetWeight w i.succ < (truncationOrders w F i : ℚ) * jetWeight w 0 := by
  change w.w i / w.theta < (truncationOrders w F i : ℚ) * w.v0
  calc
    _ = (1 / w.theta) * w.w i := by ring
    _ < F * w.w i := mul_lt_mul_of_pos_right hF (w.w_pos i)
    _ ≤ (truncationOrders w F i : ℚ) * w.v0 :=
      (div_le_iff₀ w.v0_pos).mp (Nat.le_ceil _)

theorem chosen_truncation_weight_strict (n : ℕ) (hn : 1 ≤ n) {m : ℕ}
    (q : Fin m → ℕ) (hq : ∀ i, 2 ≤ q i) (i : Fin m) :
    let w := chosenWeights n hn m q hq
    jetWeight w i.succ <
      (truncationOrders w (truncationFactor n) i : ℚ) * jetWeight w 0 := by
  dsimp only
  apply truncation_weight_strict
  change 1 / theta (delta n) < truncationFactor n
  calc
    _ < 2 / theta (delta n) :=
      (div_lt_div_iff_of_pos_right (shape n hn).theta_pos).mpr (by norm_num)
    _ < _ := (scalarConditions n hn).factor_gt

end
end LogTwo.Geometry

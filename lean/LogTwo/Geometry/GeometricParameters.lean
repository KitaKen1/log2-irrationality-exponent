module

public import LogTwo.Geometry.WeightedIndices
public import LogTwo.ParameterAssembly

@[expose] public section

/-! An explicit rational margin meets the two scalar geometric requirements.
No new analytic estimate or limiting argument is needed. -/
namespace LogTwo.Geometry
open LogTwo.Interpolation LogTwo.Parameters
noncomputable section

def rationalColumnWeight {m : ℕ} (w : Weights m) : Fin (m+1) → ℚ :=
  Fin.cases w.w0 w.w

theorem rationalColumnWeight_pos {m : ℕ} (w : Weights m) :
    ∀ i, 0 < rationalColumnWeight w i :=
  fun i => Fin.cases w.w0_pos w.w_pos i

theorem cast_rationalColumnWeight {m : ℕ} (w : Weights m) :
    (fun i => (rationalColumnWeight w i : ℝ)) = columnWeight w := by
  funext i
  refine Fin.cases rfl (fun _ => rfl) i

theorem weighted_volume_ratio {m : ℕ} (w : Weights m) :
    (w.K : ℚ) * (∏ i, rationalColumnWeight w i) / (∏ i, jetWeight w i) =
      (w.K : ℚ) * (w.w0 / w.v0) * w.theta^m := by
  have hp : (∏ i, w.w i) ≠ 0 := (Finset.prod_pos (fun i _ => w.w_pos i)).ne'
  simp only [Fin.prod_univ_succ, rationalColumnWeight, jetWeight,
    Fin.cases_zero, Fin.cases_succ, Finset.prod_div_distrib, Finset.prod_const,
    Finset.card_univ, Fintype.card_fin]
  field_simp

def curveSigma (theta : ℚ) (m : ℕ) : ℚ :=
  min ((1-theta)/(2*theta)) (1/(12*((m : ℚ)+1)))

theorem curveSigma_pos {theta : ℚ} (htheta : 0 < theta) (hlt : theta < 1) (m : ℕ) :
    0 < curveSigma theta m := by
  unfold curveSigma
  apply lt_min
  · exact div_pos (sub_pos.mpr hlt) (by positivity)
  · positivity

theorem curveSigma_contact_margin {theta : ℚ}
    (htheta : 0 < theta) (hlt : theta < 1) (m : ℕ) :
    (1+curveSigma theta m)*theta < 1 := by
  have hb : curveSigma theta m * (2*theta) ≤ 1-theta :=
    (le_div_iff₀ (by positivity)).mp (min_le_left _ _)
  nlinarith

/-- An elementary reciprocal form of Bernoulli's bound, proved without division.
It is useful only when 1-n*x is positive, but the statement holds for every n. -/
theorem pow_mul_one_sub_mul_le_one {x : ℚ} (hx : 0 ≤ x) (n : ℕ) :
    (1+x)^n * (1-(n : ℚ)*x) ≤ 1 := by
  induction n with
  | zero => simp
  | succ n ih =>
    have hstep : (1+x)*(1-((n : ℚ)+1)*x) ≤ 1-(n : ℚ)*x := by
      have hnx : 0 ≤ (n : ℚ)*x^2 := mul_nonneg (Nat.cast_nonneg _) (sq_nonneg x)
      nlinarith [sq_nonneg x]
    calc
      _ = (1+x)^n * ((1+x)*(1-((n : ℚ)+1)*x)) := by
        rw [pow_succ, Nat.cast_succ]
        ring
      _ ≤ (1+x)^n * (1-(n : ℚ)*x) :=
        mul_le_mul_of_nonneg_left hstep (pow_nonneg (by linarith) n)
      _ ≤ 1 := ih

theorem curveSigma_power_bound {theta : ℚ}
    (htheta : 0 < theta) (hlt : theta < 1) (m : ℕ) :
    (1+3*curveSigma theta m)^(m+1) ≤ 4/3 := by
  have hs := curveSigma_pos htheta hlt m
  have hb : curveSigma theta m * (12*((m : ℚ)+1)) ≤ 1 :=
    (le_div_iff₀ (by positivity)).mp (min_le_right _ _)
  have h := pow_mul_one_sub_mul_le_one (show 0 ≤ 3*curveSigma theta m by positivity) (m+1)
  have hp : 0 ≤ (1+3*curveSigma theta m)^(m+1) := by positivity
  have hsmall : (3/4 : ℚ) ≤ 1-((m : ℚ)+1)*(3*curveSigma theta m) := by
    nlinarith
  have hh := mul_le_mul_of_nonneg_left hsmall hp
  norm_num only [Nat.cast_add, Nat.cast_one] at h
  nlinarith

/-- The enlarged jet volume stays below one whenever the unscaled volume is 1/2. -/
theorem curveSigma_volume_lt_one {m : ℕ} (w : Weights m)
    (hhalf : (w.K : ℚ)*(w.w0/w.v0)*w.theta^m = 1/2) :
    (w.K : ℝ) * (1+3*(curveSigma w.theta m : ℝ))^(m+1) *
      (∏ i, (rationalColumnWeight w i : ℝ)) / (∏ i, (jetWeight w i : ℝ)) < 1 := by
  have hbase : (w.K : ℚ)*(∏ i, rationalColumnWeight w i)/(∏ i, jetWeight w i) = 1/2 :=
    (weighted_volume_ratio w).trans hhalf
  have hpow := curveSigma_power_bound w.theta_pos w.theta_lt_one m
  have hscaled : (w.K : ℚ)*(1+3*curveSigma w.theta m)^(m+1)*
      (∏ i, rationalColumnWeight w i)/(∏ i, jetWeight w i) < 1 := by
    calc
      _ = (1+3*curveSigma w.theta m)^(m+1) *
          ((w.K : ℚ)*(∏ i, rationalColumnWeight w i)/(∏ i, jetWeight w i)) := by ring
      _ = (1+3*curveSigma w.theta m)^(m+1) * (1/2) := by rw [hbase]
      _ < 1 := by linarith
  exact_mod_cast hscaled

/-- The actual arithmetic weights already have the required volume 1/2. -/
theorem chosenWeights_half_volume (n : ℕ) (hn : 1 ≤ n) (m : ℕ)
    (q : Fin m → ℕ) (hq : ∀ i, 2 ≤ q i) :
    let w := LogTwo.chosenWeights n hn m q hq
    (w.K : ℚ)*(w.w0/w.v0)*w.theta^m = 1/2 := by
  exact chosen_volume_ratio (shape n hn).theta_pos
    ((shape n hn).theta_pos.trans ((shape n hn).theta_lt_a.trans (shape n hn).a_lt_b))
    (shape n hn).one_lt_c.le m

theorem chosenWeights_geometric_margins (n : ℕ) (hn : 1 ≤ n) (m : ℕ)
    (q : Fin m → ℕ) (hq : ∀ i, 2 ≤ q i) :
    let w := LogTwo.chosenWeights n hn m q hq
    let sigma := curveSigma w.theta m
    0 < sigma ∧ (1+sigma)*w.theta < 1 ∧
      (w.K : ℝ)*(1+3*(sigma : ℝ))^(m+1)*(∏ i, (rationalColumnWeight w i : ℝ))/
        (∏ i, (jetWeight w i : ℝ)) < 1 := by
  dsimp only
  let w := LogTwo.chosenWeights n hn m q hq
  exact ⟨curveSigma_pos w.theta_pos w.theta_lt_one m,
    curveSigma_contact_margin w.theta_pos w.theta_lt_one m,
    curveSigma_volume_lt_one w (chosenWeights_half_volume n hn m q hq)⟩

end
end LogTwo.Geometry

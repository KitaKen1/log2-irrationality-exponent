module

public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Ring
public import Mathlib.Data.Rat.Cast.Order

@[expose] public section

/-! Explicit rational choices replace a chain of nonconstructive parameter choices. -/
namespace LogTwo.Parameters

def theta (d : ℚ) : ℚ := 1 - d
def a (d : ℚ) : ℚ := 1 - d / 2 - d ^ 2
def b (d : ℚ) : ℚ := 1 - d / 2 - 3 * d ^ 2 / 4
def c (d : ℚ) : ℚ := 1 + d / 2

structure Shape (θ a B C : ℚ) : Prop where
  theta_pos : 0 < θ
  theta_lt_a : θ < a
  a_lt_b : a < B
  b_lt_one : B < 1
  one_lt_c : 1 < C
  cb_lt_one : C * B < 1
  b_lt_c_theta : B < C * θ
  c_theta_lt_one : C * θ < 1
  a_sq_lt_theta : a ^ 2 < θ

theorem b_sub_a (d : ℚ) : b d - a d = d ^ 2 / 4 := by
  unfold b a
  ring

theorem c_theta_sub_b (d : ℚ) : c d * theta d - b d = d ^ 2 / 4 := by
  unfold c theta b
  ring

theorem one_sub_cb (d : ℚ) : 1 - c d * b d = d ^ 2 * (1 + 3 * d / 8) := by
  unfold c b
  ring

theorem theta_sub_a_sq (d : ℚ) : theta d - (a d) ^ 2 = d ^ 2 * (7 / 4 - d - d ^ 2) := by
  unfold theta a
  ring

theorem explicit_shape {d : ℚ} (hd : 0 < d) (hsmall : d ≤ 1 / 12) :
    Shape (theta d) (a d) (b d) (c d) := by
  have hs : 0 < d ^ 2 := sq_pos_of_pos hd
  have hsbound : d ^ 2 ≤ 1 / 144 := by nlinarith
  have hda : d ^ 2 < d / 2 := by nlinarith
  have hcb : 0 < d ^ 2 * (1 + 3 * d / 8) := mul_pos hs (by linarith)
  have hasq : 0 < d ^ 2 * (7 / 4 - d - d ^ 2) :=
    mul_pos hs (by linarith)
  constructor
  · dsimp [theta]; linarith
  · dsimp [theta, a]; linarith
  · linarith [b_sub_a d]
  · dsimp [b]; linarith
  · dsimp [c]; linarith
  · linarith [one_sub_cb d]
  · linarith [c_theta_sub_b d]
  · dsimp [c, theta]; nlinarith
  · linarith [theta_sub_a_sq d]

def delta (n : ℕ) : ℚ := 1 / (4 * (2 * (n : ℚ) + 1))
def nu (n : ℕ) : ℚ := 2 + 1 / (n : ℚ)
def eta (n : ℕ) : ℚ := 1 / (32 * (2 * (n : ℚ) + 1) ^ 2)
def epsilon (n : ℕ) : ℚ := 1 / (64 * (n : ℚ) * (2 * (n : ℚ) + 1))
def truncationFactor (n : ℕ) : ℚ := 256 * (2 * (n : ℚ) + 1) ^ 2
def initialGap (n : ℕ) : ℚ := delta n / (4 * (n : ℚ))
def finalGap (n : ℕ) : ℚ :=
  nu n * (a (delta n) * (1 - eta n) - theta (delta n)) - (1 - theta (delta n))

theorem delta_pos (n : ℕ) : 0 < delta n := by unfold delta; positivity

theorem delta_le {n : ℕ} (hn : 1 ≤ n) : delta n ≤ 1 / 12 := by
  have hn' : (1 : ℚ) ≤ n := by exact_mod_cast hn
  unfold delta
  apply (div_le_div_iff₀ (by positivity) (by norm_num : (0 : ℚ) < 12)).mpr
  linarith

theorem shape (n : ℕ) (hn : 1 ≤ n) :
    Shape (theta (delta n)) (a (delta n)) (b (delta n)) (c (delta n)) :=
  explicit_shape (delta_pos n) (delta_le hn)

theorem gap_before_eta (n : ℕ) (hn : 1 ≤ n) :
    nu n * (a (delta n) - theta (delta n)) - (1 - theta (delta n)) = initialGap n := by
  have hn0 : (n : ℚ) ≠ 0 := by exact_mod_cast (show n ≠ 0 by omega)
  have hden : 2 * (n : ℚ) + 1 ≠ 0 := by positivity
  dsimp [nu, a, theta, initialGap, delta]
  field_simp
  ring

theorem gap_after_eta (n : ℕ) (hn : 1 ≤ n) :
    finalGap n = initialGap n * (1 - a (delta n) / 2) := by
  have hn0 : (n : ℚ) ≠ 0 := by exact_mod_cast (show n ≠ 0 by omega)
  have hden : 2 * (n : ℚ) + 1 ≠ 0 := by positivity
  dsimp [finalGap, nu, a, theta, initialGap, eta, delta]
  field_simp
  ring

theorem epsilon_eq (n : ℕ) : epsilon n = initialGap n / 4 := by
  simp only [epsilon, initialGap, delta, div_eq_mul_inv, mul_inv_rev]
  ring

theorem nu_div_factor (n : ℕ) (hn : 1 ≤ n) :
    nu n / truncationFactor n = epsilon n / 4 := by
  have hn0 : (n : ℚ) ≠ 0 := by exact_mod_cast (show n ≠ 0 by omega)
  have hden : 2 * (n : ℚ) + 1 ≠ 0 := by positivity
  dsimp [nu, truncationFactor, epsilon]
  field_simp
  ring

/-- All scalar inequalities needed before choosing the large dimension. -/
structure ScalarConditions (n : ℕ) : Prop where
  shape : Shape (theta (delta n)) (a (delta n)) (b (delta n)) (c (delta n))
  eta_pos : 0 < eta n
  eta_lt_one : eta n < 1
  epsilon_pos : 0 < epsilon n
  epsilon_lt_gap : epsilon n < finalGap n
  epsilon_lt_half : epsilon n < 1 / 2
  factor_gt : 2 / theta (delta n) < truncationFactor n
  truncation_error : nu n / truncationFactor n < epsilon n / 3

theorem scalarConditions (n : ℕ) (hn : 1 ≤ n) : ScalarConditions n := by
  have hn' : (1 : ℚ) ≤ n := by exact_mod_cast hn
  have hnpos : (0 : ℚ) < n := by linarith
  have hd := delta_pos n
  have hdsmall := delta_le hn
  have hs := shape n hn
  have hg : 0 < initialGap n := by unfold initialGap; positivity
  have hgsmall : initialGap n ≤ 1 / 48 := by
    unfold initialGap
    apply (div_le_iff₀ (by positivity : (0 : ℚ) < 4 * n)).mpr
    linarith
  have ha : a (delta n) < 1 := hs.a_lt_b.trans hs.b_lt_one
  have hgap : initialGap n / 2 < finalGap n := by
    rw [gap_after_eta n hn]
    nlinarith
  have heps : 0 < epsilon n := by rw [epsilon_eq]; positivity
  have htheta : (11 / 12 : ℚ) ≤ theta (delta n) := by dsimp [theta]; linarith
  have hF : (256 : ℚ) ≤ truncationFactor n := by
    unfold truncationFactor
    nlinarith [sq_nonneg (2 * (n : ℚ))]
  constructor
  · exact hs
  · unfold eta; positivity
  · unfold eta
    apply (div_lt_iff₀ (by positivity : (0 : ℚ) < 32 * (2 * (n : ℚ) + 1) ^ 2)).mpr
    nlinarith [sq_nonneg (2 * (n : ℚ))]
  · exact heps
  · rw [epsilon_eq]
    linarith
  · rw [epsilon_eq]
    linarith
  · apply (div_lt_iff₀ hs.theta_pos).mpr
    have := mul_le_mul_of_nonneg_right hF hs.theta_pos.le
    nlinarith
  · rw [nu_div_factor n hn]
    linarith

theorem growth_ratios (n : ℕ) (hn : 1 ≤ n) :
    1 < c (delta n) * theta (delta n) / b (delta n) ∧
    1 < b (delta n) / a (delta n) := by
  have hs := shape n hn
  have ha : 0 < a (delta n) := hs.theta_pos.trans hs.theta_lt_a
  have hb : 0 < b (delta n) := ha.trans hs.a_lt_b
  constructor
  · exact (lt_div_iff₀ hb).mpr (by simpa using hs.b_lt_c_theta)
  · exact (lt_div_iff₀ ha).mpr (by simpa using hs.a_lt_b)

end LogTwo.Parameters

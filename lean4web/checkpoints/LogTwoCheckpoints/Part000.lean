/- Generated rc4 checkpoint for LogTwo.
Modified from the reduced edition: new imports, separate module compilation,
and synchronous elaboration. Original source blocks and notices are retained.
See ../../../THIRD_PARTY_NOTICES.txt and ../../reduction.json.
-/
module
public import Batteries.Data.Nat.Basic
public import Batteries.Data.Nat.Lemmas
public import Mathlib.Analysis.Complex.Polynomial.Basic
public import Mathlib.Analysis.Real.Pi.Irrational
public import Mathlib.Data.FunLike.Basic
public import Mathlib.NumberTheory.Chebyshev
public import Mathlib.NumberTheory.DiophantineApproximation.Basic
public import Mathlib.RingTheory.MvPowerSeries.Equiv
public import Mathlib.RingTheory.PowerSeries.Log
@[expose] public section
set_option Elab.async false

-- Source: OAI/NumberTheory/PiExponent/Statement.lean
section Source0000
/-
Modification notice for the LogTwo project.
Derived from openai/math (Apache-2.0), revision adc7f1241b42e322a6451854ab7e4b4c146bf78a.
Original source: lean/OAI/NumberTheory/PiExponent/Statement.lean
Changes: Convert module/import declarations to the Lean 4.34 public module format.
See ../THIRD_PARTY_NOTICES.txt for provenance and the recorded changes.
-/

namespace OAI

namespace PiExponent

def GoodRationalApproximations (x ν : ℝ) : Set ℚ :=
  {r | 2 ≤ r.den ∧ 0 < |x - (r : ℝ)| ∧ |x - (r : ℝ)| < (r.den : ℝ) ^ (-ν)}

def ApproximationExponents (x : ℝ) : Set ℝ :=
  {ν | 0 < ν ∧ (GoodRationalApproximations x ν).Infinite}

noncomputable def irrationalityExponent (x : ℝ) : ℝ := sSup (ApproximationExponents x)

def EventualLowerBound (x : ℝ) : Prop :=
  ∀ ν : ℝ, 2 < ν → ∃ Q : ℕ, 2 ≤ Q ∧
    ∀ (p : ℤ) (q : ℕ), Q ≤ q → (q : ℝ) ^ (-ν) ≤ |x - (p : ℝ) / (q : ℝ)|

def PiEventualLowerBound : Prop := EventualLowerBound Real.pi

def IntegerEventualLowerBound (x : ℝ) : Prop :=
  ∀ ν : ℝ, 2 < ν → ∃ Q : ℤ, 2 ≤ Q ∧
    ∀ (p q : ℤ), Q ≤ q → (q : ℝ) ^ (-ν) ≤ |x - (p : ℝ) / (q : ℝ)|

end PiExponent

end OAI
end Source0000

-- Source: LogTwo/Statement.lean
section Source0001
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
end Source0001

-- Source: LogTwo/ApproximationSelection.lean
section Source0002
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
end Source0002

-- Source: OAI/NumberTheory/PiExponent/Approximation/Exponent.lean
section Source0003
-- Modified in this edition: unused plain lemmas removed; see reduction.json.
/-
Modification notice for the LogTwo project.
Derived from openai/math (Apache-2.0), revision adc7f1241b42e322a6451854ab7e4b4c146bf78a.
Original source: lean/OAI/NumberTheory/PiExponent/Approximation/Exponent.lean
Changes: Convert module/import declarations to the Lean 4.34 public module format.
See ../THIRD_PARTY_NOTICES.txt for provenance and the recorded changes.
-/

namespace OAI

namespace PiExponent

 theorem eventualLowerBound_iff_integer (x : ℝ) :
    EventualLowerBound x ↔ IntegerEventualLowerBound x := by
  unfold EventualLowerBound IntegerEventualLowerBound
  constructor
  · intro h ν hν
    obtain ⟨Q, hQ, hb⟩ := h ν hν
    refine ⟨Q, by exact_mod_cast hQ, ?_⟩
    intro p q hq
    have hq0 : 0 ≤ q := le_trans (by omega) hq
    have hnat : Q ≤ q.toNat := by omega
    have heq : (q.toNat : ℝ) = (q : ℝ) := by
      exact_mod_cast (Int.toNat_of_nonneg hq0)
    simpa only [heq] using hb p q.toNat hnat
  · intro h ν hν
    obtain ⟨Q, hQ, hb⟩ := h ν hν
    have hQ0 : 0 ≤ Q := by omega
    refine ⟨Q.toNat, by omega, ?_⟩
    intro p q hq
    have hqi : Q ≤ (q : ℤ) := by omega
    simpa using hb p q hqi

theorem finite_rat_den_le_abs_sub_lt_one (x : ℝ) (N : ℕ) :
    {r : ℚ | r.den ≤ N ∧ |x - (r : ℝ)| < 1}.Finite := by
  classical
  let f : ℚ → ℤ × ℕ := fun r => (r.num, r.den)
  have hinj : Function.Injective f := by
    intro a b hab
    have hp := Prod.mk.inj hab
    rw [← Rat.num_div_den a, ← Rat.num_div_den b, hp.1, hp.2]
  let t : Set (ℤ × ℕ) := ⋃ (q : ℕ) (_ : q ∈ Set.Icc 1 N),
    Set.Icc ⌈(x - 1) * q⌉ ⌊(x + 1) * q⌋ ×ˢ {q}
  have ht : t.Finite :=
    Set.Finite.biUnion (Set.finite_Icc _ _) fun q _ =>
      Set.Finite.prod (Set.finite_Icc _ _) (Set.finite_singleton _)
  have hsub : f '' {r : ℚ | r.den ≤ N ∧ |x - (r : ℝ)| < 1} ⊆ t := by
    rintro _ ⟨r, ⟨hrN, hr⟩, rfl⟩
    have hrden : (0 : ℝ) < r.den := Nat.cast_pos.mpr r.pos
    have hrlow : x - 1 < (r : ℝ) := by linarith [(abs_lt.mp hr).2]
    have hrhigh : (r : ℝ) < x + 1 := by linarith [(abs_lt.mp hr).1]
    have hnlow : (x - 1) * r.den ≤ (r.num : ℝ) := by
      rw [Rat.cast_def] at hrlow
      exact ((lt_div_iff₀ hrden).mp hrlow).le
    have hnhigh : (r.num : ℝ) ≤ (x + 1) * r.den := by
      rw [Rat.cast_def] at hrhigh
      exact ((div_lt_iff₀ hrden).mp hrhigh).le
    simp only [t, Set.mem_iUnion]
    refine ⟨r.den, ⟨r.pos, hrN⟩, ?_⟩
    exact ⟨⟨Int.ceil_le.mpr hnlow, Int.le_floor.mpr hnhigh⟩, rfl⟩
  exact (ht.subset hsub).of_finite_image hinj.injOn

theorem two_mem_approximationExponents {x : ℝ} (hx : Irrational x) :
    (2 : ℝ) ∈ ApproximationExponents x := by
  refine ⟨by norm_num, ?_⟩
  have hi := Real.infinite_rat_abs_sub_lt_one_div_den_sq_of_irrational hx
  have hf := finite_rat_den_le_abs_sub_lt_one x 1
  apply (hi.sdiff hf).mono
  intro r hr
  have hrden : 1 ≤ (r.den : ℝ) := by exact_mod_cast r.pos
  have hrone : |x - (r : ℝ)| < 1 :=
    hr.1.trans_le (by
      simpa only [div_one] using
        one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 1)
          (by nlinarith : (1 : ℝ) ≤ (r.den : ℝ)^2))
  have hr2 : 2 ≤ r.den := by
    by_contra h
    exact hr.2 ⟨by omega, hrone⟩
  refine ⟨hr2, abs_pos.mpr (sub_ne_zero.mpr (hx.ne_rat r)), ?_⟩
  simpa only [Set.mem_ofPred_eq, Real.rpow_neg (Nat.cast_nonneg r.den),
    Real.rpow_two, one_div] using hr.1

theorem finite_goodRationalApproximations_of_eventualLowerBound {x ν : ℝ}
    (hx : EventualLowerBound x) (hν : 2 < ν) :
    (GoodRationalApproximations x ν).Finite := by
  obtain ⟨Q, hQ, hb⟩ := hx ν hν
  apply (finite_rat_den_le_abs_sub_lt_one x Q).subset
  intro r hr
  have hltQ : r.den < Q := by
    by_contra h
    have h := hb r.num r.den (by omega)
    rw [← Rat.cast_def] at h
    exact (not_lt_of_ge h) hr.2.2
  refine ⟨hltQ.le, hr.2.2.trans_le ?_⟩
  exact Real.rpow_le_one_of_one_le_of_nonpos
    (by exact_mod_cast r.pos) (by linarith)

theorem irrationalityExponent_eq_two_of_eventualLowerBound {x : ℝ}
    (hi : Irrational x) (hx : EventualLowerBound x) :
    irrationalityExponent x = 2 := by
  have htwo := two_mem_approximationExponents hi
  have hbound : ∀ ν ∈ ApproximationExponents x, ν ≤ 2 := by
    intro ν hν
    by_contra h
    exact (finite_goodRationalApproximations_of_eventualLowerBound hx (by linarith)).not_infinite hν.2
  apply le_antisymm
  · exact csSup_le ⟨2, htwo⟩ hbound
  · exact le_csSup ⟨2, hbound⟩ htwo

end PiExponent

end OAI
end Source0003

-- Source: LogTwo/Approximation.lean
section Source0004
namespace LogTwo

open OAI.PiExponent

/-- It suffices to rule out approximation at the countable exponents `2 + 1/n`. -/
theorem sequentialLowerBound_iff (x : ℝ) :
    SequentialLowerBound x ↔ EventualLowerBound x := by
  constructor
  · intro h ν hν
    obtain ⟨k, hk⟩ := exists_nat_one_div_lt (by linarith : (0 : ℝ) < ν - 2)
    obtain ⟨Q, hQ, hb⟩ := h (k + 1) (by omega)
    refine ⟨Q, hQ, ?_⟩
    intro p q hq
    have hbase : (1 : ℝ) ≤ q := by exact_mod_cast (show 1 ≤ q by omega)
    have hexp : -(ν : ℝ) ≤ -(2 + 1 / ((k + 1 : ℕ) : ℝ)) := by
      push_cast
      linarith
    exact (Real.rpow_le_rpow_of_exponent_le hbase hexp).trans (hb p q hq)
  · intro h n hn
    have hnreal : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
    apply h
    linarith [one_div_pos.mpr hnreal]

/-- Failure of the target bound supplies the bad approximation family used by
the parameter construction. The integer n is fixed before its denominators. -/
theorem exists_unbounded_of_not_sequential {x : ℝ} (h : ¬ SequentialLowerBound x) :
    ∃ n : ℕ, 1 ≤ n ∧ UnboundedApproximations x (2 + 1 / (n : ℝ)) := by
  classical
  unfold SequentialLowerBound at h
  push Not at h
  obtain ⟨n, hn, h⟩ := h
  refine ⟨n, hn, ?_⟩
  intro Q
  obtain ⟨p, q, hq, herr⟩ := h (max 2 Q) (le_max_left _ _)
  exact ⟨p, q, (le_max_right _ _).trans hq, herr.le⟩

/-- The bound quantifies over unreduced fractions, so it also excludes exact rational values. -/
theorem irrational_of_eventualLowerBound {x : ℝ} (h : EventualLowerBound x) :
    Irrational x := by
  rintro ⟨r, rfl⟩
  obtain ⟨Q, hQ, hb⟩ := h 3 (by norm_num)
  have hk : (0 : ℝ) < (Q + 1 : ℕ) := by positivity
  have hq : Q ≤ r.den * (Q + 1) := by nlinarith [r.pos]
  have hfrac : ((r.num * (Q + 1 : ℕ) : ℤ) : ℝ) /
      ((r.den * (Q + 1) : ℕ) : ℝ) = (r : ℝ) := by
    push_cast
    rw [mul_div_mul_right _ _ (by positivity : (Q : ℝ) + 1 ≠ 0)]
    exact Rat.cast_def r |>.symm
  have hh := hb (r.num * (Q + 1 : ℕ)) (r.den * (Q + 1)) hq
  rw [hfrac, sub_self, abs_zero] at hh
  have hp : (0 : ℝ) < (r.den * (Q + 1) : ℕ) := by
    exact_mod_cast (Nat.mul_pos r.pos (Nat.succ_pos Q))
  exact (not_le_of_gt (Real.rpow_pos_of_pos hp (-3))) hh

/-- Conditional endgame: the difficult analytic lower bound is an explicit argument. -/
theorem exponent_eq_two_of_sequentialLowerBound {x : ℝ}
    (h : SequentialLowerBound x) : irrationalityExponent x = 2 := by
  have hb := (sequentialLowerBound_iff x).mp h
  exact irrationalityExponent_eq_two_of_eventualLowerBound
    (irrational_of_eventualLowerBound hb) hb

theorem logTwoExponentTwo_of_sequentialLowerBound
    (h : SequentialLowerBound (Real.log 2)) : LogTwoExponentTwo :=
  exponent_eq_two_of_sequentialLowerBound h

end LogTwo
end Source0004

-- Source: LogTwo/Parameters.lean
section Source0005
-- Modified in this edition: unused plain lemmas removed; see reduction.json.
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
end Source0005

-- Source: LogTwo/Dimension.lean
section Source0006
/-! Growth estimates used by the ceiling-based dimension and denominator choices. -/
namespace LogTwo.Parameters

open Filter
open scoped Topology

theorem geometric_over_succ_tendsto {r : ℝ} (hr : 1 < r) :
    Tendsto (fun m : ℕ => r ^ m / ((m : ℝ) + 1)) atTop atTop := by
  have hz : Tendsto (fun m : ℕ => ((m : ℝ) + 1) / r ^ m) atTop (𝓝 0) := by
    have h1 := tendsto_pow_const_div_const_pow_of_one_lt 1 hr
    have h0 := tendsto_pow_const_div_const_pow_of_one_lt 0 hr
    simpa only [pow_one, pow_zero, zero_add, add_div] using h1.add h0
  have hp : ∀ m : ℕ, (0 : ℝ) < ((m : ℝ) + 1) / r ^ m := by
    intro m
    have : 0 < r := by linarith
    positivity
  have hz' : Tendsto (fun m : ℕ => ((m : ℝ) + 1) / r ^ m) atTop (𝓝[>] 0) :=
    tendsto_nhdsWithin_iff.mpr ⟨hz, Filter.Eventually.of_forall hp⟩
  have hinv := hz'.inv_tendsto_nhdsGT_zero
  change Tendsto (fun m : ℕ => (((m : ℝ) + 1) / r ^ m)⁻¹) atTop atTop at hinv
  simpa only [inv_div] using hinv

/-- Three growth/decay facts supplied by the explicit scalar choices. -/
theorem dimension_growth (n : ℕ) (hn : 1 ≤ n) :
    Tendsto (fun m : ℕ => ((c (delta n) * b (delta n) : ℚ) : ℝ) ^ m)
      atTop (𝓝 0) ∧
    Tendsto (fun m : ℕ => ((c (delta n) * theta (delta n) / b (delta n) : ℚ) : ℝ) ^ m)
      atTop atTop ∧
    Tendsto (fun m : ℕ => ((b (delta n) / a (delta n) : ℚ) : ℝ) ^ m / ((m : ℝ) + 1))
      atTop atTop := by
  have hs := shape n hn
  have hr := growth_ratios n hn
  have hb : 0 < b (delta n) := hs.theta_pos.trans (hs.theta_lt_a.trans hs.a_lt_b)
  have hc : 0 < c (delta n) := by linarith [hs.one_lt_c]
  refine ⟨?_, ?_, ?_⟩
  · apply tendsto_pow_atTop_nhds_zero_of_lt_one
    · exact_mod_cast (mul_pos hc hb).le
    · exact_mod_cast hs.cb_lt_one
  · apply tendsto_pow_atTop_atTop_of_one_lt
    exact_mod_cast hr.1
  · apply geometric_over_succ_tendsto
    exact_mod_cast hr.2

/-- Choosing v0 by this formula fixes the volume ratio at one half. -/
theorem volume_ratio_half {K w0 θ : ℚ} (hK : K ≠ 0) (hw : w0 ≠ 0)
    (hθ : θ ≠ 0) (m : ℕ) :
    K * (w0 / (2 * K * θ ^ m * w0)) * θ ^ m = 1 / 2 := by
  field_simp

end LogTwo.Parameters
end Source0006

-- Source: LogTwo/DimensionChoice.lean
section Source0007
/-! Ceiling-based choices avoid a separate eventual lower bound for the floor. -/
namespace LogTwo.Parameters

open Filter
open scoped Topology

def centerCount (C : ℚ) (m : ℕ) : ℕ := ⌈C ^ m⌉₊
def horizontalWeight (B : ℚ) (m : ℕ) : ℚ := (B ^ m)⁻¹
def verticalWeight (θ B C : ℚ) (m : ℕ) : ℚ :=
  2 * (centerCount C m : ℚ) * θ ^ m * horizontalWeight B m

theorem centerCount_bounds {C : ℚ} (hC : 1 ≤ C) (m : ℕ) :
    C ^ m ≤ (centerCount C m : ℚ) ∧ (centerCount C m : ℚ) ≤ 2 * C ^ m := by
  have hp : 1 ≤ C ^ m := one_le_pow₀ hC
  refine ⟨Nat.le_ceil _, ?_⟩
  have ht := Nat.ceil_lt_add_one (show 0 ≤ C ^ m by linarith)
  dsimp [centerCount]
  linarith

theorem centerCount_pos {C : ℚ} (hC : 1 ≤ C) (m : ℕ) : 0 < centerCount C m := by
  have hb := (centerCount_bounds hC m).1
  have hp : 1 ≤ C ^ m := one_le_pow₀ hC
  have : (0 : ℚ) < centerCount C m := by linarith
  exact_mod_cast this

theorem horizontalWeight_pos {B : ℚ} (hB : 0 < B) (m : ℕ) :
    0 < horizontalWeight B m := by unfold horizontalWeight; positivity

theorem verticalWeight_pos {θ B C : ℚ} (hθ : 0 < θ) (hB : 0 < B)
    (hC : 1 ≤ C) (m : ℕ) : 0 < verticalWeight θ B C m := by
  have hK := centerCount_pos hC m
  have hw := horizontalWeight_pos hB m
  unfold verticalWeight
  positivity

theorem count_over_horizontal_le {B C : ℚ} (hB : 0 < B) (hC : 1 ≤ C) (m : ℕ) :
    (centerCount C m : ℚ) / horizontalWeight B m ≤ 2 * (C * B) ^ m := by
  have hb := mul_le_mul_of_nonneg_right (centerCount_bounds hC m).2
    (pow_nonneg hB.le m)
  simpa [horizontalWeight, div_inv_eq_mul, mul_pow, mul_assoc] using hb

theorem verticalWeight_lower {θ B C : ℚ} (hθ : 0 < θ) (hB : 0 < B)
    (hC : 1 ≤ C) (m : ℕ) :
    2 * (C * θ / B) ^ m ≤ verticalWeight θ B C m := by
  have hb := mul_le_mul_of_nonneg_right (centerCount_bounds hC m).1
    (show 0 ≤ 2 * θ ^ m * (B ^ m)⁻¹ by positivity)
  simpa [verticalWeight, horizontalWeight, div_pow, mul_pow, div_eq_mul_inv,
    mul_comm, mul_left_comm, mul_assoc] using hb

theorem count_over_horizontal_tendsto {B C : ℚ} (hB : 0 < B) (hC : 1 ≤ C)
    (hCB : C * B < 1) :
    Tendsto (fun m => ((centerCount C m : ℚ) / horizontalWeight B m : ℚ) : ℕ → ℝ)
      atTop (𝓝 0) := by
  have hz : Tendsto (fun m : ℕ => 2 * ((C * B : ℚ) : ℝ) ^ m) atTop (𝓝 0) := by
    have hh := tendsto_pow_atTop_nhds_zero_of_lt_one
      (show (0 : ℝ) ≤ ((C * B : ℚ) : ℝ) by exact_mod_cast mul_nonneg (by linarith) hB.le)
      (show ((C * B : ℚ) : ℝ) < 1 by exact_mod_cast hCB)
    simpa using hh.const_mul 2
  apply squeeze_zero _ _ hz
  · intro m
    exact_mod_cast (div_nonneg (Nat.cast_nonneg _) (horizontalWeight_pos hB m).le)
  · intro m
    exact_mod_cast count_over_horizontal_le hB hC m

theorem verticalWeight_tendsto {θ B C : ℚ} (hθ : 0 < θ) (hB : 0 < B)
    (hC : 1 ≤ C) (hr : 1 < C * θ / B) :
    Tendsto (fun m => (verticalWeight θ B C m : ℝ)) atTop atTop := by
  have hp := tendsto_pow_atTop_atTop_of_one_lt
    (show (1 : ℝ) < ((C * θ / B : ℚ) : ℝ) by exact_mod_cast hr)
  apply tendsto_atTop_mono _ hp
  intro m
  have hlow := verticalWeight_lower hθ hB hC m
  have hpos : 0 ≤ (C * θ / B) ^ m := pow_nonneg (by linarith) m
  exact_mod_cast (show (C * θ / B) ^ m ≤ verticalWeight θ B C m by linarith)

theorem dimension_over_vertical_tendsto {θ B C : ℚ} (hθ : 0 < θ) (hB : 0 < B)
    (hC : 1 ≤ C) (hr : 1 < C * θ / B) :
    Tendsto (fun m : ℕ => (m : ℝ) / (verticalWeight θ B C m : ℝ)) atTop (𝓝 0) := by
  have hz := tendsto_pow_const_div_const_pow_of_one_lt 1
    (show (1 : ℝ) < ((C * θ / B : ℚ) : ℝ) by exact_mod_cast hr)
  simp only [pow_one] at hz
  apply squeeze_zero _ _ hz
  · intro m
    have hv : (0 : ℝ) < (verticalWeight θ B C m : ℝ) := by
      exact_mod_cast verticalWeight_pos hθ hB hC m
    positivity
  · intro m
    have hp : (0 : ℝ) < ((C * θ / B : ℚ) : ℝ) ^ m := by
      have : (0 : ℝ) < ((C * θ / B : ℚ) : ℝ) := by exact_mod_cast (show 0 < C * θ / B by linarith)
      positivity
    apply div_le_div_of_nonneg_left (Nat.cast_nonneg _) hp
    have hl := verticalWeight_lower hθ hB hC m
    have hq : 0 ≤ (C * θ / B) ^ m := pow_nonneg (by linarith) m
    exact_mod_cast (show (C * θ / B) ^ m ≤ verticalWeight θ B C m by linarith)

/-- All dimension requirements can be imposed at once, including any fixed
multiple of the arithmetic term `m/v₀`. The constants are chosen before `m`. -/
theorem exists_dimension (n : ℕ) (hn : 1 ≤ n) (ε A D R : ℝ) (hε : 0 < ε)
    (m₀ : ℕ) : ∃ m : ℕ, m₀ ≤ m ∧
      ((centerCount (c (delta n)) m : ℚ) / horizontalWeight (b (delta n)) m : ℝ) < ε ∧
      A * ((m : ℝ) / (verticalWeight (theta (delta n)) (b (delta n)) (c (delta n)) m : ℝ)) < ε ∧
      D < (verticalWeight (theta (delta n)) (b (delta n)) (c (delta n)) m : ℝ) ∧
      R < ((b (delta n) / a (delta n) : ℚ) : ℝ) ^ m / ((m : ℝ) + 1) := by
  have hs := shape n hn
  have hb := hs.theta_pos.trans (hs.theta_lt_a.trans hs.a_lt_b)
  have hr := (growth_ratios n hn).1
  have hc := count_over_horizontal_tendsto hb hs.one_lt_c.le hs.cb_lt_one
  have hm := dimension_over_vertical_tendsto hs.theta_pos hb hs.one_lt_c.le hr
  have hv := verticalWeight_tendsto hs.theta_pos hb hs.one_lt_c.le hr
  have hA : Tendsto (fun m : ℕ => A * ((m : ℝ) /
      (verticalWeight (theta (delta n)) (b (delta n)) (c (delta n)) m : ℝ)))
      atTop (𝓝 0) := by simpa using hm.const_mul A
  have he := (hc.eventually_lt_const hε).and (hA.eventually_lt_const hε)
  have he' := he.and ((hv.eventually (eventually_gt_atTop D)).and
    ((dimension_growth n hn).2.2.eventually (eventually_gt_atTop R)))
  obtain ⟨m, hm₀, ⟨hmc, hmA⟩, hmD, hmR⟩ :=
    ((eventually_ge_atTop m₀).and he').exists
  exact ⟨m, hm₀, by exact_mod_cast hmc, hmA, hmD, hmR⟩

theorem chosen_volume_ratio {θ B C : ℚ} (hθ : 0 < θ) (hB : 0 < B)
    (hC : 1 ≤ C) (m : ℕ) :
    (centerCount C m : ℚ) * (horizontalWeight B m / verticalWeight θ B C m) * θ ^ m =
      1 / 2 := by
  apply volume_ratio_half
  · exact_mod_cast (centerCount_pos hC m).ne'
  · exact (horizontalWeight_pos hB m).ne'
  · exact hθ.ne'

end LogTwo.Parameters
end Source0007

-- Source: LogTwo/Geometry/Centers.lean
section Source0008
-- Modified in this edition: unused plain lemmas removed; see reduction.json.
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

end LogTwo.Geometry
end Source0008

-- Source: LogTwo/Matrix.lean
section Source0009
-- Modified in this edition: unused plain lemmas removed; see reduction.json.
/-!
The rational coefficient matrix from equation (3.2) of the supplied manuscript.
`FullRowMinor` records the missing interpolation output; no instance or existence
theorem is postulated. In particular it requires every admissible row.
-/
namespace LogTwo.Interpolation

open MvPolynomial
noncomputable section

structure Row (m : ℕ) where
  j : ℕ
  s : ℕ
  beta : Fin m → ℕ
  deriving DecidableEq

structure Column (m : ℕ) where
  h : ℕ
  alpha : Fin m → ℕ
  deriving DecidableEq

def truncatedLog {m : ℕ} (T : ℕ) : MvPolynomial (Option (Fin m)) ℚ :=
  ∑ k ∈ Finset.Ico 1 T, C ((-1 : ℚ) ^ (k + 1) / (k : ℚ)) * X none ^ k

def rowExponent {m : ℕ} (r : Row m) : Option (Fin m) →₀ ℕ :=
  Finsupp.equivFunOnFinite.symm (fun i => match i with
    | none => r.s
    | some k => r.beta k)

def columnExpansion {m : ℕ} (r : Fin m → ℚ) (T : Fin m → ℕ)
    (j : ℕ) (col : Column m) : MvPolynomial (Option (Fin m)) ℚ :=
  C ((2 : ℚ) ^ (j * col.h)) * (1 + X none) ^ col.h *
    ∏ i, (C ((j : ℚ) * r i) + truncatedLog (T i) + X (some i)) ^ col.alpha i

def coefficientMatrix {m : ℕ} (r : Fin m → ℚ) (T : Fin m → ℕ) :
    Matrix (Row m) (Column m) ℚ :=
  fun row col => (columnExpansion r T row.j col).coeff (rowExponent row)

def valueRow (m j : ℕ) : Row m := ⟨j, 0, fun _ => 0⟩
def oneColumn (m : ℕ) : Column m := ⟨0, fun _ => 0⟩
def yColumn (m : ℕ) : Column m := ⟨1, fun _ => 0⟩

@[simp] theorem valueRow_exponent (m j : ℕ) : rowExponent (valueRow m j) = 0 := by
  ext i
  cases i <;> rfl

structure Weights (m : ℕ) where
  K : ℕ
  w0 : ℚ
  v0 : ℚ
  w : Fin m → ℚ
  theta : ℚ
  w0_pos : 0 < w0
  v0_pos : 0 < v0
  w_pos : ∀ i, 0 < w i
  theta_pos : 0 < theta
  theta_lt_one : theta < 1

def AdmissibleRow {m : ℕ} (w : Weights m) (H : ℚ) (r : Row m) : Prop :=
  r.j < w.K ∧ w.v0 * r.s + (∑ i, w.w i * r.beta i) / w.theta < H

def AdmissibleColumn {m : ℕ} (w : Weights m) (H : ℚ) (c : Column m) : Prop :=
  w.w0 * c.h + ∑ i, w.w i * c.alpha i ≤ H

/-- A single square minor, with all the rows required by the manuscript. -/
structure FullRowMinor {m : ℕ} (w : Weights m) (H : ℚ)
    (r : Fin m → ℚ) (T : Fin m → ℕ) where
  size : ℕ
  rows : Fin size → Row m
  columns : Fin size → Column m
  rows_injective : Function.Injective rows
  columns_injective : Function.Injective columns
  row_valid : ∀ k, AdmissibleRow w H (rows k)
  all_rows : ∀ row, AdmissibleRow w H row → ∃ k, rows k = row
  column_valid : ∀ k, AdmissibleColumn w H (columns k)
  det_ne_zero : (Matrix.of (fun i j => coefficientMatrix r T (rows i) (columns j))).det ≠ 0

def FullRowMinor.matrix {m : ℕ} {w : Weights m} {H : ℚ}
    {r : Fin m → ℚ} {T : Fin m → ℕ} (minor : FullRowMinor w H r T) :
    Matrix (Fin minor.size) (Fin minor.size) ℚ :=
  fun i j => coefficientMatrix r T (minor.rows i) (minor.columns j)

theorem FullRowMinor.matrix_det_ne_zero {m : ℕ} {w : Weights m} {H : ℚ}
    {r : Fin m → ℚ} {T : Fin m → ℕ} (minor : FullRowMinor w H r T) :
    minor.matrix.det ≠ 0 := minor.det_ne_zero

end
end LogTwo.Interpolation
end Source0009

-- Source: LogTwo/Determinant.lean
section Source0010
-- Modified in this edition: unused plain lemmas removed; see reduction.json.
namespace LogTwo.Determinant

open scoped BigOperators

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

def scale (A : Matrix ι ι ℚ) (r c : ι → ℚ) : Matrix ι ι ℚ :=
  fun i j => r i * A i j * c j

theorem det_scale (A : Matrix ι ι ℚ) (r c : ι → ℚ) :
    (scale A r c).det = ((∏ i, r i) * (∏ i, c i)) * A.det := by
  have heq : scale A r c = Matrix.diagonal r * A * Matrix.diagonal c := by
    ext i j
    simp [scale]
  rw [heq, Matrix.det_mul, Matrix.det_mul, Matrix.det_diagonal, Matrix.det_diagonal]
  ring

/-- Clearing denominators in the very same minor gives a nonzero integer determinant. -/
theorem scaled_integer_det_ne_zero (A : Matrix ι ι ℚ) (r c : ι → ℚ)
    (Z : Matrix ι ι ℤ) (hA : A.det ≠ 0)
    (hr : ∀ i, r i ≠ 0) (hc : ∀ i, c i ≠ 0)
    (hZ : ∀ i j, (Z i j : ℚ) = scale A r c i j) : Z.det ≠ 0 := by
  have heq : (Z.det : ℚ) = (scale A r c).det := by
    rw [Int.cast_det]
    congr 1
    ext i j
    exact hZ i j
  have hn : (Z.det : ℚ) ≠ 0 := by
    rw [heq, det_scale]
    exact mul_ne_zero (mul_ne_zero (Finset.prod_ne_zero_iff.mpr (by simpa using hr))
      (Finset.prod_ne_zero_iff.mpr (by simpa using hc))) hA
  exact fun hz => hn (by simp [hz])

/-- The generic arithmetic lower bound; the concrete denominator estimates are separate. -/
theorem scaled_integer_lower_bound (A : Matrix ι ι ℚ) (r c : ι → ℚ)
    (Z : Matrix ι ι ℤ) (hA : A.det ≠ 0)
    (hr : ∀ i, r i ≠ 0) (hc : ∀ i, c i ≠ 0)
    (hZ : ∀ i j, (Z i j : ℚ) = scale A r c i j) :
    (1 : ℚ) ≤ |((∏ i, r i) * (∏ i, c i)) * A.det| := by
  have hn := scaled_integer_det_ne_zero A r c Z hA hr hc hZ
  have hi : (1 : ℤ) ≤ |Z.det| := by
    have := abs_pos.mpr hn
    omega
  have heq : (Z.det : ℚ) = ((∏ i, r i) * (∏ i, c i)) * A.det := by
    rw [← det_scale, Int.cast_det]
    congr 1
    ext i j
    exact hZ i j
  rw [← heq]
  exact_mod_cast hi

end LogTwo.Determinant
end Source0010

-- Source: LogTwo/Rescale.lean
section Source0011
/-! Diagonal variable substitution, with an exact coefficient formula. -/
namespace LogTwo.Polynomial

open MvPolynomial
noncomputable section

variable {σ : Type*}

def rescale (a : σ → ℚ) : MvPolynomial σ ℚ →+* MvPolynomial σ ℚ :=
  eval₂Hom C (fun i => C (a i) * X i)

@[simp] theorem rescale_C (a : σ → ℚ) (b : ℚ) : rescale a (C b) = C b := by
  simp [rescale]

@[simp] theorem rescale_X (a : σ → ℚ) (i : σ) : rescale a (X i) = C (a i) * X i := by
  simp [rescale]

variable [Fintype σ]

theorem rescale_monomial (a : σ → ℚ) (d : σ →₀ ℕ) (b : ℚ) :
    rescale a (monomial d b) = monomial d (b * ∏ i, a i ^ d i) := by
  rw [rescale, eval₂Hom_monomial, monomial_eq]
  rw [Finsupp.prod_fintype d (fun i k => (C (a i) * X i) ^ k) (by intro i; simp)]
  rw [Finsupp.prod_fintype d (fun i k => (X i : MvPolynomial σ ℚ) ^ k) (by intro i; simp)]
  simp only [mul_pow, ← map_pow,
    Finset.prod_mul_distrib, ← map_prod, map_mul, mul_assoc]

theorem coeff_rescale (a : σ → ℚ) (P : MvPolynomial σ ℚ) (d : σ →₀ ℕ) :
    (rescale a P).coeff d = P.coeff d * ∏ i, a i ^ d i := by
  classical
  induction P using MvPolynomial.induction_on' with
  | add p q hp hq => simp [map_add, hp, hq, add_mul]
  | monomial e b =>
    rw [rescale_monomial]
    by_cases he : e = d
    · subst e; simp
    · simp [MvPolynomial.coeff_monomial, he]

end
end LogTwo.Polynomial
end Source0011

-- Source: LogTwo/LogDenominator.lean
section Source0012
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
end Source0012

-- Source: LogTwo/Arithmetic.lean
section Source0013
/-!
Concrete denominator clearing for the matrix (3.2). The row multiplier retains
the factor q_i^(-beta_i), which is essential in the manuscript's arithmetic bound.
-/
namespace LogTwo.Arithmetic

open MvPolynomial LogTwo.Interpolation LogTwo.Polynomial
noncomputable section

def rationalPoint {m : ℕ} (p : Fin m → ℤ) (q : Fin m → ℕ) : Fin m → ℚ :=
  fun i => (p i : ℚ) / (q i : ℚ)

def variableScale {m : ℕ} (q : Fin m → ℕ) : Option (Fin m) → ℚ
  | none => 1
  | some i => (q i : ℚ)⁻¹

def rowMultiplier {m : ℕ} (q : Fin m → ℕ) (r : Row m) : ℚ :=
  ∏ i, ((q i : ℚ)⁻¹) ^ r.beta i

def columnMultiplier {m : ℕ} (q T : Fin m → ℕ) (c : Column m) : ℚ :=
  ∏ i, ((q i : ℚ) * (lcmBelow (T i) : ℚ)) ^ c.alpha i

theorem rescale_truncatedLog {m : ℕ} (q : Fin m → ℕ) (T : ℕ) :
    rescale (variableScale q) (truncatedLog T) = truncatedLog T := by
  simp [truncatedLog, map_sum, variableScale]

theorem coeff_rescale_row {m : ℕ} (q : Fin m → ℕ)
    (P : MvPolynomial (Option (Fin m)) ℚ) (r : Row m) :
    (rescale (variableScale q) P).coeff (rowExponent r) =
      P.coeff (rowExponent r) * rowMultiplier q r := by
  rw [coeff_rescale]
  simp [rowMultiplier, rowExponent, variableScale, Fintype.prod_option]

def integerFactor {m : ℕ} (p : ℤ) (q T j : ℕ) (i : Fin m) :
    MvPolynomial (Option (Fin m)) ℤ :=
  C ((lcmBelow T : ℤ) * (j : ℤ) * p) + C (q : ℤ) * integerLog T +
    C (lcmBelow T : ℤ) * X (some i)

theorem map_integerFactor {m : ℕ} (p : Fin m → ℤ) (q T : Fin m → ℕ)
    (hq : ∀ i, q i ≠ 0) (j : ℕ) (i : Fin m) :
    MvPolynomial.map (Int.castRingHom ℚ) (integerFactor (p i) (q i) (T i) j i) =
      C ((q i : ℚ) * (lcmBelow (T i) : ℚ)) *
        rescale (variableScale q)
          (C ((j : ℚ) * rationalPoint p q i) + truncatedLog (T i) + X (some i)) := by
  have hqi : (q i : ℚ) ≠ 0 := by exact_mod_cast hq i
  simp only [integerFactor, map_add, map_mul, MvPolynomial.map_C, MvPolynomial.map_X,
    map_integerLog, rescale_C, rescale_truncatedLog, rescale_X, variableScale]
  change C (lcmBelow (T i) : ℚ) * C (j : ℚ) * C (p i : ℚ) +
      C (q i : ℚ) * (C (lcmBelow (T i) : ℚ) * truncatedLog (T i)) +
      C (lcmBelow (T i) : ℚ) * X (some i) = _
  simp only [← map_mul, rationalPoint]
  have hconst : (q i : ℚ) * lcmBelow (T i) * ((j : ℚ) * ((p i : ℚ) / q i)) =
      (lcmBelow (T i) : ℚ) * j * p i := by field_simp
  have hvar : (q i : ℚ) * lcmBelow (T i) * (q i : ℚ)⁻¹ = lcmBelow (T i) := by
    field_simp
  simp only [mul_add, ← mul_assoc, ← map_mul, hconst, hvar]

def integerColumnExpansion {m : ℕ} (p : Fin m → ℤ) (q T : Fin m → ℕ)
    (j : ℕ) (col : Column m) : MvPolynomial (Option (Fin m)) ℤ :=
  C ((2 : ℤ) ^ (j * col.h)) * (1 + X none) ^ col.h *
    ∏ i, (integerFactor (p i) (q i) (T i) j i) ^ col.alpha i

theorem map_integerColumnExpansion {m : ℕ} (p : Fin m → ℤ) (q T : Fin m → ℕ)
    (hq : ∀ i, q i ≠ 0) (j : ℕ) (col : Column m) :
    MvPolynomial.map (Int.castRingHom ℚ) (integerColumnExpansion p q T j col) =
      C (columnMultiplier q T col) *
        rescale (variableScale q) (columnExpansion (rationalPoint p q) T j col) := by
  simp only [integerColumnExpansion, map_mul, map_pow, map_prod,
    map_integerFactor p q T hq, columnMultiplier, columnExpansion]
  simp only [map_mul, map_add, map_one,
    MvPolynomial.map_X, rescale_C, rescale_X, variableScale, map_ofNat, one_mul,
    mul_pow, Finset.prod_mul_distrib]
  ring

def integerMatrix {m : ℕ} (p : Fin m → ℤ) (q T : Fin m → ℕ) :
    Matrix (Row m) (Column m) ℤ :=
  fun row col => (integerColumnExpansion p q T row.j col).coeff (rowExponent row)

/-- Exact integer clearing, including the denominator saving from the row multi-index. -/
theorem integerMatrix_cast {m : ℕ} (p : Fin m → ℤ) (q T : Fin m → ℕ)
    (hq : ∀ i, q i ≠ 0) (row : Row m) (col : Column m) :
    (integerMatrix p q T row col : ℚ) =
      rowMultiplier q row * coefficientMatrix (rationalPoint p q) T row col *
        columnMultiplier q T col := by
  have he := congrArg (fun P : MvPolynomial (Option (Fin m)) ℚ => P.coeff (rowExponent row))
    (map_integerColumnExpansion p q T hq row.j col)
  rw [MvPolynomial.coeff_map, MvPolynomial.coeff_C_mul, coeff_rescale_row] at he
  change (integerMatrix p q T row col : ℚ) =
    columnMultiplier q T col *
      (coefficientMatrix (rationalPoint p q) T row col * rowMultiplier q row) at he
  rw [he]
  ring

theorem rowMultiplier_ne_zero {m : ℕ} (q : Fin m → ℕ) (hq : ∀ i, q i ≠ 0) (r : Row m) :
    rowMultiplier q r ≠ 0 := by
  apply Finset.prod_ne_zero_iff.mpr
  intro i _
  exact pow_ne_zero _ (inv_ne_zero (by exact_mod_cast hq i))

theorem columnMultiplier_ne_zero {m : ℕ} (q T : Fin m → ℕ)
    (hq : ∀ i, q i ≠ 0) (c : Column m) : columnMultiplier q T c ≠ 0 := by
  apply Finset.prod_ne_zero_iff.mpr
  intro i _
  apply pow_ne_zero
  exact mul_ne_zero (by exact_mod_cast hq i) (by exact_mod_cast lcmBelow_ne_zero (T i))

theorem rowMultiplier_pos {m : ℕ} (q : Fin m → ℕ) (hq : ∀ i, q i ≠ 0) (r : Row m) :
    0 < rowMultiplier q r := by
  apply Finset.prod_pos
  intro i _
  apply pow_pos
  apply inv_pos.mpr
  exact_mod_cast Nat.pos_of_ne_zero (hq i)

theorem columnMultiplier_pos {m : ℕ} (q T : Fin m → ℕ)
    (hq : ∀ i, q i ≠ 0) (c : Column m) : 0 < columnMultiplier q T c := by
  apply Finset.prod_pos
  intro i _
  apply pow_pos
  exact mul_pos (by exact_mod_cast Nat.pos_of_ne_zero (hq i))
    (by exact_mod_cast lcmBelow_pos (T i))

def integerMinor {m : ℕ} {w : Weights m} {H : ℚ}
    (p : Fin m → ℤ) (q T : Fin m → ℕ)
    (minor : FullRowMinor w H (rationalPoint p q) T) :
    Matrix (Fin minor.size) (Fin minor.size) ℤ :=
  fun i j => integerMatrix p q T (minor.rows i) (minor.columns j)

/-- Arithmetic lower bound for the actual full-row minor, with no integrality hypothesis left. -/
theorem fullRowMinor_arithmetic_bound {m : ℕ} {w : Weights m} {H : ℚ}
    (p : Fin m → ℤ) (q T : Fin m → ℕ) (hq : ∀ i, q i ≠ 0)
    (minor : FullRowMinor w H (rationalPoint p q) T) :
    (1 : ℚ) ≤ |((∏ i, rowMultiplier q (minor.rows i)) *
      (∏ j, columnMultiplier q T (minor.columns j))) * minor.matrix.det| := by
  apply LogTwo.Determinant.scaled_integer_lower_bound minor.matrix
    (fun i => rowMultiplier q (minor.rows i))
    (fun j => columnMultiplier q T (minor.columns j)) (integerMinor p q T minor)
    minor.matrix_det_ne_zero
  · intro i; exact rowMultiplier_ne_zero q hq _
  · intro j; exact columnMultiplier_ne_zero q T hq _
  · intro i j
    exact integerMatrix_cast p q T hq (minor.rows i) (minor.columns j)

end
end LogTwo.Arithmetic
end Source0013

-- Source: LogTwo/LogarithmicBound.lean
section Source0014
namespace LogTwo.Arithmetic

open LogTwo.Interpolation
noncomputable section

def rowLogSaving {m : ℕ} (q : Fin m → ℕ) (r : Row m) : ℝ :=
  ∑ i, (r.beta i : ℝ) * Real.log (q i : ℝ)

def columnLogCost {m : ℕ} (q T : Fin m → ℕ) (c : Column m) : ℝ :=
  ∑ i, (c.alpha i : ℝ) * (Real.log (q i : ℝ) + Real.log (lcmBelow (T i) : ℝ))

theorem log_rowMultiplier {m : ℕ} (q : Fin m → ℕ) (hq : ∀ i, q i ≠ 0) (r : Row m) :
    Real.log (rowMultiplier q r : ℝ) = -rowLogSaving q r := by
  simp only [rowMultiplier, Rat.cast_prod, Rat.cast_pow, Rat.cast_inv, Rat.cast_natCast]
  rw [Real.log_prod (fun i _ => pow_ne_zero _ (inv_ne_zero (by exact_mod_cast hq i)))]
  simp [Real.log_pow, Real.log_inv, rowLogSaving, Finset.sum_neg_distrib]

theorem log_columnMultiplier {m : ℕ} (q T : Fin m → ℕ)
    (hq : ∀ i, q i ≠ 0) (c : Column m) :
    Real.log (columnMultiplier q T c : ℝ) = columnLogCost q T c := by
  simp only [columnMultiplier, Rat.cast_prod, Rat.cast_pow, Rat.cast_mul, Rat.cast_natCast]
  rw [Real.log_prod (fun i _ => pow_ne_zero _ (mul_ne_zero
    (by exact_mod_cast hq i) (by exact_mod_cast lcmBelow_ne_zero (T i))))]
  apply Finset.sum_congr rfl
  intro i _
  rw [Real.log_pow, Real.log_mul (by exact_mod_cast hq i)
    (by exact_mod_cast lcmBelow_ne_zero (T i))]

/-- Exact logarithmic lower bound for the same minor used by interpolation. -/
theorem fullRowMinor_logarithmic_bound {m : ℕ} {w : Weights m} {H : ℚ}
    (p : Fin m → ℤ) (q T : Fin m → ℕ) (hq : ∀ i, q i ≠ 0)
    (minor : FullRowMinor w H (rationalPoint p q) T) :
    (∑ i, rowLogSaving q (minor.rows i)) - (∑ j, columnLogCost q T (minor.columns j)) ≤
      Real.log |(minor.matrix.det : ℝ)| := by
  let R : ℚ := ∏ i, rowMultiplier q (minor.rows i)
  let C : ℚ := ∏ j, columnMultiplier q T (minor.columns j)
  have hr : 0 < R := Finset.prod_pos (fun i _ => rowMultiplier_pos q hq _)
  have hc : 0 < C := Finset.prod_pos (fun j _ => columnMultiplier_pos q T hq _)
  have hr' : (0 : ℝ) < R := by exact_mod_cast hr
  have hc' : (0 : ℝ) < C := by exact_mod_cast hc
  have hd : (0 : ℝ) < |(minor.matrix.det : ℝ)| := by
    apply abs_pos.mpr
    exact_mod_cast minor.matrix_det_ne_zero
  have hb := fullRowMinor_arithmetic_bound p q T hq minor
  have hb' : (1 : ℝ) ≤ |((R * C : ℚ) : ℝ) * (minor.matrix.det : ℝ)| := by
    exact_mod_cast hb
  rw [Rat.cast_mul, abs_mul, abs_of_pos (mul_pos hr' hc')] at hb'
  have hh := Real.log_le_log (by norm_num : (0 : ℝ) < 1) hb'
  rw [Real.log_one, Real.log_mul (mul_pos hr' hc').ne' hd.ne',
    Real.log_mul hr'.ne' hc'.ne'] at hh
  have hR : Real.log (R : ℝ) = -∑ i, rowLogSaving q (minor.rows i) := by
    dsimp [R]
    rw [Rat.cast_prod, Real.log_prod (fun i _ => by
      exact_mod_cast rowMultiplier_ne_zero q hq (minor.rows i))]
    simp only [log_rowMultiplier q hq, Finset.sum_neg_distrib]
  have hC : Real.log (C : ℝ) = ∑ j, columnLogCost q T (minor.columns j) := by
    dsimp [C]
    rw [Rat.cast_prod, Real.log_prod (fun j _ => by
      exact_mod_cast columnMultiplier_ne_zero q T hq (minor.columns j))]
    simp only [log_columnMultiplier q T hq]
  rw [hR, hC] at hh
  linarith

/-- Each weighted column has a coordinate bound needed for the uniform denominator D_H. -/
theorem alpha_le_floor {m : ℕ} (w : Weights m) (H : ℚ) (c : Column m)
    (hc : AdmissibleColumn w H c) (i : Fin m) : c.alpha i ≤ ⌊H / w.w i⌋₊ := by
  have hsum : w.w i * c.alpha i ≤ ∑ k, w.w k * c.alpha k :=
    Finset.single_le_sum (fun k _ => mul_nonneg (w.w_pos k).le (Nat.cast_nonneg _))
      (Finset.mem_univ i)
  have hh : w.w i * c.alpha i ≤ H := by
    have hzero : 0 ≤ w.w0 * c.h := mul_nonneg w.w0_pos.le (Nat.cast_nonneg _)
    dsimp [AdmissibleColumn] at hc
    linarith
  have hdiv : (c.alpha i : ℚ) ≤ H / w.w i := by
    apply (le_div_iff₀ (w.w_pos i)).mpr
    simpa only [mul_comm] using hh
  exact (Nat.le_floor_iff ((Nat.cast_nonneg _).trans hdiv)).mpr hdiv

def denominatorBudget {m : ℕ} (w : Weights m) (H : ℚ) (T : Fin m → ℕ) : ℝ :=
  ∑ i, (⌊H / w.w i⌋₊ : ℝ) * Real.log (lcmBelow (T i) : ℝ)

def columnQCost {m : ℕ} (q : Fin m → ℕ) (c : Column m) : ℝ :=
  ∑ i, (c.alpha i : ℝ) * Real.log (q i : ℝ)

theorem columnLogCost_le {m : ℕ} (w : Weights m) (H : ℚ) (q T : Fin m → ℕ)
    (c : Column m) (hc : AdmissibleColumn w H c) :
    columnLogCost q T c ≤ columnQCost q c + denominatorBudget w H T := by
  unfold columnLogCost columnQCost denominatorBudget
  simp_rw [mul_add]
  rw [Finset.sum_add_distrib]
  apply add_le_add le_rfl
  apply Finset.sum_le_sum
  intro i _
  apply mul_le_mul_of_nonneg_right
  · exact_mod_cast alpha_le_floor w H c hc i
  · apply Real.log_nonneg
    exact_mod_cast (Nat.one_le_iff_ne_zero.mpr (lcmBelow_ne_zero (T i)))

/-- The manuscript's uniform denominator version, before bounding log lcm. -/
theorem fullRowMinor_uniform_log_bound {m : ℕ} {w : Weights m} {H : ℚ}
    (p : Fin m → ℤ) (q T : Fin m → ℕ) (hq : ∀ i, q i ≠ 0)
    (minor : FullRowMinor w H (rationalPoint p q) T) :
    (∑ i, rowLogSaving q (minor.rows i)) -
      (∑ j, columnQCost q (minor.columns j)) -
      (minor.size : ℝ) * denominatorBudget w H T ≤ Real.log |(minor.matrix.det : ℝ)| := by
  have hcost : (∑ j, columnLogCost q T (minor.columns j)) ≤
      (∑ j, columnQCost q (minor.columns j)) + (minor.size : ℝ) * denominatorBudget w H T := by
    calc
      _ ≤ ∑ j, (columnQCost q (minor.columns j) + denominatorBudget w H T) :=
        Finset.sum_le_sum (fun j _ => columnLogCost_le w H q T _ (minor.column_valid j))
      _ = _ := by simp [Finset.sum_add_distrib]
  have hbound := fullRowMinor_logarithmic_bound p q T hq minor
  linarith

end
end LogTwo.Arithmetic
end Source0014

-- Source: LogTwo/LcmBound.lean
section Source0015
-- Modified in this edition: unused plain lemmas removed; see reduction.json.
/-!
A deliberately weaker absolute constant than the manuscript's 4*log 2:
Mathlib directly proves the sufficient linear bound with log 4 + 4. Keeping this
choice explicit avoids silently claiming the sharper numerical estimate.
-/
namespace LogTwo.Arithmetic

open LogTwo.Interpolation
noncomputable section

def lcmConstant : ℝ := Real.log 4 + 4

theorem lcmConstant_pos : 0 < lcmConstant := by
  have := Real.log_pos (by norm_num : (1 : ℝ) < 4)
  dsimp [lcmConstant]
  linarith

theorem lcmBelow_dvd_lcmUpto (T : ℕ) : lcmBelow T ∣ Nat.lcmUpto T := by
  apply Finset.lcm_dvd
  intro k hk
  apply Finset.dvd_lcm (f := id)
  exact Finset.mem_Icc.mpr ⟨(Finset.mem_Ico.mp hk).1, (Finset.mem_Ico.mp hk).2.le⟩

theorem log_lcmBelow_le (T : ℕ) :
    Real.log (lcmBelow T : ℝ) ≤ lcmConstant * T := by
  calc
    _ ≤ Real.log (Nat.lcmUpto T : ℝ) := by
      apply Real.log_le_log (by exact_mod_cast lcmBelow_pos T)
      exact_mod_cast Nat.le_of_dvd (Nat.lcmUpto_pos T) (lcmBelow_dvd_lcmUpto T)
    _ ≤ _ := by
      rw [← Chebyshev.psi_eq_log_lcmUpto]
      exact Chebyshev.psi_le_const_mul_self (by positivity)

theorem denominatorBudget_le {m : ℕ} (w : Weights m) (H : ℚ) (hH : 0 ≤ H)
    (T : Fin m → ℕ) :
    denominatorBudget w H T ≤
      (H : ℝ) * lcmConstant * ∑ i, (T i : ℝ) / (w.w i : ℝ) := by
  unfold denominatorBudget
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro i _
  have hf : (⌊H / w.w i⌋₊ : ℝ) ≤ (H : ℝ) / (w.w i : ℝ) := by
    exact_mod_cast Nat.floor_le (div_nonneg hH (w.w_pos i).le)
  calc
    _ ≤ (⌊H / w.w i⌋₊ : ℝ) * (lcmConstant * T i) :=
      mul_le_mul_of_nonneg_left (log_lcmBelow_le (T i)) (Nat.cast_nonneg _)
    _ ≤ ((H : ℝ) / (w.w i : ℝ)) * (lcmConstant * T i) :=
      mul_le_mul_of_nonneg_right hf (mul_nonneg lcmConstant_pos.le (Nat.cast_nonneg _))
    _ = _ := by ring

def truncationOrders {m : ℕ} (w : Weights m) (F : ℚ) : Fin m → ℕ :=
  fun i => ⌈F * w.w i / w.v0⌉₊

theorem sum_truncation_div_le {m : ℕ} (w : Weights m) (F : ℚ) (hF : 0 ≤ F) :
    (∑ i, (truncationOrders w F i : ℝ) / (w.w i : ℝ)) ≤
      (F : ℝ) * m / (w.v0 : ℝ) + ∑ i, 1 / (w.w i : ℝ) := by
  calc
    _ ≤ ∑ i, (((F : ℝ) * (w.w i : ℝ) / (w.v0 : ℝ) + 1) / (w.w i : ℝ)) := by
      apply Finset.sum_le_sum
      intro i _
      apply div_le_div_of_nonneg_right _ (by exact_mod_cast (w.w_pos i).le)
      have hh := (Nat.ceil_lt_add_one (div_nonneg (mul_nonneg hF (w.w_pos i).le) w.v0_pos.le)).le
      exact_mod_cast hh
    _ = ∑ i, ((F : ℝ) / (w.v0 : ℝ) + 1 / (w.w i : ℝ)) := by
      apply Finset.sum_congr rfl
      intro i _
      field_simp [(show (w.w i : ℝ) ≠ 0 by exact_mod_cast (w.w_pos i).ne'),
        (show (w.v0 : ℝ) ≠ 0 by exact_mod_cast w.v0_pos.ne')]
    _ = _ := by simp [Finset.sum_add_distrib]; ring

theorem truncation_denominatorBudget_le {m : ℕ} (w : Weights m)
    (H F : ℚ) (hH : 0 ≤ H) (hF : 0 ≤ F) :
    denominatorBudget w H (truncationOrders w F) ≤
      (H : ℝ) * (lcmConstant * (F : ℝ) * m / (w.v0 : ℝ) +
        lcmConstant * ∑ i, 1 / (w.w i : ℝ)) := by
  calc
    _ ≤ (H : ℝ) * lcmConstant * ∑ i, (truncationOrders w F i : ℝ) / (w.w i : ℝ) :=
      denominatorBudget_le w H hH _
    _ ≤ (H : ℝ) * lcmConstant * ((F : ℝ) * m / (w.v0 : ℝ) + ∑ i, 1 / (w.w i : ℝ)) :=
      mul_le_mul_of_nonneg_left (sum_truncation_div_le w F hF)
        (mul_nonneg (by exact_mod_cast hH) lcmConstant_pos.le)
    _ = _ := by ring

end
end LogTwo.Arithmetic
end Source0015

-- Source: LogTwo/ArithmeticEstimate.lean
section Source0016
/-! Normalized arithmetic estimate, with the row saving preserved. -/
namespace LogTwo.Arithmetic

open LogTwo.Interpolation
noncomputable section

def ceilLogWeight (q : ℕ) : ℚ := (⌈Real.log (q : ℝ)⌉₊ : ℚ)

theorem ceilLogWeight_bounds (q : ℕ) :
    Real.log (q : ℝ) ≤ (ceilLogWeight q : ℝ) ∧
    (ceilLogWeight q : ℝ) - 1 ≤ Real.log (q : ℝ) := by
  simp only [ceilLogWeight, Rat.cast_natCast]
  exact ⟨Nat.le_ceil _, by linarith [Nat.ceil_lt_add_one (Real.log_natCast_nonneg q)]⟩

def rowWeight {m : ℕ} (w : Weights m) (r : Row m) : ℝ :=
  ∑ i, (w.w i : ℝ) * (r.beta i : ℝ)

theorem rowWeight_lt {m : ℕ} (w : Weights m) (H : ℚ) (r : Row m)
    (hr : AdmissibleRow w H r) : rowWeight w r < (w.theta : ℝ) * (H : ℝ) := by
  have hz : (0 : ℚ) ≤ w.v0 * r.s := mul_nonneg w.v0_pos.le (Nat.cast_nonneg _)
  have hh : (∑ i, w.w i * r.beta i) / w.theta < H := by
    have := hr.2
    linarith
  have hh' := (div_lt_iff₀ w.theta_pos).mp hh
  simpa only [rowWeight, Rat.cast_sum, Rat.cast_mul, Rat.cast_natCast, mul_comm] using
    (show ((∑ i, w.w i * r.beta i : ℚ) : ℝ) < ((H * w.theta : ℚ) : ℝ) by exact_mod_cast hh')

theorem columnQCost_le_height {m : ℕ} (w : Weights m) (H : ℚ) (q : Fin m → ℕ)
    (hlog : ∀ i, Real.log (q i : ℝ) ≤ (w.w i : ℝ))
    (c : Column m) (hc : AdmissibleColumn w H c) : columnQCost q c ≤ (H : ℝ) := by
  have hh : (∑ i, w.w i * c.alpha i) ≤ H := by
    have hz : (0 : ℚ) ≤ w.w0 * c.h := mul_nonneg w.w0_pos.le (Nat.cast_nonneg _)
    dsimp [AdmissibleColumn] at hc
    linarith
  calc
    _ ≤ ∑ i, (c.alpha i : ℝ) * (w.w i : ℝ) :=
      Finset.sum_le_sum (fun i _ => mul_le_mul_of_nonneg_left (hlog i) (Nat.cast_nonneg _))
    _ ≤ _ := by
      simpa only [Rat.cast_sum, Rat.cast_mul, Rat.cast_natCast, mul_comm] using
        (show ((∑ i, w.w i * c.alpha i : ℚ) : ℝ) ≤ (H : ℝ) by exact_mod_cast hh)

theorem rowLogSaving_lower {m : ℕ} (w : Weights m) (H : ℚ) (q : Fin m → ℕ)
    (hlog : ∀ i, (w.w i : ℝ) - 1 ≤ Real.log (q i : ℝ))
    (wmin : ℝ) (hmin : 0 < wmin) (hweights : ∀ i, wmin ≤ (w.w i : ℝ))
    (r : Row m) (hr : AdmissibleRow w H r) :
    rowWeight w r - (w.theta : ℝ) * (H : ℝ) / wmin ≤ rowLogSaving q r := by
  have hcount : wmin * ∑ i, (r.beta i : ℝ) ≤ rowWeight w r := by
    rw [Finset.mul_sum]
    exact Finset.sum_le_sum (fun i _ => mul_le_mul_of_nonneg_right (hweights i) (Nat.cast_nonneg _))
  have hcount' : (∑ i, (r.beta i : ℝ)) ≤ (w.theta : ℝ) * (H : ℝ) / wmin := by
    apply (le_div_iff₀ hmin).mpr
    rw [mul_comm]
    exact hcount.trans (rowWeight_lt w H r hr).le
  have hsave : rowWeight w r - (∑ i, (r.beta i : ℝ)) ≤ rowLogSaving q r := by
    calc
      _ = ∑ i, (r.beta i : ℝ) * ((w.w i : ℝ) - 1) := by
        simp [rowWeight, mul_sub, Finset.sum_sub_distrib, mul_comm]
      _ ≤ _ := Finset.sum_le_sum (fun i _ =>
        mul_le_mul_of_nonneg_left (hlog i) (Nat.cast_nonneg _))
  linarith

theorem fullRowMinor_size_pos {m : ℕ} {w : Weights m} {H : ℚ}
    {r : Fin m → ℚ} {T : Fin m → ℕ} (hK : 0 < w.K) (hH : 0 < H)
    (minor : FullRowMinor w H r T) : 0 < minor.size := by
  have hrow : AdmissibleRow w H (valueRow m 0) := by
    refine ⟨hK, ?_⟩
    simpa [valueRow] using hH
  obtain ⟨i, _⟩ := minor.all_rows (valueRow m 0) hrow
  exact Nat.zero_lt_of_lt i.isLt

def averageRowWeight {m : ℕ} {w : Weights m} {H : ℚ}
    {r : Fin m → ℚ} {T : Fin m → ℕ} (minor : FullRowMinor w H r T) : ℝ :=
  (∑ i, rowWeight w (minor.rows i)) / ((minor.size : ℝ) * (H : ℝ))

theorem averageRowWeight_bounds {m : ℕ} {w : Weights m} {H : ℚ}
    {r : Fin m → ℚ} {T : Fin m → ℕ} (hK : 0 < w.K) (hH : 0 < H)
    (minor : FullRowMinor w H r T) :
    0 ≤ averageRowWeight minor ∧ averageRowWeight minor < (w.theta : ℝ) := by
  have hsize := fullRowMinor_size_pos hK hH minor
  have hM : (0 : ℝ) < minor.size := by exact_mod_cast hsize
  have hH' : (0 : ℝ) < H := by exact_mod_cast hH
  constructor
  · apply div_nonneg _ (mul_pos hM hH').le
    apply Finset.sum_nonneg
    intro i _
    apply Finset.sum_nonneg
    intro k _
    exact mul_nonneg (by exact_mod_cast (w.w_pos k).le) (Nat.cast_nonneg _)
  · apply (div_lt_iff₀ (mul_pos hM hH')).mpr
    calc
      _ < ∑ _i : Fin minor.size, (w.theta : ℝ) * (H : ℝ) := by
        apply Finset.sum_lt_sum
        · intro i _; exact (rowWeight_lt w H _ (minor.row_valid i)).le
        · exact ⟨⟨0, hsize⟩, Finset.mem_univ _, rowWeight_lt w H _ (minor.row_valid _)⟩
      _ = _ := by simp; ring

def arithmeticError {m : ℕ} (w : Weights m) (F : ℚ) (wmin : ℝ) : ℝ :=
  lcmConstant * (F : ℝ) * m / (w.v0 : ℝ) +
    lcmConstant * ∑ i, 1 / (w.w i : ℝ) + (w.theta : ℝ) / wmin

/-- Variant of (3.5), using the explicit Mathlib constant log 4 + 4. -/
theorem fullRowMinor_normalized_arithmetic_bound {m : ℕ} {w : Weights m} {H F : ℚ}
    (p : Fin m → ℤ) (q : Fin m → ℕ) (hq : ∀ i, q i ≠ 0)
    (hK : 0 < w.K) (hH : 0 < H) (hF : 0 ≤ F)
    (hlog : ∀ i, Real.log (q i : ℝ) ≤ (w.w i : ℝ))
    (hlog' : ∀ i, (w.w i : ℝ) - 1 ≤ Real.log (q i : ℝ))
    (wmin : ℝ) (hmin : 0 < wmin) (hweights : ∀ i, wmin ≤ (w.w i : ℝ))
    (minor : FullRowMinor w H (rationalPoint p q) (truncationOrders w F)) :
    -(1 - averageRowWeight minor) - arithmeticError w F wmin ≤
      Real.log |(minor.matrix.det : ℝ)| / ((minor.size : ℝ) * (H : ℝ)) := by
  have hM : (0 : ℝ) < minor.size := by exact_mod_cast fullRowMinor_size_pos hK hH minor
  have hH' : (0 : ℝ) < H := by exact_mod_cast hH
  have hs : (∑ i, rowWeight w (minor.rows i)) -
      (minor.size : ℝ) * ((w.theta : ℝ) * (H : ℝ) / wmin) ≤
      ∑ i, rowLogSaving q (minor.rows i) := by
    calc
      _ = ∑ i, (rowWeight w (minor.rows i) - (w.theta : ℝ) * (H : ℝ) / wmin) := by
        simp [Finset.sum_sub_distrib]
      _ ≤ _ := Finset.sum_le_sum (fun i _ =>
        rowLogSaving_lower w H q hlog' wmin hmin hweights _ (minor.row_valid i))
  have hc : (∑ j, columnQCost q (minor.columns j)) ≤ (minor.size : ℝ) * (H : ℝ) := by
    calc
      _ ≤ ∑ j : Fin minor.size, (H : ℝ) := Finset.sum_le_sum
        (fun j _ => columnQCost_le_height w H q hlog _ (minor.column_valid j))
      _ = _ := by simp
  have hd := mul_le_mul_of_nonneg_left
    (truncation_denominatorBudget_le w H F hH.le hF) hM.le
  have hb := fullRowMinor_uniform_log_bound p q (truncationOrders w F) hq minor
  apply (le_div_iff₀ (mul_pos hM hH')).mpr
  dsimp [averageRowWeight, arithmeticError]
  rw [sub_mul, neg_mul, sub_mul, one_mul, div_mul_cancel₀ _ (mul_pos hM hH').ne']
  have halg : (minor.size : ℝ) * ((w.theta : ℝ) * (H : ℝ) / wmin) =
      ((w.theta : ℝ) / wmin) * ((minor.size : ℝ) * (H : ℝ)) := by ring
  rw [halg] at hs
  nlinarith only [hs, hc, hd, hb]

/-- The concrete ceil(log q_i) specialization needs no separate logarithmic weight assumptions. -/
theorem fullRowMinor_bound_of_ceilLogWeights {m : ℕ} {w : Weights m} {H F : ℚ}
    (p : Fin m → ℤ) (q : Fin m → ℕ) (hq : ∀ i, 2 ≤ q i)
    (hw : ∀ i, w.w i = ceilLogWeight (q i))
    (hK : 0 < w.K) (hH : 0 < H) (hF : 0 ≤ F)
    (wmin : ℝ) (hmin : 0 < wmin) (hweights : ∀ i, wmin ≤ (w.w i : ℝ))
    (minor : FullRowMinor w H (rationalPoint p q) (truncationOrders w F)) :
    -(1 - averageRowWeight minor) - arithmeticError w F wmin ≤
      Real.log |(minor.matrix.det : ℝ)| / ((minor.size : ℝ) * (H : ℝ)) := by
  apply fullRowMinor_normalized_arithmetic_bound p q (fun i => by have := hq i; omega)
    hK hH hF _ _ wmin hmin hweights minor
  · intro i; rw [hw i]; exact (ceilLogWeight_bounds (q i)).1
  · intro i; rw [hw i]; exact (ceilLogWeight_bounds (q i)).2

end
end LogTwo.Arithmetic
end Source0016

-- Source: LogTwo/ParameterAssembly.lean
section Source0017
-- Modified in this edition: unused plain lemmas removed; see reduction.json.
/-! Construct the actual weights used by the matrix and make the arithmetic
error small. Interpolation and the analytic upper bound are still separate goals. -/
namespace LogTwo

open Parameters Arithmetic Interpolation
noncomputable section

theorem ceilLogWeight_pos {q : ℕ} (hq : 2 ≤ q) : 0 < ceilLogWeight q := by
  have hlog : 0 < Real.log (q : ℝ) :=
    Real.log_pos (by exact_mod_cast (show 1 < q by omega))
  exact_mod_cast hlog.trans_le (ceilLogWeight_bounds q).1

def chosenWeights (n : ℕ) (hn : 1 ≤ n) (m : ℕ) (q : Fin m → ℕ)
    (hq : ∀ i, 2 ≤ q i) : Weights m where
  K := centerCount (c (delta n)) m
  w0 := horizontalWeight (b (delta n)) m
  v0 := verticalWeight (theta (delta n)) (b (delta n)) (c (delta n)) m
  w := fun i => ceilLogWeight (q i)
  theta := theta (delta n)
  w0_pos := horizontalWeight_pos
    ((shape n hn).theta_pos.trans ((shape n hn).theta_lt_a.trans (shape n hn).a_lt_b)) m
  v0_pos := verticalWeight_pos (shape n hn).theta_pos
    ((shape n hn).theta_pos.trans ((shape n hn).theta_lt_a.trans (shape n hn).a_lt_b))
    (shape n hn).one_lt_c.le m
  w_pos := fun i => ceilLogWeight_pos (hq i)
  theta_pos := (shape n hn).theta_pos
  theta_lt_one := (shape n hn).theta_lt_a.trans
    ((shape n hn).a_lt_b.trans (shape n hn).b_lt_one)

theorem arithmeticError_le_uniform {m : ℕ} (w : Weights m) (F : ℚ) (W : ℝ)
    (hW : 0 < W) (hw : ∀ i, W ≤ (w.w i : ℝ)) :
    arithmeticError w F W ≤ lcmConstant * (F : ℝ) * m / (w.v0 : ℝ) +
      (lcmConstant * m + (w.theta : ℝ)) / W := by
  have hs : (∑ i, 1 / (w.w i : ℝ)) ≤ (m : ℝ) / W := by
    calc
      _ ≤ ∑ _i : Fin m, (1 : ℝ) / W := Finset.sum_le_sum
        (fun i _ => one_div_le_one_div_of_le hW (hw i))
      _ = _ := by simp [div_eq_mul_inv]
  have hh := mul_le_mul_of_nonneg_left hs lcmConstant_pos.le
  unfold arithmeticError
  calc
    _ ≤ lcmConstant * (F : ℝ) * m / (w.v0 : ℝ) +
        lcmConstant * ((m : ℝ) / W) + (w.theta : ℝ) / W := by linarith
    _ = _ := by ring

end
end LogTwo
end Source0017

-- Source: OAI/NumberTheory/PiExponent/Polynomials/PolynomialFrameDegree.lean
section Source0018
/-
Modification notice for the LogTwo project.
Derived from openai/math (Apache-2.0), revision adc7f1241b42e322a6451854ab7e4b4c146bf78a.
Original source: lean/OAI/NumberTheory/PiExponent/Polynomials/PolynomialFrameDegree.lean
Changes: Convert module/import declarations to the Lean 4.34 public module format.
See ../THIRD_PARTY_NOTICES.txt for provenance and the recorded changes.
-/

namespace OAI

namespace PiExponentApprox

noncomputable section

open MvPolynomial

def monomialWeight {m : ℕ} (w : Fin (m + 1) → ℝ)
    (d : Fin (m + 1) →₀ ℕ) : ℝ :=
  ∑ i, (d i : ℝ) * w i

def HasWeightedDegreeLE {m : ℕ} (w : Fin (m + 1) → ℝ) (N : ℝ)
    (p : MvPolynomial (Fin (m + 1)) ℂ) : Prop :=
  ∀ d ∈ p.support, monomialWeight w d ≤ N

theorem monomialWeight_add {m : ℕ} (w : Fin (m + 1) → ℝ)
    (d e : Fin (m + 1) →₀ ℕ) :
    monomialWeight w (d + e) = monomialWeight w d + monomialWeight w e := by
  simp [monomialWeight, Finsupp.add_apply, Nat.cast_add, add_mul, Finset.sum_add_distrib]

theorem monomialWeight_single {m : ℕ} (w : Fin (m + 1) → ℝ)
    (i : Fin (m + 1)) : monomialWeight w (Finsupp.single i 1) = w i := by
  classical
  simp [monomialWeight, Finsupp.single_apply]

theorem HasWeightedDegreeLE.zero {m : ℕ} (w : Fin (m + 1) → ℝ) (N : ℝ) :
    HasWeightedDegreeLE w N (0 : MvPolynomial (Fin (m + 1)) ℂ) := by
  simp [HasWeightedDegreeLE]

theorem HasWeightedDegreeLE.mono {m : ℕ} {w : Fin (m + 1) → ℝ} {N M : ℝ}
    {p : MvPolynomial (Fin (m + 1)) ℂ} (hp : HasWeightedDegreeLE w N p)
    (hNM : N ≤ M) : HasWeightedDegreeLE w M p :=
  fun d hd => (hp d hd).trans hNM

theorem HasWeightedDegreeLE.add {m : ℕ} {w : Fin (m + 1) → ℝ} {N : ℝ}
    {p q : MvPolynomial (Fin (m + 1)) ℂ}
    (hp : HasWeightedDegreeLE w N p) (hq : HasWeightedDegreeLE w N q) :
    HasWeightedDegreeLE w N (p + q) := by
  intro d hd
  rcases Finset.mem_union.mp (MvPolynomial.support_add hd) with hd | hd
  · exact hp d hd
  · exact hq d hd

theorem HasWeightedDegreeLE.sum {m : ℕ} {α : Type*} {w : Fin (m + 1) → ℝ}
    {N : ℝ} (s : Finset α) (p : α → MvPolynomial (Fin (m + 1)) ℂ)
    (hp : ∀ a ∈ s, HasWeightedDegreeLE w N (p a)) :
    HasWeightedDegreeLE w N (∑ a ∈ s, p a) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using HasWeightedDegreeLE.zero w N
  | @insert a s ha ih =>
      rw [Finset.sum_insert ha]
      exact (hp a (Finset.mem_insert_self a s)).add
        (ih (fun b hb => hp b (Finset.mem_insert_of_mem hb)))

theorem pderiv_support_shift {m : ℕ} (i : Fin (m + 1))
    (p : MvPolynomial (Fin (m + 1)) ℂ) (d : Fin (m + 1) →₀ ℕ)
    (hd : d ∈ (MvPolynomial.pderiv i p).support) : d + Finsupp.single i 1 ∈ p.support := by
  apply MvPolynomial.mem_support_iff.mpr
  intro hz
  have hcoeff := MvPolynomial.mem_support_iff.mp hd
  apply hcoeff
  rw [MvPolynomial.coeff_pderiv, hz, zero_mul]

theorem HasWeightedDegreeLE.pderiv {m : ℕ} {w : Fin (m + 1) → ℝ} {N : ℝ}
    {p : MvPolynomial (Fin (m + 1)) ℂ} (hp : HasWeightedDegreeLE w N p)
    (i : Fin (m + 1)) : HasWeightedDegreeLE w (N - w i) (MvPolynomial.pderiv i p) := by
  intro d hd
  apply (le_sub_iff_add_le).mpr
  have h := hp (d + Finsupp.single i 1) (pderiv_support_shift i p d hd)
  simpa only [monomialWeight_add, monomialWeight_single] using h

theorem HasWeightedDegreeLE.X_mul {m : ℕ} {w : Fin (m + 1) → ℝ} {N : ℝ}
    {p : MvPolynomial (Fin (m + 1)) ℂ} (hp : HasWeightedDegreeLE w N p)
    (i : Fin (m + 1)) : HasWeightedDegreeLE w (N + w i) (MvPolynomial.X i * p) := by
  intro d hd
  have hsupp := MvPolynomial.support_X_mul i p
  rw [hsupp] at hd
  obtain ⟨e, he, hed⟩ := Finset.mem_map.mp hd
  have heq : Finsupp.single i 1 + e = d := hed
  rw [← heq, monomialWeight_add, monomialWeight_single, add_comm (w i)]
  exact add_le_add (hp e he) (le_refl (w i))

theorem HasWeightedDegreeLE.X_mul_pderiv {m : ℕ} {w : Fin (m + 1) → ℝ} {N : ℝ}
    {p : MvPolynomial (Fin (m + 1)) ℂ} (hp : HasWeightedDegreeLE w N p)
    (i : Fin (m + 1)) : HasWeightedDegreeLE w N (MvPolynomial.X i * MvPolynomial.pderiv i p) := by
  simpa only [sub_add_cancel] using (hp.pderiv i).X_mul i

theorem HasWeightedDegreeLE.pderiv_preserves {m : ℕ} {w : Fin (m + 1) → ℝ}
    {N : ℝ} {p : MvPolynomial (Fin (m + 1)) ℂ}
    (hp : HasWeightedDegreeLE w N p) (i : Fin (m + 1)) (hi : 0 ≤ w i) :
    HasWeightedDegreeLE w N (MvPolynomial.pderiv i p) :=
  (hp.pderiv i).mono (sub_le_self N hi)

end

end PiExponentApprox

end OAI
end Source0018

-- Source: OAI/NumberTheory/PiExponent/Polynomials/PolynomialFrame.lean
section Source0019
-- Modified in this edition: unused plain lemmas removed; see reduction.json.
/-
Modification notice for the LogTwo project.
Derived from openai/math (Apache-2.0), revision adc7f1241b42e322a6451854ab7e4b4c146bf78a.
Original source: lean/OAI/NumberTheory/PiExponent/Polynomials/PolynomialFrame.lean
Changes: Convert module/import declarations to the Lean 4.34 public module format.
See ../THIRD_PARTY_NOTICES.txt for provenance and the recorded changes.
-/

namespace OAI

namespace PiExponentApprox

noncomputable section

abbrev FramePolynomial (m : ℕ) := MvPolynomial (Fin (m + 1)) ℂ

def logarithmicDerivation (m : ℕ) :
    Derivation ℂ (FramePolynomial m) (FramePolynomial m) :=
  (MvPolynomial.X (0 : Fin (m + 1)) : FramePolynomial m) •
    MvPolynomial.pderiv (R := ℂ) (0 : Fin (m + 1)) +
    ∑ i : Fin m, MvPolynomial.pderiv (R := ℂ) i.succ

def polynomialFrame (m : ℕ) (i : Fin (m + 1)) :
    Derivation ℂ (FramePolynomial m) (FramePolynomial m) :=
  if i = 0 then logarithmicDerivation m else MvPolynomial.pderiv i

theorem derivation_finset_sum_apply {α : Type*} (m : ℕ) (s : Finset α)
    (D : α → Derivation ℂ (FramePolynomial m) (FramePolynomial m))
    (p : FramePolynomial m) : (∑ a ∈ s, D a) p = ∑ a ∈ s, D a p := by
  classical
  induction s using Finset.induction_on with
  | empty => simp only [Finset.sum_empty, Derivation.zero_apply]
  | @insert a s ha ih =>
      rw [Finset.sum_insert ha, Finset.sum_insert ha, Derivation.add_apply, ih]

@[simp] theorem logarithmicDerivation_apply (m : ℕ) (p : FramePolynomial m) :
    logarithmicDerivation m p =
      MvPolynomial.X (0 : Fin (m + 1)) * MvPolynomial.pderiv 0 p +
        ∑ i : Fin m, MvPolynomial.pderiv i.succ p := by
  simp only [logarithmicDerivation, Derivation.add_apply, Derivation.smul_apply,
    derivation_finset_sum_apply, smul_eq_mul]

@[simp] theorem polynomialFrame_zero (m : ℕ) :
    polynomialFrame m 0 = logarithmicDerivation m := by
  simp only [polynomialFrame, ite_true]

@[simp] theorem polynomialFrame_pos (m : ℕ) (i : Fin (m + 1)) (hi : i ≠ 0) :
    polynomialFrame m i = MvPolynomial.pderiv i := by
  simp only [polynomialFrame, ite_eq_right hi]

@[simp] theorem polynomialFrame_add (m : ℕ) (i : Fin (m + 1))
    (p q : FramePolynomial m) :
    polynomialFrame m i (p + q) = polynomialFrame m i p + polynomialFrame m i q :=
  map_add _ _ _

@[simp] theorem polynomialFrame_C (m : ℕ) (i : Fin (m + 1)) (a : ℂ) :
    polynomialFrame m i (MvPolynomial.C a) = 0 := by
  rw [MvPolynomial.C_eq_algebraMap]
  exact Derivation.map_algebraMap _ a

theorem HasWeightedDegreeLE.logarithmicDerivation {m : ℕ}
    {w : Fin (m + 1) → ℝ} {N : ℝ} {p : FramePolynomial m}
    (hp : HasWeightedDegreeLE w N p) (hw : ∀ i, 0 ≤ w i) :
    HasWeightedDegreeLE w N (PiExponentApprox.logarithmicDerivation m p) := by
  rw [logarithmicDerivation_apply]
  apply (hp.X_mul_pderiv 0).add
  exact HasWeightedDegreeLE.sum Finset.univ _
    (fun i _ => hp.pderiv_preserves i.succ (hw i.succ))

theorem HasWeightedDegreeLE.polynomialFrame {m : ℕ}
    {w : Fin (m + 1) → ℝ} {N : ℝ} {p : FramePolynomial m}
    (hp : HasWeightedDegreeLE w N p) (hw : ∀ i, 0 ≤ w i) (i : Fin (m + 1)) :
    HasWeightedDegreeLE w N (PiExponentApprox.polynomialFrame m i p) := by
  by_cases hi : i = 0
  · subst i
    rw [polynomialFrame_zero]
    exact hp.logarithmicDerivation hw
  · rw [polynomialFrame_pos m i hi]
    exact hp.pderiv_preserves i (hw i)

def polynomialFrameWord (m : ℕ) (word : List (Fin (m + 1)))
    (p : FramePolynomial m) : FramePolynomial m :=
  word.foldr (fun i q => polynomialFrame m i q) p

@[simp] theorem polynomialFrameWord_nil (m : ℕ) (p : FramePolynomial m) :
    polynomialFrameWord m [] p = p := rfl

@[simp] theorem polynomialFrameWord_cons (m : ℕ) (i : Fin (m + 1))
    (word : List (Fin (m + 1))) (p : FramePolynomial m) :
    polynomialFrameWord m (i :: word) p =
      polynomialFrame m i (polynomialFrameWord m word p) := rfl

theorem HasWeightedDegreeLE.polynomialFrameWord {m : ℕ}
    {w : Fin (m + 1) → ℝ} {N : ℝ} {p : FramePolynomial m}
    (hp : HasWeightedDegreeLE w N p) (hw : ∀ i, 0 ≤ w i)
    (word : List (Fin (m + 1))) :
    HasWeightedDegreeLE w N (PiExponentApprox.polynomialFrameWord m word p) := by
  induction word with
  | nil => exact hp
  | cons i word ih => exact ih.polynomialFrame hw i

end
end PiExponentApprox

end OAI
end Source0019

-- Source: LogTwo/Geometry/YScaling.lean
section Source0020
-- Modified in this edition: unused plain lemmas removed; see reduction.json.
/-! Polynomial and curve-coordinate normalization, independent of the local curve theory. -/
namespace LogTwo.Geometry
open OAI PiExponentApprox MvPolynomial
noncomputable section

def scaleY {m : ℕ} (y : ℂ) : FramePolynomial m →ₐ[ℂ] FramePolynomial m :=
  MvPolynomial.aeval (Fin.cases (C y * X 0) (fun i => X i.succ))

@[simp] theorem scaleY_C {m : ℕ} (y a : ℂ) : scaleY (m := m) y (C a) = C a := by
  simp [scaleY]

@[simp] theorem scaleY_X_zero {m : ℕ} (y : ℂ) :
    scaleY y (X (0 : Fin (m+1))) = C y * X 0 := by simp [scaleY]

@[simp] theorem scaleY_X_succ {m : ℕ} (y : ℂ) (i : Fin m) :
    scaleY y (X i.succ) = X i.succ := by simp [scaleY]

theorem scaleY_polynomialFrame_X {m : ℕ} (y : ℂ) (i j : Fin (m+1)) :
    scaleY y (polynomialFrame m i (X j)) = polynomialFrame m i (scaleY y (X j)) := by
  classical
  cases i using Fin.cases with
  | zero =>
    cases j using Fin.cases with
    | zero =>
      simp [polynomialFrame_zero, logarithmicDerivation_apply, mul_comm]
    | succ j =>
      simp [polynomialFrame_zero, logarithmicDerivation_apply, Pi.single_apply]
  | succ i =>
    rw [polynomialFrame_pos m i.succ (Fin.succ_ne_zero i)]
    cases j using Fin.cases with
    | zero => simp
    | succ j =>
      by_cases hij : i = j
      · subst j; simp
      · simp [Ne.symm hij]

/-- Constant scaling of Y commutes with Y∂Y + Σ∂Xi and the ordinary Xi derivatives. -/
theorem scaleY_polynomialFrame {m : ℕ} (y : ℂ) (i : Fin (m+1))
    (F : FramePolynomial m) :
    scaleY y (polynomialFrame m i F) = polynomialFrame m i (scaleY y F) :=
  by
    induction F using MvPolynomial.induction_on with
    | C a => simp [polynomialFrame]
    | add F G hF hG => simp only [map_add, hF, hG]
    | mul_X F j hF =>
      simp only [Derivation.leibniz, smul_eq_mul, map_add, map_mul, hF,
        scaleY_polynomialFrame_X y i j]

theorem scaleY_polynomialFrameWord {m : ℕ} (y : ℂ) (word : List (Fin (m+1)))
    (F : FramePolynomial m) :
    scaleY y (polynomialFrameWord m word F) = polynomialFrameWord m word (scaleY y F) := by
  induction word with
  | nil => rfl
  | cons i word ih => rw [polynomialFrameWord_cons, scaleY_polynomialFrame, ih]; rfl

variable {E : Type*} [Field E] [Algebra ℂ E]

def normalizeY {m : ℕ} (y : ℂ) (z : Fin (m+1) → E) : Fin (m+1) → E :=
  Fin.cases (z 0 / algebraMap ℂ E y) (fun i => z i.succ)

/-- The polynomial scaling and the point normalization cancel exactly. -/
theorem aeval_normalizeY_scaleY {m : ℕ} (y : ℂ) (hy : y ≠ 0)
    (z : Fin (m+1) → E) (F : FramePolynomial m) :
    MvPolynomial.aeval (normalizeY y z) (scaleY y F) = MvPolynomial.aeval z F := by
  have hy' : algebraMap ℂ E y ≠ 0 := (map_ne_zero_iff _ (algebraMap ℂ E).injective).mpr hy
  have he : (MvPolynomial.aeval (normalizeY y z)).comp (scaleY y) = MvPolynomial.aeval z := by
    apply MvPolynomial.algHom_ext
    intro i
    cases i using Fin.cases with
    | zero => simp [normalizeY, hy', mul_div_cancel₀]
    | succ i => simp [normalizeY]
  exact DFunLike.congr_fun he F

theorem aeval_normalizeY_scaled_word {m : ℕ} (y : ℂ) (hy : y ≠ 0)
    (z : Fin (m+1) → E) (word : List (Fin (m+1))) (F : FramePolynomial m) :
    MvPolynomial.aeval (normalizeY y z) (polynomialFrameWord m word (scaleY y F)) =
      MvPolynomial.aeval z (polynomialFrameWord m word F) := by
  rw [← scaleY_polynomialFrameWord, aeval_normalizeY_scaleY y hy]

end
end LogTwo.Geometry
end Source0020

-- Source: OAI/NumberTheory/PiExponent/Jets/JetGeometry.lean
section Source0021
-- Modified in this edition: unused plain lemmas removed; see reduction.json.
/-
Modification notice for the LogTwo project.
Derived from openai/math (Apache-2.0), revision adc7f1241b42e322a6451854ab7e4b4c146bf78a.
Original source: lean/OAI/NumberTheory/PiExponent/Jets/JetGeometry.lean
Changes: Convert module/import declarations to the Lean 4.34 public module format.
See ../THIRD_PARTY_NOTICES.txt for provenance and the recorded changes.
-/

namespace OAI

namespace PiExponent.JetGeometry

noncomputable section

open MvPowerSeries

variable {σ R : Type*} [CommRing R]

def weightedIdeal (w : σ → ℕ) (N : ℕ) : Ideal (MvPowerSeries σ R) where
  carrier := {f | (N : ℕ∞) ≤ f.weightedOrder w}
  zero_mem' := by simp
  add_mem' hf hg := (le_min hf hg).trans (min_weightedOrder_le_add w)
  smul_mem' a f hf := by
    change (N : ℕ∞) ≤ weightedOrder w (a * f)
    exact hf.trans (le_add_self.trans (le_weightedOrder_mul w))

@[simp] theorem mem_weightedIdeal (w : σ → ℕ) (N : ℕ)
    (f : MvPowerSeries σ R) :
    f ∈ weightedIdeal w N ↔ (N : ℕ∞) ≤ f.weightedOrder w := Iff.rfl

theorem mem_weightedIdeal_iff (w : σ → ℕ) (N : ℕ)
    (f : MvPowerSeries σ R) :
    f ∈ weightedIdeal w N ↔ ∀ d, Finsupp.weight w d < N → coeff d f = 0 := by
  constructor
  · intro hf d hd
    have hd' : (Finsupp.weight w d : ℕ∞) < (N : ℕ∞) := by exact_mod_cast hd
    exact coeff_eq_zero_of_lt_weightedOrder w (hd'.trans_le hf)
  · intro hf
    exact nat_le_weightedOrder w hf

theorem weightedIdeal_mul_le (w : σ → ℕ) (M N : ℕ) :
    (weightedIdeal w M : Ideal (MvPowerSeries σ R)) * weightedIdeal w N ≤
      weightedIdeal w (M + N) := by
  apply Ideal.mul_le.mpr
  intro f hf g hg
  change ((M + N : ℕ) : ℕ∞) ≤ weightedOrder w (f * g)
  rw [Nat.cast_add]
  exact (add_le_add hf hg).trans (le_weightedOrder_mul w)

theorem ideal_pow_le_weightedIdeal (w : σ → ℕ) (I : Ideal (MvPowerSeries σ R))
    (R₀ : ℕ) (hI : I ≤ weightedIdeal w R₀) (n : ℕ) :
    I ^ n ≤ weightedIdeal w (n * R₀) := by
  induction n with
  | zero =>
      intro f hf
      change ((0 * R₀ : ℕ) : ℕ∞) ≤ weightedOrder w f
      simp
  | succ n ih =>
      rw [pow_succ, Nat.succ_mul]
      apply Ideal.mul_le.mpr
      intro f hf g hg
      exact (Ideal.mul_le.mp (weightedIdeal_mul_le w (n * R₀) R₀)) f (ih hf) g (hI hg)

def coordinatePowerIdeal (e : σ → ℕ) : Ideal (MvPowerSeries σ R) :=
  Ideal.span (Set.range (fun i => (X i : MvPowerSeries σ R) ^ e i))

def CoefficientPacket (w : σ → ℕ) (N : ℕ) :=
  {d : σ →₀ ℕ // Finsupp.weight w d < N} → R

def coefficientPacket (w : σ → ℕ) (N : ℕ) (f : MvPowerSeries σ R) :
    CoefficientPacket (R := R) w N := fun d => coeff d.val f

theorem rational_weight_nonneg (v : σ → ℚ) (hv : ∀ i, 0 ≤ v i)
    (d : σ →₀ ℕ) : 0 ≤ Finsupp.weight v d := by
  rw [Finsupp.weight_apply, Finsupp.sum]
  exact Finset.sum_nonneg (fun i _ => nsmul_nonneg (hv i) (d i))

def rationalWeightedIdeal (v : σ → ℚ) (hv : ∀ i, 0 ≤ v i) (H : ℚ) :
    Ideal (MvPowerSeries σ R) where
  carrier := {f | ∀ d, Finsupp.weight v d < H → coeff d f = 0}
  zero_mem' := by simp
  add_mem' hf hg := by
    intro d hd
    rw [map_add, hf d hd, hg d hd, add_zero]
  smul_mem' a f hf := by
    classical
    intro d hd
    change coeff d (a * f) = 0
    rw [coeff_mul]
    apply Finset.sum_eq_zero
    intro ij hij
    have he : ij.1 + ij.2 = d := Finset.HasAntidiagonal.mem_antidiagonal.mp hij
    have hw : Finsupp.weight v ij.2 ≤ Finsupp.weight v d := by
      rw [← he, map_add]
      exact le_add_of_nonneg_left (rational_weight_nonneg v hv ij.1)
    rw [hf ij.2 (hw.trans_lt hd), mul_zero]

@[simp] theorem mem_rationalWeightedIdeal (v : σ → ℚ) (hv : ∀ i, 0 ≤ v i)
    (H : ℚ) (f : MvPowerSeries σ R) :
    f ∈ rationalWeightedIdeal v hv H ↔
      ∀ d, Finsupp.weight v d < H → coeff d f = 0 := Iff.rfl

theorem rationalWeightedIdeal_mul_le (v : σ → ℚ) (hv : ∀ i, 0 ≤ v i) (H K : ℚ) :
    (rationalWeightedIdeal v hv H : Ideal (MvPowerSeries σ R)) *
      rationalWeightedIdeal v hv K ≤ rationalWeightedIdeal v hv (H + K) := by
  classical
  apply Ideal.mul_le.mpr
  intro f hf g hg d hd
  rw [coeff_mul]
  apply Finset.sum_eq_zero
  intro ij hij
  have he : ij.1 + ij.2 = d := Finset.HasAntidiagonal.mem_antidiagonal.mp hij
  by_cases hfirst : Finsupp.weight v ij.1 < H
  · rw [hf ij.1 hfirst, zero_mul]
  · have hsecond : Finsupp.weight v ij.2 < K := by
      apply lt_of_not_ge
      intro hsecond
      have hsum := add_le_add (le_of_not_gt hfirst) hsecond
      rw [← map_add, he] at hsum
      exact (not_le_of_gt hd) hsum
    rw [hg ij.2 hsecond, mul_zero]

theorem ideal_pow_le_rationalWeightedIdeal (v : σ → ℚ) (hv : ∀ i, 0 ≤ v i)
    (I : Ideal (MvPowerSeries σ R)) (H : ℚ)
    (hI : I ≤ rationalWeightedIdeal v hv H) (n : ℕ) :
    I ^ n ≤ rationalWeightedIdeal v hv (n * H) := by
  induction n with
  | zero =>
      intro f hf d hd
      have hzero := rational_weight_nonneg v hv d
      simp only [Nat.cast_zero, zero_mul] at hd
      exact False.elim ((not_lt_of_ge hzero) hd)
  | succ n ih =>
      rw [pow_succ, Nat.cast_add, Nat.cast_one, add_mul, one_mul]
      apply Ideal.mul_le.mpr
      intro f hf g hg
      exact (Ideal.mul_le.mp (rationalWeightedIdeal_mul_le v hv (n * H) H))
        f (ih hf) g (hI hg)

theorem coordinatePowerIdeal_pow_le_rational (v : σ → ℚ) (hv : ∀ i, 0 ≤ v i)
    (e : σ → ℕ) (H : ℚ) (he : ∀ i, H ≤ (e i : ℚ) * v i) (n : ℕ) :
    (coordinatePowerIdeal e : Ideal (MvPowerSeries σ R)) ^ n ≤
      rationalWeightedIdeal v hv (n * H) := by
  classical
  apply ideal_pow_le_rationalWeightedIdeal v hv _ H _ n
  apply Ideal.span_le.mpr
  rintro _ ⟨i, rfl⟩ d hd
  rw [coeff_X_pow]
  split_ifs with h
  · subst d
    rw [Finsupp.weight_single, nsmul_eq_mul] at hd
    exact False.elim ((not_lt_of_ge (he i)) hd)
  · rfl

def RationalCoefficientPacket (v : σ → ℚ) (H : ℚ) :=
  {d : σ →₀ ℕ // Finsupp.weight v d < H} → R

def rationalCoefficientPacket (v : σ → ℚ) (H : ℚ) (f : MvPowerSeries σ R) :
    RationalCoefficientPacket (R := R) v H := fun d => coeff d.val f

end

end PiExponent.JetGeometry

end OAI
end Source0021

-- Source: OAI/NumberTheory/PiExponent/Jets/FormalJetDerivatives.lean
section Source0022
/-
Modification notice for the LogTwo project.
Derived from openai/math (Apache-2.0), revision adc7f1241b42e322a6451854ab7e4b4c146bf78a.
Original source: lean/OAI/NumberTheory/PiExponent/Jets/FormalJetDerivatives.lean
Changes: Convert module/import declarations to the Lean 4.34 public module format.
See ../THIRD_PARTY_NOTICES.txt for provenance and the recorded changes.
-/

namespace OAI

noncomputable section
namespace PiExponent.FormalJetDerivatives
open MvPowerSeries
open PiExponent.JetGeometry

variable {σ R : Type*} [CommRing R]

theorem pderiv_mem_rationalWeightedIdeal (v : σ → ℚ) (hv : ∀ i, 0 ≤ v i)
    (H : ℚ) (f : MvPowerSeries σ R)
    (hf : f ∈ rationalWeightedIdeal v hv H) (i : σ) :
    pderiv i f ∈ rationalWeightedIdeal v hv (H - v i) := by
  intro d hd
  rw [coeff_pderiv, hf, zero_mul]
  rw [map_add, Finsupp.weight_single, one_nsmul]
  linarith

theorem mul_pderiv_mem_rationalWeightedIdeal (v : σ → ℚ) (hv : ∀ i, 0 ≤ v i)
    (H : ℚ) (f g : MvPowerSeries σ R)
    (hf : f ∈ rationalWeightedIdeal v hv H) (i : σ) :
    g * pderiv i f ∈ rationalWeightedIdeal v hv (H - v i) :=
  (rationalWeightedIdeal v hv (H - v i)).mul_mem_left g
    (pderiv_mem_rationalWeightedIdeal v hv H f hf i)

def jetFrame (m : ℕ) (i : Fin (m + 1)) :
    Derivation R (MvPowerSeries (Fin (m + 1)) R) (MvPowerSeries (Fin (m + 1)) R) :=
  if i = 0 then (1 + X (0 : Fin (m + 1)) : MvPowerSeries (Fin (m+1)) R) • pderiv 0 else pderiv i

@[simp] theorem jetFrame_zero (m : ℕ) (f : MvPowerSeries (Fin (m + 1)) R) :
    jetFrame m 0 f = (1 + X 0) * pderiv 0 f := by
  simp [jetFrame, Derivation.smul_apply, smul_eq_mul]

@[simp] theorem jetFrame_pos (m : ℕ) (i : Fin (m + 1)) (hi : i ≠ 0)
    (f : MvPowerSeries (Fin (m + 1)) R) : jetFrame m i f = pderiv i f := by
  simp [jetFrame, hi]

theorem jetFrame_mem_rationalWeightedIdeal {m : ℕ}
    (v : Fin (m + 1) → ℚ) (hv : ∀ i, 0 ≤ v i)
    (H : ℚ) (f : MvPowerSeries (Fin (m + 1)) R)
    (hf : f ∈ rationalWeightedIdeal v hv H) (i : Fin (m + 1)) :
    jetFrame m i f ∈ rationalWeightedIdeal v hv (H - v i) := by
  by_cases hi : i = 0
  · subst i
    rw [jetFrame_zero]
    exact mul_pderiv_mem_rationalWeightedIdeal v hv H f (1 + X 0) hf 0
  · rw [jetFrame_pos m i hi]
    exact pderiv_mem_rationalWeightedIdeal v hv H f hf i

def jetFrameWord (m : ℕ) (word : List (Fin (m + 1)))
    (f : MvPowerSeries (Fin (m + 1)) R) : MvPowerSeries (Fin (m + 1)) R :=
  word.foldr (fun i g => jetFrame m i g) f

theorem jetFrameWord_mem_rationalWeightedIdeal {m : ℕ}
    (v : Fin (m + 1) → ℚ) (hv : ∀ i, 0 ≤ v i)
    (H : ℚ) (f : MvPowerSeries (Fin (m + 1)) R)
    (hf : f ∈ rationalWeightedIdeal v hv H) (word : List (Fin (m + 1))) :
    jetFrameWord m word f ∈ rationalWeightedIdeal v hv (H - (word.map v).sum) := by
  induction word with
  | nil => simpa [jetFrameWord] using hf
  | cons i word ih =>
    have hh := jetFrame_mem_rationalWeightedIdeal v hv
      (H - (word.map v).sum) (jetFrameWord m word f) ih i
    simpa only [jetFrameWord, List.foldr_cons, List.map_cons, List.sum_cons,
      sub_sub, add_comm] using hh

end PiExponent.FormalJetDerivatives

end

end OAI
end Source0022

-- Source: OAI/NumberTheory/PiExponent/Jets/FormalLogJet.lean
section Source0023
/-
Modification notice for the LogTwo project.
Derived from openai/math (Apache-2.0), revision adc7f1241b42e322a6451854ab7e4b4c146bf78a.
Original source: lean/OAI/NumberTheory/PiExponent/Jets/FormalLogJet.lean
Changes: Convert module/import declarations to the Lean 4.34 public module format.
See ../THIRD_PARTY_NOTICES.txt for provenance and the recorded changes.
-/

namespace OAI

noncomputable section
namespace PiExponent.FormalLogJet
open MvPowerSeries
open PiExponent.FormalJetDerivatives

variable {R : Type*} [CommRing R]

def liftSeries (m : ℕ) : PowerSeries R →+* MvPowerSeries (Fin (m + 1)) R :=
  (finSuccEquiv R m).symm.toRingHom.comp (PowerSeries.map MvPowerSeries.C)

@[simp] theorem coeff_liftSeries (m : ℕ) (f : PowerSeries R)
    (d : Fin (m + 1) →₀ ℕ) :
    coeff d (liftSeries m f) = if d.tail = 0 then PowerSeries.coeff (d 0) f else 0 := by
  have h := coeff_coeff_finSuccEquiv (liftSeries m f) (k := d 0) (x := d.tail)
  rw [Finsupp.cons_tail] at h
  rw [← h]
  simp [liftSeries, PowerSeries.coeff_map, coeff_C]

@[simp] theorem liftSeries_X (m : ℕ) : liftSeries (R := R) m PowerSeries.X = X 0 := by
  apply (finSuccEquiv R m).injective
  simp [liftSeries]

@[simp] theorem liftSeries_C (m : ℕ) (r : R) :
    liftSeries m (PowerSeries.C r) = C r := by
  apply (finSuccEquiv R m).injective
  simp [liftSeries]

theorem pderiv_zero_liftSeries (m : ℕ) (f : PowerSeries R) :
    pderiv 0 (liftSeries m f) = liftSeries m (PowerSeries.derivative f) := by
  ext d
  rw [coeff_pderiv, coeff_liftSeries, coeff_liftSeries, PowerSeries.coeff_derivative]
  have ht : (d + Finsupp.single (0 : Fin (m+1)) 1).tail = d.tail := by
    ext i
    simp [Finsupp.tail_apply]
  simp only [ht, Finsupp.add_apply, Finsupp.single_eq_same]
  split_ifs <;> simp_all

theorem pderiv_succ_liftSeries (m : ℕ) (i : Fin m) (f : PowerSeries R) :
    pderiv i.succ (liftSeries m f) = 0 := by
  ext d
  rw [coeff_pderiv, coeff_liftSeries, coeff_zero]
  have ht : (d + Finsupp.single i.succ 1).tail ≠ 0 := by
    intro h
    have hi := DFunLike.congr_fun h i
    simp [Finsupp.tail_apply] at hi
  simp [ht]

def formalLog (m : ℕ) : MvPowerSeries (Fin (m+1)) ℂ :=
  liftSeries m (PowerSeries.log ℂ)

@[simp] theorem pderiv_succ_formalLog (m : ℕ) (i : Fin m) :
    pderiv i.succ (formalLog m) = 0 := pderiv_succ_liftSeries m i _

theorem one_add_X_mul_pderiv_formalLog (m : ℕ) :
    (1 + X 0) * pderiv 0 (formalLog m) = 1 := by
  have h := congrArg (liftSeries m) (PowerSeries.derivative_log_mul_one_add_X (A := ℂ))
  rw [map_mul, map_add, map_one, liftSeries_X] at h
  rw [formalLog, pderiv_zero_liftSeries, mul_comm]
  exact h

def formalJet {m : ℕ} (c : Fin m → ℂ) :
    PiExponentApprox.FramePolynomial m →ₐ[ℂ] MvPowerSeries (Fin (m+1)) ℂ :=
  MvPolynomial.aeval (Fin.cases (1 + X 0)
    (fun i => C (c i) + X i.succ + formalLog m))

@[simp] theorem formalJet_Y {m : ℕ} (c : Fin m → ℂ) :
    formalJet c (MvPolynomial.X (0 : Fin (m+1))) = 1 + X 0 := by
  simp [formalJet]

@[simp] theorem formalJet_X {m : ℕ} (c : Fin m → ℂ) (i : Fin m) :
    formalJet c (MvPolynomial.X i.succ) = C (c i) + X i.succ + formalLog m := by
  simp [formalJet]

theorem derivation_map_of_X {σ S : Type*} [CommRing S] [Algebra R S]
    (φ : MvPolynomial σ R →ₐ[R] S)
    (D : Derivation R (MvPolynomial σ R) (MvPolynomial σ R))
    (δ : Derivation R S S)
    (hX : ∀ i, φ (D (MvPolynomial.X i)) = δ (φ (MvPolynomial.X i)))
    (p : MvPolynomial σ R) : φ (D p) = δ (φ p) := by
  induction p using MvPolynomial.induction_on with
  | C a => simp
  | add p q hp hq => simp only [map_add, hp, hq]
  | mul_X p i hp =>
    simp only [Derivation.leibniz, smul_eq_mul, map_add, map_mul, hp, hX]

theorem formalJet_frame_X {m : ℕ} (c : Fin m → ℂ) (i j : Fin (m+1)) :
    formalJet c (PiExponentApprox.polynomialFrame m i (MvPolynomial.X j)) =
      jetFrame m i (formalJet c (MvPolynomial.X j)) := by
  classical
  cases i using Fin.cases with
  | zero =>
    cases j using Fin.cases with
    | zero =>
      simp [PiExponentApprox.polynomialFrame_zero,
        PiExponentApprox.logarithmicDerivation_apply, MvPolynomial.pderiv_X]
    | succ j =>
      simp [PiExponentApprox.polynomialFrame_zero,
        PiExponentApprox.logarithmicDerivation_apply, MvPolynomial.pderiv_X,
        Pi.single_apply, MvPowerSeries.pderiv_X_of_ne,
        one_add_X_mul_pderiv_formalLog]
  | succ i =>
    rw [PiExponentApprox.polynomialFrame_pos m i.succ (Fin.succ_ne_zero i),
      jetFrame_pos m i.succ (Fin.succ_ne_zero i)]
    cases j using Fin.cases with
    | zero => simp [MvPowerSeries.pderiv_X_of_ne (Ne.symm (Fin.succ_ne_zero i))]
    | succ j =>
      by_cases hij : i = j
      · subst j; simp
      · simp [MvPowerSeries.pderiv_X_of_ne, Ne.symm hij]

theorem formalJet_polynomialFrame {m : ℕ} (c : Fin m → ℂ)
    (i : Fin (m+1)) (p : PiExponentApprox.FramePolynomial m) :
    formalJet c (PiExponentApprox.polynomialFrame m i p) =
      jetFrame m i (formalJet c p) :=
  derivation_map_of_X (formalJet c) (PiExponentApprox.polynomialFrame m i)
    (jetFrame m i) (formalJet_frame_X c i) p

theorem formalJet_polynomialFrameWord {m : ℕ} (c : Fin m → ℂ)
    (word : List (Fin (m+1))) (p : PiExponentApprox.FramePolynomial m) :
    formalJet c (PiExponentApprox.polynomialFrameWord m word p) =
      jetFrameWord m word (formalJet c p) := by
  induction word with
  | nil => rfl
  | cons i word ih =>
    rw [PiExponentApprox.polynomialFrameWord_cons, formalJet_polynomialFrame, ih]
    rfl

theorem formalJet_polynomialFrameWord_vanishing {m : ℕ} (c : Fin m → ℂ)
    (v : Fin (m+1) → ℚ) (hv : ∀ i, 0 ≤ v i) (H : ℚ)
    (p : PiExponentApprox.FramePolynomial m)
    (hp : formalJet c p ∈ JetGeometry.rationalWeightedIdeal v hv H)
    (word : List (Fin (m+1))) :
    formalJet c (PiExponentApprox.polynomialFrameWord m word p) ∈
      JetGeometry.rationalWeightedIdeal v hv (H - (word.map v).sum) := by
  rw [formalJet_polynomialFrameWord]
  exact jetFrameWord_mem_rationalWeightedIdeal v hv H (formalJet c p) hp word

end PiExponent.FormalLogJet

end

end OAI
end Source0023

-- Source: LogTwo/Geometry/ScaledJet.lean
section Source0024
-- Modified in this edition: unused plain lemmas removed; see reduction.json.
/-! The full formal logarithmic jet at an arbitrary Y-center. -/
namespace LogTwo.Geometry
open OAI PiExponentApprox MvPolynomial
open PiExponent.FormalLogJet PiExponent.FormalJetDerivatives
noncomputable section

def formalJetAt {m : ℕ} (y : ℂ) (c : Fin m → ℂ) :
    FramePolynomial m →ₐ[ℂ] MvPowerSeries (Fin (m+1)) ℂ :=
  (formalJet c).comp (scaleY y)

@[simp] theorem formalJetAt_Y {m : ℕ} (y : ℂ) (c : Fin m → ℂ) :
    formalJetAt y c (X (0 : Fin (m+1))) = MvPowerSeries.C y * (1 + MvPowerSeries.X 0) := by
  simp [formalJetAt, MvPowerSeries.algebraMap_apply]

@[simp] theorem formalJetAt_X {m : ℕ} (y : ℂ) (c : Fin m → ℂ) (i : Fin m) :
    formalJetAt y c (X i.succ) =
      MvPowerSeries.C (c i) + MvPowerSeries.X i.succ + formalLog m := by
  simp [formalJetAt]

def frameMonomial {m : ℕ} (h : ℕ) (α : Fin m → ℕ) : FramePolynomial m :=
  X 0 ^ h * ∏ i, X i.succ ^ α i

end
end LogTwo.Geometry
end Source0024

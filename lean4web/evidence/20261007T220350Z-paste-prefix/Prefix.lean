/-
Copyright 2026 Kenta Kitamura. Portions: OpenAI, openai/math (Apache-2.0).
Modified for LogTwo: flattening, rc4 compatibility, narrower imports, and
removal of unused plain lemmas. Individual provenance notices are retained.
See ../THIRD_PARTY_NOTICES.txt and ../LICENSES/openai-math-Apache-2.0.txt.
-/
module
public meta import Lean.Elab.Tactic
public meta import Lean.Elab.BuiltinEvalCommand
public import Batteries.Data.Nat.Basic
public import Batteries.Data.Nat.Lemmas
public import Batteries.Logic
public import Lean.Elab.Tactic.Omega
public import Lean.Meta.Tactic.Simp.BuiltinSimprocs.Core
public import Mathlib.Algebra.Algebra.Hom.Rat
public import Mathlib.Algebra.Category.Grp.Zero
public import Mathlib.Algebra.Category.ModuleCat.Ext.HasExt
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.EpiMono
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Monoidal
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.PullbackFree
public import Mathlib.Algebra.Group.ForwardDiff
public import Mathlib.Algebra.Homology.DerivedCategory.Ext.EnoughInjectives
public import Mathlib.Algebra.Homology.DerivedCategory.Ext.MapBijective
public import Mathlib.Algebra.Module.LocalizedModule.Away
public import Mathlib.Algebra.Module.Submodule.Union
public import Mathlib.Algebra.Order.Antidiag.FinsuppEquiv
public import Mathlib.AlgebraicGeometry.Modules.Tilde
public import Mathlib.AlgebraicGeometry.Morphisms.SchemeTheoreticallyDominant
public import Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Functor
public import Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Proper
public import Mathlib.AlgebraicGeometry.SpreadingOut
public import Mathlib.AlgebraicGeometry.ZariskisMainTheorem
public import Mathlib.AlgebraicTopology.ExtraDegeneracy
public import Mathlib.Analysis.Complex.Polynomial.Basic
public import Mathlib.Analysis.Polynomial.Basic
public import Mathlib.Analysis.Real.Pi.Bounds
public import Mathlib.Analysis.Real.Pi.Irrational
public import Mathlib.Analysis.SpecialFunctions.Choose
public import Mathlib.Analysis.SpecialFunctions.Complex.Analytic
public import Mathlib.Analysis.SpecialFunctions.Complex.LogBounds
public import Mathlib.CategoryTheory.Abelian.Projective.Ext
public import Mathlib.CategoryTheory.Sites.Hypercover.Subcanonical
public import Mathlib.Data.ENat.BigOperators
public import Mathlib.Data.ENat.SuccOrder
public import Mathlib.Data.FunLike.Basic
public import Mathlib.Data.Opposite
public import Mathlib.Data.SetLike.Basic
public import Mathlib.Data.Sym.Card
public import Mathlib.LinearAlgebra.DirectSum.Finite
public import Mathlib.NumberTheory.BernoulliPolynomials
public import Mathlib.NumberTheory.Chebyshev
public import Mathlib.NumberTheory.DiophantineApproximation.Basic
public import Mathlib.NumberTheory.FunctionField
public import Mathlib.RingTheory.GradedAlgebra.Radical
public import Mathlib.RingTheory.Ideal.AssociatedPrime.Finiteness
public import Mathlib.RingTheory.Ideal.AssociatedPrime.Localization
public import Mathlib.RingTheory.IntegralClosure.GoingDown
public import Mathlib.RingTheory.KrullDimension.Field
public import Mathlib.RingTheory.KrullDimension.LocalRing
public import Mathlib.RingTheory.KrullDimension.Polynomial
public import Mathlib.RingTheory.KrullDimension.Regular
public import Mathlib.RingTheory.LaurentSeries
public import Mathlib.RingTheory.LocalRing.Quotient
public import Mathlib.RingTheory.Localization.AtPrime.Extension
public import Mathlib.RingTheory.MvPowerSeries.Equiv
public import Mathlib.RingTheory.NoetherNormalization
public import Mathlib.RingTheory.Noetherian.Nilpotent
public import Mathlib.RingTheory.OrderOfVanishing.Noetherian
public import Mathlib.RingTheory.Polynomial.HilbertPoly
public import Mathlib.RingTheory.PowerSeries.Log
public import Mathlib.RingTheory.RamificationInertia.Basic
public import Mathlib.RingTheory.Regular.Flat
public import Mathlib.RingTheory.RegularLocalRing.Polynomial
public import Mathlib.Tactic
public import Mathlib.Topology.Sheaves.Flasque
public import Mathlib.Topology.Sheaves.LocallySurjective
public import Mathlib.Topology.Sheaves.MayerVietoris
@[expose] public section

/-! Reduced proof source for Lean v4.35.0-rc4.
The public target and its independent definition are unchanged.
Generation is not verification: see lite-build-status.json and reduction.json.
-/
-- Browser memory improvement: omit proof-internal goal/hover history for dependencies.
-- Outer command information remains, as required by rc4's language server.
-- Proof elaboration, kernel checking, errors and the final axiom audit remain enabled.
set_option Elab.async false
set_option linter.all false
namespace LogTwoWebMemory
syntax (name := quietProof) "logtwo_quiet " tacticSeq : tactic
@[tactic quietProof] meta def evalQuietProof : Lean.Elab.Tactic.Tactic :=
  fun stx => Lean.Elab.withEnableInfoTree false do
    Lean.Elab.Tactic.evalTactic stx[1]
end LogTwoWebMemory


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
      |x - (p : ℝ) / q| ≤ (q : ℝ) ^ (-ν) := by logtwo_quiet
  obtain ⟨N, hN⟩ := exists_nat_gt (Real.exp X)
  obtain ⟨p, q, hq, herr⟩ := hbad (max 2 N)
  have hq2 : 2 ≤ q := (le_max_left _ _).trans hq
  have hNq : N ≤ q := (le_max_right _ _).trans hq
  have hexp : Real.exp X < (q : ℝ) := hN.trans_le (by logtwo_quiet exact_mod_cast hNq)
  have hlog : X < Real.log q := by logtwo_quiet
    simpa using Real.log_lt_log (Real.exp_pos X) hexp
  exact ⟨p, q, hq2, hlog, herr⟩

/-- Any threshold depending on the entire finite past can be imposed. This
preserves the quantifier order needed by rapidly separated logarithmic weights. -/
theorem exists_sequential_approximations {x ν : ℝ}
    (hbad : UnboundedApproximations x ν)
    (threshold : (i : ℕ) → (Fin i → ℕ) → ℝ) :
    ∃ p : ℕ → ℤ, ∃ q : ℕ → ℕ, ∀ i : ℕ,
      2 ≤ q i ∧ threshold i (fun j => q j) < Real.log (q i) ∧
      |x - (p i : ℝ) / q i| ≤ (q i : ℝ) ^ (-ν) := by logtwo_quiet
  choose p₀ q₀ hq₀ hlog₀ herr₀ using exists_large_log_approximation hbad
  let pick (X : ℝ) : ℤ × ℕ := (p₀ X, q₀ X)
  let point : ℕ → ℤ × ℕ := Nat.strongRec fun i previous =>
    pick (threshold i (fun j => (previous j j.isLt).2))
  have heq (i : ℕ) : point i = pick (threshold i (fun j => (point j).2)) := by logtwo_quiet
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
    EventualLowerBound x ↔ IntegerEventualLowerBound x := by logtwo_quiet
  unfold EventualLowerBound IntegerEventualLowerBound
  constructor
  · intro h ν hν
    obtain ⟨Q, hQ, hb⟩ := h ν hν
    refine ⟨Q, by logtwo_quiet exact_mod_cast hQ, ?_⟩
    intro p q hq
    have hq0 : 0 ≤ q := le_trans (by logtwo_quiet omega) hq
    have hnat : Q ≤ q.toNat := by logtwo_quiet omega
    have heq : (q.toNat : ℝ) = (q : ℝ) := by logtwo_quiet
      exact_mod_cast (Int.toNat_of_nonneg hq0)
    simpa only [heq] using hb p q.toNat hnat
  · intro h ν hν
    obtain ⟨Q, hQ, hb⟩ := h ν hν
    have hQ0 : 0 ≤ Q := by logtwo_quiet omega
    refine ⟨Q.toNat, by logtwo_quiet omega, ?_⟩
    intro p q hq
    have hqi : Q ≤ (q : ℤ) := by logtwo_quiet omega
    simpa using hb p q hqi

theorem finite_rat_den_le_abs_sub_lt_one (x : ℝ) (N : ℕ) :
    {r : ℚ | r.den ≤ N ∧ |x - (r : ℝ)| < 1}.Finite := by logtwo_quiet
  classical
  let f : ℚ → ℤ × ℕ := fun r => (r.num, r.den)
  have hinj : Function.Injective f := by logtwo_quiet
    intro a b hab
    have hp := Prod.mk.inj hab
    rw [← Rat.num_div_den a, ← Rat.num_div_den b, hp.1, hp.2]
  let t : Set (ℤ × ℕ) := ⋃ (q : ℕ) (_ : q ∈ Set.Icc 1 N),
    Set.Icc ⌈(x - 1) * q⌉ ⌊(x + 1) * q⌋ ×ˢ {q}
  have ht : t.Finite :=
    Set.Finite.biUnion (Set.finite_Icc _ _) fun q _ =>
      Set.Finite.prod (Set.finite_Icc _ _) (Set.finite_singleton _)
  have hsub : f '' {r : ℚ | r.den ≤ N ∧ |x - (r : ℝ)| < 1} ⊆ t := by logtwo_quiet
    rintro _ ⟨r, ⟨hrN, hr⟩, rfl⟩
    have hrden : (0 : ℝ) < r.den := Nat.cast_pos.mpr r.pos
    have hrlow : x - 1 < (r : ℝ) := by logtwo_quiet linarith [(abs_lt.mp hr).2]
    have hrhigh : (r : ℝ) < x + 1 := by logtwo_quiet linarith [(abs_lt.mp hr).1]
    have hnlow : (x - 1) * r.den ≤ (r.num : ℝ) := by logtwo_quiet
      rw [Rat.cast_def] at hrlow
      exact ((lt_div_iff₀ hrden).mp hrlow).le
    have hnhigh : (r.num : ℝ) ≤ (x + 1) * r.den := by logtwo_quiet
      rw [Rat.cast_def] at hrhigh
      exact ((div_lt_iff₀ hrden).mp hrhigh).le
    simp only [t, Set.mem_iUnion]
    refine ⟨r.den, ⟨r.pos, hrN⟩, ?_⟩
    exact ⟨⟨Int.ceil_le.mpr hnlow, Int.le_floor.mpr hnhigh⟩, rfl⟩
  exact (ht.subset hsub).of_finite_image hinj.injOn

theorem two_mem_approximationExponents {x : ℝ} (hx : Irrational x) :
    (2 : ℝ) ∈ ApproximationExponents x := by logtwo_quiet
  refine ⟨by logtwo_quiet norm_num, ?_⟩
  have hi := Real.infinite_rat_abs_sub_lt_one_div_den_sq_of_irrational hx
  have hf := finite_rat_den_le_abs_sub_lt_one x 1
  apply (hi.sdiff hf).mono
  intro r hr
  have hrden : 1 ≤ (r.den : ℝ) := by logtwo_quiet exact_mod_cast r.pos
  have hrone : |x - (r : ℝ)| < 1 :=
    hr.1.trans_le (by logtwo_quiet
      simpa only [div_one] using
        one_div_le_one_div_of_le (by logtwo_quiet norm_num : (0 : ℝ) < 1)
          (by logtwo_quiet nlinarith : (1 : ℝ) ≤ (r.den : ℝ)^2))
  have hr2 : 2 ≤ r.den := by logtwo_quiet
    by_contra h
    exact hr.2 ⟨by logtwo_quiet omega, hrone⟩
  refine ⟨hr2, abs_pos.mpr (sub_ne_zero.mpr (hx.ne_rat r)), ?_⟩
  simpa only [Set.mem_ofPred_eq, Real.rpow_neg (Nat.cast_nonneg r.den),
    Real.rpow_two, one_div] using hr.1

theorem finite_goodRationalApproximations_of_eventualLowerBound {x ν : ℝ}
    (hx : EventualLowerBound x) (hν : 2 < ν) :
    (GoodRationalApproximations x ν).Finite := by logtwo_quiet
  obtain ⟨Q, hQ, hb⟩ := hx ν hν
  apply (finite_rat_den_le_abs_sub_lt_one x Q).subset
  intro r hr
  have hltQ : r.den < Q := by logtwo_quiet
    by_contra h
    have h := hb r.num r.den (by logtwo_quiet omega)
    rw [← Rat.cast_def] at h
    exact (not_lt_of_ge h) hr.2.2
  refine ⟨hltQ.le, hr.2.2.trans_le ?_⟩
  exact Real.rpow_le_one_of_one_le_of_nonpos
    (by logtwo_quiet exact_mod_cast r.pos) (by logtwo_quiet linarith)

theorem irrationalityExponent_eq_two_of_eventualLowerBound {x : ℝ}
    (hi : Irrational x) (hx : EventualLowerBound x) :
    irrationalityExponent x = 2 := by logtwo_quiet
  have htwo := two_mem_approximationExponents hi
  have hbound : ∀ ν ∈ ApproximationExponents x, ν ≤ 2 := by logtwo_quiet
    intro ν hν
    by_contra h
    exact (finite_goodRationalApproximations_of_eventualLowerBound hx (by logtwo_quiet linarith)).not_infinite hν.2
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
    SequentialLowerBound x ↔ EventualLowerBound x := by logtwo_quiet
  constructor
  · intro h ν hν
    obtain ⟨k, hk⟩ := exists_nat_one_div_lt (by logtwo_quiet linarith : (0 : ℝ) < ν - 2)
    obtain ⟨Q, hQ, hb⟩ := h (k + 1) (by logtwo_quiet omega)
    refine ⟨Q, hQ, ?_⟩
    intro p q hq
    have hbase : (1 : ℝ) ≤ q := by logtwo_quiet exact_mod_cast (show 1 ≤ q by logtwo_quiet omega)
    have hexp : -(ν : ℝ) ≤ -(2 + 1 / ((k + 1 : ℕ) : ℝ)) := by logtwo_quiet
      push_cast
      linarith
    exact (Real.rpow_le_rpow_of_exponent_le hbase hexp).trans (hb p q hq)
  · intro h n hn
    have hnreal : (0 : ℝ) < n := by logtwo_quiet exact_mod_cast (show 0 < n by logtwo_quiet omega)
    apply h
    linarith [one_div_pos.mpr hnreal]

/-- Failure of the target bound supplies the bad approximation family used by
the parameter construction. The integer n is fixed before its denominators. -/
theorem exists_unbounded_of_not_sequential {x : ℝ} (h : ¬ SequentialLowerBound x) :
    ∃ n : ℕ, 1 ≤ n ∧ UnboundedApproximations x (2 + 1 / (n : ℝ)) := by logtwo_quiet
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
    Irrational x := by logtwo_quiet
  rintro ⟨r, rfl⟩
  obtain ⟨Q, hQ, hb⟩ := h 3 (by logtwo_quiet norm_num)
  have hk : (0 : ℝ) < (Q + 1 : ℕ) := by logtwo_quiet positivity
  have hq : Q ≤ r.den * (Q + 1) := by logtwo_quiet nlinarith [r.pos]
  have hfrac : ((r.num * (Q + 1 : ℕ) : ℤ) : ℝ) /
      ((r.den * (Q + 1) : ℕ) : ℝ) = (r : ℝ) := by logtwo_quiet
    push_cast
    rw [mul_div_mul_right _ _ (by logtwo_quiet positivity : (Q : ℝ) + 1 ≠ 0)]
    exact Rat.cast_def r |>.symm
  have hh := hb (r.num * (Q + 1 : ℕ)) (r.den * (Q + 1)) hq
  rw [hfrac, sub_self, abs_zero] at hh
  have hp : (0 : ℝ) < (r.den * (Q + 1) : ℕ) := by logtwo_quiet
    exact_mod_cast (Nat.mul_pos r.pos (Nat.succ_pos Q))
  exact (not_le_of_gt (Real.rpow_pos_of_pos hp (-3))) hh

/-- Conditional endgame: the difficult analytic lower bound is an explicit argument. -/
theorem exponent_eq_two_of_sequentialLowerBound {x : ℝ}
    (h : SequentialLowerBound x) : irrationalityExponent x = 2 := by logtwo_quiet
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

theorem b_sub_a (d : ℚ) : b d - a d = d ^ 2 / 4 := by logtwo_quiet
  unfold b a
  ring

theorem c_theta_sub_b (d : ℚ) : c d * theta d - b d = d ^ 2 / 4 := by logtwo_quiet
  unfold c theta b
  ring

theorem one_sub_cb (d : ℚ) : 1 - c d * b d = d ^ 2 * (1 + 3 * d / 8) := by logtwo_quiet
  unfold c b
  ring

theorem theta_sub_a_sq (d : ℚ) : theta d - (a d) ^ 2 = d ^ 2 * (7 / 4 - d - d ^ 2) := by logtwo_quiet
  unfold theta a
  ring

theorem explicit_shape {d : ℚ} (hd : 0 < d) (hsmall : d ≤ 1 / 12) :
    Shape (theta d) (a d) (b d) (c d) := by logtwo_quiet
  have hs : 0 < d ^ 2 := sq_pos_of_pos hd
  have hsbound : d ^ 2 ≤ 1 / 144 := by logtwo_quiet nlinarith
  have hda : d ^ 2 < d / 2 := by logtwo_quiet nlinarith
  have hcb : 0 < d ^ 2 * (1 + 3 * d / 8) := mul_pos hs (by logtwo_quiet linarith)
  have hasq : 0 < d ^ 2 * (7 / 4 - d - d ^ 2) :=
    mul_pos hs (by logtwo_quiet linarith)
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

theorem delta_pos (n : ℕ) : 0 < delta n := by logtwo_quiet unfold delta; positivity

theorem delta_le {n : ℕ} (hn : 1 ≤ n) : delta n ≤ 1 / 12 := by logtwo_quiet
  have hn' : (1 : ℚ) ≤ n := by logtwo_quiet exact_mod_cast hn
  unfold delta
  apply (div_le_div_iff₀ (by logtwo_quiet positivity) (by logtwo_quiet norm_num : (0 : ℚ) < 12)).mpr
  linarith

theorem shape (n : ℕ) (hn : 1 ≤ n) :
    Shape (theta (delta n)) (a (delta n)) (b (delta n)) (c (delta n)) :=
  explicit_shape (delta_pos n) (delta_le hn)

theorem gap_after_eta (n : ℕ) (hn : 1 ≤ n) :
    finalGap n = initialGap n * (1 - a (delta n) / 2) := by logtwo_quiet
  have hn0 : (n : ℚ) ≠ 0 := by logtwo_quiet exact_mod_cast (show n ≠ 0 by logtwo_quiet omega)
  have hden : 2 * (n : ℚ) + 1 ≠ 0 := by logtwo_quiet positivity
  dsimp [finalGap, nu, a, theta, initialGap, eta, delta]
  field_simp
  ring

theorem epsilon_eq (n : ℕ) : epsilon n = initialGap n / 4 := by logtwo_quiet
  simp only [epsilon, initialGap, delta, div_eq_mul_inv, mul_inv_rev]
  ring

theorem nu_div_factor (n : ℕ) (hn : 1 ≤ n) :
    nu n / truncationFactor n = epsilon n / 4 := by logtwo_quiet
  have hn0 : (n : ℚ) ≠ 0 := by logtwo_quiet exact_mod_cast (show n ≠ 0 by logtwo_quiet omega)
  have hden : 2 * (n : ℚ) + 1 ≠ 0 := by logtwo_quiet positivity
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

theorem scalarConditions (n : ℕ) (hn : 1 ≤ n) : ScalarConditions n := by logtwo_quiet
  have hn' : (1 : ℚ) ≤ n := by logtwo_quiet exact_mod_cast hn
  have hnpos : (0 : ℚ) < n := by logtwo_quiet linarith
  have hd := delta_pos n
  have hdsmall := delta_le hn
  have hs := shape n hn
  have hg : 0 < initialGap n := by logtwo_quiet unfold initialGap; positivity
  have hgsmall : initialGap n ≤ 1 / 48 := by logtwo_quiet
    unfold initialGap
    apply (div_le_iff₀ (by logtwo_quiet positivity : (0 : ℚ) < 4 * n)).mpr
    linarith
  have ha : a (delta n) < 1 := hs.a_lt_b.trans hs.b_lt_one
  have hgap : initialGap n / 2 < finalGap n := by logtwo_quiet
    rw [gap_after_eta n hn]
    nlinarith
  have heps : 0 < epsilon n := by logtwo_quiet rw [epsilon_eq]; positivity
  have htheta : (11 / 12 : ℚ) ≤ theta (delta n) := by logtwo_quiet dsimp [theta]; linarith
  have hF : (256 : ℚ) ≤ truncationFactor n := by logtwo_quiet
    unfold truncationFactor
    nlinarith [sq_nonneg (2 * (n : ℚ))]
  constructor
  · exact hs
  · unfold eta; positivity
  · unfold eta
    apply (div_lt_iff₀ (by logtwo_quiet positivity : (0 : ℚ) < 32 * (2 * (n : ℚ) + 1) ^ 2)).mpr
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
    1 < b (delta n) / a (delta n) := by logtwo_quiet
  have hs := shape n hn
  have ha : 0 < a (delta n) := hs.theta_pos.trans hs.theta_lt_a
  have hb : 0 < b (delta n) := ha.trans hs.a_lt_b
  constructor
  · exact (lt_div_iff₀ hb).mpr (by logtwo_quiet simpa using hs.b_lt_c_theta)
  · exact (lt_div_iff₀ ha).mpr (by logtwo_quiet simpa using hs.a_lt_b)

end LogTwo.Parameters
end Source0005

-- Source: LogTwo/Dimension.lean
section Source0006
/-! Growth estimates used by the ceiling-based dimension and denominator choices. -/
namespace LogTwo.Parameters

open Filter
open scoped Topology

theorem geometric_over_succ_tendsto {r : ℝ} (hr : 1 < r) :
    Tendsto (fun m : ℕ => r ^ m / ((m : ℝ) + 1)) atTop atTop := by logtwo_quiet
  have hz : Tendsto (fun m : ℕ => ((m : ℝ) + 1) / r ^ m) atTop (𝓝 0) := by logtwo_quiet
    have h1 := tendsto_pow_const_div_const_pow_of_one_lt 1 hr
    have h0 := tendsto_pow_const_div_const_pow_of_one_lt 0 hr
    simpa only [pow_one, pow_zero, zero_add, add_div] using h1.add h0
  have hp : ∀ m : ℕ, (0 : ℝ) < ((m : ℝ) + 1) / r ^ m := by logtwo_quiet
    intro m
    have : 0 < r := by logtwo_quiet linarith
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
      atTop atTop := by logtwo_quiet
  have hs := shape n hn
  have hr := growth_ratios n hn
  have hb : 0 < b (delta n) := hs.theta_pos.trans (hs.theta_lt_a.trans hs.a_lt_b)
  have hc : 0 < c (delta n) := by logtwo_quiet linarith [hs.one_lt_c]
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
    K * (w0 / (2 * K * θ ^ m * w0)) * θ ^ m = 1 / 2 := by logtwo_quiet
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
    C ^ m ≤ (centerCount C m : ℚ) ∧ (centerCount C m : ℚ) ≤ 2 * C ^ m := by logtwo_quiet
  have hp : 1 ≤ C ^ m := one_le_pow₀ hC
  refine ⟨Nat.le_ceil _, ?_⟩
  have ht := Nat.ceil_lt_add_one (show 0 ≤ C ^ m by logtwo_quiet linarith)
  dsimp [centerCount]
  linarith

theorem centerCount_pos {C : ℚ} (hC : 1 ≤ C) (m : ℕ) : 0 < centerCount C m := by logtwo_quiet
  have hb := (centerCount_bounds hC m).1
  have hp : 1 ≤ C ^ m := one_le_pow₀ hC
  have : (0 : ℚ) < centerCount C m := by logtwo_quiet linarith
  exact_mod_cast this

theorem horizontalWeight_pos {B : ℚ} (hB : 0 < B) (m : ℕ) :
    0 < horizontalWeight B m := by logtwo_quiet unfold horizontalWeight; positivity

theorem verticalWeight_pos {θ B C : ℚ} (hθ : 0 < θ) (hB : 0 < B)
    (hC : 1 ≤ C) (m : ℕ) : 0 < verticalWeight θ B C m := by logtwo_quiet
  have hK := centerCount_pos hC m
  have hw := horizontalWeight_pos hB m
  unfold verticalWeight
  positivity

theorem count_over_horizontal_le {B C : ℚ} (hB : 0 < B) (hC : 1 ≤ C) (m : ℕ) :
    (centerCount C m : ℚ) / horizontalWeight B m ≤ 2 * (C * B) ^ m := by logtwo_quiet
  have hb := mul_le_mul_of_nonneg_right (centerCount_bounds hC m).2
    (pow_nonneg hB.le m)
  simpa [horizontalWeight, div_inv_eq_mul, mul_pow, mul_assoc] using hb

theorem verticalWeight_lower {θ B C : ℚ} (hθ : 0 < θ) (hB : 0 < B)
    (hC : 1 ≤ C) (m : ℕ) :
    2 * (C * θ / B) ^ m ≤ verticalWeight θ B C m := by logtwo_quiet
  have hb := mul_le_mul_of_nonneg_right (centerCount_bounds hC m).1
    (show 0 ≤ 2 * θ ^ m * (B ^ m)⁻¹ by logtwo_quiet positivity)
  simpa [verticalWeight, horizontalWeight, div_pow, mul_pow, div_eq_mul_inv,
    mul_comm, mul_left_comm, mul_assoc] using hb

theorem count_over_horizontal_tendsto {B C : ℚ} (hB : 0 < B) (hC : 1 ≤ C)
    (hCB : C * B < 1) :
    Tendsto (fun m => ((centerCount C m : ℚ) / horizontalWeight B m : ℚ) : ℕ → ℝ)
      atTop (𝓝 0) := by logtwo_quiet
  have hz : Tendsto (fun m : ℕ => 2 * ((C * B : ℚ) : ℝ) ^ m) atTop (𝓝 0) := by logtwo_quiet
    have hh := tendsto_pow_atTop_nhds_zero_of_lt_one
      (show (0 : ℝ) ≤ ((C * B : ℚ) : ℝ) by logtwo_quiet exact_mod_cast mul_nonneg (by logtwo_quiet linarith) hB.le)
      (show ((C * B : ℚ) : ℝ) < 1 by logtwo_quiet exact_mod_cast hCB)
    simpa using hh.const_mul 2
  apply squeeze_zero _ _ hz
  · intro m
    exact_mod_cast (div_nonneg (Nat.cast_nonneg _) (horizontalWeight_pos hB m).le)
  · intro m
    exact_mod_cast count_over_horizontal_le hB hC m

theorem verticalWeight_tendsto {θ B C : ℚ} (hθ : 0 < θ) (hB : 0 < B)
    (hC : 1 ≤ C) (hr : 1 < C * θ / B) :
    Tendsto (fun m => (verticalWeight θ B C m : ℝ)) atTop atTop := by logtwo_quiet
  have hp := tendsto_pow_atTop_atTop_of_one_lt
    (show (1 : ℝ) < ((C * θ / B : ℚ) : ℝ) by logtwo_quiet exact_mod_cast hr)
  apply tendsto_atTop_mono _ hp
  intro m
  have hlow := verticalWeight_lower hθ hB hC m
  have hpos : 0 ≤ (C * θ / B) ^ m := pow_nonneg (by logtwo_quiet linarith) m
  exact_mod_cast (show (C * θ / B) ^ m ≤ verticalWeight θ B C m by logtwo_quiet linarith)

theorem dimension_over_vertical_tendsto {θ B C : ℚ} (hθ : 0 < θ) (hB : 0 < B)
    (hC : 1 ≤ C) (hr : 1 < C * θ / B) :
    Tendsto (fun m : ℕ => (m : ℝ) / (verticalWeight θ B C m : ℝ)) atTop (𝓝 0) := by logtwo_quiet
  have hz := tendsto_pow_const_div_const_pow_of_one_lt 1
    (show (1 : ℝ) < ((C * θ / B : ℚ) : ℝ) by logtwo_quiet exact_mod_cast hr)
  simp only [pow_one] at hz
  apply squeeze_zero _ _ hz
  · intro m
    have hv : (0 : ℝ) < (verticalWeight θ B C m : ℝ) := by logtwo_quiet
      exact_mod_cast verticalWeight_pos hθ hB hC m
    positivity
  · intro m
    have hp : (0 : ℝ) < ((C * θ / B : ℚ) : ℝ) ^ m := by logtwo_quiet
      have : (0 : ℝ) < ((C * θ / B : ℚ) : ℝ) := by logtwo_quiet exact_mod_cast (show 0 < C * θ / B by logtwo_quiet linarith)
      positivity
    apply div_le_div_of_nonneg_left (Nat.cast_nonneg _) hp
    have hl := verticalWeight_lower hθ hB hC m
    have hq : 0 ≤ (C * θ / B) ^ m := pow_nonneg (by logtwo_quiet linarith) m
    exact_mod_cast (show (C * θ / B) ^ m ≤ verticalWeight θ B C m by logtwo_quiet linarith)

/-- All dimension requirements can be imposed at once, including any fixed
multiple of the arithmetic term `m/v₀`. The constants are chosen before `m`. -/
theorem exists_dimension (n : ℕ) (hn : 1 ≤ n) (ε A D R : ℝ) (hε : 0 < ε)
    (m₀ : ℕ) : ∃ m : ℕ, m₀ ≤ m ∧
      ((centerCount (c (delta n)) m : ℚ) / horizontalWeight (b (delta n)) m : ℝ) < ε ∧
      A * ((m : ℝ) / (verticalWeight (theta (delta n)) (b (delta n)) (c (delta n)) m : ℝ)) < ε ∧
      D < (verticalWeight (theta (delta n)) (b (delta n)) (c (delta n)) m : ℝ) ∧
      R < ((b (delta n) / a (delta n) : ℚ) : ℝ) ^ m / ((m : ℝ) + 1) := by logtwo_quiet
  have hs := shape n hn
  have hb := hs.theta_pos.trans (hs.theta_lt_a.trans hs.a_lt_b)
  have hr := (growth_ratios n hn).1
  have hc := count_over_horizontal_tendsto hb hs.one_lt_c.le hs.cb_lt_one
  have hm := dimension_over_vertical_tendsto hs.theta_pos hb hs.one_lt_c.le hr
  have hv := verticalWeight_tendsto hs.theta_pos hb hs.one_lt_c.le hr
  have hA : Tendsto (fun m : ℕ => A * ((m : ℝ) /
      (verticalWeight (theta (delta n)) (b (delta n)) (c (delta n)) m : ℝ)))
      atTop (𝓝 0) := by logtwo_quiet simpa using hm.const_mul A
  have he := (hc.eventually_lt_const hε).and (hA.eventually_lt_const hε)
  have he' := he.and ((hv.eventually (eventually_gt_atTop D)).and
    ((dimension_growth n hn).2.2.eventually (eventually_gt_atTop R)))
  obtain ⟨m, hm₀, ⟨hmc, hmA⟩, hmD, hmR⟩ :=
    ((eventually_ge_atTop m₀).and he').exists
  exact ⟨m, hm₀, by logtwo_quiet exact_mod_cast hmc, hmA, hmD, hmR⟩

theorem chosen_volume_ratio {θ B C : ℚ} (hθ : 0 < θ) (hB : 0 < B)
    (hC : 1 ≤ C) (m : ℕ) :
    (centerCount C m : ℚ) * (horizontalWeight B m / verticalWeight θ B C m) * θ ^ m =
      1 / 2 := by logtwo_quiet
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

theorem centerY_strictMono : StrictMono centerY := by logtwo_quiet
  apply strictMono_nat_of_lt_succ
  intro n
  dsimp [centerY]
  rw [pow_succ]
  nlinarith [pow_pos (by logtwo_quiet norm_num : (0 : ℚ) < 2) n]

theorem centerY_injective : Function.Injective centerY := centerY_strictMono.injective

theorem complex_centerY_injective : Function.Injective (fun j : ℕ => (2 : ℂ) ^ j) := by logtwo_quiet
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

@[simp] theorem valueRow_exponent (m j : ℕ) : rowExponent (valueRow m j) = 0 := by logtwo_quiet
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
    (scale A r c).det = ((∏ i, r i) * (∏ i, c i)) * A.det := by logtwo_quiet
  have heq : scale A r c = Matrix.diagonal r * A * Matrix.diagonal c := by logtwo_quiet
    ext i j
    simp [scale]
  rw [heq, Matrix.det_mul, Matrix.det_mul, Matrix.det_diagonal, Matrix.det_diagonal]
  ring

/-- Clearing denominators in the very same minor gives a nonzero integer determinant. -/
theorem scaled_integer_det_ne_zero (A : Matrix ι ι ℚ) (r c : ι → ℚ)
    (Z : Matrix ι ι ℤ) (hA : A.det ≠ 0)
    (hr : ∀ i, r i ≠ 0) (hc : ∀ i, c i ≠ 0)
    (hZ : ∀ i j, (Z i j : ℚ) = scale A r c i j) : Z.det ≠ 0 := by logtwo_quiet
  have heq : (Z.det : ℚ) = (scale A r c).det := by logtwo_quiet
    rw [Int.cast_det]
    congr 1
    ext i j
    exact hZ i j
  have hn : (Z.det : ℚ) ≠ 0 := by logtwo_quiet
    rw [heq, det_scale]
    exact mul_ne_zero (mul_ne_zero (Finset.prod_ne_zero_iff.mpr (by logtwo_quiet simpa using hr))
      (Finset.prod_ne_zero_iff.mpr (by logtwo_quiet simpa using hc))) hA
  exact fun hz => hn (by logtwo_quiet simp [hz])

/-- The generic arithmetic lower bound; the concrete denominator estimates are separate. -/
theorem scaled_integer_lower_bound (A : Matrix ι ι ℚ) (r c : ι → ℚ)
    (Z : Matrix ι ι ℤ) (hA : A.det ≠ 0)
    (hr : ∀ i, r i ≠ 0) (hc : ∀ i, c i ≠ 0)
    (hZ : ∀ i j, (Z i j : ℚ) = scale A r c i j) :
    (1 : ℚ) ≤ |((∏ i, r i) * (∏ i, c i)) * A.det| := by logtwo_quiet
  have hn := scaled_integer_det_ne_zero A r c Z hA hr hc hZ
  have hi : (1 : ℤ) ≤ |Z.det| := by logtwo_quiet
    have := abs_pos.mpr hn
    omega
  have heq : (Z.det : ℚ) = ((∏ i, r i) * (∏ i, c i)) * A.det := by logtwo_quiet
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

@[simp] theorem rescale_C (a : σ → ℚ) (b : ℚ) : rescale a (C b) = C b := by logtwo_quiet
  simp [rescale]

@[simp] theorem rescale_X (a : σ → ℚ) (i : σ) : rescale a (X i) = C (a i) * X i := by logtwo_quiet
  simp [rescale]

variable [Fintype σ]

theorem rescale_monomial (a : σ → ℚ) (d : σ →₀ ℕ) (b : ℚ) :
    rescale a (monomial d b) = monomial d (b * ∏ i, a i ^ d i) := by logtwo_quiet
  rw [rescale, eval₂Hom_monomial, monomial_eq]
  rw [Finsupp.prod_fintype d (fun i k => (C (a i) * X i) ^ k) (by logtwo_quiet intro i; simp)]
  rw [Finsupp.prod_fintype d (fun i k => (X i : MvPolynomial σ ℚ) ^ k) (by logtwo_quiet intro i; simp)]
  simp only [mul_pow, ← map_pow,
    Finset.prod_mul_distrib, ← map_prod, map_mul, mul_assoc]

theorem coeff_rescale (a : σ → ℚ) (P : MvPolynomial σ ℚ) (d : σ →₀ ℕ) :
    (rescale a P).coeff d = P.coeff d * ∏ i, a i ^ d i := by logtwo_quiet
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

theorem lcmBelow_ne_zero (T : ℕ) : lcmBelow T ≠ 0 := by logtwo_quiet
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
      C (lcmBelow T : ℚ) * truncatedLog T := by logtwo_quiet
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
    rescale (variableScale q) (truncatedLog T) = truncatedLog T := by logtwo_quiet
  simp [truncatedLog, map_sum, variableScale]

theorem coeff_rescale_row {m : ℕ} (q : Fin m → ℕ)
    (P : MvPolynomial (Option (Fin m)) ℚ) (r : Row m) :
    (rescale (variableScale q) P).coeff (rowExponent r) =
      P.coeff (rowExponent r) * rowMultiplier q r := by logtwo_quiet
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
          (C ((j : ℚ) * rationalPoint p q i) + truncatedLog (T i) + X (some i)) := by logtwo_quiet
  have hqi : (q i : ℚ) ≠ 0 := by logtwo_quiet exact_mod_cast hq i
  simp only [integerFactor, map_add, map_mul, MvPolynomial.map_C, MvPolynomial.map_X,
    map_integerLog, rescale_C, rescale_truncatedLog, rescale_X, variableScale]
  change C (lcmBelow (T i) : ℚ) * C (j : ℚ) * C (p i : ℚ) +
      C (q i : ℚ) * (C (lcmBelow (T i) : ℚ) * truncatedLog (T i)) +
      C (lcmBelow (T i) : ℚ) * X (some i) = _
  simp only [← map_mul, rationalPoint]
  have hconst : (q i : ℚ) * lcmBelow (T i) * ((j : ℚ) * ((p i : ℚ) / q i)) =
      (lcmBelow (T i) : ℚ) * j * p i := by logtwo_quiet field_simp
  have hvar : (q i : ℚ) * lcmBelow (T i) * (q i : ℚ)⁻¹ = lcmBelow (T i) := by logtwo_quiet
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
        rescale (variableScale q) (columnExpansion (rationalPoint p q) T j col) := by logtwo_quiet
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
        columnMultiplier q T col := by logtwo_quiet
  have he := congrArg (fun P : MvPolynomial (Option (Fin m)) ℚ => P.coeff (rowExponent row))
    (map_integerColumnExpansion p q T hq row.j col)
  rw [MvPolynomial.coeff_map, MvPolynomial.coeff_C_mul, coeff_rescale_row] at he
  change (integerMatrix p q T row col : ℚ) =
    columnMultiplier q T col *
      (coefficientMatrix (rationalPoint p q) T row col * rowMultiplier q row) at he
  rw [he]
  ring

theorem rowMultiplier_ne_zero {m : ℕ} (q : Fin m → ℕ) (hq : ∀ i, q i ≠ 0) (r : Row m) :
    rowMultiplier q r ≠ 0 := by logtwo_quiet
  apply Finset.prod_ne_zero_iff.mpr
  intro i _
  exact pow_ne_zero _ (inv_ne_zero (by logtwo_quiet exact_mod_cast hq i))

theorem columnMultiplier_ne_zero {m : ℕ} (q T : Fin m → ℕ)
    (hq : ∀ i, q i ≠ 0) (c : Column m) : columnMultiplier q T c ≠ 0 := by logtwo_quiet
  apply Finset.prod_ne_zero_iff.mpr
  intro i _
  apply pow_ne_zero
  exact mul_ne_zero (by logtwo_quiet exact_mod_cast hq i) (by logtwo_quiet exact_mod_cast lcmBelow_ne_zero (T i))

theorem rowMultiplier_pos {m : ℕ} (q : Fin m → ℕ) (hq : ∀ i, q i ≠ 0) (r : Row m) :
    0 < rowMultiplier q r := by logtwo_quiet
  apply Finset.prod_pos
  intro i _
  apply pow_pos
  apply inv_pos.mpr
  exact_mod_cast Nat.pos_of_ne_zero (hq i)

theorem columnMultiplier_pos {m : ℕ} (q T : Fin m → ℕ)
    (hq : ∀ i, q i ≠ 0) (c : Column m) : 0 < columnMultiplier q T c := by logtwo_quiet
  apply Finset.prod_pos
  intro i _
  apply pow_pos
  exact mul_pos (by logtwo_quiet exact_mod_cast Nat.pos_of_ne_zero (hq i))
    (by logtwo_quiet exact_mod_cast lcmBelow_pos (T i))

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
      (∏ j, columnMultiplier q T (minor.columns j))) * minor.matrix.det| := by logtwo_quiet
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
    Real.log (rowMultiplier q r : ℝ) = -rowLogSaving q r := by logtwo_quiet
  simp only [rowMultiplier, Rat.cast_prod, Rat.cast_pow, Rat.cast_inv, Rat.cast_natCast]
  rw [Real.log_prod (fun i _ => pow_ne_zero _ (inv_ne_zero (by logtwo_quiet exact_mod_cast hq i)))]
  simp [Real.log_pow, Real.log_inv, rowLogSaving, Finset.sum_neg_distrib]

theorem log_columnMultiplier {m : ℕ} (q T : Fin m → ℕ)
    (hq : ∀ i, q i ≠ 0) (c : Column m) :
    Real.log (columnMultiplier q T c : ℝ) = columnLogCost q T c := by logtwo_quiet
  simp only [columnMultiplier, Rat.cast_prod, Rat.cast_pow, Rat.cast_mul, Rat.cast_natCast]
  rw [Real.log_prod (fun i _ => pow_ne_zero _ (mul_ne_zero
    (by logtwo_quiet exact_mod_cast hq i) (by logtwo_quiet exact_mod_cast lcmBelow_ne_zero (T i))))]
  apply Finset.sum_congr rfl
  intro i _
  rw [Real.log_pow, Real.log_mul (by logtwo_quiet exact_mod_cast hq i)
    (by logtwo_quiet exact_mod_cast lcmBelow_ne_zero (T i))]

/-- Exact logarithmic lower bound for the same minor used by interpolation. -/
theorem fullRowMinor_logarithmic_bound {m : ℕ} {w : Weights m} {H : ℚ}
    (p : Fin m → ℤ) (q T : Fin m → ℕ) (hq : ∀ i, q i ≠ 0)
    (minor : FullRowMinor w H (rationalPoint p q) T) :
    (∑ i, rowLogSaving q (minor.rows i)) - (∑ j, columnLogCost q T (minor.columns j)) ≤
      Real.log |(minor.matrix.det : ℝ)| := by logtwo_quiet
  let R : ℚ := ∏ i, rowMultiplier q (minor.rows i)
  let C : ℚ := ∏ j, columnMultiplier q T (minor.columns j)
  have hr : 0 < R := Finset.prod_pos (fun i _ => rowMultiplier_pos q hq _)
  have hc : 0 < C := Finset.prod_pos (fun j _ => columnMultiplier_pos q T hq _)
  have hr' : (0 : ℝ) < R := by logtwo_quiet exact_mod_cast hr
  have hc' : (0 : ℝ) < C := by logtwo_quiet exact_mod_cast hc
  have hd : (0 : ℝ) < |(minor.matrix.det : ℝ)| := by logtwo_quiet
    apply abs_pos.mpr
    exact_mod_cast minor.matrix_det_ne_zero
  have hb := fullRowMinor_arithmetic_bound p q T hq minor
  have hb' : (1 : ℝ) ≤ |((R * C : ℚ) : ℝ) * (minor.matrix.det : ℝ)| := by logtwo_quiet
    exact_mod_cast hb
  rw [Rat.cast_mul, abs_mul, abs_of_pos (mul_pos hr' hc')] at hb'
  have hh := Real.log_le_log (by logtwo_quiet norm_num : (0 : ℝ) < 1) hb'
  rw [Real.log_one, Real.log_mul (mul_pos hr' hc').ne' hd.ne',
    Real.log_mul hr'.ne' hc'.ne'] at hh
  have hR : Real.log (R : ℝ) = -∑ i, rowLogSaving q (minor.rows i) := by logtwo_quiet
    dsimp [R]
    rw [Rat.cast_prod, Real.log_prod (fun i _ => by logtwo_quiet
      exact_mod_cast rowMultiplier_ne_zero q hq (minor.rows i))]
    simp only [log_rowMultiplier q hq, Finset.sum_neg_distrib]
  have hC : Real.log (C : ℝ) = ∑ j, columnLogCost q T (minor.columns j) := by logtwo_quiet
    dsimp [C]
    rw [Rat.cast_prod, Real.log_prod (fun j _ => by logtwo_quiet
      exact_mod_cast columnMultiplier_ne_zero q T hq (minor.columns j))]
    simp only [log_columnMultiplier q T hq]
  rw [hR, hC] at hh
  linarith

/-- Each weighted column has a coordinate bound needed for the uniform denominator D_H. -/
theorem alpha_le_floor {m : ℕ} (w : Weights m) (H : ℚ) (c : Column m)
    (hc : AdmissibleColumn w H c) (i : Fin m) : c.alpha i ≤ ⌊H / w.w i⌋₊ := by logtwo_quiet
  have hsum : w.w i * c.alpha i ≤ ∑ k, w.w k * c.alpha k :=
    Finset.single_le_sum (fun k _ => mul_nonneg (w.w_pos k).le (Nat.cast_nonneg _))
      (Finset.mem_univ i)
  have hh : w.w i * c.alpha i ≤ H := by logtwo_quiet
    have hzero : 0 ≤ w.w0 * c.h := mul_nonneg w.w0_pos.le (Nat.cast_nonneg _)
    dsimp [AdmissibleColumn] at hc
    linarith
  have hdiv : (c.alpha i : ℚ) ≤ H / w.w i := by logtwo_quiet
    apply (le_div_iff₀ (w.w_pos i)).mpr
    simpa only [mul_comm] using hh
  exact (Nat.le_floor_iff ((Nat.cast_nonneg _).trans hdiv)).mpr hdiv

def denominatorBudget {m : ℕ} (w : Weights m) (H : ℚ) (T : Fin m → ℕ) : ℝ :=
  ∑ i, (⌊H / w.w i⌋₊ : ℝ) * Real.log (lcmBelow (T i) : ℝ)

def columnQCost {m : ℕ} (q : Fin m → ℕ) (c : Column m) : ℝ :=
  ∑ i, (c.alpha i : ℝ) * Real.log (q i : ℝ)

theorem columnLogCost_le {m : ℕ} (w : Weights m) (H : ℚ) (q T : Fin m → ℕ)
    (c : Column m) (hc : AdmissibleColumn w H c) :
    columnLogCost q T c ≤ columnQCost q c + denominatorBudget w H T := by logtwo_quiet
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
      (minor.size : ℝ) * denominatorBudget w H T ≤ Real.log |(minor.matrix.det : ℝ)| := by logtwo_quiet
  have hcost : (∑ j, columnLogCost q T (minor.columns j)) ≤
      (∑ j, columnQCost q (minor.columns j)) + (minor.size : ℝ) * denominatorBudget w H T := by logtwo_quiet
    calc
      _ ≤ ∑ j, (columnQCost q (minor.columns j) + denominatorBudget w H T) :=
        Finset.sum_le_sum (fun j _ => columnLogCost_le w H q T _ (minor.column_valid j))
      _ = _ := by logtwo_quiet simp [Finset.sum_add_distrib]
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

theorem lcmConstant_pos : 0 < lcmConstant := by logtwo_quiet
  have := Real.log_pos (by logtwo_quiet norm_num : (1 : ℝ) < 4)
  dsimp [lcmConstant]
  linarith

theorem lcmBelow_dvd_lcmUpto (T : ℕ) : lcmBelow T ∣ Nat.lcmUpto T := by logtwo_quiet
  apply Finset.lcm_dvd
  intro k hk
  apply Finset.dvd_lcm (f := id)
  exact Finset.mem_Icc.mpr ⟨(Finset.mem_Ico.mp hk).1, (Finset.mem_Ico.mp hk).2.le⟩

theorem log_lcmBelow_le (T : ℕ) :
    Real.log (lcmBelow T : ℝ) ≤ lcmConstant * T := by logtwo_quiet
  calc
    _ ≤ Real.log (Nat.lcmUpto T : ℝ) := by logtwo_quiet
      apply Real.log_le_log (by logtwo_quiet exact_mod_cast lcmBelow_pos T)
      exact_mod_cast Nat.le_of_dvd (Nat.lcmUpto_pos T) (lcmBelow_dvd_lcmUpto T)
    _ ≤ _ := by logtwo_quiet
      rw [← Chebyshev.psi_eq_log_lcmUpto]
      exact Chebyshev.psi_le_const_mul_self (by logtwo_quiet positivity)

theorem denominatorBudget_le {m : ℕ} (w : Weights m) (H : ℚ) (hH : 0 ≤ H)
    (T : Fin m → ℕ) :
    denominatorBudget w H T ≤
      (H : ℝ) * lcmConstant * ∑ i, (T i : ℝ) / (w.w i : ℝ) := by logtwo_quiet
  unfold denominatorBudget
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro i _
  have hf : (⌊H / w.w i⌋₊ : ℝ) ≤ (H : ℝ) / (w.w i : ℝ) := by logtwo_quiet
    exact_mod_cast Nat.floor_le (div_nonneg hH (w.w_pos i).le)
  calc
    _ ≤ (⌊H / w.w i⌋₊ : ℝ) * (lcmConstant * T i) :=
      mul_le_mul_of_nonneg_left (log_lcmBelow_le (T i)) (Nat.cast_nonneg _)
    _ ≤ ((H : ℝ) / (w.w i : ℝ)) * (lcmConstant * T i) :=
      mul_le_mul_of_nonneg_right hf (mul_nonneg lcmConstant_pos.le (Nat.cast_nonneg _))
    _ = _ := by logtwo_quiet ring

def truncationOrders {m : ℕ} (w : Weights m) (F : ℚ) : Fin m → ℕ :=
  fun i => ⌈F * w.w i / w.v0⌉₊

theorem sum_truncation_div_le {m : ℕ} (w : Weights m) (F : ℚ) (hF : 0 ≤ F) :
    (∑ i, (truncationOrders w F i : ℝ) / (w.w i : ℝ)) ≤
      (F : ℝ) * m / (w.v0 : ℝ) + ∑ i, 1 / (w.w i : ℝ) := by logtwo_quiet
  calc
    _ ≤ ∑ i, (((F : ℝ) * (w.w i : ℝ) / (w.v0 : ℝ) + 1) / (w.w i : ℝ)) := by logtwo_quiet
      apply Finset.sum_le_sum
      intro i _
      apply div_le_div_of_nonneg_right _ (by logtwo_quiet exact_mod_cast (w.w_pos i).le)
      have hh := (Nat.ceil_lt_add_one (div_nonneg (mul_nonneg hF (w.w_pos i).le) w.v0_pos.le)).le
      exact_mod_cast hh
    _ = ∑ i, ((F : ℝ) / (w.v0 : ℝ) + 1 / (w.w i : ℝ)) := by logtwo_quiet
      apply Finset.sum_congr rfl
      intro i _
      field_simp [(show (w.w i : ℝ) ≠ 0 by logtwo_quiet exact_mod_cast (w.w_pos i).ne'),
        (show (w.v0 : ℝ) ≠ 0 by logtwo_quiet exact_mod_cast w.v0_pos.ne')]
    _ = _ := by logtwo_quiet simp [Finset.sum_add_distrib]; ring

theorem truncation_denominatorBudget_le {m : ℕ} (w : Weights m)
    (H F : ℚ) (hH : 0 ≤ H) (hF : 0 ≤ F) :
    denominatorBudget w H (truncationOrders w F) ≤
      (H : ℝ) * (lcmConstant * (F : ℝ) * m / (w.v0 : ℝ) +
        lcmConstant * ∑ i, 1 / (w.w i : ℝ)) := by logtwo_quiet
  calc
    _ ≤ (H : ℝ) * lcmConstant * ∑ i, (truncationOrders w F i : ℝ) / (w.w i : ℝ) :=
      denominatorBudget_le w H hH _
    _ ≤ (H : ℝ) * lcmConstant * ((F : ℝ) * m / (w.v0 : ℝ) + ∑ i, 1 / (w.w i : ℝ)) :=
      mul_le_mul_of_nonneg_left (sum_truncation_div_le w F hF)
        (mul_nonneg (by logtwo_quiet exact_mod_cast hH) lcmConstant_pos.le)
    _ = _ := by logtwo_quiet ring

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
    (ceilLogWeight q : ℝ) - 1 ≤ Real.log (q : ℝ) := by logtwo_quiet
  simp only [ceilLogWeight, Rat.cast_natCast]
  exact ⟨Nat.le_ceil _, by logtwo_quiet linarith [Nat.ceil_lt_add_one (Real.log_natCast_nonneg q)]⟩

def rowWeight {m : ℕ} (w : Weights m) (r : Row m) : ℝ :=
  ∑ i, (w.w i : ℝ) * (r.beta i : ℝ)

theorem rowWeight_lt {m : ℕ} (w : Weights m) (H : ℚ) (r : Row m)
    (hr : AdmissibleRow w H r) : rowWeight w r < (w.theta : ℝ) * (H : ℝ) := by logtwo_quiet
  have hz : (0 : ℚ) ≤ w.v0 * r.s := mul_nonneg w.v0_pos.le (Nat.cast_nonneg _)
  have hh : (∑ i, w.w i * r.beta i) / w.theta < H := by logtwo_quiet
    have := hr.2
    linarith
  have hh' := (div_lt_iff₀ w.theta_pos).mp hh
  simpa only [rowWeight, Rat.cast_sum, Rat.cast_mul, Rat.cast_natCast, mul_comm] using
    (show ((∑ i, w.w i * r.beta i : ℚ) : ℝ) < ((H * w.theta : ℚ) : ℝ) by logtwo_quiet exact_mod_cast hh')

theorem columnQCost_le_height {m : ℕ} (w : Weights m) (H : ℚ) (q : Fin m → ℕ)
    (hlog : ∀ i, Real.log (q i : ℝ) ≤ (w.w i : ℝ))
    (c : Column m) (hc : AdmissibleColumn w H c) : columnQCost q c ≤ (H : ℝ) := by logtwo_quiet
  have hh : (∑ i, w.w i * c.alpha i) ≤ H := by logtwo_quiet
    have hz : (0 : ℚ) ≤ w.w0 * c.h := mul_nonneg w.w0_pos.le (Nat.cast_nonneg _)
    dsimp [AdmissibleColumn] at hc
    linarith
  calc
    _ ≤ ∑ i, (c.alpha i : ℝ) * (w.w i : ℝ) :=
      Finset.sum_le_sum (fun i _ => mul_le_mul_of_nonneg_left (hlog i) (Nat.cast_nonneg _))
    _ ≤ _ := by logtwo_quiet
      simpa only [Rat.cast_sum, Rat.cast_mul, Rat.cast_natCast, mul_comm] using
        (show ((∑ i, w.w i * c.alpha i : ℚ) : ℝ) ≤ (H : ℝ) by logtwo_quiet exact_mod_cast hh)

theorem rowLogSaving_lower {m : ℕ} (w : Weights m) (H : ℚ) (q : Fin m → ℕ)
    (hlog : ∀ i, (w.w i : ℝ) - 1 ≤ Real.log (q i : ℝ))
    (wmin : ℝ) (hmin : 0 < wmin) (hweights : ∀ i, wmin ≤ (w.w i : ℝ))
    (r : Row m) (hr : AdmissibleRow w H r) :
    rowWeight w r - (w.theta : ℝ) * (H : ℝ) / wmin ≤ rowLogSaving q r := by logtwo_quiet
  have hcount : wmin * ∑ i, (r.beta i : ℝ) ≤ rowWeight w r := by logtwo_quiet
    rw [Finset.mul_sum]
    exact Finset.sum_le_sum (fun i _ => mul_le_mul_of_nonneg_right (hweights i) (Nat.cast_nonneg _))
  have hcount' : (∑ i, (r.beta i : ℝ)) ≤ (w.theta : ℝ) * (H : ℝ) / wmin := by logtwo_quiet
    apply (le_div_iff₀ hmin).mpr
    rw [mul_comm]
    exact hcount.trans (rowWeight_lt w H r hr).le
  have hsave : rowWeight w r - (∑ i, (r.beta i : ℝ)) ≤ rowLogSaving q r := by logtwo_quiet
    calc
      _ = ∑ i, (r.beta i : ℝ) * ((w.w i : ℝ) - 1) := by logtwo_quiet
        simp [rowWeight, mul_sub, Finset.sum_sub_distrib, mul_comm]
      _ ≤ _ := Finset.sum_le_sum (fun i _ =>
        mul_le_mul_of_nonneg_left (hlog i) (Nat.cast_nonneg _))
  linarith

theorem fullRowMinor_size_pos {m : ℕ} {w : Weights m} {H : ℚ}
    {r : Fin m → ℚ} {T : Fin m → ℕ} (hK : 0 < w.K) (hH : 0 < H)
    (minor : FullRowMinor w H r T) : 0 < minor.size := by logtwo_quiet
  have hrow : AdmissibleRow w H (valueRow m 0) := by logtwo_quiet
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
    0 ≤ averageRowWeight minor ∧ averageRowWeight minor < (w.theta : ℝ) := by logtwo_quiet
  have hsize := fullRowMinor_size_pos hK hH minor
  have hM : (0 : ℝ) < minor.size := by logtwo_quiet exact_mod_cast hsize
  have hH' : (0 : ℝ) < H := by logtwo_quiet exact_mod_cast hH
  constructor
  · apply div_nonneg _ (mul_pos hM hH').le
    apply Finset.sum_nonneg
    intro i _
    apply Finset.sum_nonneg
    intro k _
    exact mul_nonneg (by logtwo_quiet exact_mod_cast (w.w_pos k).le) (Nat.cast_nonneg _)
  · apply (div_lt_iff₀ (mul_pos hM hH')).mpr
    calc
      _ < ∑ _i : Fin minor.size, (w.theta : ℝ) * (H : ℝ) := by logtwo_quiet
        apply Finset.sum_lt_sum
        · intro i _; exact (rowWeight_lt w H _ (minor.row_valid i)).le
        · exact ⟨⟨0, hsize⟩, Finset.mem_univ _, rowWeight_lt w H _ (minor.row_valid _)⟩
      _ = _ := by logtwo_quiet simp; ring

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
      Real.log |(minor.matrix.det : ℝ)| / ((minor.size : ℝ) * (H : ℝ)) := by logtwo_quiet
  have hM : (0 : ℝ) < minor.size := by logtwo_quiet exact_mod_cast fullRowMinor_size_pos hK hH minor
  have hH' : (0 : ℝ) < H := by logtwo_quiet exact_mod_cast hH
  have hs : (∑ i, rowWeight w (minor.rows i)) -
      (minor.size : ℝ) * ((w.theta : ℝ) * (H : ℝ) / wmin) ≤
      ∑ i, rowLogSaving q (minor.rows i) := by logtwo_quiet
    calc
      _ = ∑ i, (rowWeight w (minor.rows i) - (w.theta : ℝ) * (H : ℝ) / wmin) := by logtwo_quiet
        simp [Finset.sum_sub_distrib]
      _ ≤ _ := Finset.sum_le_sum (fun i _ =>
        rowLogSaving_lower w H q hlog' wmin hmin hweights _ (minor.row_valid i))
  have hc : (∑ j, columnQCost q (minor.columns j)) ≤ (minor.size : ℝ) * (H : ℝ) := by logtwo_quiet
    calc
      _ ≤ ∑ j : Fin minor.size, (H : ℝ) := Finset.sum_le_sum
        (fun j _ => columnQCost_le_height w H q hlog _ (minor.column_valid j))
      _ = _ := by logtwo_quiet simp
  have hd := mul_le_mul_of_nonneg_left
    (truncation_denominatorBudget_le w H F hH.le hF) hM.le
  have hb := fullRowMinor_uniform_log_bound p q (truncationOrders w F) hq minor
  apply (le_div_iff₀ (mul_pos hM hH')).mpr
  dsimp [averageRowWeight, arithmeticError]
  rw [sub_mul, neg_mul, sub_mul, one_mul, div_mul_cancel₀ _ (mul_pos hM hH').ne']
  have halg : (minor.size : ℝ) * ((w.theta : ℝ) * (H : ℝ) / wmin) =
      ((w.theta : ℝ) / wmin) * ((minor.size : ℝ) * (H : ℝ)) := by logtwo_quiet ring
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
      Real.log |(minor.matrix.det : ℝ)| / ((minor.size : ℝ) * (H : ℝ)) := by logtwo_quiet
  apply fullRowMinor_normalized_arithmetic_bound p q (fun i => by logtwo_quiet have := hq i; omega)
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

theorem ceilLogWeight_pos {q : ℕ} (hq : 2 ≤ q) : 0 < ceilLogWeight q := by logtwo_quiet
  have hlog : 0 < Real.log (q : ℝ) :=
    Real.log_pos (by logtwo_quiet exact_mod_cast (show 1 < q by logtwo_quiet omega))
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
      (lcmConstant * m + (w.theta : ℝ)) / W := by logtwo_quiet
  have hs : (∑ i, 1 / (w.w i : ℝ)) ≤ (m : ℝ) / W := by logtwo_quiet
    calc
      _ ≤ ∑ _i : Fin m, (1 : ℝ) / W := Finset.sum_le_sum
        (fun i _ => one_div_le_one_div_of_le hW (hw i))
      _ = _ := by logtwo_quiet simp [div_eq_mul_inv]
  have hh := mul_le_mul_of_nonneg_left hs lcmConstant_pos.le
  unfold arithmeticError
  calc
    _ ≤ lcmConstant * (F : ℝ) * m / (w.v0 : ℝ) +
        lcmConstant * ((m : ℝ) / W) + (w.theta : ℝ) / W := by logtwo_quiet linarith
    _ = _ := by logtwo_quiet ring

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
    monomialWeight w (d + e) = monomialWeight w d + monomialWeight w e := by logtwo_quiet
  simp [monomialWeight, Finsupp.add_apply, Nat.cast_add, add_mul, Finset.sum_add_distrib]

theorem monomialWeight_single {m : ℕ} (w : Fin (m + 1) → ℝ)
    (i : Fin (m + 1)) : monomialWeight w (Finsupp.single i 1) = w i := by logtwo_quiet
  classical
  simp [monomialWeight, Finsupp.single_apply]

theorem HasWeightedDegreeLE.zero {m : ℕ} (w : Fin (m + 1) → ℝ) (N : ℝ) :
    HasWeightedDegreeLE w N (0 : MvPolynomial (Fin (m + 1)) ℂ) := by logtwo_quiet
  simp [HasWeightedDegreeLE]

theorem HasWeightedDegreeLE.mono {m : ℕ} {w : Fin (m + 1) → ℝ} {N M : ℝ}
    {p : MvPolynomial (Fin (m + 1)) ℂ} (hp : HasWeightedDegreeLE w N p)
    (hNM : N ≤ M) : HasWeightedDegreeLE w M p :=
  fun d hd => (hp d hd).trans hNM

theorem HasWeightedDegreeLE.add {m : ℕ} {w : Fin (m + 1) → ℝ} {N : ℝ}
    {p q : MvPolynomial (Fin (m + 1)) ℂ}
    (hp : HasWeightedDegreeLE w N p) (hq : HasWeightedDegreeLE w N q) :
    HasWeightedDegreeLE w N (p + q) := by logtwo_quiet
  intro d hd
  rcases Finset.mem_union.mp (MvPolynomial.support_add hd) with hd | hd
  · exact hp d hd
  · exact hq d hd

theorem HasWeightedDegreeLE.sum {m : ℕ} {α : Type*} {w : Fin (m + 1) → ℝ}
    {N : ℝ} (s : Finset α) (p : α → MvPolynomial (Fin (m + 1)) ℂ)
    (hp : ∀ a ∈ s, HasWeightedDegreeLE w N (p a)) :
    HasWeightedDegreeLE w N (∑ a ∈ s, p a) := by logtwo_quiet
  classical
  induction s using Finset.induction_on with
  | empty => simpa using HasWeightedDegreeLE.zero w N
  | @insert a s ha ih =>
      rw [Finset.sum_insert ha]
      exact (hp a (Finset.mem_insert_self a s)).add
        (ih (fun b hb => hp b (Finset.mem_insert_of_mem hb)))

theorem pderiv_support_shift {m : ℕ} (i : Fin (m + 1))
    (p : MvPolynomial (Fin (m + 1)) ℂ) (d : Fin (m + 1) →₀ ℕ)
    (hd : d ∈ (MvPolynomial.pderiv i p).support) : d + Finsupp.single i 1 ∈ p.support := by logtwo_quiet
  apply MvPolynomial.mem_support_iff.mpr
  intro hz
  have hcoeff := MvPolynomial.mem_support_iff.mp hd
  apply hcoeff
  rw [MvPolynomial.coeff_pderiv, hz, zero_mul]

theorem HasWeightedDegreeLE.pderiv {m : ℕ} {w : Fin (m + 1) → ℝ} {N : ℝ}
    {p : MvPolynomial (Fin (m + 1)) ℂ} (hp : HasWeightedDegreeLE w N p)
    (i : Fin (m + 1)) : HasWeightedDegreeLE w (N - w i) (MvPolynomial.pderiv i p) := by logtwo_quiet
  intro d hd
  apply (le_sub_iff_add_le).mpr
  have h := hp (d + Finsupp.single i 1) (pderiv_support_shift i p d hd)
  simpa only [monomialWeight_add, monomialWeight_single] using h

theorem HasWeightedDegreeLE.X_mul {m : ℕ} {w : Fin (m + 1) → ℝ} {N : ℝ}
    {p : MvPolynomial (Fin (m + 1)) ℂ} (hp : HasWeightedDegreeLE w N p)
    (i : Fin (m + 1)) : HasWeightedDegreeLE w (N + w i) (MvPolynomial.X i * p) := by logtwo_quiet
  intro d hd
  have hsupp := MvPolynomial.support_X_mul i p
  rw [hsupp] at hd
  obtain ⟨e, he, hed⟩ := Finset.mem_map.mp hd
  have heq : Finsupp.single i 1 + e = d := hed
  rw [← heq, monomialWeight_add, monomialWeight_single, add_comm (w i)]
  exact add_le_add (hp e he) (le_refl (w i))

theorem HasWeightedDegreeLE.X_mul_pderiv {m : ℕ} {w : Fin (m + 1) → ℝ} {N : ℝ}
    {p : MvPolynomial (Fin (m + 1)) ℂ} (hp : HasWeightedDegreeLE w N p)
    (i : Fin (m + 1)) : HasWeightedDegreeLE w N (MvPolynomial.X i * MvPolynomial.pderiv i p) := by logtwo_quiet
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
    (p : FramePolynomial m) : (∑ a ∈ s, D a) p = ∑ a ∈ s, D a p := by logtwo_quiet
  classical
  induction s using Finset.induction_on with
  | empty => simp only [Finset.sum_empty, Derivation.zero_apply]
  | @insert a s ha ih =>
      rw [Finset.sum_insert ha, Finset.sum_insert ha, Derivation.add_apply, ih]

@[simp] theorem logarithmicDerivation_apply (m : ℕ) (p : FramePolynomial m) :
    logarithmicDerivation m p =
      MvPolynomial.X (0 : Fin (m + 1)) * MvPolynomial.pderiv 0 p +
        ∑ i : Fin m, MvPolynomial.pderiv i.succ p := by logtwo_quiet
  simp only [logarithmicDerivation, Derivation.add_apply, Derivation.smul_apply,
    derivation_finset_sum_apply, smul_eq_mul]

@[simp] theorem polynomialFrame_zero (m : ℕ) :
    polynomialFrame m 0 = logarithmicDerivation m := by logtwo_quiet
  simp only [polynomialFrame, ite_true]

@[simp] theorem polynomialFrame_pos (m : ℕ) (i : Fin (m + 1)) (hi : i ≠ 0) :
    polynomialFrame m i = MvPolynomial.pderiv i := by logtwo_quiet
  simp only [polynomialFrame, ite_eq_right hi]

@[simp] theorem polynomialFrame_add (m : ℕ) (i : Fin (m + 1))
    (p q : FramePolynomial m) :
    polynomialFrame m i (p + q) = polynomialFrame m i p + polynomialFrame m i q :=
  map_add _ _ _

@[simp] theorem polynomialFrame_C (m : ℕ) (i : Fin (m + 1)) (a : ℂ) :
    polynomialFrame m i (MvPolynomial.C a) = 0 := by logtwo_quiet
  rw [MvPolynomial.C_eq_algebraMap]
  exact Derivation.map_algebraMap _ a

theorem HasWeightedDegreeLE.logarithmicDerivation {m : ℕ}
    {w : Fin (m + 1) → ℝ} {N : ℝ} {p : FramePolynomial m}
    (hp : HasWeightedDegreeLE w N p) (hw : ∀ i, 0 ≤ w i) :
    HasWeightedDegreeLE w N (PiExponentApprox.logarithmicDerivation m p) := by logtwo_quiet
  rw [logarithmicDerivation_apply]
  apply (hp.X_mul_pderiv 0).add
  exact HasWeightedDegreeLE.sum Finset.univ _
    (fun i _ => hp.pderiv_preserves i.succ (hw i.succ))

theorem HasWeightedDegreeLE.polynomialFrame {m : ℕ}
    {w : Fin (m + 1) → ℝ} {N : ℝ} {p : FramePolynomial m}
    (hp : HasWeightedDegreeLE w N p) (hw : ∀ i, 0 ≤ w i) (i : Fin (m + 1)) :
    HasWeightedDegreeLE w N (PiExponentApprox.polynomialFrame m i p) := by logtwo_quiet
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
    HasWeightedDegreeLE w N (PiExponentApprox.polynomialFrameWord m word p) := by logtwo_quiet
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

@[simp] theorem scaleY_C {m : ℕ} (y a : ℂ) : scaleY (m := m) y (C a) = C a := by logtwo_quiet
  simp [scaleY]

@[simp] theorem scaleY_X_zero {m : ℕ} (y : ℂ) :
    scaleY y (X (0 : Fin (m+1))) = C y * X 0 := by logtwo_quiet simp [scaleY]

@[simp] theorem scaleY_X_succ {m : ℕ} (y : ℂ) (i : Fin m) :
    scaleY y (X i.succ) = X i.succ := by logtwo_quiet simp [scaleY]

theorem scaleY_polynomialFrame_X {m : ℕ} (y : ℂ) (i j : Fin (m+1)) :
    scaleY y (polynomialFrame m i (X j)) = polynomialFrame m i (scaleY y (X j)) := by logtwo_quiet
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
  by logtwo_quiet
    induction F using MvPolynomial.induction_on with
    | C a => simp [polynomialFrame]
    | add F G hF hG => simp only [map_add, hF, hG]
    | mul_X F j hF =>
      simp only [Derivation.leibniz, smul_eq_mul, map_add, map_mul, hF,
        scaleY_polynomialFrame_X y i j]

theorem scaleY_polynomialFrameWord {m : ℕ} (y : ℂ) (word : List (Fin (m+1)))
    (F : FramePolynomial m) :
    scaleY y (polynomialFrameWord m word F) = polynomialFrameWord m word (scaleY y F) := by logtwo_quiet
  induction word with
  | nil => rfl
  | cons i word ih => rw [polynomialFrameWord_cons, scaleY_polynomialFrame, ih]; rfl

variable {E : Type*} [Field E] [Algebra ℂ E]

def normalizeY {m : ℕ} (y : ℂ) (z : Fin (m+1) → E) : Fin (m+1) → E :=
  Fin.cases (z 0 / algebraMap ℂ E y) (fun i => z i.succ)

/-- The polynomial scaling and the point normalization cancel exactly. -/
theorem aeval_normalizeY_scaleY {m : ℕ} (y : ℂ) (hy : y ≠ 0)
    (z : Fin (m+1) → E) (F : FramePolynomial m) :
    MvPolynomial.aeval (normalizeY y z) (scaleY y F) = MvPolynomial.aeval z F := by logtwo_quiet
  have hy' : algebraMap ℂ E y ≠ 0 := (map_ne_zero_iff _ (algebraMap ℂ E).injective).mpr hy
  have he : (MvPolynomial.aeval (normalizeY y z)).comp (scaleY y) = MvPolynomial.aeval z := by logtwo_quiet
    apply MvPolynomial.algHom_ext
    intro i
    cases i using Fin.cases with
    | zero => simp [normalizeY, hy', mul_div_cancel₀]
    | succ i => simp [normalizeY]
  exact DFunLike.congr_fun he F

theorem aeval_normalizeY_scaled_word {m : ℕ} (y : ℂ) (hy : y ≠ 0)
    (z : Fin (m+1) → E) (word : List (Fin (m+1))) (F : FramePolynomial m) :
    MvPolynomial.aeval (normalizeY y z) (polynomialFrameWord m word (scaleY y F)) =
      MvPolynomial.aeval z (polynomialFrameWord m word F) := by logtwo_quiet
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
  zero_mem' := by logtwo_quiet simp
  add_mem' hf hg := (le_min hf hg).trans (min_weightedOrder_le_add w)
  smul_mem' a f hf := by logtwo_quiet
    change (N : ℕ∞) ≤ weightedOrder w (a * f)
    exact hf.trans (le_add_self.trans (le_weightedOrder_mul w))

@[simp] theorem mem_weightedIdeal (w : σ → ℕ) (N : ℕ)
    (f : MvPowerSeries σ R) :
    f ∈ weightedIdeal w N ↔ (N : ℕ∞) ≤ f.weightedOrder w := Iff.rfl

theorem mem_weightedIdeal_iff (w : σ → ℕ) (N : ℕ)
    (f : MvPowerSeries σ R) :
    f ∈ weightedIdeal w N ↔ ∀ d, Finsupp.weight w d < N → coeff d f = 0 := by logtwo_quiet
  constructor
  · intro hf d hd
    have hd' : (Finsupp.weight w d : ℕ∞) < (N : ℕ∞) := by logtwo_quiet exact_mod_cast hd
    exact coeff_eq_zero_of_lt_weightedOrder w (hd'.trans_le hf)
  · intro hf
    exact nat_le_weightedOrder w hf

theorem weightedIdeal_mul_le (w : σ → ℕ) (M N : ℕ) :
    (weightedIdeal w M : Ideal (MvPowerSeries σ R)) * weightedIdeal w N ≤
      weightedIdeal w (M + N) := by logtwo_quiet
  apply Ideal.mul_le.mpr
  intro f hf g hg
  change ((M + N : ℕ) : ℕ∞) ≤ weightedOrder w (f * g)
  rw [Nat.cast_add]
  exact (add_le_add hf hg).trans (le_weightedOrder_mul w)

theorem ideal_pow_le_weightedIdeal (w : σ → ℕ) (I : Ideal (MvPowerSeries σ R))
    (R₀ : ℕ) (hI : I ≤ weightedIdeal w R₀) (n : ℕ) :
    I ^ n ≤ weightedIdeal w (n * R₀) := by logtwo_quiet
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
    (d : σ →₀ ℕ) : 0 ≤ Finsupp.weight v d := by logtwo_quiet
  rw [Finsupp.weight_apply, Finsupp.sum]
  exact Finset.sum_nonneg (fun i _ => nsmul_nonneg (hv i) (d i))

def rationalWeightedIdeal (v : σ → ℚ) (hv : ∀ i, 0 ≤ v i) (H : ℚ) :
    Ideal (MvPowerSeries σ R) where
  carrier := {f | ∀ d, Finsupp.weight v d < H → coeff d f = 0}
  zero_mem' := by logtwo_quiet simp
  add_mem' hf hg := by logtwo_quiet
    intro d hd
    rw [map_add, hf d hd, hg d hd, add_zero]
  smul_mem' a f hf := by logtwo_quiet
    classical
    intro d hd
    change coeff d (a * f) = 0
    rw [coeff_mul]
    apply Finset.sum_eq_zero
    intro ij hij
    have he : ij.1 + ij.2 = d := Finset.HasAntidiagonal.mem_antidiagonal.mp hij
    have hw : Finsupp.weight v ij.2 ≤ Finsupp.weight v d := by logtwo_quiet
      rw [← he, map_add]
      exact le_add_of_nonneg_left (rational_weight_nonneg v hv ij.1)
    rw [hf ij.2 (hw.trans_lt hd), mul_zero]

@[simp] theorem mem_rationalWeightedIdeal (v : σ → ℚ) (hv : ∀ i, 0 ≤ v i)
    (H : ℚ) (f : MvPowerSeries σ R) :
    f ∈ rationalWeightedIdeal v hv H ↔
      ∀ d, Finsupp.weight v d < H → coeff d f = 0 := Iff.rfl

theorem rationalWeightedIdeal_mul_le (v : σ → ℚ) (hv : ∀ i, 0 ≤ v i) (H K : ℚ) :
    (rationalWeightedIdeal v hv H : Ideal (MvPowerSeries σ R)) *
      rationalWeightedIdeal v hv K ≤ rationalWeightedIdeal v hv (H + K) := by logtwo_quiet
  classical
  apply Ideal.mul_le.mpr
  intro f hf g hg d hd
  rw [coeff_mul]
  apply Finset.sum_eq_zero
  intro ij hij
  have he : ij.1 + ij.2 = d := Finset.HasAntidiagonal.mem_antidiagonal.mp hij
  by_cases hfirst : Finsupp.weight v ij.1 < H
  · rw [hf ij.1 hfirst, zero_mul]
  · have hsecond : Finsupp.weight v ij.2 < K := by logtwo_quiet
      apply lt_of_not_ge
      intro hsecond
      have hsum := add_le_add (le_of_not_gt hfirst) hsecond
      rw [← map_add, he] at hsum
      exact (not_le_of_gt hd) hsum
    rw [hg ij.2 hsecond, mul_zero]

theorem ideal_pow_le_rationalWeightedIdeal (v : σ → ℚ) (hv : ∀ i, 0 ≤ v i)
    (I : Ideal (MvPowerSeries σ R)) (H : ℚ)
    (hI : I ≤ rationalWeightedIdeal v hv H) (n : ℕ) :
    I ^ n ≤ rationalWeightedIdeal v hv (n * H) := by logtwo_quiet
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
      rationalWeightedIdeal v hv (n * H) := by logtwo_quiet
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
    pderiv i f ∈ rationalWeightedIdeal v hv (H - v i) := by logtwo_quiet
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
    jetFrame m 0 f = (1 + X 0) * pderiv 0 f := by logtwo_quiet
  simp [jetFrame, Derivation.smul_apply, smul_eq_mul]

@[simp] theorem jetFrame_pos (m : ℕ) (i : Fin (m + 1)) (hi : i ≠ 0)
    (f : MvPowerSeries (Fin (m + 1)) R) : jetFrame m i f = pderiv i f := by logtwo_quiet
  simp [jetFrame, hi]

theorem jetFrame_mem_rationalWeightedIdeal {m : ℕ}
    (v : Fin (m + 1) → ℚ) (hv : ∀ i, 0 ≤ v i)
    (H : ℚ) (f : MvPowerSeries (Fin (m + 1)) R)
    (hf : f ∈ rationalWeightedIdeal v hv H) (i : Fin (m + 1)) :
    jetFrame m i f ∈ rationalWeightedIdeal v hv (H - v i) := by logtwo_quiet
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
    jetFrameWord m word f ∈ rationalWeightedIdeal v hv (H - (word.map v).sum) := by logtwo_quiet
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
    coeff d (liftSeries m f) = if d.tail = 0 then PowerSeries.coeff (d 0) f else 0 := by logtwo_quiet
  have h := coeff_coeff_finSuccEquiv (liftSeries m f) (k := d 0) (x := d.tail)
  rw [Finsupp.cons_tail] at h
  rw [← h]
  simp [liftSeries, PowerSeries.coeff_map, coeff_C]

@[simp] theorem liftSeries_X (m : ℕ) : liftSeries (R := R) m PowerSeries.X = X 0 := by logtwo_quiet
  apply (finSuccEquiv R m).injective
  simp [liftSeries]

@[simp] theorem liftSeries_C (m : ℕ) (r : R) :
    liftSeries m (PowerSeries.C r) = C r := by logtwo_quiet
  apply (finSuccEquiv R m).injective
  simp [liftSeries]

theorem pderiv_zero_liftSeries (m : ℕ) (f : PowerSeries R) :
    pderiv 0 (liftSeries m f) = liftSeries m (PowerSeries.derivative f) := by logtwo_quiet
  ext d
  rw [coeff_pderiv, coeff_liftSeries, coeff_liftSeries, PowerSeries.coeff_derivative]
  have ht : (d + Finsupp.single (0 : Fin (m+1)) 1).tail = d.tail := by logtwo_quiet
    ext i
    simp [Finsupp.tail_apply]
  simp only [ht, Finsupp.add_apply, Finsupp.single_eq_same]
  split_ifs <;> simp_all

theorem pderiv_succ_liftSeries (m : ℕ) (i : Fin m) (f : PowerSeries R) :
    pderiv i.succ (liftSeries m f) = 0 := by logtwo_quiet
  ext d
  rw [coeff_pderiv, coeff_liftSeries, coeff_zero]
  have ht : (d + Finsupp.single i.succ 1).tail ≠ 0 := by logtwo_quiet
    intro h
    have hi := DFunLike.congr_fun h i
    simp [Finsupp.tail_apply] at hi
  simp [ht]

def formalLog (m : ℕ) : MvPowerSeries (Fin (m+1)) ℂ :=
  liftSeries m (PowerSeries.log ℂ)

@[simp] theorem pderiv_succ_formalLog (m : ℕ) (i : Fin m) :
    pderiv i.succ (formalLog m) = 0 := pderiv_succ_liftSeries m i _

theorem one_add_X_mul_pderiv_formalLog (m : ℕ) :
    (1 + X 0) * pderiv 0 (formalLog m) = 1 := by logtwo_quiet
  have h := congrArg (liftSeries m) (PowerSeries.derivative_log_mul_one_add_X (A := ℂ))
  rw [map_mul, map_add, map_one, liftSeries_X] at h
  rw [formalLog, pderiv_zero_liftSeries, mul_comm]
  exact h

def formalJet {m : ℕ} (c : Fin m → ℂ) :
    PiExponentApprox.FramePolynomial m →ₐ[ℂ] MvPowerSeries (Fin (m+1)) ℂ :=
  MvPolynomial.aeval (Fin.cases (1 + X 0)
    (fun i => C (c i) + X i.succ + formalLog m))

@[simp] theorem formalJet_Y {m : ℕ} (c : Fin m → ℂ) :
    formalJet c (MvPolynomial.X (0 : Fin (m+1))) = 1 + X 0 := by logtwo_quiet
  simp [formalJet]

@[simp] theorem formalJet_X {m : ℕ} (c : Fin m → ℂ) (i : Fin m) :
    formalJet c (MvPolynomial.X i.succ) = C (c i) + X i.succ + formalLog m := by logtwo_quiet
  simp [formalJet]

theorem derivation_map_of_X {σ S : Type*} [CommRing S] [Algebra R S]
    (φ : MvPolynomial σ R →ₐ[R] S)
    (D : Derivation R (MvPolynomial σ R) (MvPolynomial σ R))
    (δ : Derivation R S S)
    (hX : ∀ i, φ (D (MvPolynomial.X i)) = δ (φ (MvPolynomial.X i)))
    (p : MvPolynomial σ R) : φ (D p) = δ (φ p) := by logtwo_quiet
  induction p using MvPolynomial.induction_on with
  | C a => simp
  | add p q hp hq => simp only [map_add, hp, hq]
  | mul_X p i hp =>
    simp only [Derivation.leibniz, smul_eq_mul, map_add, map_mul, hp, hX]

theorem formalJet_frame_X {m : ℕ} (c : Fin m → ℂ) (i j : Fin (m+1)) :
    formalJet c (PiExponentApprox.polynomialFrame m i (MvPolynomial.X j)) =
      jetFrame m i (formalJet c (MvPolynomial.X j)) := by logtwo_quiet
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
      jetFrameWord m word (formalJet c p) := by logtwo_quiet
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
      JetGeometry.rationalWeightedIdeal v hv (H - (word.map v).sum) := by logtwo_quiet
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
    formalJetAt y c (X (0 : Fin (m+1))) = MvPowerSeries.C y * (1 + MvPowerSeries.X 0) := by logtwo_quiet
  simp [formalJetAt, MvPowerSeries.algebraMap_apply]

@[simp] theorem formalJetAt_X {m : ℕ} (y : ℂ) (c : Fin m → ℂ) (i : Fin m) :
    formalJetAt y c (X i.succ) =
      MvPowerSeries.C (c i) + MvPowerSeries.X i.succ + formalLog m := by logtwo_quiet
  simp [formalJetAt]

def frameMonomial {m : ℕ} (h : ℕ) (α : Fin m → ℕ) : FramePolynomial m :=
  X 0 ^ h * ∏ i, X i.succ ^ α i

end
end LogTwo.Geometry
end Source0024

run_cmd Lean.logInfo "LogTwo progress: reached module 25/885"

-- Source: OAI/NumberTheory/PiExponent/Geometry/CurveParameterFinite.lean
section Source0025
/-
Modification notice for the LogTwo project.
Derived from openai/math (Apache-2.0), revision adc7f1241b42e322a6451854ab7e4b4c146bf78a.
Original source: lean/OAI/NumberTheory/PiExponent/Geometry/CurveParameterFinite.lean
Changes: Convert module/import declarations to the Lean 4.34 public module format.
See ../THIRD_PARTY_NOTICES.txt for provenance and the recorded changes.
-/

namespace OAI

namespace PiExponent.CurveParameterFinite

theorem finiteDimensional_adjoin_singleton
    (F E : Type*) [Field F] [Field E] [Algebra F E]
    [Algebra.EssFiniteType F E] (htrdeg : Algebra.trdeg F E ≤ 1)
    {g : E} (hg : Transcendental F g) :
    FiniteDimensional (IntermediateField.adjoin F {g}) E := by logtwo_quiet
  have hind : AlgebraicIndependent F (fun z : ({g} : Set E) => (z : E)) := by logtwo_quiet
    rw [algebraicIndependent_singleton_iff ⟨g, rfl⟩]
    exact hg
  have hb := hind.isTranscendenceBasis_of_trdeg_le_of_finite (by logtwo_quiet simpa using htrdeg)
  have hrange : Set.range (fun z : ({g} : Set E) => (z : E)) = {g} :=
    Subtype.range_coe
  let : Algebra.IsAlgebraic (IntermediateField.adjoin F {g}) E := by logtwo_quiet
    have ha := hb.isAlgebraic_field
    rw [hrange] at ha
    exact ha
  let : Algebra.EssFiniteType (IntermediateField.adjoin F {g}) E :=
    Algebra.EssFiniteType.of_comp F (IntermediateField.adjoin F {g}) E
  exact Algebra.finite_of_essFiniteType_of_isAlgebraic

theorem finite_over_every_parameter
    (F E : Type*) [Field F] [Field E] [Algebra F E]
    [Algebra.EssFiniteType F E] (htrdeg : Algebra.trdeg F E = 1) :
    ∀ g : E, Transcendental F g →
      FiniteDimensional (IntermediateField.adjoin F {g}) E :=
  fun _ hg => finiteDimensional_adjoin_singleton F E htrdeg.le hg

end PiExponent.CurveParameterFinite

end OAI
end Source0025

-- Source: OAI/NumberTheory/PiExponent/Geometry/WeightedCurveDegree.lean
section Source0026
-- Modified in this edition: unused plain lemmas removed; see reduction.json.
/-
Modification notice for the LogTwo project.
Derived from openai/math (Apache-2.0), revision adc7f1241b42e322a6451854ab7e4b4c146bf78a.
Original source: lean/OAI/NumberTheory/PiExponent/Geometry/WeightedCurveDegree.lean
Changes: Convert module/import declarations to the Lean 4.34 public module format.
See ../THIRD_PARTY_NOTICES.txt for provenance and the recorded changes.
-/

namespace OAI

open scoped BigOperators

namespace PiExponent.WeightedCurveDegree

noncomputable def integerOrder {K : Type*} [Field K]
    (v : AddValuation K (WithTop ℤ)) (x : Kˣ) : ℤ :=
  (v (x : K)).untop ((AddValuation.top_iff v).not.mpr x.ne_zero)

@[simp] theorem coe_integerOrder {K : Type*} [Field K]
    (v : AddValuation K (WithTop ℤ)) (x : Kˣ) :
    (integerOrder v x : WithTop ℤ) = v (x : K) := WithTop.coe_untop _ _

@[simp] theorem integerOrder_one {K : Type*} [Field K]
    (v : AddValuation K (WithTop ℤ)) : integerOrder v 1 = 0 := by logtwo_quiet
  apply WithTop.coe_injective
  simp

@[simp] theorem integerOrder_mul {K : Type*} [Field K]
    (v : AddValuation K (WithTop ℤ)) (x y : Kˣ) :
    integerOrder v (x * y) = integerOrder v x + integerOrder v y := by logtwo_quiet
  apply WithTop.coe_injective
  simp

@[simp] theorem integerOrder_pow {K : Type*} [Field K]
    (v : AddValuation K (WithTop ℤ)) (x : Kˣ) (n : ℕ) :
    integerOrder v (x ^ n) = n * integerOrder v x := by logtwo_quiet
  induction n with
  | zero => simp
  | succ n ih => rw [pow_succ, integerOrder_mul, ih]; push_cast; ring

@[simp] theorem integerOrder_prod {K ι : Type*} [Field K]
    (v : AddValuation K (WithTop ℤ)) (s : Finset ι) (x : ι → Kˣ) :
    integerOrder v (∏ i ∈ s, x i) = ∑ i ∈ s, integerOrder v (x i) := by logtwo_quiet
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert i s hi ih => simp [hi, ih]

noncomputable def weightedPole {ι : Type*} [Fintype ι]
    (w z : ι → ℚ) : ℚ :=
  (Finset.univ : Finset (Option ι)).sup' Finset.univ_nonempty
    (fun i => i.elim 0 (fun j => -z j / w j))

theorem weightedPole_nonneg {ι : Type*} [Fintype ι] (w z : ι → ℚ) :
    0 ≤ weightedPole w z := by logtwo_quiet
  exact Finset.le_sup' (fun i : Option ι => i.elim 0 (fun j => -z j / w j))
    (Finset.mem_univ (none : Option ι))

theorem div_le_weightedPole {ι : Type*} [Fintype ι] (w z : ι → ℚ) (i : ι) :
    -z i / w i ≤ weightedPole w z := by logtwo_quiet
  exact Finset.le_sup' (fun o : Option ι => o.elim 0 (fun j => -z j / w j))
    (Finset.mem_univ (some i))

theorem monomial_pole_le {ι : Type*} [Fintype ι]
    (w z : ι → ℚ) (hw : ∀ i, 0 < w i) (a : ι → ℕ) {R : ℚ}
    (ha : (∑ i, w i * (a i : ℚ)) ≤ R) :
    -(∑ i, (a i : ℚ) * z i) ≤ R * weightedPole w z := by logtwo_quiet
  have hcoord (i : ι) : -z i ≤ w i * weightedPole w z := by logtwo_quiet
    have h := (div_le_iff₀ (hw i)).mp (div_le_weightedPole w z i)
    simpa [mul_comm] using h
  calc
    _ = ∑ i, (a i : ℚ) * (-z i) := by logtwo_quiet simp [Finset.sum_neg_distrib]
    _ ≤ ∑ i, (a i : ℚ) * (w i * weightedPole w z) := by logtwo_quiet
      apply Finset.sum_le_sum
      intro i _
      exact mul_le_mul_of_nonneg_left (hcoord i) (Nat.cast_nonneg _)
    _ = (∑ i, w i * (a i : ℚ)) * weightedPole w z := by logtwo_quiet
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro i _
      ring
    _ ≤ R * weightedPole w z :=
      mul_le_mul_of_nonneg_right ha (weightedPole_nonneg w z)

noncomputable def monomialPoleCoefficient
    {K ι : Type*} [Field K] [Fintype ι]
    (v : AddValuation K (WithTop ℤ)) (x : ι → Kˣ)
    (monomials : Finset (ι → ℕ)) (hzero : 0 ∈ monomials) : ℤ :=
  monomials.sup' ⟨0, hzero⟩ (fun a => -integerOrder v (∏ i, x i ^ a i))

theorem monomialPoleCoefficient_eq_zero
    {K ι : Type*} [Field K] [Fintype ι]
    (v : AddValuation K (WithTop ℤ)) (x : ι → Kˣ)
    (monomials : Finset (ι → ℕ)) (hzero : 0 ∈ monomials)
    (hx : ∀ i, integerOrder v (x i) = 0) :
    monomialPoleCoefficient v x monomials hzero = 0 := by logtwo_quiet
  unfold monomialPoleCoefficient
  simp only [integerOrder_prod, integerOrder_pow, hx, mul_zero, Finset.sum_const_zero, neg_zero]
  exact Finset.sup'_const _ _

noncomputable def monomialPoleDivisor
    {K ι P : Type*} [Field K] [Fintype ι]
    (v : P → AddValuation K (WithTop ℤ)) (x : ι → Kˣ)
    (monomials : Finset (ι → ℕ)) (hzero : 0 ∈ monomials)
    (support : Finset P)
    (hsupport : ∀ p ∉ support, ∀ i, integerOrder (v p) (x i) = 0) : P →₀ ℤ :=
  Finsupp.onFinset support (fun p => monomialPoleCoefficient (v p) x monomials hzero)
    (by logtwo_quiet
      intro p hp
      by_contra hnot
      exact hp (monomialPoleCoefficient_eq_zero (v p) x monomials hzero (hsupport p hnot)))

@[simp] theorem monomialPoleDivisor_apply
    {K ι P : Type*} [Field K] [Fintype ι]
    (v : P → AddValuation K (WithTop ℤ)) (x : ι → Kˣ)
    (monomials : Finset (ι → ℕ)) (hzero : 0 ∈ monomials)
    (support : Finset P)
    (hsupport : ∀ p ∉ support, ∀ i, integerOrder (v p) (x i) = 0) (p : P) :
    monomialPoleDivisor v x monomials hzero support hsupport p =
      monomialPoleCoefficient (v p) x monomials hzero := by logtwo_quiet
  unfold monomialPoleDivisor
  exact Finsupp.onFinset_apply

@[simp] theorem integerOrder_inv {K : Type*} [Field K]
    (v : AddValuation K (WithTop ℤ)) (x : Kˣ) :
    integerOrder v x⁻¹ = -integerOrder v x := by logtwo_quiet
  apply WithTop.coe_injective
  simp

@[simp] theorem integerOrder_div {K : Type*} [Field K]
    (v : AddValuation K (WithTop ℤ)) (x y : Kˣ) :
    integerOrder v (x / y) = integerOrder v x - integerOrder v y := by logtwo_quiet
  simp [div_eq_mul_inv, sub_eq_add_neg]

theorem mem_valuationSubring_iff_order_nonneg {K : Type*} [Field K]
    (v : AddValuation K (WithTop ℤ)) (x : Kˣ) :
    (x : K) ∈ v.toValuation.valuationSubring ↔ 0 ≤ integerOrder v x := by logtwo_quiet
  change (0 : WithTop ℤ) ≤ v (x : K) ↔ 0 ≤ integerOrder v x
  rw [← coe_integerOrder]
  exact WithTop.coe_le_coe

theorem exists_regular_monomial_chart
    {K ι : Type*} [Field K] [Fintype ι]
    (v : AddValuation K (WithTop ℤ)) (x : ι → Kˣ)
    (monomials : Finset (ι → ℕ)) (hzero : 0 ∈ monomials) :
    ∃ a ∈ monomials,
      integerOrder v (∏ i, x i ^ a i) = -monomialPoleCoefficient v x monomials hzero ∧
      (∀ b ∈ monomials,
        (((∏ i, x i ^ b i) / (∏ i, x i ^ a i) : Kˣ) : K) ∈
          v.toValuation.valuationSubring) ∧
      (((∏ i, x i ^ a i) / (∏ i, x i ^ a i) : Kˣ) : K) = 1 := by logtwo_quiet
  obtain ⟨a, ha, hmax⟩ := Finset.exists_mem_eq_sup' ⟨0, hzero⟩
    (fun a => -integerOrder v (∏ i, x i ^ a i))
  change monomialPoleCoefficient v x monomials hzero = _ at hmax
  refine ⟨a, ha, by logtwo_quiet linarith, ?_, ?_⟩
  · intro b hb
    apply (mem_valuationSubring_iff_order_nonneg v _).mpr
    rw [integerOrder_div]
    have h := Finset.le_sup' (fun a => -integerOrder v (∏ i, x i ^ a i)) hb
    change -integerOrder v (∏ i, x i ^ b i) ≤ monomialPoleCoefficient v x monomials hzero at h
    linarith
  · simp

end PiExponent.WeightedCurveDegree

end OAI
end Source0026

-- Source: OAI/NumberTheory/PiExponent/Jets/IntrinsicLength.lean
section Source0027
/-
Modification notice for the LogTwo project.
Derived from openai/math (Apache-2.0), revision adc7f1241b42e322a6451854ab7e4b4c146bf78a.
Original source: lean/OAI/NumberTheory/PiExponent/Jets/IntrinsicLength.lean
Changes: Convert module/import declarations to the Lean 4.34 public module format.
See ../THIRD_PARTY_NOTICES.txt for provenance and the recorded changes.
-/

namespace OAI

namespace PiExponentJets.W24

variable {K A : Type*} [Field K] [CommRing A] [Algebra K A]

theorem augmentation_surjective (ε : A →+* K)
    (hε : ∀ k : K, ε (algebraMap K A k) = k) : Function.Surjective ε :=
  fun k => ⟨algebraMap K A k, hε k⟩

variable [IsLocalRing A]

theorem simple_annihilator_eq_augmentation_kernel (ε : A →+* K)
    (hε : ∀ k : K, ε (algebraMap K A k) = k)
    {M : Type*} [AddCommGroup M] [Module A M] [IsSimpleModule A M] :
    Module.annihilator A M = RingHom.ker ε := by logtwo_quiet
  have hker : (RingHom.ker ε).IsMaximal :=
    RingHom.ker_isMaximal_of_surjective ε (augmentation_surjective ε hε)
  exact (IsLocalRing.eq_maximalIdeal (IsSimpleModule.annihilator_isMaximal (R := A)
    (M := M))).trans (IsLocalRing.eq_maximalIdeal hker).symm

theorem simple_smul_eq_augmentation_smul (ε : A →+* K)
    (hε : ∀ k : K, ε (algebraMap K A k) = k)
    {M : Type*} [AddCommGroup M] [Module A M] [Module K M]
    [IsScalarTower K A M] [IsSimpleModule A M] (a : A) (x : M) :
    a • x = ε a • x := by logtwo_quiet
  have ha : a - algebraMap K A (ε a) ∈ Module.annihilator A M := by logtwo_quiet
    rw [simple_annihilator_eq_augmentation_kernel ε hε]
    rw [RingHom.mem_ker, map_sub, hε, sub_self]
  have hx := Module.mem_annihilator.mp ha x
  exact sub_eq_zero.mp (by logtwo_quiet simpa only [sub_smul, algebraMap_smul] using hx)

theorem simple_over_coefficient_field (ε : A →+* K)
    (hε : ∀ k : K, ε (algebraMap K A k) = k)
    {M : Type*} [AddCommGroup M] [Module A M] [Module K M]
    [IsScalarTower K A M] [IsSimpleModule A M] : IsSimpleModule K M := by logtwo_quiet
  apply isSimpleModule_iff_toSpanSingleton_surjective.mpr
  refine ⟨IsSimpleModule.nontrivial A M, ?_⟩
  intro x hx y
  obtain ⟨a, ha⟩ := IsSimpleModule.toSpanSingleton_surjective A hx y
  refine ⟨ε a, ?_⟩
  change ε a • x = y
  rw [← simple_smul_eq_augmentation_smul ε hε a x]
  exact ha

theorem length_eq_coefficient_length (ε : A →+* K)
    (hε : ∀ k : K, ε (algebraMap K A k) = k)
    {M : Type*} [AddCommGroup M] [Module A M] (hM : IsFiniteLength A M) :
    ∀ [Module K M] [IsScalarTower K A M], Module.length A M = Module.length K M := by logtwo_quiet
  induction hM with
  | of_subsingleton =>
    intro _ _
    simp only [Module.length_eq_zero]
  | @of_simple_quotient M _ _ N hsimple hN ih =>
    intro _ _
    have : IsSimpleModule K (M ⧸ N) := simple_over_coefficient_field ε hε
    have hexact : Function.Exact N.subtype N.mkQ := by logtwo_quiet
      rw [LinearMap.exact_iff, Submodule.range_subtype, Submodule.ker_mkQ]
    have hA := Module.length_eq_add_of_exact N.subtype N.mkQ
      (Submodule.subtype_injective N) (Submodule.mkQ_surjective N) hexact
    have hK := Module.length_eq_add_of_exact (N.subtype.restrictScalars K)
      (N.mkQ.restrictScalars K) (Submodule.subtype_injective N)
      (Submodule.mkQ_surjective N) hexact
    calc
      Module.length A M = Module.length A N + Module.length A (M ⧸ N) := hA
      _ = Module.length K N + Module.length K (M ⧸ N) := by logtwo_quiet
        rw [ih, Module.length_eq_one A (M ⧸ N), Module.length_eq_one K (M ⧸ N)]
      _ = Module.length K M := hK.symm

theorem module_length_eq_finrank_of_augmentation (ε : A →+* K)
    (hε : ∀ k : K, ε (algebraMap K A k) = k)
    {M : Type*} [AddCommGroup M] [Module A M] [Module K M]
    [IsScalarTower K A M] [Module.Finite K M] :
    Module.length A M = Module.finrank K M := by logtwo_quiet
  have : IsNoetherian A M := isNoetherian_of_tower K inferInstance
  have : IsArtinian A M := isArtinian_of_tower K inferInstance
  have hM : IsFiniteLength A M := isFiniteLength_iff_isNoetherian_isArtinian.mpr
    ⟨inferInstance, inferInstance⟩
  rw [length_eq_coefficient_length ε hε hM, Module.length_eq_finrank]

theorem ring_length_eq_finrank_of_augmentation [Module.Finite K A] (ε : A →+* K)
    (hε : ∀ k : K, ε (algebraMap K A k) = k) :
    Module.length A A = Module.finrank K A :=
  module_length_eq_finrank_of_augmentation ε hε

end PiExponentJets.W24

end OAI
end Source0027

-- Source: OAI/NumberTheory/PiExponent/Geometry/CurveLocalOrder.lean
section Source0028
-- Modified in this edition: unused plain lemmas removed; see reduction.json.
/-
Modification notice for the LogTwo project.
Derived from openai/math (Apache-2.0), revision adc7f1241b42e322a6451854ab7e4b4c146bf78a.
Original source: lean/OAI/NumberTheory/PiExponent/Geometry/CurveLocalOrder.lean
Changes: Convert module/import declarations to the Lean 4.34 public module format.
See ../THIRD_PARTY_NOTICES.txt for provenance and the recorded changes.
-/

namespace OAI

open scoped BigOperators nonZeroDivisors
open IsLocalRing IsDiscreteValuationRing

namespace PiExponent.CurveLocalOrder

theorem length_quotient_span_eq_addVal
    {A : Type*} [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
    {a : A} (ha : a ≠ 0) :
    Module.length A (A ⧸ Ideal.span {a}) = IsDiscreteValuationRing.addVal A a := by logtwo_quiet
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible A
  obtain ⟨n, u, rfl⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible ha hϖ
  rw [IsDiscreteValuationRing.addVal_def' u hϖ]
  rw [Ideal.span_singleton_mul_left_unit u.isUnit,
    ← Ideal.span_singleton_pow, ← hϖ.maximalIdeal_eq]
  exact IsDiscreteValuationRing.length_quotient_pow_maximalIdeal A n

def enatToIntegerOrder : ℕ∞ →+ WithTop ℤ where
  toFun := ENat.map (fun n : ℕ => (n : ℤ))
  map_zero' := by logtwo_quiet simp
  map_add' a b := ENat.map_add (Nat.castAddMonoidHom ℤ) a b

@[simp] theorem enatToIntegerOrder_top : enatToIntegerOrder ⊤ = ⊤ := rfl

@[simp] theorem enatToIntegerOrder_natCast (n : ℕ) :
    enatToIntegerOrder n = (n : WithTop ℤ) := rfl

@[simp] theorem enatToIntegerOrder_eq_top_iff (n : ℕ∞) :
    enatToIntegerOrder n = ⊤ ↔ n = ⊤ := ENat.map_eq_top_iff

theorem enatToIntegerOrder_monotone : Monotone enatToIntegerOrder := by logtwo_quiet
  apply ENat.monotone_map_iff.mpr
  intro m n h
  change (m : ℤ) ≤ (n : ℤ)
  exact_mod_cast h

noncomputable def localAddValuation
    (A : Type*) [CommRing A] [IsDomain A] [IsDiscreteValuationRing A] :
    AddValuation A (WithTop ℤ) :=
  (IsDiscreteValuationRing.addVal A).map
    { toAddMonoidHom := enatToIntegerOrder
      monotone' := enatToIntegerOrder_monotone } enatToIntegerOrder_top

@[simp] theorem localAddValuation_apply
    {A : Type*} [CommRing A] [IsDomain A] [IsDiscreteValuationRing A] (a : A) :
    localAddValuation A a = enatToIntegerOrder (IsDiscreteValuationRing.addVal A a) := rfl

@[simp] theorem localAddValuation_eq_top_iff
    {A : Type*} [CommRing A] [IsDomain A] [IsDiscreteValuationRing A] (a : A) :
    localAddValuation A a = ⊤ ↔ a = 0 := by logtwo_quiet
  rw [localAddValuation_apply, enatToIntegerOrder_eq_top_iff,
    IsDiscreteValuationRing.addVal_eq_top_iff]

theorem nonZeroDivisors_le_primeCompl
    (A : Type*) [CommRing A] [IsDomain A] [IsDiscreteValuationRing A] :
    nonZeroDivisors A ≤ (localAddValuation A).toValuation.supp.primeCompl := by logtwo_quiet
  intro a ha
  change localAddValuation A a ≠ ⊤
  rw [ne_eq, localAddValuation_eq_top_iff]
  exact mem_nonZeroDivisors_iff_ne_zero.mp ha

noncomputable def fractionAddValuation
    (A K : Type*) [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
    [Field K] [Algebra A K] [IsFractionRing A K] : AddValuation K (WithTop ℤ) :=
  AddValuation.ofValuation
    ((localAddValuation A).toValuation.extendToLocalization
      (nonZeroDivisors_le_primeCompl A) K)

@[simp] theorem fractionAddValuation_algebraMap
    {A K : Type*} [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
    [Field K] [Algebra A K] [IsFractionRing A K] (a : A) :
    fractionAddValuation A K (algebraMap A K a) = localAddValuation A a := by logtwo_quiet
  exact Valuation.extendToLocalization_apply_map_apply
    (localAddValuation A).toValuation (nonZeroDivisors_le_primeCompl A) K a

theorem fraction_order_eq_principal_colength
    {A K : Type*} [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
    [Field K] [Algebra A K] [IsFractionRing A K] {a : A} (ha : a ≠ 0) :
    fractionAddValuation A K (algebraMap A K a) =
      enatToIntegerOrder (Module.length A (A ⧸ Ideal.span {a})) := by logtwo_quiet
  rw [fractionAddValuation_algebraMap, localAddValuation_apply,
    length_quotient_span_eq_addVal ha]

theorem principal_colength_ne_top
    {A : Type*} [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
    {a : A} (ha : a ≠ 0) : Module.length A (A ⧸ Ideal.span {a}) ≠ ⊤ := by logtwo_quiet
  rw [length_quotient_span_eq_addVal ha]
  exact IsDiscreteValuationRing.addVal_eq_top_iff.not.mpr ha

theorem integerOrder_field_image_eq_length
    {A K : Type*} [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
    [Field K] [Algebra A K] [IsFractionRing A K] {a : A} (ha : a ≠ 0) :
    WeightedCurveDegree.integerOrder (fractionAddValuation A K)
      (Units.mk0 (algebraMap A K a) ((map_ne_zero_iff _ (IsFractionRing.injective A K)).mpr ha)) =
        ((Module.length A (A ⧸ Ideal.span {a})).toNat : ℤ) := by logtwo_quiet
  apply WithTop.coe_injective
  rw [WeightedCurveDegree.coe_integerOrder]
  change fractionAddValuation A K (algebraMap A K a) = _
  rw [fraction_order_eq_principal_colength ha]
  obtain ⟨n, hn⟩ := ENat.ne_top_iff_exists.mp (principal_colength_ne_top ha)
  rw [← hn]
  simp

noncomputable def residueCoefficientEquiv
    (F A : Type*) [Field F] [IsAlgClosed F] [CommRing A] [Algebra F A]
    [IsLocalRing A] [Algebra.IsIntegral F (IsLocalRing.ResidueField A)] :
    F ≃ₐ[F] IsLocalRing.ResidueField A :=
  AlgEquiv.ofBijective (Algebra.ofId F (IsLocalRing.ResidueField A))
    IsAlgClosed.algebraMap_bijective_of_isIntegral

noncomputable def residueAugmentation
    (F A : Type*) [Field F] [IsAlgClosed F] [CommRing A] [Algebra F A]
    [IsLocalRing A] [Algebra.IsIntegral F (IsLocalRing.ResidueField A)] : A →+* F :=
  (residueCoefficientEquiv F A).symm.toRingHom.comp (IsLocalRing.residue A)

@[simp] theorem residueAugmentation_algebraMap
    (F A : Type*) [Field F] [IsAlgClosed F] [CommRing A] [Algebra F A]
    [IsLocalRing A] [Algebra.IsIntegral F (IsLocalRing.ResidueField A)] (c : F) :
    residueAugmentation F A (algebraMap F A c) = c := by logtwo_quiet
  change (residueCoefficientEquiv F A).symm
    (algebraMap A (IsLocalRing.ResidueField A) (algebraMap F A c)) = c
  rw [← IsScalarTower.algebraMap_apply F A (IsLocalRing.ResidueField A)]
  exact (residueCoefficientEquiv F A).symm.commutes c

end PiExponent.CurveLocalOrder

end OAI
end Source0028

-- Source: OAI/NumberTheory/PiExponent/Geometry/CurveZeroPole.lean
section Source0029
-- Modified in this edition: unused plain lemmas removed; see reduction.json.
/-
Modification notice for the LogTwo project.
Derived from openai/math (Apache-2.0), revision adc7f1241b42e322a6451854ab7e4b4c146bf78a.
Original source: lean/OAI/NumberTheory/PiExponent/Geometry/CurveZeroPole.lean
Changes: Convert module/import declarations to the Lean 4.34 public module format.
See ../THIRD_PARTY_NOTICES.txt for provenance and the recorded changes.
-/

namespace OAI

noncomputable section
open scoped BigOperators Polynomial nonZeroDivisors

namespace PiExponent.CurveZeroPole

def fiberDegree {R : Type*} [CommRing R] (S : Type*) [CommRing S]
    [Algebra R S] [Algebra.QuasiFinite R S] (p : Ideal R) : ℕ :=
  let := (Algebra.QuasiFinite.finite_primesOver (R := R) (S := S) p).fintype
  ∑ q : p.primesOver S, q.1.ramificationIdx R * q.1.inertiaDeg R

theorem fiberDegree_eq_rank {R : Type*} [CommRing R] [IsDomain R]
    (S : Type*) [CommRing S] [Algebra R S]
    [Module.Finite R S] [Module.Flat R S]
    (p : Ideal R) [p.IsPrime] :
    fiberDegree S p = Module.finrank R S := by logtwo_quiet
  let := (Algebra.QuasiFinite.finite_primesOver (R := R) (S := S) p).fintype
  exact Ideal.sum_ramification_inertia_eq_finrank p S

theorem fiberDegree_eq_fractionField_rank
    (R K S L : Type*) [CommRing R] [IsDomain R] [Field K]
    [CommRing S] [Field L] [Algebra R S] [Algebra K L]
    [Algebra R K] [Algebra S L] [Algebra R L]
    [IsScalarTower R K L] [IsScalarTower R S L]
    [IsFractionRing R K] [IsFractionRing S L]
    [Module.Finite R S] [Module.Flat R S]
    (p : Ideal R) [p.IsPrime] :
    fiberDegree S p = Module.finrank K L := by logtwo_quiet
  rw [fiberDegree_eq_rank, IsFractionRing.finrank_eq R K S L]

theorem functionField_fiberDegree
    (F E : Type*) [Field F] [Field E]
    [Algebra F[X] E] [Algebra (RatFunc F) E]
    [IsScalarTower F[X] (RatFunc F) E]
    [FunctionField F E] [Algebra.IsSeparable (RatFunc F) E]
    (p : Ideal F[X]) [p.IsPrime] :
    fiberDegree (FunctionField.ringOfIntegers F E) p =
      Module.finrank (RatFunc F) E := by logtwo_quiet
  let : Module.IsTorsionFree F[X] (FunctionField.ringOfIntegers F E) :=
    Module.isTorsionFree_iff_algebraMap_injective.mpr
      (FunctionField.ringOfIntegers.algebraMap_injective F E)
  exact fiberDegree_eq_fractionField_rank F[X] (RatFunc F)
    (FunctionField.ringOfIntegers F E) E p

theorem adjoin_inverse_eq {F E : Type*} [Field F] [Field E] [Algebra F E] (f : E) :
    IntermediateField.adjoin F {f⁻¹} = IntermediateField.adjoin F {f} := by logtwo_quiet
  apply le_antisymm
  · exact IntermediateField.adjoin_simple_le_iff.mpr
      (IntermediateField.inv_mem _ (IntermediateField.subset_adjoin F {f} (by logtwo_quiet simp)))
  · apply IntermediateField.adjoin_simple_le_iff.mpr
    simpa using IntermediateField.inv_mem (IntermediateField.adjoin F {f⁻¹})
      (show f⁻¹ ∈ IntermediateField.adjoin F {f⁻¹} from
        IntermediateField.subset_adjoin F {f⁻¹} (Set.mem_singleton _))

theorem parameter_inverse_degree_eq
    {F E : Type*} [Field F] [Field E] [Algebra F E] (f : E) :
    Module.finrank (IntermediateField.adjoin F {f⁻¹}) E =
      Module.finrank (IntermediateField.adjoin F {f}) E := by logtwo_quiet
  rw [adjoin_inverse_eq]

def parameterEmbedding {F E : Type*} [Field F] [Field E] [Algebra F E]
    (f : E) (hf : Transcendental F f) : RatFunc F →ₐ[F] E :=
  (IntermediateField.val (IntermediateField.adjoin F {f})).comp
    (RatFunc.algEquivOfTranscendental f hf).toAlgHom

@[simp] theorem parameterEmbedding_X {F E : Type*} [Field F] [Field E] [Algebra F E]
    (f : E) (hf : Transcendental F f) : parameterEmbedding f hf RatFunc.X = f := by logtwo_quiet
  simp [parameterEmbedding]

abbrev parameterAlgebra {F E : Type*} [Field F] [Field E] [Algebra F E]
    (f : E) (hf : Transcendental F f) : Algebra (RatFunc F) E :=
  (parameterEmbedding f hf).toRingHom.toAlgebra

theorem parameter_finrank {F E : Type*} [Field F] [Field E] [Algebra F E]
    (f : E) (hf : Transcendental F f) :
    let := parameterAlgebra f hf
    Module.finrank (RatFunc F) E = Module.finrank (IntermediateField.adjoin F {f}) E := by logtwo_quiet
  let := parameterAlgebra f hf
  apply Algebra.finrank_eq_of_equiv_equiv
    (RatFunc.algEquivOfTranscendental f hf).toRingEquiv (RingEquiv.refl E)
  rfl

theorem parameter_finite {F E : Type*} [Field F] [Field E] [Algebra F E]
    (f : E) (hf : Transcendental F f)
    [FiniteDimensional (IntermediateField.adjoin F {f}) E] :
    let := parameterAlgebra f hf
    FiniteDimensional (RatFunc F) E := by logtwo_quiet
  let := parameterAlgebra f hf
  let e := RatFunc.algEquivOfTranscendental f hf
  let b := Module.finBasis (IntermediateField.adjoin F {f}) E
  apply (b.mapCoeffs e.symm.toRingEquiv ?_).finiteDimensional_of_finite
  intro c x
  change (↑(e (e.symm c)) : E) * x = (c : E) * x
  rw [e.apply_symm_apply]

abbrev parameterPolynomialAlgebra {F E : Type*} [Field F] [Field E] [Algebra F E]
    (f : E) (hf : Transcendental F f) : Algebra F[X] E :=
  ((parameterEmbedding f hf).toRingHom.comp (algebraMap F[X] (RatFunc F))).toAlgebra

theorem parameter_scalarTower {F E : Type*} [Field F] [Field E] [Algebra F E]
    (f : E) (hf : Transcendental F f) :
    let := parameterAlgebra f hf
    let := parameterPolynomialAlgebra f hf
    IsScalarTower F[X] (RatFunc F) E := by logtwo_quiet
  let := parameterAlgebra f hf
  let := parameterPolynomialAlgebra f hf
  apply IsScalarTower.of_algebraMap_eq
  intro x
  rfl

def zeroPrime (F : Type*) [Field F] : Ideal F[X] :=
  RingHom.ker Polynomial.constantCoeff

instance zeroPrime_isPrime (F : Type*) [Field F] : (zeroPrime F).IsPrime :=
  RingHom.ker_isPrime Polynomial.constantCoeff

theorem zeroPrime_eq_span_X (F : Type*) [Field F] :
    zeroPrime F = Ideal.span {Polynomial.X} := Polynomial.ker_constantCoeff

def parameterFiberDegree {F E : Type*} [Field F] [CharZero F] [Field E] [Algebra F E]
    (f : E) (hf : Transcendental F f)
    [FiniteDimensional (IntermediateField.adjoin F {f}) E] : ℕ :=
  let := parameterAlgebra f hf
  let := parameterPolynomialAlgebra f hf
  let := parameter_scalarTower f hf
  let := parameter_finite f hf
  fiberDegree (FunctionField.ringOfIntegers F E) (zeroPrime F)

theorem parameterFiberDegree_eq {F E : Type*} [Field F] [CharZero F] [Field E] [Algebra F E]
    (f : E) (hf : Transcendental F f)
    [FiniteDimensional (IntermediateField.adjoin F {f}) E] :
    parameterFiberDegree f hf = Module.finrank (IntermediateField.adjoin F {f}) E := by logtwo_quiet
  let := parameterAlgebra f hf
  let := parameterPolynomialAlgebra f hf
  let := parameter_scalarTower f hf
  let := parameter_finite f hf
  change fiberDegree (FunctionField.ringOfIntegers F E) (zeroPrime F) = _
  rw [functionField_fiberDegree]
  exact parameter_finrank f hf

theorem transcendental_inverse {F E : Type*} [Field F] [Field E] [Algebra F E]
    (f : E) (hf : Transcendental F f) : Transcendental F f⁻¹ := by logtwo_quiet
  simpa only [Transcendental, IsAlgebraic.inv_iff] using hf

theorem constantCoeff_surjective (F : Type*) [Field F] :
    Function.Surjective (Polynomial.constantCoeff : F[X] →+* F) := by logtwo_quiet
  intro x
  exact ⟨Polynomial.C x, by logtwo_quiet simp⟩

instance zeroPrime_isMaximal (F : Type*) [Field F] : (zeroPrime F).IsMaximal :=
  RingHom.ker_isMaximal_of_surjective Polynomial.constantCoeff (constantCoeff_surjective F)

def zeroPrimeQuotientEquiv (F : Type*) [Field F] : (F[X] ⧸ zeroPrime F) ≃+* F :=
  RingHom.quotientKerEquivOfSurjective (constantCoeff_surjective F)

theorem zeroFiber_inertiaDeg_eq_one (F S : Type*) [Field F] [IsAlgClosed F]
    [CommRing S] [Algebra F[X] S] [Module.Finite F[X] S]
    (q : Ideal S) [q.IsPrime] [q.LiesOver (zeroPrime F)] :
    q.inertiaDeg F[X] = 1 := by logtwo_quiet
  have : q.IsMaximal := Ideal.IsMaximal.of_liesOver_isMaximal q (zeroPrime F)
  let : Field (F[X] ⧸ zeroPrime F) := Ideal.Quotient.field _
  let : Field (S ⧸ q) := Ideal.Quotient.field _
  let : IsAlgClosed (F[X] ⧸ zeroPrime F) :=
    IsAlgClosed.of_ringEquiv F _ (zeroPrimeQuotientEquiv F).symm
  rw [Ideal.inertiaDeg_eq_of_isMaximal (zeroPrime F) q]
  apply Module.finrank_of_bijective_algebraMap
  apply IsAlgClosed.algebraMap_bijective_of_isIntegral

def zeroFiberLength (F S : Type*) [Field F] [CommRing S]
    [Algebra F[X] S] [Module.Finite F[X] S] : ℕ :=
  let := (Algebra.QuasiFinite.finite_primesOver (R := F[X]) (S := S) (zeroPrime F)).fintype
  ∑ q : (zeroPrime F).primesOver S,
    (Module.length (Localization.AtPrime q.1)
      ((Localization.AtPrime q.1) ⧸
        Ideal.span {algebraMap F[X] (Localization.AtPrime q.1) Polynomial.X})).toNat

theorem zeroFiberLength_eq_fiberDegree (F S : Type*) [Field F] [IsAlgClosed F]
    [CommRing S] [Algebra F[X] S] [Module.Finite F[X] S] :
    zeroFiberLength F S = fiberDegree S (zeroPrime F) := by logtwo_quiet
  unfold zeroFiberLength fiberDegree
  apply Finset.sum_congr rfl
  intro q _
  rw [zeroFiber_inertiaDeg_eq_one F S q.1, mul_one,
    Ideal.ramificationIdx_eq (zeroPrime F) q.1]
  have hm : (zeroPrime F).map (algebraMap F[X] (Localization.AtPrime q.1)) =
      Ideal.span {algebraMap F[X] (Localization.AtPrime q.1) Polynomial.X} := by logtwo_quiet
    calc
      _ = (Ideal.span {Polynomial.X}).map
          (algebraMap F[X] (Localization.AtPrime q.1)) :=
        congrArg (Ideal.map (algebraMap F[X] (Localization.AtPrime q.1))) (zeroPrime_eq_span_X F)
      _ = _ := by logtwo_quiet rw [Ideal.map_span, Set.image_singleton]
  exact congrArg (fun I : Ideal (Localization.AtPrime q.1) =>
    (Module.length (Localization.AtPrime q.1) ((Localization.AtPrime q.1) ⧸ I)).toNat) hm.symm

def parameterZeroLength {F E : Type*} [Field F] [CharZero F] [Field E] [Algebra F E]
    (f : E) (hf : Transcendental F f)
    [FiniteDimensional (IntermediateField.adjoin F {f}) E] : ℕ :=
  let := parameterAlgebra f hf
  let := parameterPolynomialAlgebra f hf
  let := parameter_scalarTower f hf
  let := parameter_finite f hf
  zeroFiberLength F (FunctionField.ringOfIntegers F E)

theorem parameterZeroLength_eq_degree
    {F E : Type*} [Field F] [CharZero F] [IsAlgClosed F] [Field E] [Algebra F E]
    (f : E) (hf : Transcendental F f)
    [FiniteDimensional (IntermediateField.adjoin F {f}) E] :
    parameterZeroLength f hf = Module.finrank (IntermediateField.adjoin F {f}) E := by logtwo_quiet
  let := parameterAlgebra f hf
  let := parameterPolynomialAlgebra f hf
  let := parameter_scalarTower f hf
  let := parameter_finite f hf
  change zeroFiberLength F (FunctionField.ringOfIntegers F E) = _
  rw [zeroFiberLength_eq_fiberDegree]
  exact parameterFiberDegree_eq f hf

theorem zero_pole_length_eq
    {F E : Type*} [Field F] [CharZero F] [IsAlgClosed F] [Field E] [Algebra F E]
    (f : E) (hf : Transcendental F f)
    [FiniteDimensional (IntermediateField.adjoin F {f}) E] :
    letI : FiniteDimensional (IntermediateField.adjoin F {f⁻¹}) E :=
      (adjoin_inverse_eq (F := F) f).symm ▸ inferInstance
    parameterZeroLength f hf = parameterZeroLength f⁻¹ (transcendental_inverse f hf) := by logtwo_quiet
  let : FiniteDimensional (IntermediateField.adjoin F {f⁻¹}) E :=
    (adjoin_inverse_eq (F := F) f).symm ▸ inferInstance
  rw [parameterZeroLength_eq_degree, parameterZeroLength_eq_degree, parameter_inverse_degree_eq]

def primeFieldValuation (S E : Type*) [CommRing S] [IsDedekindDomain S]
    [Field E] [Algebra S E] [IsFractionRing S E]
    (q : IsDedekindDomain.HeightOneSpectrum S) : AddValuation E (WithTop ℤ) :=
  let A := Localization.AtPrime q.asIdeal
  let := IsLocalization.localizationAlgebraOfSubmonoidLe A E
    q.asIdeal.primeCompl S⁰ q.asIdeal.primeCompl_le_nonZeroDivisors
  let := IsLocalization.localization_isScalarTower_of_submonoid_le A E
    q.asIdeal.primeCompl S⁰ q.asIdeal.primeCompl_le_nonZeroDivisors
  let := IsFractionRing.isFractionRing_of_isDomain_of_isLocalization q.asIdeal.primeCompl A E
  let := IsLocalization.AtPrime.isDiscreteValuationRing_of_dedekind_domain S q.ne_bot A
  CurveLocalOrder.fractionAddValuation A E

theorem primeFieldValuation_algebraMap
    (S E : Type*) [CommRing S] [IsDedekindDomain S]
    [Field E] [Algebra S E] [IsFractionRing S E]
    (q : IsDedekindDomain.HeightOneSpectrum S) (a : S) (ha : a ≠ 0) :
    primeFieldValuation S E q (algebraMap S E a) =
      CurveLocalOrder.enatToIntegerOrder
        (Module.length (Localization.AtPrime q.asIdeal)
          ((Localization.AtPrime q.asIdeal) ⧸
            Ideal.span {algebraMap S (Localization.AtPrime q.asIdeal) a})) := by logtwo_quiet
  let A := Localization.AtPrime q.asIdeal
  let := IsLocalization.localizationAlgebraOfSubmonoidLe A E
    q.asIdeal.primeCompl S⁰ q.asIdeal.primeCompl_le_nonZeroDivisors
  let := IsLocalization.localization_isScalarTower_of_submonoid_le A E
    q.asIdeal.primeCompl S⁰ q.asIdeal.primeCompl_le_nonZeroDivisors
  let := IsFractionRing.isFractionRing_of_isDomain_of_isLocalization q.asIdeal.primeCompl A E
  let := IsLocalization.AtPrime.isDiscreteValuationRing_of_dedekind_domain S q.ne_bot A
  change CurveLocalOrder.fractionAddValuation A E (algebraMap S E a) = _
  rw [IsScalarTower.algebraMap_apply S A E]
  apply CurveLocalOrder.fraction_order_eq_principal_colength
  exact (map_ne_zero_iff _ (IsLocalization.injective A
    q.asIdeal.primeCompl_le_nonZeroDivisors)).mpr ha

theorem primeField_integerOrder_algebraMap
    (S E : Type*) [CommRing S] [IsDedekindDomain S]
    [Field E] [Algebra S E] [IsFractionRing S E]
    (q : IsDedekindDomain.HeightOneSpectrum S) (a : S) (ha : a ≠ 0) :
    WeightedCurveDegree.integerOrder (primeFieldValuation S E q)
      (Units.mk0 (algebraMap S E a) ((map_ne_zero_iff _ (IsFractionRing.injective S E)).mpr ha)) =
      ((Module.length (Localization.AtPrime q.asIdeal)
        ((Localization.AtPrime q.asIdeal) ⧸
          Ideal.span {algebraMap S (Localization.AtPrime q.asIdeal) a})).toNat : ℤ) := by logtwo_quiet
  let A := Localization.AtPrime q.asIdeal
  let := IsLocalization.AtPrime.isDiscreteValuationRing_of_dedekind_domain S q.ne_bot A
  have ha' : algebraMap S A a ≠ 0 :=
    (map_ne_zero_iff _ (IsLocalization.injective A
      q.asIdeal.primeCompl_le_nonZeroDivisors)).mpr ha
  apply WithTop.coe_injective
  rw [WeightedCurveDegree.coe_integerOrder]
  change primeFieldValuation S E q (algebraMap S E a) = _
  rw [primeFieldValuation_algebraMap S E q a ha]
  obtain ⟨n, hn⟩ := ENat.ne_top_iff_exists.mp
    (CurveLocalOrder.principal_colength_ne_top ha')
  change CurveLocalOrder.enatToIntegerOrder
    (Module.length A (A ⧸ Ideal.span {algebraMap S A a})) = _
  rw [← hn]
  simp

theorem zeroPrime_ne_bot (F : Type*) [Field F] : zeroPrime F ≠ ⊥ := by logtwo_quiet
  intro h
  have hx : Polynomial.X ∈ zeroPrime F := by logtwo_quiet
    change Polynomial.constantCoeff Polynomial.X = (0 : F)
    simp
  rw [h, Ideal.mem_bot] at hx
  exact Polynomial.X_ne_zero hx

def zeroFiberHeightOne (F S : Type*) [Field F] [CommRing S] [IsDomain S]
    [Algebra F[X] S] [FaithfulSMul F[X] S]
    (q : (zeroPrime F).primesOver S) : IsDedekindDomain.HeightOneSpectrum S :=
  ⟨q.1, q.2.1, Ideal.ne_bot_of_mem_primesOver (zeroPrime_ne_bot F) q.2⟩

theorem baseParameter_nonzero (F S E : Type*) [Field F] [CommRing S] [IsDomain S]
    [Field E] [Algebra F[X] S] [FaithfulSMul F[X] S]
    [Algebra S E] [IsFractionRing S E] [Algebra F[X] E] [IsScalarTower F[X] S E] :
    algebraMap F[X] E Polynomial.X ≠ 0 := by logtwo_quiet
  rw [IsScalarTower.algebraMap_apply F[X] S E]
  exact (map_ne_zero_iff _ (IsFractionRing.injective S E)).mpr
    ((map_ne_zero_iff _ (FaithfulSMul.algebraMap_injective F[X] S)).mpr Polynomial.X_ne_zero)

def zeroFiberIntegerOrderSum (F S E : Type*) [Field F] [CommRing S]
    [IsDedekindDomain S] [Field E] [Algebra F[X] S] [FaithfulSMul F[X] S]
    [Module.Finite F[X] S] [Algebra S E] [IsFractionRing S E]
    [Algebra F[X] E] [IsScalarTower F[X] S E] : ℤ :=
  let := (Algebra.QuasiFinite.finite_primesOver (R := F[X]) (S := S) (zeroPrime F)).fintype
  ∑ q : (zeroPrime F).primesOver S,
    WeightedCurveDegree.integerOrder (primeFieldValuation S E (zeroFiberHeightOne F S q))
      (Units.mk0 (algebraMap F[X] E Polynomial.X) (baseParameter_nonzero F S E))

theorem zeroFiberIntegerOrderSum_eq_length (F S E : Type*) [Field F] [CommRing S]
    [IsDedekindDomain S] [Field E] [Algebra F[X] S] [FaithfulSMul F[X] S]
    [Module.Finite F[X] S] [Algebra S E] [IsFractionRing S E]
    [Algebra F[X] E] [IsScalarTower F[X] S E] :
    zeroFiberIntegerOrderSum F S E = (zeroFiberLength F S : ℤ) := by logtwo_quiet
  unfold zeroFiberIntegerOrderSum zeroFiberLength
  rw [Nat.cast_sum]
  apply Finset.sum_congr rfl
  intro q _
  have hx : algebraMap F[X] S Polynomial.X ≠ 0 :=
    (map_ne_zero_iff _ (FaithfulSMul.algebraMap_injective F[X] S)).mpr Polynomial.X_ne_zero
  have he := primeField_integerOrder_algebraMap S E
    (zeroFiberHeightOne F S q) (algebraMap F[X] S Polynomial.X) hx
  calc
    _ = WeightedCurveDegree.integerOrder
        (primeFieldValuation S E (zeroFiberHeightOne F S q))
        (Units.mk0 (algebraMap S E (algebraMap F[X] S Polynomial.X))
          ((map_ne_zero_iff _ (IsFractionRing.injective S E)).mpr hx)) := by logtwo_quiet
      congr 1
      ext
      exact IsScalarTower.algebraMap_apply F[X] S E Polynomial.X
    _ = _ := he
    _ = _ := by logtwo_quiet
      let A := Localization.AtPrime q.1
      have hi : Ideal.span {algebraMap S A (algebraMap F[X] S Polynomial.X)} =
          Ideal.span {algebraMap F[X] A Polynomial.X} :=
        congrArg (fun z : A => Ideal.span {z})
          (IsScalarTower.algebraMap_apply F[X] S A Polynomial.X).symm
      exact congrArg (fun I : Ideal A => ((Module.length A (A ⧸ I)).toNat : ℤ)) hi

def parameterZeroOrder {F E : Type*} [Field F] [CharZero F] [Field E] [Algebra F E]
    (f : E) (hf : Transcendental F f)
    [FiniteDimensional (IntermediateField.adjoin F {f}) E] : ℤ :=
  let := parameterAlgebra f hf
  let := parameterPolynomialAlgebra f hf
  let := parameter_scalarTower f hf
  let := parameter_finite f hf
  let : Module.IsTorsionFree F[X] (FunctionField.ringOfIntegers F E) :=
    Module.isTorsionFree_iff_algebraMap_injective.mpr
      (FunctionField.ringOfIntegers.algebraMap_injective F E)
  zeroFiberIntegerOrderSum F (FunctionField.ringOfIntegers F E) E

theorem parameterZeroOrder_eq_length
    {F E : Type*} [Field F] [CharZero F] [Field E] [Algebra F E]
    (f : E) (hf : Transcendental F f)
    [FiniteDimensional (IntermediateField.adjoin F {f}) E] :
    parameterZeroOrder f hf = (parameterZeroLength f hf : ℤ) := by logtwo_quiet
  let := parameterAlgebra f hf
  let := parameterPolynomialAlgebra f hf
  let := parameter_scalarTower f hf
  let := parameter_finite f hf
  let : Module.IsTorsionFree F[X] (FunctionField.ringOfIntegers F E) :=
    Module.isTorsionFree_iff_algebraMap_injective.mpr
      (FunctionField.ringOfIntegers.algebraMap_injective F E)
  exact zeroFiberIntegerOrderSum_eq_length F (FunctionField.ringOfIntegers F E) E

theorem zero_pole_order_eq
    {F E : Type*} [Field F] [CharZero F] [IsAlgClosed F] [Field E] [Algebra F E]
    (f : E) (hf : Transcendental F f)
    [FiniteDimensional (IntermediateField.adjoin F {f}) E] :
    letI : FiniteDimensional (IntermediateField.adjoin F {f⁻¹}) E :=
      (adjoin_inverse_eq (F := F) f).symm ▸ inferInstance
    parameterZeroOrder f hf = parameterZeroOrder f⁻¹ (transcendental_inverse f hf) := by logtwo_quiet
  let : FiniteDimensional (IntermediateField.adjoin F {f⁻¹}) E :=
    (adjoin_inverse_eq (F := F) f).symm ▸ inferInstance
  rw [parameterZeroOrder_eq_length, parameterZeroOrder_eq_length, zero_pole_length_eq]

abbrev parameterChart {F E : Type*} [Field F] [Field E] [Algebra F E]
    (f : E) (hf : Transcendental F f) : Type _ :=
  let := parameterPolynomialAlgebra f hf
  FunctionField.ringOfIntegers F E

abbrev parameterZeroPlaces {F E : Type*} [Field F] [Field E] [Algebra F E]
    (f : E) (hf : Transcendental F f) : Type _ :=
  let := parameterPolynomialAlgebra f hf
  (zeroPrime F).primesOver (parameterChart f hf)

abbrev parameterZeroPlacesFintype
    {F E : Type*} [Field F] [CharZero F] [Field E] [Algebra F E]
    (f : E) (hf : Transcendental F f)
    [FiniteDimensional (IntermediateField.adjoin F {f}) E] :
    Fintype (parameterZeroPlaces f hf) :=
  let := parameterAlgebra f hf
  let := parameterPolynomialAlgebra f hf
  let := parameter_scalarTower f hf
  let := parameter_finite f hf
  (Algebra.QuasiFinite.finite_primesOver
    (R := F[X]) (S := FunctionField.ringOfIntegers F E) (zeroPrime F)).fintype

def parameterPlaceValuation
    {F E : Type*} [Field F] [CharZero F] [Field E] [Algebra F E]
    (f : E) (hf : Transcendental F f)
    [FiniteDimensional (IntermediateField.adjoin F {f}) E]
    (q : parameterZeroPlaces f hf) : AddValuation E (WithTop ℤ) :=
  let := parameterAlgebra f hf
  let := parameterPolynomialAlgebra f hf
  let := parameter_scalarTower f hf
  let := parameter_finite f hf
  let : Module.IsTorsionFree F[X] (FunctionField.ringOfIntegers F E) :=
    Module.isTorsionFree_iff_algebraMap_injective.mpr
      (FunctionField.ringOfIntegers.algebraMap_injective F E)
  primeFieldValuation (parameterChart f hf) E
    (zeroFiberHeightOne F (parameterChart f hf) q)

theorem parameterPolynomialAlgebra_map
    {F E : Type*} [Field F] [Field E] [Algebra F E]
    (f : E) (hf : Transcendental F f) (p : F[X]) :
    letI := parameterPolynomialAlgebra f hf
    algebraMap F[X] E p = Polynomial.aeval f p := by logtwo_quiet
  let := parameterPolynomialAlgebra f hf
  change parameterEmbedding f hf (algebraMap F[X] (RatFunc F) p) = Polynomial.aeval f p
  change (↑(RatFunc.algEquivOfTranscendental f hf (algebraMap F[X] (RatFunc F) p)) : E) = _
  rw [RatFunc.algEquivOfTranscendental_algebraMap]
  exact IntermediateField.AdjoinSimple.coe_aeval_gen_apply F f p

theorem parameterZeroOrder_eq_sum
    {F E : Type*} [Field F] [CharZero F] [Field E] [Algebra F E]
    (f : E) (hf : Transcendental F f)
    [FiniteDimensional (IntermediateField.adjoin F {f}) E] :
    letI := parameterZeroPlacesFintype f hf
    parameterZeroOrder f hf =
      ∑ q : parameterZeroPlaces f hf,
        WeightedCurveDegree.integerOrder (parameterPlaceValuation f hf q)
          (Units.mk0 f hf.ne_zero) := by logtwo_quiet
  let := parameterAlgebra f hf
  let := parameterPolynomialAlgebra f hf
  let := parameter_scalarTower f hf
  let := parameter_finite f hf
  let : Module.IsTorsionFree F[X] (FunctionField.ringOfIntegers F E) :=
    Module.isTorsionFree_iff_algebraMap_injective.mpr
      (FunctionField.ringOfIntegers.algebraMap_injective F E)
  dsimp only [parameterZeroOrder, zeroFiberIntegerOrderSum, parameterPlaceValuation]
  apply Finset.sum_congr rfl
  intro q _
  congr 1
  ext
  change parameterEmbedding f hf RatFunc.X = f
  exact parameterEmbedding_X f hf

end PiExponent.CurveZeroPole

end

end OAI
end Source0029

-- Source: OAI/NumberTheory/PiExponent/LocalAlgebra/DVRValuationUnique.lean
section Source0030
/-
Modification notice for the LogTwo project.
Derived from openai/math (Apache-2.0), revision adc7f1241b42e322a6451854ab7e4b4c146bf78a.
Original source: lean/OAI/NumberTheory/PiExponent/LocalAlgebra/DVRValuationUnique.lean
Changes: Convert module/import declarations to the Lean 4.34 public module format.
See ../THIRD_PARTY_NOTICES.txt for provenance and the recorded changes.
-/

namespace OAI

noncomputable section
open scoped nonZeroDivisors
open PiExponent.WeightedCurveDegree PiExponent.CurveLocalOrder

namespace PiExponent.DVRValuationUnique

variable {A E : Type*} [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
  [Field E] [Algebra A E] [IsFractionRing A E]

def localFieldUnit (a : A) (ha : a ≠ 0) : Eˣ :=
  Units.mk0 (algebraMap A E a) ((map_ne_zero_iff _ (IsFractionRing.injective A E)).mpr ha)

omit [IsDomain A] [IsDiscreteValuationRing A] in
@[simp] theorem localFieldUnit_val (a : A) (ha : a ≠ 0) :
    ((localFieldUnit (E := E) a ha : Eˣ) : E) = algebraMap A E a := rfl

omit [IsDomain A] [IsDiscreteValuationRing A] [IsFractionRing A E] in
theorem integerOrder_unit_eq_zero
    (v : AddValuation E (WithTop ℤ))
    (hregular : ∀ a : A, 0 ≤ v (algebraMap A E a)) (u : Aˣ) :
    integerOrder v (Units.map (algebraMap A E) u) = 0 := by logtwo_quiet
  have hpos : 0 ≤ integerOrder v (Units.map (algebraMap A E) u) := by logtwo_quiet
    apply WithTop.coe_le_coe.mp
    simpa using hregular (u : A)
  have hneg : 0 ≤ integerOrder v (Units.map (algebraMap A E) u⁻¹) := by logtwo_quiet
    apply WithTop.coe_le_coe.mp
    simpa using hregular (u⁻¹ : Aˣ)
  simp only [map_inv, integerOrder_inv] at hneg
  omega

theorem exists_order_eq_uniformizer_multiple
    (v : AddValuation E (WithTop ℤ))
    (hregular : ∀ a : A, 0 ≤ v (algebraMap A E a))
    {π : A} (hπ : Irreducible π) (a : A) (ha : a ≠ 0) :
    ∃ n : ℕ, integerOrder v (localFieldUnit (E := E) a ha) =
      (n : ℤ) * integerOrder v (localFieldUnit (E := E) π hπ.ne_zero) ∧
      IsDiscreteValuationRing.addVal A a = n := by logtwo_quiet
  obtain ⟨n, u, rfl⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible ha hπ
  refine ⟨n, ?_, IsDiscreteValuationRing.addVal_def' u hπ n⟩
  have he : localFieldUnit (E := E) ((u : A) * π ^ n) ha =
      Units.map (algebraMap A E) u * localFieldUnit (E := E) π hπ.ne_zero ^ n := by logtwo_quiet
    ext
    simp [localFieldUnit, map_mul, map_pow]
  rw [he, integerOrder_mul, integerOrder_pow, integerOrder_unit_eq_zero v hregular]
  simp

theorem uniformizer_order_dvd
    (v : AddValuation E (WithTop ℤ))
    (hregular : ∀ a : A, 0 ≤ v (algebraMap A E a))
    {π : A} (hπ : Irreducible π) (z : Eˣ) :
    integerOrder v (localFieldUnit (E := E) π hπ.ne_zero) ∣ integerOrder v z := by logtwo_quiet
  obtain ⟨a, b, hb, hab⟩ := IsFractionRing.div_surjective A (z : E)
  have hb0 : b ≠ 0 := mem_nonZeroDivisors_iff_ne_zero.mp hb
  have ha0 : a ≠ 0 := by logtwo_quiet
    intro ha
    apply z.ne_zero
    rw [← hab, ha, map_zero, zero_div]
  have hz : z = localFieldUnit (E := E) a ha0 / localFieldUnit (E := E) b hb0 := by logtwo_quiet
    ext
    simpa only [Units.val_div_eq_div_val, localFieldUnit_val] using hab.symm
  obtain ⟨m, hm, _⟩ := exists_order_eq_uniformizer_multiple v hregular hπ a ha0
  obtain ⟨n, hn, _⟩ := exists_order_eq_uniformizer_multiple v hregular hπ b hb0
  rw [hz, integerOrder_div, hm, hn]
  exact ⟨(m : ℤ) - n, by logtwo_quiet ring⟩

theorem eq_fractionAddValuation
    (v : AddValuation E (WithTop ℤ))
    (hregular : ∀ a : A, 0 ≤ v (algebraMap A E a))
    (hcenter : ∀ a ∈ IsLocalRing.maximalIdeal A, a ≠ 0 → 0 < v (algebraMap A E a))
    (hnormalized : ∃ z : Eˣ, integerOrder v z = 1) :
    v = fractionAddValuation A E := by logtwo_quiet
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible A
  have hπmem : π ∈ IsLocalRing.maximalIdeal A := by logtwo_quiet
    rw [hπ.maximalIdeal_eq]
    exact Ideal.subset_span (Set.mem_singleton π)
  have hpos : 0 < integerOrder v (localFieldUnit (E := E) π hπ.ne_zero) := by logtwo_quiet
    apply WithTop.coe_lt_coe.mp
    simpa using hcenter π hπmem hπ.ne_zero
  have hone : integerOrder v (localFieldUnit (E := E) π hπ.ne_zero) = 1 := by logtwo_quiet
    obtain ⟨z, hz⟩ := hnormalized
    apply Int.eq_one_of_dvd_one hpos.le
    rw [← hz]
    exact uniformizer_order_dvd v hregular hπ z
  have hlocal (a : A) : v (algebraMap A E a) = localAddValuation A a := by logtwo_quiet
    by_cases ha : a = 0
    · simp [ha]
    obtain ⟨n, hn, hcanonical⟩ := exists_order_eq_uniformizer_multiple v hregular hπ a ha
    rw [hone, mul_one] at hn
    rw [localAddValuation_apply, hcanonical, enatToIntegerOrder_natCast]
    rw [← localFieldUnit_val a ha, ← coe_integerOrder, hn]
    rfl
  ext x
  obtain ⟨a, b, _, rfl⟩ := IsFractionRing.div_surjective A x
  rw [AddValuation.map_div, AddValuation.map_div, hlocal, hlocal,
    fractionAddValuation_algebraMap, fractionAddValuation_algebraMap]

theorem fractionAddValuation_normalized :
    ∃ z : Eˣ, integerOrder (fractionAddValuation A E) z = 1 := by logtwo_quiet
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible A
  refine ⟨localFieldUnit (E := E) π hπ.ne_zero, ?_⟩
  apply WithTop.coe_injective
  rw [coe_integerOrder, localFieldUnit_val, fractionAddValuation_algebraMap,
    localAddValuation_apply, IsDiscreteValuationRing.addVal_uniformizer hπ]
  rfl

end PiExponent.DVRValuationUnique

end

end OAI
end Source0030

-- Source: OAI/NumberTheory/PiExponent/Geometry/CurveValuationCenter.lean
section Source0031
/-
Modification notice for the LogTwo project.
Derived from openai/math (Apache-2.0), revision adc7f1241b42e322a6451854ab7e4b4c146bf78a.
Original source: lean/OAI/NumberTheory/PiExponent/Geometry/CurveValuationCenter.lean
Changes: Convert module/import declarations to the Lean 4.34 public module format.
See ../THIRD_PARTY_NOTICES.txt for provenance and the recorded changes.
-/

namespace OAI

noncomputable section
open scoped Polynomial nonZeroDivisors
namespace PiExponent.CurveValuationCenter
open PiExponent.CurveZeroPole

theorem integral_mem_valuationSubring
    {R E Γ : Type*} [CommRing R] [Field E] [LinearOrderedCommGroupWithZero Γ]
    [Algebra R E] (v : Valuation E Γ)
    (hR : ∀ r : R, algebraMap R E r ∈ v.valuationSubring)
    {x : E} (hx : IsIntegral R x) : x ∈ v.valuationSubring := by logtwo_quiet
  let φ : R →+* v.valuationSubring :=
    { toFun := fun r => ⟨algebraMap R E r, hR r⟩
      map_zero' := by logtwo_quiet ext; simp
      map_one' := by logtwo_quiet ext; simp
      map_add' := by logtwo_quiet intros; ext; simp
      map_mul' := by logtwo_quiet intros; ext; simp }
  let : Algebra R v.valuationSubring := φ.toAlgebra
  let : IsScalarTower R v.valuationSubring E :=
    IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  exact (Valuation.valuationSubring.integers v).mem_of_integral hx.tower_top

theorem aeval_mem_valuationSubring
    {F E : Type*} [Field F] [Field E] [Algebra F E]
    (v : AddValuation E (WithTop ℤ)) (hF : ∀ c : F, 0 ≤ v (algebraMap F E c))
    (f : E) (hf : 0 ≤ v f) (p : F[X]) :
    Polynomial.aeval f p ∈ v.toValuation.valuationSubring := by logtwo_quiet
  induction p using Polynomial.induction_on' with
  | add p q hp hq =>
    rw [map_add]
    exact v.toValuation.valuationSubring.toSubring.add_mem hp hq
  | monomial n a =>
    rw [Polynomial.aeval_monomial]
    exact v.toValuation.valuationSubring.toSubring.mul_mem (hF a)
      (v.toValuation.valuationSubring.toSubring.pow_mem hf n)

theorem parameterChart_mem_valuationSubring
    {F E : Type*} [Field F] [Field E] [Algebra F E]
    (f : E) (hf : Transcendental F f)
    (v : AddValuation E (WithTop ℤ)) (hF : ∀ c : F, 0 ≤ v (algebraMap F E c))
    (hvf : 0 ≤ v f) (x : parameterChart f hf) :
    (x : E) ∈ v.toValuation.valuationSubring := by logtwo_quiet
  let := parameterPolynomialAlgebra f hf
  apply integral_mem_valuationSubring v.toValuation
    (fun p => ?_) x.property
  rw [parameterPolynomialAlgebra_map f hf p]
  exact aeval_mem_valuationSubring v hF f hvf p

def parameterChartValuationHom
    {F E : Type*} [Field F] [Field E] [Algebra F E]
    (f : E) (hf : Transcendental F f)
    (v : AddValuation E (WithTop ℤ)) (hF : ∀ c : F, 0 ≤ v (algebraMap F E c))
    (hvf : 0 ≤ v f) : parameterChart f hf →+* v.toValuation.valuationSubring where
  toFun x := ⟨x, parameterChart_mem_valuationSubring f hf v hF hvf x⟩
  map_zero' := rfl
  map_one' := rfl
  map_add' _ _ := rfl
  map_mul' _ _ := rfl

def parameterValuationCenter
    {F E : Type*} [Field F] [Field E] [Algebra F E]
    (f : E) (hf : Transcendental F f)
    (v : AddValuation E (WithTop ℤ)) (hF : ∀ c : F, 0 ≤ v (algebraMap F E c))
    (hvf : 0 ≤ v f) : Ideal (parameterChart f hf) :=
  (IsLocalRing.maximalIdeal v.toValuation.valuationSubring).comap
    (parameterChartValuationHom f hf v hF hvf)

instance parameterValuationCenter_isPrime
    {F E : Type*} [Field F] [Field E] [Algebra F E]
    (f : E) (hf : Transcendental F f)
    (v : AddValuation E (WithTop ℤ)) (hF : ∀ c : F, 0 ≤ v (algebraMap F E c))
    (hvf : 0 ≤ v f) : (parameterValuationCenter f hf v hF hvf).IsPrime :=
  inferInstanceAs (Ideal.comap _ (IsLocalRing.maximalIdeal _)).IsPrime

theorem mem_parameterValuationCenter_iff
    {F E : Type*} [Field F] [Field E] [Algebra F E]
    (f : E) (hf : Transcendental F f)
    (v : AddValuation E (WithTop ℤ)) (hF : ∀ c : F, 0 ≤ v (algebraMap F E c))
    (hvf : 0 ≤ v f) (x : parameterChart f hf) :
    x ∈ parameterValuationCenter f hf v hF hvf ↔ 0 < v (x : E) := by logtwo_quiet
  change parameterChartValuationHom f hf v hF hvf x ∈
    IsLocalRing.maximalIdeal v.toValuation.valuationSubring ↔ _
  exact v.toValuation.mem_maximalIdeal_iff

theorem parameterValuationCenter_liesOver
    {F E : Type*} [Field F] [Field E] [Algebra F E]
    (f : E) (hf : Transcendental F f)
    (v : AddValuation E (WithTop ℤ)) (hF : ∀ c : F, 0 ≤ v (algebraMap F E c))
    (hvf : 0 < v f) :
    letI := parameterPolynomialAlgebra f hf
    (parameterValuationCenter f hf v hF hvf.le).LiesOver (zeroPrime F) := by logtwo_quiet
  let := parameterPolynomialAlgebra f hf
  constructor
  apply (zeroPrime_isMaximal F).eq_of_le
  · exact Ideal.IsPrime.ne_top inferInstance
  rw [zeroPrime_eq_span_X, Ideal.span_singleton_le_iff_mem, Ideal.mem_under]
  rw [mem_parameterValuationCenter_iff]
  change 0 < v (algebraMap F[X] E Polynomial.X)
  rw [parameterPolynomialAlgebra_map f hf Polynomial.X, Polynomial.aeval_X]
  exact hvf

def parameterCenterPlace
    {F E : Type*} [Field F] [Field E] [Algebra F E]
    (f : E) (hf : Transcendental F f)
    (v : AddValuation E (WithTop ℤ)) (hF : ∀ c : F, 0 ≤ v (algebraMap F E c))
    (hvf : 0 < v f) : parameterZeroPlaces f hf :=
  let := parameterPolynomialAlgebra f hf
  let := parameterValuationCenter_liesOver f hf v hF hvf
  Ideal.primesOver.mk (zeroPrime F) (parameterValuationCenter f hf v hF hvf.le)

def parameterCenterLocalHom
    {F E : Type*} [Field F] [Field E] [Algebra F E]
    (f : E) (hf : Transcendental F f)
    (v : AddValuation E (WithTop ℤ)) (hF : ∀ c : F, 0 ≤ v (algebraMap F E c))
    (hvf : 0 ≤ v f) :
    Localization.AtPrime (parameterValuationCenter f hf v hF hvf) →+*
      v.toValuation.valuationSubring :=
  IsLocalization.lift (M := (parameterValuationCenter f hf v hF hvf).primeCompl)
    (g := parameterChartValuationHom f hf v hF hvf) (fun y => by logtwo_quiet
      have hy : parameterChartValuationHom f hf v hF hvf y ∉
          IsLocalRing.maximalIdeal v.toValuation.valuationSubring := y.property
      simpa only [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff, not_not] using hy)

@[simp] theorem parameterCenterLocalHom_algebraMap
    {F E : Type*} [Field F] [Field E] [Algebra F E]
    (f : E) (hf : Transcendental F f)
    (v : AddValuation E (WithTop ℤ)) (hF : ∀ c : F, 0 ≤ v (algebraMap F E c))
    (hvf : 0 ≤ v f) (x : parameterChart f hf) :
    parameterCenterLocalHom f hf v hF hvf
      (algebraMap (parameterChart f hf) _ x) = parameterChartValuationHom f hf v hF hvf x :=
  IsLocalization.lift_eq _ x

theorem parameterCenterLocalHom_comap_maximalIdeal
    {F E : Type*} [Field F] [Field E] [Algebra F E]
    (f : E) (hf : Transcendental F f)
    (v : AddValuation E (WithTop ℤ)) (hF : ∀ c : F, 0 ≤ v (algebraMap F E c))
    (hvf : 0 ≤ v f) :
    (IsLocalRing.maximalIdeal v.toValuation.valuationSubring).comap
      (parameterCenterLocalHom f hf v hF hvf) =
    IsLocalRing.maximalIdeal (Localization.AtPrime (parameterValuationCenter f hf v hF hvf)) := by logtwo_quiet
  apply (Localization.AtPrime.eq_maximalIdeal_iff_under_eq
    (I := parameterValuationCenter f hf v hF hvf)).mp
  ext x
  change parameterCenterLocalHom f hf v hF hvf
    (algebraMap (parameterChart f hf) _ x) ∈
      IsLocalRing.maximalIdeal v.toValuation.valuationSubring ↔ _
  rw [parameterCenterLocalHom_algebraMap]
  rfl

theorem parameterCenterLocalHom_coe
    {F E : Type*} [Field F] [Field E] [Algebra F E]
    (f : E) (hf : Transcendental F f)
    (v : AddValuation E (WithTop ℤ)) (hF : ∀ c : F, 0 ≤ v (algebraMap F E c))
    (hvf : 0 ≤ v f)
    [Algebra (Localization.AtPrime (parameterValuationCenter f hf v hF hvf)) E]
    [IsScalarTower (parameterChart f hf)
      (Localization.AtPrime (parameterValuationCenter f hf v hF hvf)) E]
    (a : Localization.AtPrime (parameterValuationCenter f hf v hF hvf)) :
    (parameterCenterLocalHom f hf v hF hvf a : E) = algebraMap _ E a := by logtwo_quiet
  have hm : v.toValuation.valuationSubring.subtype.comp
      (parameterCenterLocalHom f hf v hF hvf) = algebraMap _ E := by logtwo_quiet
    apply IsLocalization.ringHom_ext (parameterValuationCenter f hf v hF hvf).primeCompl
    ext x
    simp only [RingHom.comp_apply]
    rw [parameterCenterLocalHom_algebraMap]
    exact (IsScalarTower.algebraMap_apply (parameterChart f hf)
      (Localization.AtPrime (parameterValuationCenter f hf v hF hvf)) E x)
  exact RingHom.congr_fun hm a

theorem parameterCenterLocal_nonneg
    {F E : Type*} [Field F] [Field E] [Algebra F E]
    (f : E) (hf : Transcendental F f)
    (v : AddValuation E (WithTop ℤ)) (hF : ∀ c : F, 0 ≤ v (algebraMap F E c))
    (hvf : 0 ≤ v f)
    [Algebra (Localization.AtPrime (parameterValuationCenter f hf v hF hvf)) E]
    [IsScalarTower (parameterChart f hf)
      (Localization.AtPrime (parameterValuationCenter f hf v hF hvf)) E]
    (a : Localization.AtPrime (parameterValuationCenter f hf v hF hvf)) :
    0 ≤ v (algebraMap _ E a) := by logtwo_quiet
  rw [← parameterCenterLocalHom_coe f hf v hF hvf a]
  exact (parameterCenterLocalHom f hf v hF hvf a).property

theorem parameterCenterLocal_positive
    {F E : Type*} [Field F] [Field E] [Algebra F E]
    (f : E) (hf : Transcendental F f)
    (v : AddValuation E (WithTop ℤ)) (hF : ∀ c : F, 0 ≤ v (algebraMap F E c))
    (hvf : 0 ≤ v f)
    [Algebra (Localization.AtPrime (parameterValuationCenter f hf v hF hvf)) E]
    [IsScalarTower (parameterChart f hf)
      (Localization.AtPrime (parameterValuationCenter f hf v hF hvf)) E]
    (a : Localization.AtPrime (parameterValuationCenter f hf v hF hvf))
    (ha : a ∈ IsLocalRing.maximalIdeal _) : 0 < v (algebraMap _ E a) := by logtwo_quiet
  rw [← parameterCenterLocalHom_coe f hf v hF hvf a]
  apply v.toValuation.mem_maximalIdeal_iff.mp
  change a ∈ (IsLocalRing.maximalIdeal v.toValuation.valuationSubring).comap
    (parameterCenterLocalHom f hf v hF hvf)
  rw [parameterCenterLocalHom_comap_maximalIdeal]
  exact ha

theorem primeFieldValuation_algebraMap_localOrder
    (S E : Type*) [CommRing S] [IsDedekindDomain S]
    [Field E] [Algebra S E] [IsFractionRing S E]
    (q : IsDedekindDomain.HeightOneSpectrum S) (a : S) :
    letI := IsLocalization.AtPrime.isDiscreteValuationRing_of_dedekind_domain S q.ne_bot
      (Localization.AtPrime q.asIdeal)
    primeFieldValuation S E q (algebraMap S E a) =
      CurveLocalOrder.enatToIntegerOrder
        (IsDiscreteValuationRing.addVal (Localization.AtPrime q.asIdeal)
          (algebraMap S (Localization.AtPrime q.asIdeal) a)) := by logtwo_quiet
  let A := Localization.AtPrime q.asIdeal
  let := IsLocalization.localizationAlgebraOfSubmonoidLe A E
    q.asIdeal.primeCompl S⁰ q.asIdeal.primeCompl_le_nonZeroDivisors
  let := IsLocalization.localization_isScalarTower_of_submonoid_le A E
    q.asIdeal.primeCompl S⁰ q.asIdeal.primeCompl_le_nonZeroDivisors
  let := IsFractionRing.isFractionRing_of_isDomain_of_isLocalization q.asIdeal.primeCompl A E
  let := IsLocalization.AtPrime.isDiscreteValuationRing_of_dedekind_domain S q.ne_bot A
  change CurveLocalOrder.fractionAddValuation A E (algebraMap S E a) = _
  rw [IsScalarTower.algebraMap_apply S A E, CurveLocalOrder.fractionAddValuation_algebraMap]
  rfl

theorem primeFieldValuation_algebraMap_nonneg
    (S E : Type*) [CommRing S] [IsDedekindDomain S]
    [Field E] [Algebra S E] [IsFractionRing S E]
    (q : IsDedekindDomain.HeightOneSpectrum S) (a : S) :
    0 ≤ primeFieldValuation S E q (algebraMap S E a) := by logtwo_quiet
  rw [primeFieldValuation_algebraMap_localOrder]
  exact CurveLocalOrder.enatToIntegerOrder_monotone (show (0 : ℕ∞) ≤ _ from zero_le)

theorem enatToIntegerOrder_pos_iff (n : ℕ∞) :
    0 < CurveLocalOrder.enatToIntegerOrder n ↔ 0 < n := by logtwo_quiet
  rcases eq_or_ne n ⊤ with rfl | hn
  · simp
  obtain ⟨k, hk⟩ := ENat.ne_top_iff_exists.mp hn
  rw [← hk]
  simp

theorem primeFieldValuation_positive_iff
    (S E : Type*) [CommRing S] [IsDedekindDomain S]
    [Field E] [Algebra S E] [IsFractionRing S E]
    (q : IsDedekindDomain.HeightOneSpectrum S) (a : S) :
    0 < primeFieldValuation S E q (algebraMap S E a) ↔ a ∈ q.asIdeal := by logtwo_quiet
  let := IsLocalization.AtPrime.isDiscreteValuationRing_of_dedekind_domain S q.ne_bot
    (Localization.AtPrime q.asIdeal)
  rw [primeFieldValuation_algebraMap_localOrder, enatToIntegerOrder_pos_iff,
    pos_iff_ne_zero, ne_eq, IsDiscreteValuationRing.addVal_eq_zero_iff,
    IsLocalization.AtPrime.isUnit_to_map_iff (Localization.AtPrime q.asIdeal) q.asIdeal]
  simp

structure NormalizedPlace (F E : Type*) [Field F] [Field E] [Algebra F E] where
  valuation : AddValuation E (WithTop ℤ)
  constants_nonneg : ∀ c : F, 0 ≤ valuation (algebraMap F E c)
  normalized : ∃ z : Eˣ, WeightedCurveDegree.integerOrder valuation z = 1

@[ext] theorem NormalizedPlace.ext
    {F E : Type*} [Field F] [Field E] [Algebra F E]
    {p q : NormalizedPlace F E} (h : p.valuation = q.valuation) : p = q := by logtwo_quiet
  cases p
  cases q
  cases h
  rfl

theorem valuation_eq_parameterPlaceValuation
    {F E : Type*} [Field F] [CharZero F] [Field E] [Algebra F E]
    (f : E) (hf : Transcendental F f)
    [FiniteDimensional (IntermediateField.adjoin F {f}) E]
    (v : AddValuation E (WithTop ℤ)) (hF : ∀ c : F, 0 ≤ v (algebraMap F E c))
    (hvf : 0 < v f) (hnormalized : ∃ z : Eˣ, WeightedCurveDegree.integerOrder v z = 1) :
    v = parameterPlaceValuation f hf (parameterCenterPlace f hf v hF hvf) := by logtwo_quiet
  let := parameterAlgebra f hf
  let := parameterPolynomialAlgebra f hf
  let := parameter_scalarTower f hf
  let := parameter_finite f hf
  let S := parameterChart f hf
  let : Module.IsTorsionFree F[X] S :=
    Module.isTorsionFree_iff_algebraMap_injective.mpr
      (FunctionField.ringOfIntegers.algebraMap_injective F E)
  let q := parameterValuationCenter f hf v hF hvf.le
  have hq : q ≠ ⊥ :=
    Ideal.ne_bot_of_mem_primesOver (zeroPrime_ne_bot F)
      (parameterCenterPlace f hf v hF hvf).property
  let A := Localization.AtPrime q
  let := IsLocalization.localizationAlgebraOfSubmonoidLe A E
    q.primeCompl S⁰ q.primeCompl_le_nonZeroDivisors
  let := IsLocalization.localization_isScalarTower_of_submonoid_le A E
    q.primeCompl S⁰ q.primeCompl_le_nonZeroDivisors
  let := IsFractionRing.isFractionRing_of_isDomain_of_isLocalization q.primeCompl A E
  let := IsLocalization.AtPrime.isDiscreteValuationRing_of_dedekind_domain S hq A
  change v = CurveLocalOrder.fractionAddValuation A E
  apply PiExponent.DVRValuationUnique.eq_fractionAddValuation v
  · exact parameterCenterLocal_nonneg f hf v hF hvf.le
  · intro a ha _
    exact parameterCenterLocal_positive f hf v hF hvf.le a ha
  · exact hnormalized

theorem primeFieldValuation_normalized
    (S E : Type*) [CommRing S] [IsDedekindDomain S]
    [Field E] [Algebra S E] [IsFractionRing S E]
    (q : IsDedekindDomain.HeightOneSpectrum S) :
    ∃ z : Eˣ, WeightedCurveDegree.integerOrder (primeFieldValuation S E q) z = 1 := by logtwo_quiet
  let A := Localization.AtPrime q.asIdeal
  let := IsLocalization.localizationAlgebraOfSubmonoidLe A E
    q.asIdeal.primeCompl S⁰ q.asIdeal.primeCompl_le_nonZeroDivisors
  let := IsLocalization.localization_isScalarTower_of_submonoid_le A E
    q.asIdeal.primeCompl S⁰ q.asIdeal.primeCompl_le_nonZeroDivisors
  let := IsFractionRing.isFractionRing_of_isDomain_of_isLocalization q.asIdeal.primeCompl A E
  let := IsLocalization.AtPrime.isDiscreteValuationRing_of_dedekind_domain S q.ne_bot A
  exact PiExponent.DVRValuationUnique.fractionAddValuation_normalized

theorem parameterPlaceValuation_constants_nonneg
    {F E : Type*} [Field F] [CharZero F] [Field E] [Algebra F E]
    (f : E) (hf : Transcendental F f)
    [FiniteDimensional (IntermediateField.adjoin F {f}) E]
    (q : parameterZeroPlaces f hf) (c : F) :
    0 ≤ parameterPlaceValuation f hf q (algebraMap F E c) := by logtwo_quiet
  let := parameterAlgebra f hf
  let := parameterPolynomialAlgebra f hf
  let := parameter_scalarTower f hf
  let := parameter_finite f hf
  let S := parameterChart f hf
  let : Module.IsTorsionFree F[X] S :=
    Module.isTorsionFree_iff_algebraMap_injective.mpr
      (FunctionField.ringOfIntegers.algebraMap_injective F E)
  have hmap : algebraMap S E (algebraMap F[X] S (Polynomial.C c)) = algebraMap F E c := by logtwo_quiet
    rw [← IsScalarTower.algebraMap_apply F[X] S E,
      parameterPolynomialAlgebra_map f hf, Polynomial.aeval_C]
  change 0 ≤ primeFieldValuation S E (zeroFiberHeightOne F S q) (algebraMap F E c)
  rw [← hmap]
  exact primeFieldValuation_algebraMap_nonneg S E _ _

theorem parameterPlaceValuation_positive
    {F E : Type*} [Field F] [CharZero F] [Field E] [Algebra F E]
    (f : E) (hf : Transcendental F f)
    [FiniteDimensional (IntermediateField.adjoin F {f}) E]
    (q : parameterZeroPlaces f hf) : 0 < parameterPlaceValuation f hf q f := by logtwo_quiet
  let := parameterAlgebra f hf
  let := parameterPolynomialAlgebra f hf
  let := parameter_scalarTower f hf
  let := parameter_finite f hf
  let S := parameterChart f hf
  let : Module.IsTorsionFree F[X] S :=
    Module.isTorsionFree_iff_algebraMap_injective.mpr
      (FunctionField.ringOfIntegers.algebraMap_injective F E)
  have hmap : algebraMap S E (algebraMap F[X] S Polynomial.X) = f := by logtwo_quiet
    rw [← IsScalarTower.algebraMap_apply F[X] S E,
      parameterPolynomialAlgebra_map f hf, Polynomial.aeval_X]
  change 0 < primeFieldValuation S E (zeroFiberHeightOne F S q) f
  have hx : algebraMap F[X] S Polynomial.X ∈ q.1 := by logtwo_quiet
    apply (Ideal.mem_of_liesOver q.1 (zeroPrime F) Polynomial.X).mp
    change Polynomial.constantCoeff Polynomial.X = (0 : F)
    simp
  have hp := (primeFieldValuation_positive_iff S E (zeroFiberHeightOne F S q)
    (algebraMap F[X] S Polynomial.X)).mpr hx
  exact lt_of_lt_of_eq hp (congrArg (primeFieldValuation S E (zeroFiberHeightOne F S q)) hmap)

def parameterNormalizedPlace
    {F E : Type*} [Field F] [CharZero F] [Field E] [Algebra F E]
    (f : E) (hf : Transcendental F f)
    [FiniteDimensional (IntermediateField.adjoin F {f}) E]
    (q : parameterZeroPlaces f hf) : NormalizedPlace F E where
  valuation := parameterPlaceValuation f hf q
  constants_nonneg := parameterPlaceValuation_constants_nonneg f hf q
  normalized := by logtwo_quiet
    let := parameterAlgebra f hf
    let := parameterPolynomialAlgebra f hf
    let := parameter_scalarTower f hf
    let := parameter_finite f hf
    let S := parameterChart f hf
    let : Module.IsTorsionFree F[X] S :=
      Module.isTorsionFree_iff_algebraMap_injective.mpr
        (FunctionField.ringOfIntegers.algebraMap_injective F E)
    exact primeFieldValuation_normalized S E (zeroFiberHeightOne F S q)

theorem parameterCenterPlace_parameterNormalizedPlace
    {F E : Type*} [Field F] [CharZero F] [Field E] [Algebra F E]
    (f : E) (hf : Transcendental F f)
    [FiniteDimensional (IntermediateField.adjoin F {f}) E]
    (q : parameterZeroPlaces f hf) :
    parameterCenterPlace f hf (parameterNormalizedPlace f hf q).valuation
      (parameterNormalizedPlace f hf q).constants_nonneg
      (parameterPlaceValuation_positive f hf q) = q := by logtwo_quiet
  let := parameterAlgebra f hf
  let := parameterPolynomialAlgebra f hf
  let := parameter_scalarTower f hf
  let := parameter_finite f hf
  let S := parameterChart f hf
  let : Module.IsTorsionFree F[X] S :=
    Module.isTorsionFree_iff_algebraMap_injective.mpr
      (FunctionField.ringOfIntegers.algebraMap_injective F E)
  apply Subtype.ext
  apply Ideal.ext
  intro x
  change x ∈ parameterValuationCenter f hf (parameterNormalizedPlace f hf q).valuation
    (parameterNormalizedPlace f hf q).constants_nonneg _ ↔ x ∈ q.1
  rw [mem_parameterValuationCenter_iff]
  exact primeFieldValuation_positive_iff S E (zeroFiberHeightOne F S q) x

def positivePlaceEquivZeroPlaces
    {F E : Type*} [Field F] [CharZero F] [Field E] [Algebra F E]
    (f : E) (hf : Transcendental F f)
    [FiniteDimensional (IntermediateField.adjoin F {f}) E] :
    {p : NormalizedPlace F E // 0 < p.valuation f} ≃ parameterZeroPlaces f hf where
  toFun p := parameterCenterPlace f hf p.1.valuation p.1.constants_nonneg p.2
  invFun q := ⟨parameterNormalizedPlace f hf q, parameterPlaceValuation_positive f hf q⟩
  left_inv p := by logtwo_quiet
    apply Subtype.ext
    apply NormalizedPlace.ext
    exact (valuation_eq_parameterPlaceValuation f hf p.1.valuation
      p.1.constants_nonneg p.2 p.1.normalized).symm
  right_inv q := parameterCenterPlace_parameterNormalizedPlace f hf q

theorem finite_positivePlaces
    {F E : Type*} [Field F] [CharZero F] [Field E] [Algebra F E]
    (f : E) (hf : Transcendental F f)
    [FiniteDimensional (IntermediateField.adjoin F {f}) E] :
    Set.Finite {p : NormalizedPlace F E | 0 < p.valuation f} := by logtwo_quiet
  let := parameterZeroPlacesFintype f hf
  have : Finite {p : NormalizedPlace F E // 0 < p.valuation f} :=
    Finite.of_equiv (parameterZeroPlaces f hf) (positivePlaceEquivZeroPlaces f hf).symm
  exact Set.finite_coe_iff.mp this

end PiExponent.CurveValuationCenter

end

end OAI
end Source0031

-- Source: OAI/NumberTheory/PiExponent/Geometry/CurveProductFormula.lean
section Source0032
/-
Modification notice for the LogTwo project.
Derived from openai/math (Apache-2.0), revision adc7f1241b42e322a6451854ab7e4b4c146bf78a.
Original source: lean/OAI/NumberTheory/PiExponent/Geometry/CurveProductFormula.lean
Changes: Convert module/import declarations to the Lean 4.34 public module format.
See ../THIRD_PARTY_NOTICES.txt for provenance and the recorded changes.
-/

namespace OAI

noncomputable section
open scoped BigOperators
namespace PiExponent.CurveProductFormula
open PiExponent.CurveZeroPole PiExponent.CurveValuationCenter
open PiExponent.WeightedCurveDegree

def placeOrder {F E : Type*} [Field F] [Field E] [Algebra F E]
    (p : NormalizedPlace F E) (z : Eˣ) : ℤ := integerOrder p.valuation z

@[simp] theorem placeOrder_inv {F E : Type*} [Field F] [Field E] [Algebra F E]
    (p : NormalizedPlace F E) (z : Eˣ) : placeOrder p z⁻¹ = -placeOrder p z := by logtwo_quiet
  exact integerOrder_inv p.valuation z

theorem valuation_pos_iff_order_pos {F E : Type*} [Field F] [Field E] [Algebra F E]
    (p : NormalizedPlace F E) (z : Eˣ) : 0 < p.valuation (z : E) ↔ 0 < placeOrder p z := by logtwo_quiet
  rw [← coe_integerOrder]
  exact WithTop.coe_lt_coe

theorem order_ne_zero_iff_positive_or_inverse
    {F E : Type*} [Field F] [Field E] [Algebra F E]
    (p : NormalizedPlace F E) (z : Eˣ) :
    placeOrder p z ≠ 0 ↔ 0 < p.valuation (z : E) ∨ 0 < p.valuation ((z : E)⁻¹) := by logtwo_quiet
  rw [valuation_pos_iff_order_pos p z]
  rw [← Units.val_inv_eq_inv_val]
  rw [valuation_pos_iff_order_pos, placeOrder_inv]
  omega

def positivePlaces {F E : Type*} [Field F] [CharZero F] [Field E] [Algebra F E]
    (f : E) (hf : Transcendental F f)
    [FiniteDimensional (IntermediateField.adjoin F {f}) E] : Finset (NormalizedPlace F E) :=
  (finite_positivePlaces f hf).toFinset

@[simp] theorem mem_positivePlaces
    {F E : Type*} [Field F] [CharZero F] [Field E] [Algebra F E]
    (f : E) (hf : Transcendental F f)
    [FiniteDimensional (IntermediateField.adjoin F {f}) E] (p : NormalizedPlace F E) :
    p ∈ positivePlaces f hf ↔ 0 < p.valuation f := by logtwo_quiet
  classical
  exact (finite_positivePlaces f hf).mem_toFinset

abbrev positivePlacesFintype
    {F E : Type*} [Field F] [CharZero F] [Field E] [Algebra F E]
    (f : E) (hf : Transcendental F f)
    [FiniteDimensional (IntermediateField.adjoin F {f}) E] :
    Fintype {p : NormalizedPlace F E // 0 < p.valuation f} :=
  let := parameterZeroPlacesFintype f hf
  Fintype.ofEquiv (parameterZeroPlaces f hf) (positivePlaceEquivZeroPlaces f hf).symm

theorem sum_positiveOrders_eq
    {F E : Type*} [Field F] [CharZero F] [Field E] [Algebra F E]
    (f : E) (hf : Transcendental F f)
    [FiniteDimensional (IntermediateField.adjoin F {f}) E] :
    ∑ p ∈ positivePlaces f hf, placeOrder p (Units.mk0 f hf.ne_zero) = parameterZeroOrder f hf := by logtwo_quiet
  let := positivePlacesFintype f hf
  let := parameterZeroPlacesFintype f hf
  rw [Finset.sum_subtype (positivePlaces f hf) (mem_positivePlaces f hf)]
  calc
    _ = ∑ q : parameterZeroPlaces f hf,
        placeOrder (parameterNormalizedPlace f hf q) (Units.mk0 f hf.ne_zero) :=
      ((positivePlaceEquivZeroPlaces f hf).symm.sum_comp
        (fun p => placeOrder p.1 (Units.mk0 f hf.ne_zero))).symm
    _ = _ := (parameterZeroOrder_eq_sum f hf).symm

theorem finite_support_placeOrder
    {F E : Type*} [Field F] [CharZero F] [Field E] [Algebra F E]
    (f : E) (hf : Transcendental F f)
    [FiniteDimensional (IntermediateField.adjoin F {f}) E] :
    (Function.support (fun p : NormalizedPlace F E => placeOrder p (Units.mk0 f hf.ne_zero))).Finite := by logtwo_quiet
  let : FiniteDimensional (IntermediateField.adjoin F {f⁻¹}) E :=
    (adjoin_inverse_eq (F := F) f).symm ▸ inferInstance
  apply ((finite_positivePlaces f hf).union
    (finite_positivePlaces f⁻¹ (transcendental_inverse f hf))).subset
  intro p hp
  exact (order_ne_zero_iff_positive_or_inverse p (Units.mk0 f hf.ne_zero)).mp hp

def principalDivisor
    {F E : Type*} [Field F] [CharZero F] [Field E] [Algebra F E]
    (f : E) (hf : Transcendental F f)
    [FiniteDimensional (IntermediateField.adjoin F {f}) E] : NormalizedPlace F E →₀ ℤ :=
  Finsupp.ofSupportFinite (fun p => placeOrder p (Units.mk0 f hf.ne_zero))
    (finite_support_placeOrder f hf)

@[simp] theorem principalDivisor_apply
    {F E : Type*} [Field F] [CharZero F] [Field E] [Algebra F E]
    (f : E) (hf : Transcendental F f)
    [FiniteDimensional (IntermediateField.adjoin F {f}) E] (p : NormalizedPlace F E) :
    principalDivisor f hf p = placeOrder p (Units.mk0 f hf.ne_zero) := rfl

theorem principalDivisor_degree_zero
    {F E : Type*} [Field F] [CharZero F] [IsAlgClosed F] [Field E] [Algebra F E]
    (f : E) (hf : Transcendental F f)
    [FiniteDimensional (IntermediateField.adjoin F {f}) E] :
    (principalDivisor f hf).sum (fun _ n => n) = 0 := by logtwo_quiet
  classical
  let : FiniteDimensional (IntermediateField.adjoin F {f⁻¹}) E :=
    (adjoin_inverse_eq (F := F) f).symm ▸ inferInstance
  let z : Eˣ := Units.mk0 f hf.ne_zero
  let zi : Eˣ := Units.mk0 f⁻¹ (transcendental_inverse f hf).ne_zero
  have hiz : zi = z⁻¹ := by logtwo_quiet ext; simp [zi, z]
  have hsup : (principalDivisor f hf).support ⊆
      positivePlaces f hf ∪ positivePlaces f⁻¹ (transcendental_inverse f hf) := by logtwo_quiet
    intro p hp
    have hn : placeOrder p z ≠ 0 := by logtwo_quiet simpa [z] using Finsupp.mem_support_iff.mp hp
    simpa only [Finset.mem_union, mem_positivePlaces, z, Units.val_mk0] using
      (order_ne_zero_iff_positive_or_inverse p z).mp hn
  have hdisj : Disjoint (positivePlaces f hf)
      (positivePlaces f⁻¹ (transcendental_inverse f hf)) := by logtwo_quiet
    apply Finset.disjoint_left.mpr
    intro p hp hi
    have hp' : 0 < placeOrder p z :=
      (valuation_pos_iff_order_pos p z).mp ((mem_positivePlaces f hf p).mp hp)
    have hi' : 0 < placeOrder p zi :=
      (valuation_pos_iff_order_pos p zi).mp
        ((mem_positivePlaces f⁻¹ (transcendental_inverse f hf) p).mp hi)
    rw [hiz, placeOrder_inv] at hi'
    omega
  rw [Finsupp.sum_of_support_subset _ hsup _ (by logtwo_quiet intro _ _; rfl)]
  simp only [principalDivisor_apply]
  rw [Finset.sum_union hdisj, sum_positiveOrders_eq]
  have hi : (∑ p ∈ positivePlaces f⁻¹ (transcendental_inverse f hf), placeOrder p z) =
      -parameterZeroOrder f⁻¹ (transcendental_inverse f hf) := by logtwo_quiet
    calc
      _ = ∑ p ∈ positivePlaces f⁻¹ (transcendental_inverse f hf), -(placeOrder p zi) := by logtwo_quiet
        apply Finset.sum_congr rfl
        intro p _
        rw [hiz, placeOrder_inv, neg_neg]
      _ = -(∑ p ∈ positivePlaces f⁻¹ (transcendental_inverse f hf), placeOrder p zi) :=
        Finset.sum_neg_distrib (fun p => placeOrder p zi)
      _ = _ := congrArg Neg.neg (sum_positiveOrders_eq f⁻¹ (transcendental_inverse f hf))
  change parameterZeroOrder f hf + (∑ p ∈ positivePlaces f⁻¹ (transcendental_inverse f hf),
    placeOrder p z) = 0
  rw [hi, zero_pole_order_eq]
  exact add_neg_cancel _

theorem valuation_constant_eq_zero
    {F E : Type*} [Field F] [Field E] [Algebra F E]
    (p : NormalizedPlace F E) (c : F) (hc : c ≠ 0) :
    p.valuation (algebraMap F E c) = 0 := by logtwo_quiet
  let z : Eˣ := Units.mk0 (algebraMap F E c) ((map_ne_zero_iff _ (algebraMap F E).injective).mpr hc)
  have hpos : 0 ≤ integerOrder p.valuation z := by logtwo_quiet
    apply WithTop.coe_le_coe.mp
    rw [coe_integerOrder]
    exact p.constants_nonneg c
  have hinv : 0 ≤ integerOrder p.valuation z⁻¹ := by logtwo_quiet
    apply WithTop.coe_le_coe.mp
    rw [coe_integerOrder]
    simpa [z] using p.constants_nonneg c⁻¹
  rw [integerOrder_inv] at hinv
  have hz : integerOrder p.valuation z = 0 := by logtwo_quiet omega
  have he := coe_integerOrder p.valuation z
  rw [hz] at he
  exact he.symm

theorem placeOrder_constant_eq_zero
    {F E : Type*} [Field F] [Field E] [Algebra F E]
    (p : NormalizedPlace F E) (c : F) (hc : c ≠ 0) :
    placeOrder p (Units.mk0 (algebraMap F E c) ((map_ne_zero_iff _ (algebraMap F E).injective).mpr hc)) = 0 := by logtwo_quiet
  apply WithTop.coe_injective
  rw [placeOrder, coe_integerOrder]
  exact valuation_constant_eq_zero p c hc

end PiExponent.CurveProductFormula

end

end OAI
end Source0032

-- Source: OAI/NumberTheory/PiExponent/Jets/FormalBranchOrder.lean
section Source0033
-- Modified in this edition: unused plain lemmas removed; see reduction.json.
/-
Modification notice for the LogTwo project.
Derived from openai/math (Apache-2.0), revision adc7f1241b42e322a6451854ab7e4b4c146bf78a.
Original source: lean/OAI/NumberTheory/PiExponent/Jets/FormalBranchOrder.lean
Changes: Convert module/import declarations to the Lean 4.34 public module format.
See ../THIRD_PARTY_NOTICES.txt for provenance and the recorded changes.
-/

namespace OAI

noncomputable section

namespace PiExponent.FormalBranchOrder

open MvPowerSeries

variable {σ τ R S : Type*} [CommRing R] [CommRing S] [Algebra R S]

end PiExponent.FormalBranchOrder

end

end OAI
end Source0033

-- Source: OAI/NumberTheory/PiExponent/Jets/FormalBranchOrderRational.lean
section Source0034
-- Modified in this edition: unused plain lemmas removed; see reduction.json.
/-
Modification notice for the LogTwo project.
Derived from openai/math (Apache-2.0), revision adc7f1241b42e322a6451854ab7e4b4c146bf78a.
Original source: lean/OAI/NumberTheory/PiExponent/Jets/FormalBranchOrderRational.lean
Changes: Convert module/import declarations to the Lean 4.34 public module format.
See ../THIRD_PARTY_NOTICES.txt for provenance and the recorded changes.
-/

namespace OAI

noncomputable section

namespace PiExponent.FormalBranchOrder

open MvPowerSeries

variable {σ τ R S : Type*} [CommRing R] [CommRing S] [Algebra R S]

theorem rational_weight_le_of_contact
    (v : σ → ℚ) (μ : ℚ) (a : σ → MvPowerSeries τ S)
    (hcontact : ∀ i (k : ℕ), (a i).order = (k : ℕ∞) → μ * v i ≤ (k : ℚ))
    (d : σ →₀ ℕ) (n : ℕ)
    (hbound : d.weight (order ∘ a) ≤ (n : ℕ∞)) :
    μ * d.weight v ≤ (n : ℚ) := by logtwo_quiet
  classical
  have hfinite : ∀ i ∈ d.support, (a i).order ≠ ⊤ := by logtwo_quiet
    intro i hi
    apply ne_top_of_le_ne_top (by logtwo_quiet simp : (n : ℕ∞) ≠ ⊤)
    exact (Finsupp.le_weight_of_ne_zero' (order ∘ a)
      (Finsupp.mem_support_iff.mp hi)).trans hbound
  have hsum :
      ((∑ i ∈ d.support, d i * (a i).order.toNat : ℕ) : ℕ∞) =
        d.weight (order ∘ a) := by logtwo_quiet
    simp only [Nat.cast_sum, Nat.cast_mul, Finsupp.weight_apply,
      Finsupp.sum, Function.comp_apply, nsmul_eq_mul]
    apply Finset.sum_congr rfl
    intro i hi
    rw [ENat.natCast_toNat (hfinite i hi)]
  have hnat : (∑ i ∈ d.support, d i * (a i).order.toNat : ℕ) ≤ n := by logtwo_quiet
    exact_mod_cast hsum.symm ▸ hbound
  calc
    μ * d.weight v = ∑ i ∈ d.support, (d i : ℚ) * (μ * v i) := by logtwo_quiet
      simp only [Finsupp.weight_apply, Finsupp.sum, nsmul_eq_mul, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i hi
      ring
    _ ≤ ∑ i ∈ d.support, (d i : ℚ) * ((a i).order.toNat : ℚ) := by logtwo_quiet
      apply Finset.sum_le_sum
      intro i hi
      exact mul_le_mul_of_nonneg_left
        (hcontact i _ (ENat.natCast_toNat (hfinite i hi)).symm) (by logtwo_quiet positivity)
    _ ≤ (n : ℚ) := by logtwo_quiet exact_mod_cast hnat

theorem rational_order_subst_of_jet_vanishing
    (v : σ → ℚ) (μ H : ℚ) (hμ : 0 ≤ μ)
    (f : MvPowerSeries σ R) (a : σ → MvPowerSeries τ S)
    (ha : HasSubst a)
    (hjet : ∀ d : σ →₀ ℕ, d.weight v < H → coeff d f = 0)
    (hcontact : ∀ i (k : ℕ), (a i).order = (k : ℕ∞) → μ * v i ≤ (k : ℚ)) :
    (⌈μ * H⌉₊ : ℕ∞) ≤ (f.subst a).order := by logtwo_quiet
  classical
  by_cases htop : (f.subst a).order = ⊤
  · rw [htop]
    exact le_top
  obtain ⟨n, hn⟩ := ENat.ne_top_iff_exists.mp htop
  rw [← hn, ENat.natCast_le_natCast, Nat.ceil_le]
  obtain ⟨d, hd⟩ := ENat.exists_eq_iInf
    (fun d : σ →₀ ℕ => ⨅ _ : coeff d f ≠ 0, d.weight (order ∘ a))
  have hbound : (⨅ _ : coeff d f ≠ 0, d.weight (order ∘ a)) ≤ (n : ℕ∞) :=
    hd.le.trans ((le_weightedOrder_subst (fun _ : τ => 1) ha f).trans hn.ge)
  have hdne : coeff d f ≠ 0 := by logtwo_quiet
    intro he
    simp [he] at hbound
  have hbound' : d.weight (order ∘ a) ≤ (n : ℕ∞) := by logtwo_quiet
    simpa [hdne] using hbound
  have hH : H ≤ d.weight v := by logtwo_quiet
    by_contra! h
    exact hdne (hjet d h)
  exact (mul_le_mul_of_nonneg_left hH hμ).trans
    (rational_weight_le_of_contact v μ a hcontact d n hbound')

theorem rational_order_subst_of_mem_weightedIdeal
    (v : σ → ℚ) (hv : ∀ i, 0 ≤ v i) (μ H : ℚ) (hμ : 0 ≤ μ)
    (f : MvPowerSeries σ R) (a : σ → MvPowerSeries τ S)
    (ha : HasSubst a) (hf : f ∈ JetGeometry.rationalWeightedIdeal v hv H)
    (hcontact : ∀ i (k : ℕ), (a i).order = (k : ℕ∞) → μ * v i ≤ (k : ℚ)) :
    (⌈μ * H⌉₊ : ℕ∞) ≤ (f.subst a).order :=
  rational_order_subst_of_jet_vanishing v μ H hμ f a ha hf hcontact

theorem rational_powerSeries_order_subst_of_mem_weightedIdeal
    (v : σ → ℚ) (hv : ∀ i, 0 ≤ v i) (μ H : ℚ) (hμ : 0 ≤ μ)
    (f : MvPowerSeries σ R) (a : σ → PowerSeries S)
    (ha : HasSubst a) (hf : f ∈ JetGeometry.rationalWeightedIdeal v hv H)
    (hcontact : ∀ i (k : ℕ), (a i).order = (k : ℕ∞) → μ * v i ≤ (k : ℚ)) :
    (⌈μ * H⌉₊ : ℕ∞) ≤ PowerSeries.order (f.subst a) := by logtwo_quiet
  simp only [PowerSeries.order_eq_order] at hcontact ⊢
  exact rational_order_subst_of_mem_weightedIdeal v hv μ H hμ f a ha hf hcontact

end PiExponent.FormalBranchOrder

end

end OAI
end Source0034

-- Source: OAI/NumberTheory/PiExponent/Jets/BranchContact.lean
section Source0035
/-
Modification notice for the LogTwo project.
Derived from openai/math (Apache-2.0), revision adc7f1241b42e322a6451854ab7e4b4c146bf78a.
Original source: lean/OAI/NumberTheory/PiExponent/Jets/BranchContact.lean
Changes: Convert module/import declarations to the Lean 4.34 public module format.
See ../THIRD_PARTY_NOTICES.txt for provenance and the recorded changes.
-/

namespace OAI

noncomputable section
namespace PiExponent.BranchContact

variable {ι : Type*} [Fintype ι]

def active (a : ι → PowerSeries ℂ) : Finset ι := by logtwo_quiet
  classical
  exact Finset.univ.filter (fun i => a i ≠ 0)

@[simp] theorem mem_active (a : ι → PowerSeries ℂ) (i : ι) :
    i ∈ active a ↔ a i ≠ 0 := by logtwo_quiet
  classical
  simp [active]

theorem active_nonempty (a : ι → PowerSeries ℂ) (hne : ∃ i, a i ≠ 0) :
    (active a).Nonempty := by logtwo_quiet
  obtain ⟨i,hi⟩ := hne
  exact ⟨i,(mem_active a i).mpr hi⟩

def contact (v : ι → ℚ) (a : ι → PowerSeries ℂ) (hne : ∃ i, a i ≠ 0) : ℚ :=
  (active a).inf' (active_nonempty a hne) (fun i => ((a i).order.toNat : ℚ) / v i)

theorem contact_le (v : ι → ℚ) (a : ι → PowerSeries ℂ) (hne : ∃ i, a i ≠ 0)
    (i : ι) (hi : a i ≠ 0) :
    contact v a hne ≤ ((a i).order.toNat : ℚ) / v i :=
  Finset.inf'_le _ ((mem_active a i).mpr hi)

theorem exists_attains (v : ι → ℚ) (a : ι → PowerSeries ℂ) (hne : ∃ i, a i ≠ 0) :
    ∃ i, a i ≠ 0 ∧ contact v a hne = ((a i).order.toNat : ℚ) / v i := by logtwo_quiet
  obtain ⟨i,hi,he⟩ := Finset.exists_mem_eq_inf' (active_nonempty a hne)
    (fun i => ((a i).order.toNat : ℚ) / v i)
  exact ⟨i,(mem_active a i).mp hi,he⟩

theorem contact_pos (v : ι → ℚ) (hv : ∀ i, 0 < v i)
    (a : ι → PowerSeries ℂ) (hne : ∃ i, a i ≠ 0)
    (hc : ∀ i, PowerSeries.constantCoeff (a i) = 0) : 0 < contact v a hne := by logtwo_quiet
  obtain ⟨i,hi,he⟩ := exists_attains v a hne
  rw [he]
  apply div_pos _ (hv i)
  have horder := PowerSeries.one_le_order_iff_constCoeff_eq_zero.mpr (hc i)
  rw [← PowerSeries.coe_toNat_order hi] at horder
  have hnat : 1 ≤ (a i).order.toNat := by logtwo_quiet exact_mod_cast horder
  exact_mod_cast (show 0 < (a i).order.toNat by logtwo_quiet omega)

theorem contact_bound (v : ι → ℚ) (hv : ∀ i, 0 < v i)
    (a : ι → PowerSeries ℂ) (hne : ∃ i, a i ≠ 0) (i : ι) (k : ℕ)
    (hk : (a i).order = (k : ℕ∞)) : contact v a hne * v i ≤ (k : ℚ) := by logtwo_quiet
  have hi : a i ≠ 0 := by logtwo_quiet
    intro hz
    simp [hz] at hk
  have hnat : (a i).order.toNat = k := by logtwo_quiet simpa using congrArg ENat.toNat hk
  exact hnat ▸ (le_div_iff₀ (hv i)).mp (contact_le v a hne i hi)

theorem le_contact (v : ι → ℚ) (hv : ∀ i, 0 < v i)
    (a : ι → PowerSeries ℂ) (hne : ∃ i, a i ≠ 0) (μ : ℚ)
    (hμ : ∀ i (k : ℕ), (a i).order = (k : ℕ∞) → μ * v i ≤ (k : ℚ)) :
    μ ≤ contact v a hne := by logtwo_quiet
  apply Finset.le_inf'
  intro i hi
  apply (le_div_iff₀ (hv i)).mpr
  exact hμ i _ (PowerSeries.coe_toNat_order ((mem_active a i).mp hi)).symm

theorem order_add_lower (B : ℚ) (f g : PowerSeries ℂ)
    (hf : ∀ k : ℕ, f.order = (k : ℕ∞) → B ≤ (k : ℚ))
    (hg : ∀ k : ℕ, g.order = (k : ℕ∞) → B ≤ (k : ℚ))
    (k : ℕ) (hk : (f + g).order = (k : ℕ∞)) : B ≤ (k : ℚ) := by logtwo_quiet
  have hmin : min f.order g.order ≤ (k : ℕ∞) :=
    (PowerSeries.min_order_le_order_add f g).trans hk.le
  rcases min_le_iff.mp hmin with h | h
  · have hn : f.order ≠ ⊤ := ne_top_of_le_ne_top (by logtwo_quiet simp) h
    have he := ENat.natCast_toNat hn
    have hb := hf f.order.toNat he.symm
    have hnat : f.order.toNat ≤ k := by logtwo_quiet
      exact_mod_cast he.symm ▸ h
    exact hb.trans (by logtwo_quiet exact_mod_cast hnat)
  · have hn : g.order ≠ ⊤ := ne_top_of_le_ne_top (by logtwo_quiet simp) h
    have he := ENat.natCast_toNat hn
    have hb := hg g.order.toNat he.symm
    have hnat : g.order.toNat ≤ k := by logtwo_quiet
      exact_mod_cast he.symm ▸ h
    exact hb.trans (by logtwo_quiet exact_mod_cast hnat)

theorem exists_attaining_add (v : ι → ℚ) (hv : ∀ i, 0 < v i)
    (a t : ι → PowerSeries ℂ) (hne : ∃ i, a i ≠ 0)
    (ht : ∀ i (k : ℕ), (t i).order = (k : ℕ∞) → contact v a hne * v i < (k : ℚ)) :
    ∃ i, a i + t i ≠ 0 ∧ (a i + t i).order = (a i).order ∧
      contact v a hne = ((a i + t i).order.toNat : ℚ) / v i := by logtwo_quiet
  obtain ⟨i,hi,he⟩ := exists_attains v a hne
  have heq : contact v a hne * v i = ((a i).order.toNat : ℚ) :=
    (eq_div_iff (ne_of_gt (hv i))).mp he
  have hord : (a i).order < (t i).order := by logtwo_quiet
    by_cases hzero : t i = 0
    · simpa [hzero] using PowerSeries.order_finite_iff_ne_zero.mpr hi
    · have ht' := ht i (t i).order.toNat (PowerSeries.coe_toNat_order hzero).symm
      rw [heq] at ht'
      have hnat : (a i).order.toNat < (t i).order.toNat := by logtwo_quiet exact_mod_cast ht'
      rw [← PowerSeries.coe_toNat_order hi, ← PowerSeries.coe_toNat_order hzero]
      exact_mod_cast hnat
  have hsum : (a i + t i).order = (a i).order := by logtwo_quiet
    rw [PowerSeries.order_add_of_order_ne _ _ hord.ne, inf_eq_left.mpr hord.le]
  have hne' : a i + t i ≠ 0 := by logtwo_quiet
    intro hz
    have hh := PowerSeries.order_eq_top.mpr hz
    rw [hsum] at hh
    exact hi (PowerSeries.order_eq_top.mp hh)
  exact ⟨i,hne',hsum,hsum ▸ he⟩

theorem add_not_all_zero (v : ι → ℚ) (hv : ∀ i, 0 < v i)
    (a t : ι → PowerSeries ℂ) (hne : ∃ i, a i ≠ 0)
    (ht : ∀ i (k : ℕ), (t i).order = (k : ℕ∞) → contact v a hne * v i < (k : ℚ)) :
    ∃ i, a i + t i ≠ 0 := by logtwo_quiet
  obtain ⟨i,hi,_⟩ := exists_attaining_add v hv a t hne ht
  exact ⟨i,hi⟩

theorem contact_add_high_tail (v : ι → ℚ) (hv : ∀ i, 0 < v i)
    (a t : ι → PowerSeries ℂ) (hne : ∃ i, a i ≠ 0)
    (ht : ∀ i (k : ℕ), (t i).order = (k : ℕ∞) → contact v a hne * v i < (k : ℚ)) :
    contact v (fun i => a i + t i) (add_not_all_zero v hv a t hne ht) = contact v a hne := by logtwo_quiet
  apply le_antisymm
  · obtain ⟨i,hi,horder,he⟩ := exists_attaining_add v hv a t hne ht
    exact (contact_le v _ _ i hi).trans_eq he.symm
  · apply le_contact v hv _ _
    intro i k hk
    exact order_add_lower _ (a i) (t i) (contact_bound v hv a hne i)
      (fun n hn => (ht i n hn).le) k hk

end PiExponent.BranchContact

end

end OAI
end Source0035

-- Source: OAI/NumberTheory/PiExponent/Jets/DVRBranchExpansion.lean
section Source0036
/-
Modification notice for the LogTwo project.
Derived from openai/math (Apache-2.0), revision adc7f1241b42e322a6451854ab7e4b4c146bf78a.
Original source: lean/OAI/NumberTheory/PiExponent/Jets/DVRBranchExpansion.lean
Changes: Convert module/import declarations to the Lean 4.34 public module format.
See ../THIRD_PARTY_NOTICES.txt for provenance and the recorded changes.
-/

namespace OAI

noncomputable section
namespace PiExponent.DVRBranchExpansion
open PowerSeries

variable {C A : Type*} [Field C] [CommRing A] [Algebra C A]
variable (ρ : A →ₐ[C] C) (π : A) (hπ : π ≠ 0)
variable (hker : RingHom.ker ρ.toRingHom = Ideal.span {π})

include hker in

theorem residue_sub_dvd (a : A) : π ∣ a - algebraMap C A (ρ a) := by logtwo_quiet
  apply Ideal.mem_span_singleton.mp
  rw [← hker]
  change ρ (a - algebraMap C A (ρ a)) = 0
  simp

def remainder (a : A) : A := Classical.choose (residue_sub_dvd ρ π hker a)

theorem mul_remainder (a : A) : π * remainder ρ π hker a = a - algebraMap C A (ρ a) :=
  (Classical.choose_spec (residue_sub_dvd ρ π hker a)).symm

variable [IsDomain A]

include hπ in
@[simp] theorem remainder_add (a b : A) :
    remainder ρ π hker (a+b) = remainder ρ π hker a + remainder ρ π hker b := by logtwo_quiet
  apply mul_left_cancel₀ hπ
  rw [mul_add, mul_remainder, mul_remainder, mul_remainder, map_add, map_add]
  ring

include hπ in
@[simp] theorem remainder_smul (c : C) (a : A) :
    remainder ρ π hker (c • a) = c • remainder ρ π hker a := by logtwo_quiet
  apply mul_left_cancel₀ hπ
  rw [Algebra.smul_def, mul_remainder, map_mul, AlgHom.commutes, map_mul]
  rw [Algebra.smul_def, mul_left_comm, mul_remainder]
  simp only [Algebra.algebraMap_self, RingHom.id_apply]
  ring

include hπ in
@[simp] theorem remainder_algebraMap (c : C) :
    remainder ρ π hker (algebraMap C A c) = 0 := by logtwo_quiet
  apply mul_left_cancel₀ hπ
  rw [mul_zero, mul_remainder, AlgHom.commutes]
  simp

include hker in
omit [IsDomain A] in
theorem residue_uniformizer : ρ π = 0 := by logtwo_quiet
  change π ∈ RingHom.ker ρ.toRingHom
  rw [hker]
  exact Ideal.subset_span (by logtwo_quiet simp)

include hπ in
@[simp] theorem remainder_uniformizer_mul (a : A) :
    remainder ρ π hker (π*a) = a := by logtwo_quiet
  apply mul_left_cancel₀ hπ
  rw [mul_remainder, map_mul, residue_uniformizer ρ π hker, zero_mul, map_zero, sub_zero]

def remainderLinear : A →ₗ[C] A where
  toFun := remainder ρ π hker
  map_add' := remainder_add ρ π hπ hker
  map_smul' := remainder_smul ρ π hπ hker

def expansionCoeff (n : ℕ) (a : A) : C := ρ ((remainderLinear ρ π hπ hker ^ n) a)

@[simp] theorem expansionCoeff_zero (a : A) : expansionCoeff ρ π hπ hker 0 a = ρ a := rfl

@[simp] theorem expansionCoeff_succ (n : ℕ) (a : A) :
    expansionCoeff ρ π hπ hker (n+1) a =
      expansionCoeff ρ π hπ hker n (remainder ρ π hker a) := by logtwo_quiet
  simp only [expansionCoeff, pow_succ, Module.End.mul_apply]
  rfl

@[simp] theorem expansionCoeff_add (n : ℕ) (a b : A) :
    expansionCoeff ρ π hπ hker n (a+b) =
      expansionCoeff ρ π hπ hker n a + expansionCoeff ρ π hπ hker n b := by logtwo_quiet
  simp [expansionCoeff]

@[simp] theorem expansionCoeff_smul (n : ℕ) (c : C) (a : A) :
    expansionCoeff ρ π hπ hker n (c • a) = c * expansionCoeff ρ π hπ hker n a := by logtwo_quiet
  simp [expansionCoeff]

def expansion (a : A) : PowerSeries C := PowerSeries.mk (fun n => expansionCoeff ρ π hπ hker n a)

@[simp] theorem coeff_expansion (a : A) (n : ℕ) :
    PowerSeries.coeff n (expansion ρ π hπ hker a) = expansionCoeff ρ π hπ hker n a :=
  PowerSeries.coeff_mk _ _

@[simp] theorem expansion_add (a b : A) :
    expansion ρ π hπ hker (a+b) = expansion ρ π hπ hker a + expansion ρ π hπ hker b := by logtwo_quiet
  ext n
  simp only [map_add, coeff_expansion, expansionCoeff_add]

@[simp] theorem expansion_smul (c : C) (a : A) :
    expansion ρ π hπ hker (c • a) = c • expansion ρ π hπ hker a := by logtwo_quiet
  ext n
  simp only [map_smul, coeff_expansion, expansionCoeff_smul, smul_eq_mul]

@[simp] theorem expansion_algebraMap (c : C) :
    expansion ρ π hπ hker (algebraMap C A c) = PowerSeries.C c := by logtwo_quiet
  ext n
  cases n with
  | zero => simp
  | succ n =>
    rw [coeff_expansion, expansionCoeff_succ, remainder_algebraMap ρ π hπ hker]
    simp [expansionCoeff]

theorem expansion_rec (a : A) :
    expansion ρ π hπ hker a = PowerSeries.C (ρ a) +
      expansion ρ π hπ hker (remainder ρ π hker a) * PowerSeries.X := by logtwo_quiet
  ext n
  cases n with
  | zero => simp
  | succ n => simp only [map_add, coeff_expansion, PowerSeries.coeff_succ_C,
      PowerSeries.coeff_succ_mul_X, expansionCoeff_succ, zero_add]

include hπ in

theorem remainder_mul (a b : A) :
    remainder ρ π hker (a*b) = remainder ρ π hker a * b +
      algebraMap C A (ρ a) * remainder ρ π hker b := by logtwo_quiet
  apply mul_left_cancel₀ hπ
  rw [mul_add, ← mul_assoc, mul_remainder, mul_left_comm π,
    mul_remainder, mul_remainder, map_mul, map_mul]
  ring

theorem expansion_mul (a b : A) :
    expansion ρ π hπ hker (a*b) = expansion ρ π hπ hker a * expansion ρ π hπ hker b := by logtwo_quiet
  apply PowerSeries.ext
  intro n
  induction n generalizing a b with
  | zero =>
    simp only [coeff_expansion, expansionCoeff_zero, map_mul,
      PowerSeries.coeff_zero_eq_constantCoeff_apply]
    simp [← PowerSeries.coeff_zero_eq_constantCoeff_apply, coeff_expansion]
  | succ n ih =>
    calc
      PowerSeries.coeff (n+1) (expansion ρ π hπ hker (a*b)) =
          expansionCoeff ρ π hπ hker n (remainder ρ π hker (a*b)) := by logtwo_quiet
        rw [coeff_expansion, expansionCoeff_succ]
      _ = expansionCoeff ρ π hπ hker n (remainder ρ π hker a * b) +
          ρ a * expansionCoeff ρ π hπ hker n (remainder ρ π hker b) := by logtwo_quiet
        rw [remainder_mul ρ π hπ hker, ← Algebra.smul_def, expansionCoeff_add,
          expansionCoeff_smul]
      _ = PowerSeries.coeff n (expansion ρ π hπ hker (remainder ρ π hker a) *
          expansion ρ π hπ hker b) +
          ρ a * PowerSeries.coeff (n+1) (expansion ρ π hπ hker b) := by logtwo_quiet
        rw [← coeff_expansion, ih]
        rw [coeff_expansion, expansionCoeff_succ]
      _ = PowerSeries.coeff (n+1)
          ((expansion ρ π hπ hker (remainder ρ π hker a) * expansion ρ π hπ hker b) *
            PowerSeries.X + PowerSeries.C (ρ a) * expansion ρ π hπ hker b) := by logtwo_quiet
        simp only [map_add, PowerSeries.coeff_succ_mul_X, PowerSeries.coeff_C_mul]
      _ = PowerSeries.coeff (n+1) (expansion ρ π hπ hker a * expansion ρ π hπ hker b) := by logtwo_quiet
        conv_rhs => rw [expansion_rec ρ π hπ hker a]
        congr 1
        ring

def expansionHom : A →ₐ[C] PowerSeries C where
  toFun := expansion ρ π hπ hker
  map_zero' := by logtwo_quiet ext n; simp [expansionCoeff]
  map_one' := by logtwo_quiet simpa using expansion_algebraMap ρ π hπ hker (1 : C)
  map_add' := expansion_add ρ π hπ hker
  map_mul' := expansion_mul ρ π hπ hker
  commutes' := expansion_algebraMap ρ π hπ hker

@[simp] theorem constantCoeff_expansionHom (a : A) :
    PowerSeries.constantCoeff (expansionHom ρ π hπ hker a) = ρ a := by logtwo_quiet
  change PowerSeries.constantCoeff (expansion ρ π hπ hker a) = ρ a
  rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply, coeff_expansion, expansionCoeff_zero]

theorem expansionHom_uniformizer : expansionHom ρ π hπ hker π = PowerSeries.X := by logtwo_quiet
  change expansion ρ π hπ hker π = PowerSeries.X
  rw [expansion_rec, residue_uniformizer ρ π hker, map_zero, zero_add]
  have hr : remainder ρ π hker π = 1 := by logtwo_quiet
    simpa using remainder_uniformizer_mul ρ π hπ hker (1 : A)
  rw [hr]
  have he : expansion ρ π hπ hker (1 : A) = 1 := by logtwo_quiet
    simpa using expansion_algebraMap ρ π hπ hker (1 : C)
  rw [he, one_mul]

end PiExponent.DVRBranchExpansion

end

end OAI
end Source0036

-- Source: OAI/NumberTheory/PiExponent/Jets/DVRBranchOrder.lean
section Source0037
-- Modified in this edition: unused plain lemmas removed; see reduction.json.
/-
Modification notice for the LogTwo project.
Derived from openai/math (Apache-2.0), revision adc7f1241b42e322a6451854ab7e4b4c146bf78a.
Original source: lean/OAI/NumberTheory/PiExponent/Jets/DVRBranchOrder.lean
Changes: Convert module/import declarations to the Lean 4.34 public module format.
See ../THIRD_PARTY_NOTICES.txt for provenance and the recorded changes.
-/

namespace OAI

noncomputable section
namespace PiExponent.DVRBranchOrder

variable {A C : Type*} [CommRing A] [IsDomain A] [IsDiscreteValuationRing A] [Field C]

theorem order_eq_addVal (φ : A →+* PowerSeries C) (π : A)
    (hπ : Irreducible π) (hφπ : φ π = PowerSeries.X) (a : A) :
    PowerSeries.order (φ a) = IsDiscreteValuationRing.addVal A a := by logtwo_quiet
  by_cases ha : a = 0
  · subst a
    rw [map_zero, PowerSeries.order_zero, IsDiscreteValuationRing.addVal_zero]
  · obtain ⟨n, u, rfl⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible ha hπ
    rw [map_mul, map_pow, hφπ, PowerSeries.order_mul, PowerSeries.order_X_pow,
      PowerSeries.order_zero_of_isUnit (u.isUnit.map φ), zero_add,
      IsDiscreteValuationRing.addVal_def' u hπ]

theorem injective (φ : A →+* PowerSeries C) (π : A)
    (hπ : Irreducible π) (hφπ : φ π = PowerSeries.X) : Function.Injective φ := by logtwo_quiet
  intro a b hab
  have hz : φ (a - b) = 0 := by logtwo_quiet rw [map_sub, hab, sub_self]
  have ho := order_eq_addVal φ π hπ hφπ (a - b)
  rw [hz, PowerSeries.order_zero] at ho
  exact sub_eq_zero.mp (IsDiscreteValuationRing.addVal_eq_top_iff.mp ho.symm)

variable [Algebra C A]

theorem algHom_order_eq_addVal (φ : A →ₐ[C] PowerSeries C) (π : A)
    (hπ : Irreducible π) (hφπ : φ π = PowerSeries.X) (a : A) :
    PowerSeries.order (φ a) = IsDiscreteValuationRing.addVal A a :=
  order_eq_addVal φ.toRingHom π hπ hφπ a

theorem algHom_injective (φ : A →ₐ[C] PowerSeries C) (π : A)
    (hπ : Irreducible π) (hφπ : φ π = PowerSeries.X) : Function.Injective φ :=
  injective φ.toRingHom π hπ hφπ

end PiExponent.DVRBranchOrder
end

end OAI
end Source0037

-- Source: OAI/NumberTheory/PiExponent/Jets/DVRBranch.lean
section Source0038
-- Modified in this edition: unused plain lemmas removed; see reduction.json.
/-
Modification notice for the LogTwo project.
Derived from openai/math (Apache-2.0), revision adc7f1241b42e322a6451854ab7e4b4c146bf78a.
Original source: lean/OAI/NumberTheory/PiExponent/Jets/DVRBranch.lean
Changes: Convert module/import declarations to the Lean 4.34 public module format.
See ../THIRD_PARTY_NOTICES.txt for provenance and the recorded changes.
-/

namespace OAI

noncomputable section
namespace PiExponent.DVRBranch
open CurveLocalOrder

variable (C A : Type*) [Field C] [IsAlgClosed C] [CommRing A] [IsDomain A]
    [IsDiscreteValuationRing A] [Algebra C A]
    [Algebra.IsIntegral C (IsLocalRing.ResidueField A)]

def residueCoefficientMap : A →ₐ[C] C where
  toRingHom := residueAugmentation C A
  commutes' := residueAugmentation_algebraMap C A

@[simp] theorem residueCoefficientMap_ker :
    RingHom.ker (residueCoefficientMap C A).toRingHom = IsLocalRing.maximalIdeal A := by logtwo_quiet
  ext a
  change (residueCoefficientEquiv C A).symm (IsLocalRing.residue A a) = 0 ↔
    a ∈ IsLocalRing.maximalIdeal A
  rw [map_eq_zero_iff _ (AlgEquiv.injective _)]
  exact IsLocalRing.residue_eq_zero_iff a

def uniformizer : A := Classical.choose (IsDiscreteValuationRing.exists_irreducible A)

theorem uniformizer_irreducible : Irreducible (uniformizer A) :=
  Classical.choose_spec (IsDiscreteValuationRing.exists_irreducible A)

theorem residueCoefficientMap_ker_span :
    RingHom.ker (residueCoefficientMap C A).toRingHom = Ideal.span {uniformizer A} := by logtwo_quiet
  rw [residueCoefficientMap_ker, (uniformizer_irreducible A).maximalIdeal_eq]

def expansion : A →ₐ[C] PowerSeries C :=
  DVRBranchExpansion.expansionHom (residueCoefficientMap C A) (uniformizer A)
    (uniformizer_irreducible A).ne_zero (residueCoefficientMap_ker_span C A)

@[simp] theorem expansion_uniformizer : expansion C A (uniformizer A) = PowerSeries.X :=
  DVRBranchExpansion.expansionHom_uniformizer _ _ _ _

theorem expansion_order (a : A) :
    PowerSeries.order (expansion C A a) = IsDiscreteValuationRing.addVal A a :=
  DVRBranchOrder.algHom_order_eq_addVal (expansion C A) (uniformizer A)
    (uniformizer_irreducible A) (expansion_uniformizer C A) a

theorem expansion_injective : Function.Injective (expansion C A) :=
  DVRBranchOrder.algHom_injective (expansion C A) (uniformizer A)
    (uniformizer_irreducible A) (expansion_uniformizer C A)

@[simp] theorem expansion_constantCoeff (a : A) :
    PowerSeries.constantCoeff (expansion C A a) = residueAugmentation C A a :=
  DVRBranchExpansion.constantCoeff_expansionHom _ _ _ _ a

end PiExponent.DVRBranch

end

end OAI
end Source0038

-- Source: OAI/NumberTheory/PiExponent/Analysis/FormalLogTruncation.lean
section Source0039
-- Modified in this edition: unused plain lemmas removed; see reduction.json.
/-
Modification notice for the LogTwo project.
Derived from openai/math (Apache-2.0), revision adc7f1241b42e322a6451854ab7e4b4c146bf78a.
Original source: lean/OAI/NumberTheory/PiExponent/Analysis/FormalLogTruncation.lean
Changes: Convert module/import declarations to the Lean 4.34 public module format.
See ../THIRD_PARTY_NOTICES.txt for provenance and the recorded changes.
-/

namespace OAI

namespace PiExponent.FormalLogTruncation

open MvPowerSeries
open scoped BigOperators

variable {R : Type*} [CommRing R]

theorem liftSeries_eq_toMvPowerSeries (m : ℕ) (f : PowerSeries R) :
    FormalLogJet.liftSeries m f = f.toMvPowerSeries (0 : Fin (m+1)) := by logtwo_quiet
  classical
  let e : Unit ↪ Fin (m+1) := ⟨fun _ => 0, fun a b _ => Subsingleton.elim a b⟩
  ext d
  rw [FormalLogJet.coeff_liftSeries]
  change (if d.tail = 0 then PowerSeries.coeff (d 0) f else 0) = coeff d (rename e f)
  by_cases ht : d.tail = 0
  · rw [ite_eq_left ht]
    have hd : d = Finsupp.single 0 (d 0) := by logtwo_quiet
      calc
        d = Finsupp.cons (d 0) d.tail := (Finsupp.cons_tail d).symm
        _ = Finsupp.single 0 (d 0) := by logtwo_quiet rw [ht, Finsupp.cons_zero_eq_single_zero]
    have he : Finsupp.embDomain e (Finsupp.single () (d 0)) = Finsupp.single 0 (d 0) := by logtwo_quiet
      rw [Finsupp.embDomain_single]
      rfl
    conv_rhs => rw [hd, ← he, coeff_embDomain_rename]
    rfl
  · rw [ite_eq_right ht]
    symm
    apply coeff_rename_eq_zero
    rintro ⟨x, hx⟩
    have hx' : x = Finsupp.single () (x ()) := by logtwo_quiet ext; simp
    rw [hx', Finsupp.mapDomain_single] at hx
    apply ht
    rw [← hx]
    ext i
    change (Finsupp.single (0 : Fin (m+1)) (x ())) i.succ = 0
    exact Finsupp.single_eq_of_ne (Fin.succ_ne_zero i)

noncomputable def shiftVars {m : ℕ} (tail : Fin m → PowerSeries R) :
    Fin (m+1) → MvPowerSeries (Fin (m+1)) R :=
  Fin.cases (X 0) (fun i => X i.succ + (tail i).toMvPowerSeries 0)

theorem shiftVars_hasSubst {m : ℕ} (tail : Fin m → PowerSeries R)
    (ht : ∀ i, PowerSeries.constantCoeff (tail i) = 0) : HasSubst (shiftVars tail) := by logtwo_quiet
  apply hasSubst_of_constantCoeff_zero
  intro i
  cases i using Fin.cases with
  | zero => simp [shiftVars]
  | succ i =>
      simp only [shiftVars, Fin.cases_succ, map_add, constantCoeff_X,
        PowerSeries.toMvPowerSeries_apply, constantCoeff_rename, zero_add]
      exact ht i

noncomputable def shiftMap {m : ℕ} (tail : Fin m → PowerSeries R)
    (ht : ∀ i, PowerSeries.constantCoeff (tail i) = 0) :
    MvPowerSeries (Fin (m+1)) R →ₐ[R] MvPowerSeries (Fin (m+1)) R :=
  substAlgHom (shiftVars_hasSubst tail ht)

@[simp] theorem shiftMap_X_zero {m : ℕ} (tail : Fin m → PowerSeries R)
    (ht : ∀ i, PowerSeries.constantCoeff (tail i) = 0) :
    shiftMap tail ht (X 0) = X 0 := by logtwo_quiet
  rw [shiftMap, substAlgHom_X]
  rfl

@[simp] theorem shiftMap_X_succ {m : ℕ} (tail : Fin m → PowerSeries R)
    (ht : ∀ i, PowerSeries.constantCoeff (tail i) = 0) (i : Fin m) :
    shiftMap tail ht (X i.succ) = X i.succ + (tail i).toMvPowerSeries 0 := by logtwo_quiet
  rw [shiftMap, substAlgHom_X]
  rfl

@[simp] theorem shiftMap_toMvPowerSeries {m : ℕ} (tail : Fin m → PowerSeries R)
    (ht : ∀ i, PowerSeries.constantCoeff (tail i) = 0) (f : PowerSeries R) :
    shiftMap tail ht (f.toMvPowerSeries (0 : Fin (m+1))) = f.toMvPowerSeries 0 := by logtwo_quiet
  rw [shiftMap, substAlgHom_apply, PowerSeries.subst_toMvPowerSeries (shiftVars_hasSubst tail ht)]
  change PowerSeries.subst (X (0 : Fin (m+1))) f = f.toMvPowerSeries 0
  exact PowerSeries.toMvPowerSeries_eq_subst.symm

@[simp] theorem shiftMap_liftSeries {m : ℕ} (tail : Fin m → PowerSeries R)
    (ht : ∀ i, PowerSeries.constantCoeff (tail i) = 0) (f : PowerSeries R) :
    shiftMap tail ht (FormalLogJet.liftSeries m f) = FormalLogJet.liftSeries m f := by logtwo_quiet
  rw [liftSeries_eq_toMvPowerSeries, shiftMap_toMvPowerSeries]

@[simp] theorem shiftMap_apply {m : ℕ} (tail : Fin m → PowerSeries R)
    (ht : ∀ i, PowerSeries.constantCoeff (tail i) = 0) (f) :
    shiftMap tail ht f = subst (shiftVars tail) f := substAlgHom_apply _ _

theorem shiftMap_inverse {m : ℕ} (s t : Fin m → PowerSeries R)
    (hs : ∀ i, PowerSeries.constantCoeff (s i) = 0)
    (ht : ∀ i, PowerSeries.constantCoeff (t i) = 0)
    (hst : ∀ i, s i + t i = 0) (f : MvPowerSeries (Fin (m+1)) R) :
    shiftMap s hs (shiftMap t ht f) = f := by logtwo_quiet
  simp only [shiftMap_apply]
  rw [subst_comp_subst_apply (shiftVars_hasSubst t ht) (shiftVars_hasSubst s hs)]
  have hvars : (fun i => subst (shiftVars s) (shiftVars t i)) = X := by logtwo_quiet
    funext i
    rw [← shiftMap_apply s hs]
    cases i using Fin.cases with
    | zero => exact shiftMap_X_zero s hs
    | succ i =>
      change shiftMap s hs (X i.succ + (t i).toMvPowerSeries 0) = X i.succ
      rw [map_add, shiftMap_X_succ, shiftMap_toMvPowerSeries, add_assoc,
        ← map_add, hst i, map_zero, add_zero]
  rw [hvars]
  exact congrFun subst_self f

noncomputable def shiftEquiv {m : ℕ} (tail : Fin m → PowerSeries R)
    (ht : ∀ i, PowerSeries.constantCoeff (tail i) = 0) :
    MvPowerSeries (Fin (m+1)) R ≃ₐ[R] MvPowerSeries (Fin (m+1)) R := by logtwo_quiet
  let hn : ∀ i, PowerSeries.constantCoeff (-tail i) = 0 := by logtwo_quiet simp [ht]
  refine AlgEquiv.ofAlgHom (shiftMap tail ht) (shiftMap (fun i => -tail i) hn) ?_ ?_
  · apply AlgHom.ext
    intro f
    exact shiftMap_inverse tail (fun i => -tail i) ht hn (fun i => add_neg_cancel _) f
  · apply AlgHom.ext
    intro f
    exact shiftMap_inverse (fun i => -tail i) tail hn ht (fun i => neg_add_cancel _) f

@[simp] theorem shiftEquiv_apply {m : ℕ} (tail : Fin m → PowerSeries R)
    (ht : ∀ i, PowerSeries.constantCoeff (tail i) = 0) (f) :
    shiftEquiv tail ht f = shiftMap tail ht f := rfl

open JetGeometry

theorem rationalWeightedIdeal_prod {σ ι : Type*} (v : σ → ℚ) (hv : ∀ i, 0 ≤ v i)
    (s : Finset ι) (f : ι → MvPowerSeries σ R) (c : ι → ℚ)
    (hf : ∀ i ∈ s, f i ∈ rationalWeightedIdeal v hv (c i)) :
    ∏ i ∈ s, f i ∈ rationalWeightedIdeal v hv (∑ i ∈ s, c i) := by logtwo_quiet
  classical
  induction s using Finset.induction_on with
  | empty =>
    intro d hd
    simp only [Finset.sum_empty] at hd
    exact False.elim ((not_lt_of_ge (rational_weight_nonneg v hv d)) hd)
  | @insert i s hi ih =>
    rw [Finset.prod_insert hi, Finset.sum_insert hi]
    exact Ideal.mul_le.mp (rationalWeightedIdeal_mul_le v hv (c i) (∑j∈s,c j))
      _ (hf i (Finset.mem_insert_self _ _)) _
      (ih (fun j hj => hf j (Finset.mem_insert_of_mem hj)))

theorem subst_mem_rationalWeightedIdeal {σ τ : Type*}
    (w : σ → ℚ) (v : τ → ℚ) (hw : ∀ i, 0 ≤ w i) (hv : ∀ i, 0 ≤ v i)
    (a : σ → MvPowerSeries τ R) (ha : HasSubst a)
    (hweight : ∀ i, a i ∈ rationalWeightedIdeal v hv (w i))
    (H : ℚ) (f : MvPowerSeries σ R) (hf : f ∈ rationalWeightedIdeal w hw H) :
    subst a f ∈ rationalWeightedIdeal v hv H := by logtwo_quiet
  classical
  intro d hd
  rw [coeff_subst ha]
  apply finsum_eq_zero_of_forall_eq_zero
  intro e
  by_cases he : coeff e f = 0
  · rw [he, zero_smul]
  have hHe : H ≤ Finsupp.weight w e := le_of_not_gt (fun h => he (hf e h))
  have hprod : e.prod (fun i n => a i ^ n) ∈
      rationalWeightedIdeal v hv (Finsupp.weight w e) := by logtwo_quiet
    rw [Finsupp.prod, Finsupp.weight_apply, Finsupp.sum]
    apply rationalWeightedIdeal_prod
    intro i hi
    have hp := Ideal.pow_mem_pow (hweight i) (e i)
    have hh := ideal_pow_le_rationalWeightedIdeal v hv
      (rationalWeightedIdeal v hv (w i)) (w i) le_rfl (e i) hp
    simpa only [nsmul_eq_mul] using hh
  rw [hprod d (hd.trans_le hHe), smul_zero]

theorem X_mem_rationalWeightedIdeal {σ : Type*} (v : σ → ℚ) (hv : ∀ i, 0 ≤ v i)
    (i : σ) : (X i : MvPowerSeries σ R) ∈ rationalWeightedIdeal v hv (v i) := by logtwo_quiet
  classical
  intro d hd
  rw [coeff_X]
  split_ifs with he
  · subst d
    simp only [Finsupp.weight_single, one_nsmul] at hd
    exact False.elim (lt_irrefl _ hd)
  · rfl

theorem shiftMap_mem_rationalWeightedIdeal {m : ℕ} (tail : Fin m → PowerSeries R)
    (ht : ∀ i, PowerSeries.constantCoeff (tail i) = 0)
    (v : Fin (m+1) → ℚ) (hv : ∀ i, 0 ≤ v i)
    (hweight : ∀ i, (tail i).toMvPowerSeries (0 : Fin (m+1)) ∈
      rationalWeightedIdeal v hv (v i.succ)) (H : ℚ)
    (f : MvPowerSeries (Fin (m+1)) R) (hf : f ∈ rationalWeightedIdeal v hv H) :
    shiftMap tail ht f ∈ rationalWeightedIdeal v hv H := by logtwo_quiet
  rw [shiftMap_apply]
  apply subst_mem_rationalWeightedIdeal v v hv hv _ (shiftVars_hasSubst tail ht) _ H f hf
  intro i
  cases i using Fin.cases with
  | zero => exact X_mem_rationalWeightedIdeal v hv 0
  | succ i => exact Ideal.add_mem _ (X_mem_rationalWeightedIdeal v hv i.succ) (hweight i)

theorem rationalCoefficientPacket_eq_iff {σ : Type*} (v : σ → ℚ)
    (hv : ∀ i, 0 ≤ v i) (H : ℚ) (f g : MvPowerSeries σ R) :
    rationalCoefficientPacket v H f = rationalCoefficientPacket v H g ↔
      f - g ∈ rationalWeightedIdeal v hv H := by logtwo_quiet
  constructor
  · intro h d hd
    exact sub_eq_zero.mpr (congrFun h ⟨d,hd⟩)
  · intro h
    funext d
    exact sub_eq_zero.mp (h d.val d.property)

theorem rationalCoefficientPacket_surjective {σ : Type*} (v : σ → ℚ) (H : ℚ) :
    Function.Surjective (rationalCoefficientPacket (R := R) v H) := by logtwo_quiet
  classical
  intro p
  refine ⟨fun d => if hd : Finsupp.weight v d < H then p ⟨d,hd⟩ else 0, ?_⟩
  funext d
  exact dite_eq_left d.property

@[simp] theorem shiftEquiv_symm_apply {m : ℕ} (tail : Fin m → PowerSeries R)
    (ht : ∀ i, PowerSeries.constantCoeff (tail i) = 0) (f) :
    (shiftEquiv tail ht).symm f =
      shiftMap (fun i => -tail i) (by logtwo_quiet simp [ht]) f := rfl

theorem shiftEquiv_mem_iff {m : ℕ} (tail : Fin m → PowerSeries R)
    (ht : ∀ i, PowerSeries.constantCoeff (tail i) = 0)
    (v : Fin (m+1) → ℚ) (hv : ∀ i, 0 ≤ v i)
    (hweight : ∀ i, (tail i).toMvPowerSeries (0 : Fin (m+1)) ∈
      rationalWeightedIdeal v hv (v i.succ)) (H : ℚ) (f) :
    shiftEquiv tail ht f ∈ rationalWeightedIdeal v hv H ↔
      f ∈ rationalWeightedIdeal v hv H := by logtwo_quiet
  have hn : ∀ i, (-tail i).toMvPowerSeries (0 : Fin (m+1)) ∈
      rationalWeightedIdeal v hv (v i.succ) := by logtwo_quiet
    intro i
    rw [map_neg]
    intro d hd
    rw [map_neg, hweight i d hd, neg_zero]
  constructor
  · intro hf
    have h := shiftMap_mem_rationalWeightedIdeal (fun i => -tail i)
      (by logtwo_quiet simp [ht]) v hv hn H _ hf
    change (shiftEquiv tail ht).symm (shiftEquiv tail ht f) ∈ _ at h
    simpa only [AlgEquiv.symm_apply_apply] using h
  · exact shiftMap_mem_rationalWeightedIdeal tail ht v hv hweight H f

noncomputable def logTail (T : ℕ) : PowerSeries ℂ :=
  PowerSeries.log ℂ - (PowerSeries.trunc T (PowerSeries.log ℂ) : PowerSeries ℂ)

@[simp] theorem logTail_constantCoeff (T : ℕ) : PowerSeries.constantCoeff (logTail T) = 0 := by logtwo_quiet
  simp [logTail, Polynomial.constantCoeff_coe, PowerSeries.coeff_trunc,
    PowerSeries.coeff_log]

theorem coeff_logTail_eq_zero (T n : ℕ) (hn : n < T) :
    PowerSeries.coeff n (logTail T) = 0 := by logtwo_quiet
  simp [logTail, Polynomial.coeff_coe, PowerSeries.coeff_trunc, hn]

theorem logTail_mem_rationalWeightedIdeal {m : ℕ} (v : Fin (m+1) → ℚ)
    (hv : ∀ i, 0 ≤ v i) (T : ℕ) (H : ℚ) (hT : H ≤ (T : ℚ) * v 0) :
    (logTail T).toMvPowerSeries (0 : Fin (m+1)) ∈ rationalWeightedIdeal v hv H := by logtwo_quiet
  intro d hd
  rw [← liftSeries_eq_toMvPowerSeries, FormalLogJet.coeff_liftSeries]
  split_ifs with ht
  · have he : d = Finsupp.single 0 (d 0) := by logtwo_quiet
      calc
        d = Finsupp.cons (d 0) d.tail := (Finsupp.cons_tail d).symm
        _ = Finsupp.single 0 (d 0) := by logtwo_quiet rw [ht, Finsupp.cons_zero_eq_single_zero]
    have hdeg : (d 0 : ℚ) * v 0 < H := by logtwo_quiet
      calc
        (d 0 : ℚ) * v 0 = Finsupp.weight v (Finsupp.single 0 (d 0)) := by logtwo_quiet
          rw [Finsupp.weight_single, nsmul_eq_mul]
        _ = Finsupp.weight v d := congrArg _ he.symm
        _ < H := hd
    apply coeff_logTail_eq_zero
    by_contra hn
    have hcast : (T : ℚ) ≤ d 0 := by logtwo_quiet exact_mod_cast (Nat.le_of_not_gt hn)
    exact (not_lt_of_ge ((mul_le_mul_of_nonneg_right hcast (hv 0)).trans' hT)) hdeg
  · rfl

noncomputable def truncatedFormalJet {m : ℕ} (c : Fin m → ℂ) (T : Fin m → ℕ) :
    PiExponentApprox.FramePolynomial m →ₐ[ℂ] MvPowerSeries (Fin (m+1)) ℂ :=
  MvPolynomial.aeval (Fin.cases (1 + X 0) (fun i =>
    C (c i) + X i.succ + FormalLogJet.liftSeries m
      (PowerSeries.trunc (T i) (PowerSeries.log ℂ) : PowerSeries ℂ)))

theorem shiftMap_truncatedFormalJet {m : ℕ} (c : Fin m → ℂ) (T : Fin m → ℕ)
    (P : PiExponentApprox.FramePolynomial m) :
    shiftMap (fun i => logTail (T i)) (fun i => logTail_constantCoeff (T i))
      (truncatedFormalJet c T P) = FormalLogJet.formalJet c P := by logtwo_quiet
  have he : (shiftMap (fun i => logTail (T i)) (fun i => logTail_constantCoeff (T i))).comp
      (truncatedFormalJet c T) = FormalLogJet.formalJet c := by logtwo_quiet
    apply MvPolynomial.algHom_ext
    intro i
    cases i using Fin.cases with
    | zero =>
      simp only [AlgHom.comp_apply, truncatedFormalJet, MvPolynomial.aeval_X,
        Fin.cases_zero, FormalLogJet.formalJet_Y, map_add, map_one, shiftMap_X_zero]
    | succ i =>
      simp only [AlgHom.comp_apply, truncatedFormalJet, MvPolynomial.aeval_X,
        Fin.cases_succ, FormalLogJet.formalJet_X, map_add,
        shiftMap_X_succ, shiftMap_liftSeries]
      rw [← liftSeries_eq_toMvPowerSeries, logTail, map_sub, FormalLogJet.formalLog]
      have hc : shiftMap (fun i => logTail (T i)) (fun i => logTail_constantCoeff (T i))
          (C (c i)) = C (c i) := (shiftMap _ _).commutes (c i)
      rw [hc]
      ring
  exact DFunLike.congr_fun he P

theorem packets_surjective_comp_equiv {σ α J : Type*} (v : σ → ℚ)
    (hv : ∀ i, 0 ≤ v i) (H : ℚ)
    (e : MvPowerSeries σ R ≃ₐ[R] MvPowerSeries σ R)
    (he : ∀ f ∈ rationalWeightedIdeal v hv H, e f ∈ rationalWeightedIdeal v hv H)
    (f : α → J → MvPowerSeries σ R)
    (hf : Function.Surjective (fun a j => rationalCoefficientPacket v H (f a j))) :
    Function.Surjective (fun a j => rationalCoefficientPacket v H (e (f a j))) := by logtwo_quiet
  intro p
  choose F hF using fun j => rationalCoefficientPacket_surjective (R := R) v H (p j)
  obtain ⟨a,ha⟩ := hf (fun j => rationalCoefficientPacket v H (e.symm (F j)))
  refine ⟨a, ?_⟩
  funext j
  have hdiff := he _ ((rationalCoefficientPacket_eq_iff v hv H _ _).mp (congrFun ha j))
  rw [map_sub, e.apply_symm_apply] at hdiff
  exact ((rationalCoefficientPacket_eq_iff v hv H _ _).mpr hdiff).trans (hF j)

theorem packets_surjective_comp_equiv_iff {σ α J : Type*} (v : σ → ℚ)
    (hv : ∀ i, 0 ≤ v i) (H : ℚ)
    (e : MvPowerSeries σ R ≃ₐ[R] MvPowerSeries σ R)
    (he : ∀ f ∈ rationalWeightedIdeal v hv H, e f ∈ rationalWeightedIdeal v hv H)
    (hi : ∀ f ∈ rationalWeightedIdeal v hv H, e.symm f ∈ rationalWeightedIdeal v hv H)
    (f : α → J → MvPowerSeries σ R) :
    Function.Surjective (fun a j => rationalCoefficientPacket v H (e (f a j))) ↔
      Function.Surjective (fun a j => rationalCoefficientPacket v H (f a j)) := by logtwo_quiet
  constructor
  · intro h
    simpa only [e.symm_apply_apply] using
      packets_surjective_comp_equiv v hv H e.symm hi (fun a j => e (f a j)) h
  · exact packets_surjective_comp_equiv v hv H e he f

theorem formalLog_packets_surjective_iff_truncated {m : ℕ} {α J : Type*}
    (v : Fin (m+1) → ℚ) (hv : ∀ i, 0 ≤ v i) (H : ℚ)
    (T : Fin m → ℕ) (hT : ∀ i, v i.succ ≤ (T i : ℚ) * v 0)
    (c : J → Fin m → ℂ) (P : α → PiExponentApprox.FramePolynomial m) :
    Function.Surjective (fun a j => rationalCoefficientPacket v H (FormalLogJet.formalJet (c j) (P a))) ↔
      Function.Surjective (fun a j => rationalCoefficientPacket v H (truncatedFormalJet (c j) T (P a))) := by logtwo_quiet
  let tail := fun i => logTail (T i)
  let ht := fun i => logTail_constantCoeff (T i)
  let e := shiftEquiv tail ht
  have hw : ∀ i, (tail i).toMvPowerSeries (0 : Fin (m+1)) ∈
      rationalWeightedIdeal v hv (v i.succ) :=
    fun i => logTail_mem_rationalWeightedIdeal v hv (T i) (v i.succ) (hT i)
  have he : ∀ f ∈ rationalWeightedIdeal v hv H, e f ∈ rationalWeightedIdeal v hv H :=
    fun f hf => (shiftEquiv_mem_iff tail ht v hv hw H f).mpr hf
  have hi : ∀ f ∈ rationalWeightedIdeal v hv H, e.symm f ∈ rationalWeightedIdeal v hv H := by logtwo_quiet
    intro f hf
    apply (shiftEquiv_mem_iff tail ht v hv hw H (e.symm f)).mp
    change e (e.symm f) ∈ rationalWeightedIdeal v hv H
    simpa only [AlgEquiv.apply_symm_apply] using hf
  have hh := packets_surjective_comp_equiv_iff v hv H e he hi
    (fun a j => truncatedFormalJet (c j) T (P a))
  simpa only [e, tail, ht, shiftEquiv_apply, shiftMap_truncatedFormalJet] using hh

end PiExponent.FormalLogTruncation

end OAI
end Source0039

-- Source: OAI/NumberTheory/PiExponent/Jets/FormalBranchEvaluation.lean
section Source0040
/-
Modification notice for the LogTwo project.
Derived from openai/math (Apache-2.0), revision adc7f1241b42e322a6451854ab7e4b4c146bf78a.
Original source: lean/OAI/NumberTheory/PiExponent/Jets/FormalBranchEvaluation.lean
Changes: Convert module/import declarations to the Lean 4.34 public module format.
See ../THIRD_PARTY_NOTICES.txt for provenance and the recorded changes.
-/

namespace OAI

noncomputable section
namespace PiExponent.FormalBranchEvaluation
open MvPowerSeries
open FormalLogJet FormalLogTruncation

def branchCoordinates {m : ℕ} (c : Fin m → ℂ) (y : PowerSeries ℂ)
    (x : Fin m → PowerSeries ℂ) : Fin (m+1) → PowerSeries ℂ :=
  Fin.cases (y-1) (fun i => x i - PowerSeries.C (c i) -
    PowerSeries.subst (y-1) (PowerSeries.log ℂ))

theorem branchCoordinates_hasSubst {m : ℕ} (c : Fin m → ℂ) (y : PowerSeries ℂ)
    (x : Fin m → PowerSeries ℂ) (hy : PowerSeries.constantCoeff y = 1)
    (hx : ∀ i, PowerSeries.constantCoeff (x i) = c i) :
    HasSubst (branchCoordinates c y x) := by logtwo_quiet
  apply hasSubst_of_constantCoeff_zero
  intro i
  have ht : MvPowerSeries.constantCoeff (y-1) = 0 := by logtwo_quiet
    simpa only [map_sub, map_one, PowerSeries.constantCoeff_eq, sub_eq_zero] using hy
  cases i using Fin.cases with
  | zero => exact ht
  | succ i =>
    change MvPowerSeries.constantCoeff
      (x i - PowerSeries.C (c i) - PowerSeries.subst (y-1) (PowerSeries.log ℂ)) = 0
    rw [map_sub, PowerSeries.constantCoeff_subst_eq_zero ht _ (PowerSeries.constantCoeff_log),
      sub_zero, map_sub]
    change PowerSeries.constantCoeff (x i) - PowerSeries.constantCoeff (PowerSeries.C (c i)) = 0
    rw [hx i, PowerSeries.constantCoeff_C, sub_self]

theorem subst_liftSeries {m : ℕ} (a : Fin (m+1) → PowerSeries ℂ) (ha : HasSubst a)
    (f : PowerSeries ℂ) :
    subst a (liftSeries m f) = PowerSeries.subst (a 0) f := by logtwo_quiet
  rw [liftSeries_eq_toMvPowerSeries, PowerSeries.subst_toMvPowerSeries ha]

theorem formalJet_subst_branch {m : ℕ} (c : Fin m → ℂ) (y : PowerSeries ℂ)
    (x : Fin m → PowerSeries ℂ) (hy : PowerSeries.constantCoeff y = 1)
    (hx : ∀ i, PowerSeries.constantCoeff (x i) = c i)
    (p : PiExponentApprox.FramePolynomial m) :
    subst (branchCoordinates c y x) (formalJet c p) =
      MvPolynomial.aeval (Fin.cases y x) p := by logtwo_quiet
  let ha := branchCoordinates_hasSubst c y x hy hx
  have heq : (substAlgHom ha).comp (formalJet c) = MvPolynomial.aeval (Fin.cases y x) := by logtwo_quiet
    apply MvPolynomial.algHom_ext
    intro i
    cases i using Fin.cases with
    | zero =>
      simp only [AlgHom.comp_apply, formalJet_Y, map_add, map_one, substAlgHom_X,
        MvPolynomial.aeval_X, Fin.cases_zero]
      change 1 + (y-1) = y
      ring
    | succ i =>
      simp only [AlgHom.comp_apply, formalJet_X, map_add,
        MvPolynomial.aeval_X, Fin.cases_succ]
      rw [substAlgHom_X]
      have hl : substAlgHom ha (formalLog m) = PowerSeries.subst (y-1) (PowerSeries.log ℂ) := by logtwo_quiet
        rw [substAlgHom_apply, formalLog, subst_liftSeries _ ha]
        rfl
      rw [hl, substAlgHom_apply, subst_C]
      change PowerSeries.C (c i) +
        (x i - PowerSeries.C (c i) - PowerSeries.subst (y-1) (PowerSeries.log ℂ)) +
        PowerSeries.subst (y-1) (PowerSeries.log ℂ) = x i
      ring
  simpa only [AlgHom.comp_apply, substAlgHom_apply] using AlgHom.congr_fun heq p

theorem polynomialFrameWord_branch_order {m : ℕ}
    (c : Fin m → ℂ) (y : PowerSeries ℂ) (x : Fin m → PowerSeries ℂ)
    (hy : PowerSeries.constantCoeff y = 1)
    (hx : ∀ i, PowerSeries.constantCoeff (x i) = c i)
    (v : Fin (m+1) → ℚ) (hv : ∀ i, 0 ≤ v i) (μ H : ℚ) (hμ : 0 ≤ μ)
    (p : PiExponentApprox.FramePolynomial m)
    (hp : formalJet c p ∈ JetGeometry.rationalWeightedIdeal v hv H)
    (hcontact : ∀ i (k : ℕ), (branchCoordinates c y x i).order = (k : ℕ∞) →
      μ * v i ≤ (k : ℚ)) (word : List (Fin (m+1))) :
    (⌈μ * (H - (word.map v).sum)⌉₊ : ℕ∞) ≤
      PowerSeries.order (MvPolynomial.aeval (Fin.cases y x)
        (PiExponentApprox.polynomialFrameWord m word p)) := by logtwo_quiet
  have h := FormalBranchOrder.rational_powerSeries_order_subst_of_mem_weightedIdeal
    v hv μ (H - (word.map v).sum) hμ
    (formalJet c (PiExponentApprox.polynomialFrameWord m word p)) (branchCoordinates c y x)
    (branchCoordinates_hasSubst c y x hy hx)
    (formalJet_polynomialFrameWord_vanishing c v hv H p hp word) hcontact
  rwa [formalJet_subst_branch c y x hy hx] at h

theorem polynomialFrameWord_branch_order_toNat {m : ℕ}
    (c : Fin m → ℂ) (y : PowerSeries ℂ) (x : Fin m → PowerSeries ℂ)
    (hy : PowerSeries.constantCoeff y = 1)
    (hx : ∀ i, PowerSeries.constantCoeff (x i) = c i)
    (v : Fin (m+1) → ℚ) (hv : ∀ i, 0 ≤ v i) (μ H : ℚ) (hμ : 0 ≤ μ)
    (p : PiExponentApprox.FramePolynomial m)
    (hp : formalJet c p ∈ JetGeometry.rationalWeightedIdeal v hv H)
    (hcontact : ∀ i (k : ℕ), (branchCoordinates c y x i).order = (k : ℕ∞) →
      μ * v i ≤ (k : ℚ)) (word : List (Fin (m+1)))
    (hne : MvPolynomial.aeval (Fin.cases y x)
      (PiExponentApprox.polynomialFrameWord m word p) ≠ 0) :
    μ * (H - (word.map v).sum) ≤
      ((PowerSeries.order (MvPolynomial.aeval (Fin.cases y x)
        (PiExponentApprox.polynomialFrameWord m word p))).toNat : ℚ) := by logtwo_quiet
  have h := polynomialFrameWord_branch_order c y x hy hx v hv μ H hμ p hp hcontact word
  have hn := PowerSeries.order_eq_top.not.mpr hne
  have hh := ENat.toNat_le_toNat h hn
  exact Nat.ceil_le.mp (by logtwo_quiet simpa using hh)

end PiExponent.FormalBranchEvaluation

end

end OAI
end Source0040

-- Source: OAI/NumberTheory/PiExponent/Jets/DVRBranchJet.lean
section Source0041
/-
Modification notice for the LogTwo project.
Derived from openai/math (Apache-2.0), revision adc7f1241b42e322a6451854ab7e4b4c146bf78a.
Original source: lean/OAI/NumberTheory/PiExponent/Jets/DVRBranchJet.lean
Changes: Convert module/import declarations to the Lean 4.34 public module format.
See ../THIRD_PARTY_NOTICES.txt for provenance and the recorded changes.
-/

namespace OAI

noncomputable section
namespace PiExponent.DVRBranchJet
open PiExponentApprox FormalBranchEvaluation

variable {A : Type*} [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
    [Algebra ℂ A] [Algebra.IsIntegral ℂ (IsLocalRing.ResidueField A)]

theorem expansion_aeval {n : ℕ} (x : Fin n → A) (p : MvPolynomial (Fin n) ℂ) :
    DVRBranch.expansion ℂ A (MvPolynomial.aeval x p) =
      MvPolynomial.aeval (fun i => DVRBranch.expansion ℂ A (x i)) p := by logtwo_quiet
  have h : (DVRBranch.expansion ℂ A).comp (MvPolynomial.aeval x) =
      MvPolynomial.aeval (fun i => DVRBranch.expansion ℂ A (x i)) := by logtwo_quiet
    apply MvPolynomial.algHom_ext
    intro i
    simp
  exact AlgHom.congr_fun h p

def coordinates {m : ℕ} (c : Fin m → ℂ) (y : A) (x : Fin m → A) :
    Fin (m+1) → PowerSeries ℂ :=
  branchCoordinates c (DVRBranch.expansion ℂ A y)
    (fun i => DVRBranch.expansion ℂ A (x i))

theorem coordinates_centered {m : ℕ} (c : Fin m → ℂ) (y : A) (x : Fin m → A)
    (hy : CurveLocalOrder.residueAugmentation ℂ A y = 1)
    (hx : ∀ i, CurveLocalOrder.residueAugmentation ℂ A (x i) = c i) :
    ∀ i, PowerSeries.constantCoeff (coordinates c y x i) = 0 := by logtwo_quiet
  intro i
  have ht : MvPowerSeries.constantCoeff (DVRBranch.expansion ℂ A y - 1) = 0 := by logtwo_quiet
    change PowerSeries.constantCoeff (DVRBranch.expansion ℂ A y - 1) = 0
    simp [hy]
  cases i using Fin.cases with
  | zero => exact ht
  | succ i =>
    change PowerSeries.constantCoeff
      (DVRBranch.expansion ℂ A (x i) - PowerSeries.C (c i) -
        PowerSeries.subst (DVRBranch.expansion ℂ A y - 1) (PowerSeries.log ℂ)) = 0
    change MvPowerSeries.constantCoeff
      (DVRBranch.expansion ℂ A (x i) - PowerSeries.C (c i) -
        PowerSeries.subst (DVRBranch.expansion ℂ A y - 1) (PowerSeries.log ℂ)) = 0
    rw [map_sub, PowerSeries.constantCoeff_subst_eq_zero ht _ PowerSeries.constantCoeff_log,
      sub_zero, map_sub]
    change PowerSeries.constantCoeff (DVRBranch.expansion ℂ A (x i)) -
      PowerSeries.constantCoeff (PowerSeries.C (c i)) = 0
    rw [DVRBranch.expansion_constantCoeff, hx i, PowerSeries.constantCoeff_C, sub_self]

theorem coordinates_nonzero {m : ℕ} (c : Fin m → ℂ) (y : A) (x : Fin m → A)
    (hnc : y ≠ 1 ∨ ∃ i, x i ≠ algebraMap ℂ A (c i)) :
    ∃ i, coordinates c y x i ≠ 0 := by logtwo_quiet
  classical
  by_contra hn
  push Not at hn
  have hy : y = 1 := by logtwo_quiet
    apply DVRBranch.expansion_injective ℂ A
    have h0 := hn 0
    change DVRBranch.expansion ℂ A y - 1 = 0 at h0
    simpa only [map_one] using sub_eq_zero.mp h0
  rcases hnc with hnc | ⟨i, hi⟩
  · exact hnc hy
  · apply hi
    apply DVRBranch.expansion_injective ℂ A
    have hs := hn i.succ
    change DVRBranch.expansion ℂ A (x i) - PowerSeries.C (c i) -
      PowerSeries.subst (DVRBranch.expansion ℂ A y - 1) (PowerSeries.log ℂ) = 0 at hs
    rw [hy, map_one, sub_self,
      PowerSeries.subst_zero_of_constantCoeff_zero PowerSeries.constantCoeff_log, sub_zero] at hs
    rw [AlgHom.commutes]
    change DVRBranch.expansion ℂ A (x i) = PowerSeries.C (c i)
    exact sub_eq_zero.mp hs

def contact {m : ℕ} (v : Fin (m+1) → ℚ) (c : Fin m → ℂ) (y : A) (x : Fin m → A)
    (hnc : y ≠ 1 ∨ ∃ i, x i ≠ algebraMap ℂ A (c i)) : ℚ :=
  BranchContact.contact v (coordinates c y x) (coordinates_nonzero c y x hnc)

theorem contact_pos {m : ℕ} (v : Fin (m+1) → ℚ) (hv : ∀ i, 0 < v i)
    (c : Fin m → ℂ) (y : A) (x : Fin m → A)
    (hy : CurveLocalOrder.residueAugmentation ℂ A y = 1)
    (hx : ∀ i, CurveLocalOrder.residueAugmentation ℂ A (x i) = c i)
    (hnc : y ≠ 1 ∨ ∃ i, x i ≠ algebraMap ℂ A (c i)) :
    0 < contact v c y x hnc :=
  BranchContact.contact_pos v hv _ _ (coordinates_centered c y x hy hx)

theorem frameWord_addVal_lower {m : ℕ}
    (v : Fin (m+1) → ℚ) (hv : ∀ i, 0 < v i) (H : ℚ)
    (c : Fin m → ℂ) (y : A) (x : Fin m → A)
    (hy : CurveLocalOrder.residueAugmentation ℂ A y = 1)
    (hx : ∀ i, CurveLocalOrder.residueAugmentation ℂ A (x i) = c i)
    (hnc : y ≠ 1 ∨ ∃ i, x i ≠ algebraMap ℂ A (c i))
    (p : FramePolynomial m)
    (hp : FormalLogJet.formalJet c p ∈
      JetGeometry.rationalWeightedIdeal v (fun i => (hv i).le) H)
    (word : List (Fin (m+1)))
    (hne : MvPolynomial.aeval (Fin.cases y x) (polynomialFrameWord m word p) ≠ 0) :
    contact v c y x hnc * (H - (word.map v).sum) ≤
      ((IsDiscreteValuationRing.addVal A
        (MvPolynomial.aeval (Fin.cases y x) (polynomialFrameWord m word p))).toNat : ℚ) := by logtwo_quiet
  have heval (q : FramePolynomial m) :
      DVRBranch.expansion ℂ A (MvPolynomial.aeval (Fin.cases y x) q) =
      MvPolynomial.aeval (Fin.cases (DVRBranch.expansion ℂ A y)
        (fun i => DVRBranch.expansion ℂ A (x i))) q := by logtwo_quiet
    rw [expansion_aeval]
    apply congrArg (fun z => MvPolynomial.aeval z q)
    funext i
    cases i using Fin.cases <;> rfl
  have hne' : MvPolynomial.aeval (Fin.cases (DVRBranch.expansion ℂ A y)
      (fun i => DVRBranch.expansion ℂ A (x i))) (polynomialFrameWord m word p) ≠ 0 := by logtwo_quiet
    rw [← heval]
    exact (map_ne_zero_iff _ (DVRBranch.expansion_injective ℂ A)).mpr hne
  have hb := polynomialFrameWord_branch_order_toNat c (DVRBranch.expansion ℂ A y)
    (fun i => DVRBranch.expansion ℂ A (x i))
    (by logtwo_quiet simpa using hy) (fun i => by logtwo_quiet simpa using hx i)
    v (fun i => (hv i).le) (contact v c y x hnc) H
    (contact_pos v hv c y x hy hx hnc).le p hp
    (BranchContact.contact_bound v hv _ _) word hne'
  rw [← heval, DVRBranch.expansion_order] at hb
  exact hb

theorem frameWord_colength_lower {m : ℕ}
    (v : Fin (m+1) → ℚ) (hv : ∀ i, 0 < v i) (H : ℚ)
    (c : Fin m → ℂ) (y : A) (x : Fin m → A)
    (hy : CurveLocalOrder.residueAugmentation ℂ A y = 1)
    (hx : ∀ i, CurveLocalOrder.residueAugmentation ℂ A (x i) = c i)
    (hnc : y ≠ 1 ∨ ∃ i, x i ≠ algebraMap ℂ A (c i))
    (p : FramePolynomial m)
    (hp : FormalLogJet.formalJet c p ∈
      JetGeometry.rationalWeightedIdeal v (fun i => (hv i).le) H)
    (word : List (Fin (m+1)))
    (hne : MvPolynomial.aeval (Fin.cases y x) (polynomialFrameWord m word p) ≠ 0) :
    contact v c y x hnc * (H - (word.map v).sum) ≤
      ((Module.length A (A ⧸ Ideal.span {
        MvPolynomial.aeval (Fin.cases y x) (polynomialFrameWord m word p)})).toNat : ℚ) := by logtwo_quiet
  rw [CurveLocalOrder.length_quotient_span_eq_addVal hne]
  exact frameWord_addVal_lower v hv H c y x hy hx hnc p hp word hne

end PiExponent.DVRBranchJet

end

end OAI
end Source0041

-- Source: OAI/NumberTheory/PiExponent/Polynomials/PolynomialPoleBound.lean
section Source0042
-- Modified in this edition: unused plain lemmas removed; see reduction.json.
/-
Modification notice for the LogTwo project.
Derived from openai/math (Apache-2.0), revision adc7f1241b42e322a6451854ab7e4b4c146bf78a.
Original source: lean/OAI/NumberTheory/PiExponent/Polynomials/PolynomialPoleBound.lean
Changes: Convert module/import declarations to the Lean 4.34 public module format.
See ../THIRD_PARTY_NOTICES.txt for provenance and the recorded changes.
-/

namespace OAI

noncomputable section
open scoped BigOperators
namespace PiExponent.PolynomialPoleBound

variable {K C σ : Type*} [Field K] [CommRing C] [Algebra C K]

def realValuation (v : AddValuation K (WithTop ℤ)) : AddValuation K (WithTop ℝ) :=
  v.map { toAddMonoidHom := (Int.castAddHom ℝ).withTopMap
          monotone' := (show Monotone (fun z : ℤ => (z : ℝ)) from Int.cast_mono).withTop_map } rfl

@[simp] theorem realValuation_apply (v : AddValuation K (WithTop ℤ)) (x : K) :
    realValuation v x = WithTop.map (fun z : ℤ => (z : ℝ)) (v x) := rfl

theorem valuation_prod (v : AddValuation K (WithTop ℝ))
    (s : Finset σ) (f : σ → K) : v (∏ i ∈ s, f i) = ∑ i ∈ s, v (f i) := by logtwo_quiet
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert i s hi ih => simp [hi, ih]

theorem monomial_order_lower (v : AddValuation K (WithTop ℝ))
    (x : σ → K) (w : σ → ℝ) (D : ℝ)
    (hx : ∀ i, ((-w i * D : ℝ) : WithTop ℝ) ≤ v (x i))
    (hc : ∀ c : C, (0 : WithTop ℝ) ≤ v (algebraMap C K c))
    (d : σ →₀ ℕ) (c : C) :
    ((-Finsupp.weight w d * D : ℝ) : WithTop ℝ) ≤
      v (MvPolynomial.aeval x (MvPolynomial.monomial d c)) := by logtwo_quiet
  classical
  rw [MvPolynomial.aeval_monomial, v.map_mul, Finsupp.prod, valuation_prod]
  have heq : ((-Finsupp.weight w d * D : ℝ) : WithTop ℝ) =
      ∑ i ∈ d.support, d i • ((-w i * D : ℝ) : WithTop ℝ) := by logtwo_quiet
    simp only [← WithTop.coe_nsmul, ← WithTop.coe_sum]
    apply congrArg (fun r : ℝ => (r : WithTop ℝ))
    simp only [Finsupp.weight_apply, Finsupp.sum, nsmul_eq_mul,
      Finset.sum_mul, neg_mul]
    rw [← Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl
    intro i hi
    ring
  rw [heq]
  calc
    (∑ i ∈ d.support, d i • ((-w i * D : ℝ) : WithTop ℝ)) ≤
      ∑ i ∈ d.support, v (x i ^ d i) := by logtwo_quiet
        apply Finset.sum_le_sum
        intro i hi
        rw [v.map_pow]
        exact nsmul_le_nsmul_right (hx i) (d i)
    _ ≤ v (algebraMap C K c) + ∑ i ∈ d.support, v (x i ^ d i) :=
      le_add_of_nonneg_left (hc c)

theorem polynomial_order_lower (v : AddValuation K (WithTop ℝ))
    (x : σ → K) (w : σ → ℝ) (D N : ℝ) (hD : 0 ≤ D)
    (hx : ∀ i, ((-w i * D : ℝ) : WithTop ℝ) ≤ v (x i))
    (hc : ∀ c : C, (0 : WithTop ℝ) ≤ v (algebraMap C K c))
    (p : MvPolynomial σ C)
    (hp : ∀ d ∈ p.support, Finsupp.weight w d ≤ N) :
    ((-N * D : ℝ) : WithTop ℝ) ≤ v (MvPolynomial.aeval x p) := by logtwo_quiet
  classical
  rw [p.as_sum, map_sum]
  apply v.map_le_sum
  intro d hd
  have hnum : -N * D ≤ -Finsupp.weight w d * D :=
    mul_le_mul_of_nonneg_right (neg_le_neg (hp d hd)) hD
  exact (WithTop.coe_le_coe.mpr hnum).trans (monomial_order_lower v x w D hx hc d _)

end PiExponent.PolynomialPoleBound

end

end OAI
end Source0042

-- Source: OAI/NumberTheory/PiExponent/Polynomials/WeightedPolynomialPole.lean
section Source0043
-- Modified in this edition: unused plain lemmas removed; see reduction.json.
/-
Modification notice for the LogTwo project.
Derived from openai/math (Apache-2.0), revision adc7f1241b42e322a6451854ab7e4b4c146bf78a.
Original source: lean/OAI/NumberTheory/PiExponent/Polynomials/WeightedPolynomialPole.lean
Changes: Convert module/import declarations to the Lean 4.34 public module format.
See ../THIRD_PARTY_NOTICES.txt for provenance and the recorded changes.
-/

namespace OAI

noncomputable section
namespace PiExponent.WeightedPolynomialPole
open WeightedCurveDegree PolynomialPoleBound

variable {K ι : Type*} [Field K] [Fintype ι]

def coordinateOrder (v : AddValuation K (WithTop ℤ)) (x : K) : ℤ := by logtwo_quiet
  classical
  exact if h : x = 0 then 0 else integerOrder v (Units.mk0 x h)

def coordinatePole (v : AddValuation K (WithTop ℤ)) (x : ι → K) (w : ι → ℚ) : ℚ :=
  weightedPole w (fun i => (coordinateOrder v (x i) : ℚ))

@[simp] theorem realValuation_of_ne_zero (v : AddValuation K (WithTop ℤ))
    (x : K) (hx : x ≠ 0) :
    realValuation v x = ((coordinateOrder v x : ℝ) : WithTop ℝ) := by logtwo_quiet
  rw [coordinateOrder, dite_eq_right hx, realValuation_apply]
  have h : v x = (integerOrder v (Units.mk0 x hx) : WithTop ℤ) :=
    (coe_integerOrder v (Units.mk0 x hx)).symm
  rw [h, WithTop.map_coe]

theorem coordinate_order_lower (v : AddValuation K (WithTop ℤ))
    (x : ι → K) (w : ι → ℚ) (hw : ∀ i, 0 < w i) (i : ι) :
    ((-(w i : ℝ) * (coordinatePole v x w : ℝ) : ℝ) : WithTop ℝ) ≤
      realValuation v (x i) := by logtwo_quiet
  by_cases hx : x i = 0
  · simp [hx]
  · rw [realValuation_of_ne_zero v (x i) hx]
    apply WithTop.coe_le_coe.mpr
    have h := (div_le_iff₀ (hw i)).mp
      (div_le_weightedPole w (fun j => (coordinateOrder v (x j) : ℚ)) i)
    have hq : -(w i) * coordinatePole v x w ≤ (coordinateOrder v (x i) : ℚ) := by logtwo_quiet
      dsimp [coordinatePole]
      nlinarith
    exact_mod_cast hq

end PiExponent.WeightedPolynomialPole

end

end OAI
end Source0043

-- Source: OAI/NumberTheory/PiExponent/Geometry/CurveContactSum.lean
section Source0044
-- Modified in this edition: unused plain lemmas removed; see reduction.json.
/-
Modification notice for the LogTwo project.
Derived from openai/math (Apache-2.0), revision adc7f1241b42e322a6451854ab7e4b4c146bf78a.
Original source: lean/OAI/NumberTheory/PiExponent/Geometry/CurveContactSum.lean
Changes: Convert module/import declarations to the Lean 4.34 public module format.
See ../THIRD_PARTY_NOTICES.txt for provenance and the recorded changes.
-/

namespace OAI

noncomputable section
open scoped BigOperators
namespace PiExponent.CurveContactSum

open WeightedPolynomialPole WeightedCurveDegree CurveValuationCenter PolynomialPoleBound

theorem contact_sum_le_of_principal_sum
    {P : Type*} (z : P →₀ ℤ) (pole : P →₀ ℚ)
    (hz : z.sum (fun _ n => n) = 0) (hpole_nonneg : ∀ p, 0 ≤ pole p)
    (S : Finset P) (μ : P → ℝ) (N B : ℝ) (hN : 0 ≤ N)
    (hlocal : ∀ p ∈ S, B * μ p ≤ (z p : ℝ))
    (hglobal : ∀ p, -N * (pole p : ℝ) ≤ (z p : ℝ)) :
    B * (∑ p ∈ S, μ p) ≤ N * pole.sum (fun _ n => (n : ℝ)) := by logtwo_quiet
  classical
  let T := S ∪ z.support ∪ pole.support
  have hST : S ⊆ T := by logtwo_quiet intro p hp; simp [T, hp]
  have hzT : z.support ⊆ T := by logtwo_quiet intro p hp; simp [T, hp]
  have hpT : pole.support ⊆ T := by logtwo_quiet intro p hp; simp [T, hp]
  have hzsum : (∑ p ∈ T, (z p : ℝ)) = 0 := by logtwo_quiet
    have hh := z.sum_of_support_subset hzT (fun _ n => n) (by logtwo_quiet simp)
    have hi : (∑ p ∈ T, z p) = 0 := hh.symm.trans hz
    exact_mod_cast hi
  have hpsum : (∑ p ∈ T, (pole p : ℝ)) = pole.sum (fun _ n => (n : ℝ)) :=
    (pole.sum_of_support_subset hpT (fun _ n => (n : ℝ)) (by logtwo_quiet simp)).symm
  calc
    B * (∑ p ∈ S, μ p) = ∑ p ∈ S, B * μ p := Finset.mul_sum _ _ _
    _ ≤ ∑ p ∈ S, ((z p : ℝ) + N * (pole p : ℝ)) := by logtwo_quiet
      apply Finset.sum_le_sum
      intro p hp
      exact (hlocal p hp).trans (le_add_of_nonneg_right
        (mul_nonneg hN (by logtwo_quiet exact_mod_cast hpole_nonneg p)))
    _ ≤ ∑ p ∈ T, ((z p : ℝ) + N * (pole p : ℝ)) := by logtwo_quiet
      apply Finset.sum_le_sum_of_subset_of_nonneg hST
      intro p hp hnot
      have hh := hglobal p
      linarith
    _ = N * pole.sum (fun _ n => (n : ℝ)) := by logtwo_quiet
      rw [Finset.sum_add_distrib, ← Finset.mul_sum, hzsum, zero_add, hpsum]

theorem coordinatePole_eq_zero {E ι : Type*} [Field E] [Fintype ι]
    (v : AddValuation E (WithTop ℤ)) (x : ι → E) (w : ι → ℚ)
    (hx : ∀ i, coordinateOrder v (x i) = 0) : coordinatePole v x w = 0 := by logtwo_quiet
  unfold coordinatePole weightedPole
  simp only [hx, Int.cast_zero, neg_zero, zero_div]
  have he : (fun i : Option ι => i.elim 0 (fun _ => (0 : ℚ))) = fun _ => 0 := by logtwo_quiet
    funext i
    cases i <;> rfl
  rw [he]
  exact Finset.sup'_const _ _

theorem coordinatePole_finite_support {E ι P : Type*} [Field E] [Fintype ι]
    (v : P → AddValuation E (WithTop ℤ)) (x : ι → E) (w : ι → ℚ)
    (hfinite : ∀ i, Set.Finite {p | coordinateOrder (v p) (x i) ≠ 0}) :
    Set.Finite {p | coordinatePole (v p) x w ≠ 0} := by logtwo_quiet
  have hu : Set.Finite (⋃ i, {p | coordinateOrder (v p) (x i) ≠ 0}) :=
    Set.finite_iUnion (fun i => hfinite i)
  apply hu.subset
  intro p hp
  by_contra hn
  apply hp
  apply coordinatePole_eq_zero
  intro i
  by_contra hi
  exact hn (Set.mem_iUnion.mpr ⟨i,hi⟩)

theorem exists_constant_of_isAlgebraic {E : Type*} [Field E] [Algebra ℂ E]
    (f : E) (hf : IsAlgebraic ℂ f) : ∃ c : ℂ, algebraMap ℂ E c = f := by logtwo_quiet
  have hm : f ∈ algebraicClosure ℂ E := mem_algebraicClosure_iff.mpr hf
  rw [IntermediateField.eq_bot_of_isAlgClosed_of_isAlgebraic (algebraicClosure ℂ E)] at hm
  exact hm

theorem coordinateOrder_constant_eq_zero {E : Type*} [Field E] [Algebra ℂ E]
    (p : NormalizedPlace ℂ E) (c : ℂ) : coordinateOrder p.valuation (algebraMap ℂ E c) = 0 := by logtwo_quiet
  by_cases hc : c = 0
  · simp [hc, coordinateOrder]
  have hm : algebraMap ℂ E c ≠ 0 := (map_ne_zero_iff _ (algebraMap ℂ E).injective).mpr hc
  rw [coordinateOrder, dite_eq_right hm]
  exact CurveProductFormula.placeOrder_constant_eq_zero p c hc

def coordinateOrderDivisor {E : Type*} [Field E] [Algebra ℂ E]
    (hfinite : ∀ f : E, Transcendental ℂ f → FiniteDimensional (IntermediateField.adjoin ℂ {f}) E)
    (f : E) : NormalizedPlace ℂ E →₀ ℤ := by logtwo_quiet
  classical
  exact if ht : Transcendental ℂ f then
    letI := hfinite f ht
    CurveProductFormula.principalDivisor f ht
  else 0

@[simp] theorem coordinateOrderDivisor_apply {E : Type*} [Field E] [Algebra ℂ E]
    (hfinite : ∀ f : E, Transcendental ℂ f → FiniteDimensional (IntermediateField.adjoin ℂ {f}) E)
    (f : E) (p : NormalizedPlace ℂ E) :
    coordinateOrderDivisor hfinite f p = coordinateOrder p.valuation f := by logtwo_quiet
  classical
  by_cases ht : Transcendental ℂ f
  · let := hfinite f ht
    simp only [coordinateOrderDivisor, dite_eq_left ht, CurveProductFormula.principalDivisor_apply,
      coordinateOrder, dite_eq_right ht.ne_zero]
    rfl
  · rw [coordinateOrderDivisor, dite_eq_right ht]
    obtain ⟨c,rfl⟩ := exists_constant_of_isAlgebraic f (not_not.mp ht)
    exact (coordinateOrder_constant_eq_zero p c).symm

theorem coordinateOrderDivisor_degree_zero {E : Type*} [Field E] [Algebra ℂ E]
    (hfinite : ∀ f : E, Transcendental ℂ f → FiniteDimensional (IntermediateField.adjoin ℂ {f}) E)
    (f : E) : (coordinateOrderDivisor hfinite f).sum (fun _ n => n) = 0 := by logtwo_quiet
  classical
  by_cases ht : Transcendental ℂ f
  · let := hfinite f ht
    rw [coordinateOrderDivisor, dite_eq_left ht]
    exact CurveProductFormula.principalDivisor_degree_zero f ht
  · simp [coordinateOrderDivisor, ht]

def weightedPoleDivisor {E ι : Type*} [Field E] [Algebra ℂ E] [Fintype ι]
    (hfinite : ∀ f : E, Transcendental ℂ f → FiniteDimensional (IntermediateField.adjoin ℂ {f}) E)
    (x : ι → E) (w : ι → ℚ) : NormalizedPlace ℂ E →₀ ℚ :=
  Finsupp.ofSupportFinite (fun p => coordinatePole p.valuation x w)
    (coordinatePole_finite_support (fun p : NormalizedPlace ℂ E => p.valuation) x w (by logtwo_quiet
      intro i
      simpa only [Function.HasFiniteSupport, Function.support, coordinateOrderDivisor_apply] using
        (coordinateOrderDivisor hfinite (x i)).hasFiniteSupport))

@[simp] theorem weightedPoleDivisor_apply {E ι : Type*} [Field E] [Algebra ℂ E] [Fintype ι]
    (hfinite : ∀ f : E, Transcendental ℂ f → FiniteDimensional (IntermediateField.adjoin ℂ {f}) E)
    (x : ι → E) (w : ι → ℚ) (p : NormalizedPlace ℂ E) :
    weightedPoleDivisor hfinite x w p = coordinatePole p.valuation x w := rfl

def weightedDegree {E ι : Type*} [Field E] [Algebra ℂ E] [Fintype ι]
    (hfinite : ∀ f : E, Transcendental ℂ f → FiniteDimensional (IntermediateField.adjoin ℂ {f}) E)
    (x : ι → E) (w : ι → ℚ) : ℝ :=
  (weightedPoleDivisor hfinite x w).sum (fun _ n => (n : ℝ))

theorem weightedDegree_nonneg {E ι : Type*} [Field E] [Algebra ℂ E] [Fintype ι]
    (hfinite : ∀ f : E, Transcendental ℂ f → FiniteDimensional (IntermediateField.adjoin ℂ {f}) E)
    (x : ι → E) (w : ι → ℚ) : 0 ≤ weightedDegree hfinite x w := by logtwo_quiet
  apply Finset.sum_nonneg
  intro p hp
  change (0 : ℝ) ≤ (coordinatePole p.valuation x w : ℚ)
  exact_mod_cast weightedPole_nonneg w (fun i => (coordinateOrder p.valuation (x i) : ℚ))

theorem constants_real_nonneg {E : Type*} [Field E] [Algebra ℂ E]
    (p : NormalizedPlace ℂ E) (c : ℂ) :
    0 ≤ realValuation p.valuation (algebraMap ℂ E c) := by logtwo_quiet
  have h := (show Monotone (WithTop.map (fun z : ℤ => (z : ℝ))) from
    (Int.cast_mono (R := ℝ)).withTop_map) (p.constants_nonneg c)
  have hz : WithTop.map (fun z : ℤ => (z : ℝ)) (0 : WithTop ℤ) = (0 : WithTop ℝ) := by logtwo_quiet
    change (((0 : ℤ) : ℝ) : WithTop ℝ) = 0
    norm_num
  rw [hz] at h
  exact h

theorem polynomial_order_lower {E ι : Type*} [Field E] [Algebra ℂ E] [Fintype ι]
    (x : ι → E) (w : ι → ℚ) (hw : ∀ i, 0 < w i) (N : ℝ)
    (f : MvPolynomial ι ℂ)
    (hdegree : ∀ d ∈ f.support, Finsupp.weight (fun i => (w i : ℝ)) d ≤ N)
    (hne : MvPolynomial.aeval x f ≠ 0) (p : NormalizedPlace ℂ E) :
    -N * (coordinatePole p.valuation x w : ℝ) ≤
      (coordinateOrder p.valuation (MvPolynomial.aeval x f) : ℝ) := by logtwo_quiet
  have h := PolynomialPoleBound.polynomial_order_lower (realValuation p.valuation) x
    (fun i => (w i : ℝ)) (coordinatePole p.valuation x w : ℝ) N
    (by logtwo_quiet exact_mod_cast weightedPole_nonneg w (fun i => (coordinateOrder p.valuation (x i) : ℚ)))
    (coordinate_order_lower p.valuation x w hw) (constants_real_nonneg p) f hdegree
  rw [realValuation_of_ne_zero _ _ hne] at h
  exact WithTop.coe_le_coe.mp h

theorem polynomial_contact_sum_le {E ι : Type*} [Field E] [Algebra ℂ E] [Fintype ι]
    (hfinite : ∀ f : E, Transcendental ℂ f → FiniteDimensional (IntermediateField.adjoin ℂ {f}) E)
    (x : ι → E) (w : ι → ℚ) (hw : ∀ i, 0 < w i) (N B : ℝ) (hN : 0 ≤ N)
    (f : MvPolynomial ι ℂ)
    (hdegree : ∀ d ∈ f.support, Finsupp.weight (fun i => (w i : ℝ)) d ≤ N)
    (hne : MvPolynomial.aeval x f ≠ 0)
    (S : Finset (NormalizedPlace ℂ E)) (μ : NormalizedPlace ℂ E → ℝ)
    (hlocal : ∀ p ∈ S, B * μ p ≤
      (coordinateOrder p.valuation (MvPolynomial.aeval x f) : ℝ)) :
    B * (∑ p ∈ S, μ p) ≤ N * weightedDegree hfinite x w := by logtwo_quiet
  refine contact_sum_le_of_principal_sum
    (coordinateOrderDivisor hfinite (MvPolynomial.aeval x f)) (weightedPoleDivisor hfinite x w)
    (coordinateOrderDivisor_degree_zero hfinite _) ?_ S μ N B hN ?_ ?_
  · intro p
    exact weightedPole_nonneg w (fun i => (coordinateOrder p.valuation (x i) : ℚ))
  · intro p hp
    simpa only [coordinateOrderDivisor_apply] using hlocal p hp
  · intro p
    simpa only [weightedPoleDivisor_apply, coordinateOrderDivisor_apply] using
      polynomial_order_lower x w hw N f hdegree hne p

theorem polynomial_eq_zero_of_excess_contact
    {E ι : Type*} [Field E] [Algebra ℂ E] [Fintype ι]
    (hfinite : ∀ f : E, Transcendental ℂ f → FiniteDimensional (IntermediateField.adjoin ℂ {f}) E)
    (x : ι → E) (w : ι → ℚ) (hw : ∀ i, 0 < w i) (N B : ℝ) (hN : 0 ≤ N)
    (f : MvPolynomial ι ℂ)
    (hdegree : ∀ d ∈ f.support, Finsupp.weight (fun i => (w i : ℝ)) d ≤ N)
    (S : Finset (NormalizedPlace ℂ E)) (μ : NormalizedPlace ℂ E → ℝ)
    (hlocal : MvPolynomial.aeval x f ≠ 0 → ∀ p ∈ S, B * μ p ≤
      (coordinateOrder p.valuation (MvPolynomial.aeval x f) : ℝ))
    (hexcess : N * weightedDegree hfinite x w < B * (∑ p ∈ S, μ p)) :
    MvPolynomial.aeval x f = 0 := by logtwo_quiet
  by_contra hne
  exact (not_le_of_gt hexcess)
    (polynomial_contact_sum_le hfinite x w hw N B hN f hdegree hne S μ (hlocal hne))

end PiExponent.CurveContactSum

end

end OAI
end Source0044

-- Source: OAI/NumberTheory/PiExponent/Geometry/CurveCenters.lean
section Source0045
-- Modified in this edition: unused plain lemmas removed; see reduction.json.
/-
Modification notice for the LogTwo project.
Derived from openai/math (Apache-2.0), revision adc7f1241b42e322a6451854ab7e4b4c146bf78a.
Original source: lean/OAI/NumberTheory/PiExponent/Geometry/CurveCenters.lean
Changes: Convert module/import declarations to the Lean 4.34 public module format.
See ../THIRD_PARTY_NOTICES.txt for provenance and the recorded changes.
-/

namespace OAI

noncomputable section
namespace PiExponent.CurveCenters

open CurveValuationCenter

variable {E ι J : Type*} [Field E] [Algebra ℂ E]

def Centered (x : ι → E) (a : ι → ℂ) (p : NormalizedPlace ℂ E) : Prop :=
  ∀ i, 0 < p.valuation (x i - algebraMap ℂ E (a i))

theorem transcendental_sub_constant {x : E} (hx : Transcendental ℂ x) (c : ℂ) :
    Transcendental ℂ (x - algebraMap ℂ E c) := by logtwo_quiet
  intro h
  apply hx
  simpa only [sub_add_cancel] using h.add (isAlgebraic_algebraMap c)

theorem exists_transcendental_coordinate (x : ι → E)
    (hx : IntermediateField.adjoin ℂ (Set.range x) = ⊤)
    (hE : ∃ z : E, Transcendental ℂ z) : ∃ i, Transcendental ℂ (x i) := by logtwo_quiet
  by_contra hn
  push Not at hn
  have hle : IntermediateField.adjoin ℂ (Set.range x) ≤ ⊥ := by logtwo_quiet
    apply IntermediateField.adjoin_le_iff.mpr
    rintro _ ⟨i, rfl⟩
    obtain ⟨c, hc⟩ := CurveContactSum.exists_constant_of_isAlgebraic (x i) (by logtwo_quiet
      simpa only [Transcendental, not_not] using hn i)
    exact IntermediateField.mem_bot.mpr ⟨c, hc⟩
  obtain ⟨z, hz⟩ := hE
  have hzbot : z ∈ (⊥ : IntermediateField ℂ E) := hle (by logtwo_quiet simp [hx])
  obtain ⟨c, hc⟩ := IntermediateField.mem_bot.mp hzbot
  exact hz (hc ▸ isAlgebraic_algebraMap c)

theorem finite_centered (x : ι → E) (a : ι → ℂ)
    (hx : ∃ i, Transcendental ℂ (x i))
    (hfinite : ∀ g : E, Transcendental ℂ g →
      FiniteDimensional (IntermediateField.adjoin ℂ {g}) E) :
    Set.Finite {p : NormalizedPlace ℂ E | Centered x a p} := by logtwo_quiet
  obtain ⟨i, hi⟩ := hx
  have ht := transcendental_sub_constant hi (a i)
  let := hfinite (x i - algebraMap ℂ E (a i)) ht
  exact (finite_positivePlaces (x i - algebraMap ℂ E (a i)) ht).subset
    (fun p hp => hp i)

theorem finite_centered_family [Finite J] (x : ι → E) (a : J → ι → ℂ)
    (hx : ∃ i, Transcendental ℂ (x i))
    (hfinite : ∀ g : E, Transcendental ℂ g →
      FiniteDimensional (IntermediateField.adjoin ℂ {g}) E) :
    Set.Finite {p : NormalizedPlace ℂ E | ∃ j, Centered x (a j) p} := by logtwo_quiet
  have he : {p : NormalizedPlace ℂ E | ∃ j, Centered x (a j) p} =
      ⋃ j, {p : NormalizedPlace ℂ E | Centered x (a j) p} := by logtwo_quiet ext p; simp
  rw [he]
  exact Set.finite_iUnion (fun j => finite_centered x (a j) hx hfinite)

def centerPlaces [Finite J] (x : ι → E) (a : J → ι → ℂ)
    (hx : ∃ i, Transcendental ℂ (x i))
    (hfinite : ∀ g : E, Transcendental ℂ g →
      FiniteDimensional (IntermediateField.adjoin ℂ {g}) E) :
    Finset (NormalizedPlace ℂ E) :=
  (finite_centered_family x a hx hfinite).toFinset

@[simp] theorem mem_centerPlaces [Finite J] (x : ι → E) (a : J → ι → ℂ)
    (hx : ∃ i, Transcendental ℂ (x i))
    (hfinite : ∀ g : E, Transcendental ℂ g →
      FiniteDimensional (IntermediateField.adjoin ℂ {g}) E)
    (p : NormalizedPlace ℂ E) :
    p ∈ centerPlaces x a hx hfinite ↔ ∃ j, Centered x (a j) p :=
  (finite_centered_family x a hx hfinite).mem_toFinset

theorem Centered.constant_coordinate {x : ι → E} {a : ι → ℂ} {p : NormalizedPlace ℂ E}
    (ha : Centered x a p) (i : ι) (c : ℂ) (hc : x i = algebraMap ℂ E c) : c = a i := by logtwo_quiet
  by_contra hne
  have h := ha i
  rw [hc, ← map_sub, CurveProductFormula.valuation_constant_eq_zero p _ (sub_ne_zero.mpr hne)] at h
  exact lt_irrefl _ h

theorem Centered.coordinate_nonneg {x : ι → E} {a : ι → ℂ} {p : NormalizedPlace ℂ E}
    (ha : Centered x a p) (i : ι) : 0 ≤ p.valuation (x i) := by logtwo_quiet
  have h := (le_min (ha i).le (p.constants_nonneg (a i))).trans
    (p.valuation.map_add (x i - algebraMap ℂ E (a i)) (algebraMap ℂ E (a i)))
  simpa only [sub_add_cancel] using h

theorem Centered.exists_nonzero_difference (x : ι → E) (a : ι → ℂ)
    (hx : ∃ i, Transcendental ℂ (x i)) :
    ∃ i, x i ≠ algebraMap ℂ E (a i) := by logtwo_quiet
  obtain ⟨i, hi⟩ := hx
  refine ⟨i, ?_⟩
  intro he
  exact hi (he.symm ▸ isAlgebraic_algebraMap (a i))

end PiExponent.CurveCenters
end

end OAI
end Source0045

-- Source: OAI/NumberTheory/PiExponent/Geometry/PlaceValuationRing.lean
section Source0046
/-
Modification notice for the LogTwo project.
Derived from openai/math (Apache-2.0), revision adc7f1241b42e322a6451854ab7e4b4c146bf78a.
Original source: lean/OAI/NumberTheory/PiExponent/Geometry/PlaceValuationRing.lean
Changes: Convert module/import declarations to the Lean 4.34 public module format.
See ../THIRD_PARTY_NOTICES.txt for provenance and the recorded changes.
-/

namespace OAI

noncomputable section

namespace PiExponent.PlaceValuationRing

open CurveValuationCenter WeightedCurveDegree

variable {F E : Type*} [Field F] [Field E] [Algebra F E]

abbrev ring (p : NormalizedPlace F E) : ValuationSubring E :=
  p.valuation.toValuation.valuationSubring

def constantsHom (p : NormalizedPlace F E) : F →+* ring p where
  toFun c := ⟨algebraMap F E c, p.constants_nonneg c⟩
  map_zero' := by logtwo_quiet ext; exact map_zero _
  map_one' := by logtwo_quiet ext; exact map_one _
  map_add' _ _ := by logtwo_quiet ext; exact map_add _ _ _
  map_mul' _ _ := by logtwo_quiet ext; exact map_mul _ _ _

instance constantsAlgebra (p : NormalizedPlace F E) : Algebra F (ring p) :=
  (constantsHom p).toAlgebra

instance scalarTower (p : NormalizedPlace F E) : IsScalarTower F (ring p) E :=
  IsScalarTower.of_algebraMap_eq (fun _ => rfl)

@[simp] theorem constants_algebraMap (p : NormalizedPlace F E) (c : F) :
    (algebraMap F (ring p) c : E) = algebraMap F E c := rfl

instance valuation_nontrivial (p : NormalizedPlace F E) :
    p.valuation.toValuation.IsNontrivial := by logtwo_quiet
  obtain ⟨z, hz⟩ := p.normalized
  apply (Valuation.isNontrivial_iff_exists_lt_one _).mpr
  refine ⟨z, z.ne_zero, ?_⟩
  change (0 : WithTop ℤ) < p.valuation (z : E)
  rw [← coe_integerOrder, hz]
  norm_num

instance discreteValuationRing (p : NormalizedPlace F E) :
    IsDiscreteValuationRing (ring p) := by logtwo_quiet
  let : IsCyclic (Multiplicative (OrderDual (WithTop ℤ)))ˣ :=
    inferInstanceAs (IsCyclic (WithZero (Multiplicative ℤ))ˣ)
  let : IsCyclic (MonoidWithZeroHom.valueGroup (.ofClass p.valuation.toValuation)) := by logtwo_quiet
    infer_instance
  exact Valuation.valuationSubring_isDiscreteValuationRing p.valuation.toValuation

theorem valuation_eq_fractionAddValuation (p : NormalizedPlace F E) :
    p.valuation = CurveLocalOrder.fractionAddValuation (ring p) E := by logtwo_quiet
  apply DVRValuationUnique.eq_fractionAddValuation p.valuation
  · intro a
    exact a.property
  · intro a ha _
    exact p.valuation.toValuation.mem_maximalIdeal_iff.mp ha
  · exact p.normalized

end PiExponent.PlaceValuationRing

end

end OAI
end Source0046

-- Source: OAI/NumberTheory/PiExponent/Approximation/WeightedSliceDegree.lean
section Source0047
-- Modified in this edition: unused plain lemmas removed; see reduction.json.
/-
Modification notice for the LogTwo project.
Derived from openai/math (Apache-2.0), revision adc7f1241b42e322a6451854ab7e4b4c146bf78a.
Original source: lean/OAI/NumberTheory/PiExponent/Approximation/WeightedSliceDegree.lean
Changes: Convert module/import declarations to the Lean 4.34 public module format.
See ../THIRD_PARTY_NOTICES.txt for provenance and the recorded changes.
-/

namespace OAI

namespace PiExponent.WeightedSliceDegree

open scoped BigOperators Pointwise

variable {C E ι σ : Type*} [Field C] [Field E] [Algebra C E]

def SupportBound (ρ : σ → ℝ) (N : ℝ) (p : MvPolynomial σ E) : Prop :=
  ∀ d ∈ p.support, Finsupp.weight ρ d ≤ N

theorem SupportBound.mono {ρ : σ → ℝ} {M N : ℝ} {p : MvPolynomial σ E}
    (hp : SupportBound ρ M p) (hMN : M ≤ N) : SupportBound ρ N p :=
  fun d hd => (hp d hd).trans hMN

theorem supportBound_zero (ρ : σ → ℝ) (N : ℝ) :
    SupportBound ρ N (0 : MvPolynomial σ E) := by logtwo_quiet
  intro d hd
  simp at hd

theorem supportBound_C (ρ : σ → ℝ) (c : E) :
    SupportBound ρ 0 (MvPolynomial.C c) := by logtwo_quiet
  intro d hd
  have he : d = 0 := Finset.mem_singleton.mp (MvPolynomial.support_monomial_subset hd)
  subst d
  simp

theorem supportBound_X (ρ : σ → ℝ) (i : σ) :
    SupportBound ρ (ρ i) (MvPolynomial.X i : MvPolynomial σ E) := by logtwo_quiet
  classical
  intro d hd
  have he : d = Finsupp.single i 1 := by logtwo_quiet simpa only [MvPolynomial.support_X, Finset.mem_singleton] using hd
  subst d
  simp [Finsupp.weight_single]

theorem SupportBound.add {ρ : σ → ℝ} {N : ℝ} {p q : MvPolynomial σ E}
    (hp : SupportBound ρ N p) (hq : SupportBound ρ N q) : SupportBound ρ N (p + q) := by logtwo_quiet
  classical
  intro d hd
  rcases Finset.mem_union.mp (MvPolynomial.support_add hd) with h | h
  · exact hp d h
  · exact hq d h

theorem SupportBound.mul {ρ : σ → ℝ} {M N : ℝ} {p q : MvPolynomial σ E}
    (hp : SupportBound ρ M p) (hq : SupportBound ρ N q) : SupportBound ρ (M + N) (p * q) := by logtwo_quiet
  classical
  intro d hd
  obtain ⟨a, ha, b, hb, rfl⟩ := Finset.mem_add.mp (MvPolynomial.support_mul p q hd)
  simpa only [map_add] using add_le_add (hp a ha) (hq b hb)

theorem SupportBound.pow {ρ : σ → ℝ} {N : ℝ} {p : MvPolynomial σ E}
    (hp : SupportBound ρ N p) (m : ℕ) : SupportBound ρ ((m : ℝ) * N) (p ^ m) := by logtwo_quiet
  induction m with
  | zero => simpa only [pow_zero, Nat.cast_zero, zero_mul, MvPolynomial.C_1] using supportBound_C ρ (1 : E)
  | succ m ih =>
    simpa only [pow_succ, Nat.cast_add, Nat.cast_one, add_mul, one_mul] using ih.mul hp

theorem supportBound_prod {α : Type*} (s : Finset α) (ρ : σ → ℝ)
    (p : α → MvPolynomial σ E) (N : α → ℝ)
    (hp : ∀ i ∈ s, SupportBound ρ (N i) (p i)) :
    SupportBound ρ (∑ i ∈ s, N i) (∏ i ∈ s, p i) := by logtwo_quiet
  classical
  induction s using Finset.induction_on with
  | empty => simpa only [Finset.sum_empty, Finset.prod_empty, MvPolynomial.C_1] using supportBound_C ρ (1 : E)
  | @insert i s hi ih =>
    simp only [Finset.sum_insert hi, Finset.prod_insert hi]
    exact (hp i (Finset.mem_insert_self _ _)).mul (ih (fun j hj => hp j (Finset.mem_insert_of_mem hj)))

theorem supportBound_sum {α : Type*} (s : Finset α) (ρ : σ → ℝ)
    (p : α → MvPolynomial σ E) (N : ℝ)
    (hp : ∀ i ∈ s, SupportBound ρ N (p i)) :
    SupportBound ρ N (∑ i ∈ s, p i) := by logtwo_quiet
  classical
  induction s using Finset.induction_on with
  | empty => simpa only [Finset.sum_empty] using supportBound_zero ρ N
  | @insert i s hi ih =>
    rw [Finset.sum_insert hi]
    exact (hp i (Finset.mem_insert_self _ _)).add (ih (fun j hj => hp j (Finset.mem_insert_of_mem hj)))

theorem supportBound_aeval_monomial (ρ : ι → ℝ) (κ : σ → ℝ)
    (g : ι → MvPolynomial σ E) (hg : ∀ i, SupportBound κ (ρ i) (g i))
    (d : ι →₀ ℕ) (c : C) :
    SupportBound κ (Finsupp.weight ρ d) (MvPolynomial.aeval g (MvPolynomial.monomial d c)) := by logtwo_quiet
  classical
  rw [MvPolynomial.aeval_monomial]
  have hC : SupportBound κ 0 (algebraMap C (MvPolynomial σ E) c) :=
    supportBound_C κ (algebraMap C E c)
  have hprod := supportBound_prod d.support κ (fun i => g i ^ d i)
    (fun i => (d i : ℝ) * ρ i) (fun i _ => (hg i).pow (d i))
  have h := hC.mul hprod
  simpa only [zero_add, Finsupp.weight_apply, Finsupp.sum, nsmul_eq_mul, Finsupp.prod] using h

theorem supportBound_aeval (ρ : ι → ℝ) (κ : σ → ℝ)
    (g : ι → MvPolynomial σ E) (hg : ∀ i, SupportBound κ (ρ i) (g i))
    (N : ℝ) (p : MvPolynomial ι C)
    (hp : ∀ d ∈ p.support, Finsupp.weight ρ d ≤ N) :
    SupportBound κ N (MvPolynomial.aeval g p) := by logtwo_quiet
  classical
  conv_rhs => rw [MvPolynomial.as_sum p, map_sum]
  exact supportBound_sum p.support κ _ N
    (fun d hd => (supportBound_aeval_monomial ρ κ g hg d (p.coeff d)).mono (hp d hd))

noncomputable def sliceMap (A : Finset ι) (b : ι → E) :
    MvPolynomial ι C →ₐ[C] MvPolynomial A E := by logtwo_quiet
  classical
  exact MvPolynomial.aeval (fun i => if h : i ∈ A then MvPolynomial.X ⟨i, h⟩ else MvPolynomial.C (b i))

@[simp] theorem sliceMap_X_mem (A : Finset ι) (b : ι → E) (i : ι) (hi : i ∈ A) :
    sliceMap (C := C) A b (MvPolynomial.X i) = MvPolynomial.X ⟨i, hi⟩ := by logtwo_quiet
  classical
  simp [sliceMap, hi]

@[simp] theorem sliceMap_X_notMem (A : Finset ι) (b : ι → E) (i : ι) (hi : i ∉ A) :
    sliceMap (C := C) A b (MvPolynomial.X i) = MvPolynomial.C (b i) := by logtwo_quiet
  classical
  simp [sliceMap, hi]

@[simp] theorem sliceMap_C (A : Finset ι) (b : ι → E) (c : C) :
    sliceMap A b (MvPolynomial.C c) = MvPolynomial.C (algebraMap C E c) := by logtwo_quiet
  classical
  simp [sliceMap]

theorem supportBound_sliceMap (A : Finset ι) (b : ι → E)
    (ρ : ι → ℝ) (hρ : ∀ i, 0 ≤ ρ i) (N : ℝ) (p : MvPolynomial ι C)
    (hp : ∀ d ∈ p.support, Finsupp.weight ρ d ≤ N) :
    SupportBound (fun i : A => ρ i) N (sliceMap A b p) := by logtwo_quiet
  classical
  let g : ι → MvPolynomial A E := fun i =>
    if h : i ∈ A then MvPolynomial.X ⟨i, h⟩ else MvPolynomial.C (b i)
  change SupportBound (fun i : A => ρ i) N (MvPolynomial.aeval g p)
  have hg : ∀ i, SupportBound (fun j : A => ρ j) (ρ i) (g i) := by logtwo_quiet
    intro i
    dsimp only [g]
    split_ifs with hi
    · exact supportBound_X (E := E) (fun j : A => ρ j) ⟨i, hi⟩
    · exact (supportBound_C (fun j : A => ρ j) (b i)).mono (hρ i)
  exact supportBound_aeval ρ (fun i : A => ρ i) g hg N p hp

theorem supportBound_renameEquiv (e : ι ≃ σ) (ρ : ι → ℝ) (N : ℝ)
    (p : MvPolynomial ι E) (hp : SupportBound ρ N p) :
    SupportBound (fun j => ρ (e.symm j)) N (MvPolynomial.rename e p) := by logtwo_quiet
  rw [MvPolynomial.rename_eq_aeval]
  apply supportBound_aeval (C := E) ρ (fun j => ρ (e.symm j)) (MvPolynomial.X ∘ e) _ N p hp
  intro i
  simpa only [Function.comp_apply, e.symm_apply_apply] using
    supportBound_X (E := E) (fun j => ρ (e.symm j)) (e i)

noncomputable def enumeratedSliceMap (A : Finset ι) (b : ι → E) :
    MvPolynomial ι C →ₐ[C] MvPolynomial (Fin A.card) E :=
  ((MvPolynomial.rename (R := E) A.equivFin).restrictScalars C).comp (sliceMap A b)

theorem supportBound_enumeratedSliceMap (A : Finset ι) (b : ι → E)
    (ρ : ι → ℝ) (hρ : ∀ i, 0 ≤ ρ i) (N : ℝ) (p : MvPolynomial ι C)
    (hp : ∀ d ∈ p.support, Finsupp.weight ρ d ≤ N) :
    SupportBound (fun j : Fin A.card => ρ (A.equivFin.symm j)) N
      (enumeratedSliceMap A b p) :=
  supportBound_renameEquiv A.equivFin (fun i : A => ρ i) N (sliceMap A b p)
    (supportBound_sliceMap A b ρ hρ N p hp)

theorem supportBound_enumeratedSliceMap_sum (A : Finset ι) (b : ι → E)
    (ρ : ι → ℝ) (hρ : ∀ i, 0 ≤ ρ i) (N : ℝ) (p : MvPolynomial ι C)
    (hp : ∀ d ∈ p.support, (∑ i ∈ d.support, (d i : ℝ) * ρ i) ≤ N) :
    ∀ d ∈ (enumeratedSliceMap A b p).support,
      (∑ j ∈ d.support, (d j : ℝ) * ρ (A.equivFin.symm j)) ≤ N := by logtwo_quiet
  have h := supportBound_enumeratedSliceMap A b ρ hρ N p (by logtwo_quiet
    simpa only [Finsupp.weight_apply, Finsupp.sum, nsmul_eq_mul] using hp)
  simpa only [SupportBound, Finsupp.weight_apply, Finsupp.sum, nsmul_eq_mul] using h

end PiExponent.WeightedSliceDegree

end OAI
end Source0047

-- Source: OAI/NumberTheory/PiExponent/Polynomials/SimplexFloor.lean
section Source0048
-- Modified in this edition: unused plain lemmas removed; see reduction.json.
/-
Modification notice for the LogTwo project.
Derived from openai/math (Apache-2.0), revision adc7f1241b42e322a6451854ab7e4b4c146bf78a.
Original source: lean/OAI/NumberTheory/PiExponent/Polynomials/SimplexFloor.lean
Changes: Convert module/import declarations to the Lean 4.34 public module format.
See ../THIRD_PARTY_NOTICES.txt for provenance and the recorded changes.
-/

namespace OAI

open Filter Topology

namespace PiExponent

theorem tendsto_natFloor_affine_atTop {a : ℝ} (ha : 0 < a) (b : ℝ) :
    Tendsto (fun x : ℝ => ⌊a * x + b⌋₊) atTop atTop :=
  tendsto_nat_floor_atTop.comp
    (tendsto_atTop_add_const_right atTop b (Tendsto.const_mul_atTop ha tendsto_id))

theorem tendsto_natFloor_affine_div {a : ℝ} (ha : 0 < a) (b : ℝ) :
    Tendsto (fun x : ℝ => (⌊a * x + b⌋₊ : ℝ) / x) atTop (𝓝 a) := by logtwo_quiet
  have hy : Tendsto (fun x : ℝ => a * x + b) atTop atTop :=
    tendsto_atTop_add_const_right atTop b (Tendsto.const_mul_atTop ha tendsto_id)
  have hratio : Tendsto (fun x : ℝ => (a * x + b) / x) atTop (𝓝 a) := by logtwo_quiet
    have h : Tendsto (fun x : ℝ => a + b * x⁻¹) atTop (𝓝 (a + b * 0)) :=
      tendsto_const_nhds.add (tendsto_const_nhds.mul
      (tendsto_inv_atTop_zero : Tendsto (fun x : ℝ => x⁻¹) atTop (𝓝 0)))
    simp only [mul_zero, add_zero] at h
    apply h.congr'
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with x hx
    field_simp
  have h := (tendsto_nat_floor_div_atTop.comp hy).mul hratio
  simp only [one_mul] at h
  apply h.congr'
  filter_upwards [hy.eventually (eventually_gt_atTop (0 : ℝ))] with x hx
  change (⌊a * x + b⌋₊ : ℝ) / (a * x + b) * ((a * x + b) / x) = _
  field_simp

theorem tendsto_normalized_natFloor_affine {f : ℕ → ℝ} {d : ℕ} {L a : ℝ}
    (hf : Tendsto (fun n : ℕ => f n / (n : ℝ) ^ d) atTop (𝓝 L))
    (ha : 0 < a) (b : ℝ) :
    Tendsto (fun x : ℝ => f ⌊a * x + b⌋₊ / x ^ d) atTop (𝓝 (L * a ^ d)) := by logtwo_quiet
  have hfloor := tendsto_natFloor_affine_atTop ha b
  have h := (hf.comp hfloor).mul ((tendsto_natFloor_affine_div ha b).pow d)
  apply h.congr'
  filter_upwards [hfloor.eventually (eventually_ge_atTop 1)] with x hx
  have hn : (⌊a * x + b⌋₊ : ℝ) ≠ 0 := by logtwo_quiet
    exact_mod_cast (by logtwo_quiet omega : ⌊a * x + b⌋₊ ≠ 0)
  simp only [Function.comp_apply]
  rw [div_pow]
  field_simp

end PiExponent

end OAI
end Source0048

-- Source: OAI/NumberTheory/PiExponent/Polynomials/SimplexUnweighted.lean
section Source0049
/-
Modification notice for the LogTwo project.
Derived from openai/math (Apache-2.0), revision adc7f1241b42e322a6451854ab7e4b4c146bf78a.
Original source: lean/OAI/NumberTheory/PiExponent/Polynomials/SimplexUnweighted.lean
Changes: Convert module/import declarations to the Lean 4.34 public module format.
See ../THIRD_PARTY_NOTICES.txt for provenance and the recorded changes.
-/

namespace OAI

open scoped BigOperators

namespace PiExponent

def unweightedSimplex (d N : ℕ) : Finset (Fin d → ℕ) :=
  (Fintype.piFinset (fun _ => Finset.range (N + 1))).filter
    (fun a => ∑ i, a i ≤ N)

@[simp] theorem mem_unweightedSimplex {d N : ℕ} {a : Fin d → ℕ} :
    a ∈ unweightedSimplex d N ↔ ∑ i, a i ≤ N := by logtwo_quiet
  constructor
  · exact fun h => (Finset.mem_filter.mp h).2
  · intro h
    refine Finset.mem_filter.mpr ⟨Fintype.mem_piFinset.mpr ?_, h⟩
    intro i
    apply Finset.mem_range.mpr
    have := Finset.single_le_sum (fun j _ => Nat.zero_le (a j)) (Finset.mem_univ i)
    omega

theorem card_unweightedSimplex (d N : ℕ) :
    (unweightedSimplex d N).card = (N + d).choose d := by logtwo_quiet
  classical
  let target : Finset (Fin (d + 1) →₀ ℕ) := Finset.univ.finsuppAntidiag N
  have hc : target.card = (N + d).choose d := by logtwo_quiet
    rw [Finset.card_finsuppAntidiag_nat_eq_choose]
    simp only [Finset.card_univ, Fintype.card_fin]
    rw [show d + 1 + N - 1 = N + d by logtwo_quiet omega, Nat.choose_symm_add]
  rw [← hc]
  let f : (Fin d → ℕ) → (Fin (d + 1) →₀ ℕ) := fun a =>
    Finsupp.equivFunOnFinite.symm (Fin.cons (N - ∑ i, a i) a)
  apply Finset.card_bij (fun a _ => f a)
  · intro a ha
    apply Finset.mem_finsuppAntidiag.mpr
    constructor
    · simp only [f, Finsupp.coe_equivFunOnFinite_symm, Fin.sum_univ_succ,
        Fin.cons_zero, Fin.cons_succ]
      exact Nat.sub_add_cancel (mem_unweightedSimplex.mp ha)
    · exact Finset.subset_univ _
  · intro a ha b hb hab
    funext i
    have h := congrArg (fun g : Fin (d + 1) →₀ ℕ => g i.succ) hab
    simpa only [f, Finsupp.coe_equivFunOnFinite_symm, Fin.cons_succ] using h
  · intro b hb
    obtain ⟨hs, _⟩ := Finset.mem_finsuppAntidiag.mp hb
    have hs' : b 0 + ∑ i : Fin d, b i.succ = N := by logtwo_quiet
      simpa only [Fin.sum_univ_succ] using hs
    refine ⟨fun i => b i.succ, mem_unweightedSimplex.mpr (by logtwo_quiet omega), ?_⟩
    apply Finsupp.ext
    intro i
    refine Fin.cases ?_ (fun j => ?_) i
    · change N - ∑ j : Fin d, b j.succ = b 0
      omega
    · change b j.succ = b j.succ
      rfl

open Filter Topology Asymptotics

theorem tendsto_choose_normalized (d : ℕ) :
    Tendsto (fun N : ℕ => (N.choose d : ℝ) / (N : ℝ) ^ d)
      atTop (𝓝 (1 / (d.factorial : ℝ))) := by logtwo_quiet
  have h := (isEquivalent_choose d).div
    (IsEquivalent.refl : (fun N : ℕ => (N : ℝ) ^ d) ~[atTop]
      (fun N : ℕ => (N : ℝ) ^ d))
  apply h.symm.tendsto_nhds
  apply tendsto_const_nhds.congr'
  filter_upwards [eventually_ge_atTop 1] with N hN
  have hn : (N : ℝ) ≠ 0 := by logtwo_quiet exact_mod_cast (by logtwo_quiet omega : N ≠ 0)
  change 1 / (d.factorial : ℝ) = ((N : ℝ) ^ d / (d.factorial : ℝ)) / (N : ℝ) ^ d
  field_simp

theorem tendsto_choose_add_normalized (d c : ℕ) :
    Tendsto (fun N : ℕ => ((N + c).choose d : ℝ) / (N : ℝ) ^ d)
      atTop (𝓝 (1 / (d.factorial : ℝ))) := by logtwo_quiet
  have h₁ := (tendsto_choose_normalized d).comp (tendsto_add_atTop_nat c)
  have h₂ : Tendsto (fun N : ℕ => ((N + c : ℕ) : ℝ) / (N : ℝ))
      atTop (𝓝 1) := by logtwo_quiet
    simpa [Nat.cast_add, add_comm] using
      (tendsto_add_mul_div_add_mul_atTop_nhds (c : ℝ) 0 1 (d := 1) (by logtwo_quiet norm_num))
  have h := h₁.mul (h₂.pow d)
  simp only [one_pow, mul_one] at h
  apply h.congr'
  filter_upwards [eventually_ge_atTop 1] with N hN
  have hn : ((N + c : ℕ) : ℝ) ≠ 0 := by logtwo_quiet exact_mod_cast (by logtwo_quiet omega : N + c ≠ 0)
  simp only [Function.comp_apply]
  rw [div_pow]
  field_simp

theorem tendsto_card_unweightedSimplex (d : ℕ) :
    Tendsto (fun N : ℕ => ((unweightedSimplex d N).card : ℝ) / (N : ℝ) ^ d)
      atTop (𝓝 (1 / (d.factorial : ℝ))) := by logtwo_quiet
  simpa only [card_unweightedSimplex] using tendsto_choose_add_normalized d d

theorem tendsto_card_unweightedSimplex_add (d c : ℕ) :
    Tendsto (fun N : ℕ => ((unweightedSimplex d (N + c)).card : ℝ) / (N : ℝ) ^ d)
      atTop (𝓝 (1 / (d.factorial : ℝ))) := by logtwo_quiet
  simpa only [card_unweightedSimplex, Nat.add_assoc] using
    tendsto_choose_add_normalized d (c + d)

end PiExponent

end OAI
end Source0049

run_cmd Lean.logInfo "LogTwo progress: reached module 50/885"

-- Source: OAI/NumberTheory/PiExponent/Polynomials/SimplexCounting.lean
section Source0050
-- Modified in this edition: unused plain lemmas removed; see reduction.json.
/-
Modification notice for the LogTwo project.
Derived from openai/math (Apache-2.0), revision adc7f1241b42e322a6451854ab7e4b4c146bf78a.
Original source: lean/OAI/NumberTheory/PiExponent/Polynomials/SimplexCounting.lean
Changes: Convert module/import declarations to the Lean 4.34 public module format.
See ../THIRD_PARTY_NOTICES.txt for provenance and the recorded changes.
-/

namespace OAI

open scoped BigOperators

namespace PiExponent

def natWeightedSimplex {d : ℕ} (w : Fin d → ℕ) (N : ℕ) : Finset (Fin d → ℕ) :=
  (Fintype.piFinset (fun _ => Finset.range (N + 1))).filter
    (fun a => ∑ i, w i * a i ≤ N)

theorem mem_natWeightedSimplex {d : ℕ} {w : Fin d → ℕ}
    (hw : ∀ i, 0 < w i) {N : ℕ} {a : Fin d → ℕ} :
    a ∈ natWeightedSimplex w N ↔ ∑ i, w i * a i ≤ N := by logtwo_quiet
  constructor
  · exact fun h => (Finset.mem_filter.mp h).2
  · intro h
    refine Finset.mem_filter.mpr ⟨Fintype.mem_piFinset.mpr ?_, h⟩
    intro i
    apply Finset.mem_range.mpr
    have h₁ : a i ≤ w i * a i := Nat.le_mul_of_pos_left (a i) (hw i)
    have h₂ : w i * a i ≤ ∑ j, w j * a j :=
      Finset.single_le_sum (f := fun j => w j * a j)
        (fun j _ => Nat.zero_le _) (Finset.mem_univ i)
    omega

def residueRectangle {d : ℕ} (w : Fin d → ℕ) : Finset (Fin d → ℕ) :=
  Fintype.piFinset (fun i => Finset.range (w i))

@[simp] theorem mem_residueRectangle {d : ℕ} {w r : Fin d → ℕ} :
    r ∈ residueRectangle w ↔ ∀ i, r i < w i := by logtwo_quiet
  simp [residueRectangle, Fintype.mem_piFinset]

@[simp] theorem card_residueRectangle {d : ℕ} (w : Fin d → ℕ) :
    (residueRectangle w).card = ∏ i, w i := by logtwo_quiet
  simp [residueRectangle, Fintype.card_piFinset]

theorem simplex_count_lower_sandwich {d : ℕ} (w : Fin d → ℕ)
    (hw : ∀ i, 0 < w i) (N : ℕ) :
    (natWeightedSimplex (fun _ : Fin d => 1) N).card ≤
      (natWeightedSimplex w N).card * ∏ i, w i := by logtwo_quiet
  rw [← card_residueRectangle, ← Finset.card_product]
  let f : (Fin d → ℕ) → (Fin d → ℕ) × (Fin d → ℕ) :=
    fun b => (fun i => b i / w i, fun i => b i % w i)
  apply Finset.card_le_card_of_injOn f
  · intro b hb
    apply Finset.mem_product.mpr
    constructor
    · apply (mem_natWeightedSimplex hw).mpr
      have hb' := (mem_natWeightedSimplex (fun _ => by logtwo_quiet decide)).mp hb
      simp only [one_mul] at hb'
      exact (Finset.sum_le_sum (fun i _ => Nat.mul_div_le (b i) (w i))).trans hb'
    · exact mem_residueRectangle.mpr (fun i => Nat.mod_lt (b i) (hw i))
  · intro a ha b hb hab
    have hq := congrArg Prod.fst hab
    have hr := congrArg Prod.snd hab
    funext i
    have hqi := congrFun hq i
    have hri := congrFun hr i
    change a i / w i = b i / w i at hqi
    change a i % w i = b i % w i at hri
    have ha' := Nat.div_add_mod (a i) (w i)
    have hb' := Nat.div_add_mod (b i) (w i)
    calc
      a i = w i * (a i / w i) + a i % w i := ha'.symm
      _ = w i * (b i / w i) + b i % w i := by logtwo_quiet rw [hqi, hri]
      _ = b i := hb'

theorem simplex_count_upper_sandwich {d : ℕ} (w : Fin d → ℕ)
    (hw : ∀ i, 0 < w i) (N : ℕ) :
    (natWeightedSimplex w N).card * (∏ i, w i) ≤
      (natWeightedSimplex (fun _ : Fin d => 1) (N + ∑ i, (w i - 1))).card := by logtwo_quiet
  rw [← card_residueRectangle, ← Finset.card_product]
  let f : ((Fin d → ℕ) × (Fin d → ℕ)) → (Fin d → ℕ) :=
    fun ar i => w i * ar.1 i + ar.2 i
  apply Finset.card_le_card_of_injOn f
  · intro ar har
    obtain ⟨ha, hr⟩ := Finset.mem_product.mp har
    apply (mem_natWeightedSimplex (fun _ => by logtwo_quiet decide)).mpr
    simp only [one_mul]
    change ∑ i, (w i * ar.1 i + ar.2 i) ≤ _
    rw [Finset.sum_add_distrib]
    apply Nat.add_le_add ((mem_natWeightedSimplex hw).mp ha)
    apply Finset.sum_le_sum
    intro i hi
    have := mem_residueRectangle.mp hr i
    omega
  · intro ar har bs hbs hab
    obtain ⟨ha, hr⟩ := Finset.mem_product.mp har
    obtain ⟨hb, hs⟩ := Finset.mem_product.mp hbs
    apply Prod.ext
    · funext i
      have hi := congrFun hab i
      change w i * ar.1 i + ar.2 i = w i * bs.1 i + bs.2 i at hi
      have hri := mem_residueRectangle.mp hr i
      have hsi := mem_residueRectangle.mp hs i
      have hdiv := congrArg (fun n => n / w i) hi
      rw [Nat.add_div_of_dvd_right (Nat.dvd_mul_right (w i) (ar.1 i)),
        Nat.add_div_of_dvd_right (Nat.dvd_mul_right (w i) (bs.1 i))] at hdiv
      simpa [Nat.div_eq_of_lt hri, Nat.div_eq_of_lt hsi,
        Nat.mul_div_cancel_left _ (hw i)] using hdiv
    · funext i
      have hi := congrFun hab i
      change w i * ar.1 i + ar.2 i = w i * bs.1 i + bs.2 i at hi
      have hri := mem_residueRectangle.mp hr i
      have hsi := mem_residueRectangle.mp hs i
      have hmod := congrArg (fun n => n % w i) hi
      simpa [Nat.add_mod, Nat.mod_eq_of_lt hri, Nat.mod_eq_of_lt hsi] using hmod

@[simp] theorem natWeightedSimplex_one (d N : ℕ) :
    natWeightedSimplex (fun _ : Fin d => 1) N = unweightedSimplex d N := by logtwo_quiet
  ext a
  rw [mem_natWeightedSimplex (w := fun _ : Fin d => 1) (fun _ => by logtwo_quiet decide), mem_unweightedSimplex]
  simp only [one_mul]

open Filter Topology

theorem tendsto_card_natWeightedSimplex {d : ℕ} (w : Fin d → ℕ)
    (hw : ∀ i, 0 < w i) :
    Tendsto (fun N : ℕ => ((natWeightedSimplex w N).card : ℝ) / (N : ℝ) ^ d)
      atTop (𝓝 (1 / ((d.factorial : ℝ) * ∏ i, (w i : ℝ)))) := by logtwo_quiet
  let P : ℝ := ∏ i, (w i : ℝ)
  have hP : 0 < P := Finset.prod_pos (fun i _ => by logtwo_quiet exact_mod_cast hw i)
  have hs : Tendsto
      (fun N : ℕ => ((natWeightedSimplex w N).card : ℝ) * P / (N : ℝ) ^ d)
      atTop (𝓝 (1 / (d.factorial : ℝ))) := by logtwo_quiet
    apply tendsto_of_tendsto_of_tendsto_of_le_of_le
      (tendsto_card_unweightedSimplex d)
      (tendsto_card_unweightedSimplex_add d (∑ i, (w i - 1)))
    · intro N
      apply div_le_div_of_nonneg_right _ (by logtwo_quiet positivity)
      have h := simplex_count_lower_sandwich w hw N
      rw [natWeightedSimplex_one] at h
      dsimp [P]
      exact_mod_cast h
    · intro N
      apply div_le_div_of_nonneg_right _ (by logtwo_quiet positivity)
      have h := simplex_count_upper_sandwich w hw N
      rw [natWeightedSimplex_one] at h
      dsimp [P]
      exact_mod_cast h
  have h := hs.div_const P
  have heq : 1 / (d.factorial : ℝ) / P =
      1 / ((d.factorial : ℝ) * ∏ i, (w i : ℝ)) := by logtwo_quiet
    simp only [P, div_div]
  rw [heq] at h
  apply h.congr'
  exact Filter.Eventually.of_forall (fun N => by logtwo_quiet
    change ((natWeightedSimplex w N).card : ℝ) * P / (N : ℝ) ^ d / P = _
    field_simp)

noncomputable def realWeightedSimplex {d : ℕ} (w : Fin d → ℝ) (H : ℝ) :
    Finset (Fin d → ℕ) := by logtwo_quiet
  classical
  exact (Fintype.piFinset (fun i => Finset.range (⌊H / w i⌋₊ + 1))).filter
    (fun a => ∑ i, w i * (a i : ℝ) ≤ H)

noncomputable def strictWeightedSimplex {d : ℕ} (w : Fin d → ℝ) (H : ℝ) :
    Finset (Fin d → ℕ) := by logtwo_quiet
  classical
  exact (realWeightedSimplex w H).filter (fun a => ∑ i, w i * (a i : ℝ) < H)

theorem mem_realWeightedSimplex {d : ℕ} {w : Fin d → ℝ}
    (hw : ∀ i, 0 < w i) {H : ℝ} {a : Fin d → ℕ} :
    a ∈ realWeightedSimplex w H ↔ ∑ i, w i * (a i : ℝ) ≤ H := by logtwo_quiet
  classical
  constructor
  · exact fun h => (Finset.mem_filter.mp h).2
  · intro h
    refine Finset.mem_filter.mpr ⟨Fintype.mem_piFinset.mpr ?_, h⟩
    intro i
    apply Finset.mem_range.mpr
    apply Nat.lt_succ_of_le
    apply Nat.le_floor
    apply (le_div_iff₀ (hw i)).mpr
    rw [mul_comm]
    exact (Finset.single_le_sum (f := fun j => w j * (a j : ℝ))
      (fun j _ => mul_nonneg (hw j).le (Nat.cast_nonneg _)) (Finset.mem_univ i)).trans h

theorem mem_strictWeightedSimplex {d : ℕ} {w : Fin d → ℝ}
    (hw : ∀ i, 0 < w i) {H : ℝ} {a : Fin d → ℕ} :
    a ∈ strictWeightedSimplex w H ↔ ∑ i, w i * (a i : ℝ) < H := by logtwo_quiet
  classical
  simp only [strictWeightedSimplex, Finset.mem_filter, mem_realWeightedSimplex hw,
    and_iff_right_iff_imp]
  exact fun h => h.le

theorem realWeightedSimplex_scaled {d : ℕ} (w : Fin d → ℕ)
    (hw : ∀ i, 0 < w i) {c H : ℝ} (hc : 0 < c) (hH : 0 ≤ H) :
    realWeightedSimplex (fun i => (w i : ℝ) / c) H =
      natWeightedSimplex w ⌊c * H⌋₊ := by logtwo_quiet
  ext a
  rw [mem_realWeightedSimplex (fun i => div_pos (by logtwo_quiet exact_mod_cast hw i) hc),
    mem_natWeightedSimplex hw, Nat.le_floor_iff (mul_nonneg hc.le hH)]
  have hs : (∑ i, (w i : ℝ) / c * (a i : ℝ)) =
      ((∑ i, w i * a i : ℕ) : ℝ) / c := by logtwo_quiet
    simp [Nat.cast_sum, Nat.cast_mul, Finset.sum_div, div_mul_eq_mul_div]
  rw [hs, div_le_iff₀ hc, mul_comm H c]

theorem tendsto_card_realWeightedSimplex_scaled {d : ℕ} (w : Fin d → ℕ)
    (hw : ∀ i, 0 < w i) {c : ℝ} (hc : 0 < c) :
    Tendsto (fun H : ℝ => ((realWeightedSimplex (fun i => (w i : ℝ) / c) H).card : ℝ) / H ^ d)
      atTop (𝓝 ((1 / ((d.factorial : ℝ) * ∏ i, (w i : ℝ))) * c ^ d)) := by logtwo_quiet
  have h := tendsto_normalized_natFloor_affine
    (tendsto_card_natWeightedSimplex w hw) hc 0
  apply h.congr'
  filter_upwards [eventually_ge_atTop (0 : ℝ)] with H hH
  simp only [add_zero, realWeightedSimplex_scaled w hw hc hH]

theorem tendsto_card_strictWeightedSimplex_scaled {d : ℕ} (w : Fin d → ℕ)
    (hw : ∀ i, 0 < w i) {c : ℝ} (hc : 0 < c) :
    Tendsto (fun H : ℝ => ((strictWeightedSimplex (fun i => (w i : ℝ) / c) H).card : ℝ) / H ^ d)
      atTop (𝓝 ((1 / ((d.factorial : ℝ) * ∏ i, (w i : ℝ))) * c ^ d)) := by logtwo_quiet
  have hlo := tendsto_normalized_natFloor_affine
    (tendsto_card_natWeightedSimplex w hw) hc (-1)
  have hhi := tendsto_card_realWeightedSimplex_scaled w hw hc
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' hlo hhi
  · filter_upwards [eventually_ge_atTop (1 / c)] with H hH
    have hHpos : 0 < H := (div_pos zero_lt_one hc).trans_le hH
    have hcH : 1 ≤ c * H := by logtwo_quiet
      have := (div_le_iff₀ hc).mp hH
      nlinarith
    apply div_le_div_of_nonneg_right _ (pow_nonneg hHpos.le d)
    exact_mod_cast (Finset.card_le_card (show
      natWeightedSimplex w ⌊c * H + -1⌋₊ ⊆
      strictWeightedSimplex (fun i => (w i : ℝ) / c) H from by logtwo_quiet
        intro a ha
        apply (mem_strictWeightedSimplex (fun i => div_pos (by logtwo_quiet exact_mod_cast hw i) hc)).mpr
        have ha' := (mem_natWeightedSimplex hw).mp ha
        have hs : ((∑ i, w i * a i : ℕ) : ℝ) ≤ c * H + -1 :=
          (Nat.le_floor_iff (by logtwo_quiet linarith)).mp ha'
        have heq : (∑ i, (w i : ℝ) / c * (a i : ℝ)) =
            ((∑ i, w i * a i : ℕ) : ℝ) / c := by logtwo_quiet
          simp [Nat.cast_sum, Nat.cast_mul, Finset.sum_div, div_mul_eq_mul_div]
        rw [heq, div_lt_iff₀ hc]
        nlinarith))
  · filter_upwards [eventually_ge_atTop (0 : ℝ)] with H hH
    apply div_le_div_of_nonneg_right _ (pow_nonneg hH d)
    exact_mod_cast (Finset.card_le_card (Finset.filter_subset
      (fun a : Fin d → ℕ => ∑ i, (w i : ℝ) / c * (a i : ℝ) < H)
      (realWeightedSimplex (fun i => (w i : ℝ) / c) H)))

end PiExponent

end OAI
end Source0050

-- Source: OAI/NumberTheory/PiExponent/Approximation/InterpolationMatrix.lean
section Source0051
-- Modified in this edition: unused plain lemmas removed; see reduction.json.
/-
Modification notice for the LogTwo project.
Derived from openai/math (Apache-2.0), revision adc7f1241b42e322a6451854ab7e4b4c146bf78a.
Original source: lean/OAI/NumberTheory/PiExponent/Approximation/InterpolationMatrix.lean
Changes: Convert module/import declarations to the Lean 4.34 public module format.
See ../THIRD_PARTY_NOTICES.txt for provenance and the recorded changes.
-/

namespace OAI

open scoped BigOperators

namespace PiExponent.InterpolationMatrix

noncomputable def exponentVector {m : ℕ} (a : Fin m → ℕ) : Fin m →₀ ℕ :=
  Finsupp.equivFunOnFinite.symm a

@[simp] theorem exponentVector_apply {m : ℕ} (a : Fin m → ℕ) (i : Fin m) :
    exponentVector a i = a i := by logtwo_quiet
  simp [exponentVector]

noncomputable def truncatedLog (T : ℕ) : Polynomial ℂ :=
  PowerSeries.trunc T (PowerSeries.log ℂ)

@[simp] theorem truncatedLog_coeff (T k : ℕ) :
    (truncatedLog T).coeff k =
      if k < T then
        if k = 0 then 0 else algebraMap ℚ ℂ ((-1 : ℚ) ^ (k + 1) / k)
      else 0 := by logtwo_quiet
  simp [truncatedLog, PowerSeries.coeff_trunc]

noncomputable def monomialImage {m : ℕ} (r : Fin m → ℂ)
    (G : Fin m → Polynomial ℂ) (j h : ℕ) (a : Fin m → ℕ) :
    MvPolynomial (Fin m) (Polynomial ℂ) :=
  MvPolynomial.C ((1 + Polynomial.X) ^ h) *
    ∏ i, (MvPolynomial.C (Polynomial.C ((j : ℂ) * r i) + G i) +
      MvPolynomial.X i) ^ a i

noncomputable def entry {m : ℕ} (r : Fin m → ℂ)
    (G : Fin m → Polynomial ℂ) (j s : ℕ) (b : Fin m → ℕ)
    (h : ℕ) (a : Fin m → ℕ) : ℂ :=
  ((monomialImage r G j h a).coeff (exponentVector b)).coeff s

noncomputable def sectionImage {m : ℕ} {C : Type*} [Fintype C]
    (r : Fin m → ℂ) (G : Fin m → Polynomial ℂ)
    (h : C → ℕ) (a : C → Fin m → ℕ) (x : C → ℂ) (j : ℕ) :
    MvPolynomial (Fin m) (Polynomial ℂ) :=
  ∑ c, MvPolynomial.C (Polynomial.C (x c)) * monomialImage r G j (h c) (a c)

def columnWeights {m : ℕ} (w0 : ℝ) (w : Fin m → ℝ) : Fin (m + 1) → ℝ :=
  Fin.cases w0 w

noncomputable def rowWeights {m : ℕ} (v0 θ : ℝ) (w : Fin m → ℝ) : Fin (m + 1) → ℝ :=
  Fin.cases v0 (fun i => w i / θ)

abbrev Column {m : ℕ} (w0 : ℝ) (w : Fin m → ℝ) (H : ℝ) :=
  ↥(PiExponent.realWeightedSimplex (columnWeights w0 w) H)

abbrev Row {m : ℕ} (K : ℕ) (v0 θ : ℝ) (w : Fin m → ℝ) (H : ℝ) :=
  Fin K × ↥(PiExponent.strictWeightedSimplex (rowWeights v0 θ w) H)

theorem column_mem_iff {m : ℕ} {w0 H : ℝ} {w : Fin m → ℝ}
    (hw0 : 0 < w0) (hw : ∀ i, 0 < w i) (a : Fin (m + 1) → ℕ) :
    a ∈ PiExponent.realWeightedSimplex (columnWeights w0 w) H ↔
      w0 * (a 0 : ℝ) + ∑ i, w i * (a i.succ : ℝ) ≤ H := by logtwo_quiet
  have hp : ∀ i, 0 < columnWeights w0 w i := by logtwo_quiet
    intro i
    refine Fin.cases hw0 (fun j => hw j) i
  rw [PiExponent.mem_realWeightedSimplex hp, Fin.sum_univ_succ]
  rfl

theorem row_mem_iff {m : ℕ} {v0 θ H : ℝ} {w : Fin m → ℝ}
    (hv0 : 0 < v0) (hθ : 0 < θ) (hw : ∀ i, 0 < w i) (b : Fin (m + 1) → ℕ) :
    b ∈ PiExponent.strictWeightedSimplex (rowWeights v0 θ w) H ↔
      v0 * (b 0 : ℝ) + (∑ i, w i * (b i.succ : ℝ)) / θ < H := by logtwo_quiet
  have hp : ∀ i, 0 < rowWeights v0 θ w i := by logtwo_quiet
    intro i
    refine Fin.cases hv0 (fun j => div_pos (hw j) hθ) i
  rw [PiExponent.mem_strictWeightedSimplex hp, Fin.sum_univ_succ]
  simp only [rowWeights, Fin.cases_zero, Fin.cases_succ, div_mul_eq_mul_div,
    Finset.sum_div]

noncomputable def matrix {m : ℕ} (K : ℕ) (w0 v0 θ : ℝ)
    (w : Fin m → ℝ) (H : ℝ) (r : Fin m → ℂ) (G : Fin m → Polynomial ℂ) :
    Matrix (Row K v0 θ w H) (Column w0 w H) ℂ :=
  fun ρ c => entry r G ρ.1.val (ρ.2.1 0) (fun i => ρ.2.1 i.succ)
    (c.1 0) (fun i => c.1 i.succ)

noncomputable def linearEvaluation {m : ℕ} (K : ℕ) (w0 v0 θ : ℝ)
    (w : Fin m → ℝ) (H : ℝ) (r : Fin m → ℂ) (G : Fin m → Polynomial ℂ) :
    (Column w0 w H → ℂ) →ₗ[ℂ] (Row K v0 θ w H → ℂ) :=
  (matrix K w0 v0 θ w H r G).mulVecLin

@[simp] theorem row_card {m : ℕ} (K : ℕ) (v0 θ : ℝ)
    (w : Fin m → ℝ) (H : ℝ) :
    Fintype.card (Row K v0 θ w H) =
      K * (PiExponent.strictWeightedSimplex (rowWeights v0 θ w) H).card := by logtwo_quiet
  classical
  simp [Row]

theorem exists_full_row_minor_of_surjective
    {R C K : Type*} [Fintype R] [Fintype C] [DecidableEq R] [Field K]
    (A : Matrix R C K) (hA : Function.Surjective A.mulVecLin) :
    ∃ selection : R → C, Function.Injective selection ∧
      (A.submatrix id selection).det ≠ 0 := by logtwo_quiet
  classical
  obtain ⟨B, hB⟩ := Matrix.mulVec_surjective_iff_exists_right_inverse.mp hA
  have hexp : (A * B).det =
      ∑ p : R → C, (A.submatrix id p).det * ∏ i, B (p i) i := by logtwo_quiet
    calc
      (A * B).det = ∑ p : R → C, ∑ σ : Equiv.Perm R,
          ((Equiv.Perm.sign σ : ℤ) : K) * ∏ i, A (σ i) (p i) * B (p i) i := by logtwo_quiet
        simp only [Matrix.det_apply', Matrix.mul_apply, Finset.prod_univ_sum,
          Finset.mul_sum, Fintype.piFinset_univ]
        rw [Finset.sum_comm]
      _ = ∑ p : R → C, (A.submatrix id p).det * ∏ i, B (p i) i := by logtwo_quiet
        apply Finset.sum_congr rfl
        intro p hp
        simp only [Matrix.det_apply', Matrix.submatrix_apply, id_eq,
          Finset.prod_mul_distrib, ← mul_assoc, ← Finset.sum_mul]
  have hsum : (∑ p : R → C, (A.submatrix id p).det * ∏ i, B (p i) i) ≠ 0 := by logtwo_quiet
    rw [← hexp, hB, Matrix.det_one]
    exact one_ne_zero
  obtain ⟨p, _, hp⟩ := Finset.exists_ne_zero_of_sum_ne_zero hsum
  have hdet : (A.submatrix id p).det ≠ 0 := by logtwo_quiet
    intro h
    apply hp
    rw [h, zero_mul]
  refine ⟨p, ?_, hdet⟩
  intro i j hij
  by_contra hne
  exact hdet (Matrix.det_zero_of_column_eq hne (fun k => congrArg (A k) hij))

noncomputable def truncatedLogMatrix {m : ℕ} (K : ℕ) (w0 v0 θ : ℝ)
    (w : Fin m → ℝ) (H : ℝ) (r : Fin m → ℂ) (T : Fin m → ℕ) :
    Matrix (Row K v0 θ w H) (Column w0 w H) ℂ :=
  matrix K w0 v0 θ w H r (fun i => truncatedLog (T i))

end PiExponent.InterpolationMatrix

end OAI
end Source0051

-- Source: OAI/NumberTheory/PiExponent/Polynomials/SimplexRationalWeights.lean
section Source0052
/-
Modification notice for the LogTwo project.
Derived from openai/math (Apache-2.0), revision adc7f1241b42e322a6451854ab7e4b4c146bf78a.
Original source: lean/OAI/NumberTheory/PiExponent/Polynomials/SimplexRationalWeights.lean
Changes: Convert module/import declarations to the Lean 4.34 public module format.
See ../THIRD_PARTY_NOTICES.txt for provenance and the recorded changes.
-/

namespace OAI

open scoped BigOperators

namespace PiExponent

theorem positive_rational_weights_common_denominator {d : ℕ}
    (ρ : Fin d → ℚ) (hρ : ∀ i, 0 < ρ i) :
    ∃ D : ℕ, 0 < D ∧ ∃ w : Fin d → ℕ,
      (∀ i, 0 < w i) ∧ ∀ i, (ρ i : ℝ) = (w i : ℝ) / (D : ℝ) := by logtwo_quiet
  classical
  let D : ℕ := ∏ i, (ρ i).den
  have hD : 0 < D := Finset.prod_pos (fun i _ => (ρ i).den_pos)
  have hd : ∀ i, (ρ i).den ∣ D :=
    fun i => Finset.dvd_prod_of_mem (fun j => (ρ j).den) (Finset.mem_univ i)
  choose k hk using hd
  have hkpos : ∀ i, 0 < k i := by logtwo_quiet
    intro i
    by_contra h
    have hkzero : k i = 0 := by logtwo_quiet omega
    have := hk i
    rw [hkzero, mul_zero] at this
    omega
  let w : Fin d → ℕ := fun i => (ρ i).num.toNat * k i
  refine ⟨D, hD, w, ?_, ?_⟩
  · intro i
    have hn : 0 < (ρ i).num := Rat.num_pos.mpr (hρ i)
    exact Nat.mul_pos (by logtwo_quiet omega) (hkpos i)
  · intro i
    have hnum : (((ρ i).num.toNat : ℕ) : ℝ) = ((ρ i).num : ℝ) := by logtwo_quiet
      exact_mod_cast (Int.toNat_of_nonneg (Rat.num_pos.mpr (hρ i)).le)
    have hcastD : (D : ℝ) = ((ρ i).den : ℝ) * (k i : ℝ) := by logtwo_quiet
      exact_mod_cast hk i
    have hkne : (k i : ℝ) ≠ 0 := by logtwo_quiet exact_mod_cast (hkpos i).ne'
    have hdenne : ((ρ i).den : ℝ) ≠ 0 := by logtwo_quiet exact_mod_cast (ρ i).den_ne_zero
    rw [Rat.cast_def, hcastD]
    change ((ρ i).num : ℝ) / ((ρ i).den : ℝ) =
      (((ρ i).num.toNat * k i : ℕ) : ℝ) / (((ρ i).den : ℝ) * (k i : ℝ))
    rw [Nat.cast_mul, hnum]
    field_simp

end PiExponent

end OAI
end Source0052

-- Source: OAI/NumberTheory/PiExponent/Polynomials/SimplexRational.lean
section Source0053
-- Modified in this edition: unused plain lemmas removed; see reduction.json.
/-
Modification notice for the LogTwo project.
Derived from openai/math (Apache-2.0), revision adc7f1241b42e322a6451854ab7e4b4c146bf78a.
Original source: lean/OAI/NumberTheory/PiExponent/Polynomials/SimplexRational.lean
Changes: Convert module/import declarations to the Lean 4.34 public module format.
See ../THIRD_PARTY_NOTICES.txt for provenance and the recorded changes.
-/

namespace OAI

open scoped BigOperators
open Filter Topology

namespace PiExponent

theorem common_denominator_simplex_constant {d D : ℕ} {ρ : Fin d → ℚ}
    {w : Fin d → ℕ} (hD : 0 < D) (hw : ∀ i, 0 < w i)
    (hweights : ∀ i, (ρ i : ℝ) = (w i : ℝ) / (D : ℝ)) :
    (1 / ((d.factorial : ℝ) * ∏ i, (w i : ℝ))) * (D : ℝ) ^ d =
      1 / ((d.factorial : ℝ) * ∏ i, (ρ i : ℝ)) := by logtwo_quiet
  have hprod : (∏ i, (ρ i : ℝ)) = (∏ i, (w i : ℝ)) / (D : ℝ) ^ d := by logtwo_quiet
    simp_rw [hweights]
    rw [Finset.prod_div_distrib]
    simp
  have hDne : (D : ℝ) ≠ 0 := by logtwo_quiet exact_mod_cast hD.ne'
  have hPne : (∏ i, (w i : ℝ)) ≠ 0 :=
    (Finset.prod_pos (fun i _ => by logtwo_quiet exact_mod_cast hw i)).ne'
  have hfac : (d.factorial : ℝ) ≠ 0 := by logtwo_quiet exact_mod_cast Nat.factorial_ne_zero d
  rw [hprod]
  field_simp

theorem tendsto_card_realWeightedSimplex_rational {d : ℕ}
    (ρ : Fin d → ℚ) (hρ : ∀ i, 0 < ρ i) :
    Tendsto (fun H : ℝ =>
      ((realWeightedSimplex (fun i => (ρ i : ℝ)) H).card : ℝ) / H ^ d)
      atTop (𝓝 (1 / ((d.factorial : ℝ) * ∏ i, (ρ i : ℝ)))) := by logtwo_quiet
  obtain ⟨D, hD, w, hw, hweights⟩ := positive_rational_weights_common_denominator ρ hρ
  have h := tendsto_card_realWeightedSimplex_scaled w hw
    (show (0 : ℝ) < D by logtwo_quiet exact_mod_cast hD)
  rw [common_denominator_simplex_constant hD hw hweights] at h
  simpa only [← hweights] using h

theorem tendsto_card_strictWeightedSimplex_rational {d : ℕ}
    (ρ : Fin d → ℚ) (hρ : ∀ i, 0 < ρ i) :
    Tendsto (fun H : ℝ =>
      ((strictWeightedSimplex (fun i => (ρ i : ℝ)) H).card : ℝ) / H ^ d)
      atTop (𝓝 (1 / ((d.factorial : ℝ) * ∏ i, (ρ i : ℝ)))) := by logtwo_quiet
  obtain ⟨D, hD, w, hw, hweights⟩ := positive_rational_weights_common_denominator ρ hρ
  have h := tendsto_card_strictWeightedSimplex_scaled w hw
    (show (0 : ℝ) < D by logtwo_quiet exact_mod_cast hD)
  rw [common_denominator_simplex_constant hD hw hweights] at h
  simpa only [← hweights] using h

end PiExponent

end OAI
end Source0053

-- Source: OAI/NumberTheory/PiExponent/Polynomials/AuxiliaryPolynomial.lean
section Source0054
/-
Modification notice for the LogTwo project.
Derived from openai/math (Apache-2.0), revision adc7f1241b42e322a6451854ab7e4b4c146bf78a.
Original source: lean/OAI/NumberTheory/PiExponent/Polynomials/AuxiliaryPolynomial.lean
Changes: Convert module/import declarations to the Lean 4.34 public module format.
See ../THIRD_PARTY_NOTICES.txt for provenance and the recorded changes.
-/

namespace OAI

open scoped BigOperators
open Filter Topology

namespace PiExponent

noncomputable def polynomialOfCoefficients {d : ℕ} (S : Finset (Fin d → ℕ)) :
    (S → ℂ) →ₗ[ℂ] MvPolynomial (Fin d) ℂ := by logtwo_quiet
  classical
  exact
    { toFun := fun x => ∑ a : S, MvPolynomial.monomial
        (InterpolationMatrix.exponentVector a.val) (x a)
      map_add' := fun x y => by logtwo_quiet simp [Finset.sum_add_distrib]
      map_smul' := fun z x => by logtwo_quiet
        simp only [Pi.smul_apply, map_smul, Finset.smul_sum, RingHom.id_apply]  }

theorem exponentVector_injective {d : ℕ} :
    Function.Injective (@InterpolationMatrix.exponentVector d) := by logtwo_quiet
  intro a b h
  funext i
  have hi := congrArg (fun v : Fin d →₀ ℕ => v i) h
  simpa only [InterpolationMatrix.exponentVector_apply] using hi

@[simp] theorem polynomialOfCoefficients_coeff {d : ℕ} (S : Finset (Fin d → ℕ))
    (x : S → ℂ) (a : S) :
    (polynomialOfCoefficients S x).coeff (InterpolationMatrix.exponentVector a.val) = x a := by logtwo_quiet
  classical
  change (∑ exponent : S, MvPolynomial.monomial
    (InterpolationMatrix.exponentVector exponent.val) (x exponent)).coeff
      (InterpolationMatrix.exponentVector a.val) = x a
  simp only [MvPolynomial.coeff_sum, MvPolynomial.coeff_monomial]
  rw [Finset.sum_eq_single a]
  · simp
  · intro b hb hba
    have hne : InterpolationMatrix.exponentVector b.val ≠
        InterpolationMatrix.exponentVector a.val := by logtwo_quiet
      intro h
      exact hba (Subtype.ext (exponentVector_injective h))
    simp [hne]
  · simp

theorem polynomialOfCoefficients_injective {d : ℕ} (S : Finset (Fin d → ℕ)) :
    Function.Injective (polynomialOfCoefficients S) := by logtwo_quiet
  intro x y h
  funext a
  have := congrArg (fun p : MvPolynomial (Fin d) ℂ =>
    p.coeff (InterpolationMatrix.exponentVector a.val)) h
  simpa only [polynomialOfCoefficients_coeff] using this

theorem polynomialOfCoefficients_support {d : ℕ} (S : Finset (Fin d → ℕ))
    (x : S → ℂ) :
    (polynomialOfCoefficients S x).support ⊆ S.image InterpolationMatrix.exponentVector := by logtwo_quiet
  classical
  intro e he
  by_contra hn
  have hzero : (polynomialOfCoefficients S x).coeff e = 0 := by logtwo_quiet
    change (∑ exponent : S, MvPolynomial.monomial
      (InterpolationMatrix.exponentVector exponent.val) (x exponent)).coeff e = 0
    rw [MvPolynomial.coeff_sum]
    apply Finset.sum_eq_zero
    intro a ha
    have hne : InterpolationMatrix.exponentVector a.val ≠ e := by logtwo_quiet
      intro h
      exact hn (Finset.mem_image.mpr ⟨a.val, a.property, h⟩)
    simp [MvPolynomial.coeff_monomial, hne]
  exact (MvPolynomial.mem_support_iff.mp he) hzero

theorem polynomialOfCoefficients_weighted {m : ℕ} (W : Fin (m + 1) → ℝ)
    (hW : ∀ i, 0 < W i) (N : ℝ)
    (x : ↥(realWeightedSimplex W N) → ℂ) :
    PiExponentApprox.HasWeightedDegreeLE W N
      (polynomialOfCoefficients (realWeightedSimplex W N) x) := by logtwo_quiet
  classical
  intro e he
  obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp
    (polynomialOfCoefficients_support _ x he)
  have h := (mem_realWeightedSimplex hW).mp ha
  simpa only [PiExponentApprox.monomialWeight,
    InterpolationMatrix.exponentVector_apply, mul_comm] using h

theorem exists_nonzero_kernel_of_card_lt {C R : Type*} [Fintype C] [Fintype R]
    (E : (C → ℂ) →ₗ[ℂ] (R → ℂ)) (h : Fintype.card R < Fintype.card C) :
    ∃ x : C → ℂ, x ≠ 0 ∧ E x = 0 := by logtwo_quiet
  have hk : LinearMap.ker E ≠ ⊥ := LinearMap.ker_ne_bot_of_finrank_lt
    (by logtwo_quiet simpa only [Module.finrank_fintype_fun_eq_card] using h)
  obtain ⟨x, hx, hn⟩ := (LinearMap.ker E).ne_bot_iff.mp hk
  exact ⟨x, hn, LinearMap.mem_ker.mp hx⟩

theorem tendsto_card_strictWeightedSimplex_scale {d : ℕ} (V : Fin d → ℚ)
    (hV : ∀ i, 0 < V i) {a : ℝ} (ha : 0 < a) :
    Tendsto (fun N : ℝ =>
      ((strictWeightedSimplex (fun i => (V i : ℝ)) (a * N)).card : ℝ) / N ^ d)
      atTop (𝓝 (a ^ d / ((d.factorial : ℝ) * ∏ i, (V i : ℝ)))) := by logtwo_quiet
  have ht : Tendsto (fun N : ℝ => a * N) atTop atTop :=
    Tendsto.const_mul_atTop ha tendsto_id
  have h := ((tendsto_card_strictWeightedSimplex_rational V hV).comp ht).mul_const (a ^ d)
  have heq : 1 / ((d.factorial : ℝ) * ∏ i, (V i : ℝ)) * a ^ d =
      a ^ d / ((d.factorial : ℝ) * ∏ i, (V i : ℝ)) := by logtwo_quiet ring
  rw [heq] at h
  apply h.congr'
  exact Eventually.of_forall (fun N => by logtwo_quiet
    simp only [Function.comp_apply, mul_pow]
    field_simp)

theorem eventually_auxiliary_card_lt {d : ℕ} (W V : Fin d → ℚ)
    (hW : ∀ i, 0 < W i) (hV : ∀ i, 0 < V i) (K : ℕ)
    {a : ℝ} (ha : 0 < a)
    (hvol : (K : ℝ) * a ^ d * (∏ i, (W i : ℝ)) / (∏ i, (V i : ℝ)) < 1) :
    ∀ᶠ N : ℝ in atTop,
      K * (strictWeightedSimplex (fun i => (V i : ℝ)) (a * N)).card <
        (realWeightedSimplex (fun i => (W i : ℝ)) N).card := by logtwo_quiet
  have hPW : 0 < ∏ i, (W i : ℝ) := Finset.prod_pos (fun i _ => by logtwo_quiet exact_mod_cast hW i)
  have hPV : 0 < ∏ i, (V i : ℝ) := Finset.prod_pos (fun i _ => by logtwo_quiet exact_mod_cast hV i)
  have hF : (0 : ℝ) < d.factorial := by logtwo_quiet exact_mod_cast Nat.factorial_pos d
  have hconst : (K : ℝ) * (a ^ d / ((d.factorial : ℝ) * ∏ i, (V i : ℝ))) <
      1 / ((d.factorial : ℝ) * ∏ i, (W i : ℝ)) := by logtwo_quiet
    have hmain := (div_lt_one hPV).mp hvol
    apply (lt_div_iff₀ (mul_pos hF hPW)).mpr
    have heq : (K : ℝ) * (a ^ d / ((d.factorial : ℝ) * ∏ i, (V i : ℝ))) *
        ((d.factorial : ℝ) * ∏ i, (W i : ℝ)) =
        (K : ℝ) * a ^ d * (∏ i, (W i : ℝ)) / (∏ i, (V i : ℝ)) := by logtwo_quiet
      field_simp
    rw [heq]
    exact hvol
  have hsmall := ((tendsto_card_strictWeightedSimplex_scale V hV ha).const_mul (K : ℝ)).eventually_lt
    (tendsto_card_realWeightedSimplex_rational W hW) hconst
  filter_upwards [hsmall, eventually_gt_atTop (0 : ℝ)] with N hN hNpos
  have hscaled : ((K * (strictWeightedSimplex (fun i => (V i : ℝ)) (a * N)).card : ℕ) : ℝ) /
      N ^ d < ((realWeightedSimplex (fun i => (W i : ℝ)) N).card : ℝ) / N ^ d := by logtwo_quiet
    simpa only [Nat.cast_mul, mul_div_assoc] using hN
  exact_mod_cast (div_lt_div_iff_of_pos_right (pow_pos hNpos d)).mp hscaled

theorem eventually_exists_auxiliaryPolynomial {m : ℕ} (W V : Fin (m + 1) → ℚ)
    (hW : ∀ i, 0 < W i) (hV : ∀ i, 0 < V i) (K : ℕ)
    {a : ℝ} (ha : 0 < a)
    (hvol : (K : ℝ) * a ^ (m + 1) * (∏ i, (W i : ℝ)) / (∏ i, (V i : ℝ)) < 1) :
    ∀ᶠ N : ℝ in atTop,
      ∀ E : PiExponentApprox.FramePolynomial m →ₗ[ℂ]
        ((Fin K × ↥(strictWeightedSimplex (fun i => (V i : ℝ)) (a * N))) → ℂ),
      ∃ p : PiExponentApprox.FramePolynomial m, p ≠ 0 ∧
        PiExponentApprox.HasWeightedDegreeLE (fun i => (W i : ℝ)) N p ∧ E p = 0 := by logtwo_quiet
  classical
  filter_upwards [eventually_auxiliary_card_lt W V hW hV K ha hvol] with N hN
  intro E
  let S := realWeightedSimplex (fun i => (W i : ℝ)) N
  let A := E.comp (polynomialOfCoefficients S)
  have hcard : Fintype.card (Fin K × ↥(strictWeightedSimplex (fun i => (V i : ℝ)) (a * N))) <
      Fintype.card S := by logtwo_quiet simpa [S] using hN
  obtain ⟨x, hx, hAx⟩ := exists_nonzero_kernel_of_card_lt A hcard
  refine ⟨polynomialOfCoefficients S x, ?_, ?_, hAx⟩
  · intro hp
    apply hx
    apply polynomialOfCoefficients_injective S
    simpa using hp
  · exact polynomialOfCoefficients_weighted (fun i => (W i : ℝ))
      (fun i => by logtwo_quiet exact_mod_cast hW i) N x

end PiExponent

end OAI
end Source0054

-- Source: OAI/NumberTheory/PiExponent/Jets/OrdinaryAuxiliaryJet.lean
section Source0055
-- Modified in this edition: unused plain lemmas removed; see reduction.json.
/-
Modification notice for the LogTwo project.
Derived from openai/math (Apache-2.0), revision adc7f1241b42e322a6451854ab7e4b4c146bf78a.
Original source: lean/OAI/NumberTheory/PiExponent/Jets/OrdinaryAuxiliaryJet.lean
Changes: Convert module/import declarations to the Lean 4.34 public module format.
See ../THIRD_PARTY_NOTICES.txt for provenance and the recorded changes.
-/

namespace OAI

noncomputable section
open scoped BigOperators
open Filter Topology
namespace PiExponent.OrdinaryAuxiliaryJet

def formalJet {n : ℕ} (c : Fin n → ℂ) :
    MvPolynomial (Fin n) ℂ →ₐ[ℂ] MvPowerSeries (Fin n) ℂ :=
  MvPolynomial.aeval (fun i => MvPowerSeries.C (c i) + MvPowerSeries.X i)

def evaluation {n : ℕ} (K : ℕ) (V : Fin n → ℝ) (H : ℝ)
    (c : Fin K → Fin n → ℂ) :
    MvPolynomial (Fin n) ℂ →ₗ[ℂ]
      ((Fin K × ↥(strictWeightedSimplex V H)) → ℂ) :=
  LinearMap.pi (fun r =>
    (MvPowerSeries.coeff (InterpolationMatrix.exponentVector r.2.val)).comp
      (formalJet (c r.1)).toLinearMap)

theorem polynomialOfCoefficients_supportBound {n : ℕ} (W : Fin n → ℝ)
    (hW : ∀ i, 0 < W i) (N : ℝ)
    (x : ↥(realWeightedSimplex W N) → ℂ) :
    WeightedSliceDegree.SupportBound W N
      (polynomialOfCoefficients (realWeightedSimplex W N) x) := by logtwo_quiet
  intro e he
  obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp
    (polynomialOfCoefficients_support _ x he)
  have h := (mem_realWeightedSimplex hW).mp ha
  simpa only [Finsupp.weight_eq_sum, InterpolationMatrix.exponentVector_apply,
    nsmul_eq_mul, mul_comm] using h

theorem eventually_exists_auxiliaryPolynomial {n : ℕ}
    (W V : Fin n → ℚ) (hW : ∀ i, 0 < W i) (hV : ∀ i, 0 < V i)
    (K : ℕ) {a : ℝ} (ha : 0 < a)
    (hvol : (K : ℝ) * a^n * (∏ i, (W i : ℝ)) / (∏ i, (V i : ℝ)) < 1)
    (c : Fin K → Fin n → ℂ) :
    ∀ᶠ N : ℝ in atTop, ∃ p : MvPolynomial (Fin n) ℂ, p ≠ 0 ∧
      WeightedSliceDegree.SupportBound (fun i => (W i : ℝ)) N p ∧
      ∀ j d, Finsupp.weight (fun i => (V i : ℝ)) d < a*N →
        MvPowerSeries.coeff d (formalJet (c j) p) = 0 := by logtwo_quiet
  classical
  filter_upwards [eventually_auxiliary_card_lt W V hW hV K ha hvol] with N hN
  let S := realWeightedSimplex (fun i => (W i : ℝ)) N
  let E := (evaluation K (fun i => (V i : ℝ)) (a*N) c).comp (polynomialOfCoefficients S)
  have hcard : Fintype.card (Fin K × ↥(strictWeightedSimplex (fun i => (V i : ℝ)) (a*N))) <
      Fintype.card S := by logtwo_quiet simpa [S] using hN
  obtain ⟨x, hx, hEx⟩ := exists_nonzero_kernel_of_card_lt E hcard
  refine ⟨polynomialOfCoefficients S x, ?_, ?_, ?_⟩
  · intro hp
    apply hx
    apply polynomialOfCoefficients_injective S
    simpa using hp
  · exact polynomialOfCoefficients_supportBound (fun i => (W i : ℝ))
      (fun i => by logtwo_quiet exact_mod_cast hW i) N x
  · intro j d hd
    have hmem : (fun i => d i) ∈ strictWeightedSimplex (fun i => (V i : ℝ)) (a*N) := by logtwo_quiet
      apply (mem_strictWeightedSimplex (fun i => by logtwo_quiet exact_mod_cast hV i)).mpr
      simpa [Finsupp.weight_eq_sum, nsmul_eq_mul, mul_comm] using hd
    have hh := congrFun hEx (j, ⟨(fun i => d i), hmem⟩)
    have hd' : InterpolationMatrix.exponentVector (fun i => d i) = d := by logtwo_quiet ext i; rfl
    simpa [E, evaluation, hd'] using hh

end PiExponent.OrdinaryAuxiliaryJet
end

end OAI
end Source0055

-- Source: OAI/NumberTheory/PiExponent/Approximation/PersistentComponents.lean
section Source0056
-- Modified in this edition: unused plain lemmas removed; see reduction.json.
/-
Modification notice for the LogTwo project.
Derived from openai/math (Apache-2.0), revision adc7f1241b42e322a6451854ab7e4b4c146bf78a.
Original source: lean/OAI/NumberTheory/PiExponent/Approximation/PersistentComponents.lean
Changes: Convert module/import declarations to the Lean 4.34 public module format.
See ../THIRD_PARTY_NOTICES.txt for provenance and the recorded changes.
-/

namespace OAI

namespace PiExponent.PersistentComponents

variable {R : Type*} [CommRing R]

theorem prime_height_step {P Q : Ideal R} (hP : P.IsPrime) (hQ : Q.IsPrime)
    (hPQ : P < Q) : P.height + 1 ≤ Q.height := by logtwo_quiet
  let := hP
  let := hQ
  exact Ideal.height_add_one_le_of_lt_of_isPrime hPQ

theorem exists_adjacent_eq_of_height_bound (P : ℕ → Ideal R) (m : ℕ)
    (hPrime : ∀ i ≤ m + 1, (P i).IsPrime)
    (hstep : ∀ i ≤ m, P i ≤ P (i + 1))
    (hheight : (P (m + 1)).height ≤ m) :
    ∃ i ≤ m, P i = P (i + 1) := by logtwo_quiet
  by_contra h
  have hneq : ∀ i ≤ m, P i ≠ P (i + 1) := by logtwo_quiet simpa only [not_exists, not_and] using h
  have hgrowth : ∀ i ≤ m + 1, (i : ℕ∞) ≤ (P i).height := by logtwo_quiet
    intro i hi
    induction i with
    | zero => exact bot_le
    | succ i ih =>
      have him : i ≤ m := by logtwo_quiet omega
      have hip : i ≤ m + 1 := by logtwo_quiet omega
      have hs := prime_height_step (hPrime i hip) (hPrime (i + 1) hi)
        (lt_of_le_of_ne (hstep i him) (hneq i him))
      have hadd : (i : ℕ∞) + 1 ≤ (P i).height + 1 := by logtwo_quiet
        gcongr
        exact ih hip
      simpa only [Nat.cast_add, Nat.cast_one] using hadd.trans hs
  have hf := (hgrowth (m + 1) le_rfl).trans hheight
  exact (by logtwo_quiet exact_mod_cast (Nat.not_succ_le_self m) : ¬ ((m + 1 : ℕ) : ℕ∞) ≤ (m : ℕ∞)) hf

theorem exists_nested_minimalPrimes (I : ℕ → Ideal R) (hI : Monotone I)
    (n : ℕ) (P : Ideal R) (hP : P.IsPrime) (hIP : I n ≤ P) :
    ∃ Q : ℕ → Ideal R,
      (∀ i ≤ n, Q i ∈ (I i).minimalPrimes) ∧
      (∀ i < n, Q i ≤ Q (i + 1)) ∧ Q n ≤ P := by logtwo_quiet
  induction n generalizing P with
  | zero =>
    let := hP
    obtain ⟨Q, hQ, hQP⟩ := Ideal.exists_minimalPrimes_le hIP
    refine ⟨fun _ => Q, ?_, ?_, hQP⟩
    · intro i hi
      have hi0 : i = 0 := by logtwo_quiet omega
      simpa only [hi0] using hQ
    · intro i hi
      omega
  | succ n ih =>
    let := hP
    obtain ⟨Qlast, hQlast, hQlastP⟩ := Ideal.exists_minimalPrimes_le hIP
    obtain ⟨Q, hQ, hstep, hQlastle⟩ :=
      ih Qlast hQlast.isPrime ((hI (Nat.le_succ n)).trans hQlast.le)
    refine ⟨fun i => if i = n + 1 then Qlast else Q i, ?_, ?_, ?_⟩
    · intro i hi
      by_cases hei : i = n + 1
      · simpa [hei] using hQlast
      · simpa [hei] using hQ i (by logtwo_quiet omega)
    · intro i hi
      have hin : i ≠ n + 1 := by logtwo_quiet omega
      by_cases hei : i = n
      · simpa [hei] using hQlastle
      · have hip : i + 1 ≠ n + 1 := by logtwo_quiet omega
        simpa [hin, hip, hei] using hstep i (by logtwo_quiet omega)
    · simpa [Nat.succ_eq_add_one] using hQlastP

theorem exists_persistent_minimalPrime (I : ℕ → Ideal R) (hI : Monotone I)
    (m : ℕ) (P : Ideal R) (hP : P.IsPrime)
    (hIP : I (m + 2) ≤ P) (hheight : P.height ≤ m) :
    ∃ r < m + 2, ∃ Q : Ideal R,
      Q ∈ (I r).minimalPrimes ∧ I (r + 1) ≤ Q ∧ Q ≤ P := by logtwo_quiet
  obtain ⟨Q, hQ, hstep, hQP⟩ := exists_nested_minimalPrimes I hI (m + 2) P hP hIP
  have hmono : ∀ i j, i ≤ j → j ≤ m + 2 → Q i ≤ Q j := by logtwo_quiet
    intro i j hij hj
    induction j with
    | zero =>
      have hi : i = 0 := by logtwo_quiet omega
      simp only [hi, le_refl]
    | succ j ih =>
      by_cases heq : i = j + 1
      · simp [heq]
      · exact (ih (by logtwo_quiet omega) (by logtwo_quiet omega)).trans (hstep j (by logtwo_quiet omega))
  have hbound : (Q (m + 1)).height ≤ m :=
    (Ideal.height_mono ((hmono (m + 1) (m + 2) (by logtwo_quiet omega) le_rfl).trans hQP)).trans hheight
  obtain ⟨r, hr, heq⟩ := exists_adjacent_eq_of_height_bound Q m
    (fun i hi => (hQ i (by logtwo_quiet omega)).isPrime) (fun i hi => hstep i (by logtwo_quiet omega)) hbound
  refine ⟨r, by logtwo_quiet omega, Q r, hQ r (by logtwo_quiet omega), ?_, ?_⟩
  · rw [heq]
    exact (hQ (r + 1) (by logtwo_quiet omega)).le
  · exact (hmono r (m + 2) (by logtwo_quiet omega) le_rfl).trans hQP

theorem minimalPrime_persists {I J Q : Ideal R} (hIJ : I ≤ J)
    (hQ : Q ∈ I.minimalPrimes) (hJQ : J ≤ Q) : Q ∈ J.minimalPrimes := by logtwo_quiet
  refine ⟨⟨hQ.isPrime, hJQ⟩, ?_⟩
  intro P hP hPQ
  exact hQ.2 ⟨hP.1, hIJ.trans hP.2⟩ hPQ

theorem exists_persistent_minimalPrime_pair (I : ℕ → Ideal R) (hI : Monotone I)
    (m : ℕ) (P : Ideal R) (hP : P.IsPrime)
    (hIP : I (m + 2) ≤ P) (hheight : P.height ≤ m) :
    ∃ r < m + 2, ∃ Q : Ideal R,
      Q ∈ (I r).minimalPrimes ∧ Q ∈ (I (r + 1)).minimalPrimes ∧ Q ≤ P := by logtwo_quiet
  obtain ⟨r, hr, Q, hQ, hnext, hQP⟩ :=
    exists_persistent_minimalPrime I hI m P hP hIP hheight
  exact ⟨r, hr, Q, hQ, minimalPrime_persists (hI (Nat.le_succ r)) hQ hnext, hQP⟩

theorem minimalPrime_height_pos_of_nonzero_mem [IsDomain R] {I Q : Ideal R}
    (hQ : Q ∈ I.minimalPrimes) {F : R} (hF : F ≠ 0) (hFI : F ∈ I) :
    1 ≤ Q.height := by logtwo_quiet
  have hQbot : Q ≠ ⊥ := by logtwo_quiet
    intro h
    have hFQ := hQ.le hFI
    simp only [h, Ideal.mem_bot] at hFQ
    exact hF hFQ
  exact Order.one_le_iff_ne_zero.mpr (mt Ideal.height_eq_zero_iff_eq_bot.mp hQbot)

theorem exists_persistent_component_positive_height [IsDomain R]
    (I : ℕ → Ideal R) (hI : Monotone I) (m : ℕ) (P : Ideal R) (hP : P.IsPrime)
    (hIP : I (m + 2) ≤ P) (hheight : P.height ≤ m)
    {F : R} (hF : F ≠ 0) (hFI : F ∈ I 0) :
    ∃ r < m + 2, ∃ Q : Ideal R,
      Q ∈ (I r).minimalPrimes ∧ Q ∈ (I (r + 1)).minimalPrimes ∧ Q ≤ P ∧
      1 ≤ Q.height ∧ Q.height ≤ m := by logtwo_quiet
  obtain ⟨r, hr, Q, hQr, hQnext, hQP⟩ :=
    exists_persistent_minimalPrime_pair I hI m P hP hIP hheight
  exact ⟨r, hr, Q, hQr, hQnext, hQP,
    minimalPrime_height_pos_of_nonzero_mem hQr hF ((hI (Nat.zero_le r)) hFI),
    (Ideal.height_mono hQP).trans hheight⟩

end PiExponent.PersistentComponents

end OAI
end Source0056

-- Source: OAI/NumberTheory/PiExponent/Jets/DerivativeIdeals.lean
section Source0057
-- Modified in this edition: unused plain lemmas removed; see reduction.json.
/-
Modification notice for the LogTwo project.
Derived from openai/math (Apache-2.0), revision adc7f1241b42e322a6451854ab7e4b4c146bf78a.
Original source: lean/OAI/NumberTheory/PiExponent/Jets/DerivativeIdeals.lean
Changes: Convert module/import declarations to the Lean 4.34 public module format.
See ../THIRD_PARTY_NOTICES.txt for provenance and the recorded changes.
-/

namespace OAI

noncomputable section
namespace PiExponent.DerivativeIdeals

variable {C R ι : Type*} [CommRing C] [CommRing R] [Algebra C R]

def wordDerivative (D : ι → Derivation C R R) (word : List ι) (f : R) : R :=
  word.foldr (fun i g => D i g) f

@[simp] theorem wordDerivative_nil (D : ι → Derivation C R R) (f : R) :
    wordDerivative D [] f = f := rfl

@[simp] theorem wordDerivative_cons (D : ι → Derivation C R R) (i : ι)
    (word : List ι) (f : R) : wordDerivative D (i :: word) f = D i (wordDerivative D word f) := rfl

def wordCost (cost : ι → ℝ) (word : List ι) : ℝ := (word.map cost).sum

@[simp] theorem wordCost_nil (cost : ι → ℝ) : wordCost cost [] = 0 := rfl
@[simp] theorem wordCost_cons (cost : ι → ℝ) (i : ι) (word : List ι) :
    wordCost cost (i :: word) = cost i + wordCost cost word := rfl

def derivativeIdeal (D : ι → Derivation C R R) (cost : ι → ℝ) (bound : ℝ) (f : R) :
    Ideal R := Ideal.span {g | ∃ word, wordCost cost word ≤ bound ∧ wordDerivative D word f = g}

theorem word_mem_derivativeIdeal (D : ι → Derivation C R R) (cost : ι → ℝ)
    (bound : ℝ) (f : R) (word : List ι) (hw : wordCost cost word ≤ bound) :
    wordDerivative D word f ∈ derivativeIdeal D cost bound f :=
  Ideal.subset_span ⟨word, hw, rfl⟩

theorem derivativeIdeal_mono (D : ι → Derivation C R R) (cost : ι → ℝ)
    (f : R) {a b : ℝ} (hab : a ≤ b) :
    derivativeIdeal D cost a f ≤ derivativeIdeal D cost b f := by logtwo_quiet
  apply Ideal.span_mono
  rintro g ⟨word, hw, rfl⟩
  exact ⟨word, hw.trans hab, rfl⟩

def derivativeCore (D : Derivation C R R) (I : Ideal R) : Ideal R where
  carrier := {f | f ∈ I ∧ D f ∈ I}
  zero_mem' := by logtwo_quiet simp only [Set.mem_ofPred_eq, map_zero]; exact ⟨I.zero_mem, I.zero_mem⟩
  add_mem' := by logtwo_quiet
    intro f g hf hg
    refine ⟨I.add_mem hf.1 hg.1, ?_⟩
    rw [map_add]
    exact I.add_mem hf.2 hg.2
  smul_mem' := by logtwo_quiet
    intro r f hf
    change r * f ∈ I ∧ D (r * f) ∈ I
    refine ⟨I.mul_mem_left r hf.1, ?_⟩
    rw [Derivation.leibniz]
    exact I.add_mem (I.mul_mem_left r hf.2) (by logtwo_quiet
      simpa only [smul_eq_mul, mul_comm] using I.mul_mem_left (D r) hf.1)

theorem derivation_mem_derivativeIdeal (D : ι → Derivation C R R) (cost : ι → ℝ)
    (hcost : ∀ i, 0 ≤ cost i) (bound : ℝ) (f g : R) (i : ι)
    (hg : g ∈ derivativeIdeal D cost bound f) :
    D i g ∈ derivativeIdeal D cost (bound + cost i) f := by logtwo_quiet
  let I := derivativeIdeal D cost (bound + cost i) f
  have hle : derivativeIdeal D cost bound f ≤ derivativeCore (D i) I := by logtwo_quiet
    apply Ideal.span_le.mpr
    rintro g ⟨word, hw, rfl⟩
    refine ⟨?_, ?_⟩
    · exact word_mem_derivativeIdeal D cost (bound + cost i) f word
        (hw.trans (le_add_of_nonneg_right (hcost i)))
    · exact word_mem_derivativeIdeal D cost (bound + cost i) f (i :: word)
        (by logtwo_quiet simpa only [wordCost_cons, add_comm] using add_le_add_left hw (cost i))
  exact (hle hg).2

theorem wordDerivative_mem_derivativeIdeal (D : ι → Derivation C R R) (cost : ι → ℝ)
    (hcost : ∀ i, 0 ≤ cost i) (bound : ℝ) (f g : R) (word : List ι)
    (hg : g ∈ derivativeIdeal D cost bound f) :
    wordDerivative D word g ∈ derivativeIdeal D cost (bound + wordCost cost word) f := by logtwo_quiet
  induction word with
  | nil => simpa only [wordDerivative_nil, wordCost_nil, add_zero] using hg
  | cons i word ih =>
    have h := derivation_mem_derivativeIdeal D cost hcost
      (bound + wordCost cost word) f (wordDerivative D word g) i ih
    simpa only [wordDerivative_cons, wordCost_cons, add_assoc,
      add_comm (wordCost cost word) (cost i)] using h

theorem derivative_vanishes_on_persistent_ideal (D : ι → Derivation C R R)
    (cost : ι → ℝ) (hcost : ∀ i, 0 ≤ cost i) (bound delta : ℝ) (f g : R)
    (Q : Ideal R) (hg : g ∈ derivativeIdeal D cost bound f)
    (hpersist : derivativeIdeal D cost (bound + delta) f ≤ Q)
    (word : List ι) (hw : wordCost cost word ≤ delta) :
    wordDerivative D word g ∈ Q := by logtwo_quiet
  apply hpersist
  have hb : bound + wordCost cost word ≤ bound + delta := by logtwo_quiet linarith
  exact derivativeIdeal_mono D cost f hb
    (wordDerivative_mem_derivativeIdeal D cost hcost bound f g word hg)

end PiExponent.DerivativeIdeals
end

end OAI
end Source0057

-- Source: OAI/NumberTheory/PiExponent/Jets/OrdinaryDerivativeIdeals.lean
section Source0058
-- Modified in this edition: unused plain lemmas removed; see reduction.json.
/-
Modification notice for the LogTwo project.
Derived from openai/math (Apache-2.0), revision adc7f1241b42e322a6451854ab7e4b4c146bf78a.
Original source: lean/OAI/NumberTheory/PiExponent/Jets/OrdinaryDerivativeIdeals.lean
Changes: Convert module/import declarations to the Lean 4.34 public module format.
See ../THIRD_PARTY_NOTICES.txt for provenance and the recorded changes.
-/

namespace OAI

noncomputable section
namespace PiExponent.OrdinaryDerivatives

open scoped BigOperators
open DerivativeIdeals

abbrev Polynomial (n : ℕ) := MvPolynomial (Fin n) ℂ

def partialFrame (n : ℕ) (i : Fin n) : Derivation ℚ (Polynomial n) (Polynomial n) :=
  (MvPolynomial.pderiv i).restrictScalars ℚ

@[simp] theorem partialFrame_apply (n : ℕ) (i : Fin n) (p : Polynomial n) :
    partialFrame n i p = MvPolynomial.pderiv i p := rfl

def word (n : ℕ) (l : List (Fin n)) (p : Polynomial n) : Polynomial n :=
  wordDerivative (partialFrame n) l p

@[simp] theorem word_nil (n : ℕ) (p : Polynomial n) : word n [] p = p := rfl
@[simp] theorem word_cons (n : ℕ) (i : Fin n) (l : List (Fin n)) (p : Polynomial n) :
    word n (i :: l) p = MvPolynomial.pderiv i (word n l p) := rfl

def ideal (n : ℕ) (cost : Fin n → ℝ) (bound : ℝ) (p : Polynomial n) : Ideal (Polynomial n) :=
  derivativeIdeal (partialFrame n) cost bound p

theorem supportBound_pderiv {n : ℕ} (W : Fin n → ℝ) (N : ℝ)
    (p : Polynomial n) (hp : WeightedSliceDegree.SupportBound W N p) (i : Fin n) :
    WeightedSliceDegree.SupportBound W (N - W i) (MvPolynomial.pderiv i p) := by logtwo_quiet
  intro d hd
  have hshift : d + Finsupp.single i 1 ∈ p.support := by logtwo_quiet
    apply MvPolynomial.mem_support_iff.mpr
    intro hz
    have hh := MvPolynomial.mem_support_iff.mp hd
    apply hh
    rw [MvPolynomial.coeff_pderiv, hz, zero_mul]
  apply (le_sub_iff_add_le).mpr
  have h := hp _ hshift
  simpa only [map_add, Finsupp.weight_single, one_smul] using h

theorem supportBound_word {n : ℕ} (W : Fin n → ℝ) (N : ℝ)
    (p : Polynomial n) (hp : WeightedSliceDegree.SupportBound W N p)
    (hW : ∀ i, 0 ≤ W i) (l : List (Fin n)) :
    WeightedSliceDegree.SupportBound W N (word n l p) := by logtwo_quiet
  induction l with
  | nil => exact hp
  | cons i l ih =>
    exact (supportBound_pderiv W N (word n l p) ih i).mono (sub_le_self N (hW i))

abbrev BoundedWords {n : ℕ} (cost : Fin n → ℝ) (bound : ℝ) :=
  {l : List (Fin n) // wordCost cost l ≤ bound}

def equations {n : ℕ} (cost : Fin n → ℝ) (bound : ℝ) (p : Polynomial n) :
    BoundedWords cost bound → Polynomial n := fun l => word n l.1 p

theorem span_equations {n : ℕ} (cost : Fin n → ℝ) (bound : ℝ) (p : Polynomial n) :
    Ideal.span (Set.range (equations cost bound p)) = ideal n cost bound p := by logtwo_quiet
  unfold ideal derivativeIdeal
  congr 1
  ext g
  constructor
  · rintro ⟨l, rfl⟩
    exact ⟨l.1, l.2, rfl⟩
  · rintro ⟨l, hl, rfl⟩
    exact ⟨⟨l, hl⟩, rfl⟩

theorem equation_supportBound {n : ℕ} (cost W : Fin n → ℝ) (bound N : ℝ)
    (p : Polynomial n) (hp : WeightedSliceDegree.SupportBound W N p)
    (hW : ∀ i, 0 ≤ W i) (l : BoundedWords cost bound) :
    WeightedSliceDegree.SupportBound W N (equations cost bound p l) :=
  supportBound_word W N p hp hW l.1

end PiExponent.OrdinaryDerivatives
end

end OAI
end Source0058

-- Source: OAI/NumberTheory/PiExponent/Jets/OrdinaryJetDerivatives.lean
section Source0059
-- Modified in this edition: unused plain lemmas removed; see reduction.json.
/-
Modification notice for the LogTwo project.
Derived from openai/math (Apache-2.0), revision adc7f1241b42e322a6451854ab7e4b4c146bf78a.
Original source: lean/OAI/NumberTheory/PiExponent/Jets/OrdinaryJetDerivatives.lean
Changes: Convert module/import declarations to the Lean 4.34 public module format.
See ../THIRD_PARTY_NOTICES.txt for provenance and the recorded changes.
-/

namespace OAI

noncomputable section
namespace PiExponent.OrdinaryAuxiliaryJet

theorem formalJet_pderiv {n : ℕ} (c : Fin n → ℂ) (i : Fin n)
    (p : MvPolynomial (Fin n) ℂ) :
    formalJet c (MvPolynomial.pderiv i p) = MvPowerSeries.pderiv i (formalJet c p) := by logtwo_quiet
  apply FormalLogJet.derivation_map_of_X (formalJet c) (MvPolynomial.pderiv i)
    (MvPowerSeries.pderiv i) _ p
  intro j
  by_cases hij : i = j
  · subst j
    simp [formalJet]
  · simp [formalJet, MvPowerSeries.pderiv_X_of_ne, Ne.symm hij]

theorem formalJet_word_vanishing {n : ℕ} (c : Fin n → ℂ)
    (v : Fin n → ℚ) (hv : ∀ i, 0 ≤ v i) (H : ℚ)
    (p : MvPolynomial (Fin n) ℂ)
    (hp : formalJet c p ∈ JetGeometry.rationalWeightedIdeal v hv H)
    (word : List (Fin n)) :
    formalJet c (OrdinaryDerivatives.word n word p) ∈
      JetGeometry.rationalWeightedIdeal v hv (H - (word.map v).sum) := by logtwo_quiet
  induction word with
  | nil => simpa only [OrdinaryDerivatives.word_nil, List.map_nil, List.sum_nil, sub_zero] using hp
  | cons i word ih =>
    rw [OrdinaryDerivatives.word_cons, formalJet_pderiv]
    have h := FormalJetDerivatives.pderiv_mem_rationalWeightedIdeal v hv
      (H - (word.map v).sum) (formalJet c (OrdinaryDerivatives.word n word p)) ih i
    simpa only [List.map_cons, List.sum_cons, sub_sub, add_comm] using h

end PiExponent.OrdinaryAuxiliaryJet
end

end OAI
end Source0059

-- Source: OAI/NumberTheory/PiExponent/Jets/OrdinaryBranchEvaluation.lean
section Source0060
-- Modified in this edition: unused plain lemmas removed; see reduction.json.
/-
Modification notice for the LogTwo project.
Derived from openai/math (Apache-2.0), revision adc7f1241b42e322a6451854ab7e4b4c146bf78a.
Original source: lean/OAI/NumberTheory/PiExponent/Jets/OrdinaryBranchEvaluation.lean
Changes: Convert module/import declarations to the Lean 4.34 public module format.
See ../THIRD_PARTY_NOTICES.txt for provenance and the recorded changes.
-/

namespace OAI

noncomputable section
namespace PiExponent.OrdinaryAuxiliaryJet

open MvPowerSeries

def branchCoordinates {n : ℕ} (c : Fin n → ℂ) (x : Fin n → PowerSeries ℂ) :
    Fin n → PowerSeries ℂ := fun i => x i - PowerSeries.C (c i)

theorem branchCoordinates_hasSubst {n : ℕ} (c : Fin n → ℂ)
    (x : Fin n → PowerSeries ℂ) (hx : ∀ i, PowerSeries.constantCoeff (x i) = c i) :
    HasSubst (branchCoordinates c x) := by logtwo_quiet
  apply hasSubst_of_constantCoeff_zero
  intro i
  change PowerSeries.constantCoeff (x i - PowerSeries.C (c i)) = 0
  rw [map_sub, hx i, PowerSeries.constantCoeff_C, sub_self]

theorem formalJet_subst_branch {n : ℕ} (c : Fin n → ℂ)
    (x : Fin n → PowerSeries ℂ) (hx : ∀ i, PowerSeries.constantCoeff (x i) = c i)
    (p : MvPolynomial (Fin n) ℂ) :
    subst (branchCoordinates c x) (formalJet c p) = MvPolynomial.aeval x p := by logtwo_quiet
  let ha := branchCoordinates_hasSubst c x hx
  have heq : (substAlgHom ha).comp (formalJet c) = MvPolynomial.aeval x := by logtwo_quiet
    apply MvPolynomial.algHom_ext
    intro i
    simp only [AlgHom.comp_apply, formalJet, MvPolynomial.aeval_X, map_add]
    rw [substAlgHom_X, substAlgHom_apply, subst_C]
    change PowerSeries.C (c i) + (x i - PowerSeries.C (c i)) = x i
    ring
  simpa only [AlgHom.comp_apply, substAlgHom_apply] using AlgHom.congr_fun heq p

theorem ordinaryWord_branch_order {n : ℕ}
    (c : Fin n → ℂ) (x : Fin n → PowerSeries ℂ)
    (hx : ∀ i, PowerSeries.constantCoeff (x i) = c i)
    (v : Fin n → ℚ) (hv : ∀ i, 0 ≤ v i) (mu H : ℚ) (hmu : 0 ≤ mu)
    (p : MvPolynomial (Fin n) ℂ)
    (hp : formalJet c p ∈ JetGeometry.rationalWeightedIdeal v hv H)
    (hcontact : ∀ i (k : ℕ), (branchCoordinates c x i).order = (k : ℕ∞) →
      mu * v i ≤ (k : ℚ)) (word : List (Fin n)) :
    (⌈mu * (H - (word.map v).sum)⌉₊ : ℕ∞) ≤
      PowerSeries.order (MvPolynomial.aeval x (OrdinaryDerivatives.word n word p)) := by logtwo_quiet
  have h := FormalBranchOrder.rational_powerSeries_order_subst_of_mem_weightedIdeal
    v hv mu (H - (word.map v).sum) hmu
    (formalJet c (OrdinaryDerivatives.word n word p)) (branchCoordinates c x)
    (branchCoordinates_hasSubst c x hx)
    (formalJet_word_vanishing c v hv H p hp word) hcontact
  rwa [formalJet_subst_branch c x hx] at h

end PiExponent.OrdinaryAuxiliaryJet
end

end OAI
end Source0060

-- Source: OAI/NumberTheory/PiExponent/Jets/OrdinaryDVRBranchJet.lean
section Source0061
/-
Modification notice for the LogTwo project.
Derived from openai/math (Apache-2.0), revision adc7f1241b42e322a6451854ab7e4b4c146bf78a.
Original source: lean/OAI/NumberTheory/PiExponent/Jets/OrdinaryDVRBranchJet.lean
Changes: Convert module/import declarations to the Lean 4.34 public module format.
See ../THIRD_PARTY_NOTICES.txt for provenance and the recorded changes.
-/

namespace OAI

noncomputable section
namespace PiExponent.OrdinaryDVRBranchJet
open OrdinaryAuxiliaryJet

variable {A : Type*} [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
    [Algebra ℂ A] [Algebra.IsIntegral ℂ (IsLocalRing.ResidueField A)]

theorem expansion_aeval {n : ℕ} (x : Fin n → A) (p : MvPolynomial (Fin n) ℂ) :
    DVRBranch.expansion ℂ A (MvPolynomial.aeval x p) =
      MvPolynomial.aeval (fun i => DVRBranch.expansion ℂ A (x i)) p := by logtwo_quiet
  have h : (DVRBranch.expansion ℂ A).comp (MvPolynomial.aeval x) =
      MvPolynomial.aeval (fun i => DVRBranch.expansion ℂ A (x i)) := by logtwo_quiet
    apply MvPolynomial.algHom_ext
    intro i
    simp
  exact AlgHom.congr_fun h p

def coordinates {n : ℕ} (c : Fin n → ℂ) (x : Fin n → A) :
    Fin n → PowerSeries ℂ :=
  branchCoordinates c (fun i => DVRBranch.expansion ℂ A (x i))

theorem coordinates_centered {n : ℕ} (c : Fin n → ℂ) (x : Fin n → A)
    (hx : ∀ i, CurveLocalOrder.residueAugmentation ℂ A (x i) = c i) :
    ∀ i, PowerSeries.constantCoeff (coordinates c x i) = 0 := by logtwo_quiet
  intro i
  change PowerSeries.constantCoeff
    (DVRBranch.expansion ℂ A (x i) - PowerSeries.C (c i)) = 0
  rw [map_sub, DVRBranch.expansion_constantCoeff, hx i,
    PowerSeries.constantCoeff_C, sub_self]

theorem coordinates_nonzero {n : ℕ} (c : Fin n → ℂ) (x : Fin n → A)
    (hnc : ∃ i, x i ≠ algebraMap ℂ A (c i)) :
    ∃ i, coordinates c x i ≠ 0 := by logtwo_quiet
  obtain ⟨i, hi⟩ := hnc
  refine ⟨i, ?_⟩
  intro hz
  apply hi
  apply DVRBranch.expansion_injective ℂ A
  rw [AlgHom.commutes]
  change DVRBranch.expansion ℂ A (x i) = PowerSeries.C (c i)
  exact sub_eq_zero.mp hz

def contact {n : ℕ} (v : Fin n → ℚ) (c : Fin n → ℂ) (x : Fin n → A)
    (hnc : ∃ i, x i ≠ algebraMap ℂ A (c i)) : ℚ :=
  BranchContact.contact v (coordinates c x) (coordinates_nonzero c x hnc)

theorem contact_pos {n : ℕ} (v : Fin n → ℚ) (hv : ∀ i, 0 < v i)
    (c : Fin n → ℂ) (x : Fin n → A)
    (hx : ∀ i, CurveLocalOrder.residueAugmentation ℂ A (x i) = c i)
    (hnc : ∃ i, x i ≠ algebraMap ℂ A (c i)) :
    0 < contact v c x hnc :=
  BranchContact.contact_pos v hv _ _ (coordinates_centered c x hx)

theorem ordinaryWord_addVal_lower {n : ℕ}
    (v : Fin n → ℚ) (hv : ∀ i, 0 < v i) (H : ℚ)
    (c : Fin n → ℂ) (x : Fin n → A)
    (hx : ∀ i, CurveLocalOrder.residueAugmentation ℂ A (x i) = c i)
    (hnc : ∃ i, x i ≠ algebraMap ℂ A (c i))
    (p : MvPolynomial (Fin n) ℂ)
    (hp : formalJet c p ∈ JetGeometry.rationalWeightedIdeal v (fun i => (hv i).le) H)
    (word : List (Fin n)) :
    (⌈contact v c x hnc * (H - (word.map v).sum)⌉₊ : ℕ∞) ≤
      IsDiscreteValuationRing.addVal A
        (MvPolynomial.aeval x (OrdinaryDerivatives.word n word p)) := by logtwo_quiet
  have h := ordinaryWord_branch_order c (fun i => DVRBranch.expansion ℂ A (x i))
    (fun i => by logtwo_quiet simpa using hx i) v (fun i => (hv i).le)
    (contact v c x hnc) H (contact_pos v hv c x hx hnc).le p hp
    (BranchContact.contact_bound v hv _ _) word
  rwa [← expansion_aeval, DVRBranch.expansion_order] at h

theorem ordinaryWord_addVal_toNat_lower {n : ℕ}
    (v : Fin n → ℚ) (hv : ∀ i, 0 < v i) (H : ℚ)
    (c : Fin n → ℂ) (x : Fin n → A)
    (hx : ∀ i, CurveLocalOrder.residueAugmentation ℂ A (x i) = c i)
    (hnc : ∃ i, x i ≠ algebraMap ℂ A (c i))
    (p : MvPolynomial (Fin n) ℂ)
    (hp : formalJet c p ∈ JetGeometry.rationalWeightedIdeal v (fun i => (hv i).le) H)
    (word : List (Fin n))
    (hne : MvPolynomial.aeval x (OrdinaryDerivatives.word n word p) ≠ 0) :
    contact v c x hnc * (H - (word.map v).sum) ≤
      ((IsDiscreteValuationRing.addVal A
        (MvPolynomial.aeval x (OrdinaryDerivatives.word n word p))).toNat : ℚ) := by logtwo_quiet
  have h := ordinaryWord_addVal_lower v hv H c x hx hnc p hp word
  have hn := IsDiscreteValuationRing.addVal_eq_top_iff.not.mpr hne
  have hh := ENat.toNat_le_toNat h hn
  exact Nat.ceil_le.mp (by logtwo_quiet simpa using hh)

theorem ordinaryWord_colength_lower {n : ℕ}
    (v : Fin n → ℚ) (hv : ∀ i, 0 < v i) (H : ℚ)
    (c : Fin n → ℂ) (x : Fin n → A)
    (hx : ∀ i, CurveLocalOrder.residueAugmentation ℂ A (x i) = c i)
    (hnc : ∃ i, x i ≠ algebraMap ℂ A (c i))
    (p : MvPolynomial (Fin n) ℂ)
    (hp : formalJet c p ∈ JetGeometry.rationalWeightedIdeal v (fun i => (hv i).le) H)
    (word : List (Fin n))
    (hne : MvPolynomial.aeval x (OrdinaryDerivatives.word n word p) ≠ 0) :
    contact v c x hnc * (H - (word.map v).sum) ≤
      ((Module.length A (A ⧸ Ideal.span {
        MvPolynomial.aeval x (OrdinaryDerivatives.word n word p)})).toNat : ℚ) := by logtwo_quiet
  rw [CurveLocalOrder.length_quotient_span_eq_addVal hne]
  exact ordinaryWord_addVal_toNat_lower v hv H c x hx hnc p hp word hne

end PiExponent.OrdinaryDVRBranchJet
end

end OAI
end Source0061

-- Source: OAI/NumberTheory/PiExponent/LocalAlgebra/FibreContact.lean
section Source0062
/-
Modification notice for the LogTwo project.
Derived from openai/math (Apache-2.0), revision adc7f1241b42e322a6451854ab7e4b4c146bf78a.
Original source: lean/OAI/NumberTheory/PiExponent/LocalAlgebra/FibreContact.lean
Changes: Convert module/import declarations to the Lean 4.34 public module format.
See ../THIRD_PARTY_NOTICES.txt for provenance and the recorded changes.
-/

namespace OAI

noncomputable section
namespace PiExponent.FibreContact

theorem contact_zero_cons {m : ℕ} (v : Fin (m+1) → ℚ)
    (a : Fin m → PowerSeries ℂ) (ha : ∃ i, a i ≠ 0)
    (hfull : ∃ i, (Fin.cases 0 a : Fin (m+1) → PowerSeries ℂ) i ≠ 0) :
    BranchContact.contact v (Fin.cases 0 a) hfull =
      BranchContact.contact (fun i => v i.succ) a ha := by logtwo_quiet
  apply le_antisymm
  · obtain ⟨i, hi, he⟩ := BranchContact.exists_attains (fun i => v i.succ) a ha
    have hh := BranchContact.contact_le v
      (Fin.cases (0 : PowerSeries ℂ) a : Fin (m+1) → PowerSeries ℂ) hfull i.succ
      (by logtwo_quiet simpa only [Fin.cases_succ] using hi)
    simp only [Fin.cases_succ] at hh
    exact hh.trans_eq he.symm
  · obtain ⟨i, hi, he⟩ := BranchContact.exists_attains v (Fin.cases (0 : PowerSeries ℂ) a : Fin (m+1) → PowerSeries ℂ) hfull
    cases i using Fin.cases with
    | zero => exact (hi rfl).elim
    | succ i =>
      have hh := BranchContact.contact_le (fun i => v i.succ) a ha i
        (by logtwo_quiet simpa only [Fin.cases_succ] using hi)
      simp only [Fin.cases_succ] at he
      exact hh.trans_eq he.symm

variable {A : Type*} [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
    [Algebra ℂ A] [Algebra.IsIntegral ℂ (IsLocalRing.ResidueField A)]

theorem coordinates_one {m : ℕ} (c : Fin m → ℂ) (x : Fin m → A) :
    DVRBranchJet.coordinates c (1 : A) x =
      Fin.cases 0 (OrdinaryDVRBranchJet.coordinates c x) := by logtwo_quiet
  funext i
  cases i using Fin.cases with
  | zero => simp [DVRBranchJet.coordinates, FormalBranchEvaluation.branchCoordinates]
  | succ i =>
    simp only [DVRBranchJet.coordinates, FormalBranchEvaluation.branchCoordinates,
      Fin.cases_succ, map_one, sub_self,
      PowerSeries.subst_zero_of_constantCoeff_zero PowerSeries.constantCoeff_log, sub_zero]
    rfl

theorem logarithmic_contact_eq_ordinary {m : ℕ} (v : Fin (m+1) → ℚ)
    (c : Fin m → ℂ) (x : Fin m → A)
    (hnc : ∃ i, x i ≠ algebraMap ℂ A (c i)) :
    DVRBranchJet.contact v c (1 : A) x (Or.inr hnc) =
      OrdinaryDVRBranchJet.contact (fun i => v i.succ) c x hnc := by logtwo_quiet
  have ha := OrdinaryDVRBranchJet.coordinates_nonzero c x hnc
  have hb : ∃ i, (Fin.cases (0 : PowerSeries ℂ)
      (OrdinaryDVRBranchJet.coordinates c x) : Fin (m+1) → PowerSeries ℂ) i ≠ 0 := by logtwo_quiet
    obtain ⟨i, hi⟩ := ha
    exact ⟨i.succ, by logtwo_quiet simpa only [Fin.cases_succ] using hi⟩
  have hcongr {b d : Fin (m+1) → PowerSeries ℂ} (he : b = d)
      (hb : ∃ i, b i ≠ 0) (hd : ∃ i, d i ≠ 0) :
      BranchContact.contact v b hb = BranchContact.contact v d hd := by logtwo_quiet subst d; rfl
  exact (hcongr (coordinates_one c x)
    (DVRBranchJet.coordinates_nonzero c 1 x (Or.inr hnc)) hb).trans
      (contact_zero_cons v (OrdinaryDVRBranchJet.coordinates c x) ha hb)

theorem weightedPole_le {ι : Type*} [Fintype ι]
    (w z : ι → ℚ) (t : ℚ) (ht : 0 ≤ t) (hcoord : ∀ i, -z i / w i ≤ t) :
    WeightedCurveDegree.weightedPole w z ≤ t := by logtwo_quiet
  apply Finset.sup'_le
  intro i hi
  cases i with
  | none => exact ht
  | some i => exact hcoord i

theorem weightedPole_zero_cons {m : ℕ} (w : Fin (m+1) → ℚ) (z : Fin m → ℚ) :
    WeightedCurveDegree.weightedPole w (Fin.cases 0 z) =
      WeightedCurveDegree.weightedPole (fun i => w i.succ) z := by logtwo_quiet
  let zz : Fin (m+1) → ℚ := Fin.cases 0 z
  let ww : Fin m → ℚ := fun i => w i.succ
  change WeightedCurveDegree.weightedPole w zz = WeightedCurveDegree.weightedPole ww z
  have hz0 : zz 0 = 0 := rfl
  have hzs (i : Fin m) : zz i.succ = z i := rfl
  have hws (i : Fin m) : ww i = w i.succ := rfl
  have hleft0 := WeightedCurveDegree.weightedPole_nonneg w zz
  have hright0 := WeightedCurveDegree.weightedPole_nonneg ww z
  apply le_antisymm
  · apply weightedPole_le w zz _ hright0
    intro i
    cases i using Fin.cases with
    | zero => simpa only [hz0, neg_zero, zero_div] using hright0
    | succ i =>
      rw [hzs]
      have hh := WeightedCurveDegree.div_le_weightedPole ww z i
      rw [hws] at hh
      exact hh
  · apply weightedPole_le ww z _ hleft0
    intro i
    have hh := WeightedCurveDegree.div_le_weightedPole w zz i.succ
    rw [hzs] at hh
    rw [hws]
    exact hh

theorem coordinatePole_one {E : Type*} [Field E] {m : ℕ}
    (val : AddValuation E (WithTop ℤ)) (w : Fin (m+1) → ℚ) (x : Fin m → E) :
    WeightedPolynomialPole.coordinatePole val (Fin.cases 1 x) w =
      WeightedPolynomialPole.coordinatePole val x (fun i => w i.succ) := by logtwo_quiet
  have h1 : WeightedPolynomialPole.coordinateOrder val 1 = 0 := by logtwo_quiet
    simp [WeightedPolynomialPole.coordinateOrder]
  have he : (fun i : Fin (m+1) =>
      (WeightedPolynomialPole.coordinateOrder val ((Fin.cases (1 : E) x : Fin (m+1) → E) i) : ℚ)) =
      Fin.cases 0 (fun i => (WeightedPolynomialPole.coordinateOrder val (x i) : ℚ)) := by logtwo_quiet
    funext i
    cases i using Fin.cases <;> simp [h1]
  unfold WeightedPolynomialPole.coordinatePole
  rw [he]
  exact weightedPole_zero_cons w _

theorem weightedDegree_one {E : Type*} [Field E] [Algebra ℂ E] {m : ℕ}
    (hfinite : ∀ f : E, Transcendental ℂ f →
      FiniteDimensional (IntermediateField.adjoin ℂ {f}) E)
    (w : Fin (m+1) → ℚ) (x : Fin m → E) :
    CurveContactSum.weightedDegree hfinite (Fin.cases (1 : E) x : Fin (m+1) → E) w =
      CurveContactSum.weightedDegree hfinite x (fun i => w i.succ) := by logtwo_quiet
  have he : CurveContactSum.weightedPoleDivisor hfinite
      (Fin.cases (1 : E) x : Fin (m+1) → E) w =
      CurveContactSum.weightedPoleDivisor hfinite x (fun i => w i.succ) := by logtwo_quiet
    ext p
    exact coordinatePole_one p.valuation w x
  unfold CurveContactSum.weightedDegree
  rw [he]

end PiExponent.FibreContact
end

end OAI
end Source0062

-- Source: OAI/NumberTheory/PiExponent/Geometry/PlaceCenteredBranch.lean
section Source0063
-- Modified in this edition: unused plain lemmas removed; see reduction.json.
/-
Modification notice for the LogTwo project.
Derived from openai/math (Apache-2.0), revision adc7f1241b42e322a6451854ab7e4b4c146bf78a.
Original source: lean/OAI/NumberTheory/PiExponent/Geometry/PlaceCenteredBranch.lean
Changes: Convert module/import declarations to the Lean 4.34 public module format.
See ../THIRD_PARTY_NOTICES.txt for provenance and the recorded changes.
-/

namespace OAI

noncomputable section
namespace PiExponent.PlaceCenteredBranch

open CurveValuationCenter CurveCenters PlaceValuationRing WeightedPolynomialPole

variable {E ι : Type*} [Field E] [Algebra ℂ E]

def lift (p : NormalizedPlace ℂ E) (z : ι → E) (c : ι → ℂ)
    (hc : Centered z c p) (i : ι) : ring p :=
  ⟨z i, hc.coordinate_nonneg i⟩

@[simp] theorem lift_coe (p : NormalizedPlace ℂ E) (z : ι → E) (c : ι → ℂ)
    (hc : Centered z c p) (i : ι) : (lift p z c hc i : E) = z i := rfl

theorem lift_nonconstant (p : NormalizedPlace ℂ E) (z : ι → E) (c : ι → ℂ)
    (hc : Centered z c p) (hnc : ∃ i, z i ≠ algebraMap ℂ E (c i)) :
    ∃ i, lift p z c hc i ≠ algebraMap ℂ (ring p) (c i) := by logtwo_quiet
  obtain ⟨i,hi⟩ := hnc
  refine ⟨i,?_⟩
  intro he
  exact hi (congrArg (fun a : ring p => (a : E)) he)

theorem lift_aeval (p : NormalizedPlace ℂ E) (z : ι → E) (c : ι → ℂ)
    (hc : Centered z c p) (f : MvPolynomial ι ℂ) :
    algebraMap (ring p) E (MvPolynomial.aeval (lift p z c hc) f) =
      MvPolynomial.aeval z f := by logtwo_quiet
  exact MvPolynomial.comp_aeval_apply (f := lift p z c hc)
    (IsScalarTower.toAlgHom ℂ (ring p) E) f

theorem coordinateOrder_aeval_eq_length
    (p : NormalizedPlace ℂ E) (z : ι → E) (c : ι → ℂ) (hc : Centered z c p)
    (f : MvPolynomial ι ℂ) (hne : MvPolynomial.aeval z f ≠ 0) :
    coordinateOrder p.valuation (MvPolynomial.aeval z f) =
      ((Module.length (ring p) ((ring p) ⧸
        Ideal.span {MvPolynomial.aeval (lift p z c hc) f})).toNat : ℤ) := by logtwo_quiet
  have hn : MvPolynomial.aeval (lift p z c hc) f ≠ 0 := by logtwo_quiet
    intro h
    apply hne
    rw [← lift_aeval p z c hc f, h, map_zero]
  rw [coordinateOrder, dite_eq_right hne, valuation_eq_fractionAddValuation p]
  have hu : Units.mk0 (MvPolynomial.aeval z f) hne =
      Units.mk0 (algebraMap (ring p) E (MvPolynomial.aeval (lift p z c hc) f))
        ((map_ne_zero_iff _ (IsFractionRing.injective (ring p) E)).mpr hn) := by logtwo_quiet
    apply Units.ext
    exact (lift_aeval p z c hc f).symm
  rw [hu]
  exact CurveLocalOrder.integerOrder_field_image_eq_length hn

variable (p : NormalizedPlace ℂ E)
    [Algebra.IsIntegral ℂ (IsLocalRing.ResidueField (ring p))]

theorem lift_residue (z : ι → E) (c : ι → ℂ) (hc : Centered z c p) (i : ι) :
    CurveLocalOrder.residueAugmentation ℂ (ring p) (lift p z c hc i) = c i := by logtwo_quiet
  have hm : lift p z c hc i - algebraMap ℂ (ring p) (c i) ∈
      IsLocalRing.maximalIdeal (ring p) := by logtwo_quiet
    apply p.valuation.toValuation.mem_maximalIdeal_iff.mpr
    exact hc i
  have hz : CurveLocalOrder.residueAugmentation ℂ (ring p)
      (lift p z c hc i - algebraMap ℂ (ring p) (c i)) = 0 := by logtwo_quiet
    change (CurveLocalOrder.residueCoefficientEquiv ℂ (ring p)).symm
      (IsLocalRing.residue (ring p) _) = 0
    rw [(IsLocalRing.residue_eq_zero_iff _).mpr hm, map_zero]
  rw [map_sub, CurveLocalOrder.residueAugmentation_algebraMap, sub_eq_zero] at hz
  exact hz

omit [Algebra.IsIntegral ℂ (IsLocalRing.ResidueField (ring p))] in
theorem logLift_nonconstant {m : ℕ} (z : Fin (m+1) → E) (c : Fin m → ℂ)
    (hc : Centered z (Fin.cases 1 c) p)
    (hnc : ∃ i : Fin (m+1), z i ≠ algebraMap ℂ E ((Fin.cases (1 : ℂ) c : Fin (m+1) → ℂ) i)) :
    lift p z (Fin.cases 1 c) hc 0 ≠ 1 ∨
      ∃ i, lift p z (Fin.cases 1 c) hc i.succ ≠ algebraMap ℂ (ring p) (c i) := by logtwo_quiet
  obtain ⟨i,hi⟩ := lift_nonconstant p z (Fin.cases 1 c) hc hnc
  cases i using Fin.cases with
  | zero => exact Or.inl (by logtwo_quiet simpa using hi)
  | succ i => exact Or.inr ⟨i,hi⟩

def logContact {m : ℕ} (z : Fin (m+1) → E) (c : Fin m → ℂ)
    (hc : Centered z (Fin.cases 1 c) p)
    (hnc : ∃ i : Fin (m+1), z i ≠ algebraMap ℂ E ((Fin.cases (1 : ℂ) c : Fin (m+1) → ℂ) i))
    (v : Fin (m+1) → ℚ) : ℚ :=
  DVRBranchJet.contact v c (lift p z (Fin.cases 1 c) hc 0)
    (fun i => lift p z (Fin.cases 1 c) hc i.succ) (logLift_nonconstant p z c hc hnc)

theorem logContact_pos {m : ℕ} (z : Fin (m+1) → E) (c : Fin m → ℂ)
    (hc : Centered z (Fin.cases 1 c) p)
    (hnc : ∃ i : Fin (m+1), z i ≠ algebraMap ℂ E ((Fin.cases (1 : ℂ) c : Fin (m+1) → ℂ) i))
    (v : Fin (m+1) → ℚ) (hv : ∀ i, 0 < v i) : 0 < logContact p z c hc hnc v := by logtwo_quiet
  exact DVRBranchJet.contact_pos v hv c _ _
    (lift_residue p z (Fin.cases 1 c) hc 0)
    (fun i => lift_residue p z (Fin.cases 1 c) hc i.succ) _

def ordinaryContact {n : ℕ} (z : Fin n → E) (c : Fin n → ℂ)
    (hc : Centered z c p) (hnc : ∃ i, z i ≠ algebraMap ℂ E (c i))
    (v : Fin n → ℚ) : ℚ :=
  OrdinaryDVRBranchJet.contact v c (lift p z c hc) (lift_nonconstant p z c hc hnc)

theorem logWord_field_order_lower {m : ℕ} (z : Fin (m+1) → E) (c : Fin m → ℂ)
    (hc : Centered z (Fin.cases 1 c) p)
    (hnc : ∃ i : Fin (m+1), z i ≠ algebraMap ℂ E ((Fin.cases (1 : ℂ) c : Fin (m+1) → ℂ) i))
    (v : Fin (m+1) → ℚ) (hv : ∀ i, 0 < v i) (H : ℚ)
    (f : PiExponentApprox.FramePolynomial m)
    (hf : FormalLogJet.formalJet c f ∈ JetGeometry.rationalWeightedIdeal v (fun i => (hv i).le) H)
    (word : List (Fin (m+1)))
    (hne : MvPolynomial.aeval z (PiExponentApprox.polynomialFrameWord m word f) ≠ 0) :
    logContact p z c hc hnc v * (H - (word.map v).sum) ≤
      (coordinateOrder p.valuation
        (MvPolynomial.aeval z (PiExponentApprox.polynomialFrameWord m word f)) : ℚ) := by logtwo_quiet
  let x := lift p z (Fin.cases 1 c) hc
  have he : (fun i => Fin.cases (x 0) (fun j => x j.succ) i) = x := by logtwo_quiet
    funext i
    cases i using Fin.cases <;> rfl
  have hn : MvPolynomial.aeval x (PiExponentApprox.polynomialFrameWord m word f) ≠ 0 := by logtwo_quiet
    intro hz
    apply hne
    rw [← lift_aeval p z (Fin.cases 1 c) hc, hz, map_zero]
  have hb := DVRBranchJet.frameWord_colength_lower v hv H c (x 0) (fun i => x i.succ)
    (lift_residue p z (Fin.cases 1 c) hc 0)
    (fun i => lift_residue p z (Fin.cases 1 c) hc i.succ)
    (logLift_nonconstant p z c hc hnc) f hf word (he.symm ▸ hn)
  have heval := congrArg (fun u : Fin (m+1) → ring p =>
    MvPolynomial.aeval u (PiExponentApprox.polynomialFrameWord m word f)) he
  rw [heval] at hb
  rw [coordinateOrder_aeval_eq_length p z (Fin.cases 1 c) hc _ hne]
  simpa only [Int.cast_natCast, logContact, x] using hb

theorem ordinaryWord_field_order_lower {n : ℕ} (z : Fin n → E) (c : Fin n → ℂ)
    (hc : Centered z c p) (hnc : ∃ i, z i ≠ algebraMap ℂ E (c i))
    (v : Fin n → ℚ) (hv : ∀ i, 0 < v i) (H : ℚ)
    (f : MvPolynomial (Fin n) ℂ)
    (hf : OrdinaryAuxiliaryJet.formalJet c f ∈ JetGeometry.rationalWeightedIdeal v (fun i => (hv i).le) H)
    (word : List (Fin n))
    (hne : MvPolynomial.aeval z (OrdinaryDerivatives.word n word f) ≠ 0) :
    ordinaryContact p z c hc hnc v * (H - (word.map v).sum) ≤
      (coordinateOrder p.valuation (MvPolynomial.aeval z (OrdinaryDerivatives.word n word f)) : ℚ) := by logtwo_quiet
  have hn : MvPolynomial.aeval (lift p z c hc) (OrdinaryDerivatives.word n word f) ≠ 0 := by logtwo_quiet
    intro hz
    apply hne
    rw [← lift_aeval p z c hc, hz, map_zero]
  rw [coordinateOrder_aeval_eq_length p z c hc _ hne]
  simpa only [Int.cast_natCast, ordinaryContact] using
    OrdinaryDVRBranchJet.ordinaryWord_colength_lower v hv H c (lift p z c hc)
      (lift_residue p z c hc) (lift_nonconstant p z c hc hnc) f hf word hn

theorem fibre_nonconstant {m : ℕ} (x : Fin m → E) (c : Fin m → ℂ)
    (hnc : ∃ i : Fin (m+1), (Fin.cases (1 : E) x : Fin (m+1) → E) i ≠
      algebraMap ℂ E ((Fin.cases (1 : ℂ) c : Fin (m+1) → ℂ) i)) :
    ∃ i, x i ≠ algebraMap ℂ E (c i) := by logtwo_quiet
  obtain ⟨i,hi⟩ := hnc
  cases i using Fin.cases with
  | zero => simp at hi
  | succ i => exact ⟨i,hi⟩

theorem logContact_one {m : ℕ} (x : Fin m → E) (c : Fin m → ℂ)
    (hc : Centered (Fin.cases (1 : E) x) (Fin.cases (1 : ℂ) c) p)
    (hnc : ∃ i : Fin (m+1), (Fin.cases (1 : E) x : Fin (m+1) → E) i ≠
      algebraMap ℂ E ((Fin.cases (1 : ℂ) c : Fin (m+1) → ℂ) i))
    (v : Fin (m+1) → ℚ) :
    logContact p (Fin.cases (1 : E) x) c hc hnc v =
      ordinaryContact p x c (fun i => hc i.succ) (fibre_nonconstant x c hnc)
        (fun i => v i.succ) := by logtwo_quiet
  have hy : lift p (Fin.cases (1 : E) x) (Fin.cases (1 : ℂ) c) hc 0 = 1 :=
    Subtype.ext rfl
  have hx : (fun i => lift p (Fin.cases (1 : E) x) (Fin.cases (1 : ℂ) c) hc i.succ) =
      lift p x c (fun i => hc i.succ) := rfl
  simpa only [logContact, ordinaryContact, hy, hx] using
    FibreContact.logarithmic_contact_eq_ordinary v c (lift p x c (fun i => hc i.succ))
      (lift_nonconstant p x c (fun i => hc i.succ) (fibre_nonconstant x c hnc))

end PiExponent.PlaceCenteredBranch

end

end OAI
end Source0063

-- Source: LogTwo/Geometry/NormalizedContact.lean
section Source0064
/-! Local logarithmic contact at an arbitrary nonzero Y-coordinate. The old
Y=1 theorem is applied after normalization; the final order is that of the
original polynomial at the original curve coordinates. -/
namespace LogTwo.Geometry

open OAI PiExponent PiExponentApprox
open CurveValuationCenter CurveCenters PlaceValuationRing WeightedPolynomialPole
noncomputable section

variable {E : Type*} [Field E] [Algebra ℂ E]

def centerPoint {m : ℕ} (y : ℂ) (c : Fin m → ℂ) : Fin (m+1) → ℂ := Fin.cases y c

theorem valuation_div_constant (p : NormalizedPlace ℂ E) (y : ℂ) (hy : y ≠ 0) (f : E) :
    p.valuation (f / algebraMap ℂ E y) = p.valuation f := by logtwo_quiet
  rw [p.valuation.map_div, CurveProductFormula.valuation_constant_eq_zero p y hy, sub_zero]

theorem coordinateOrder_div_constant (p : NormalizedPlace ℂ E) (y : ℂ) (hy : y ≠ 0) (f : E) :
    coordinateOrder p.valuation (f / algebraMap ℂ E y) = coordinateOrder p.valuation f := by logtwo_quiet
  classical
  have hy' : algebraMap ℂ E y ≠ 0 := (map_ne_zero_iff _ (algebraMap ℂ E).injective).mpr hy
  by_cases hf : f = 0
  · simp [hf, coordinateOrder]
  · simp only [coordinateOrder, dif_neg (div_ne_zero hf hy'), dif_neg hf]
    apply WithTop.coe_injective
    rw [WeightedCurveDegree.coe_integerOrder, WeightedCurveDegree.coe_integerOrder]
    exact valuation_div_constant p y hy f

theorem coordinatePole_normalizeY (p : NormalizedPlace ℂ E) {m : ℕ}
    (y : ℂ) (hy : y ≠ 0) (z : Fin (m+1) → E) (w : Fin (m+1) → ℚ) :
    coordinatePole p.valuation (normalizeY y z) w = coordinatePole p.valuation z w := by logtwo_quiet
  have he : ∀ i, coordinateOrder p.valuation (normalizeY y z i) = coordinateOrder p.valuation (z i) := by logtwo_quiet
    intro i
    cases i using Fin.cases with
    | zero => exact coordinateOrder_div_constant p y hy (z 0)
    | succ i => rfl
  simp only [coordinatePole, he]

theorem weightedDegree_normalizeY {m : ℕ}
    (hfinite : ∀ f : E, Transcendental ℂ f →
      FiniteDimensional (IntermediateField.adjoin ℂ {f}) E)
    (y : ℂ) (hy : y ≠ 0) (z : Fin (m+1) → E) (w : Fin (m+1) → ℚ) :
    CurveContactSum.weightedDegree hfinite (normalizeY y z) w =
      CurveContactSum.weightedDegree hfinite z w := by logtwo_quiet
  have he : CurveContactSum.weightedPoleDivisor hfinite (normalizeY y z) w =
      CurveContactSum.weightedPoleDivisor hfinite z w := by logtwo_quiet
    ext p
    exact coordinatePole_normalizeY p y hy z w
  unfold CurveContactSum.weightedDegree
  rw [he]

theorem valuation_normalizeY_sub_center (p : NormalizedPlace ℂ E) {m : ℕ}
    (y : ℂ) (hy : y ≠ 0) (z : Fin (m+1) → E) (c : Fin m → ℂ) (i : Fin (m+1)) :
    p.valuation (normalizeY y z i - algebraMap ℂ E (centerPoint 1 c i)) =
      p.valuation (z i - algebraMap ℂ E (centerPoint y c i)) := by logtwo_quiet
  cases i using Fin.cases with
  | zero =>
    have hy' : algebraMap ℂ E y ≠ 0 := (map_ne_zero_iff _ (algebraMap ℂ E).injective).mpr hy
    have he : normalizeY y z 0 - algebraMap ℂ E (centerPoint 1 c 0) =
        (z 0 - algebraMap ℂ E y) / algebraMap ℂ E y := by logtwo_quiet
      simp [normalizeY, centerPoint, sub_div, hy']
    rw [he, valuation_div_constant p y hy]
    rfl
  | succ i => rfl

theorem normalized_centered_iff (p : NormalizedPlace ℂ E) {m : ℕ}
    (y : ℂ) (hy : y ≠ 0) (z : Fin (m+1) → E) (c : Fin m → ℂ) :
    Centered (normalizeY y z) (centerPoint 1 c) p ↔ Centered z (centerPoint y c) p := by logtwo_quiet
  unfold Centered
  simp only [valuation_normalizeY_sub_center p y hy]

theorem normalized_nonconstant {m : ℕ} (y : ℂ) (hy : y ≠ 0)
    (z : Fin (m+1) → E) (c : Fin m → ℂ)
    (hnc : ∃ i, z i ≠ algebraMap ℂ E (centerPoint y c i)) :
    ∃ i, normalizeY y z i ≠ algebraMap ℂ E (centerPoint 1 c i) := by logtwo_quiet
  obtain ⟨i, hi⟩ := hnc
  refine ⟨i, ?_⟩
  intro he
  apply hi
  cases i using Fin.cases with
  | zero =>
    have hy' : algebraMap ℂ E y ≠ 0 := (map_ne_zero_iff _ (algebraMap ℂ E).injective).mpr hy
    have hd : z 0 / algebraMap ℂ E y = 1 := by logtwo_quiet simpa [normalizeY, centerPoint] using he
    exact (div_eq_one_iff_eq hy').mp hd
  | succ i => exact he

/-- A constant Y-coordinate forces every centered branch, even at different
places, to belong to the same center when the Y-centers are distinct. -/
theorem center_index_unique_of_constantY {m : ℕ} {J : Type*}
    (y : J → ℂ) (hy : Function.Injective y) (c : J → Fin m → ℂ)
    (z : Fin (m+1) → E) (a : ℂ) (hconst : z 0 = algebraMap ℂ E a)
    (j k : J) (p q : NormalizedPlace ℂ E)
    (hp : Centered z (centerPoint (y j) (c j)) p)
    (hq : Centered z (centerPoint (y k) (c k)) q) : j = k := by logtwo_quiet
  apply hy
  exact (hp.constant_coordinate 0 a hconst).symm.trans (hq.constant_coordinate 0 a hconst)

variable (p : NormalizedPlace ℂ E)
  [Algebra.IsIntegral ℂ (IsLocalRing.ResidueField (ring p))]

def logContactAt {m : ℕ} (y : ℂ) (hy : y ≠ 0) (z : Fin (m+1) → E) (c : Fin m → ℂ)
    (hc : Centered z (centerPoint y c) p)
    (hnc : ∃ i, z i ≠ algebraMap ℂ E (centerPoint y c i)) (v : Fin (m+1) → ℚ) : ℚ :=
  PlaceCenteredBranch.logContact p (normalizeY y z) c
    ((normalized_centered_iff p y hy z c).mpr hc) (normalized_nonconstant y hy z c hnc) v

theorem logContactAt_pos {m : ℕ} (y : ℂ) (hy : y ≠ 0)
    (z : Fin (m+1) → E) (c : Fin m → ℂ) (hc : Centered z (centerPoint y c) p)
    (hnc : ∃ i, z i ≠ algebraMap ℂ E (centerPoint y c i))
    (v : Fin (m+1) → ℚ) (hv : ∀ i, 0 < v i) : 0 < logContactAt p y hy z c hc hnc v :=
  PlaceCenteredBranch.logContact_pos p _ _ _ _ v hv

/-- The existing local derivative-order estimate, now at Y=y rather than Y=1. -/
theorem logWord_order_lower_at {m : ℕ} (y : ℂ) (hy : y ≠ 0)
    (z : Fin (m+1) → E) (c : Fin m → ℂ) (hc : Centered z (centerPoint y c) p)
    (hnc : ∃ i, z i ≠ algebraMap ℂ E (centerPoint y c i))
    (v : Fin (m+1) → ℚ) (hv : ∀ i, 0 < v i) (H : ℚ) (F : FramePolynomial m)
    (hF : formalJetAt y c F ∈ JetGeometry.rationalWeightedIdeal v (fun i => (hv i).le) H)
    (word : List (Fin (m+1)))
    (hne : MvPolynomial.aeval z (polynomialFrameWord m word F) ≠ 0) :
    logContactAt p y hy z c hc hnc v * (H - (word.map v).sum) ≤
      (coordinateOrder p.valuation (MvPolynomial.aeval z (polynomialFrameWord m word F)) : ℚ) := by logtwo_quiet
  have hn : MvPolynomial.aeval (normalizeY y z)
      (polynomialFrameWord m word (scaleY y F)) ≠ 0 := by logtwo_quiet
    rw [aeval_normalizeY_scaled_word y hy]
    exact hne
  have hb := PlaceCenteredBranch.logWord_field_order_lower p (normalizeY y z) c
    ((normalized_centered_iff p y hy z c).mpr hc) (normalized_nonconstant y hy z c hnc)
    v hv H (scaleY y F) hF word hn
  rw [aeval_normalizeY_scaled_word y hy] at hb
  exact hb

theorem normalizeY_fiber {m : ℕ} (y : ℂ) (hy : y ≠ 0) (x : Fin m → E) :
    normalizeY y (Fin.cases (algebraMap ℂ E y) x) = Fin.cases (1 : E) x := by logtwo_quiet
  have hy' : algebraMap ℂ E y ≠ 0 := (map_ne_zero_iff _ (algebraMap ℂ E).injective).mpr hy
  funext i
  cases i using Fin.cases <;> simp [normalizeY, hy']

theorem fiber_nonconstant_at {m : ℕ} (y : ℂ) (x : Fin m → E) (c : Fin m → ℂ)
    (hnc : ∃ i : Fin (m+1), (Fin.cases (algebraMap ℂ E y) x : Fin (m+1) → E) i ≠
      algebraMap ℂ E (centerPoint y c i)) : ∃ i, x i ≠ algebraMap ℂ E (c i) := by logtwo_quiet
  obtain ⟨i, hi⟩ := hnc
  cases i using Fin.cases with
  | zero => simp [centerPoint] at hi
  | succ i => exact ⟨i, hi⟩

/-- On the constant Y=y fiber, logarithmic contact is exactly ordinary contact. -/
theorem logContactAt_fiber {m : ℕ} (y : ℂ) (hy : y ≠ 0) (x : Fin m → E) (c : Fin m → ℂ)
    (hc : Centered (Fin.cases (algebraMap ℂ E y) x) (centerPoint y c) p)
    (hnc : ∃ i : Fin (m+1), (Fin.cases (algebraMap ℂ E y) x : Fin (m+1) → E) i ≠
      algebraMap ℂ E (centerPoint y c i)) (v : Fin (m+1) → ℚ) :
    logContactAt p y hy (Fin.cases (algebraMap ℂ E y) x) c hc hnc v =
      PlaceCenteredBranch.ordinaryContact p x c (fun i => hc i.succ)
        (fiber_nonconstant_at y x c hnc) (fun i => v i.succ) := by logtwo_quiet
  unfold logContactAt
  simp only [normalizeY_fiber y hy]
  exact PlaceCenteredBranch.logContact_one p x c _ _ v

end
end LogTwo.Geometry
end Source0064

-- Source: LogTwo/Geometry/JetTruncation.lean
section Source0065
/-
Modification notice for the LogTwo project.
Adapted from openai/math (Apache-2.0), revision adc7f1241b42e322a6451854ab7e4b4c146bf78a.
Changes: Adapt the formal-log truncation proof to varying Y-centers and scaled polynomials.
See ../THIRD_PARTY_NOTICES.txt for provenance and the recorded changes.
-/

/-! Adapted from openai/math, commit adc7f1241b42e322a6451854ab7e4b4c146bf78a,
FormalLogTruncation.formalLog_packets_surjective_iff_truncated (Apache-2.0).
Modified here to allow a family of different Y-centers; see THIRD_PARTY_NOTICES.txt.

Transfer interpolation surjectivity through a filtration-preserving change
of variables. The full and truncated coefficient packets need not be equal. -/
namespace LogTwo.Geometry
open OAI PiExponentApprox
open PiExponent.FormalLogTruncation PiExponent.JetGeometry
noncomputable section

def truncatedJetAt {m : ℕ} (y : ℂ) (c : Fin m → ℂ) (T : Fin m → ℕ) :
    FramePolynomial m →ₐ[ℂ] MvPowerSeries (Fin (m+1)) ℂ :=
  (truncatedFormalJet c T).comp (scaleY y)

theorem shiftMap_truncatedJetAt {m : ℕ} (y : ℂ) (c : Fin m → ℂ)
    (T : Fin m → ℕ) (P : FramePolynomial m) :
    shiftMap (fun i => logTail (T i)) (fun i => logTail_constantCoeff (T i))
      (truncatedJetAt y c T P) = formalJetAt y c P :=
  shiftMap_truncatedFormalJet c T (scaleY y P)

/-- For an entire family of different Y-centers, one common shift of jet variables
transfers surjectivity. No equality of the individual coefficient packets is used. -/
theorem formalJetAt_surjective_iff_truncated {m : ℕ} {α J : Type*}
    (v : Fin (m+1) → ℚ) (hv : ∀ i, 0 ≤ v i) (H : ℚ)
    (T : Fin m → ℕ) (hT : ∀ i, v i.succ ≤ (T i : ℚ) * v 0)
    (y : J → ℂ) (c : J → Fin m → ℂ) (P : α → FramePolynomial m) :
    Function.Surjective (fun a j => rationalCoefficientPacket v H (formalJetAt (y j) (c j) (P a))) ↔
      Function.Surjective (fun a j => rationalCoefficientPacket v H
        (truncatedJetAt (y j) (c j) T (P a))) := by logtwo_quiet
  let tail := fun i => logTail (T i)
  let ht := fun i => logTail_constantCoeff (T i)
  let e := shiftEquiv tail ht
  have hw : ∀ i, (tail i).toMvPowerSeries (0 : Fin (m+1)) ∈
      rationalWeightedIdeal v hv (v i.succ) :=
    fun i => logTail_mem_rationalWeightedIdeal v hv (T i) (v i.succ) (hT i)
  have he : ∀ f ∈ rationalWeightedIdeal v hv H, e f ∈ rationalWeightedIdeal v hv H :=
    fun f hf => (shiftEquiv_mem_iff tail ht v hv hw H f).mpr hf
  have hi : ∀ f ∈ rationalWeightedIdeal v hv H, e.symm f ∈ rationalWeightedIdeal v hv H := by logtwo_quiet
    intro f hf
    apply (shiftEquiv_mem_iff tail ht v hv hw H (e.symm f)).mp
    change e (e.symm f) ∈ rationalWeightedIdeal v hv H
    simpa only [AlgEquiv.apply_symm_apply] using hf
  have hh := packets_surjective_comp_equiv_iff v hv H e he hi
    (fun a j => truncatedJetAt (y j) (c j) T (P a))
  simpa only [e, tail, ht, shiftEquiv_apply, shiftMap_truncatedJetAt] using hh

end
end LogTwo.Geometry
end Source0065

-- Source: LogTwo/Analysis/CenterGrowth.lean
section Source0066
-- Modified in this edition: unused plain lemmas removed; see reduction.json.
/-! The extra growth from the centers Y=2^j. These estimates control individual
positive factors and Leibniz products. They do not transfer a determinant bound
from the Y=1 matrix: its cancellations still require a separate analytic proof. -/
namespace LogTwo.Analysis
open LogTwo.Interpolation LogTwo.Parameters Filter
open scoped Topology
noncomputable section

def centerGrowth {m : ℕ} (w : Weights m) : ℝ :=
  Real.log 2 * ((w.K : ℝ) / (w.w0 : ℝ))

end
end LogTwo.Analysis
end Source0066

-- Source: OAI/NumberTheory/PiExponent/LocalAlgebra/CoordinateContactBound.lean
section Source0067
/-
Modification notice for the LogTwo project.
Derived from openai/math (Apache-2.0), revision adc7f1241b42e322a6451854ab7e4b4c146bf78a.
Original source: lean/OAI/NumberTheory/PiExponent/LocalAlgebra/CoordinateContactBound.lean
Changes: Convert module/import declarations to the Lean 4.34 public module format.
See ../THIRD_PARTY_NOTICES.txt for provenance and the recorded changes.
-/

namespace OAI

noncomputable section
open scoped BigOperators
namespace PiExponent.CoordinateContactBound

open WeightedSliceDegree CurveValuationCenter CurveCenters

theorem supportBound_X_sub_C
    {K ι : Type*} [Field K] (W : ι → ℝ) (i : ι) (hi : 0 ≤ W i) (c : K) :
    SupportBound W (W i) (MvPolynomial.X i - MvPolynomial.C c) := by logtwo_quiet
  have hX : SupportBound W (W i) (MvPolynomial.X i : MvPolynomial ι K) :=
    supportBound_X W i
  have hC : SupportBound W (W i) (MvPolynomial.C (-c)) := (supportBound_C W (-c)).mono hi
  simpa only [map_neg, sub_eq_add_neg] using hX.add hC

@[simp] theorem ordinary_formalJet_X_sub_C {n : ℕ} (c : Fin n → ℂ) (i : Fin n) :
    OrdinaryAuxiliaryJet.formalJet c (MvPolynomial.X i - MvPolynomial.C (c i)) =
      MvPowerSeries.X i := by logtwo_quiet
  simp only [OrdinaryAuxiliaryJet.formalJet, map_sub, MvPolynomial.aeval_X, MvPolynomial.aeval_C]
  change MvPowerSeries.C (c i) + MvPowerSeries.X i - MvPowerSeries.C (c i) = MvPowerSeries.X i
  abel

theorem X_mem_rationalWeightedIdeal
    {K ι : Type*} [CommRing K] (V : ι → ℚ) (hV : ∀ i, 0 ≤ V i) (i : ι) :
    MvPowerSeries.X i ∈ (JetGeometry.rationalWeightedIdeal V hV (V i) :
      Ideal (MvPowerSeries ι K)) := by logtwo_quiet
  classical
  intro d hd
  rw [MvPowerSeries.coeff_X, ite_eq_right]
  intro he
  subst d
  simp [Finsupp.weight_single] at hd

theorem ordinary_formalJet_coordinate_mem {n : ℕ} (c : Fin n → ℂ)
    (V : Fin n → ℚ) (hV : ∀ i, 0 ≤ V i) (i : Fin n) :
    OrdinaryAuxiliaryJet.formalJet c (MvPolynomial.X i - MvPolynomial.C (c i)) ∈
      JetGeometry.rationalWeightedIdeal V hV (V i) := by logtwo_quiet
  rw [ordinary_formalJet_X_sub_C]
  exact X_mem_rationalWeightedIdeal V hV i

theorem coordinate_contact_sum_le
    {E : Type*} [Field E] [Algebra ℂ E] {n : ℕ}
    (hfinite : ∀ f : E, Transcendental ℂ f →
      FiniteDimensional (IntermediateField.adjoin ℂ {f}) E)
    (x : Fin n → E) (c : Fin n → ℂ)
    (W V : Fin n → ℚ) (hW : ∀ i, 0 < W i) (hV : ∀ i, 0 < V i)
    (i : Fin n) (hne : x i - algebraMap ℂ E (c i) ≠ 0)
    (S : Finset (NormalizedPlace ℂ E))
    (hc : ∀ p ∈ S, Centered x c p)
    (hres : ∀ p ∈ S,
      Algebra.IsIntegral ℂ (IsLocalRing.ResidueField (PlaceValuationRing.ring p)))
    (μ : NormalizedPlace ℂ E → ℝ)
    (hμ : ∀ p (hp : p ∈ S), letI := hres p hp;
      μ p = (PlaceCenteredBranch.ordinaryContact p x c (hc p hp)
        ⟨i, sub_ne_zero.mp hne⟩ V : ℝ)) :
    (V i : ℝ) * (∑ p ∈ S, μ p) ≤
      (W i : ℝ) * CurveContactSum.weightedDegree hfinite x W := by logtwo_quiet
  let f : MvPolynomial (Fin n) ℂ := MvPolynomial.X i - MvPolynomial.C (c i)
  have hfe : MvPolynomial.aeval x f = x i - algebraMap ℂ E (c i) := by logtwo_quiet simp [f]
  apply CurveContactSum.polynomial_contact_sum_le hfinite x W hW
    (W i : ℝ) (V i : ℝ) (by logtwo_quiet exact_mod_cast (hW i).le) f
    (supportBound_X_sub_C (fun j => (W j : ℝ)) i (by logtwo_quiet exact_mod_cast (hW i).le) (c i))
    (hfe ▸ hne) S μ
  intro p hp
  let := hres p hp
  rw [hμ p hp]
  have h := PlaceCenteredBranch.ordinaryWord_field_order_lower p x c (hc p hp)
    ⟨i, sub_ne_zero.mp hne⟩ V hV (V i) f
    (ordinary_formalJet_coordinate_mem c V (fun j => (hV j).le) i) []
    (by logtwo_quiet simpa only [OrdinaryDerivatives.word_nil, hfe] using hne)
  simp only [List.map_nil, List.sum_nil, sub_zero, OrdinaryDerivatives.word_nil] at h
  exact_mod_cast (by logtwo_quiet simpa only [mul_comm] using h :
    V i * PlaceCenteredBranch.ordinaryContact p x c (hc p hp) ⟨i, sub_ne_zero.mp hne⟩ V ≤
      (WeightedPolynomialPole.coordinateOrder p.valuation (MvPolynomial.aeval x f) : ℚ))

end PiExponent.CoordinateContactBound

end

end OAI
end Source0067

-- Source: LogTwo/Geometry/ConstantFiber.lean
section Source0068
/-! The actual contact-sum bound on one constant nonzero Y fiber. This uses the
existing coordinate-contact theorem, rather than assuming a per-center bound.
The global argument forcing an exceptional curve onto such a fiber is separate. -/
namespace LogTwo.Geometry
open OAI PiExponent
open CurveValuationCenter CurveCenters PlaceValuationRing
noncomputable section
variable {E : Type*} [Field E] [Algebra ℂ E]

theorem weightedDegree_constant_fiber {m : ℕ}
    (hfinite : ∀ f : E, Transcendental ℂ f →
      FiniteDimensional (IntermediateField.adjoin ℂ {f}) E)
    (y : ℂ) (hy : y ≠ 0) (x : Fin m → E) (w : Fin (m+1) → ℚ) :
    CurveContactSum.weightedDegree hfinite (Fin.cases (algebraMap ℂ E y) x) w =
      CurveContactSum.weightedDegree hfinite x (fun i => w i.succ) := by logtwo_quiet
  calc
    _ = CurveContactSum.weightedDegree hfinite
        (normalizeY y (Fin.cases (algebraMap ℂ E y) x)) w :=
      (weightedDegree_normalizeY hfinite y hy _ w).symm
    _ = CurveContactSum.weightedDegree hfinite (Fin.cases (1 : E) x) w := by logtwo_quiet
      rw [normalizeY_fiber y hy]
    _ = _ := FibreContact.weightedDegree_one hfinite w x

/-- On Y=y, V_i=W_i/theta gives sum(contact) <= theta*degree. The contact
function is required to be the actual normalized logarithmic contact; no local
or global inequality is an input. Center-index uniqueness is a separate lemma. -/
theorem constant_fiber_contact_sum_le {m : ℕ}
    (hfinite : ∀ f : E, Transcendental ℂ f →
      FiniteDimensional (IntermediateField.adjoin ℂ {f}) E)
    (y : ℂ) (hy : y ≠ 0) (x : Fin m → E) (c : Fin m → ℂ)
    (w v : Fin (m+1) → ℚ) (hw : ∀ i, 0 < w i) (hv : ∀ i, 0 < v i)
    (theta : ℚ) (hratio : ∀ i : Fin m, w i.succ = theta * v i.succ)
    (S : Finset (NormalizedPlace ℂ E))
    (hc : ∀ p ∈ S, Centered (Fin.cases (algebraMap ℂ E y) x) (centerPoint y c) p)
    (hres : ∀ p ∈ S, Algebra.IsIntegral ℂ (IsLocalRing.ResidueField (ring p)))
    (hnc : ∃ i : Fin (m+1), (Fin.cases (algebraMap ℂ E y) x : Fin (m+1) → E) i ≠
      algebraMap ℂ E (centerPoint y c i))
    (μ : NormalizedPlace ℂ E → ℝ)
    (hμ : ∀ p (hp : p ∈ S), letI := hres p hp;
      μ p = (logContactAt p y hy (Fin.cases (algebraMap ℂ E y) x) c (hc p hp) hnc v : ℝ)) :
    (∑ p ∈ S, μ p) ≤ (theta : ℝ) *
      CurveContactSum.weightedDegree hfinite (Fin.cases (algebraMap ℂ E y) x) w := by logtwo_quiet
  obtain ⟨i, hi⟩ := fiber_nonconstant_at y x c hnc
  have hcenter : ∀ p ∈ S, Centered x c p := fun p hp k => hc p hp k.succ
  have hbound := CoordinateContactBound.coordinate_contact_sum_le hfinite x c
    (fun k => w k.succ) (fun k => v k.succ)
    (fun k => hw k.succ) (fun k => hv k.succ) i (sub_ne_zero.mpr hi)
    S hcenter hres μ (by logtwo_quiet
      intro p hp
      letI := hres p hp
      simpa only [logContactAt_fiber] using hμ p hp)
  have hratioR : (w i.succ : ℝ) = (v i.succ : ℝ) * (theta : ℝ) := by logtwo_quiet
    exact_mod_cast (hratio i).trans (mul_comm theta (v i.succ))
  rw [hratioR, mul_assoc] at hbound
  have hpos : (0 : ℝ) < v i.succ := by logtwo_quiet exact_mod_cast hv i.succ
  have hsum := (mul_le_mul_iff_right₀ hpos).mp hbound
  simpa only [weightedDegree_constant_fiber hfinite y hy x w] using hsum

/-- If the Y-centers are distinct and Y is constant, every selected branch has
one common center. Summing the actual contacts therefore loses no factor K. -/
theorem constant_fiber_family_contact_sum_le {m : ℕ} {J : Type*}
    (hfinite : ∀ f : E, Transcendental ℂ f →
      FiniteDimensional (IntermediateField.adjoin ℂ {f}) E)
    (a : ℂ) (x : Fin m → E) (y : J → ℂ) (hy : Function.Injective y)
    (hy0 : ∀ j, y j ≠ 0) (c : J → Fin m → ℂ)
    (w v : Fin (m+1) → ℚ) (hw : ∀ i, 0 < w i) (hv : ∀ i, 0 < v i)
    (theta : ℚ) (htheta : 0 ≤ theta)
    (hratio : ∀ i : Fin m, w i.succ = theta * v i.succ)
    (S : Finset (NormalizedPlace ℂ E)) (j : NormalizedPlace ℂ E → J)
    (hc : ∀ p ∈ S, Centered (Fin.cases (algebraMap ℂ E a) x)
      (centerPoint (y (j p)) (c (j p))) p)
    (hres : ∀ p ∈ S, Algebra.IsIntegral ℂ (IsLocalRing.ResidueField (ring p)))
    (hnc : ∀ k : J, ∃ i : Fin (m+1),
      (Fin.cases (algebraMap ℂ E a) x : Fin (m+1) → E) i ≠
        algebraMap ℂ E (centerPoint (y k) (c k) i))
    (μ : NormalizedPlace ℂ E → ℝ)
    (hμ : ∀ p (hp : p ∈ S), letI := hres p hp;
      μ p = (logContactAt p (y (j p)) (hy0 (j p))
        (Fin.cases (algebraMap ℂ E a) x) (c (j p)) (hc p hp) (hnc (j p)) v : ℝ)) :
    (∑ p ∈ S, μ p) ≤ (theta : ℝ) *
      CurveContactSum.weightedDegree hfinite (Fin.cases (algebraMap ℂ E a) x) w := by logtwo_quiet
  classical
  by_cases hS : S.Nonempty
  · obtain ⟨p0, hp0⟩ := hS
    have he : ∀ p ∈ S, j p = j p0 := by logtwo_quiet
      intro p hp
      exact center_index_unique_of_constantY y hy c _ a rfl
        (j p) (j p0) p p0 (hc p hp) (hc p0 hp0)
    have ha : a = y (j p0) := (hc p0 hp0).constant_coordinate 0 a rfl
    subst a
    have hcenter : ∀ p ∈ S, Centered (Fin.cases (algebraMap ℂ E (y (j p0))) x)
        (centerPoint (y (j p0)) (c (j p0))) p := by logtwo_quiet
      intro p hp
      simpa only [he p hp] using hc p hp
    apply constant_fiber_contact_sum_le hfinite (y (j p0)) (hy0 (j p0)) x (c (j p0))
      w v hw hv theta hratio S hcenter hres (hnc (j p0)) μ
    intro p hp
    letI := hres p hp
    simpa only [he p hp] using hμ p hp
  · rw [Finset.not_nonempty_iff_eq_empty.mp hS, Finset.sum_empty]
    exact mul_nonneg (by logtwo_quiet exact_mod_cast htheta)
      (CurveContactSum.weightedDegree_nonneg hfinite _ w)

end
end LogTwo.Geometry
end Source0068

-- Source: LogTwo/Geometry/JetMatrix.lean
section Source0069
/-! The actual rational matrix entries are the coefficients of the truncated
complex jets. Renaming the distinguished variable preserves coefficients. -/
namespace LogTwo.Geometry
open OAI PiExponentApprox
open PiExponent.FormalLogJet PiExponent.FormalLogTruncation
open LogTwo.Interpolation
noncomputable section

/-- Coefficient extension Q -> C, followed by none -> 0 and some i -> i.succ. -/
def rationalJetEmbedding (m : ℕ) :
    MvPolynomial (Option (Fin m)) ℚ →+* MvPowerSeries (Fin (m+1)) ℂ :=
  MvPolynomial.coeToMvPowerSeries.ringHom.comp
    ((MvPolynomial.rename (_root_.finSuccEquiv m).symm).toRingHom.comp
      (MvPolynomial.map (algebraMap ℚ ℂ)))

@[simp] theorem rationalJetEmbedding_C (m : ℕ) (a : ℚ) :
    rationalJetEmbedding m (MvPolynomial.C a) = MvPowerSeries.C (a : ℂ) := by logtwo_quiet
  simp [rationalJetEmbedding]

@[simp] theorem rationalJetEmbedding_X (m : ℕ) (i : Option (Fin m)) :
    rationalJetEmbedding m (MvPolynomial.X i) =
      MvPowerSeries.X ((_root_.finSuccEquiv m).symm i) := by logtwo_quiet
  simp [rationalJetEmbedding]

theorem coeff_rationalJetEmbedding {m : ℕ}
    (P : MvPolynomial (Option (Fin m)) ℚ) (d : Option (Fin m) →₀ ℕ) :
    MvPowerSeries.coeff (d.mapDomain (_root_.finSuccEquiv m).symm)
      (rationalJetEmbedding m P) = (P.coeff d : ℂ) := by logtwo_quiet
  change (MvPolynomial.rename (_root_.finSuccEquiv m).symm
    (MvPolynomial.map (algebraMap ℚ ℂ) P)).coeff _ = _
  rw [MvPolynomial.coeff_rename_mapDomain _ (_root_.finSuccEquiv m).symm.injective]
  exact MvPolynomial.coeff_map _ _ _

/-- The finite sum uses precisely the same cutoff as PowerSeries.trunc. -/
theorem rationalJetEmbedding_truncatedLog (m T : ℕ) :
    rationalJetEmbedding m (truncatedLog T) =
      liftSeries m (PowerSeries.trunc T (PowerSeries.log ℂ) : PowerSeries ℂ) := by logtwo_quiet
  induction T with
  | zero => simp [truncatedLog]
  | succ T ih =>
    by_cases hT : T = 0
    · subst T
      simp [truncatedLog, PowerSeries.trunc_succ, PowerSeries.coeff_log]
    · have hT1 : 1 ≤ T := Nat.one_le_iff_ne_zero.mpr hT
      have hs : truncatedLog (m := m) (T+1) = truncatedLog T +
          MvPolynomial.C ((-1 : ℚ) ^ (T+1) / T) * MvPolynomial.X none ^ T := by logtwo_quiet
        exact Finset.sum_Ico_succ_top hT1 _
      rw [hs, map_add, map_mul, map_pow, rationalJetEmbedding_C,
        rationalJetEmbedding_X, _root_.finSuccEquiv_symm_none, ih,
        PowerSeries.trunc_succ]
      simp [PowerSeries.coeff_log, hT, ← Polynomial.C_mul_X_pow_eq_monomial,
        liftSeries_eq_toMvPowerSeries]

theorem truncatedJetAt_frameMonomial {m : ℕ} (y : ℂ) (c : Fin m → ℂ)
    (T : Fin m → ℕ) (h : ℕ) (α : Fin m → ℕ) :
    truncatedJetAt y c T (frameMonomial h α) =
      MvPowerSeries.C (y ^ h) * (1 + MvPowerSeries.X 0) ^ h *
      ∏ i, (MvPowerSeries.C (c i) +
        liftSeries m (PowerSeries.trunc (T i) (PowerSeries.log ℂ) : PowerSeries ℂ) +
        MvPowerSeries.X i.succ) ^ α i := by logtwo_quiet
  simp [truncatedJetAt, truncatedFormalJet, frameMonomial, scaleY, map_prod,
    mul_pow, MvPowerSeries.algebraMap_apply, add_comm, add_left_comm, add_assoc]

/-- Equality for every column, before any admissibility or interpolation assumptions. -/
theorem rationalJetEmbedding_columnExpansion {m : ℕ}
    (r : Fin m → ℚ) (T : Fin m → ℕ) (j : ℕ) (col : Column m) :
    rationalJetEmbedding m (columnExpansion r T j col) =
      truncatedJetAt ((2 : ℂ)^j) (fun i => (j : ℂ) * (r i : ℂ)) T
        (frameMonomial col.h col.alpha) := by logtwo_quiet
  rw [truncatedJetAt_frameMonomial]
  simp [columnExpansion, map_prod, rationalJetEmbedding_truncatedLog, pow_mul]

/-- Exact bridge from the manuscript's rational matrix to the geometric jet. -/
theorem coefficientMatrix_eq_truncatedJetAt {m : ℕ}
    (r : Fin m → ℚ) (T : Fin m → ℕ) (row : Row m) (col : Column m) :
    (coefficientMatrix r T row col : ℂ) =
      MvPowerSeries.coeff ((rowExponent row).mapDomain (_root_.finSuccEquiv m).symm)
        (truncatedJetAt ((2 : ℂ)^row.j)
          (fun i => (row.j : ℂ) * (r i : ℂ)) T (frameMonomial col.h col.alpha)) := by logtwo_quiet
  rw [← rationalJetEmbedding_columnExpansion, coeff_rationalJetEmbedding]
  rfl

end
end LogTwo.Geometry
end Source0069

-- Source: OAI/NumberTheory/PiExponent/Jets/FormalJetIndices.lean
section Source0070
/-
Modification notice for the LogTwo project.
Derived from openai/math (Apache-2.0), revision adc7f1241b42e322a6451854ab7e4b4c146bf78a.
Original source: lean/OAI/NumberTheory/PiExponent/Jets/FormalJetIndices.lean
Changes: Convert module/import declarations to the Lean 4.34 public module format.
See ../THIRD_PARTY_NOTICES.txt for provenance and the recorded changes.
-/

namespace OAI

noncomputable section

namespace PiExponent.FormalMatrixBridge

@[simp] theorem exponentVector_coe {n : ℕ} (d : Fin n →₀ ℕ) :
    InterpolationMatrix.exponentVector (fun i => d i) = d := by logtwo_quiet
  ext i
  simp

theorem cast_finsupp_weight {n : ℕ} (V : Fin n → ℚ) (d : Fin n →₀ ℕ) :
    (Finsupp.weight V d : ℝ) = ∑ i, (V i : ℝ) * (d i : ℝ) := by logtwo_quiet
  simp only [Finsupp.weight_eq_sum, nsmul_eq_mul, Rat.cast_sum,
    Rat.cast_mul, Rat.cast_natCast, mul_comm]

def rationalJetIndexEquiv {n : ℕ} (V : Fin n → ℚ) (hV : ∀ i, 0 < V i) (H : ℚ) :
    {d : Fin n →₀ ℕ // Finsupp.weight V d < H} ≃
      ↥(strictWeightedSimplex (fun i => (V i : ℝ)) (H : ℝ)) where
  toFun d := ⟨fun i => d.val i, by logtwo_quiet
    apply (mem_strictWeightedSimplex (fun i => by logtwo_quiet exact_mod_cast hV i)).mpr
    rw [← cast_finsupp_weight]
    exact_mod_cast d.property⟩
  invFun a := ⟨InterpolationMatrix.exponentVector a.val, by logtwo_quiet
    have ha := (mem_strictWeightedSimplex
      (fun i => by logtwo_quiet exact_mod_cast hV i)).mp a.property
    have hcast : (Finsupp.weight V (InterpolationMatrix.exponentVector a.val) : ℝ) <
        (H : ℝ) := by logtwo_quiet
      simpa only [cast_finsupp_weight, InterpolationMatrix.exponentVector_apply] using ha
    exact_mod_cast hcast⟩
  left_inv d := by logtwo_quiet apply Subtype.ext; exact exponentVector_coe d.val
  right_inv a := by logtwo_quiet apply Subtype.ext; funext i; simp

@[simp] theorem rationalJetIndexEquiv_apply_val {n : ℕ}
    (V : Fin n → ℚ) (hV : ∀ i, 0 < V i) (H : ℚ)
    (d : {d : Fin n →₀ ℕ // Finsupp.weight V d < H}) :
    (rationalJetIndexEquiv V hV H d).val = fun i => d.val i := rfl

@[simp] theorem rationalJetIndexEquiv_symm_val {n : ℕ}
    (V : Fin n → ℚ) (hV : ∀ i, 0 < V i) (H : ℚ)
    (a : ↥(strictWeightedSimplex (fun i => (V i : ℝ)) (H : ℝ))) :
    ((rationalJetIndexEquiv V hV H).symm a).val =
      InterpolationMatrix.exponentVector a.val := rfl

theorem polynomialOfCoefficients_of_weighted {m : ℕ}
    (W : Fin (m + 1) → ℝ) (hW : ∀ i, 0 < W i) (H : ℝ)
    (p : PiExponentApprox.FramePolynomial m)
    (hp : PiExponentApprox.HasWeightedDegreeLE W H p) :
    polynomialOfCoefficients (realWeightedSimplex W H)
      (fun a => p.coeff (InterpolationMatrix.exponentVector a.val)) = p := by logtwo_quiet
  classical
  ext d
  by_cases hd : (fun i => d i) ∈ realWeightedSimplex W H
  · have he := polynomialOfCoefficients_coeff (realWeightedSimplex W H)
      (fun a => p.coeff (InterpolationMatrix.exponentVector a.val))
      ⟨fun i => d i, hd⟩
    simpa only [exponentVector_coe] using he
  · have hpzero : p.coeff d = 0 := by logtwo_quiet
      by_contra hne
      apply hd
      apply (mem_realWeightedSimplex hW).mpr
      simpa only [PiExponentApprox.monomialWeight, mul_comm] using
        hp d (MvPolynomial.mem_support_iff.mpr hne)
    rw [hpzero]
    by_contra hne
    have hmem := MvPolynomial.mem_support_iff.mpr hne
    obtain ⟨a, ha, he⟩ := Finset.mem_image.mp
      (polynomialOfCoefficients_support _ _ hmem)
    apply hd
    have hea : a = fun i => d i := by logtwo_quiet
      funext i
      simpa only [InterpolationMatrix.exponentVector_apply] using
        congrArg (fun e : Fin (m + 1) →₀ ℕ => e i) he
    simpa only [← hea] using ha

end PiExponent.FormalMatrixBridge

end

end OAI
end Source0070

-- Source: LogTwo/Geometry/WeightedIndices.lean
section Source0071
/-! Finite weighted indices for the manuscript's actual rational matrix. -/
namespace LogTwo.Geometry
open OAI PiExponentApprox LogTwo.Interpolation
open PiExponent
noncomputable section

def columnWeight {m : ℕ} (w : Weights m) : Fin (m+1) → ℝ :=
  InterpolationMatrix.columnWeights w.w0 (fun i => w.w i)

def jetWeight {m : ℕ} (w : Weights m) : Fin (m+1) → ℚ :=
  Fin.cases w.v0 (fun i => w.w i / w.theta)

theorem columnWeight_pos {m : ℕ} (w : Weights m) : ∀ i, 0 < columnWeight w i := by logtwo_quiet
  intro i
  refine Fin.cases ?_ (fun j => ?_) i
  · change (0 : ℝ) < w.w0
    exact_mod_cast w.w0_pos
  · change (0 : ℝ) < w.w j
    exact_mod_cast w.w_pos j

theorem jetWeight_pos {m : ℕ} (w : Weights m) : ∀ i, 0 < jetWeight w i :=
  fun i => Fin.cases w.v0_pos (fun j => div_pos (w.w_pos j) w.theta_pos) i

theorem cast_jetWeight {m : ℕ} (w : Weights m) :
    (fun i => (jetWeight w i : ℝ)) =
      InterpolationMatrix.rowWeights w.v0 w.theta (fun i => w.w i) := by logtwo_quiet
  funext i
  refine Fin.cases ?_ (fun j => ?_) i <;>
    simp [jetWeight, InterpolationMatrix.rowWeights]

abbrev ColumnIndex {m : ℕ} (w : Weights m) (H : ℚ) :=
  ↥(realWeightedSimplex (columnWeight w) (H : ℝ))

abbrev RowIndex {m : ℕ} (w : Weights m) (H : ℚ) :=
  Fin w.K × ↥(strictWeightedSimplex (fun i => (jetWeight w i : ℝ)) (H : ℝ))

def columnOfIndex {m : ℕ} {w : Weights m} {H : ℚ} (c : ColumnIndex w H) :
    LogTwo.Interpolation.Column m := ⟨c.val 0, fun i => c.val i.succ⟩

def rowOfIndex {m : ℕ} {w : Weights m} {H : ℚ} (r : RowIndex w H) :
    LogTwo.Interpolation.Row m := ⟨r.1.val, r.2.val 0, fun i => r.2.val i.succ⟩

theorem columnOfIndex_valid {m : ℕ} {w : Weights m} {H : ℚ} (c : ColumnIndex w H) :
    AdmissibleColumn w H (columnOfIndex c) := by logtwo_quiet
  have hc := (InterpolationMatrix.column_mem_iff
    (show (0 : ℝ) < w.w0 by logtwo_quiet exact_mod_cast w.w0_pos)
    (fun i => show (0 : ℝ) < w.w i by logtwo_quiet exact_mod_cast w.w_pos i) c.val).mp c.property
  unfold AdmissibleColumn columnOfIndex
  exact_mod_cast hc

theorem rowOfIndex_valid {m : ℕ} {w : Weights m} {H : ℚ} (r : RowIndex w H) :
    AdmissibleRow w H (rowOfIndex r) := by logtwo_quiet
  refine ⟨r.1.isLt, ?_⟩
  have hr : r.2.val ∈ strictWeightedSimplex
      (InterpolationMatrix.rowWeights w.v0 w.theta (fun i => w.w i)) (H : ℝ) := by logtwo_quiet
    simpa only [← cast_jetWeight] using r.2.property
  have hb := (InterpolationMatrix.row_mem_iff
    (show (0 : ℝ) < w.v0 by logtwo_quiet exact_mod_cast w.v0_pos)
    (show (0 : ℝ) < w.theta by logtwo_quiet exact_mod_cast w.theta_pos)
    (fun i => show (0 : ℝ) < w.w i by logtwo_quiet exact_mod_cast w.w_pos i) r.2.val).mp hr
  change w.v0 * (r.2.val 0 : ℚ) + (∑ i, w.w i * (r.2.val i.succ : ℚ)) / w.theta < H
  exact_mod_cast hb

theorem columnOfIndex_injective {m : ℕ} (w : Weights m) (H : ℚ) :
    Function.Injective (@columnOfIndex m w H) := by logtwo_quiet
  intro a b hab
  apply Subtype.ext
  funext i
  refine Fin.cases ?_ (fun j => ?_) i
  · exact congrArg LogTwo.Interpolation.Column.h hab
  · exact congrFun (congrArg LogTwo.Interpolation.Column.alpha hab) j

theorem rowOfIndex_injective {m : ℕ} (w : Weights m) (H : ℚ) :
    Function.Injective (@rowOfIndex m w H) := by logtwo_quiet
  intro a b hab
  apply Prod.ext
  · exact Fin.ext (congrArg LogTwo.Interpolation.Row.j hab)
  · apply Subtype.ext
    funext i
    refine Fin.cases ?_ (fun j => ?_) i
    · exact congrArg LogTwo.Interpolation.Row.s hab
    · exact congrFun (congrArg LogTwo.Interpolation.Row.beta hab) j

theorem exists_rowIndex {m : ℕ} (w : Weights m) (H : ℚ)
    (r : LogTwo.Interpolation.Row m) (hr : AdmissibleRow w H r) :
    ∃ a : RowIndex w H, rowOfIndex a = r := by logtwo_quiet
  let b : Fin (m+1) → ℕ := Fin.cases r.s r.beta
  have hb : b ∈ strictWeightedSimplex (fun i => (jetWeight w i : ℝ)) (H : ℝ) := by logtwo_quiet
    rw [cast_jetWeight]
    apply (InterpolationMatrix.row_mem_iff
      (by logtwo_quiet exact_mod_cast w.v0_pos) (by logtwo_quiet exact_mod_cast w.theta_pos)
      (fun i => by logtwo_quiet exact_mod_cast w.w_pos i) b).mpr
    change (w.v0 : ℝ) * r.s + (∑ i, (w.w i : ℝ) * r.beta i) / w.theta < H
    exact_mod_cast hr.2
  exact ⟨(⟨r.j, hr.1⟩, ⟨b, hb⟩), rfl⟩

theorem rowExponent_index {m : ℕ} {w : Weights m} {H : ℚ} (r : RowIndex w H) :
    (rowExponent (rowOfIndex r)).mapDomain (_root_.finSuccEquiv m).symm =
      InterpolationMatrix.exponentVector r.2.val := by logtwo_quiet
  ext i
  rw [Finsupp.mapDomain_equiv_apply]
  refine Fin.cases ?_ (fun j => ?_) i <;>
    simp [rowExponent, rowOfIndex, InterpolationMatrix.exponentVector]

end
end LogTwo.Geometry
end Source0071

-- Source: LogTwo/Geometry/InterpolationBridge.lean
section Source0072
/-
Modification notice for the LogTwo project.
Adapted from openai/math (Apache-2.0), revision adc7f1241b42e322a6451854ab7e4b4c146bf78a.
Changes: Adapt packet surjectivity to varying Y-centers and add rational determinant descent.
See ../THIRD_PARTY_NOTICES.txt for provenance and the recorded changes.
-/

/-! Conditional bridge from weighted polynomial interpolation to the actual
rational full-row minor. The interpolation surjectivity is an explicit input. -/
namespace LogTwo.Geometry
open OAI PiExponentApprox LogTwo.Interpolation
open PiExponent PiExponent.FormalMatrixBridge PiExponent.JetGeometry
noncomputable section

def indexedMatrix {m : ℕ} (w : Weights m) (H : ℚ)
    (r : Fin m → ℚ) (T : Fin m → ℕ) :
    Matrix (RowIndex w H) (ColumnIndex w H) ℂ :=
  fun a b => (coefficientMatrix r T (rowOfIndex a) (columnOfIndex b) : ℂ)

theorem monomial_eq_C_mul_frameMonomial {m : ℕ} (a : Fin (m+1) → ℕ) (z : ℂ) :
    MvPolynomial.monomial (InterpolationMatrix.exponentVector a) z =
      MvPolynomial.C z * frameMonomial (a 0) (fun i => a i.succ) := by logtwo_quiet
  rw [MvPolynomial.monomial_eq,
    Finsupp.prod_fintype _ _ (fun _ => pow_zero _), Fin.prod_univ_succ]
  rfl

theorem indexedMatrix_mulVec_eq_coeff {m : ℕ} (w : Weights m) (H : ℚ)
    (r : Fin m → ℚ) (T : Fin m → ℕ) (x : ColumnIndex w H → ℂ)
    (a : RowIndex w H) :
    (indexedMatrix w H r T).mulVec x a =
      MvPowerSeries.coeff (InterpolationMatrix.exponentVector a.2.val)
        (truncatedJetAt ((2 : ℂ)^a.1.val) (fun i => (a.1.val : ℂ)*(r i : ℂ)) T
          (polynomialOfCoefficients (realWeightedSimplex (columnWeight w) (H : ℝ)) x)) := by logtwo_quiet
  classical
  change (∑ b, (coefficientMatrix r T (rowOfIndex a) (columnOfIndex b) : ℂ) * x b) = _
  simp only [coefficientMatrix_eq_truncatedJetAt, rowExponent_index]
  change _ = MvPowerSeries.coeff _ (truncatedJetAt _ _ T
    (∑ b : ColumnIndex w H, MvPolynomial.monomial
      (InterpolationMatrix.exponentVector b.val) (x b)))
  simp only [map_sum, monomial_eq_C_mul_frameMonomial, map_mul]
  apply Finset.sum_congr rfl
  intro b hb
  simp [rowOfIndex, columnOfIndex, MvPowerSeries.algebraMap_apply,
    mul_comm]

/-- The degree constraint applies to one global polynomial for all centers. -/
theorem indexedMatrix_surjective_of_truncated_packets {m : ℕ} {α : Type*}
    (w : Weights m) (H : ℚ) (r : Fin m → ℚ) (T : Fin m → ℕ)
    (P : α → FramePolynomial m)
    (hdegree : ∀ a, HasWeightedDegreeLE (columnWeight w) (H : ℝ) (P a))
    (hpacket : Function.Surjective (fun a => fun j : Fin w.K =>
      rationalCoefficientPacket (jetWeight w) H
        (truncatedJetAt ((2 : ℂ)^j.val) (fun i => (j.val : ℂ)*(r i : ℂ)) T (P a)))) :
    Function.Surjective (indexedMatrix w H r T).mulVecLin := by logtwo_quiet
  classical
  intro y
  let e := rationalJetIndexEquiv (jetWeight w) (jetWeight_pos w) H
  let z : Fin w.K → RationalCoefficientPacket (R := ℂ) (jetWeight w) H :=
    fun j d => y (j, e d)
  obtain ⟨a, ha⟩ := hpacket z
  let x : ColumnIndex w H → ℂ :=
    fun c => (P a).coeff (InterpolationMatrix.exponentVector c.val)
  refine ⟨x, ?_⟩
  funext ρ
  change (indexedMatrix w H r T).mulVec x ρ = y ρ
  rw [indexedMatrix_mulVec_eq_coeff]
  change MvPowerSeries.coeff _ (truncatedJetAt _ _ T
    (polynomialOfCoefficients _ (fun c => (P a).coeff
      (InterpolationMatrix.exponentVector c.val)))) = _
  rw [polynomialOfCoefficients_of_weighted _ (columnWeight_pos w) _ (P a) (hdegree a)]
  have hh := congrFun (congrFun ha ρ.1) (e.symm ρ.2)
  change MvPowerSeries.coeff (e.symm ρ.2).val
    (truncatedJetAt _ _ T (P a)) = z ρ.1 (e.symm ρ.2) at hh
  simpa only [e, rationalJetIndexEquiv_symm_val, z, Equiv.apply_symm_apply] using hh

theorem indexedMatrix_surjective_of_formal_packets {m : ℕ} {α : Type*}
    (w : Weights m) (H : ℚ) (r : Fin m → ℚ) (T : Fin m → ℕ)
    (hT : ∀ i, w.w i / w.theta ≤ (T i : ℚ) * w.v0)
    (P : α → FramePolynomial m)
    (hdegree : ∀ a, HasWeightedDegreeLE (columnWeight w) (H : ℝ) (P a))
    (hpacket : Function.Surjective (fun a => fun j : Fin w.K =>
      rationalCoefficientPacket (jetWeight w) H
        (formalJetAt ((2 : ℂ)^j.val) (fun i => (j.val : ℂ)*(r i : ℂ)) (P a)))) :
    Function.Surjective (indexedMatrix w H r T).mulVecLin := by logtwo_quiet
  apply indexedMatrix_surjective_of_truncated_packets w H r T P hdegree
  exact (formalJetAt_surjective_iff_truncated (jetWeight w)
    (fun i => (jetWeight_pos w i).le) H T hT
    (fun j : Fin w.K => (2 : ℂ)^j.val)
    (fun j i => (j.val : ℂ)*(r i : ℂ)) P).mp hpacket

/-- Complex surjectivity selects rational columns with a nonzero rational determinant.
The certificate enumerates every admissible row, including when the row set is empty. -/
theorem fullRowMinor_of_indexedMatrix_surjective {m : ℕ}
    (w : Weights m) (H : ℚ) (r : Fin m → ℚ) (T : Fin m → ℕ)
    (hsurj : Function.Surjective (indexedMatrix w H r T).mulVecLin) :
    Nonempty (FullRowMinor w H r T) := by logtwo_quiet
  classical
  obtain ⟨select, hselect, hdet⟩ :=
    InterpolationMatrix.exists_full_row_minor_of_surjective (indexedMatrix w H r T) hsurj
  let e := (Fintype.equivFin (RowIndex w H)).symm
  refine ⟨{
    size := Fintype.card (RowIndex w H)
    rows := fun i => rowOfIndex (e i)
    columns := fun i => columnOfIndex (select (e i))
    rows_injective := (rowOfIndex_injective w H).comp e.injective
    columns_injective := (columnOfIndex_injective w H).comp (hselect.comp e.injective)
    row_valid := fun i => rowOfIndex_valid (e i)
    all_rows := ?_
    column_valid := fun i => columnOfIndex_valid (select (e i))
    det_ne_zero := ?_ }⟩
  · intro row hrow
    obtain ⟨a, ha⟩ := exists_rowIndex w H row hrow
    exact ⟨e.symm a, by logtwo_quiet simpa using ha⟩
  · have hd : (((indexedMatrix w H r T).submatrix id select).submatrix e e).det ≠ 0 := by logtwo_quiet
      rwa [Matrix.det_submatrix_equiv_self]
    intro hz
    apply hd
    let A : Matrix (Fin (Fintype.card (RowIndex w H))) _ ℚ :=
      fun i j => coefficientMatrix r T (rowOfIndex (e i)) (columnOfIndex (select (e j)))
    change (A.map (fun q : ℚ => (q : ℂ))).det = 0
    rw [← Rat.cast_det]
    have hA : A.det = 0 := hz
    rw [hA]
    norm_num

/-- The remaining geometric obligation is exactly the displayed packet surjectivity. -/
theorem fullRowMinor_of_formal_packets {m : ℕ} {α : Type*}
    (w : Weights m) (H : ℚ) (r : Fin m → ℚ) (T : Fin m → ℕ)
    (hT : ∀ i, w.w i / w.theta ≤ (T i : ℚ) * w.v0)
    (P : α → FramePolynomial m)
    (hdegree : ∀ a, HasWeightedDegreeLE (columnWeight w) (H : ℝ) (P a))
    (hpacket : Function.Surjective (fun a => fun j : Fin w.K =>
      rationalCoefficientPacket (jetWeight w) H
        (formalJetAt ((2 : ℂ)^j.val) (fun i => (j.val : ℂ)*(r i : ℂ)) (P a)))) :
    Nonempty (FullRowMinor w H r T) :=
  fullRowMinor_of_indexedMatrix_surjective w H r T
    (indexedMatrix_surjective_of_formal_packets w H r T hT P hdegree hpacket)

end
end LogTwo.Geometry
end Source0072

-- Source: LogTwo/Geometry/AuxiliaryAtCenters.lean
section Source0073
-- Modified in this edition: unused plain lemmas removed; see reduction.json.
/-
Modification notice for the LogTwo project.
Adapted from openai/math (Apache-2.0), revision adc7f1241b42e322a6451854ab7e4b4c146bf78a.
Changes: Adapt the auxiliary-jet proof to varying Y-centers and simultaneous derivative words.
See ../THIRD_PARTY_NOTICES.txt for provenance and the recorded changes.
-/

/-! Adapted from openai/math, commit adc7f1241b42e322a6451854ab7e4b4c146bf78a,
Jets/FormalAuxiliaryJet.lean (Apache-2.0). The same global polynomial now vanishes
at varying Y-centers. See THIRD_PARTY_NOTICES.txt. -/
namespace LogTwo.Geometry
open OAI PiExponentApprox PiExponent PiExponent.JetGeometry
open Filter Topology
noncomputable section

def formalEvaluationAtCenters {m : ℕ} (K : ℕ)
    (V : Fin (m+1) → ℝ) (H : ℝ) (y : Fin K → ℂ) (c : Fin K → Fin m → ℂ) :
    FramePolynomial m →ₗ[ℂ] ((Fin K × ↥(strictWeightedSimplex V H)) → ℂ) :=
  LinearMap.pi (fun ρ =>
    (MvPowerSeries.coeff (InterpolationMatrix.exponentVector ρ.2.val)).comp
      (formalJetAt (y ρ.1) (c ρ.1)).toLinearMap)

/-- Dimension counting supplies one nonzero polynomial, vanishing simultaneously
at every center. The volume inequality is an explicit hypothesis. -/
theorem eventually_exists_auxiliary_at_centers {m : ℕ}
    (W V : Fin (m+1) → ℚ) (hW : ∀ i, 0 < W i) (hV : ∀ i, 0 < V i)
    (K : ℕ) {a : ℝ} (ha : 0 < a)
    (hvol : (K : ℝ) * a^(m+1) * (∏ i, (W i : ℝ)) / (∏ i, (V i : ℝ)) < 1)
    (y : Fin K → ℂ) (c : Fin K → Fin m → ℂ) :
    ∀ᶠ N : ℝ in atTop, ∃ P : FramePolynomial m, P ≠ 0 ∧
      HasWeightedDegreeLE (fun i => (W i : ℝ)) N P ∧
      ∀ j d, Finsupp.weight (fun i => (V i : ℝ)) d < a*N →
        MvPowerSeries.coeff d (formalJetAt (y j) (c j) P) = 0 := by logtwo_quiet
  filter_upwards [eventually_exists_auxiliaryPolynomial W V hW hV K ha hvol] with N hN
  obtain ⟨P, hP, hw, he⟩ :=
    hN (formalEvaluationAtCenters K (fun i => (V i : ℝ)) (a*N) y c)
  refine ⟨P, hP, hw, ?_⟩
  intro j d hd
  have hmem : (fun i => d i) ∈ strictWeightedSimplex (fun i => (V i : ℝ)) (a*N) := by logtwo_quiet
    apply (mem_strictWeightedSimplex (fun i => by logtwo_quiet exact_mod_cast hV i)).mpr
    simpa [Finsupp.weight_eq_sum, nsmul_eq_mul, mul_comm] using hd
  have hh := congrFun he (j, ⟨(fun i => d i), hmem⟩)
  simpa [formalEvaluationAtCenters, FormalMatrixBridge.exponentVector_coe] using hh

theorem eventually_exists_auxiliary_at_centers_nat {m : ℕ}
    (W V : Fin (m+1) → ℚ) (hW : ∀ i, 0 < W i) (hV : ∀ i, 0 < V i)
    (K : ℕ) {a : ℚ} (ha : 0 < a)
    (hvol : (K : ℝ) * (a : ℝ)^(m+1) * (∏ i, (W i : ℝ)) / (∏ i, (V i : ℝ)) < 1)
    (y : Fin K → ℂ) (c : Fin K → Fin m → ℂ) :
    ∀ᶠ N : ℕ in atTop, ∃ P : FramePolynomial m, P ≠ 0 ∧
      HasWeightedDegreeLE (fun i => (W i : ℝ)) N P ∧
      ∀ j, formalJetAt (y j) (c j) P ∈
        rationalWeightedIdeal V (fun i => (hV i).le) (a*N) := by logtwo_quiet
  have h := (tendsto_natCast_atTop_atTop (R := ℝ)).eventually
    (eventually_exists_auxiliary_at_centers W V hW hV K (by logtwo_quiet exact_mod_cast ha) hvol y c)
  filter_upwards [h] with N hN
  obtain ⟨P, hP, hw, hv⟩ := hN
  refine ⟨P, hP, hw, ?_⟩
  intro j d hd
  apply hv j d
  have hcast : ((Finsupp.weight V d : ℚ) : ℝ) < (a : ℝ)*(N : ℝ) := by logtwo_quiet exact_mod_cast hd
  simpa [Finsupp.weight_eq_sum, nsmul_eq_mul] using hcast

end
end LogTwo.Geometry
end Source0073

-- Source: LogTwo/Geometry/CurveWordVanishing.lean
section Source0074
/-
Modification notice for the LogTwo project.
Adapted from openai/math (Apache-2.0), revision adc7f1241b42e322a6451854ab7e4b4c146bf78a.
Changes: Adapt logarithmic word vanishing to nonzero Y-centers and normalized contacts.
See ../THIRD_PARTY_NOTICES.txt for provenance and the recorded changes.
-/

/-! Adapted from openai/math, commit adc7f1241b42e322a6451854ab7e4b4c146bf78a,
Cohomology/CurveDerivativeVanishing.lean (Apache-2.0). This version uses arbitrary
nonzero Y-centers and any finite family of actual normalized contacts. It does
not import the global rigidity theorem. See THIRD_PARTY_NOTICES.txt. -/
namespace LogTwo.Geometry
open OAI PiExponentApprox PiExponent
open CurveValuationCenter CurveCenters PlaceValuationRing WeightedPolynomialPole
open Filter Topology
noncomputable section
variable {E : Type*} [Field E] [Algebra ℂ E]

/-- Excess actual contact forces low-cost derivative words to vanish identically
on the curve. Local order bounds are proved from jets, rather than assumed. -/
theorem curve_words_vanish_of_excess {m K : ℕ}
    (hfinite : ∀ f : E, Transcendental ℂ f →
      FiniteDimensional (IntermediateField.adjoin ℂ {f}) E)
    (z : Fin (m+1) → E) (y : Fin K → ℂ) (hy : ∀ j, y j ≠ 0)
    (c : Fin K → Fin m → ℂ)
    (hnc : ∀ j, ∃ i, z i ≠ algebraMap ℂ E (centerPoint (y j) (c j) i))
    (w v : Fin (m+1) → ℚ) (hw : ∀ i, 0 < w i) (hv : ∀ i, 0 < v i)
    (S : Finset (NormalizedPlace ℂ E)) (center : NormalizedPlace ℂ E → Fin K)
    (hc : ∀ p ∈ S, Centered z (centerPoint (y (center p)) (c (center p))) p)
    (hres : ∀ p ∈ S, Algebra.IsIntegral ℂ (IsLocalRing.ResidueField (ring p)))
    (μ : NormalizedPlace ℂ E → ℝ)
    (hμ : ∀ p (hp : p ∈ S), letI := hres p hp;
      μ p = (logContactAt p (y (center p)) (hy (center p)) z (c (center p))
        (hc p hp) (hnc (center p)) v : ℝ))
    (sigma : ℚ) (hsigma : 0 < sigma) (N : ℕ) (hN : 0 < N)
    (F : FramePolynomial m)
    (hF : HasWeightedDegreeLE (fun i => (w i : ℝ)) N F)
    (hjet : ∀ j, formalJetAt (y j) (c j) F ∈
      JetGeometry.rationalWeightedIdeal v (fun i => (hv i).le) ((1+3*sigma)*N))
    (hexcess : CurveContactSum.weightedDegree hfinite z w <
      (1+(sigma : ℝ)) * ∑ p ∈ S, μ p) :
    ∀ word : List (Fin (m+1)), (word.map v).sum ≤ sigma*N →
      MvPolynomial.aeval z (polynomialFrameWord m word F) = 0 := by logtwo_quiet
  intro word hword
  have hNR : (0 : ℝ) < N := by logtwo_quiet exact_mod_cast hN
  have hsigR : (0 : ℝ) < sigma := by logtwo_quiet exact_mod_cast hsigma
  have hdegree : ∀ d ∈ (polynomialFrameWord m word F).support,
      Finsupp.weight (fun i => (w i : ℝ)) d ≤ (N : ℝ) := by logtwo_quiet
    have hd := hF.polynomialFrameWord (fun i => by logtwo_quiet exact_mod_cast (hw i).le) word
    intro d hdmem
    simpa only [Finsupp.weight_eq_sum, nsmul_eq_mul, monomialWeight] using hd d hdmem
  have hsum : 0 ≤ ∑ p ∈ S, μ p := by logtwo_quiet
    apply Finset.sum_nonneg
    intro p hp
    letI := hres p hp
    rw [hμ p hp]
    exact_mod_cast (logContactAt_pos p (y (center p)) (hy (center p)) z
      (c (center p)) (hc p hp) (hnc (center p)) v hv).le
  apply CurveContactSum.polynomial_eq_zero_of_excess_contact hfinite z w hw
    (N : ℝ) ((1+2*(sigma : ℝ))*N) hNR.le (polynomialFrameWord m word F) hdegree S μ
  · intro hne p hp
    letI := hres p hp
    have hret : (1+2*sigma)*(N : ℚ) ≤ (1+3*sigma)*N - (word.map v).sum := by logtwo_quiet
      nlinarith
    have hlocal := logWord_order_lower_at p (y (center p)) (hy (center p)) z
      (c (center p)) (hc p hp) (hnc (center p)) v hv ((1+3*sigma)*N)
      F (hjet (center p)) word hne
    have hpos := (logContactAt_pos p (y (center p)) (hy (center p)) z
      (c (center p)) (hc p hp) (hnc (center p)) v hv).le
    have hq := (mul_le_mul_of_nonneg_left hret hpos).trans hlocal
    have hr : (logContactAt p (y (center p)) (hy (center p)) z (c (center p))
        (hc p hp) (hnc (center p)) v : ℝ) * ((1+2*(sigma : ℝ))*N) ≤
        (coordinateOrder p.valuation (MvPolynomial.aeval z (polynomialFrameWord m word F)) : ℝ) := by logtwo_quiet
      exact_mod_cast hq
    simpa only [← hμ p hp, mul_comm] using hr
  · calc
      (N : ℝ) * CurveContactSum.weightedDegree hfinite z w <
          N * ((1+(sigma : ℝ)) * ∑ p ∈ S, μ p) := mul_lt_mul_of_pos_left hexcess hNR
      _ = (1+(sigma : ℝ)) * (N * ∑ p ∈ S, μ p) := by logtwo_quiet ring
      _ ≤ (1+2*(sigma : ℝ)) * (N * ∑ p ∈ S, μ p) :=
        mul_le_mul_of_nonneg_right (by logtwo_quiet linarith) (mul_nonneg hNR.le hsum)
      _ = _ := by logtwo_quiet ring

end
end LogTwo.Geometry
end Source0074

run_cmd Lean.logInfo "LogTwo progress: reached module 75/885"

-- Source: LogTwo/Geometry/ContactFamilyAt.lean
section Source0075
-- Modified in this edition: unused plain lemmas removed; see reduction.json.
/-
Modification notice for the LogTwo project.
Adapted from openai/math (Apache-2.0), revision adc7f1241b42e322a6451854ab7e4b4c146bf78a.
Changes: Adapt local contact families to varying Y-centers and a total center choice.
See ../THIRD_PARTY_NOTICES.txt for provenance and the recorded changes.
-/

/-! Adapted from openai/math, commit adc7f1241b42e322a6451854ab7e4b4c146bf78a,
Geometry/CurveContactFamily.lean (Apache-2.0), to varying nonzero Y-centers.
All centered normalized places are included, not a selected subset.
See THIRD_PARTY_NOTICES.txt. -/
namespace LogTwo.Geometry.ContactFamilyAt
open OAI PiExponent PiExponentApprox
open CurveValuationCenter CurveCenters PlaceValuationRing
open Filter Topology
noncomputable section
variable {E : Type*} [Field E] [Algebra ℂ E] {m K : ℕ}

def places
    (hfinite : ∀ f : E, Transcendental ℂ f →
      FiniteDimensional (IntermediateField.adjoin ℂ {f}) E)
    (z : Fin (m+1) → E) (y : Fin K → ℂ) (c : Fin K → Fin m → ℂ)
    (hz : ∃ i, Transcendental ℂ (z i)) : Finset (NormalizedPlace ℂ E) :=
  centerPlaces z (fun j => centerPoint (y j) (c j)) hz hfinite

theorem mem_places
    (hfinite : ∀ f : E, Transcendental ℂ f →
      FiniteDimensional (IntermediateField.adjoin ℂ {f}) E)
    (z : Fin (m+1) → E) (y : Fin K → ℂ) (c : Fin K → Fin m → ℂ)
    (hz : ∃ i, Transcendental ℂ (z i)) (p : NormalizedPlace ℂ E) :
    p ∈ places hfinite z y c hz ↔ ∃ j, Centered z (centerPoint (y j) (c j)) p :=
  mem_centerPlaces z (fun j => centerPoint (y j) (c j)) hz hfinite p

/-- The value off the finite set is arbitrary and never contributes to contact. -/
def center
    (hfinite : ∀ f : E, Transcendental ℂ f →
      FiniteDimensional (IntermediateField.adjoin ℂ {f}) E)
    (z : Fin (m+1) → E) (y : Fin K → ℂ) (c : Fin K → Fin m → ℂ)
    (hz : ∃ i, Transcendental ℂ (z i)) (hK : 0 < K) (p : NormalizedPlace ℂ E) : Fin K := by logtwo_quiet
  classical
  exact if hp : p ∈ places hfinite z y c hz then
    Classical.choose ((mem_places hfinite z y c hz p).mp hp) else ⟨0, hK⟩

theorem centered
    (hfinite : ∀ f : E, Transcendental ℂ f →
      FiniteDimensional (IntermediateField.adjoin ℂ {f}) E)
    (z : Fin (m+1) → E) (y : Fin K → ℂ) (c : Fin K → Fin m → ℂ)
    (hz : ∃ i, Transcendental ℂ (z i)) (hK : 0 < K)
    (p : NormalizedPlace ℂ E) (hp : p ∈ places hfinite z y c hz) :
    Centered z (centerPoint (y (center hfinite z y c hz hK p))
      (c (center hfinite z y c hz hK p))) p := by logtwo_quiet
  simpa only [center, dite_eq_left hp] using
    Classical.choose_spec ((mem_places hfinite z y c hz p).mp hp)

theorem nonconstant (z : Fin (m+1) → E) (y : ℂ) (c : Fin m → ℂ)
    (hz : ∃ i, Transcendental ℂ (z i)) :
    ∃ i, z i ≠ algebraMap ℂ E (centerPoint y c i) :=
  Centered.exists_nonzero_difference z (centerPoint y c) hz

variable
    (hres : ∀ p : NormalizedPlace ℂ E,
      Algebra.IsIntegral ℂ (IsLocalRing.ResidueField (ring p)))
    (hfinite : ∀ f : E, Transcendental ℂ f →
      FiniteDimensional (IntermediateField.adjoin ℂ {f}) E)
    (z : Fin (m+1) → E) (y : Fin K → ℂ) (hy : ∀ j, y j ≠ 0)
    (c : Fin K → Fin m → ℂ) (hz : ∃ i, Transcendental ℂ (z i)) (hK : 0 < K)

def contact (v : Fin (m+1) → ℚ) (p : NormalizedPlace ℂ E) : ℚ := by logtwo_quiet
  classical
  let := hres p
  let j := center hfinite z y c hz hK p
  exact if hp : p ∈ places hfinite z y c hz then
    logContactAt p (y j) (hy j) z (c j)
      (centered hfinite z y c hz hK p hp) (nonconstant z (y j) (c j) hz) v
  else 0

theorem contact_eq (v : Fin (m+1) → ℚ) (p : NormalizedPlace ℂ E)
    (hp : p ∈ places hfinite z y c hz) :
    letI := hres p
    contact hres hfinite z y hy c hz hK v p =
      logContactAt p (y (center hfinite z y c hz hK p))
        (hy (center hfinite z y c hz hK p)) z (c (center hfinite z y c hz hK p))
        (centered hfinite z y c hz hK p hp)
        (nonconstant z _ _ hz) v := by logtwo_quiet
  simp only [contact, dite_eq_left hp]

theorem contact_pos (v : Fin (m+1) → ℚ) (hv : ∀ i, 0 < v i)
    (p : NormalizedPlace ℂ E) (hp : p ∈ places hfinite z y c hz) :
    0 < contact hres hfinite z y hy c hz hK v p := by logtwo_quiet
  let := hres p
  rw [contact_eq hres hfinite z y hy c hz hK v p hp]
  exact logContactAt_pos p _ _ _ _ _ _ v hv

/-- No per-place order inequalities are inputs: the actual contacts and all places
are supplied by the preceding constructions. -/
theorem words_vanish_of_excess
    (w v : Fin (m+1) → ℚ) (hw : ∀ i, 0 < w i) (hv : ∀ i, 0 < v i)
    (sigma : ℚ) (hsigma : 0 < sigma) (N : ℕ) (hN : 0 < N)
    (F : FramePolynomial m) (hF : HasWeightedDegreeLE (fun i => (w i : ℝ)) N F)
    (hjet : ∀ j, formalJetAt (y j) (c j) F ∈
      JetGeometry.rationalWeightedIdeal v (fun i => (hv i).le) ((1+3*sigma)*N))
    (hexcess : CurveContactSum.weightedDegree hfinite z w <
      (1+(sigma : ℝ)) * ∑ p ∈ places hfinite z y c hz,
        (contact hres hfinite z y hy c hz hK v p : ℝ)) :
    ∀ word : List (Fin (m+1)), (word.map v).sum ≤ sigma*N →
      MvPolynomial.aeval z (polynomialFrameWord m word F) = 0 := by logtwo_quiet
  apply curve_words_vanish_of_excess hfinite z y hy c
    (fun j => nonconstant z (y j) (c j) hz) w v hw hv
    (places hfinite z y c hz) (center hfinite z y c hz hK)
    (centered hfinite z y c hz hK) (fun p _ => hres p)
    (fun p => (contact hres hfinite z y hy c hz hK v p : ℝ))
    ?_ sigma hsigma N hN F hF hjet hexcess
  intro p hp
  let := hres p
  exact congrArg (fun q : ℚ => (q : ℝ)) (contact_eq hres hfinite z y hy c hz hK v p hp)

/-- A nonzero global polynomial with all low-cost words in the curve kernel,
for every sufficiently large natural N, assuming excess contact and volume. -/
theorem eventually_exists_annihilator_of_excess
    (w v : Fin (m+1) → ℚ) (hw : ∀ i, 0 < w i) (hv : ∀ i, 0 < v i)
    (sigma : ℚ) (hsigma : 0 < sigma)
    (hvol : (K : ℝ) * (1+3*(sigma : ℝ))^(m+1) *
      (∏ i, (w i : ℝ)) / (∏ i, (v i : ℝ)) < 1)
    (hexcess : CurveContactSum.weightedDegree hfinite z w <
      (1+(sigma : ℝ)) * ∑ p ∈ places hfinite z y c hz,
        (contact hres hfinite z y hy c hz hK v p : ℝ)) :
    ∀ᶠ N : ℕ in atTop, ∃ F : FramePolynomial m, F ≠ 0 ∧
      HasWeightedDegreeLE (fun i => (w i : ℝ)) N F ∧
      ∀ word : List (Fin (m+1)), (word.map v).sum ≤ sigma*N →
        MvPolynomial.aeval z (polynomialFrameWord m word F) = 0 := by logtwo_quiet
  have haux := eventually_exists_auxiliary_at_centers_nat w v hw hv K
    (a := 1+3*sigma) (by logtwo_quiet positivity) (by logtwo_quiet simpa using hvol) y c
  filter_upwards [haux, eventually_gt_atTop (0 : ℕ)] with N hauxN hN
  obtain ⟨F, hF0, hF, hjet⟩ := hauxN
  exact ⟨F, hF0, hF, words_vanish_of_excess hres hfinite z y hy c hz hK
    w v hw hv sigma hsigma N hN F hF hjet hexcess⟩

end
end LogTwo.Geometry.ContactFamilyAt
end Source0075

-- Source: LogTwo/Geometry/GeometricParameters.lean
section Source0076
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
    (fun i => (rationalColumnWeight w i : ℝ)) = columnWeight w := by logtwo_quiet
  funext i
  refine Fin.cases rfl (fun _ => rfl) i

theorem weighted_volume_ratio {m : ℕ} (w : Weights m) :
    (w.K : ℚ) * (∏ i, rationalColumnWeight w i) / (∏ i, jetWeight w i) =
      (w.K : ℚ) * (w.w0 / w.v0) * w.theta^m := by logtwo_quiet
  have hp : (∏ i, w.w i) ≠ 0 := (Finset.prod_pos (fun i _ => w.w_pos i)).ne'
  simp only [Fin.prod_univ_succ, rationalColumnWeight, jetWeight,
    Fin.cases_zero, Fin.cases_succ, Finset.prod_div_distrib, Finset.prod_const,
    Finset.card_univ, Fintype.card_fin]
  field_simp

def curveSigma (theta : ℚ) (m : ℕ) : ℚ :=
  min ((1-theta)/(2*theta)) (1/(12*((m : ℚ)+1)))

theorem curveSigma_pos {theta : ℚ} (htheta : 0 < theta) (hlt : theta < 1) (m : ℕ) :
    0 < curveSigma theta m := by logtwo_quiet
  unfold curveSigma
  apply lt_min
  · exact div_pos (sub_pos.mpr hlt) (by logtwo_quiet positivity)
  · positivity

theorem curveSigma_contact_margin {theta : ℚ}
    (htheta : 0 < theta) (hlt : theta < 1) (m : ℕ) :
    (1+curveSigma theta m)*theta < 1 := by logtwo_quiet
  have hb : curveSigma theta m * (2*theta) ≤ 1-theta :=
    (le_div_iff₀ (by logtwo_quiet positivity)).mp (min_le_left _ _)
  nlinarith

/-- An elementary reciprocal form of Bernoulli's bound, proved without division.
It is useful only when 1-n*x is positive, but the statement holds for every n. -/
theorem pow_mul_one_sub_mul_le_one {x : ℚ} (hx : 0 ≤ x) (n : ℕ) :
    (1+x)^n * (1-(n : ℚ)*x) ≤ 1 := by logtwo_quiet
  induction n with
  | zero => simp
  | succ n ih =>
    have hstep : (1+x)*(1-((n : ℚ)+1)*x) ≤ 1-(n : ℚ)*x := by logtwo_quiet
      have hnx : 0 ≤ (n : ℚ)*x^2 := mul_nonneg (Nat.cast_nonneg _) (sq_nonneg x)
      nlinarith [sq_nonneg x]
    calc
      _ = (1+x)^n * ((1+x)*(1-((n : ℚ)+1)*x)) := by logtwo_quiet
        rw [pow_succ, Nat.cast_succ]
        ring
      _ ≤ (1+x)^n * (1-(n : ℚ)*x) :=
        mul_le_mul_of_nonneg_left hstep (pow_nonneg (by logtwo_quiet linarith) n)
      _ ≤ 1 := ih

theorem curveSigma_power_bound {theta : ℚ}
    (htheta : 0 < theta) (hlt : theta < 1) (m : ℕ) :
    (1+3*curveSigma theta m)^(m+1) ≤ 4/3 := by logtwo_quiet
  have hs := curveSigma_pos htheta hlt m
  have hb : curveSigma theta m * (12*((m : ℚ)+1)) ≤ 1 :=
    (le_div_iff₀ (by logtwo_quiet positivity)).mp (min_le_right _ _)
  have h := pow_mul_one_sub_mul_le_one (show 0 ≤ 3*curveSigma theta m by logtwo_quiet positivity) (m+1)
  have hp : 0 ≤ (1+3*curveSigma theta m)^(m+1) := by logtwo_quiet positivity
  have hsmall : (3/4 : ℚ) ≤ 1-((m : ℚ)+1)*(3*curveSigma theta m) := by logtwo_quiet
    nlinarith
  have hh := mul_le_mul_of_nonneg_left hsmall hp
  norm_num only [Nat.cast_add, Nat.cast_one] at h
  nlinarith

/-- The enlarged jet volume stays below one whenever the unscaled volume is 1/2. -/
theorem curveSigma_volume_lt_one {m : ℕ} (w : Weights m)
    (hhalf : (w.K : ℚ)*(w.w0/w.v0)*w.theta^m = 1/2) :
    (w.K : ℝ) * (1+3*(curveSigma w.theta m : ℝ))^(m+1) *
      (∏ i, (rationalColumnWeight w i : ℝ)) / (∏ i, (jetWeight w i : ℝ)) < 1 := by logtwo_quiet
  have hbase : (w.K : ℚ)*(∏ i, rationalColumnWeight w i)/(∏ i, jetWeight w i) = 1/2 :=
    (weighted_volume_ratio w).trans hhalf
  have hpow := curveSigma_power_bound w.theta_pos w.theta_lt_one m
  have hscaled : (w.K : ℚ)*(1+3*curveSigma w.theta m)^(m+1)*
      (∏ i, rationalColumnWeight w i)/(∏ i, jetWeight w i) < 1 := by logtwo_quiet
    calc
      _ = (1+3*curveSigma w.theta m)^(m+1) *
          ((w.K : ℚ)*(∏ i, rationalColumnWeight w i)/(∏ i, jetWeight w i)) := by logtwo_quiet ring
      _ = (1+3*curveSigma w.theta m)^(m+1) * (1/2) := by logtwo_quiet rw [hbase]
      _ < 1 := by logtwo_quiet linarith
  exact_mod_cast hscaled

/-- The actual arithmetic weights already have the required volume 1/2. -/
theorem chosenWeights_half_volume (n : ℕ) (hn : 1 ≤ n) (m : ℕ)
    (q : Fin m → ℕ) (hq : ∀ i, 2 ≤ q i) :
    let w := LogTwo.chosenWeights n hn m q hq
    (w.K : ℚ)*(w.w0/w.v0)*w.theta^m = 1/2 := by logtwo_quiet
  exact chosen_volume_ratio (shape n hn).theta_pos
    ((shape n hn).theta_pos.trans ((shape n hn).theta_lt_a.trans (shape n hn).a_lt_b))
    (shape n hn).one_lt_c.le m

theorem chosenWeights_geometric_margins (n : ℕ) (hn : 1 ≤ n) (m : ℕ)
    (q : Fin m → ℕ) (hq : ∀ i, 2 ≤ q i) :
    let w := LogTwo.chosenWeights n hn m q hq
    let sigma := curveSigma w.theta m
    0 < sigma ∧ (1+sigma)*w.theta < 1 ∧
      (w.K : ℝ)*(1+3*(sigma : ℝ))^(m+1)*(∏ i, (rationalColumnWeight w i : ℝ))/
        (∏ i, (jetWeight w i : ℝ)) < 1 := by logtwo_quiet
  dsimp only
  let w := LogTwo.chosenWeights n hn m q hq
  exact ⟨curveSigma_pos w.theta_pos w.theta_lt_one m,
    curveSigma_contact_margin w.theta_pos w.theta_lt_one m,
    curveSigma_volume_lt_one w (chosenWeights_half_volume n hn m q hq)⟩

end
end LogTwo.Geometry
end Source0076

-- Source: LogTwo/Geometry/CurveCertificate.lean
section Source0077
-- Modified in this edition: unused plain lemmas removed; see reduction.json.
/-! Assemble the actual finite contact family with the explicit geometric margins.
The separated-weight rigidity theorem, forcing constant Y, remains separate. -/
namespace LogTwo.Geometry.ContactFamilyAt
open OAI PiExponent PiExponentApprox
open CurveValuationCenter CurveCenters PlaceValuationRing
open Filter Topology
noncomputable section
variable {E : Type*} [Field E] [Algebra ℂ E] {m K : ℕ}
variable
    (hres : ∀ p : NormalizedPlace ℂ E,
      Algebra.IsIntegral ℂ (IsLocalRing.ResidueField (ring p)))
    (hfinite : ∀ f : E, Transcendental ℂ f →
      FiniteDimensional (IntermediateField.adjoin ℂ {f}) E)
    (z : Fin (m+1) → E) (y : Fin K → ℂ) (hy : ∀ j, y j ≠ 0)
    (c : Fin K → Fin m → ℂ) (hz : ∃ i, Transcendental ℂ (z i)) (hK : 0 < K)

/-- The complete contact family on a constant Y fiber obeys the theta bound. -/
theorem contact_sum_le_of_constantY (hinj : Function.Injective y)
    (w v : Fin (m+1) → ℚ) (hw : ∀ i, 0 < w i) (hv : ∀ i, 0 < v i)
    (theta : ℚ) (htheta : 0 ≤ theta)
    (hratio : ∀ i : Fin m, w i.succ = theta*v i.succ)
    (a : ℂ) (ha : z 0 = algebraMap ℂ E a) :
    (∑ p ∈ places hfinite z y c hz, (contact hres hfinite z y hy c hz hK v p : ℝ)) ≤
      (theta : ℝ)*CurveContactSum.weightedDegree hfinite z w := by logtwo_quiet
  let x := fun i : Fin m => z i.succ
  have hx : (Fin.cases (algebraMap ℂ E a) x : Fin (m+1) → E) = z := by logtwo_quiet
    funext i
    exact Fin.cases ha.symm (fun _ => rfl) i
  have hc : ∀ p ∈ places hfinite z y c hz,
      Centered (Fin.cases (algebraMap ℂ E a) x)
        (centerPoint (y (center hfinite z y c hz hK p)) (c (center hfinite z y c hz hK p))) p := by logtwo_quiet
    simpa only [hx] using centered hfinite z y c hz hK
  have hnc : ∀ j, ∃ i : Fin (m+1),
      (Fin.cases (algebraMap ℂ E a) x : Fin (m+1) → E) i ≠
        algebraMap ℂ E (centerPoint (y j) (c j) i) := by logtwo_quiet
    simpa only [hx] using fun j => nonconstant z (y j) (c j) hz
  have hb := constant_fiber_family_contact_sum_le hfinite a x y hinj hy c w v hw hv
    theta htheta hratio (places hfinite z y c hz) (center hfinite z y c hz hK)
    hc (fun p _ => hres p) hnc
    (fun p => (contact hres hfinite z y hy c hz hK v p : ℝ)) (by logtwo_quiet
      intro p hp
      let := hres p
      simpa only [hx] using congrArg (fun q : ℚ => (q : ℝ))
        (contact_eq hres hfinite z y hy c hz hK v p hp))
  simpa only [hx] using hb

theorem no_excess_of_constantY (hinj : Function.Injective y)
    (w v : Fin (m+1) → ℚ) (hw : ∀ i, 0 < w i) (hv : ∀ i, 0 < v i)
    (theta : ℚ) (htheta : 0 ≤ theta)
    (hratio : ∀ i : Fin m, w i.succ = theta*v i.succ)
    (sigma : ℚ) (hsigma : 0 ≤ sigma) (hmargin : (1+sigma)*theta ≤ 1)
    (a : ℂ) (ha : z 0 = algebraMap ℂ E a) :
    (1+(sigma : ℝ)) *
      (∑ p ∈ places hfinite z y c hz, (contact hres hfinite z y hy c hz hK v p : ℝ)) ≤
        CurveContactSum.weightedDegree hfinite z w := by logtwo_quiet
  have hb := contact_sum_le_of_constantY hres hfinite z y hy c hz hK hinj
    w v hw hv theta htheta hratio a ha
  have hsigR : (0 : ℝ) ≤ sigma := by logtwo_quiet exact_mod_cast hsigma
  calc
    _ ≤ (1+(sigma : ℝ))*((theta : ℝ)*CurveContactSum.weightedDegree hfinite z w) :=
      mul_le_mul_of_nonneg_left hb (by logtwo_quiet positivity)
    _ = ((1+(sigma : ℝ))*theta)*CurveContactSum.weightedDegree hfinite z w := by logtwo_quiet ring
    _ ≤ 1*CurveContactSum.weightedDegree hfinite z w :=
      mul_le_mul_of_nonneg_right (by logtwo_quiet exact_mod_cast hmargin)
        (CurveContactSum.weightedDegree_nonneg hfinite z w)
    _ = _ := one_mul _

end
end LogTwo.Geometry.ContactFamilyAt

namespace LogTwo.Geometry
open OAI PiExponent PiExponentApprox
open CurveValuationCenter PlaceValuationRing Filter Topology
noncomputable section
variable {E : Type*} [Field E] [Algebra ℂ E]

end
end LogTwo.Geometry
end Source0077

-- Source: LogTwo/Geometry/CoordinateKernel.lean
section Source0078
/-! A short height bound suffices for rigidity. The curve kernel lies strictly
inside the kernel of evaluation at a centered point; prime-chain length then
gives height <= m. No exact dimension formula for a curve quotient is required. -/
namespace LogTwo.Geometry
open OAI PiExponent PiExponentApprox
open CurveValuationCenter CurveCenters PlaceValuationRing PlaceCenteredBranch
noncomputable section
variable {E : Type*} [Field E] [Algebra ℂ E]

def coordinateKernel {n : ℕ} (z : Fin n → E) : Ideal (MvPolynomial (Fin n) ℂ) :=
  RingHom.ker (MvPolynomial.aeval z).toRingHom

instance coordinateKernel_isPrime {n : ℕ} (z : Fin n → E) : (coordinateKernel z).IsPrime :=
  RingHom.ker_isPrime _

@[simp] theorem mem_coordinateKernel {n : ℕ} (z : Fin n → E)
    (F : MvPolynomial (Fin n) ℂ) : F ∈ coordinateKernel z ↔ MvPolynomial.aeval z F = 0 :=
  Iff.rfl

/-- Evaluation at a centered point is the residue of evaluation in its valuation ring. -/
theorem eval_center_eq_zero_of_aeval_eq_zero {n : ℕ}
    (p : NormalizedPlace ℂ E)
    [Algebra.IsIntegral ℂ (IsLocalRing.ResidueField (ring p))]
    (z : Fin n → E) (a : Fin n → ℂ) (hc : Centered z a p)
    (F : MvPolynomial (Fin n) ℂ) (hF : MvPolynomial.aeval z F = 0) :
    MvPolynomial.aeval a F = 0 := by logtwo_quiet
  have hl : MvPolynomial.aeval (lift p z a hc) F = 0 := by logtwo_quiet
    apply IsFractionRing.injective (ring p) E
    rw [map_zero, lift_aeval]
    exact hF
  let φ : ring p →ₐ[ℂ] ℂ :=
    { toRingHom := CurveLocalOrder.residueAugmentation ℂ (ring p)
      commutes' := CurveLocalOrder.residueAugmentation_algebraMap ℂ (ring p) }
  have he := MvPolynomial.comp_aeval_apply (f := lift p z a hc) φ F
  have hφ : ∀ i, φ (lift p z a hc i) = a i := lift_residue p z a hc
  simpa only [hφ, hl, map_zero] using he.symm

theorem coordinateKernel_lt_pointKernel {n : ℕ}
    (p : NormalizedPlace ℂ E)
    [Algebra.IsIntegral ℂ (IsLocalRing.ResidueField (ring p))]
    (z : Fin n → E) (a : Fin n → ℂ) (hc : Centered z a p)
    (hnc : ∃ i, z i ≠ algebraMap ℂ E (a i)) :
    coordinateKernel z < coordinateKernel a := by logtwo_quiet
  apply lt_of_le_of_ne
  · intro F hF
    exact eval_center_eq_zero_of_aeval_eq_zero p z a hc F hF
  · intro he
    obtain ⟨i, hi⟩ := hnc
    have hmem : MvPolynomial.X i - MvPolynomial.C (a i) ∈ coordinateKernel a := by logtwo_quiet
      simp
    rw [← he] at hmem
    apply hi
    simpa only [mem_coordinateKernel, map_sub, MvPolynomial.aeval_X,
      MvPolynomial.aeval_C, sub_eq_zero] using hmem

/-- The upper bound needed by rigidity follows from one centered nonconstant branch. -/
theorem coordinateKernel_height_le {m : ℕ}
    (p : NormalizedPlace ℂ E)
    [Algebra.IsIntegral ℂ (IsLocalRing.ResidueField (ring p))]
    (z : Fin (m+1) → E) (a : Fin (m+1) → ℂ) (hc : Centered z a p)
    (hnc : ∃ i, z i ≠ algebraMap ℂ E (a i)) :
    (coordinateKernel z).height ≤ (m : ℕ∞) := by logtwo_quiet
  have hstep := Ideal.height_add_one_le_of_lt_of_isPrime
    (coordinateKernel_lt_pointKernel p z a hc hnc)
  have hdim := Ideal.height_le_ringKrullDim_of_isPrime (I := coordinateKernel a)
  have hpoint : (coordinateKernel a).height ≤ ((m : ℕ∞)+1) := by logtwo_quiet
    apply WithBot.coe_le_coe.mp
    simpa only [MvPolynomial.ringKrullDim_of_isNoetherianRing,
      ringKrullDim_eq_zero_of_field, zero_add, ENat.card_eq_coe_natCard,
      Nat.card_fin, Nat.cast_add, Nat.cast_one, WithBot.coe_add, WithBot.coe_one,
      WithBot.coe_natCast] using hdim
  exact (ENat.add_le_add_iff_right (by logtwo_quiet simp : (1 : ℕ∞) ≠ ⊤)).mp (hstep.trans hpoint)

theorem coordinateKernel_X_zero_not_mem {m : ℕ}
    (p : NormalizedPlace ℂ E) (z : Fin (m+1) → E) (a : Fin (m+1) → ℂ)
    (hc : Centered z a p) (ha : a 0 ≠ 0) :
    MvPolynomial.X (0 : Fin (m+1)) ∉ coordinateKernel z := by logtwo_quiet
  intro hmem
  have hz : z 0 = 0 := by logtwo_quiet simpa only [mem_coordinateKernel, MvPolynomial.aeval_X] using hmem
  have he := hc.constant_coordinate 0 0 (by logtwo_quiet simpa using hz)
  exact ha he.symm

end
end LogTwo.Geometry
end Source0078

-- Source: LogTwo/Geometry/RigidityInput.lean
section Source0079
/-! The verified field-level inputs to the remaining separated-weight rigidity
argument. No rigidity implication or interpolation surjectivity is postulated. -/
namespace LogTwo.Geometry
open OAI PiExponent PiExponentApprox
open CurveValuationCenter CurveCenters PlaceValuationRing
open Filter Topology
noncomputable section
variable {E : Type*} [Field E] [Algebra ℂ E]

theorem cast_word_cost {ι : Type*} (v : ι → ℚ) (word : List ι) :
    (((word.map v).sum : ℚ) : ℝ) = (word.map (fun i => (v i : ℝ))).sum := by logtwo_quiet
  induction word with
  | nil => simp
  | cons i word ih => simp [ih]

/-- Excess of the constructed complete contact sum supplies the prime-kernel
height bound, the nonvanishing Y coordinate, and, for every sufficiently large N,
a nonzero polynomial of weighted degree at most N whose low-cost derivative
words lie in that kernel. -/
theorem rigidity_data_of_excess {m K : ℕ}
    (hres : ∀ p : NormalizedPlace ℂ E,
      Algebra.IsIntegral ℂ (IsLocalRing.ResidueField (ring p)))
    (hfinite : ∀ f : E, Transcendental ℂ f →
      FiniteDimensional (IntermediateField.adjoin ℂ {f}) E)
    (z : Fin (m+1) → E) (y : Fin K → ℂ) (hy : ∀ j, y j ≠ 0)
    (c : Fin K → Fin m → ℂ) (hz : ∃ i, Transcendental ℂ (z i)) (hK : 0 < K)
    (w v : Fin (m+1) → ℚ) (hw : ∀ i, 0 < w i) (hv : ∀ i, 0 < v i)
    (sigma : ℚ) (hsigma : 0 < sigma)
    (hvol : (K : ℝ)*(1+3*(sigma : ℝ))^(m+1)*(∏ i, (w i : ℝ))/(∏ i, (v i : ℝ)) < 1)
    (hexcess : CurveContactSum.weightedDegree hfinite z w <
      (1+(sigma : ℝ)) * ∑ p ∈ ContactFamilyAt.places hfinite z y c hz,
        (ContactFamilyAt.contact hres hfinite z y hy c hz hK v p : ℝ)) :
    (coordinateKernel z).height ≤ (m : ℕ∞) ∧
      MvPolynomial.X (0 : Fin (m+1)) ∉ coordinateKernel z ∧
      ∀ᶠ N : ℕ in atTop, ∃ F : FramePolynomial m, F ≠ 0 ∧
        HasWeightedDegreeLE (fun i => (w i : ℝ)) N F ∧
        ∀ word : List (Fin (m+1)),
          (word.map (fun i => (v i : ℝ))).sum ≤ (sigma : ℝ)*N →
            polynomialFrameWord m word F ∈ coordinateKernel z := by logtwo_quiet
  classical
  have hS : (ContactFamilyAt.places hfinite z y c hz).Nonempty := by logtwo_quiet
    by_contra hn
    rw [Finset.not_nonempty_iff_eq_empty.mp hn, Finset.sum_empty, mul_zero] at hexcess
    exact (not_lt_of_ge (CurveContactSum.weightedDegree_nonneg hfinite z w)) hexcess
  obtain ⟨p, hp⟩ := hS
  let := hres p
  let j := ContactFamilyAt.center hfinite z y c hz hK p
  have hc := ContactFamilyAt.centered hfinite z y c hz hK p hp
  refine ⟨coordinateKernel_height_le p z (centerPoint (y j) (c j)) hc
    (ContactFamilyAt.nonconstant z _ _ hz),
    coordinateKernel_X_zero_not_mem p z (centerPoint (y j) (c j)) hc (hy j), ?_⟩
  filter_upwards [ContactFamilyAt.eventually_exists_annihilator_of_excess hres hfinite
    z y hy c hz hK w v hw hv sigma hsigma hvol hexcess] with N hN
  obtain ⟨F, hF0, hF, hwords⟩ := hN
  refine ⟨F, hF0, hF, ?_⟩
  intro word hword
  apply hwords word
  rw [← cast_word_cost] at hword
  exact_mod_cast hword

end
end LogTwo.Geometry
end Source0079

-- Source: OAI/NumberTheory/PiExponent/Approximation/WeightSeparationProducts.lean
section Source0080
/-
Modification notice for the LogTwo project.
Derived from openai/math (Apache-2.0), revision adc7f1241b42e322a6451854ab7e4b4c146bf78a.
Original source: lean/OAI/NumberTheory/PiExponent/Approximation/WeightSeparationProducts.lean
Changes: Convert module/import declarations to the Lean 4.34 public module format.
See ../THIRD_PARTY_NOTICES.txt for provenance and the recorded changes.
-/

namespace OAI

namespace PiExponent

theorem product_dominance_of_lower_indices
    (x : ℕ → ℝ) (D : ℝ) (hx : ∀ j, 1 ≤ x j) (hD : 0 < D)
    (A B : Finset ℕ) (i : ℕ) (hiA : i ∈ A)
    (hB : ∀ j ∈ B, j < i)
    (hgrowth : D * (∏ j ∈ Finset.range i, x j) < x i) :
    D * (∏ j ∈ B, x j) < ∏ j ∈ A, x j := by logtwo_quiet
  have hxnonneg : ∀ j, 0 ≤ x j := fun j => le_trans zero_le_one (hx j)
  have hsub : B ⊆ Finset.range i := by logtwo_quiet
    intro j hj
    exact Finset.mem_range.mpr (hB j hj)
  have hprodB : (∏ j ∈ B, x j) ≤ ∏ j ∈ Finset.range i, x j :=
    Finset.prod_le_prod_of_subset_of_one_le₀ hsub
      (fun j _ => hxnonneg j) (fun j _ _ => hx j)
  have hprodA : x i ≤ ∏ j ∈ A, x j := by logtwo_quiet
    have hsubA : ({i} : Finset ℕ) ⊆ A := Finset.singleton_subset_iff.mpr hiA
    simpa only [Finset.prod_singleton] using
      (Finset.prod_le_prod_of_subset_of_one_le₀ hsubA
        (fun j _ => hxnonneg j) (fun j _ _ => hx j))
  exact lt_of_lt_of_le
    (lt_of_le_of_lt (mul_le_mul_of_nonneg_left hprodB hD.le) hgrowth) hprodA

theorem normalized_products_separated
    (x : ℕ → ℝ) (D : ℝ) (hx : ∀ j, 1 ≤ x j) (hD : 0 < D)
    (A B : Finset ℕ) (i : ℕ) (hiA : i ∈ A) (hiB : i ∉ B)
    (hB : ∀ j ∈ B \ A, j < i)
    (hgrowth : D * (∏ j ∈ Finset.range i, x j) < x i) :
    D * (∏ j ∈ B, x j) < ∏ j ∈ A, x j := by logtwo_quiet
  have hdiff : D * (∏ j ∈ B \ A, x j) < ∏ j ∈ A \ B, x j :=
    product_dominance_of_lower_indices x D hx hD (A \ B) (B \ A) i
      (Finset.mem_sdiff.mpr ⟨hiA, hiB⟩) hB hgrowth
  have hcommon : 0 < ∏ j ∈ A ∩ B, x j :=
    Finset.prod_pos (fun j _ => lt_of_lt_of_le zero_lt_one (hx j))
  calc
    D * (∏ j ∈ B, x j)
        = (∏ j ∈ A ∩ B, x j) * (D * (∏ j ∈ B \ A, x j)) := by logtwo_quiet
            rw [← Finset.prod_inter_mul_prod_sdiff B A x, Finset.inter_comm B A]
            ac_rfl
    _ < (∏ j ∈ A ∩ B, x j) * (∏ j ∈ A \ B, x j) :=
      mul_lt_mul_of_pos_left hdiff hcommon
    _ = ∏ j ∈ A, x j := Finset.prod_inter_mul_prod_sdiff A B x

end PiExponent

end OAI
end Source0080

-- Source: OAI/NumberTheory/PiExponent/Approximation/WeightSeparation.lean
section Source0081
/-
Modification notice for the LogTwo project.
Derived from openai/math (Apache-2.0), revision adc7f1241b42e322a6451854ab7e4b4c146bf78a.
Original source: lean/OAI/NumberTheory/PiExponent/Approximation/WeightSeparation.lean
Changes: Convert module/import declarations to the Lean 4.34 public module format.
See ../THIRD_PARTY_NOTICES.txt for provenance and the recorded changes.
-/

namespace OAI

namespace PiExponentApprox

noncomputable section

def geometricDegreeWeight (w0 : ℝ) (x : ℕ → ℝ) (i : ℕ) : ℝ :=
  if i = 0 then w0 else x i

def geometricJetWeight (v0 theta : ℝ) (x : ℕ → ℝ) (i : ℕ) : ℝ :=
  if i = 0 then v0 else x i / theta

def weightSeparationFactor (m : ℕ) (C w0 v0 theta : ℝ) : ℝ :=
  C * (max 1 (max v0 (1 / theta) / min w0 1)) ^ (m + 1)

theorem weightSeparationFactor_pos
    (m : ℕ) (C w0 v0 theta : ℝ) (hC : 0 < C) :
    0 < weightSeparationFactor m C w0 v0 theta := by logtwo_quiet
  unfold weightSeparationFactor
  have hbase : 0 < max 1 (max v0 (1 / theta) / min w0 1) :=
    lt_of_lt_of_le zero_lt_one (le_max_left _ _)
  exact mul_pos hC (pow_pos hbase _)

theorem geometric_weight_products_of_normalized
    (m : ℕ) (C w0 v0 theta : ℝ) (x : ℕ → ℝ)
    (hC : 0 < C) (hw0 : 0 < w0) (hv0 : 0 < v0) (htheta : 0 < theta)
    (hx0 : x 0 = 1) (hx : ∀ i, 1 ≤ x i)
    (A B : Finset ℕ) (hcard : A.card = B.card) (hbound : B.card ≤ m + 1)
    (hsep : weightSeparationFactor m C w0 v0 theta * (∏ i ∈ B, x i) <
      ∏ i ∈ A, x i) :
    C * (∏ i ∈ B, geometricJetWeight v0 theta x i) <
      ∏ i ∈ A, geometricDegreeWeight w0 x i := by logtwo_quiet
  let L : ℝ := min w0 1
  let R : ℝ := max v0 (1 / theta)
  let T : ℝ := max 1 (R / L)
  have hL : 0 < L := lt_min hw0 zero_lt_one
  have hR : 0 < R := lt_of_lt_of_le hv0 (le_max_left _ _)
  have hT : 1 ≤ T := le_max_left _ _
  have hxpos : ∀ i, 0 < x i := fun i => lt_of_lt_of_le zero_lt_one (hx i)
  have hdeg (i : ℕ) : L * x i ≤ geometricDegreeWeight w0 x i := by logtwo_quiet
    by_cases hi : i = 0
    · subst i
      simp only [geometricDegreeWeight, hx0, mul_one]
      exact min_le_left _ _
    · simp only [geometricDegreeWeight, ite_eq_right hi]
      exact mul_le_of_le_one_left (le_of_lt (hxpos i)) (min_le_right _ _)
  have hjet (i : ℕ) : geometricJetWeight v0 theta x i ≤ R * x i := by logtwo_quiet
    by_cases hi : i = 0
    · subst i
      simp only [geometricJetWeight, hx0, mul_one]
      exact le_max_left _ _
    · simp only [geometricJetWeight, ite_eq_right hi]
      calc
        x i / theta = (1 / theta) * x i := by logtwo_quiet ring
        _ ≤ R * x i := mul_le_mul_of_nonneg_right (le_max_right _ _)
          (le_of_lt (hxpos i))
  have hdegprod : L ^ A.card * (∏ i ∈ A, x i) ≤
      ∏ i ∈ A, geometricDegreeWeight w0 x i := by logtwo_quiet
    calc
      _ = ∏ i ∈ A, (L * x i) := by logtwo_quiet
        rw [Finset.prod_mul_distrib, Finset.prod_const]
      _ ≤ _ := Finset.prod_le_prod₀ (fun i _ => mul_nonneg (le_of_lt hL)
        (le_of_lt (hxpos i))) (fun i _ => hdeg i)
  have hjetnonneg (i : ℕ) : 0 ≤ geometricJetWeight v0 theta x i := by logtwo_quiet
    unfold geometricJetWeight
    split
    · exact le_of_lt hv0
    · exact div_nonneg (le_of_lt (hxpos i)) (le_of_lt htheta)
  have hjetprod : (∏ i ∈ B, geometricJetWeight v0 theta x i) ≤
      R ^ B.card * (∏ i ∈ B, x i) := by logtwo_quiet
    calc
      _ ≤ ∏ i ∈ B, (R * x i) := Finset.prod_le_prod₀
        (fun i _ => hjetnonneg i) (fun i _ => hjet i)
      _ = _ := by logtwo_quiet rw [Finset.prod_mul_distrib, Finset.prod_const]
  have hRle : R ≤ T * L := (div_le_iff₀ hL).mp (le_max_right _ _)
  have hpowers : R ^ B.card ≤ T ^ (m + 1) * L ^ B.card := by logtwo_quiet
    calc
      R ^ B.card ≤ (T * L) ^ B.card := pow_le_pow_left₀ (le_of_lt hR) hRle _
      _ = T ^ B.card * L ^ B.card := mul_pow _ _ _
      _ ≤ T ^ (m + 1) * L ^ B.card := mul_le_mul_of_nonneg_right
        (pow_le_pow_right₀ hT hbound) (pow_nonneg (le_of_lt hL) _)
  have hprodB : 0 ≤ ∏ i ∈ B, x i := Finset.prod_nonneg fun i _ => le_of_lt (hxpos i)
  calc
    C * (∏ i ∈ B, geometricJetWeight v0 theta x i) ≤
        C * (R ^ B.card * (∏ i ∈ B, x i)) :=
      mul_le_mul_of_nonneg_left hjetprod (le_of_lt hC)
    _ ≤ C * ((T ^ (m + 1) * L ^ B.card) * (∏ i ∈ B, x i)) :=
      mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_right hpowers hprodB) (le_of_lt hC)
    _ = L ^ A.card * (weightSeparationFactor m C w0 v0 theta *
          (∏ i ∈ B, x i)) := by logtwo_quiet
      rw [hcard]
      change C * ((T ^ (m + 1) * L ^ B.card) * (∏ i ∈ B, x i)) =
        L ^ B.card * ((C * T ^ (m + 1)) * (∏ i ∈ B, x i))
      ring
    _ < L ^ A.card * (∏ i ∈ A, x i) :=
      mul_lt_mul_of_pos_left hsep (pow_pos hL _)
    _ ≤ _ := hdegprod

def SeparatedWeightGrowth (m : ℕ) (D : ℝ) (x : ℕ → ℝ) : Prop :=
  ∀ i, 0 < i → i ≤ m → D * (∏ j ∈ Finset.range i, x j) < x i

theorem geometric_weight_products_separated
    (m : ℕ) (C w0 v0 theta : ℝ) (x : ℕ → ℝ)
    (hC : 0 < C) (hw0 : 0 < w0) (hv0 : 0 < v0) (htheta : 0 < theta)
    (hx0 : x 0 = 1) (hx : ∀ i, 1 ≤ x i)
    (hgrowth : SeparatedWeightGrowth m (weightSeparationFactor m C w0 v0 theta) x)
    (A B : Finset ℕ) (hcard : A.card = B.card)
    (hA : A ⊆ Finset.range (m + 1)) (hB : B ⊆ Finset.range (m + 1))
    (i : ℕ) (hi : 0 < i) (hiA : i ∈ A) (hiB : i ∉ B)
    (hbelow : ∀ j ∈ B \ A, j < i) :
    C * (∏ j ∈ B, geometricJetWeight v0 theta x j) <
      ∏ j ∈ A, geometricDegreeWeight w0 x j := by logtwo_quiet
  have hibound : i ≤ m := Nat.le_of_lt_succ (Finset.mem_range.mp (hA hiA))
  have hcardbound : B.card ≤ m + 1 := by logtwo_quiet
    simpa only [Finset.card_range] using Finset.card_le_card hB
  apply geometric_weight_products_of_normalized m C w0 v0 theta x
    hC hw0 hv0 htheta hx0 hx A B hcard hcardbound
  exact PiExponent.normalized_products_separated x
    (weightSeparationFactor m C w0 v0 theta) hx
    (weightSeparationFactor_pos m C w0 v0 theta hC)
    A B i hiA hiB hbelow (hgrowth i hi hibound)

end
end PiExponentApprox

end OAI
end Source0081

-- Source: LogTwo/Geometry/SeparatedWeights.lean
section Source0082
/-
Modification notice for the LogTwo project.
Adapted from openai/math (Apache-2.0), revision adc7f1241b42e322a6451854ab7e4b4c146bf78a.
Changes: Adapt the finite-index conversion to the log-two separated weights.
See ../THIRD_PARTY_NOTICES.txt for provenance and the recorded changes.
-/

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
    SeparatedProducts (columnWeight w) (fun i => (jetWeight w i : ℝ)) M := by logtwo_quiet
  classical
  intro A B hcard i hi hiA hiB hhigh
  let e : Fin (m+1) ↪ ℕ := ⟨Fin.val, Fin.val_injective⟩
  have hbound (S : Finset (Fin (m+1))) : S.map e ⊆ Finset.range (m+1) := by logtwo_quiet
    intro j hj
    obtain ⟨k, hk, rfl⟩ := Finset.mem_map.mp hj
    exact Finset.mem_range.mpr k.isLt
  have hbelow : ∀ j ∈ B.map e \ A.map e, j < i.val := by logtwo_quiet
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
    (by logtwo_quiet exact_mod_cast w.w0_pos) (by logtwo_quiet exact_mod_cast w.v0_pos)
    (by logtwo_quiet exact_mod_cast w.theta_pos) hx0 hx hgrowth (A.map e) (B.map e)
    (by logtwo_quiet simpa using hcard) (hbound A) (hbound B) i.val hn
    (Finset.mem_map.mpr ⟨i, hiA, rfl⟩)
    (by logtwo_quiet
      intro hmem
      obtain ⟨a, haB, hai⟩ := Finset.mem_map.mp hmem
      exact hiB ((Fin.ext hai : a = i) ▸ haB)) hbelow
  have hw (j : Fin (m+1)) :
      geometricDegreeWeight w.w0 x j.val = columnWeight w j := by logtwo_quiet
    refine Fin.cases ?_ (fun k => ?_) j
    · simp [geometricDegreeWeight, columnWeight, InterpolationMatrix.columnWeights]
    · simp [geometricDegreeWeight, columnWeight, InterpolationMatrix.columnWeights, hmatch]
  have hv (j : Fin (m+1)) :
      geometricJetWeight w.v0 w.theta x j.val = (jetWeight w j : ℝ) := by logtwo_quiet
    refine Fin.cases ?_ (fun k => ?_) j
    · simp [geometricJetWeight, jetWeight]
    · simp [geometricJetWeight, jetWeight, hmatch]
  simpa only [Finset.prod_map, e, Function.Embedding.coeFn_mk, hw, hv] using h

/-- Index zero is the normalized horizontal coordinate; denominator i is at i+1. -/
def normalizedLogWeights (q : ℕ → ℕ) : ℕ → ℝ :=
  fun i => Nat.casesOn i 1 (fun j => (Arithmetic.ceilLogWeight (q j) : ℝ))

theorem normalizedLogWeights_one_le (q : ℕ → ℕ) (hq : ∀ i, 2 ≤ q i) :
    ∀ i, 1 ≤ normalizedLogWeights q i := by logtwo_quiet
  intro i
  cases i with
  | zero => exact le_rfl
  | succ i =>
    have h := ceilLogWeight_pos (hq i)
    change (0 : ℚ) < (⌈Real.log (q i : ℝ)⌉₊ : ℚ) at h
    have hn : 1 ≤ ⌈Real.log (q i : ℝ)⌉₊ := by logtwo_quiet exact_mod_cast h
    change (1 : ℝ) ≤ ((⌈Real.log (q i : ℝ)⌉₊ : ℚ) : ℝ)
    exact_mod_cast hn

theorem normalizedLogWeights_prod (q : ℕ → ℕ) (i : ℕ) :
    (∏ j ∈ Finset.range (i+1), normalizedLogWeights q j) =
      ∏ j : Fin i, (Arithmetic.ceilLogWeight (q j) : ℝ) := by logtwo_quiet
  rw [Finset.prod_range_succ']
  simp [normalizedLogWeights]
  exact (Fin.prod_univ_eq_prod_range _ _).symm

end
end LogTwo.Geometry
end Source0082

-- Source: OAI/NumberTheory/PiExponent/Analysis/LogarithmicObstruction.lean
section Source0083
-- Modified in this edition: unused plain lemmas removed; see reduction.json.
/-
Modification notice for the LogTwo project.
Derived from openai/math (Apache-2.0), revision adc7f1241b42e322a6451854ab7e4b4c146bf78a.
Original source: lean/OAI/NumberTheory/PiExponent/Analysis/LogarithmicObstruction.lean
Changes: Convert module/import declarations to the Lean 4.34 public module format.
See ../THIRD_PARTY_NOTICES.txt for provenance and the recorded changes.
-/

namespace OAI

noncomputable section

namespace PiExponent

open scoped LaurentSeries Matrix

open Polynomial

theorem polynomial_logarithmic_equation_impossible {K : Type*} [Field K] [CharZero K]
    (P Q : K[X]) (hQ : Q ≠ 0) (hcop : IsCoprime P Q) {c : K} (hc : c ≠ 0) :
    X * (derivative P * Q - P * derivative Q) ≠ C c * Q ^ 2 := by logtwo_quiet
  intro heq
  obtain ⟨U, hfactor, hU⟩ := Q.exists_eq_pow_rootMultiplicity_mul_and_not_dvd hQ 0
  simp only [map_zero, sub_zero] at hfactor hU
  have hU0 : U.coeff 0 ≠ 0 := fun h => hU (X_dvd_iff.mpr h)
  cases hn : Q.rootMultiplicity 0 with
  | zero =>
      have hQ0 : Q.coeff 0 ≠ 0 := by logtwo_quiet
        rw [hfactor, hn]
        simpa using hU0
      have hconst := congrArg (fun f : K[X] => f.coeff 0) heq
      have hz : c * (Q.coeff 0) ^ 2 = 0 := by logtwo_quiet simpa [pow_two] using hconst.symm
      exact (mul_ne_zero hc (pow_ne_zero _ hQ0)) hz
  | succ n =>
      have hQfactor : Q = X ^ (n + 1) * U := by logtwo_quiet simpa [hn] using hfactor
      have hQ0 : Q.coeff 0 = 0 := by logtwo_quiet simp [hQfactor]
      have hP0 : P.coeff 0 ≠ 0 := by logtwo_quiet
        intro hp
        obtain ⟨A, B, hab⟩ := hcop
        have hconst := congrArg (fun f : K[X] => f.coeff 0) hab
        simp [hp, hQ0] at hconst
      have hcancel :
          X * derivative P * U - P * (C (n + 1 : K) * U + X * derivative U) =
            C c * X ^ (n + 1) * U ^ 2 := by logtwo_quiet
        apply mul_left_cancel₀ (pow_ne_zero (n + 1) (X_ne_zero (R := K)))
        calc
          X ^ (n + 1) *
              (X * derivative P * U - P * (C (n + 1 : K) * U + X * derivative U)) =
              X * (derivative P * Q - P * derivative Q) := by logtwo_quiet
                rw [hQfactor, derivative_mul, derivative_X_pow_succ]
                ring
          _ = C c * Q ^ 2 := heq
          _ = X ^ (n + 1) * (C c * X ^ (n + 1) * U ^ 2) := by logtwo_quiet rw [hQfactor]; ring
      have hconst := congrArg (fun f : K[X] => f.coeff 0) hcancel
      have hz : P.coeff 0 * ((n + 1 : K) * U.coeff 0) = 0 := by logtwo_quiet
        simpa using hconst
      exact (mul_ne_zero hP0 (mul_ne_zero (Nat.cast_add_one_ne_zero n) hU0)) hz

theorem ratFunc_derivation_polynomial {K : Type*} [Field K]
    (D : Derivation K (RatFunc K) (RatFunc K))
    (hDX : D RatFunc.X = 1) (p : K[X]) :
    D (algebraMap K[X] (RatFunc K) p) =
      algebraMap K[X] (RatFunc K) (derivative p) := by logtwo_quiet
  simpa [RatFunc.aeval_X_left_eq_algebraMap, hDX] using D.comp_aeval_eq RatFunc.X p

theorem ratFunc_derivation_ne_simple_pole {K : Type*} [Field K] [CharZero K]
    (D : Derivation K (RatFunc K) (RatFunc K))
    (hDX : D RatFunc.X = 1) (r : RatFunc K) {c : K} (hc : c ≠ 0) :
    D r ≠ RatFunc.C c / RatFunc.X := by logtwo_quiet
  intro heq
  have hquot := D.leibniz_div (algebraMap K[X] (RatFunc K) r.num)
    (algebraMap K[X] (RatFunc K) r.denom)
  rw [RatFunc.num_div_denom, ratFunc_derivation_polynomial D hDX,
    ratFunc_derivation_polynomial D hDX] at hquot
  have hder : D r =
      algebraMap K[X] (RatFunc K) (derivative r.num * r.denom - r.num * derivative r.denom) /
        (algebraMap K[X] (RatFunc K) r.denom) ^ 2 := by logtwo_quiet
    rw [hquot]
    simp only [smul_eq_mul, map_sub, map_mul, div_eq_mul_inv, inv_pow]
    ring
  have hden : algebraMap K[X] (RatFunc K) r.denom ≠ 0 :=
    RatFunc.algebraMap_ne_zero r.denom_ne_zero
  have hx : (RatFunc.X : RatFunc K) ≠ 0 := by logtwo_quiet
    rw [← RatFunc.algebraMap_X]
    exact RatFunc.algebraMap_ne_zero X_ne_zero
  have hcross := (div_eq_div_iff (pow_ne_zero 2 hden) hx).mp (hder.symm.trans heq)
  apply polynomial_logarithmic_equation_impossible r.num r.denom r.denom_ne_zero
    r.isCoprime_num_denom hc
  apply RatFunc.algebraMap_injective K
  simpa only [map_mul, map_pow, RatFunc.algebraMap_X, RatFunc.algebraMap_C, mul_comm] using hcross

theorem derivation_intermediate_smul
    {k F E : Type*} [Field k] [Field F] [Field E]
    [Algebra k F] [Algebra k E] [Algebra F E] [IsScalarTower k F E]
    (d : Derivation k F F) (D : Derivation k E E)
    (hcompat : ∀ a : F, D (algebraMap F E a) = algebraMap F E (d a))
    (a : F) (z : E) : D (a • z) = d a • z + a • D z := by logtwo_quiet
  rw [Algebra.smul_def, D.leibniz, hcompat]
  simp only [smul_eq_mul, Algebra.smul_def]
  ring

theorem derivation_basis_coordinates
    {k F E ι : Type*} [Field k] [Field F] [Field E] [Fintype ι]
    [Algebra k F] [Algebra k E] [Algebra F E] [IsScalarTower k F E]
    (d : Derivation k F F) (D : Derivation k E E)
    (hcompat : ∀ a : F, D (algebraMap F E a) = algebraMap F E (d a))
    (b : Module.Basis ι F E) (z : E) (i : ι) :
    b.repr (D z) i = d (b.repr z i) +
      ∑ j, b.repr z j * b.repr (D (b j)) i := by logtwo_quiet
  classical
  conv_lhs => rw [← b.sum_repr z]
  simp only [map_sum, derivation_intermediate_smul d D hcompat, map_add,
    map_smul, Finset.sum_add_distrib, Finsupp.coe_add, Pi.add_apply,
    Finsupp.coe_finsetSum, Finset.sum_apply, Finsupp.coe_smul, Pi.smul_apply, smul_eq_mul]
  simp [Finsupp.single_apply, eq_comm]

theorem derivation_trace_of_basis
    {k F E ι : Type*} [Field k] [Field F] [Field E] [Fintype ι]
    [Algebra k F] [Algebra k E] [Algebra F E] [IsScalarTower k F E]
    (d : Derivation k F F) (D : Derivation k E E)
    (hcompat : ∀ a : F, D (algebraMap F E a) = algebraMap F E (d a))
    (b : Module.Basis ι F E) (x : E) :
    d (Algebra.trace F E x) = Algebra.trace F E (D x) := by logtwo_quiet
  classical
  let M := Algebra.leftMulMatrix b x
  let N : Matrix ι ι F := fun i j => b.repr (D (b j)) i
  have hentry (i j : ι) :
      Algebra.leftMulMatrix b (D x) i j + (M * N) i j =
        d (M i j) + (N * M) i j := by logtwo_quiet
    have hMN : (M * N) i j = ∑ t, M i t * N t j := rfl
    have hNM : (N * M) i j = ∑ t, N i t * M t j := rfl
    have hz := derivation_basis_coordinates d D hcompat b (x * b j) i
    have hm := congrFun (Algebra.leftMulMatrix_mulVec_repr b x (D (b j))) i
    have hl : b.repr (D (x * b j)) i =
        Algebra.leftMulMatrix b (D x) i j + (M * N) i j := by logtwo_quiet
      rw [hMN, D.leibniz]
      simp only [smul_eq_mul, map_add, Finsupp.add_apply]
      rw [← hm]
      simp only [M, N, Algebra.leftMulMatrix_eq_repr_mul,
        Matrix.mulVec, dotProduct, mul_comm, add_comm]
    rw [hl] at hz
    simpa only [hNM, M, N, Algebra.leftMulMatrix_eq_repr_mul, mul_comm] using hz
  have hs := Finset.sum_congr rfl (fun i (_ : i ∈ Finset.univ) => hentry i i)
  have ht : Matrix.trace (Algebra.leftMulMatrix b (D x)) + Matrix.trace (M * N) =
      d (Matrix.trace M) + Matrix.trace (N * M) := by logtwo_quiet
    simpa only [Matrix.trace, Matrix.diag_apply, Finset.sum_add_distrib, map_sum] using hs
  rw [Matrix.trace_mul_comm M N] at ht
  have ht' := add_right_cancel ht
  simpa only [Algebra.trace_eq_matrix_trace b, M] using ht'.symm

theorem finite_extension_derivation_ne_simple_pole
    {K E : Type*} [Field K] [CharZero K] [Field E]
    [Algebra K E] [Algebra (RatFunc K) E] [IsScalarTower K (RatFunc K) E]
    [FiniteDimensional (RatFunc K) E]
    (d : Derivation K (RatFunc K) (RatFunc K)) (D : Derivation K E E)
    (hdX : d RatFunc.X = 1)
    (hcompat : ∀ a : RatFunc K,
      D (algebraMap (RatFunc K) E a) = algebraMap (RatFunc K) E (d a))
    (x : E) {c : K} (hc : c ≠ 0) :
    D x ≠ algebraMap (RatFunc K) E (RatFunc.C c / RatFunc.X) := by logtwo_quiet
  intro hx
  have ht := derivation_trace_of_basis d D hcompat
    (Module.finBasis (RatFunc K) E) x
  rw [hx, Algebra.trace_algebraMap] at ht
  have hdegree : (Module.finrank (RatFunc K) E : K) ≠ 0 := by logtwo_quiet
    exact Nat.cast_ne_zero.mpr (ne_of_gt (Module.finrank_pos (R := RatFunc K) (M := E)))
  apply ratFunc_derivation_ne_simple_pole d hdX (Algebra.trace (RatFunc K) E x)
    (mul_ne_zero hdegree hc)
  calc
    d (Algebra.trace (RatFunc K) E x) =
        Module.finrank (RatFunc K) E • (RatFunc.C c / RatFunc.X) := ht
    _ = RatFunc.C ((Module.finrank (RatFunc K) E : K) * c) / RatFunc.X := by logtwo_quiet
      simp only [map_mul, map_natCast, nsmul_eq_mul, mul_div_assoc]

end PiExponent

end

end OAI
end Source0083

-- Source: OAI/NumberTheory/PiExponent/LocalAlgebra/TranscendenceBasisReduction.lean
section Source0084
/-
Modification notice for the LogTwo project.
Derived from openai/math (Apache-2.0), revision adc7f1241b42e322a6451854ab7e4b4c146bf78a.
Original source: lean/OAI/NumberTheory/PiExponent/LocalAlgebra/TranscendenceBasisReduction.lean
Changes: Convert module/import declarations to the Lean 4.34 public module format.
See ../THIRD_PARTY_NOTICES.txt for provenance and the recorded changes.
-/

namespace OAI

noncomputable section

namespace PiExponent

open scoped IntermediateField.algebraAdjoinAdjoin

theorem exists_intermediateField_finite_over_simple
    (C E : Type*) [Field C] [Field E] [Algebra C E]
    [Algebra.EssFiniteType C E] {Y : E} (hY : Transcendental C Y) :
    ∃ K : IntermediateField C E,
      Transcendental K Y ∧ FiniteDimensional (IntermediateField.adjoin K {Y}) E := by logtwo_quiet
  classical
  have hsingle : AlgebraicIndepOn C id ({Y} : Set E) := by logtwo_quiet
    change AlgebraicIndependent C (fun z : ({Y} : Set E) => (z : E))
    rw [algebraicIndependent_singleton_iff ⟨Y, rfl⟩]
    exact hY
  obtain ⟨t, hsub, ht⟩ := exists_isTranscendenceBasis_superset hsingle
  have hYt : Y ∈ t := hsub (Set.mem_singleton Y)
  let s : Set E := t \ {Y}
  let K : IntermediateField C E := IntermediateField.adjoin C s
  have hts : insert Y s = t := by logtwo_quiet
    ext x
    simp only [s, Set.mem_insert_iff, Set.mem_sdiff, Set.mem_singleton_iff]
    constructor
    · rintro (rfl | ⟨hx, _⟩)
      · exact hYt
      · exact hx
    · intro hx
      by_cases heq : x = Y
      · exact Or.inl heq
      · exact Or.inr ⟨hx, heq⟩
  have hind : AlgebraicIndepOn C id (insert Y s) := by logtwo_quiet
    rw [hts]
    exact ht.1
  have htr : Transcendental (Algebra.adjoin C s) Y := by logtwo_quiet
    have hnot : Y ∉ s := by logtwo_quiet simp [s]
    have hh := (AlgebraicIndepOn.insert_iff hnot).mp hind
    have heq : id '' s = s := Set.image_id s
    rw [heq] at hh
    exact hh.2
  have htrK : Transcendental K Y := by logtwo_quiet
    intro h
    exact htr (h.restrictScalars (Algebra.adjoin C s))
  refine ⟨K, htrK, ?_⟩
  let L := IntermediateField.adjoin K ({Y} : Set E)
  have hL : L.restrictScalars C = IntermediateField.adjoin C t := by logtwo_quiet
    dsimp [L, K]
    rw [IntermediateField.adjoin_adjoin_left]
    congr 1
    rw [Set.union_comm, Set.singleton_union, hts]
  have halg : Algebra.IsAlgebraic L E := by logtwo_quiet
    change Algebra.IsAlgebraic (L.restrictScalars C) E
    rw [hL]
    have hh := ht.isAlgebraic_field
    have heq : Set.range ((↑) : t → E) = t := Subtype.range_coe
    rw [heq] at hh
    exact hh
  let : Algebra.IsAlgebraic L E := halg
  let : IsScalarTower C L E := IsScalarTower.of_algebraMap_eq (fun x => rfl)
  let : Algebra.EssFiniteType L E := Algebra.EssFiniteType.of_comp C L E
  exact Algebra.finite_of_essFiniteType_of_isAlgebraic

end PiExponent

end

end OAI
end Source0084

-- Source: OAI/NumberTheory/PiExponent/Analysis/AlgebraicLogarithmicObstruction.lean
section Source0085
/-
Modification notice for the LogTwo project.
Derived from openai/math (Apache-2.0), revision adc7f1241b42e322a6451854ab7e4b4c146bf78a.
Original source: lean/OAI/NumberTheory/PiExponent/Analysis/AlgebraicLogarithmicObstruction.lean
Changes: Convert module/import declarations to the Lean 4.34 public module format.
See ../THIRD_PARTY_NOTICES.txt for provenance and the recorded changes.
-/

namespace OAI

noncomputable section

namespace PiExponent

open KaehlerDifferential
open scoped TensorProduct Polynomial nonZeroDivisors IntermediateField

def extendDerivation
    {R S T : Type*} [CommRing R] [CommRing S] [CommRing T]
    [Algebra R S] [Algebra R T] [Algebra S T] [IsScalarTower R S T]
    [Algebra.FormallyEtale S T]
    (d : Derivation R S S) : Derivation R T T :=
  ((LinearMap.liftBaseChange T ((Algebra.linearMap S T).comp d.liftKaehlerDifferential)).comp
    (tensorKaehlerEquivOfFormallyEtale R S T).symm.toLinearMap).compDer (D R T)

theorem extendDerivation_algebraMap
    {R S T : Type*} [CommRing R] [CommRing S] [CommRing T]
    [Algebra R S] [Algebra R T] [Algebra S T] [IsScalarTower R S T]
    [Algebra.FormallyEtale S T]
    (d : Derivation R S S) (s : S) :
    extendDerivation (T := T) d (algebraMap S T s) = algebraMap S T (d s) := by logtwo_quiet
  simp [extendDerivation, LinearMap.compDer,
    tensorKaehlerEquivOfFormallyEtale_symm_D_algebraMap,
    Derivation.liftKaehlerDifferential_comp_D]

def ratFuncDerivative {K : Type*} [Field K] : Derivation K (RatFunc K) (RatFunc K) := by logtwo_quiet
  letI : Algebra.FormallyEtale K[X] (RatFunc K) :=
    Algebra.FormallyEtale.of_isLocalization (K[X]⁰)
  exact extendDerivation Polynomial.derivative'

@[simp]
theorem ratFuncDerivative_X {K : Type*} [Field K] :
    ratFuncDerivative (RatFunc.X : RatFunc K) = 1 := by logtwo_quiet
  let : Algebra.FormallyEtale K[X] (RatFunc K) :=
    Algebra.FormallyEtale.of_isLocalization (K[X]⁰)
  change extendDerivation Polynomial.derivative' (RatFunc.X : RatFunc K) = 1
  rw [← RatFunc.algebraMap_X, extendDerivation_algebraMap]
  simp [Polynomial.derivative']

theorem finite_extension_no_logarithmic_differential
    {K E : Type*} [Field K] [CharZero K] [Field E]
    [Algebra K E] [Algebra (RatFunc K) E] [IsScalarTower K (RatFunc K) E]
    [FiniteDimensional (RatFunc K) E] (x : E) :
    D K E x ≠ (algebraMap (RatFunc K) E RatFunc.X)⁻¹ •
      D K E (algebraMap (RatFunc K) E RatFunc.X) := by logtwo_quiet
  let : Algebra.FormallyEtale (RatFunc K) E :=
    Algebra.FormallyEtale.of_isSeparable (RatFunc K) E
  let delta : Derivation K E E := extendDerivation ratFuncDerivative
  have hcompat (a : RatFunc K) :
      delta (algebraMap (RatFunc K) E a) =
        algebraMap (RatFunc K) E (ratFuncDerivative a) :=
    extendDerivation_algebraMap ratFuncDerivative a
  intro heq
  have hd := congrArg delta.liftKaehlerDifferential heq
  simp only [Derivation.liftKaehlerDifferential_comp_D, map_smul, hcompat,
    ratFuncDerivative_X, map_one, smul_eq_mul, mul_one] at hd
  apply finite_extension_derivation_ne_simple_pole ratFuncDerivative delta
    ratFuncDerivative_X hcompat x (c := (1 : K)) one_ne_zero
  simpa only [map_div₀, map_one, one_div, map_inv₀] using hd

theorem adjoin_finite_no_logarithmic_differential
    {K E : Type*} [Field K] [CharZero K] [Field E] [Algebra K E]
    (y : E) (hy : Transcendental K y) [FiniteDimensional K⟮y⟯ E] (x : E) :
    D K E x ≠ y⁻¹ • D K E y := by logtwo_quiet
  let F := K⟮y⟯
  let e : RatFunc K ≃ₐ[K] F := RatFunc.algEquivOfTranscendental y hy
  let : Algebra (RatFunc K) F := e.toRingHom.toAlgebra
  let : Algebra (RatFunc K) E :=
    ((algebraMap F E).comp e.toRingHom).toAlgebra
  let : IsScalarTower (RatFunc K) F E := IsScalarTower.of_algebraMap_eq' rfl
  let : IsScalarTower K (RatFunc K) E := IsScalarTower.of_algebraMap_eq fun a => by logtwo_quiet
    change algebraMap K E a = algebraMap F E (e (algebraMap K (RatFunc K) a))
    rw [e.commutes]
    exact IsScalarTower.algebraMap_apply K F E a
  have : Module.Finite (RatFunc K) F :=
    Module.Finite.of_surjective (Algebra.linearMap (RatFunc K) F) e.surjective
  have : Module.Finite (RatFunc K) E := Module.Finite.trans F E
  have hX : algebraMap (RatFunc K) E RatFunc.X = y := by logtwo_quiet
    change ((RatFunc.algEquivOfTranscendental y hy) RatFunc.X : E) = y
    exact RatFunc.algEquivOfTranscendental_X y hy
  simpa only [hX] using finite_extension_no_logarithmic_differential (K := K) x

theorem logarithmic_differential_base_change
    {C K E : Type*} [Field C] [Field K] [Field E]
    [Algebra C K] [Algebra C E] [Algebra K E] [IsScalarTower C K E]
    {x y : E} (h : D C E x = y⁻¹ • D C E y) :
    D K E x = y⁻¹ • D K E y := by logtwo_quiet
  have hm := congrArg (KaehlerDifferential.map C K E E) h
  simpa only [map_D, map_smul, Algebra.algebraMap_self, RingHom.id_apply] using hm

theorem no_logarithmic_differential_over_intermediateField
    {C E : Type*} [Field C] [CharZero C] [Field E] [Algebra C E]
    (K : IntermediateField C E) (y : E) (hy : Transcendental K y)
    [FiniteDimensional K⟮y⟯ E] (x : E) :
    D C E x ≠ y⁻¹ • D C E y := by logtwo_quiet
  intro h
  exact adjoin_finite_no_logarithmic_differential y hy x
    (logarithmic_differential_base_change (K := K) h)

theorem isAlgebraic_of_logarithmic_differential
    {C E : Type*} [Field C] [CharZero C] [Field E] [Algebra C E]
    [Algebra.EssFiniteType C E] (x y : E)
    (h : D C E x = y⁻¹ • D C E y) : IsAlgebraic C y := by logtwo_quiet
  by_contra hy
  obtain ⟨K, hKy, hfinite⟩ := exists_intermediateField_finite_over_simple C E hy
  have : FiniteDimensional K⟮y⟯ E := hfinite
  exact no_logarithmic_differential_over_intermediateField K y hKy x h

theorem constant_of_logarithmic_differential
    {C E : Type*} [Field C] [CharZero C] [IsAlgClosed C] [Field E] [Algebra C E]
    [Algebra.EssFiniteType C E] (x y : E)
    (h : D C E x = y⁻¹ • D C E y) : ∃ c : C, algebraMap C E c = y := by logtwo_quiet
  have hy := isAlgebraic_of_logarithmic_differential x y h
  have hmem : y ∈ algebraicClosure C E := mem_algebraicClosure_iff.mpr hy
  rw [IntermediateField.eq_bot_of_isAlgClosed_of_isAlgebraic (algebraicClosure C E)] at hmem
  exact IntermediateField.mem_bot.mp hmem

end PiExponent

end

end OAI
end Source0085

-- Source: OAI/NumberTheory/PiExponent/Jets/DifferentialConstant.lean
section Source0086
-- Modified in this edition: unused plain lemmas removed; see reduction.json.
/-
Modification notice for the LogTwo project.
Derived from openai/math (Apache-2.0), revision adc7f1241b42e322a6451854ab7e4b4c146bf78a.
Original source: lean/OAI/NumberTheory/PiExponent/Jets/DifferentialConstant.lean
Changes: Convert module/import declarations to the Lean 4.34 public module format.
See ../THIRD_PARTY_NOTICES.txt for provenance and the recorded changes.
-/

namespace OAI

namespace PiExponent

open KaehlerDifferential

theorem constant_of_differential_eq_zero
    {C E : Type*} [Field C] [CharZero C] [IsAlgClosed C] [Field E] [Algebra C E]
    [Algebra.EssFiniteType C E] (x : E) (hx : D C E x = 0) :
    ∃ c : C, algebraMap C E c = x :=
  constant_of_logarithmic_differential (0 : E) x (by logtwo_quiet simp [hx])

end PiExponent

end OAI
end Source0086

-- Source: OAI/NumberTheory/PiExponent/Jets/NormalBasisRigidity.lean
section Source0087
-- Modified in this edition: unused plain lemmas removed; see reduction.json.
/-
Modification notice for the LogTwo project.
Derived from openai/math (Apache-2.0), revision adc7f1241b42e322a6451854ab7e4b4c146bf78a.
Original source: lean/OAI/NumberTheory/PiExponent/Jets/NormalBasisRigidity.lean
Changes: Convert module/import declarations to the Lean 4.34 public module format.
See ../THIRD_PARTY_NOTICES.txt for provenance and the recorded changes.
-/

namespace OAI

noncomputable section

namespace PiExponent.NormalBasisRigidity

open Set Submodule Module

variable {K V ι : Type*} [Field K] [AddCommGroup V] [Module K V]

def IsNormalBasis (v : ι → V) (A : Finset ι) : Prop :=
  LinearIndepOn K v (A : Set ι) ∧ span K (v '' (A : Set ι)) = ⊤

lemma exists_normalBasis_subset [Fintype ι] (v : ι → V) (S : Set ι)
    (hS : span K (v '' S) = ⊤) :
    ∃ A : Finset ι, (A : Set ι) ⊆ S ∧ IsNormalBasis (K := K) v A := by logtwo_quiet
  classical
  let h := linearIndepOn_empty K v
  let A := h.extend (Set.empty_subset S)
  refine ⟨A.toFinset, ?_, ?_, ?_⟩
  · simpa only [Set.coe_toFinset] using h.extend_subset (Set.empty_subset S)
  · simpa only [Set.coe_toFinset] using h.linearIndepOn_extend (Set.empty_subset S)
  · simpa only [Set.coe_toFinset, A] using
      (h.span_image_extend_eq_span_image (Set.empty_subset S)).trans hS

lemma exists_normalBasis_containing [Fintype ι] (v : ι → V)
    (hv : span K (Set.range v) = ⊤) (i : ι) (hi : v i ≠ 0) :
    ∃ A : Finset ι, i ∈ A ∧ IsNormalBasis (K := K) v A := by logtwo_quiet
  classical
  have h : LinearIndepOn K v ({i} : Set ι) := by logtwo_quiet
    exact LinearIndepOn.singleton hi
  let A := h.extend (Set.subset_univ _)
  refine ⟨A.toFinset, ?_, ?_, ?_⟩
  · exact Set.mem_toFinset.mpr (h.subset_extend (Set.subset_univ _) (Set.mem_singleton i))
  · simpa only [Set.coe_toFinset] using h.linearIndepOn_extend (Set.subset_univ _)
  · simpa only [Set.coe_toFinset, Set.image_univ, A] using
      (h.span_image_extend_eq_span_image (Set.subset_univ _)).trans (by logtwo_quiet simpa using hv)

lemma IsNormalBasis.ne_zero [DecidableEq ι] {v : ι → V} {A : Finset ι}
    (hA : IsNormalBasis (K := K) v A) {i : ι} (hi : i ∈ A) : v i ≠ 0 :=
  hA.1.ne_zero hi

lemma exists_normalBasis_omitting [Fintype ι] (v : ι → V) (i : ι)
    (h : span K (v '' {j | j ≠ i}) = ⊤) :
    ∃ A : Finset ι, i ∉ A ∧ IsNormalBasis (K := K) v A := by logtwo_quiet
  obtain ⟨A, hA, hB⟩ := exists_normalBasis_subset v {j | j ≠ i} h
  exact ⟨A, fun hi => hA hi rfl, hB⟩

lemma mandatory_not_mem_span [Fintype ι] (v : ι → V)
    (hv : span K (Set.range v) = ⊤) (i : ι)
    (hi : ∀ A, IsNormalBasis (K := K) v A → i ∈ A) :
    v i ∉ span K (v '' {j | j ≠ i}) := by logtwo_quiet
  intro hmem
  have hspan : span K (v '' {j | j ≠ i}) = ⊤ := by logtwo_quiet
    apply top_unique
    rw [← hv]
    apply span_le.mpr
    rintro _ ⟨j, rfl⟩
    by_cases hj : j = i
    · subst j
      exact hmem
    · exact subset_span ⟨j, hj, rfl⟩
  obtain ⟨A, hAi, hA⟩ := exists_normalBasis_omitting v i hspan
  exact hAi (hi A hA)

lemma IsNormalBasis.card_eq {v : ι → V} {A : Finset ι}
    (hA : IsNormalBasis (K := K) v A) : A.card = Module.finrank K V := by logtwo_quiet
  classical
  have hli : LinearIndependent K (fun i : A => v i) := hA.1
  let b : Basis A K V := Basis.mk hli (by logtwo_quiet
    have hr : Set.range (fun i : A => v i) = v '' (A : Set ι) := by logtwo_quiet
      ext x
      simp
    rw [hr, hA.2])
  exact (Module.finrank_eq_card_finset_basis b).symm

variable {W : Type*} [AddCommGroup W] [Module K W]

lemma mandatory_coordinate_eq_zero [Fintype ι] (b : Basis ι K V) (q : V →ₗ[K] W)
    (hq : span K (Set.range (fun j => q (b j))) = ⊤) (i : ι)
    (hi : ∀ A, IsNormalBasis (K := K) (fun j => q (b j)) A → i ∈ A)
    (t : V) (ht : q t = 0) : b.repr t i = 0 := by logtwo_quiet
  classical
  by_contra hti
  let S : Submodule K W := span K ((fun j => q (b j)) '' {j | j ≠ i})
  have hsum : (∑ j ∈ Finset.univ.erase i, b.repr t j • q (b j)) ∈ S := by logtwo_quiet
    apply S.sum_mem
    intro j hj
    exact S.smul_mem _ (subset_span ⟨j, (Finset.mem_erase.mp hj).1, rfl⟩)
  have hall : (∑ j, b.repr t j • q (b j)) = 0 := by logtwo_quiet
    calc
      _ = q (∑ j, b.repr t j • b j) := by logtwo_quiet simp only [map_sum, map_smul]
      _ = 0 := by logtwo_quiet rw [b.sum_repr, ht]
  rw [← Finset.sum_erase_add _ _ (Finset.mem_univ i)] at hall
  have hterm : b.repr t i • q (b i) ∈ S := by logtwo_quiet
    have heq : b.repr t i • q (b i) = -(∑ j ∈ Finset.univ.erase i,
        b.repr t j • q (b j)) := eq_neg_of_add_eq_zero_left (by logtwo_quiet simpa only [add_comm] using hall)
    rw [heq]
    exact S.neg_mem hsum
  exact mandatory_not_mem_span (fun j => q (b j)) hq i hi
    ((S.smul_mem_iff hti).mp hterm)

lemma largest_nontangent_mandatory {m : ℕ}
    (u v : Fin (m + 1) → V) (hu : span K (Set.range u) = ⊤)
    (hvu : ∀ i, i ≠ 0 → v i = u i)
    (hexclude : ∀ A B : Finset (Fin (m + 1)),
      IsNormalBasis (K := K) u A → IsNormalBasis (K := K) v B →
      ∀ i, i ≠ 0 → i ∈ A → i ∉ B →
      (∀ j, i < j → (j ∈ A ↔ j ∈ B)) → False)
    (i : Fin (m + 1)) (hi0 : i ≠ 0) (hi : u i ≠ 0)
    (hlarge : ∀ j, i < j → u j = 0)
    (B : Finset (Fin (m + 1))) (hB : IsNormalBasis (K := K) v B) : i ∈ B := by logtwo_quiet
  classical
  obtain ⟨A, hiA, hA⟩ := exists_normalBasis_containing u hu i hi
  by_contra hiB
  apply hexclude A B hA hB i hi0 hiA hiB
  intro j hj
  have hj0 : j ≠ 0 := by logtwo_quiet
    intro h
    subst j
    exact (not_lt_of_ge (Fin.zero_le _)) hj
  have hjA : j ∉ A := fun h => hA.ne_zero h (hlarge j hj)
  have hjB : j ∉ B := fun h => hB.ne_zero h ((hvu j hj0).trans (hlarge j hj))
  simp only [hjA, hjB]

lemma weighted_normalBasis_exclusion {m : ℕ}
    (u v : Fin (m + 1) → V) (w cost : Fin (m + 1) → ℝ) (C : ℝ)
    (hcomparison : ∀ A B, IsNormalBasis (K := K) u A →
      IsNormalBasis (K := K) v B → (∏ j ∈ A, w j) ≤ C * ∏ j ∈ B, cost j)
    (hseparated : ∀ A B : Finset (Fin (m + 1)), A.card = B.card →
      ∀ i, i ≠ 0 → i ∈ A → i ∉ B →
      (∀ j, i < j → (j ∈ A ↔ j ∈ B)) →
      C * (∏ j ∈ B, cost j) < ∏ j ∈ A, w j)
    (A B : Finset (Fin (m + 1)))
    (hA : IsNormalBasis (K := K) u A) (hB : IsNormalBasis (K := K) v B)
    (i : Fin (m + 1)) (hi0 : i ≠ 0) (hiA : i ∈ A) (hiB : i ∉ B)
    (hlarge : ∀ j, i < j → (j ∈ A ↔ j ∈ B)) : False := by logtwo_quiet
  exact (not_lt_of_ge (hcomparison A B hA hB))
    (hseparated A B (hA.card_eq.trans hB.card_eq.symm) i hi0 hiA hiB hlarge)

end PiExponent.NormalBasisRigidity

end

end OAI
end Source0087

-- Source: OAI/NumberTheory/PiExponent/Jets/NormalFrameBasis.lean
section Source0088
/-
Modification notice for the LogTwo project.
Derived from openai/math (Apache-2.0), revision adc7f1241b42e322a6451854ab7e4b4c146bf78a.
Original source: lean/OAI/NumberTheory/PiExponent/Jets/NormalFrameBasis.lean
Changes: Convert module/import declarations to the Lean 4.34 public module format.
See ../THIRD_PARTY_NOTICES.txt for provenance and the recorded changes.
-/

namespace OAI

noncomputable section
namespace PiExponent.NormalBasisRigidity
open Module

variable {K : Type*} [Field K] (m : ℕ) (y : K) (hy : y ≠ 0)

def frameEquiv : (Fin (m + 1) → K) ≃ₗ[K] (Fin (m + 1) → K) where
  toFun c := Fin.cases (y * c 0) (fun i => c i.succ + c 0)
  invFun t := Fin.cases (t 0 / y) (fun i => t i.succ - t 0 / y)
  left_inv c := by logtwo_quiet
    funext i
    refine Fin.cases ?_ (fun j => ?_) i
    · simp [hy]
    · simp [hy]
  right_inv t := by logtwo_quiet
    funext i
    refine Fin.cases ?_ (fun j => ?_) i
    · change y * (t 0 / y) = t 0
      field_simp
    · simp
  map_add' c d := by logtwo_quiet
    funext i
    refine Fin.cases ?_ (fun j => ?_) i
    · simp [mul_add]
    · simp only [Pi.add_apply, Fin.cases_succ]
      ring
  map_smul' a c := by logtwo_quiet
    funext i
    refine Fin.cases ?_ (fun j => ?_) i
    · simp only [Pi.smul_apply, Fin.cases_zero, smul_eq_mul, RingHom.id_apply]
      ring
    · simp [mul_add]

def frameBasis : Basis (Fin (m + 1)) K (Fin (m + 1) → K) :=
  (Pi.basisFun K _).map (frameEquiv m y hy)

@[simp] lemma frameBasis_repr_zero (t : Fin (m + 1) → K) :
    (frameBasis m y hy).repr t 0 = t 0 / y := by logtwo_quiet
  change (Pi.basisFun K _).repr ((frameEquiv m y hy).symm t) 0 = _
  rw [Pi.basisFun_repr]
  rfl

@[simp] lemma frameBasis_repr_succ (t : Fin (m + 1) → K) (i : Fin m) :
    (frameBasis m y hy).repr t i.succ = t i.succ - t 0 / y := by logtwo_quiet
  change (Pi.basisFun K _).repr ((frameEquiv m y hy).symm t) i.succ = _
  rw [Pi.basisFun_repr]
  rfl

@[simp] lemma frameBasis_succ (i : Fin m) :
    frameBasis m y hy i.succ = Pi.basisFun K _ i.succ := by logtwo_quiet
  ext j
  refine Fin.cases ?_ (fun k => ?_) j
  · simp [frameBasis, frameEquiv, Pi.basisFun_apply]
  · simp [frameBasis, frameEquiv, Pi.basisFun_apply, Pi.single_apply]

@[simp] lemma frameBasis_zero_zero : frameBasis m y hy 0 0 = y := by logtwo_quiet
  simp [frameBasis, frameEquiv, Pi.basisFun_apply]

@[simp] lemma frameBasis_zero_succ (i : Fin m) : frameBasis m y hy 0 i.succ = 1 := by logtwo_quiet
  simp [frameBasis, frameEquiv, Pi.basisFun_apply]

variable {V : Type*} [AddCommGroup V] [Module K V]

lemma mandatory_logarithmic_differential (q : (Fin (m + 1) → K) →ₗ[K] V)
    (hq : Submodule.span K (Set.range (fun j => q (frameBasis m y hy j))) = ⊤)
    (i : Fin m)
    (hi : ∀ A, IsNormalBasis (K := K) (fun j => q (frameBasis m y hy j)) A → i.succ ∈ A)
    (t : Fin (m + 1) → K) (ht : q t = 0) : t i.succ = t 0 / y := by logtwo_quiet
  have h := mandatory_coordinate_eq_zero (frameBasis m y hy) q hq i.succ hi t ht
  rw [frameBasis_repr_succ] at h
  exact sub_eq_zero.mp h

lemma span_mapped_basis_eq_top {ι U : Type*} [Fintype ι]
    [AddCommGroup U] [Module K U] (b : Basis ι K U) (q : U →ₗ[K] V)
    (hq : Function.Surjective q) :
    Submodule.span K (Set.range (fun j => q (b j))) = ⊤ := by logtwo_quiet
  apply top_unique
  intro x _
  obtain ⟨t, rfl⟩ := hq x
  rw [← b.sum_repr t, map_sum]
  apply Submodule.sum_mem
  intro i _
  rw [map_smul]
  exact Submodule.smul_mem _ _ (Submodule.subset_span (Set.mem_range_self i))

theorem normal_basis_differential_dichotomy
    (q : (Fin (m + 1) → K) →ₗ[K] V) (hq : Function.Surjective q) (hq0 : q ≠ 0)
    (hexclude : ∀ A B : Finset (Fin (m + 1)),
      IsNormalBasis (K := K) (fun j => q (Pi.basisFun K _ j)) A →
      IsNormalBasis (K := K) (fun j => q (frameBasis m y hy j)) B →
      ∀ i, i ≠ 0 → i ∈ A → i ∉ B →
      (∀ j, i < j → (j ∈ A ↔ j ∈ B)) → False) :
    (∀ t, q t = 0 → t 0 = 0) ∨
      ∃ i : Fin m, ∀ t, q t = 0 → t i.succ = t 0 / y := by logtwo_quiet
  classical
  let b := Pi.basisFun K (Fin (m + 1))
  let S := Finset.univ.filter (fun i : Fin (m + 1) => i ≠ 0 ∧ q (b i) ≠ 0)
  by_cases hS : S.Nonempty
  · let i := S.max' hS
    have hiS : i ∈ S := Finset.max'_mem _ _
    have hi := (Finset.mem_filter.mp hiS).2
    have hlarge : ∀ j, i < j → q (b j) = 0 := by logtwo_quiet
      intro j hj
      by_contra hjq
      have hj0 : j ≠ 0 := by logtwo_quiet
        intro hz
        subst j
        exact (not_lt_of_ge (Fin.zero_le _)) hj
      have hjS : j ∈ S := Finset.mem_filter.mpr ⟨Finset.mem_univ _, hj0, hjq⟩
      exact (not_lt_of_ge (Finset.le_max' _ _ hjS)) hj
    have hvu : ∀ j : Fin (m + 1), j ≠ 0 → q (frameBasis m y hy j) = q (b j) := by logtwo_quiet
      intro j
      refine Fin.cases ?_ (fun k _ => ?_) j
      · intro hz
        exact (hz rfl).elim
      · rw [frameBasis_succ]
    have hmand : ∀ B, IsNormalBasis (K := K) (fun j => q (frameBasis m y hy j)) B → i ∈ B :=
      largest_nontangent_mandatory (fun j => q (b j))
        (fun j => q (frameBasis m y hy j)) (span_mapped_basis_eq_top b q hq)
        hvu hexclude i hi.1 hi.2 hlarge
    rcases Fin.eq_zero_or_eq_succ i with hz | ⟨j, hj⟩
    · exact (hi.1 hz).elim
    · right
      refine ⟨j, ?_⟩
      intro t ht
      apply mandatory_logarithmic_differential m y hy q
        (span_mapped_basis_eq_top (frameBasis m y hy) q hq) j ?_ t ht
      intro B hB
      rw [← hj]
      exact hmand B hB
  · have hpos : ∀ j : Fin m, q (b j.succ) = 0 := by logtwo_quiet
      intro j
      by_contra hj
      exact hS ⟨j.succ, Finset.mem_filter.mpr ⟨Finset.mem_univ _, Fin.succ_ne_zero _, hj⟩⟩
    have he0 : q (b 0) ≠ 0 := by logtwo_quiet
      intro he
      apply hq0
      apply b.ext
      intro j
      refine Fin.cases ?_ (fun k => ?_) j
      · exact he
      · exact hpos k
    have hqform (t : Fin (m + 1) → K) : q t = t 0 • q (b 0) := by logtwo_quiet
      calc
        q t = q (∑ j, b.repr t j • b j) := congrArg q (b.sum_repr t).symm
        _ = ∑ j, b.repr t j • q (b j) := by logtwo_quiet simp only [map_sum, map_smul]
        _ = t 0 • q (b 0) := by logtwo_quiet
          rw [Fin.sum_univ_succ]
          simp only [hpos, smul_zero, Finset.sum_const_zero, add_zero]
          simp only [b, Pi.basisFun_repr]
    left
    intro t ht
    rw [hqform] at ht
    exact (smul_eq_zero.mp ht).resolve_right he0

end PiExponent.NormalBasisRigidity

end

end OAI
end Source0088

-- Source: OAI/NumberTheory/PiExponent/Jets/PolynomialTangentDifferential.lean
section Source0089
-- Modified in this edition: unused plain lemmas removed; see reduction.json.
/-
Modification notice for the LogTwo project.
Derived from openai/math (Apache-2.0), revision adc7f1241b42e322a6451854ab7e4b4c146bf78a.
Original source: lean/OAI/NumberTheory/PiExponent/Jets/PolynomialTangentDifferential.lean
Changes: Convert module/import declarations to the Lean 4.34 public module format.
See ../THIRD_PARTY_NOTICES.txt for provenance and the recorded changes.
-/

namespace OAI

noncomputable section

namespace PiExponent

open MvPolynomial KaehlerDifferential

section PolynomialMap
variable {C E ι : Type*} [Field C] [Field E] [Algebra C E] [Fintype ι]

theorem derivation_polynomial_map (φ : MvPolynomial ι C →ₐ[C] E)
    (d : Derivation C E E) (p : MvPolynomial ι C) :
    d (φ p) = ∑ i, φ (pderiv i p) * d (φ (X i)) := by logtwo_quiet
  classical
  induction p using MvPolynomial.induction_on with
  | C a => simp
  | add p q hp hq => simp [hp, hq, add_mul, Finset.sum_add_distrib]
  | mul_X p j hp =>
    simp only [map_mul, Derivation.leibniz, smul_eq_mul, hp,
      map_add, pderiv_X, Finset.sum_add_distrib, add_mul, mul_assoc]
    simp only [← Finset.mul_sum]
    simp [Pi.single_apply, mul_comm]

def polynomialJacobian (φ : MvPolynomial ι C →ₐ[C] E)
    (Q : Ideal (MvPolynomial ι C)) : (ι → E) →ₗ[E] (Q → E) where
  toFun t p := ∑ i, φ (pderiv i p.1) * t i
  map_add' t u := by logtwo_quiet ext p; simp [mul_add, Finset.sum_add_distrib]
  map_smul' a t := by logtwo_quiet ext p; simp [Finset.mul_sum, mul_left_comm]

def polynomialTangent (φ : MvPolynomial ι C →ₐ[C] E)
    (Q : Ideal (MvPolynomial ι C)) : Submodule E (ι → E) :=
  LinearMap.ker (polynomialJacobian φ Q)

abbrev PolynomialNormal (φ : MvPolynomial ι C →ₐ[C] E)
    (Q : Ideal (MvPolynomial ι C)) := (ι → E) ⧸ polynomialTangent φ Q

theorem derivation_mem_polynomialTangent (φ : MvPolynomial ι C →ₐ[C] E)
    (Q : Ideal (MvPolynomial ι C)) (hQ : ∀ p ∈ Q, φ p = 0)
    (d : Derivation C E E) :
    (fun i => d (φ (X i))) ∈ polynomialTangent φ Q := by logtwo_quiet
  change polynomialJacobian φ Q (fun i => d (φ (X i))) = 0
  ext p
  change (∑ i, φ (pderiv i p.1) * d (φ (X i))) = 0
  rw [← derivation_polynomial_map, hQ p.1 p.2, map_zero]

theorem logarithmic_differential_of_polynomialTangent
    (φ : MvPolynomial ι C →ₐ[C] E) (Q : Ideal (MvPolynomial ι C))
    (hQ : ∀ p ∈ Q, φ p = 0) (i j : ι)
    (h : ∀ t ∈ polynomialTangent φ Q, t i = t j / φ (X j)) :
    D C E (φ (X i)) = (φ (X j))⁻¹ • D C E (φ (X j)) := by logtwo_quiet
  apply sub_eq_zero.mp
  apply (Module.forall_dual_apply_eq_zero_iff E _).mp
  intro l
  let d : Derivation C E E := l.compDer (D C E)
  have hd := h (fun i => d (φ (X i))) (derivation_mem_polynomialTangent φ Q hQ d)
  change l (D C E (φ (X i))) = l (D C E (φ (X j))) / φ (X j) at hd
  simpa only [map_sub, map_smul, smul_eq_mul, div_eq_mul_inv,
    sub_eq_zero, mul_comm] using hd

theorem differential_eq_zero_of_polynomialTangent
    (φ : MvPolynomial ι C →ₐ[C] E) (Q : Ideal (MvPolynomial ι C))
    (hQ : ∀ p ∈ Q, φ p = 0) (i : ι)
    (h : ∀ t ∈ polynomialTangent φ Q, t i = 0) :
    D C E (φ (X i)) = 0 := by logtwo_quiet
  apply (Module.forall_dual_apply_eq_zero_iff E _).mp
  intro l
  let d : Derivation C E E := l.compDer (D C E)
  exact h (fun i => d (φ (X i))) (derivation_mem_polynomialTangent φ Q hQ d)

end PolynomialMap

variable {C ι : Type*} [Field C] [Fintype ι]

abbrev PolynomialResidueField (Q : Ideal (MvPolynomial ι C)) [Q.IsPrime] :=
  FractionRing (MvPolynomial ι C ⧸ Q)

def polynomialResidueMap (Q : Ideal (MvPolynomial ι C)) [Q.IsPrime] :
    MvPolynomial ι C →ₐ[C] PolynomialResidueField Q :=
  (IsScalarTower.toAlgHom C (MvPolynomial ι C ⧸ Q) (PolynomialResidueField Q)).comp
    (Ideal.Quotient.mkₐ C Q)

omit [Fintype ι] in

theorem polynomialResidueMap_eq_zero (Q : Ideal (MvPolynomial ι C)) [Q.IsPrime]
    (p : MvPolynomial ι C) (hp : p ∈ Q) : polynomialResidueMap Q p = 0 := by logtwo_quiet
  change algebraMap (MvPolynomial ι C ⧸ Q) (PolynomialResidueField Q)
    (Ideal.Quotient.mk Q p) = 0
  rw [Ideal.Quotient.eq_zero_iff_mem.mpr hp, map_zero]

omit [Fintype ι] in

theorem polynomialResidueMap_eq_zero_iff (Q : Ideal (MvPolynomial ι C)) [Q.IsPrime]
    (p : MvPolynomial ι C) : polynomialResidueMap Q p = 0 ↔ p ∈ Q := by logtwo_quiet
  constructor
  · intro h
    apply Ideal.Quotient.eq_zero_iff_mem.mp
    apply IsFractionRing.injective (MvPolynomial ι C ⧸ Q) (PolynomialResidueField Q)
    change algebraMap (MvPolynomial ι C ⧸ Q) (PolynomialResidueField Q)
      (Ideal.Quotient.mk Q p) = 0 at h
    simpa only [map_zero] using h
  · exact polynomialResidueMap_eq_zero Q p

omit [Fintype ι] in

theorem coordinate_sub_constant_mem_prime
    (Q : Ideal (MvPolynomial ι C)) [Q.IsPrime] (j : ι) (c : C)
    (h : algebraMap C (PolynomialResidueField Q) c = polynomialResidueMap Q (X j)) :
    X j - MvPolynomial.C c ∈ Q := by logtwo_quiet
  apply (polynomialResidueMap_eq_zero_iff Q _).mp
  simp only [map_sub, MvPolynomial.algHom_C, h, sub_self]

end PiExponent

end

end OAI
end Source0089

-- Source: OAI/NumberTheory/PiExponent/Polynomials/PolynomialNormalNonzero.lean
section Source0090
-- Modified in this edition: unused plain lemmas removed; see reduction.json.
/-
Modification notice for the LogTwo project.
Derived from openai/math (Apache-2.0), revision adc7f1241b42e322a6451854ab7e4b4c146bf78a.
Original source: lean/OAI/NumberTheory/PiExponent/Polynomials/PolynomialNormalNonzero.lean
Changes: Convert module/import declarations to the Lean 4.34 public module format.
See ../THIRD_PARTY_NOTICES.txt for provenance and the recorded changes.
-/

namespace OAI

namespace PiExponent

open MvPolynomial

theorem totalDegree_pderiv_lt_of_ne_zero
    {C ι : Type*} [CommSemiring C] (p : MvPolynomial ι C) (i : ι)
    (hp : pderiv i p ≠ 0) : (pderiv i p).totalDegree < p.totalDegree := by logtwo_quiet
  classical
  have hshift (d : ι →₀ ℕ) (hd : d ∈ (pderiv i p).support) :
      d + Finsupp.single i 1 ∈ p.support := by logtwo_quiet
    apply mem_support_iff.mpr
    intro hz
    have hh := mem_support_iff.mp hd
    apply hh
    rw [coeff_pderiv, hz, zero_mul]
  have hdegree (d : ι →₀ ℕ) (hd : d ∈ (pderiv i p).support) :
      d.sum (fun _ e => e) < p.totalDegree := by logtwo_quiet
    have hh := le_totalDegree (hshift d hd)
    have he : (d + Finsupp.single i 1).sum (fun _ e => e) =
        d.sum (fun _ e => e) + 1 := by logtwo_quiet
      rw [Finsupp.sum_add_index']
      · simp
      · intro; rfl
      · intros; rfl
    rw [he] at hh
    omega
  have hpos : 0 < p.totalDegree := by logtwo_quiet
    obtain ⟨d, hd⟩ := (MvPolynomial.support_nonempty.mpr hp)
    exact (Nat.zero_le _).trans_lt (hdegree d hd)
  rw [MvPolynomial.totalDegree, Finset.sup_lt_iff hpos]
  exact hdegree

theorem eq_constant_of_pderiv_eq_zero
    {C ι : Type*} [Field C] [CharZero C] (p : MvPolynomial ι C)
    (hp : ∀ i, pderiv i p = 0) : p = MvPolynomial.C (p.coeff 0) := by logtwo_quiet
  classical
  ext d
  by_cases hd : d = 0
  · subst d
    simp
  · have hex : ∃ i, d i ≠ 0 := by logtwo_quiet
      by_contra! hh
      exact hd (by logtwo_quiet ext i; exact hh i)
    obtain ⟨i, hi⟩ := hex
    have he : d - Finsupp.single i 1 + Finsupp.single i 1 = d :=
      Finsupp.sub_add_single_one_cancel hi
    have hh := congrArg (fun q : MvPolynomial ι C =>
      q.coeff (d - Finsupp.single i 1)) (hp i)
    rw [coeff_pderiv, he] at hh
    simp only [Finsupp.tsub_apply, Finsupp.single_eq_same] at hh
    have hfactor : (((d i - 1 : ℕ) : C) + 1) ≠ 0 := by logtwo_quiet
      simpa only [Nat.cast_add, Nat.cast_one] using
        (Nat.cast_ne_zero.mpr (Nat.succ_ne_zero (d i - 1)) :
          (((d i - 1 + 1 : ℕ) : C)) ≠ 0)
    have hc : p.coeff d = 0 := (mul_eq_zero.mp hh).resolve_right hfactor
    simpa [coeff_C, Ne.symm hd] using hc

theorem ideal_eq_bot_of_pderiv_stable
    {C ι : Type*} [Field C] [CharZero C] (Q : Ideal (MvPolynomial ι C))
    (hproper : Q ≠ ⊤) (hstable : ∀ p ∈ Q, ∀ i, pderiv i p ∈ Q) : Q = ⊥ := by logtwo_quiet
  have hall : ∀ n : ℕ, ∀ p : MvPolynomial ι C,
      p.totalDegree = n → p ∈ Q → p = 0 := by logtwo_quiet
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
      intro p hdegree hp
      have hderiv : ∀ i, pderiv i p = 0 := by logtwo_quiet
        intro i
        by_contra hn
        have hlt := totalDegree_pderiv_lt_of_ne_zero p i hn
        rw [hdegree] at hlt
        exact hn (ih _ hlt _ rfl (hstable p hp i))
      have hc := eq_constant_of_pderiv_eq_zero p hderiv
      have hcoeff : p.coeff 0 = 0 := by logtwo_quiet
        by_contra hne
        have hunit : IsUnit (MvPolynomial.C (p.coeff 0) : MvPolynomial ι C) :=
          (isUnit_iff_ne_zero.mpr hne).map (MvPolynomial.C : C →+* MvPolynomial ι C)
        have hmem : MvPolynomial.C (p.coeff 0) ∈ Q := by logtwo_quiet rw [← hc]; exact hp
        exact hproper (Q.eq_top_of_isUnit_mem hmem hunit)
      simpa [hcoeff] using hc
  apply le_antisymm
  · intro p hp
    exact Ideal.mem_bot.mpr (hall p.totalDegree p rfl hp)
  · exact bot_le

end PiExponent

end OAI
end Source0090

-- Source: OAI/NumberTheory/PiExponent/LocalAlgebra/PrimeNormalRigidity.lean
section Source0091
-- Modified in this edition: unused plain lemmas removed; see reduction.json.
/-
Modification notice for the LogTwo project.
Derived from openai/math (Apache-2.0), revision adc7f1241b42e322a6451854ab7e4b4c146bf78a.
Original source: lean/OAI/NumberTheory/PiExponent/LocalAlgebra/PrimeNormalRigidity.lean
Changes: Convert module/import declarations to the Lean 4.34 public module format.
See ../THIRD_PARTY_NOTICES.txt for provenance and the recorded changes.
-/

namespace OAI

noncomputable section

namespace PiExponent
open Module MvPolynomial NormalBasisRigidity

variable {C : Type*} [Field C] [CharZero C] [IsAlgClosed C] {m : ℕ}

abbrev primeNormalProjection (Q : Ideal (MvPolynomial (Fin (m + 1)) C)) [Q.IsPrime] :=
  (polynomialTangent (polynomialResidueMap Q) Q).mkQ

noncomputable def primeCoordinateNormals
    (Q : Ideal (MvPolynomial (Fin (m + 1)) C)) [Q.IsPrime] :
    Fin (m + 1) → PolynomialNormal (polynomialResidueMap Q) Q :=
  fun i => primeNormalProjection Q (Pi.basisFun (PolynomialResidueField Q) _ i)

noncomputable def primeLogarithmicNormals
    (Q : Ideal (MvPolynomial (Fin (m + 1)) C)) [Q.IsPrime]
    (hy : polynomialResidueMap Q (X (0 : Fin (m + 1))) ≠ 0) :
    Fin (m + 1) → PolynomialNormal (polynomialResidueMap Q) Q :=
  fun i => primeNormalProjection Q
    (frameBasis m (polynomialResidueMap Q (X 0)) hy i)

omit [CharZero C] [IsAlgClosed C] in
theorem constant_coordinate_eq_one_of_center
    (Q : Ideal (MvPolynomial (Fin (m + 1)) C)) (a : Fin (m + 1) → C)
    (ha : a 0 = 1) (hpoint : ∀ p ∈ Q, MvPolynomial.eval a p = 0)
    (hconstant : ∃ c : C, X (0 : Fin (m + 1)) - MvPolynomial.C c ∈ Q) :
    X (0 : Fin (m + 1)) - 1 ∈ Q := by logtwo_quiet
  obtain ⟨c, hc⟩ := hconstant
  have he := hpoint _ hc
  simp only [eval_sub, eval_X, eval_C, ha, sub_eq_zero] at he
  simpa only [← he, map_one] using hc

end PiExponent

end

end OAI
end Source0091

-- Source: OAI/NumberTheory/PiExponent/Approximation/GenericNormalRigidity.lean
section Source0092
/-
Modification notice for the LogTwo project.
Derived from openai/math (Apache-2.0), revision adc7f1241b42e322a6451854ab7e4b4c146bf78a.
Original source: lean/OAI/NumberTheory/PiExponent/Approximation/GenericNormalRigidity.lean
Changes: Convert module/import declarations to the Lean 4.34 public module format.
See ../THIRD_PARTY_NOTICES.txt for provenance and the recorded changes.
-/

namespace OAI

noncomputable section
namespace PiExponent
open Module MvPolynomial NormalBasisRigidity

variable {C E ι : Type*} [Field C] [CharZero C] [Field E] [Algebra C E] [Fintype ι]

theorem polynomialNormal_mkQ_ne_zero_of_kernel
    (φ : MvPolynomial ι C →ₐ[C] E) (Q : Ideal (MvPolynomial ι C))
    (hker : ∀ p, φ p = 0 ↔ p ∈ Q) (hQ : Q ≠ ⊥) :
    (polynomialTangent φ Q).mkQ ≠ 0 := by logtwo_quiet
  classical
  intro hzero
  have htop : polynomialTangent φ Q = ⊤ := by logtwo_quiet
    rw [← Submodule.ker_mkQ (polynomialTangent φ Q), hzero, LinearMap.ker_zero]
  apply hQ
  apply ideal_eq_bot_of_pderiv_stable Q
  · intro h
    have hh := (hker 1).mpr (by logtwo_quiet rw [h]; trivial)
    exact (one_ne_zero : (1 : E) ≠ 0) (by logtwo_quiet simpa only [map_one] using hh)
  · intro p hp i
    apply (hker _).mp
    have ht : (Pi.single i 1 : ι → E) ∈ polynomialTangent φ Q := by logtwo_quiet rw [htop]; trivial
    change polynomialJacobian φ Q (Pi.single i 1) = 0 at ht
    have hh := congrFun ht ⟨p, hp⟩
    simpa [polynomialJacobian, Pi.single_apply] using hh

theorem constant_zeroth_coordinate_of_generic_normal_separation
    [IsAlgClosed C] [Algebra.EssFiniteType C E] {m : ℕ}
    (φ : MvPolynomial (Fin (m + 1)) C →ₐ[C] E)
    (Q : Ideal (MvPolynomial (Fin (m + 1)) C))
    (hker : ∀ p, φ p = 0 ↔ p ∈ Q) (hQ : Q ≠ ⊥)
    (hy : φ (X (0 : Fin (m + 1))) ≠ 0)
    (hexclude : ∀ A B : Finset (Fin (m + 1)),
      IsNormalBasis (K := E)
        (fun j => (polynomialTangent φ Q).mkQ (Pi.basisFun E _ j)) A →
      IsNormalBasis (K := E)
        (fun j => (polynomialTangent φ Q).mkQ (frameBasis m (φ (X 0)) hy j)) B →
      ∀ i, i ≠ 0 → i ∈ A → i ∉ B →
      (∀ j, i < j → (j ∈ A ↔ j ∈ B)) → False) :
    ∃ c : C, X (0 : Fin (m + 1)) - MvPolynomial.C c ∈ Q := by logtwo_quiet
  let q := (polynomialTangent φ Q).mkQ
  have hvan : ∀ p ∈ Q, φ p = 0 := fun p hp => (hker p).mpr hp
  have hd := normal_basis_differential_dichotomy m (φ (X 0)) hy q
    (Submodule.mkQ_surjective _) (polynomialNormal_mkQ_ne_zero_of_kernel φ Q hker hQ) hexclude
  have hconst : ∃ c : C, algebraMap C E c = φ (X (0 : Fin (m + 1))) := by logtwo_quiet
    rcases hd with hzero | ⟨i, hlog⟩
    · exact constant_of_differential_eq_zero (φ (X 0))
        (differential_eq_zero_of_polynomialTangent φ Q hvan 0
          (fun t ht => hzero t ((Submodule.Quotient.mk_eq_zero _).mpr ht)))
    · exact constant_of_logarithmic_differential (φ (X i.succ)) (φ (X 0))
        (logarithmic_differential_of_polynomialTangent φ Q hvan i.succ 0
          (fun t ht => hlog t ((Submodule.Quotient.mk_eq_zero _).mpr ht)))
  obtain ⟨c, hc⟩ := hconst
  refine ⟨c, (hker _).mp ?_⟩
  simp only [map_sub, MvPolynomial.algHom_C, hc, sub_self]

end PiExponent

end

end OAI
end Source0092

-- Source: OAI/NumberTheory/PiExponent/Geometry/CurveContact.lean
section Source0093
-- Modified in this edition: unused plain lemmas removed; see reduction.json.
/-
Modification notice for the LogTwo project.
Derived from openai/math (Apache-2.0), revision adc7f1241b42e322a6451854ab7e4b4c146bf78a.
Original source: lean/OAI/NumberTheory/PiExponent/Geometry/CurveContact.lean
Changes: Convert module/import declarations to the Lean 4.34 public module format.
See ../THIRD_PARTY_NOTICES.txt for provenance and the recorded changes.
-/

namespace OAI

namespace PiExponentApprox

noncomputable section

def frameWordCost {m : ℕ} (cost : Fin (m + 1) → ℝ)
    (word : List (Fin (m + 1))) : ℝ := (word.map cost).sum

@[simp] theorem frameWordCost_nil {m : ℕ} (cost : Fin (m + 1) → ℝ) :
    frameWordCost cost [] = 0 := rfl

@[simp] theorem frameWordCost_cons {m : ℕ} (cost : Fin (m + 1) → ℝ)
    (i : Fin (m + 1)) (word : List (Fin (m + 1))) :
    frameWordCost cost (i :: word) = cost i + frameWordCost cost word := rfl

def frameDerivativeIdeal {m : ℕ} (cost : Fin (m + 1) → ℝ)
    (bound : ℝ) (F : FramePolynomial m) : Ideal (FramePolynomial m) :=
  Ideal.span {g | ∃ word, frameWordCost cost word ≤ bound ∧
    polynomialFrameWord m word F = g}

theorem frameWord_mem_derivativeIdeal {m : ℕ} (cost : Fin (m + 1) → ℝ)
    (bound : ℝ) (F : FramePolynomial m) (word : List (Fin (m + 1)))
    (hword : frameWordCost cost word ≤ bound) :
    polynomialFrameWord m word F ∈ frameDerivativeIdeal cost bound F :=
  Ideal.subset_span ⟨word, hword, rfl⟩

theorem frameDerivativeIdeal_mono {m : ℕ} (cost : Fin (m + 1) → ℝ)
    (F : FramePolynomial m) {a b : ℝ} (hab : a ≤ b) :
    frameDerivativeIdeal cost a F ≤ frameDerivativeIdeal cost b F := by logtwo_quiet
  apply Ideal.span_mono
  intro g hg
  obtain ⟨word, hword, rfl⟩ := hg
  exact ⟨word, hword.trans hab, rfl⟩

theorem polynomial_mem_frameDerivativeIdeal {m : ℕ}
    (cost : Fin (m + 1) → ℝ) (bound : ℝ) (F : FramePolynomial m)
    (hbound : 0 ≤ bound) : F ∈ frameDerivativeIdeal cost bound F :=
  frameWord_mem_derivativeIdeal cost bound F [] hbound

def polynomialDerivativeCore {m : ℕ}
    (D : Derivation ℂ (FramePolynomial m) (FramePolynomial m))
    (I : Ideal (FramePolynomial m)) : Ideal (FramePolynomial m) where
  carrier := {p | p ∈ I ∧ D p ∈ I}
  zero_mem' := by logtwo_quiet simp only [Set.mem_ofPred_eq, D.map_zero]; exact ⟨I.zero_mem, I.zero_mem⟩
  add_mem' := by logtwo_quiet
    intro p q hp hq
    refine ⟨I.add_mem hp.1 hq.1, ?_⟩
    rw [map_add]
    exact I.add_mem hp.2 hq.2
  smul_mem' := by logtwo_quiet
    intro r p hp
    change r * p ∈ I ∧ D (r * p) ∈ I
    refine ⟨I.mul_mem_left r hp.1, ?_⟩
    rw [Derivation.leibniz]
    exact I.add_mem (I.mul_mem_left r hp.2) (by logtwo_quiet
      simpa only [smul_eq_mul, mul_comm] using I.mul_mem_left (D r) hp.1)

theorem polynomialFrame_mem_derivativeIdeal {m : ℕ}
    (cost : Fin (m + 1) → ℝ) (hcost : ∀ i, 0 ≤ cost i)
    (bound : ℝ) (F p : FramePolynomial m) (i : Fin (m + 1))
    (hp : p ∈ frameDerivativeIdeal cost bound F) :
    polynomialFrame m i p ∈ frameDerivativeIdeal cost (bound + cost i) F := by logtwo_quiet
  let I := frameDerivativeIdeal cost (bound + cost i) F
  have hle : frameDerivativeIdeal cost bound F ≤
      polynomialDerivativeCore (polynomialFrame m i) I := by logtwo_quiet
    apply Ideal.span_le.mpr
    intro g hg
    obtain ⟨word, hword, rfl⟩ := hg
    refine ⟨?_, ?_⟩
    · exact frameWord_mem_derivativeIdeal cost (bound + cost i) F word
        (hword.trans (le_add_of_nonneg_right (hcost i)))
    · exact frameWord_mem_derivativeIdeal cost (bound + cost i) F (i :: word)
        (by logtwo_quiet simpa only [frameWordCost_cons, add_comm] using add_le_add_left hword (cost i))
  exact (hle hp).2

theorem polynomialFrameWord_mem_derivativeIdeal {m : ℕ}
    (cost : Fin (m + 1) → ℝ) (hcost : ∀ i, 0 ≤ cost i)
    (bound : ℝ) (F p : FramePolynomial m) (word : List (Fin (m + 1)))
    (hp : p ∈ frameDerivativeIdeal cost bound F) :
    polynomialFrameWord m word p ∈
      frameDerivativeIdeal cost (bound + frameWordCost cost word) F := by logtwo_quiet
  induction word with
  | nil => simpa only [polynomialFrameWord_nil, frameWordCost_nil, add_zero] using hp
  | cons i word ih =>
      have h := polynomialFrame_mem_derivativeIdeal cost hcost
        (bound + frameWordCost cost word) F (polynomialFrameWord m word p) i ih
      simpa only [polynomialFrameWord_cons, frameWordCost_cons, add_assoc,
        add_comm (frameWordCost cost word) (cost i)] using h

theorem derivative_vanishes_on_persistent_ideal {m : ℕ}
    (cost : Fin (m + 1) → ℝ) (hcost : ∀ i, 0 ≤ cost i)
    (bound delta : ℝ) (F p : FramePolynomial m)
    (P : Ideal (FramePolynomial m))
    (hp : p ∈ frameDerivativeIdeal cost bound F)
    (hpersist : frameDerivativeIdeal cost (bound + delta) F ≤ P)
    (word : List (Fin (m + 1))) (hword : frameWordCost cost word ≤ delta) :
    polynomialFrameWord m word p ∈ P := by logtwo_quiet
  apply hpersist
  have hbound : bound + frameWordCost cost word ≤ bound + delta := by logtwo_quiet linarith
  exact frameDerivativeIdeal_mono cost F hbound
    (polynomialFrameWord_mem_derivativeIdeal cost hcost bound F p word hp)

theorem frameDerivativeIdeal_levels_monotone {m : ℕ}
    (cost : Fin (m + 1) → ℝ) (delta : ℝ) (hdelta : 0 ≤ delta)
    (F : FramePolynomial m) :
    Monotone (fun r : ℕ => frameDerivativeIdeal cost ((r : ℝ) * delta) F) := by logtwo_quiet
  intro a b hab
  apply frameDerivativeIdeal_mono
  exact mul_le_mul_of_nonneg_right (Nat.cast_le.mpr hab) hdelta

theorem exists_persistent_frame_component {m : ℕ}
    (cost : Fin (m + 1) → ℝ) (hcost : ∀ i, 0 ≤ cost i)
    (delta : ℝ) (hdelta : 0 ≤ delta) (F : FramePolynomial m) (hF : F ≠ 0)
    (P : Ideal (FramePolynomial m)) (hP : P.IsPrime) (hheight : P.height ≤ m)
    (hvanish : ∀ word : List (Fin (m + 1)),
      frameWordCost cost word ≤ ((m : ℝ) + 2) * delta →
        polynomialFrameWord m word F ∈ P) :
    ∃ r < m + 2, ∃ Q : Ideal (FramePolynomial m),
      Q ∈ (frameDerivativeIdeal cost ((r : ℝ) * delta) F).minimalPrimes ∧
      Q ∈ (frameDerivativeIdeal cost (((r : ℝ) + 1) * delta) F).minimalPrimes ∧
      Q ≤ P ∧ 1 ≤ Q.height ∧ Q.height ≤ m ∧
      ∀ p ∈ frameDerivativeIdeal cost ((r : ℝ) * delta) F,
        ∀ word : List (Fin (m + 1)), frameWordCost cost word ≤ delta →
          polynomialFrameWord m word p ∈ Q := by logtwo_quiet
  let I : ℕ → Ideal (FramePolynomial m) :=
    fun r => frameDerivativeIdeal cost ((r : ℝ) * delta) F
  have hI : Monotone I := frameDerivativeIdeal_levels_monotone cost delta hdelta F
  have htop : I (m + 2) ≤ P := by logtwo_quiet
    apply Ideal.span_le.mpr
    intro g hg
    obtain ⟨word, hword, rfl⟩ := hg
    apply hvanish word
    simpa only [Nat.cast_add, Nat.cast_ofNat] using hword
  have hinitial : F ∈ I 0 := by logtwo_quiet
    simpa only [I, Nat.cast_zero, zero_mul] using
      polynomial_mem_frameDerivativeIdeal cost 0 F (le_refl 0)
  obtain ⟨r, hr, Q, hQr, hQnext, hQP, hQlo, hQhi⟩ :=
    PiExponent.PersistentComponents.exists_persistent_component_positive_height
      I hI m P hP htop hheight hF hinitial
  refine ⟨r, hr, Q, hQr, ?_, hQP, hQlo, hQhi, ?_⟩
  · simpa only [I, Nat.cast_add, Nat.cast_one] using hQnext
  · intro p hp word hword
    apply derivative_vanishes_on_persistent_ideal cost hcost
      ((r : ℝ) * delta) delta F p Q hp
    · have hb : (r : ℝ) * delta + delta = ((r + 1 : ℕ) : ℝ) * delta := by logtwo_quiet
        push_cast
        ring
      rw [hb]
      exact hQnext.le
    · exact hword

end
end PiExponentApprox

end OAI
end Source0093

-- Source: OAI/NumberTheory/PiExponent/Jets/ConormalPairing.lean
section Source0094
/-
Modification notice for the LogTwo project.
Derived from openai/math (Apache-2.0), revision adc7f1241b42e322a6451854ab7e4b4c146bf78a.
Original source: lean/OAI/NumberTheory/PiExponent/Jets/ConormalPairing.lean
Changes: Convert module/import declarations to the Lean 4.34 public module format.
See ../THIRD_PARTY_NOTICES.txt for provenance and the recorded changes.
-/

namespace OAI

noncomputable section
namespace PiExponentSiegel.W58

variable {K R : Type*} [CommRing K] [CommRing R] [Algebra K R]
variable (I : Ideal R) (D : Derivation K R (R ⧸ I))

theorem ideal_smul_quotient_zero (x : I) (z : R ⧸ I) : (x : R) • z = 0 := by logtwo_quiet
  rw [Algebra.smul_def]
  change Ideal.Quotient.mk I (x : R) * z = 0
  rw [Ideal.Quotient.eq_zero_iff_mem.mpr x.property, zero_mul]

def normalRestriction : I →ₗ[R] R ⧸ I where
  toFun x := D x
  map_add' x y := D.map_add x y
  map_smul' r x := by logtwo_quiet
    change D (r * (x : R)) = r • D (x : R)
    rw [D.leibniz, ideal_smul_quotient_zero I x, add_zero]

theorem normalRestriction_product_zero (x y : I) : normalRestriction I D (x * y) = 0 := by logtwo_quiet
  change D ((x : R) * (y : R)) = 0
  rw [D.leibniz, ideal_smul_quotient_zero I x, ideal_smul_quotient_zero I y, add_zero]

def conormalPairing : I.Cotangent →ₗ[R] R ⧸ I :=
  Ideal.Cotangent.lift (normalRestriction I D) (normalRestriction_product_zero I D)

@[simp] theorem conormalPairing_toCotangent (x : I) :
    conormalPairing I D (I.toCotangent x) = D x := rfl

end PiExponentSiegel.W58

end

end OAI
end Source0094

-- Source: OAI/NumberTheory/PiExponent/Jets/ResidueConormalPairing.lean
section Source0095
-- Modified in this edition: unused plain lemmas removed; see reduction.json.
/-
Modification notice for the LogTwo project.
Derived from openai/math (Apache-2.0), revision adc7f1241b42e322a6451854ab7e4b4c146bf78a.
Original source: lean/OAI/NumberTheory/PiExponent/Jets/ResidueConormalPairing.lean
Changes: Convert module/import declarations to the Lean 4.34 public module format.
See ../THIRD_PARTY_NOTICES.txt for provenance and the recorded changes.
-/

namespace OAI

noncomputable section
namespace PiExponentSiegel.W58

variable {K R : Type*} [CommRing K] [CommRing R] [Algebra K R]
variable (I : Ideal R) (D : Derivation K R (R ⧸ I))

instance cotangentQuotientScalarTower : IsScalarTower R (R ⧸ I) I.Cotangent :=
  inferInstance

def residueConormalPairing : I.Cotangent →ₗ[R ⧸ I] R ⧸ I :=
  (conormalPairing I D).extendScalarsOfSurjective
    (show Function.Surjective (algebraMap R (R ⧸ I)) from Ideal.Quotient.mk_surjective)

@[simp] theorem residueConormalPairing_apply (x : I.Cotangent) :
    residueConormalPairing I D x = conormalPairing I D x := rfl

@[simp] theorem residueConormalPairing_toCotangent (x : I) :
    residueConormalPairing I D (I.toCotangent x) = D x := rfl

def reducedDerivation (D₀ : Derivation K R R) : Derivation K R (R ⧸ I) :=
  (Ideal.Quotient.mkₐ R I).toLinearMap.compDer D₀

@[simp] theorem reducedDerivation_apply (D₀ : Derivation K R R) (x : R) :
    reducedDerivation I D₀ x = Ideal.Quotient.mk I (D₀ x) := rfl

def derivationNormal (D₀ : Derivation K R R) : I.Cotangent →ₗ[R ⧸ I] R ⧸ I :=
  residueConormalPairing I (reducedDerivation I D₀)

@[simp] theorem derivationNormal_toCotangent (D₀ : Derivation K R R) (x : I) :
    derivationNormal I D₀ (I.toCotangent x) = Ideal.Quotient.mk I (D₀ x) := rfl

end PiExponentSiegel.W58

end

end OAI
end Source0095

-- Source: OAI/NumberTheory/PiExponent/Jets/PrimeNormalCotangent.lean
section Source0096
/-
Modification notice for the LogTwo project.
Derived from openai/math (Apache-2.0), revision adc7f1241b42e322a6451854ab7e4b4c146bf78a.
Original source: lean/OAI/NumberTheory/PiExponent/Jets/PrimeNormalCotangent.lean
Changes: Convert module/import declarations to the Lean 4.34 public module format.
See ../THIRD_PARTY_NOTICES.txt for provenance and the recorded changes.
-/

namespace OAI

noncomputable section

namespace PiExponent

open KaehlerDifferential
open scoped TensorProduct

def extendModuleDerivation
    {C R A E : Type*} [CommRing C] [CommRing R] [CommRing A] [CommRing E]
    [Algebra C R] [Algebra C A] [Algebra C E]
    [Algebra R A] [Algebra R E] [Algebra A E]
    [IsScalarTower C R A] [IsScalarTower C R E] [IsScalarTower C A E]
    [IsScalarTower R A E] [Algebra.FormallyEtale R A]
    (d : Derivation C R E) : Derivation C A E :=
  ((LinearMap.liftBaseChange A d.liftKaehlerDifferential).comp
    (tensorKaehlerEquivOfFormallyEtale C R A).symm.toLinearMap).compDer (D C A)

@[simp]
theorem extendModuleDerivation_algebraMap
    {C R A E : Type*} [CommRing C] [CommRing R] [CommRing A] [CommRing E]
    [Algebra C R] [Algebra C A] [Algebra C E]
    [Algebra R A] [Algebra R E] [Algebra A E]
    [IsScalarTower C R A] [IsScalarTower C R E] [IsScalarTower C A E]
    [IsScalarTower R A E] [Algebra.FormallyEtale R A]
    (d : Derivation C R E) (r : R) :
    extendModuleDerivation (A := A) d (algebraMap R A r) = d r := by logtwo_quiet
  simp [extendModuleDerivation, LinearMap.compDer,
    tensorKaehlerEquivOfFormallyEtale_symm_D_algebraMap,
    Derivation.liftKaehlerDifferential_comp_D]

variable {C ι : Type*} [Field C] [Fintype ι]
variable (Q : Ideal (MvPolynomial ι C)) [Q.IsPrime]

abbrev PrimeLocalCotangent := IsLocalRing.CotangentSpace (Localization.AtPrime Q)

def primeResidueMap : MvPolynomial ι C →ₐ[C] Q.ResidueField :=
  IsScalarTower.toAlgHom C (MvPolynomial ι C) Q.ResidueField

def primeLocalPartial (i : ι) : Derivation C (Localization.AtPrime Q) Q.ResidueField := by logtwo_quiet
  let : Algebra.FormallyEtale (MvPolynomial ι C) (Localization.AtPrime Q) :=
    Algebra.FormallyEtale.of_isLocalization Q.primeCompl
  exact extendModuleDerivation
    ((Algebra.linearMap (MvPolynomial ι C) Q.ResidueField).compDer (MvPolynomial.pderiv i))

omit [Fintype ι] in
@[simp]
theorem primeLocalPartial_polynomial (i : ι) (p : MvPolynomial ι C) :
    primeLocalPartial Q i (algebraMap (MvPolynomial ι C) (Localization.AtPrime Q) p) =
      algebraMap (MvPolynomial ι C) Q.ResidueField (MvPolynomial.pderiv i p) := by logtwo_quiet
  let : Algebra.FormallyEtale (MvPolynomial ι C) (Localization.AtPrime Q) :=
    Algebra.FormallyEtale.of_isLocalization Q.primeCompl
  change extendModuleDerivation _ (algebraMap (MvPolynomial ι C) (Localization.AtPrime Q) p) = _
  rw [extendModuleDerivation_algebraMap]
  rfl

def primePartialNormal (i : ι) : PrimeLocalCotangent Q →ₗ[Q.ResidueField] Q.ResidueField :=
  PiExponentSiegel.W58.residueConormalPairing
    (IsLocalRing.maximalIdeal (Localization.AtPrime Q)) (primeLocalPartial Q i)

def primeNormalPairing : (ι → Q.ResidueField) →ₗ[Q.ResidueField]
    (PrimeLocalCotangent Q →ₗ[Q.ResidueField] Q.ResidueField) where
  toFun v := ∑ i, v i • primePartialNormal Q i
  map_add' v w := by logtwo_quiet simp [add_smul, Finset.sum_add_distrib]
  map_smul' c v := by logtwo_quiet simp [Finset.smul_sum, smul_smul]

def primePolynomialCotangent (p : Q) : PrimeLocalCotangent Q :=
  (IsLocalRing.maximalIdeal (Localization.AtPrime Q)).toCotangent
    ⟨algebraMap (MvPolynomial ι C) (Localization.AtPrime Q) p.1,
      (IsLocalization.AtPrime.to_map_mem_maximal_iff (Localization.AtPrime Q) Q p.1).mpr p.2⟩

@[simp]
theorem primeNormalPairing_polynomial (v : ι → Q.ResidueField) (p : Q) :
    primeNormalPairing Q v (primePolynomialCotangent Q p) =
      ∑ i, v i * primeResidueMap Q (MvPolynomial.pderiv i p.1) := by logtwo_quiet
  change (∑ i, v i • primePartialNormal Q i) (primePolynomialCotangent Q p) = _
  rw [LinearMap.sum_apply]
  apply Finset.sum_congr rfl
  intro i _
  change v i * primeLocalPartial Q i
    (algebraMap (MvPolynomial ι C) (Localization.AtPrime Q) p.1) = _
  rw [primeLocalPartial_polynomial]
  rfl

theorem primeNormalPairing_ker_le_tangent :
    LinearMap.ker (primeNormalPairing Q) ≤ polynomialTangent (primeResidueMap Q) Q := by logtwo_quiet
  intro v hv
  change primeNormalPairing Q v = 0 at hv
  change polynomialJacobian (primeResidueMap Q) Q v = 0
  ext p
  have h := LinearMap.congr_fun hv (primePolynomialCotangent Q p)
  simpa only [primeNormalPairing_polynomial, LinearMap.zero_apply,
    polynomialJacobian, LinearMap.coe_mk, AddHom.coe_mk, Pi.zero_apply, mul_comm] using h

def primeLocalDirectional (v : ι → Q.ResidueField) :
    Derivation C (Localization.AtPrime Q) Q.ResidueField :=
  ∑ i, v i • primeLocalPartial Q i

@[simp]
theorem primeNormalPairing_toCotangent (v : ι → Q.ResidueField)
    (x : IsLocalRing.maximalIdeal (Localization.AtPrime Q)) :
    primeNormalPairing Q v ((IsLocalRing.maximalIdeal (Localization.AtPrime Q)).toCotangent x) =
      primeLocalDirectional Q v x := by logtwo_quiet
  change (∑ i, v i • primePartialNormal Q i) _ = _
  rw [LinearMap.sum_apply]
  change (∑ i, v i * primeLocalPartial Q i x.1) = _
  change (∑ i, v i * primeLocalPartial Q i x.1) =
    (Derivation.coeFnAddMonoidHom (∑ i, v i • primeLocalPartial Q i)) x.1
  rw [map_sum, Finset.sum_apply]
  rfl

theorem primeNormalPairing_linearIndependent {σ : Type*} [Fintype σ]
    (v : σ → ι → Q.ResidueField)
    (hv : LinearIndependent Q.ResidueField
      (fun j => (polynomialTangent (primeResidueMap Q) Q).mkQ (v j))) :
    LinearIndependent Q.ResidueField (fun j => primeNormalPairing Q (v j)) := by logtwo_quiet
  classical
  apply Fintype.linearIndependent_iff.mpr
  intro a ha j
  have hp : primeNormalPairing Q (∑ j, a j • v j) = 0 := by logtwo_quiet
    simpa only [map_sum, map_smul] using ha
  have hm := primeNormalPairing_ker_le_tangent Q hp
  have hq : (polynomialTangent (primeResidueMap Q) Q).mkQ (∑ j, a j • v j) = 0 :=
    (Submodule.Quotient.mk_eq_zero _).mpr hm
  have hsum : ∑ j, a j • (polynomialTangent (primeResidueMap Q) Q).mkQ (v j) = 0 := by logtwo_quiet
    simpa only [map_sum, map_smul] using hq
  exact Fintype.linearIndependent_iff.mp hv a hsum j

theorem prime_cotangent_evaluation_surjective {σ : Type*} [Fintype σ]
    (v : σ → ι → Q.ResidueField)
    (hv : LinearIndependent Q.ResidueField
      (fun j => (polynomialTangent (primeResidueMap Q) Q).mkQ (v j))) :
    Function.Surjective
      (fun x : PrimeLocalCotangent Q => fun j => primeNormalPairing Q (v j) x) := by logtwo_quiet
  classical
  let f := fun j => primeNormalPairing Q (v j)
  have hf : LinearIndependent Q.ResidueField f := primeNormalPairing_linearIndependent Q v hv
  intro a
  obtain ⟨g, hg⟩ := LinearMap.dualMap_surjective_of_injective
    hf.finsuppLinearCombination_injective (Finsupp.linearCombination Q.ResidueField a)
  refine ⟨(Module.evalEquiv Q.ResidueField (PrimeLocalCotangent Q)).symm g, ?_⟩
  funext j
  change f j ((Module.evalEquiv Q.ResidueField (PrimeLocalCotangent Q)).symm g) = a j
  rw [Module.apply_evalEquiv_symm_apply]
  have hj := LinearMap.congr_fun hg (Finsupp.single j (1 : Q.ResidueField))
  simpa only [LinearMap.dualMap_apply, Finsupp.linearCombination_single, one_smul] using hj

end PiExponent

end

end OAI
end Source0096

-- Source: OAI/NumberTheory/PiExponent/Geometry/CurveComponentRigidity.lean
section Source0097
-- Modified in this edition: unused plain lemmas removed; see reduction.json.
/-
Modification notice for the LogTwo project.
Derived from openai/math (Apache-2.0), revision adc7f1241b42e322a6451854ab7e4b4c146bf78a.
Original source: lean/OAI/NumberTheory/PiExponent/Geometry/CurveComponentRigidity.lean
Changes: Convert module/import declarations to the Lean 4.34 public module format.
See ../THIRD_PARTY_NOTICES.txt for provenance and the recorded changes.
-/

namespace OAI

noncomputable section
namespace PiExponent.CurveComponentRigidity

open scoped BigOperators
open PiExponentApprox NormalBasisRigidity

theorem residueY_ne_zero {m : ℕ} (Q : Ideal (FramePolynomial m)) [Q.IsPrime]
    (hY : MvPolynomial.X (0 : Fin (m + 1)) ∉ Q) :
    primeResidueMap Q (MvPolynomial.X (0 : Fin (m + 1))) ≠ 0 := by logtwo_quiet
  intro h
  exact hY (Ideal.algebraMap_residueField_eq_zero.mp h)

def NormalProductComparison {m : ℕ} (Q : Ideal (FramePolynomial m)) [Q.IsPrime]
    (hY : MvPolynomial.X (0 : Fin (m + 1)) ∉ Q)
    (w cost : Fin (m + 1) → ℝ) (M : ℝ) : Prop :=
  ∀ A B : Finset (Fin (m + 1)),
    IsNormalBasis (K := Q.ResidueField)
      (fun j => (polynomialTangent (primeResidueMap Q) Q).mkQ
        (Pi.basisFun Q.ResidueField _ j)) A →
    IsNormalBasis (K := Q.ResidueField)
      (fun j => (polynomialTangent (primeResidueMap Q) Q).mkQ
        (frameBasis m (primeResidueMap Q (MvPolynomial.X 0)) (residueY_ne_zero Q hY) j)) B →
    (∏ j ∈ A, w j) ≤ M * ∏ j ∈ B, cost j

def PersistentNormalComparison {m : ℕ} (w cost : Fin (m + 1) → ℝ)
    (M delta : ℝ) (F : FramePolynomial m) (P : Ideal (FramePolynomial m))
    (hY : MvPolynomial.X (0 : Fin (m + 1)) ∉ P) : Prop :=
  ∀ r : ℕ, r < m + 2 → ∀ Q : Ideal (FramePolynomial m), ∀ hQ : Q.IsPrime,
    ∀ hQP : Q ≤ P,
    Q ∈ (frameDerivativeIdeal cost ((r : ℝ) * delta) F).minimalPrimes →
    Q ∈ (frameDerivativeIdeal cost (((r : ℝ) + 1) * delta) F).minimalPrimes →
    1 ≤ Q.height → Q.height ≤ m →
    (∀ p ∈ frameDerivativeIdeal cost ((r : ℝ) * delta) F,
      ∀ word : List (Fin (m + 1)), frameWordCost cost word ≤ delta →
        polynomialFrameWord m word p ∈ Q) →
    @NormalProductComparison m Q hQ (fun h => hY (hQP h)) w cost M

theorem coordinate_constant_of_persistent_comparison {m : ℕ}
    (w cost : Fin (m + 1) → ℝ) (M delta : ℝ)
    (hcost : ∀ i, 0 ≤ cost i) (hdelta : 0 ≤ delta)
    (F : FramePolynomial m) (hF : F ≠ 0)
    (P : Ideal (FramePolynomial m)) (hP : P.IsPrime) (hheight : P.height ≤ m)
    (hY : MvPolynomial.X (0 : Fin (m + 1)) ∉ P)
    (hvanish : ∀ word : List (Fin (m + 1)),
      frameWordCost cost word ≤ ((m : ℝ) + 2) * delta → polynomialFrameWord m word F ∈ P)
    (hcomparison : PersistentNormalComparison w cost M delta F P hY)
    (hseparated : ∀ A B : Finset (Fin (m + 1)), A.card = B.card →
      ∀ i, i ≠ 0 → i ∈ A → i ∉ B →
      (∀ j, i < j → (j ∈ A ↔ j ∈ B)) →
      M * (∏ j ∈ B, cost j) < ∏ j ∈ A, w j) :
    ∃ c : ℂ, MvPolynomial.X (0 : Fin (m + 1)) - MvPolynomial.C c ∈ P := by logtwo_quiet
  obtain ⟨r, hr, Q, hQr, hQnext, hQP, hQlo, hQhi, hpersist⟩ :=
    exists_persistent_frame_component cost hcost delta hdelta F hF P hP hheight hvanish
  let : Q.IsPrime := hQr.isPrime
  have hYQ : MvPolynomial.X (0 : Fin (m + 1)) ∉ Q := fun h => hY (hQP h)
  have hFQ : F ∈ Q := hQr.le
    (polynomial_mem_frameDerivativeIdeal cost ((r : ℝ) * delta) F
      (mul_nonneg (Nat.cast_nonneg r) hdelta))
  have hQ0 : Q ≠ ⊥ := by logtwo_quiet
    intro h
    exact hF (by logtwo_quiet simpa only [h, Ideal.mem_bot] using hFQ)
  have hcomp := hcomparison r hr Q inferInstance hQP hQr hQnext hQlo hQhi hpersist
  let : Algebra.EssFiniteType ℂ Q.ResidueField :=
    Algebra.EssFiniteType.comp ℂ (FramePolynomial m) Q.ResidueField
  have hker (p : FramePolynomial m) : primeResidueMap Q p = 0 ↔ p ∈ Q :=
    Ideal.algebraMap_residueField_eq_zero
  obtain ⟨c, hc⟩ := constant_zeroth_coordinate_of_generic_normal_separation
    (primeResidueMap Q) Q hker hQ0 (residueY_ne_zero Q hYQ)
    (weighted_normalBasis_exclusion _ _ w cost M hcomp hseparated)
  exact ⟨c, hQP hc⟩

end PiExponent.CurveComponentRigidity
end

end OAI
end Source0097

-- Source: OAI/NumberTheory/PiExponent/Approximation/RectangularVolume.lean
section Source0098
-- Modified in this edition: unused plain lemmas removed; see reduction.json.
/-
Modification notice for the LogTwo project.
Derived from openai/math (Apache-2.0), revision adc7f1241b42e322a6451854ab7e4b4c146bf78a.
Original source: lean/OAI/NumberTheory/PiExponent/Approximation/RectangularVolume.lean
Changes: Convert module/import declarations to the Lean 4.34 public module format.
See ../THIRD_PARTY_NOTICES.txt for provenance and the recorded changes.
-/

namespace OAI

open scoped BigOperators

namespace PiExponent

noncomputable def rectangularCutoff {k : ℕ} (κ : Fin k → ℝ) (T : ℝ) (i : Fin k) : ℕ :=
  ⌈T / ((k : ℝ) * κ i)⌉₊

theorem rectangularCutoff_pos {k : ℕ} (hk : 0 < k) (κ : Fin k → ℝ)
    (hκ : ∀ i, 0 < κ i) {T : ℝ} (hT : 0 < T) (i : Fin k) :
    0 < rectangularCutoff κ T i := by logtwo_quiet
  apply Nat.lt_ceil.mpr
  simpa only [Nat.cast_zero] using
    div_pos hT (mul_pos (by logtwo_quiet exact_mod_cast hk) (hκ i))

theorem two_le_rectangularCutoff {k : ℕ} (hk : 0 < k) (κ : Fin k → ℝ)
    (hκ : ∀ i, 0 < κ i) {T : ℝ} (i : Fin k)
    (hT : (k : ℝ) * κ i < T) :
    2 ≤ rectangularCutoff κ T i := by logtwo_quiet
  have hd : 0 < (k : ℝ) * κ i :=
    mul_pos (by logtwo_quiet exact_mod_cast hk) (hκ i)
  have h : (1 : ℝ) < T / ((k : ℝ) * κ i) :=
    (lt_div_iff₀ hd).mpr (by logtwo_quiet simpa using hT)
  exact Nat.lt_ceil.mpr (by logtwo_quiet simpa using h)

theorem rectangularCutoff_coordinate_weight_lt {k : ℕ} (hk : 0 < k)
    (κ : Fin k → ℝ) (hκ : ∀ i, 0 < κ i) {T : ℝ}
    (β : Fin k → ℕ) (hβ : ∀ i, β i < rectangularCutoff κ T i) (i : Fin k) :
    κ i * (β i : ℝ) < T / (k : ℝ) := by logtwo_quiet
  have hkR : (0 : ℝ) < k := by logtwo_quiet exact_mod_cast hk
  have hb : (β i : ℝ) < T / ((k : ℝ) * κ i) := Nat.lt_ceil.mp (hβ i)
  have h := mul_lt_mul_of_pos_left hb (hκ i)
  have he : κ i * (T / ((k : ℝ) * κ i)) = T / (k : ℝ) := by logtwo_quiet
    field_simp [(hκ i).ne']
  simpa only [he] using h

theorem rectangularCutoff_weight_lt {k : ℕ} (hk : 0 < k)
    (κ : Fin k → ℝ) (hκ : ∀ i, 0 < κ i) {T : ℝ}
    (β : Fin k → ℕ) (hβ : ∀ i, β i < rectangularCutoff κ T i) :
    (∑ i, κ i * (β i : ℝ)) < T := by logtwo_quiet
  have hkR : (0 : ℝ) < k := by logtwo_quiet exact_mod_cast hk
  have hsum : (∑ i, κ i * (β i : ℝ)) < ∑ _i : Fin k, T / (k : ℝ) := by logtwo_quiet
    apply Finset.sum_lt_sum
    · intro i hi
      exact (rectangularCutoff_coordinate_weight_lt hk κ hκ β hβ i).le
    · exact ⟨⟨0, hk⟩, Finset.mem_univ _,
        rectangularCutoff_coordinate_weight_lt hk κ hκ β hβ ⟨0, hk⟩⟩
  have he : (∑ _i : Fin k, T / (k : ℝ)) = T := by logtwo_quiet
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    field_simp [hkR.ne']
  simpa only [he] using hsum

theorem rectangularCutoff_product_lower {k : ℕ} (hk : 0 < k)
    (κ : Fin k → ℝ) (hκ : ∀ i, 0 < κ i) {T : ℝ} (hT : 0 < T) :
    T ^ k / ((k : ℝ) ^ k * ∏ i, κ i) ≤
      ∏ i, (rectangularCutoff κ T i : ℝ) := by logtwo_quiet
  have hkR : (0 : ℝ) < k := by logtwo_quiet exact_mod_cast hk
  have hp : (∏ i, T / ((k : ℝ) * κ i)) ≤
      ∏ i, (rectangularCutoff κ T i : ℝ) := by logtwo_quiet
    apply Finset.prod_le_prod₀
    · intro i hi
      exact (div_pos hT (mul_pos hkR (hκ i))).le
    · intro i hi
      exact Nat.le_ceil _
  simpa only [Finset.prod_div_distrib, Finset.prod_mul_distrib, Finset.prod_const,
    Finset.card_univ, Fintype.card_fin] using hp

end PiExponent

end OAI
end Source0098

-- Source: LogTwo/Geometry/PersistentRigidity.lean
section Source0099
-- Modified in this edition: unused plain lemmas removed; see reduction.json.
/-
Modification notice for the LogTwo project.
Adapted from openai/math (Apache-2.0), revision adc7f1241b42e322a6451854ab7e4b4c146bf78a.
Changes: Adapt the logarithmic rigidity and cutoff arguments to log-two data.
See ../THIRD_PARTY_NOTICES.txt for provenance and the recorded changes.
-/

/-! The algebraic rigidity implication, with the persistent normal-product
comparison exposed as an input here and proved in NormalComparison.lean. The implication adapts the
logarithmic part of Geometry/CurveFieldRigidity.lean (openai/math, Apache-2.0).
It applies at every nonzero Y center, not only Y=1. -/
namespace LogTwo.Geometry
open OAI PiExponent PiExponentApprox CurveValuationCenter CurveCenters
open Filter Topology
noncomputable section
variable {E : Type*} [Field E] [Algebra ℂ E]

/-- The same numerical constant as the comparison theorem, defined without its
large intersection-theory import closure. -/
def rigidityComparisonConstant (m : ℕ) (sigma : ℝ) : ℝ :=
  2*((m : ℝ)+2)^(m+2)*(1+((m : ℝ)+2)/sigma)^(m+2)

theorem rigidityComparisonConstant_pos (m : ℕ) {sigma : ℝ} (hsigma : 0 < sigma) :
    0 < rigidityComparisonConstant m sigma := by logtwo_quiet
  unfold rigidityComparisonConstant
  positivity

def UniformRectangles (n : ℕ) (cost : Fin n → ℝ) (epsilon N : ℝ) : Prop :=
  ∀ k : ℕ, 0 < k → k ≤ n → ∀ B : Fin k → Fin n, ∀ i,
    2 ≤ rectangularCutoff (fun j => cost (B j)) (epsilon*N) i

/-- Rectangular cutoffs are achieved after fixing all costs. No uniformity in
future choices of centers or denominators is asserted. -/
theorem eventually_uniformRectangles_nat (n : ℕ) (cost : Fin n → ℝ)
    (hcost : ∀ i, 0 < cost i) (epsilon : ℝ) (hepsilon : 0 < epsilon) :
    ∀ᶠ N : ℕ in atTop, UniformRectangles n cost epsilon N := by logtwo_quiet
  have ht : Tendsto (fun N : ℕ => epsilon*(N : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.const_mul_atTop hepsilon
  have hb : ∀ᶠ N : ℕ in atTop, ∀ j : Fin n,
      (n : ℝ)*cost j < epsilon*N :=
    Filter.eventually_all.mpr (fun j => ht.eventually (eventually_gt_atTop _))
  filter_upwards [hb] with N hN
  intro k hk hkn B i
  apply two_le_rectangularCutoff hk (fun j => cost (B j)) (fun j => hcost _) i
  exact (mul_le_mul_of_nonneg_right (Nat.cast_le.mpr hkn) (hcost _).le).trans_lt (hN (B i))

theorem coordinate_constant_of_persistent_comparison {m : ℕ}
    (z : Fin (m+1) → E) (hheight : (coordinateKernel z).height ≤ m)
    (hY : MvPolynomial.X (0 : Fin (m+1)) ∉ coordinateKernel z)
    (w cost : Fin (m+1) → ℝ) (M sigma N : ℝ)
    (hcost : ∀ i, 0 ≤ cost i) (hsigma : 0 ≤ sigma) (hN : 0 ≤ N)
    (F : FramePolynomial m) (hF0 : F ≠ 0)
    (hvanish : ∀ word : List (Fin (m+1)), frameWordCost cost word ≤ sigma*N →
      polynomialFrameWord m word F ∈ coordinateKernel z)
    (hcomparison : CurveComponentRigidity.PersistentNormalComparison w cost M
      ((sigma/((m : ℝ)+2))*N) F (coordinateKernel z) hY)
    (hseparated : SeparatedProducts w cost M) :
    ∃ a : ℂ, z 0 = algebraMap ℂ E a := by logtwo_quiet
  have hbound : ((m : ℝ)+2)*((sigma/((m : ℝ)+2))*N) = sigma*N := by logtwo_quiet
    have hm : (m : ℝ)+2 ≠ 0 := by logtwo_quiet positivity
    field_simp
  obtain ⟨a, ha⟩ := CurveComponentRigidity.coordinate_constant_of_persistent_comparison
    w cost M ((sigma/((m : ℝ)+2))*N) hcost (by logtwo_quiet positivity) F hF0
    (coordinateKernel z) inferInstance hheight hY
    (fun word hword => hvanish word (by logtwo_quiet simpa only [hbound] using hword))
    hcomparison hseparated
  exact ⟨a, by logtwo_quiet simpa only [mem_coordinateKernel, map_sub, MvPolynomial.aeval_X,
    MvPolynomial.aeval_C, sub_eq_zero] using ha⟩

end
end LogTwo.Geometry
end Source0099
#print axioms OAI.PiExponent.irrationalityExponent_eq_two_of_eventualLowerBound
#print axioms LogTwo.Geometry.coordinateKernel_height_le
#print axioms OAI.PiExponent.derivation_mem_polynomialTangent

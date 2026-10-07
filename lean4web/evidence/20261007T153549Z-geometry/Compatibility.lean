module
public import Mathlib
@[expose] public section

section Source0000
/-
Modification notice for the LogTwo project.
Derived from openai/math (Apache-2.0), revision adc7f1241b42e322a6451854ab7e4b4c146bf78a.
Original source: lean/OAI/NumberTheory/PiExponent/Geometry/WeightedCurveDegree.lean
Changes: Convert module/import declarations to the Lean 4.34 public module format.
See ../../../../../THIRD_PARTY_NOTICES.txt for provenance and the recorded changes.
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
    (v : AddValuation K (WithTop ℤ)) : integerOrder v 1 = 0 := by
  apply WithTop.coe_injective
  simp

@[simp] theorem integerOrder_mul {K : Type*} [Field K]
    (v : AddValuation K (WithTop ℤ)) (x y : Kˣ) :
    integerOrder v (x * y) = integerOrder v x + integerOrder v y := by
  apply WithTop.coe_injective
  simp

@[simp] theorem integerOrder_pow {K : Type*} [Field K]
    (v : AddValuation K (WithTop ℤ)) (x : Kˣ) (n : ℕ) :
    integerOrder v (x ^ n) = n * integerOrder v x := by
  induction n with
  | zero => simp
  | succ n ih => rw [pow_succ, integerOrder_mul, ih]; push_cast; ring

@[simp] theorem integerOrder_prod {K ι : Type*} [Field K]
    (v : AddValuation K (WithTop ℤ)) (s : Finset ι) (x : ι → Kˣ) :
    integerOrder v (∏ i ∈ s, x i) = ∑ i ∈ s, integerOrder v (x i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert i s hi ih => simp [hi, ih]

theorem integerOrder_monomial {K ι : Type*} [Field K] [Fintype ι]
    (v : AddValuation K (WithTop ℤ)) (x : ι → Kˣ) (a : ι → ℕ) :
    integerOrder v (∏ i, x i ^ a i) = ∑ i, (a i : ℤ) * integerOrder v (x i) := by
  simp

noncomputable def weightedPole {ι : Type*} [Fintype ι]
    (w z : ι → ℚ) : ℚ :=
  (Finset.univ : Finset (Option ι)).sup' Finset.univ_nonempty
    (fun i => i.elim 0 (fun j => -z j / w j))

theorem weightedPole_nonneg {ι : Type*} [Fintype ι] (w z : ι → ℚ) :
    0 ≤ weightedPole w z := by
  exact Finset.le_sup' (fun i : Option ι => i.elim 0 (fun j => -z j / w j))
    (Finset.mem_univ (none : Option ι))

theorem div_le_weightedPole {ι : Type*} [Fintype ι] (w z : ι → ℚ) (i : ι) :
    -z i / w i ≤ weightedPole w z := by
  exact Finset.le_sup' (fun o : Option ι => o.elim 0 (fun j => -z j / w j))
    (Finset.mem_univ (some i))

theorem monomial_pole_le {ι : Type*} [Fintype ι]
    (w z : ι → ℚ) (hw : ∀ i, 0 < w i) (a : ι → ℕ) {R : ℚ}
    (ha : (∑ i, w i * (a i : ℚ)) ≤ R) :
    -(∑ i, (a i : ℚ) * z i) ≤ R * weightedPole w z := by
  have hcoord (i : ι) : -z i ≤ w i * weightedPole w z := by
    have h := (div_le_iff₀ (hw i)).mp (div_le_weightedPole w z i)
    simpa [mul_comm] using h
  calc
    _ = ∑ i, (a i : ℚ) * (-z i) := by simp [Finset.sum_neg_distrib]
    _ ≤ ∑ i, (a i : ℚ) * (w i * weightedPole w z) := by
      apply Finset.sum_le_sum
      intro i _
      exact mul_le_mul_of_nonneg_left (hcoord i) (Nat.cast_nonneg _)
    _ = (∑ i, w i * (a i : ℚ)) * weightedPole w z := by
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro i _
      ring
    _ ≤ R * weightedPole w z :=
      mul_le_mul_of_nonneg_right ha (weightedPole_nonneg w z)

theorem monomial_max_pole_eq {ι : Type*} [Fintype ι] [DecidableEq ι]
    (w z : ι → ℚ) (hw : ∀ i, 0 < w i) {R : ℚ} (_hR : 0 < R)
    (powers : ι → ℕ) (hpowers : ∀ i, w i * (powers i : ℚ) = R)
    (monomials : Finset (ι → ℕ)) (hzero : 0 ∈ monomials)
    (hpure : ∀ i, Pi.single i (powers i) ∈ monomials)
    (hbudget : ∀ a ∈ monomials, (∑ i, w i * (a i : ℚ)) ≤ R) :
    monomials.sup' ⟨0, hzero⟩ (fun a => -(∑ i, (a i : ℚ) * z i)) =
      R * weightedPole w z := by
  apply le_antisymm
  · apply Finset.sup'_le
    intro a ha
    exact monomial_pole_le w z hw a (hbudget a ha)
  · obtain ⟨o, _, ho⟩ := Finset.exists_mem_eq_sup'
      (s := (Finset.univ : Finset (Option ι))) Finset.univ_nonempty
      (fun i => i.elim 0 (fun j => -z j / w j))
    change weightedPole w z = _ at ho
    rw [ho]
    cases o with
    | none =>
      simpa using Finset.le_sup' (fun a => -(∑ i, (a i : ℚ) * z i)) hzero
    | some i =>
      have hp := Finset.le_sup' (fun a => -(∑ j, (a j : ℚ) * z j)) (hpure i)
      have hs : (∑ j, (((Pi.single i (powers i) : ι → ℕ) j) : ℚ) * z j) = (powers i : ℚ) * z i := by
        simp [Pi.single_apply]
      rw [hs] at hp
      change R * (-z i / w i) ≤ _
      have he : R * (-z i / w i) = -(powers i : ℚ) * z i := by
        rw [← hpowers i]
        field_simp [ne_of_gt (hw i)]
      rw [he]
      simpa using hp

theorem valuation_monomial_max_pole_eq
    {K ι : Type*} [Field K] [Fintype ι] [DecidableEq ι]
    (v : AddValuation K (WithTop ℤ)) (x : ι → Kˣ)
    (w : ι → ℚ) (hw : ∀ i, 0 < w i) {R : ℚ} (hR : 0 < R)
    (powers : ι → ℕ) (hpowers : ∀ i, w i * (powers i : ℚ) = R)
    (monomials : Finset (ι → ℕ)) (hzero : 0 ∈ monomials)
    (hpure : ∀ i, Pi.single i (powers i) ∈ monomials)
    (hbudget : ∀ a ∈ monomials, (∑ i, w i * (a i : ℚ)) ≤ R) :
    monomials.sup' ⟨0, hzero⟩
        (fun a => -(integerOrder v (∏ i, x i ^ a i) : ℚ)) =
      R * weightedPole w (fun i => (integerOrder v (x i) : ℚ)) := by
  simpa only [integerOrder_monomial, Int.cast_sum, Int.cast_mul, Int.cast_natCast] using
    monomial_max_pole_eq w (fun i => (integerOrder v (x i) : ℚ)) hw hR
      powers hpowers monomials hzero hpure hbudget

noncomputable def monomialPoleCoefficient
    {K ι : Type*} [Field K] [Fintype ι]
    (v : AddValuation K (WithTop ℤ)) (x : ι → Kˣ)
    (monomials : Finset (ι → ℕ)) (hzero : 0 ∈ monomials) : ℤ :=
  monomials.sup' ⟨0, hzero⟩ (fun a => -integerOrder v (∏ i, x i ^ a i))

theorem monomialPoleCoefficient_nonneg
    {K ι : Type*} [Field K] [Fintype ι]
    (v : AddValuation K (WithTop ℤ)) (x : ι → Kˣ)
    (monomials : Finset (ι → ℕ)) (hzero : 0 ∈ monomials) :
    0 ≤ monomialPoleCoefficient v x monomials hzero := by
  have h := Finset.le_sup' (fun a => -integerOrder v (∏ i, x i ^ a i)) hzero
  simpa [monomialPoleCoefficient] using h

theorem monomialPoleCoefficient_eq
    {K ι : Type*} [Field K] [Fintype ι] [DecidableEq ι]
    (v : AddValuation K (WithTop ℤ)) (x : ι → Kˣ)
    (w : ι → ℚ) (hw : ∀ i, 0 < w i) {R : ℚ} (hR : 0 < R)
    (powers : ι → ℕ) (hpowers : ∀ i, w i * (powers i : ℚ) = R)
    (monomials : Finset (ι → ℕ)) (hzero : 0 ∈ monomials)
    (hpure : ∀ i, Pi.single i (powers i) ∈ monomials)
    (hbudget : ∀ a ∈ monomials, (∑ i, w i * (a i : ℚ)) ≤ R) :
    (monomialPoleCoefficient v x monomials hzero : ℚ) =
      R * weightedPole w (fun i => (integerOrder v (x i) : ℚ)) := by
  unfold monomialPoleCoefficient
  rw [Finset.apply_sup'_eq_sup'_comp ⟨0, hzero⟩ (fun n : ℤ => (n : ℚ))
    (by intro a b; exact_mod_cast (show max a b = max a b from rfl))]
  simpa only [Function.comp_def, Int.cast_neg] using
    valuation_monomial_max_pole_eq v x w hw hR powers hpowers monomials hzero hpure hbudget

theorem monomialPoleCoefficient_eq_zero
    {K ι : Type*} [Field K] [Fintype ι]
    (v : AddValuation K (WithTop ℤ)) (x : ι → Kˣ)
    (monomials : Finset (ι → ℕ)) (hzero : 0 ∈ monomials)
    (hx : ∀ i, integerOrder v (x i) = 0) :
    monomialPoleCoefficient v x monomials hzero = 0 := by
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
    (by
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
      monomialPoleCoefficient (v p) x monomials hzero := by
  unfold monomialPoleDivisor
  exact Finsupp.onFinset_apply

theorem monomialPoleDivisor_effective
    {K ι P : Type*} [Field K] [Fintype ι]
    (v : P → AddValuation K (WithTop ℤ)) (x : ι → Kˣ)
    (monomials : Finset (ι → ℕ)) (hzero : 0 ∈ monomials)
    (support : Finset P)
    (hsupport : ∀ p ∉ support, ∀ i, integerOrder (v p) (x i) = 0) :
    0 ≤ monomialPoleDivisor v x monomials hzero support hsupport := by
  intro p
  exact monomialPoleCoefficient_nonneg (v p) x monomials hzero

theorem monomialPoleDivisor_degree_eq
    {K ι P : Type*} [Field K] [Fintype ι] [DecidableEq ι]
    (v : P → AddValuation K (WithTop ℤ)) (x : ι → Kˣ)
    (w : ι → ℚ) (hw : ∀ i, 0 < w i) {R : ℚ} (hR : 0 < R)
    (powers : ι → ℕ) (hpowers : ∀ i, w i * (powers i : ℚ) = R)
    (monomials : Finset (ι → ℕ)) (hzero : 0 ∈ monomials)
    (hpure : ∀ i, Pi.single i (powers i) ∈ monomials)
    (hbudget : ∀ a ∈ monomials, (∑ i, w i * (a i : ℚ)) ≤ R)
    (support : Finset P)
    (hsupport : ∀ p ∉ support, ∀ i, integerOrder (v p) (x i) = 0) :
    ((monomialPoleDivisor v x monomials hzero support hsupport).sum (fun _ n => n) : ℚ) =
      R * ∑ p ∈ support, weightedPole w (fun i => (integerOrder (v p) (x i) : ℚ)) := by
  unfold monomialPoleDivisor
  rw [Finsupp.sum_onFinset _ _ _ _ (by intro p _; rfl)]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro p _
  exact monomialPoleCoefficient_eq (v p) x w hw hR powers hpowers monomials hzero hpure hbudget

@[simp] theorem integerOrder_inv {K : Type*} [Field K]
    (v : AddValuation K (WithTop ℤ)) (x : Kˣ) :
    integerOrder v x⁻¹ = -integerOrder v x := by
  apply WithTop.coe_injective
  simp

@[simp] theorem integerOrder_div {K : Type*} [Field K]
    (v : AddValuation K (WithTop ℤ)) (x y : Kˣ) :
    integerOrder v (x / y) = integerOrder v x - integerOrder v y := by
  simp [div_eq_mul_inv, sub_eq_add_neg]

theorem mem_valuationSubring_iff_order_nonneg {K : Type*} [Field K]
    (v : AddValuation K (WithTop ℤ)) (x : Kˣ) :
    (x : K) ∈ v.toValuation.valuationSubring ↔ 0 ≤ integerOrder v x := by
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
      (((∏ i, x i ^ a i) / (∏ i, x i ^ a i) : Kˣ) : K) = 1 := by
  obtain ⟨a, ha, hmax⟩ := Finset.exists_mem_eq_sup' ⟨0, hzero⟩
    (fun a => -integerOrder v (∏ i, x i ^ a i))
  change monomialPoleCoefficient v x monomials hzero = _ at hmax
  refine ⟨a, ha, by linarith, ?_, ?_⟩
  · intro b hb
    apply (mem_valuationSubring_iff_order_nonneg v _).mpr
    rw [integerOrder_div]
    have h := Finset.le_sup' (fun a => -integerOrder v (∏ i, x i ^ a i)) hb
    change -integerOrder v (∏ i, x i ^ b i) ≤ monomialPoleCoefficient v x monomials hzero at h
    linarith
  · simp

end PiExponent.WeightedCurveDegree

end OAI
end Source0000

section Source0001
/-
Modification notice for the LogTwo project.
Derived from openai/math (Apache-2.0), revision adc7f1241b42e322a6451854ab7e4b4c146bf78a.
Original source: lean/OAI/NumberTheory/PiExponent/Jets/IntrinsicLength.lean
Changes: Convert module/import declarations to the Lean 4.34 public module format.
See ../../../../../THIRD_PARTY_NOTICES.txt for provenance and the recorded changes.
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
    Module.annihilator A M = RingHom.ker ε := by
  have hker : (RingHom.ker ε).IsMaximal :=
    RingHom.ker_isMaximal_of_surjective ε (augmentation_surjective ε hε)
  exact (IsLocalRing.eq_maximalIdeal (IsSimpleModule.annihilator_isMaximal (R := A)
    (M := M))).trans (IsLocalRing.eq_maximalIdeal hker).symm

theorem simple_smul_eq_augmentation_smul (ε : A →+* K)
    (hε : ∀ k : K, ε (algebraMap K A k) = k)
    {M : Type*} [AddCommGroup M] [Module A M] [Module K M]
    [IsScalarTower K A M] [IsSimpleModule A M] (a : A) (x : M) :
    a • x = ε a • x := by
  have ha : a - algebraMap K A (ε a) ∈ Module.annihilator A M := by
    rw [simple_annihilator_eq_augmentation_kernel ε hε]
    rw [RingHom.mem_ker, map_sub, hε, sub_self]
  have hx := Module.mem_annihilator.mp ha x
  exact sub_eq_zero.mp (by simpa only [sub_smul, algebraMap_smul] using hx)

theorem simple_over_coefficient_field (ε : A →+* K)
    (hε : ∀ k : K, ε (algebraMap K A k) = k)
    {M : Type*} [AddCommGroup M] [Module A M] [Module K M]
    [IsScalarTower K A M] [IsSimpleModule A M] : IsSimpleModule K M := by
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
    ∀ [Module K M] [IsScalarTower K A M], Module.length A M = Module.length K M := by
  induction hM with
  | of_subsingleton =>
    intro _ _
    simp only [Module.length_eq_zero]
  | @of_simple_quotient M _ _ N hsimple hN ih =>
    intro _ _
    have : IsSimpleModule K (M ⧸ N) := simple_over_coefficient_field ε hε
    have hexact : Function.Exact N.subtype N.mkQ := by
      rw [LinearMap.exact_iff, Submodule.range_subtype, Submodule.ker_mkQ]
    have hA := Module.length_eq_add_of_exact N.subtype N.mkQ
      (Submodule.subtype_injective N) (Submodule.mkQ_surjective N) hexact
    have hK := Module.length_eq_add_of_exact (N.subtype.restrictScalars K)
      (N.mkQ.restrictScalars K) (Submodule.subtype_injective N)
      (Submodule.mkQ_surjective N) hexact
    calc
      Module.length A M = Module.length A N + Module.length A (M ⧸ N) := hA
      _ = Module.length K N + Module.length K (M ⧸ N) := by
        rw [ih, Module.length_eq_one A (M ⧸ N), Module.length_eq_one K (M ⧸ N)]
      _ = Module.length K M := hK.symm

theorem module_length_eq_finrank_of_augmentation (ε : A →+* K)
    (hε : ∀ k : K, ε (algebraMap K A k) = k)
    {M : Type*} [AddCommGroup M] [Module A M] [Module K M]
    [IsScalarTower K A M] [Module.Finite K M] :
    Module.length A M = Module.finrank K M := by
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
end Source0001

section Source0002
/-
Modification notice for the LogTwo project.
Derived from openai/math (Apache-2.0), revision adc7f1241b42e322a6451854ab7e4b4c146bf78a.
Original source: lean/OAI/NumberTheory/PiExponent/Geometry/CurveLocalOrder.lean
Changes: Convert module/import declarations to the Lean 4.34 public module format.
See ../../../../../THIRD_PARTY_NOTICES.txt for provenance and the recorded changes.
-/




namespace OAI

open scoped BigOperators nonZeroDivisors
open IsLocalRing IsDiscreteValuationRing

namespace PiExponent.CurveLocalOrder

theorem length_quotient_span_eq_addVal
    {A : Type*} [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
    {a : A} (ha : a ≠ 0) :
    Module.length A (A ⧸ Ideal.span {a}) = IsDiscreteValuationRing.addVal A a := by
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible A
  obtain ⟨n, u, rfl⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible ha hϖ
  rw [IsDiscreteValuationRing.addVal_def' u hϖ]
  rw [Ideal.span_singleton_mul_left_unit u.isUnit,
    ← Ideal.span_singleton_pow, ← hϖ.maximalIdeal_eq]
  exact IsDiscreteValuationRing.length_quotient_pow_maximalIdeal A n

def enatToIntegerOrder : ℕ∞ →+ WithTop ℤ where
  toFun := ENat.map (fun n : ℕ => (n : ℤ))
  map_zero' := by simp
  map_add' a b := ENat.map_add (Nat.castAddMonoidHom ℤ) a b

@[simp] theorem enatToIntegerOrder_top : enatToIntegerOrder ⊤ = ⊤ := rfl

@[simp] theorem enatToIntegerOrder_natCast (n : ℕ) :
    enatToIntegerOrder n = (n : WithTop ℤ) := rfl

@[simp] theorem enatToIntegerOrder_eq_top_iff (n : ℕ∞) :
    enatToIntegerOrder n = ⊤ ↔ n = ⊤ := ENat.map_eq_top_iff

theorem enatToIntegerOrder_monotone : Monotone enatToIntegerOrder := by
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
    localAddValuation A a = ⊤ ↔ a = 0 := by
  rw [localAddValuation_apply, enatToIntegerOrder_eq_top_iff,
    IsDiscreteValuationRing.addVal_eq_top_iff]

theorem nonZeroDivisors_le_primeCompl
    (A : Type*) [CommRing A] [IsDomain A] [IsDiscreteValuationRing A] :
    nonZeroDivisors A ≤ (localAddValuation A).toValuation.supp.primeCompl := by
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
    fractionAddValuation A K (algebraMap A K a) = localAddValuation A a := by
  exact Valuation.extendToLocalization_apply_map_apply
    (localAddValuation A).toValuation (nonZeroDivisors_le_primeCompl A) K a

theorem fraction_order_eq_principal_colength
    {A K : Type*} [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
    [Field K] [Algebra A K] [IsFractionRing A K] {a : A} (ha : a ≠ 0) :
    fractionAddValuation A K (algebraMap A K a) =
      enatToIntegerOrder (Module.length A (A ⧸ Ideal.span {a})) := by
  rw [fractionAddValuation_algebraMap, localAddValuation_apply,
    length_quotient_span_eq_addVal ha]

theorem principal_colength_ne_top
    {A : Type*} [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
    {a : A} (ha : a ≠ 0) : Module.length A (A ⧸ Ideal.span {a}) ≠ ⊤ := by
  rw [length_quotient_span_eq_addVal ha]
  exact IsDiscreteValuationRing.addVal_eq_top_iff.not.mpr ha

theorem integerOrder_field_image_eq_length
    {A K : Type*} [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
    [Field K] [Algebra A K] [IsFractionRing A K] {a : A} (ha : a ≠ 0) :
    WeightedCurveDegree.integerOrder (fractionAddValuation A K)
      (Units.mk0 (algebraMap A K a) ((map_ne_zero_iff _ (IsFractionRing.injective A K)).mpr ha)) =
        ((Module.length A (A ⧸ Ideal.span {a})).toNat : ℤ) := by
  apply WithTop.coe_injective
  rw [WeightedCurveDegree.coe_integerOrder]
  change fractionAddValuation A K (algebraMap A K a) = _
  rw [fraction_order_eq_principal_colength ha]
  obtain ⟨n, hn⟩ := ENat.ne_top_iff_exists.mp (principal_colength_ne_top ha)
  rw [← hn]
  simp

theorem atPrime_principal_colength
    {S : Type*} [CommRing S] [IsDedekindDomain S]
    (q : IsDedekindDomain.HeightOneSpectrum S) {a : S} (ha : a ≠ 0) :
    let A := Localization.AtPrime q.asIdeal
    letI : IsDiscreteValuationRing A :=
      IsLocalization.AtPrime.isDiscreteValuationRing_of_dedekind_domain S q.ne_bot A
    Module.length A (A ⧸ Ideal.span {algebraMap S A a}) =
      IsDiscreteValuationRing.addVal A (algebraMap S A a) := by
  dsimp only
  let : IsDiscreteValuationRing (Localization.AtPrime q.asIdeal) :=
    IsLocalization.AtPrime.isDiscreteValuationRing_of_dedekind_domain S q.ne_bot _
  apply length_quotient_span_eq_addVal
  exact (map_ne_zero_iff _ (IsLocalization.injective
    (Localization.AtPrime q.asIdeal) q.asIdeal.primeCompl_le_nonZeroDivisors)).mpr ha

theorem ramificationIdx_eq_local_order
    {R S : Type*} [CommRing R] [CommRing S] [IsDedekindDomain S]
    [Algebra R S] (t : R) (q : Ideal S) [q.IsPrime]
    [q.LiesOver (Ideal.span {t})] (hq : q ≠ ⊥)
    (ht : algebraMap R (Localization.AtPrime q) t ≠ 0) :
    letI : IsDiscreteValuationRing (Localization.AtPrime q) :=
      IsLocalization.AtPrime.isDiscreteValuationRing_of_dedekind_domain S hq _
    q.ramificationIdx R =
      (IsDiscreteValuationRing.addVal (Localization.AtPrime q)
        (algebraMap R (Localization.AtPrime q) t)).toNat := by
  let : IsDiscreteValuationRing (Localization.AtPrime q) :=
    IsLocalization.AtPrime.isDiscreteValuationRing_of_dedekind_domain S hq _
  rw [Ideal.ramificationIdx_eq (Ideal.span {t}) q,
    Ideal.map_span, Set.image_singleton, length_quotient_span_eq_addVal ht]

theorem finite_over_coefficient_field_of_finite_length
    {F A M : Type*} [Field F] [CommRing A] [Algebra F A] [IsLocalRing A]
    [AddCommGroup M] [Module A M] [Module F M] [IsScalarTower F A M]
    (ε : A →+* F) (hε : ∀ c : F, ε (algebraMap F A c) = c)
    (hM : IsFiniteLength A M) : Module.Finite F M := by
  have hlength := PiExponentJets.W24.length_eq_coefficient_length ε hε hM
  have hF : IsFiniteLength F M := Module.length_ne_top_iff.mp (by
    rw [← hlength]
    exact Module.length_ne_top_iff.mpr hM)
  let : IsNoetherian F M := (isFiniteLength_iff_isNoetherian_isArtinian.mp hF).1
  infer_instance

theorem principal_quotient_finite_over_coefficient_field
    {F A : Type*} [Field F] [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
    [Algebra F A] (ε : A →+* F) (hε : ∀ c : F, ε (algebraMap F A c) = c)
    {a : A} (ha : a ≠ 0) : Module.Finite F (A ⧸ Ideal.span {a}) := by
  exact finite_over_coefficient_field_of_finite_length ε hε
    (Module.length_ne_top_iff.mp (principal_colength_ne_top ha))

theorem principal_quotient_finrank_eq_order
    {F A : Type*} [Field F] [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
    [Algebra F A] (ε : A →+* F) (hε : ∀ c : F, ε (algebraMap F A c) = c)
    {a : A} (ha : a ≠ 0) :
    (Module.finrank F (A ⧸ Ideal.span {a}) : ℕ∞) = IsDiscreteValuationRing.addVal A a := by
  let := principal_quotient_finite_over_coefficient_field ε hε ha
  rw [← PiExponentJets.W24.module_length_eq_finrank_of_augmentation ε hε]
  exact length_quotient_span_eq_addVal ha

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
    residueAugmentation F A (algebraMap F A c) = c := by
  change (residueCoefficientEquiv F A).symm
    (algebraMap A (IsLocalRing.ResidueField A) (algebraMap F A c)) = c
  rw [← IsScalarTower.algebraMap_apply F A (IsLocalRing.ResidueField A)]
  exact (residueCoefficientEquiv F A).symm.commutes c

theorem principal_quotient_finrank_eq_order_of_algClosed
    {F A : Type*} [Field F] [IsAlgClosed F] [CommRing A] [IsDomain A]
    [IsDiscreteValuationRing A] [Algebra F A]
    [Algebra.IsIntegral F (IsLocalRing.ResidueField A)] {a : A} (ha : a ≠ 0) :
    (Module.finrank F (A ⧸ Ideal.span {a}) : ℕ∞) = IsDiscreteValuationRing.addVal A a :=
  principal_quotient_finrank_eq_order (residueAugmentation F A)
    (residueAugmentation_algebraMap F A) ha

end PiExponent.CurveLocalOrder

end OAI
end Source0002

section Source0003
/-
Modification notice for the LogTwo project.
Derived from openai/math (Apache-2.0), revision adc7f1241b42e322a6451854ab7e4b4c146bf78a.
Original source: lean/OAI/NumberTheory/PiExponent/Cohomology/FiniteCoverCohomology.lean
Changes: Convert module/import declarations to the Lean 4.34 public module format.
Expose private helpers and adjust helper names where needed for module compatibility.
See ../../../../../THIRD_PARTY_NOTICES.txt for provenance and the recorded changes.
-/




namespace OAI

noncomputable section

namespace PiExponentSeshadri

abbrev schemeUnit (X : AlgebraicGeometry.Scheme) : X.Modules :=
  SheafOfModules.unit X.ringCatSheaf

namespace AdicInjective
universe u v
variable {R : Type u} [CommRing R]
variable (I : Ideal R) (M : Type v) [AddCommGroup M] [Module R M]

def adicTorsion : Submodule R M :=
  ⨆ n : ℕ, Submodule.torsionBySet R M ((I ^ n : Ideal R) : Set R)

lemma torsion_mono : Monotone (fun n : ℕ => Submodule.torsionBySet R M ((I ^ n : Ideal R) : Set R)) :=
  fun a b hab => Submodule.torsionBySet_le_torsionBySet_pow a b hab I

lemma mem_adicTorsion (x : M) : x ∈ adicTorsion I M ↔
    ∃ n : ℕ, ∀ a ∈ I ^ n, a • x = 0 := by
  rw [adicTorsion, Submodule.mem_iSup_of_directed _ (torsion_mono I M).directed_le]
  simp only [Submodule.mem_torsionBySet_iff, Subtype.forall, SetLike.mem_coe]

lemma fg_uniform_exponent (N : Submodule R M) (hN : N.FG)
    (h : N ≤ adicTorsion I M) :
    ∃ n : ℕ, N ≤ Submodule.torsionBySet R M ((I ^ n : Ideal R) : Set R) := by
  classical
  obtain ⟨s, hs⟩ := IsCompactElement.exists_finset_of_le_iSup
    ((Submodule.fg_iff_compact N).mp hN)
    (fun n : ℕ => Submodule.torsionBySet R M ((I ^ n : Ideal R) : Set R)) h
  refine ⟨s.sup id, hs.trans (iSup_le fun n => iSup_le fun hn => ?_)⟩
  exact torsion_mono I M (Finset.le_sup (f := id) hn)

lemma exists_power_inf_le [IsNoetherianRing R] (J : Ideal R) (n : ℕ) :
    ∃ m : ℕ, I ^ m ⊓ J ≤ I ^ n * J := by
  obtain ⟨k, hk⟩ := I.exists_pow_inf_eq_pow_smul (M := R) J
  refine ⟨k+n, ?_⟩
  have h := hk (k+n) (Nat.le_add_right _ _)
  simp only [Ideal.smul_eq_mul, Ideal.mul_top, Nat.add_sub_cancel_left] at h
  rw [h]
  exact Ideal.mul_mono le_rfl inf_le_right

theorem adicTorsion_injective [IsNoetherianRing R] [Small.{v} R]
    [Module.Injective R M] : Module.Injective R (adicTorsion I M) := by
  apply Module.Baer.injective
  intro J g
  let g₀ : J →ₗ[R] M := (adicTorsion I M).subtype.comp g
  have hg₀ : g₀.range ≤ adicTorsion I M := by
    rintro x ⟨y, rfl⟩
    exact (g y).property
  obtain ⟨n, hn⟩ := fg_uniform_exponent I M g₀.range (Submodule.fg_range g₀) hg₀
  obtain ⟨h, hh⟩ := Module.Injective.extension_property R M J R
    J.subtype Subtype.val_injective g₀
  have hj : ∀ x : J, h x = g₀ x := fun x => LinearMap.congr_fun hh x
  have hzero : I ^ n * J ≤ h.ker := by
    apply Ideal.mul_le.mpr
    intro a ha b hb
    change h (a * b) = 0
    rw [← smul_eq_mul, h.map_smul, hj ⟨b, hb⟩]
    exact (Submodule.mem_torsionBySet_iff _ _).mp (hn (LinearMap.mem_range_self g₀ ⟨b,hb⟩)) ⟨a,ha⟩
  obtain ⟨m, hm⟩ := exists_power_inf_le I J n
  let f : R →ₗ.[R] M := ⟨J, g₀⟩
  let z : R →ₗ.[R] M := ⟨I ^ m, 0⟩
  have hz : ∀ (x : f.domain) (y : z.domain), (x : R) = y → f x = z y := by
    intro x y hxy
    change g₀ x = 0
    rw [← hj x]
    exact hzero (hm ⟨hxy ▸ y.property, x.property⟩)
  let F := f.sup z hz
  obtain ⟨H, hH⟩ := Module.Injective.extension_property R M F.domain R
    F.domain.subtype Subtype.val_injective F.toFun
  have HF : ∀ x : F.domain, H x = F x := fun x => LinearMap.congr_fun hH x
  have HJ : ∀ x : J, H x = g₀ x := by
    intro x
    rw [HF ⟨x, (show J ≤ J ⊔ I ^ m from le_sup_left) x.property⟩]
    exact ((f.left_le_sup z hz).2 (x := x) (y := ⟨x, (show J ≤ J ⊔ I ^ m from le_sup_left) x.property⟩) rfl).symm
  have HI : ∀ a ∈ I ^ m, H a = 0 := by
    intro a ha
    rw [HF ⟨a, (show I ^ m ≤ J ⊔ I ^ m from le_sup_right) ha⟩]
    exact ((f.right_le_sup z hz).2 (x := ⟨a,ha⟩) (y := ⟨a,(show I ^ m ≤ J ⊔ I ^ m from le_sup_right) ha⟩) rfl).symm
  have Hmem : ∀ a, H a ∈ adicTorsion I M := by
    intro a
    apply (mem_adicTorsion I M _).mpr
    refine ⟨m, fun b hb => ?_⟩
    rw [← H.map_smul]
    exact HI (b * a) ((I ^ m).mul_mem_right a hb)
  refine ⟨H.codRestrict (adicTorsion I M) Hmem, ?_⟩
  intro x hx
  apply Subtype.ext
  exact HJ ⟨x,hx⟩

end AdicInjective

namespace InjectiveRange
universe u v w
variable {R : Type u} [CommRing R]
variable {M : Type v} [AddCommGroup M] [Module R M] [Small.{v} R]
variable {N : Type w} [AddCommGroup N] [Module R N] [Small.{w} R]

omit [Small.{w} R] in

lemma injective_of_retract [Module.Injective R M]
    (i : N →ₗ[R] M) (p : M →ₗ[R] N) (h : p.comp i = LinearMap.id) :
    Module.Injective R N := by
  apply Module.Baer.injective
  intro J g
  obtain ⟨f, hf⟩ := Module.Baer.of_injective (R := R) (Q := M) inferInstance J (i.comp g)
  refine ⟨p.comp f, fun x hx => ?_⟩
  change p (f x) = g ⟨x,hx⟩
  rw [hf x hx]
  exact LinearMap.congr_fun h (g ⟨x,hx⟩)

omit [Small.{w} R] in
lemma range_injective (r : M →ₗ[R] N) [Module.Injective R M]
    [Module.Injective R r.ker] : Module.Injective R r.range := by
  obtain ⟨p, hp⟩ := Module.Injective.extension_property R r.ker r.ker M
    r.ker.subtype Subtype.val_injective LinearMap.id
  let f : M →ₗ[R] M := LinearMap.id - r.ker.subtype.comp p
  have hf : r.ker ≤ f.ker := by
    intro x hx
    change x - (p x : M) = 0
    have hpx := LinearMap.congr_fun hp ⟨x,hx⟩
    exact sub_eq_zero.mpr (congrArg Subtype.val hpx).symm
  let i : r.range →ₗ[R] M := (r.ker.liftQ f hf).comp r.quotKerEquivRange.symm.toLinearMap
  apply injective_of_retract i r.rangeRestrict
  ext y
  rcases y with ⟨y,hy⟩
  obtain ⟨x,rfl⟩ := hy
  change r ((r.ker.liftQ f hf) (r.quotKerEquivRange.symm ⟨r x, LinearMap.mem_range_self r x⟩)) = r x
  rw [LinearMap.quotKerEquivRange_symm_apply_image]
  change r (x - (p x : M)) = r x
  rw [map_sub, (p x).property, sub_zero]

lemma surjective_of_torsion_cokernel (I : Ideal R) (r : M →ₗ[R] N)
    [Module.Injective R M] [Module.Injective R r.ker]
    (hc : ∀ y : N, ∃ n : ℕ, ∀ a ∈ I ^ n, a • y ∈ r.range)
    (ht : ∀ y : N, (∃ n : ℕ, ∀ a ∈ I ^ n, a • y = 0) → y = 0) :
    Function.Surjective r := by
  let : Module.Injective R r.range := range_injective r
  obtain ⟨p, hp⟩ := Module.Injective.extension_property R r.range r.range N
    r.range.subtype Subtype.val_injective LinearMap.id
  intro y
  suffices h : y = (p y : N) from h ▸ (p y).property
  apply sub_eq_zero.mp
  apply ht
  obtain ⟨n, hn⟩ := hc y
  refine ⟨n, fun a ha => ?_⟩
  rw [smul_sub]
  have h := congrArg Subtype.val (LinearMap.congr_fun hp ⟨a • y, hn a ha⟩)
  change (p (a • y) : N) = a • y at h
  rw [map_smul] at h
  exact sub_eq_zero.mpr h.symm

end InjectiveRange

section
universe u
open TopCat AlgebraicGeometry TopologicalSpace CategoryTheory Opposite
open PrimeSpectrum
namespace AffineDenominators
variable {R : CommRingCat.{u}} (M : (Spec R).Modules)

abbrev schemeBasicOpen (f : R) : (Spec R).Opens := PrimeSpectrum.basicOpen f

private lemma schemeBasicOpen_mul (f g : R) :
    schemeBasicOpen (f * g) = schemeBasicOpen f ⊓ schemeBasicOpen g :=
  PrimeSpectrum.basicOpen_mul f g

private lemma schemeBasicOpen_mul_le_left (f g : R) :
    schemeBasicOpen (f * g) ≤ schemeBasicOpen f :=
  PrimeSpectrum.basicOpen_mul_le_left f g

private lemma schemeBasicOpen_mul_le_right (f g : R) :
    schemeBasicOpen (f * g) ≤ schemeBasicOpen g :=
  PrimeSpectrum.basicOpen_mul_le_right f g

private lemma schemeIsSMulRegular {f : R} {U : (Spec R).Opens}
    (hle : U ≤ schemeBasicOpen f) : IsSMulRegular Γ(M, U) f :=
  M.isSMulRegular_of_le_basicOpen (U := U) hle

structure Aux (V : (Spec R).Opens) where
  existence (f : R) (hf : schemeBasicOpen f ≤ V) (s : Γ(M, schemeBasicOpen f)) :
    ∃ (n : ℕ) (t : Γ(M, V)), M.presheaf.map (homOfLE hf).op t = f ^ n • s
  uniqueness (f : R) (hf : schemeBasicOpen f ≤ V) (t : Γ(M, V)) :
    M.presheaf.map (.op <| homOfLE hf) t = (0 : Γ(M, schemeBasicOpen f)) →
    ∃ (n : ℕ), f ^ n • t = 0

lemma Aux.of_le {M : (Spec R).Modules} {V : (Spec R).Opens} (g : R) (hg : schemeBasicOpen g ≤ V)
    (hV : Aux M V) :
    Aux M (schemeBasicOpen g) where
  existence f hfg s := by
    obtain ⟨n, t, ht⟩ := hV.existence f (le_trans hfg hg) s
    use n, M.presheaf.map (homOfLE hg).op t
    simp [← M.presheaf.map_comp_apply, ← op_comp, homOfLE_comp, ht]
  uniqueness f hfg t ht := by
    obtain ⟨n, t', ht'⟩ := hV.existence g hg t
    obtain ⟨m, hm⟩ := hV.uniqueness _ (le_trans hfg hg) t' <| by
      rw [← homOfLE_comp hfg hg, op_comp, M.presheaf.map_comp_apply, ht', M.map_smul_Spec, ht]
      simp
    refine ⟨m, ((schemeIsSMulRegular M le_rfl).pow n).right_eq_zero_of_smul ?_⟩
    simp [smul_comm, ← ht', ← M.map_smul_Spec, hm]

lemma Aux.of_eq_iSup_basicOpen {M : (Spec R).Modules} (V : (Spec R).Opens)
    {ι : Type*} [Finite ι] (g : ι → R) (hg : V = ⨆ i, schemeBasicOpen (g i))
    (h₁ : ∀ (i : ι), Aux M (schemeBasicOpen (g i))) :
    Aux M V := by
  have h₂ (i j : ι) : Aux M (schemeBasicOpen (g i * g j)) :=
    .of_le _ (schemeBasicOpen_mul_le_left _ _) (h₁ i)
  have hgle (i : ι) : schemeBasicOpen (g i) ≤ V := by rw [hg]; exact le_iSup_of_le _ le_rfl
  have hug (i : ι) (m : ℕ) :
      IsUnit (algebraMap R (Module.End R Γ(M, schemeBasicOpen (g i))) (g i ^ m)) := by
    rw [map_pow]
    exact (Scheme.Modules.isUnit_algebraMap_end_of_le_basicOpen (g i) le_rfl).pow m

  refine ⟨fun f hf s ↦ ?_, fun f hf t hs ↦ ?_⟩
  · have hfgi (i : ι) : schemeBasicOpen (f * g i) ≤ schemeBasicOpen (g i) := schemeBasicOpen_mul_le_right f (g i)
    let s' (i : ι) : Γ(M, schemeBasicOpen (f * g i)) :=
      M.presheaf.map (homOfLE <| schemeBasicOpen_mul_le_left f (g i)).op s

    obtain ⟨N, t, ht⟩ : ∃ (N : ℕ) (t : ∀ i, Γ(M, schemeBasicOpen (g i))),
        ∀ i, f ^ N • s' i = M.presheaf.map (homOfLE (schemeBasicOpen_mul_le_right f (g i))).op (t i) := by
      have (i : ι) : ∃ (n : ℕ) (t : Γ(M, schemeBasicOpen (g i))),
          f ^ n • s' i = M.presheaf.map (homOfLE (hfgi i)).op t := by
        obtain ⟨n, t', ht'⟩ := (h₁ i).existence (f * g i) (hfgi i) (s' i)
        rw [mul_pow, mul_smul, smul_comm] at ht'
        obtain ⟨ψ, hψ⟩ := IsUnit.exists_right_inv (hug i n)
        use n, ψ t'
        apply (schemeIsSMulRegular M (schemeBasicOpen_mul_le_right f (g i))).pow n
        dsimp
        rw [← ht', ← Scheme.Modules.map_smul_Spec]
        congr 1
        exact congr($hψ t').symm
      choose n t' ht' using this
      have (i : ι) : n i ≤ ⨆ i, n i := le_ciSup (Finite.bddAbove_range _) _
      have hN (i : ι) : ⨆ i, n i = ((⨆ i, n i) - n i) + n i := by grind
      refine ⟨⨆ i, n i, fun i ↦ f ^ ((⨆ i, n i) - n i) • t' i, fun i ↦ ?_⟩
      conv_lhs => rw [hN i]
      rw [pow_add, mul_smul, ht', M.map_smul_Spec]

    obtain ⟨K, hK⟩ : ∃ (K : ℕ), ∀ (i j : ι),
        M.presheaf.map (homOfLE (schemeBasicOpen_mul_le_left (g i) (g j))).op (f ^ K • t i) =
          M.presheaf.map (homOfLE (schemeBasicOpen_mul_le_right (g i) (g j))).op (f ^ K • t j) := by
      have (i j : ι) : ∃ (m : ℕ),
          M.presheaf.map (homOfLE (schemeBasicOpen_mul_le_left (g i) (g j))).op (f ^ m • t i) =
            M.presheaf.map (homOfLE (schemeBasicOpen_mul_le_right (g i) (g j))).op (f ^ m • t j) := by
        have := (h₂ i j).uniqueness (f * (g i * g j)) (schemeBasicOpen_mul_le_right _ _)
          (M.presheaf.map (homOfLE (schemeBasicOpen_mul_le_left (g i) (g j))).op (t i) -
            M.presheaf.map (homOfLE (schemeBasicOpen_mul_le_right (g i) (g j))).op (t j)) ?_
        · obtain ⟨m, hm⟩ := this
          use m
          apply (schemeIsSMulRegular M le_rfl).pow m
          simpa [M.map_smul_Spec _ (f ^ m), ← mul_smul, ← mul_smul, ← mul_pow, ← mul_comm f,
            smul_sub, sub_eq_zero] using hm
        · have hfgigi : schemeBasicOpen (f * (g i * g j)) ≤ schemeBasicOpen (f * g i) := by
            rw [← mul_assoc]
            exact schemeBasicOpen_mul_le_left _ _
          have hfgigj : schemeBasicOpen (f * (g i * g j)) ≤ schemeBasicOpen (f * g j) := by
            rw [mul_comm (g i) (g j), ← mul_assoc]
            exact schemeBasicOpen_mul_le_left _ _
          rw [map_sub, ← M.presheaf.map_comp_apply, ← op_comp, ← M.presheaf.map_comp_apply,
            ← op_comp, homOfLE_comp, homOfLE_comp, ← homOfLE_comp hfgigi (hfgi i),
            ← homOfLE_comp hfgigj (hfgi j), op_comp, M.presheaf.map_comp_apply, ← ht i,
            M.map_smul_Spec, ← M.presheaf.map_comp_apply, ← op_comp, homOfLE_comp, op_comp,
            M.presheaf.map_comp_apply, ← ht j, M.map_smul_Spec, ← M.presheaf.map_comp_apply,
            ← op_comp, homOfLE_comp]
          simp
      choose m hm using this
      let K := ⨆ i, ⨆ j, m i j
      refine ⟨K, fun i j ↦ ?_⟩
      have : m i j ≤ K :=
        le_ciSup_of_le (Finite.bddAbove_range _) i (le_ciSup (Finite.bddAbove_range _) _)
      have : K = (K - m i j) + m i j := by lia
      rw [this, pow_add, mul_smul, mul_smul, M.map_smul_Spec, M.map_smul_Spec _ (f ^ (K - m i j)),
        hm i j]

    refine ⟨N + K, ?_⟩
    have := TopCat.Sheaf.existsUnique_gluing' ⟨_, M.isSheaf⟩ (fun i ↦ schemeBasicOpen (g i)) V
      (fun i ↦ homOfLE (by rw [hg]; exact le_iSup_of_le _ le_rfl)) (by simp [hg])
      (fun i ↦ f ^ K • t i) ?_
    · obtain ⟨a, ha, -⟩ := this
      use a
      refine TopCat.Sheaf.eq_of_locally_eq' ⟨_, M.isSheaf⟩ (fun i ↦ schemeBasicOpen (f * g i)) _
          (fun i ↦ homOfLE (schemeBasicOpen_mul_le_left f (g i))) ?_ _ _ ?_
      · rw [left_eq_inf.mpr hf, hg, inf_iSup_eq]
        simp_rw [schemeBasicOpen_mul]
        exact le_rfl
      · intro i
        rw [← M.presheaf.map_comp_apply, ← op_comp, homOfLE_comp,
          ← homOfLE_comp (schemeBasicOpen_mul_le_right _ _) (hgle i), op_comp, M.presheaf.map_comp_apply,
          M.map_smul_Spec, ha, M.map_smul_Spec, pow_add, mul_smul, smul_comm, ht i]
    · intro i j
      have : Function.Injective (M.presheaf.map (eqToHom <| (schemeBasicOpen_mul (g i) (g j))).op) :=
        ConcreteCategory.injective_of_mono_of_preservesPullback _
      apply this
      dsimp [Opens.infLELeft, Opens.infLERight]
      simp_rw [← M.presheaf.map_comp_apply, ← op_comp, eqToHom_comp_homOfLE]
      exact hK i j
  · have (i : ι) : ∃ (n : ℕ), M.presheaf.map (homOfLE (hgle i)).op (f ^ n • t) = 0 := by
      have := (h₁ i).uniqueness (f * g i) (schemeBasicOpen_mul_le_right f (g i))
        (M.presheaf.map (homOfLE (hgle i)).op t) ?_
      · obtain ⟨n, hn⟩ := this
        use n
        rw [mul_pow, mul_comm, mul_smul, ← Scheme.Modules.map_smul_Spec] at hn
        exact ((schemeIsSMulRegular M le_rfl).pow n).right_eq_zero_of_smul hn
      · rw [← M.presheaf.map_comp_apply, ← op_comp, homOfLE_comp,
          ← homOfLE_comp ((schemeBasicOpen_mul_le_left f (g i))) hf, op_comp, M.presheaf.map_comp_apply]
        simp [hs]
    choose n hn using this
    use ⨆ i, n i
    apply TopCat.Sheaf.eq_of_locally_eq' ⟨_, M.isSheaf⟩ (fun i ↦ schemeBasicOpen (g i)) _
      (fun i ↦ homOfLE (by rw [hg]; exact le_iSup_of_le _ le_rfl))
    · simp [hg]
    · intro i
      have : n i ≤ ⨆ i, n i := le_ciSup (Finite.bddAbove_range _) _
      have : ⨆ i, n i = ((⨆ i, n i) - n i) + n i := by lia
      rw [this, pow_add, mul_smul, Scheme.Modules.map_smul_Spec, hn i]
      simp

lemma isLocalizing_iff_aux (M : (Spec R).Modules) :
    IsLocalizing (modulesSpecToSheaf.obj M) ↔ Aux M ⊤ := by
  let φ (f : R) := ((modulesSpecToSheaf.obj M).obj.map (schemeBasicOpen f).leTop.op).hom
  refine ⟨fun h ↦ ?_, fun h f ↦ IsLocalizedModule.Away.mk_of_addCommGroup ?_ ?_ ?_⟩
  · have hf (f : R) : IsLocalizedModule.Away f (φ f) := h f
    refine ⟨fun f hle s ↦ ?_, fun f hle s hs ↦ ?_⟩
    · obtain ⟨n, y, hy⟩ := (hf f).surj _ _ s
      use n, y, hy.symm
    · obtain ⟨⟨_, n, rfl⟩, hn⟩ := (IsLocalizedModule.eq_zero_iff (.powers f) (φ f)).mp hs
      use n, hn
  · exact Scheme.Modules.isUnit_algebraMap_end_of_le_basicOpen f le_rfl
  · intro x
    obtain ⟨n, t, ht⟩ := h.existence _ _ x
    use n, t, ht.symm
  · intro x hx
    obtain ⟨n, hn⟩ := h.uniqueness _ _ _ hx
    use n, hn

theorem aux_of_isCompact (V : (Spec R).Opens) (hV : IsCompact (V : Set (Spec R)))
    (h : IsLocalizing (modulesSpecToSheaf.obj M)) : Aux M V := by
  obtain ⟨ι, hι, g, hg⟩ := PrimeSpectrum.isBasis_basic_opens.exists_iSup_eq_of_isCompact V hV
  let := hι
  exact Aux.of_eq_iSup_basicOpen V g hg (fun i =>
    Aux.of_le (g i) le_top ((isLocalizing_iff_aux M).mp h))

variable {M}

def res (U V : (Spec R).Opens) (h : U ≤ V) : Γ(M,V) →ₗ[R] Γ(M,U) :=
  ((modulesSpecToSheaf.obj M).obj.map (homOfLE h).op).hom

lemma res_comp {U V W : (Spec R).Opens} (h : U ≤ V) (k : V ≤ W) (s : Γ(M,W)) :
    res U V h (M := M) (res V W k s) = res U W (h.trans k) s := by
  exact (M.presheaf.map_comp_apply (homOfLE k).op (homOfLE h).op s).symm

lemma eq_zero_of_cover {ι : Type*} (g : ι → R) (U : (Spec R).Opens)
    (hU : U = ⨆ i, schemeBasicOpen (g i)) (s : Γ(M,U))
    (h : ∀ i, res (schemeBasicOpen (g i)) U (hU ▸ le_iSup_of_le i le_rfl) s = 0) : s = 0 := by
  apply TopCat.Sheaf.eq_of_locally_eq' ⟨_, M.isSheaf⟩ (fun i => schemeBasicOpen (g i)) U
    (fun i => homOfLE (hU ▸ le_iSup_of_le i le_rfl)) (by rw [hU])
  intro i
  change res (schemeBasicOpen (g i)) U _ s = res (schemeBasicOpen (g i)) U _ 0
  rw [map_zero]
  exact h i

lemma power_in_ideal_of_generator_powers {ι : Type*} [Finite ι]
    (g : ι → R) (J : Ideal R) (h : ∀ i, ∃ n : ℕ, g i ^ n ∈ J) :
    ∃ n : ℕ, Ideal.span (Set.range g) ^ n ≤ J := by
  apply Ideal.exists_pow_le_of_le_radical_of_fg
  · apply Ideal.span_le.mpr
    rintro _ ⟨i,rfl⟩
    exact h i
  · exact Submodule.fg_span (Set.finite_range g)

lemma kernel_is_torsion {ι : Type*} [Finite ι] (g : ι → R) (U : (Spec R).Opens)
    (hU : U = ⨆ i, schemeBasicOpen (g i))
    (hloc : IsLocalizing (modulesSpecToSheaf.obj M)) (s : Γ(M,⊤))
    (hs : res U ⊤ le_top s = 0) :
    ∃ n : ℕ, ∀ a ∈ Ideal.span (Set.range g) ^ n, a • s = 0 := by
  let J : Ideal R := (LinearMap.toSpanSingleton R Γ(M,⊤) s).ker
  have hgen : ∀ i, ∃ n : ℕ, g i ^ n ∈ J := by
    intro i
    apply ((isLocalizing_iff_aux M).mp hloc).uniqueness (g i) le_top s
    change res (schemeBasicOpen (g i)) ⊤ le_top s = 0
    rw [← res_comp (hU ▸ le_iSup_of_le i le_rfl) le_top, hs, map_zero]
  obtain ⟨n,hn⟩ := power_in_ideal_of_generator_powers g J hgen
  exact ⟨n,fun a ha => hn ha⟩

lemma torsion_free {ι : Type*} (g : ι → R) (U : (Spec R).Opens)
    (hU : U = ⨆ i, schemeBasicOpen (g i)) (s : Γ(M,U))
    (hs : ∃ n : ℕ, ∀ a ∈ Ideal.span (Set.range g) ^ n, a • s = 0) : s = 0 := by
  obtain ⟨n,hn⟩ := hs
  apply eq_zero_of_cover g U hU s
  intro i
  have hm : g i ^ n ∈ Ideal.span (Set.range g) ^ n :=
    Ideal.pow_mem_pow (Ideal.subset_span (Set.mem_range_self i)) n
  have h := congrArg (res (schemeBasicOpen (g i)) U (hU ▸ le_iSup_of_le i le_rfl)) (hn _ hm)
  rw [map_smul, map_zero] at h
  exact ((schemeIsSMulRegular M le_rfl).pow n).right_eq_zero_of_smul h

lemma torsion_in_kernel {ι : Type*} (g : ι → R) (U : (Spec R).Opens)
    (hU : U = ⨆ i, schemeBasicOpen (g i)) (s : Γ(M,⊤))
    (hs : ∃ n : ℕ, ∀ a ∈ Ideal.span (Set.range g) ^ n, a • s = 0) :
    res U ⊤ le_top s = 0 := by
  apply torsion_free g U hU
  obtain ⟨n,hn⟩ := hs
  refine ⟨n,fun a ha => ?_⟩
  rw [← map_smul, hn a ha, map_zero]

lemma cokernel_is_torsion {ι : Type*} [Finite ι] (g : ι → R) (U : (Spec R).Opens)
    (hU : U = ⨆ i, schemeBasicOpen (g i)) (hU' : IsCompact (U : Set (Spec R)))
    (hloc : IsLocalizing (modulesSpecToSheaf.obj M)) (s : Γ(M,U)) :
    ∃ n : ℕ, ∀ a ∈ Ideal.span (Set.range g) ^ n,
      a • s ∈ (res U ⊤ le_top (M := M)).range := by
  let J : Ideal R := (res U ⊤ le_top (M := M)).range.comap
    (LinearMap.toSpanSingleton R Γ(M,U) s)
  have hgen : ∀ i, ∃ n : ℕ, g i ^ n ∈ J := by
    intro i
    let hgi : schemeBasicOpen (g i) ≤ U := hU ▸ le_iSup_of_le i le_rfl
    obtain ⟨m,t,ht⟩ := ((isLocalizing_iff_aux M).mp hloc).existence (g i) le_top
      (res (schemeBasicOpen (g i)) U hgi s)
    have hzero : res (schemeBasicOpen (g i)) U hgi (res U ⊤ le_top t - g i ^ m • s) = 0 := by
      rw [map_sub, map_smul, res_comp]
      exact sub_eq_zero.mpr ht
    obtain ⟨n,hn⟩ := (aux_of_isCompact M U hU' hloc).uniqueness (g i) hgi _ hzero
    refine ⟨n+m, ?_⟩
    change g i ^ (n+m) • s ∈ (res U ⊤ le_top (M := M)).range
    refine ⟨g i ^ n • t, ?_⟩
    rw [map_smul, pow_add, mul_smul]
    exact sub_eq_zero.mp (by simpa only [smul_sub] using hn)
  obtain ⟨n,hn⟩ := power_in_ideal_of_generator_powers g J hgen
  exact ⟨n,fun a ha => hn ha⟩

end AffineDenominators

end

namespace TildeFlasque
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace Opposite
open AffineDenominators AdicInjective InjectiveRange
universe u
variable {R : CommRingCat.{u}} [IsNoetherianRing R]
variable (M : (Spec R).Modules)

theorem top_surjective (hloc : IsLocalizing (modulesSpecToSheaf.obj M))
    [Module.Injective R Γ(M,⊤)] (U : (Spec R).Opens) :
    Function.Surjective (res U ⊤ le_top (M := M)) := by
  have hU : IsCompact (U : Set (Spec R)) := NoetherianSpace.isCompact _
  obtain ⟨ι, hι, g, hg⟩ := PrimeSpectrum.isBasis_basic_opens.exists_iSup_eq_of_isCompact U hU
  let := hι
  let I : Ideal R := Ideal.span (Set.range g)
  let r := res U ⊤ le_top (M := M)
  have hk : r.ker = adicTorsion I Γ(M,⊤) := by
    ext s
    change r s = 0 ↔ s ∈ adicTorsion I Γ(M,⊤)
    rw [mem_adicTorsion]
    exact ⟨kernel_is_torsion g U hg hloc s, torsion_in_kernel g U hg s⟩
  have hi : Module.Injective R (adicTorsion I Γ(M,⊤)) := adicTorsion_injective I Γ(M,⊤)
  let : Module.Injective R r.ker := Module.Baer.injective
    (Module.Baer.of_equiv (LinearEquiv.ofEq _ _ hk.symm) (Module.Baer.of_injective hi))
  apply surjective_of_torsion_cokernel I r
  · exact fun s => cokernel_is_torsion g U hg hU hloc s
  · exact fun s => torsion_free g U hg s

theorem flasque_of_injective_global (hloc : IsLocalizing (modulesSpecToSheaf.obj M))
    [Module.Injective R Γ(M,⊤)] :
    TopCat.Sheaf.IsFlasque ((SheafOfModules.toSheaf (Spec R).ringCatSheaf).obj M) where
  epi {U V} i := by
    apply (AddCommGrpCat.epi_iff_surjective _).mpr
    intro s
    obtain ⟨t,ht⟩ := top_surjective M hloc V.unop s
    refine ⟨res U.unop ⊤ le_top t, ?_⟩
    change res V.unop U.unop (leOfHom i.unop) (res U.unop ⊤ le_top t) = s
    rw [res_comp]
    exact ht

instance tilde_injective_isFlasque (N : ModuleCat.{u} R) [Module.Injective R N] :
    TopCat.Sheaf.IsFlasque
      ((SheafOfModules.toSheaf (Spec R).ringCatSheaf).obj (tilde N)) := by
  let : Module.Injective R Γ(tilde N,⊤) := Module.Baer.injective
    (Module.Baer.of_equiv (asIso (tilde.toOpen N ⊤)).toLinearEquiv
      (Module.Baer.of_injective inferInstance))
  exact flasque_of_injective_global (tilde N) (isLocalizing_tilde N)

end TildeFlasque

namespace TildeExact
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
universe u
variable {R : CommRingCat.{u}}

instance map_mono {M N : ModuleCat.{u} R} (f : M ⟶ N) [Mono f] : Mono (tilde.map f) := by
  apply (SheafOfModules.forget _).mono_of_mono_map
  apply PresheafOfModules.mono_of_injective
  intro U s t h
  apply Subtype.ext
  funext x
  apply LocalizedModule.map_injective x.1.asIdeal.primeCompl f.hom
    ((ModuleCat.mono_iff_injective f).mp inferInstance)
  exact congrFun (congrArg Subtype.val h) x

instance preservesMonomorphisms : (tilde.functor R).PreservesMonomorphisms where
  preserves f _ := map_mono f

instance preservesHomology : (tilde.functor R).PreservesHomology :=
  (tilde.functor R).preservesHomology_of_preservesMonos_and_cokernels

instance preservesFiniteLimits : PreservesFiniteLimits (tilde.functor R) :=
  (tilde.functor R).preservesFiniteLimits_of_preservesHomology

end TildeExact

namespace ModuleGrothendieck
open CategoryTheory CategoryTheory.Limits
universe u
variable {C : Type u} [Category.{u} C] (R₀ : Cᵒᵖ ⥤ RingCat.{u})

instance presheafAB5 : AB5 (PresheafOfModules.{u} R₀) where
  ofShape J _ _ := HasExactColimitsOfShape.domain_of_functor J
    (PresheafOfModules.toPresheaf R₀)

instance presheafHasSeparator : HasSeparator (PresheafOfModules.{u} R₀) :=
  ⟨⟨∐ (yoneda ⋙ PresheafOfModules.free R₀).obj,
    (PresheafOfModules.freeYoneda.isSeparating R₀).isSeparator_coproduct⟩⟩

instance presheafGrothendieck : IsGrothendieckAbelian.{u} (PresheafOfModules.{u} R₀) where

variable {J : GrothendieckTopology C} (R : Sheaf J RingCat.{u})
  [HasSheafify J AddCommGrpCat.{u}]

instance sheafAB5 : AB5 (SheafOfModules.{u} R) where
  ofShape K _ _ :=
    (PresheafOfModules.sheafificationAdjunction (𝟙 R.obj)).hasExactColimitsOfShape K

lemma freeSheafSeparating :
    ObjectProperty.IsSeparating (.ofObj (fun U : C =>
      (PresheafOfModules.sheafification (𝟙 R.obj)).obj
        ((PresheafOfModules.free R.obj).obj (yoneda.obj U)))) := by
  let adj := PresheafOfModules.sheafificationAdjunction (𝟙 R.obj)
  intro M N f g h
  apply (SheafOfModules.forget R ⋙ PresheafOfModules.restrictScalars (𝟙 R.obj)).map_injective
  apply PresheafOfModules.freeYoneda.isSeparating R.obj
  intro P hP a
  obtain ⟨U⟩ := hP
  obtain ⟨b, rfl⟩ := (adj.homEquiv _ _).surjective a
  rw [← Adjunction.homEquiv_naturality_right, ← Adjunction.homEquiv_naturality_right]
  exact congrArg (adj.homEquiv _ _) (h _ ⟨U⟩ b)

instance sheafHasSeparator : HasSeparator (SheafOfModules.{u} R) :=
  ⟨⟨∐ (fun U : C => (PresheafOfModules.sheafification (𝟙 R.obj)).obj
    ((PresheafOfModules.free R.obj).obj (yoneda.obj U))),
    (freeSheafSeparating R).isSeparator_coproduct⟩⟩

instance sheafGrothendieck : IsGrothendieckAbelian.{u} (SheafOfModules.{u} R) where

theorem enoughInjectives : EnoughInjectives (SheafOfModules.{u} R) := inferInstance

end ModuleGrothendieck

namespace ModuleFlasque
open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
universe u
variable {X : TopCat.{u}}
  (R : Sheaf (Opens.grothendieckTopology X) RingCat.{u})

abbrev freeOpen (U : Opens X) : SheafOfModules.{u} R :=
  (PresheafOfModules.sheafification (𝟙 R.obj)).obj
    ((PresheafOfModules.free R.obj).obj (yoneda.obj U))

abbrev freeOpenMap {U V : Opens X} (i : U ⟶ V) : freeOpen R U ⟶ freeOpen R V :=
  (PresheafOfModules.sheafification (𝟙 R.obj)).map
    ((PresheafOfModules.free R.obj).map (yoneda.map i))

lemma freeMap_mono {F G : (Opens X)ᵒᵖ ⥤ Type u} (f : F ⟶ G) [Mono f] :
    Mono ((PresheafOfModules.free R.obj).map f) := by
  apply PresheafOfModules.mono_of_injective
  intro W
  change Function.Injective (Finsupp.mapDomain (f.app W))
  exact Finsupp.mapDomain_injective ((CategoryTheory.mono_iff_injective (f.app W)).mp
    inferInstance)

instance freeOpenMap_mono {U V : Opens X} (i : U ⟶ V) : Mono (freeOpenMap R i) := by
  let := freeMap_mono R (yoneda.map i)
  dsimp [freeOpenMap]
  infer_instance

def freeOpenEquiv (M : SheafOfModules.{u} R) (U : Opens X) :
    (freeOpen R U ⟶ M) ≃ M.val.obj (op U) :=
  (PresheafOfModules.sheafificationHomEquiv (𝟙 R.obj)).trans
    PresheafOfModules.freeYonedaEquiv

lemma freeYoneda_naturality {M : PresheafOfModules.{u} R.obj} {U V : Opens X}
    (i : U ⟶ V) (f : (PresheafOfModules.free R.obj).obj (yoneda.obj V) ⟶ M) :
    PresheafOfModules.freeYonedaEquiv
      ((PresheafOfModules.free R.obj).map (yoneda.map i) ≫ f) =
      M.map i.op (PresheafOfModules.freeYonedaEquiv f) := by
  have h := (PresheafOfModules.freeAdjunction R.obj).homEquiv_naturality_left
    (yoneda.map i) f
  simp only [PresheafOfModules.freeAdjunction_homEquiv] at h
  exact (congrArg yonedaEquiv h).trans
    (yonedaEquiv_naturality (PresheafOfModules.freeHomEquiv f) i).symm

lemma freeOpenEquiv_naturality (M : SheafOfModules.{u} R) {U V : Opens X}
    (i : U ⟶ V) (f : freeOpen R V ⟶ M) :
    freeOpenEquiv R M U (freeOpenMap R i ≫ f) =
      M.val.map i.op (freeOpenEquiv R M V f) := by
  unfold freeOpenEquiv
  dsimp only [Equiv.trans_apply]
  change PresheafOfModules.freeYonedaEquiv
    ((PresheafOfModules.sheafificationAdjunction (𝟙 R.obj)).homEquiv _ _ (_ ≫ f)) = _
  rw [Adjunction.homEquiv_naturality_left]
  exact freeYoneda_naturality R i
    ((PresheafOfModules.sheafificationHomEquiv (𝟙 R.obj)) f)

theorem restriction_surjective (M : SheafOfModules.{u} R) [Injective M]
    {U V : Opens X} (i : U ⟶ V) : Function.Surjective (M.val.map i.op) := by
  intro s
  let f := (freeOpenEquiv R M U).symm s
  obtain ⟨g, hg⟩ := Injective.factors f (freeOpenMap R i)
  refine ⟨freeOpenEquiv R M V g, ?_⟩
  rw [← freeOpenEquiv_naturality, hg]
  exact (freeOpenEquiv R M U).apply_symm_apply s

instance injective_isFlasque (M : SheafOfModules.{u} R) [Injective M] :
    TopCat.Sheaf.IsFlasque ((SheafOfModules.toSheaf R).obj M) where
  epi {U V} i := by
    apply (AddCommGrpCat.epi_iff_surjective _).mpr
    exact restriction_surjective R M i.unop

end ModuleFlasque

abbrev schemeFreeOpen (X : AlgebraicGeometry.Scheme) (U : X.Opens) : X.Modules :=
  ModuleFlasque.freeOpen X.ringCatSheaf U

namespace ModuleSheafExact
open CategoryTheory CategoryTheory.Limits
universe u
variable {C : Type u} [Category.{u} C] {J : GrothendieckTopology C}
  (R : Sheaf J RingCat.{u}) [HasSheafify J AddCommGrpCat.{u}]

instance toSheafPreservesColimit {K : Type u} [Category.{u} K]
    (D : K ⥤ SheafOfModules.{u} R) : PreservesColimit D (SheafOfModules.toSheaf R) := by
  let F := PresheafOfModules.sheafification (𝟙 R.obj)
  let G := SheafOfModules.forget R ⋙ PresheafOfModules.restrictScalars (𝟙 R.obj)
  let H := SheafOfModules.toSheaf R
  let adj : F ⊣ G := PresheafOfModules.sheafificationAdjunction (𝟙 R.obj)
  have : PreservesColimitsOfSize.{u,u} (F ⋙ H) :=
    inferInstanceAs (PreservesColimitsOfSize.{u,u}
      (PresheafOfModules.toPresheaf R.obj ⋙ presheafToSheaf J AddCommGrpCat))
  have : PreservesColimit (D ⋙ G ⋙ F) H :=
    preservesColimit_of_preserves_colimit_cocone
      (isColimitOfPreserves F (colimit.isColimit (D ⋙ G)))
      (isColimitOfPreserves (F ⋙ H) (colimit.isColimit (D ⋙ G)))
  exact preservesColimit_of_iso_diagram H
    ((Functor.isoWhiskerLeft D (asIso adj.counit)) ≪≫ D.rightUnitor)

instance toSheafPreservesColimits :
    PreservesColimitsOfSize.{u,u} (SheafOfModules.toSheaf.{u} R) where
  preservesColimitsOfShape := ⟨fun {_} => inferInstance⟩

theorem shortExact_map {S : ShortComplex (SheafOfModules.{u} R)} (hS : S.ShortExact) :
    (S.map (SheafOfModules.toSheaf R)).ShortExact := hS.map_of_exact _

end ModuleSheafExact

namespace FlasqueCohomology
open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open Abelian
universe u
variable {X : TopCat.{u}}
  (R : Sheaf (Opens.grothendieckTopology X) RingCat.{u})

def sectionsTopEquiv (M : SheafOfModules.{u} R) : M.sections ≃ M.val.obj (op ⊤) where
  toFun s := s.val (op ⊤)
  invFun t := PresheafOfModules.sectionsMk
    (fun U => M.val.map (homOfLE le_top).op t)
    (by
      intro U V i
      rw [← M.val.map_comp_apply]
      exact M.val.congr_map_apply (Subsingleton.elim _ _) t)
  left_inv s := by
    apply PresheafOfModules.sections_ext
    intro U
    exact s.property (homOfLE le_top).op
  right_inv t := by
    change M.val.map (𝟙 (op ⊤)) t = t
    rw [M.val.map_id]
    rfl

def globalHomEquiv (M : SheafOfModules.{u} R) :
    (SheafOfModules.unit R ⟶ M) ≃ M.val.obj (op ⊤) :=
  M.unitHomEquiv.trans (sectionsTopEquiv R M)

lemma globalHomEquiv_comp {M N : SheafOfModules.{u} R}
    (f : SheafOfModules.unit R ⟶ M) (g : M ⟶ N) :
    globalHomEquiv R N (f ≫ g) = g.val.app (op ⊤) (globalHomEquiv R M f) := rfl

theorem globalHom_surjective {S : ShortComplex (SheafOfModules.{u} R)}
    (hS : S.ShortExact)
    [TopCat.Sheaf.IsFlasque ((SheafOfModules.toSheaf R).obj S.X₁)] :
    Function.Surjective (fun f : SheafOfModules.unit R ⟶ S.X₂ => f ≫ S.g) := by
  have h := ModuleSheafExact.shortExact_map R hS
  let : TopCat.Sheaf.IsFlasque ((S.map (SheafOfModules.toSheaf R)).X₁) :=
    ‹TopCat.Sheaf.IsFlasque ((SheafOfModules.toSheaf R).obj S.X₁)›
  have he := TopCat.Sheaf.IsFlasque.epi_of_shortExact (U := ⊤) h
  have hs := (AddCommGrpCat.epi_iff_surjective
    (((SheafOfModules.toSheaf R).map S.g).hom.app (op ⊤))).mp he
  intro f
  obtain ⟨t, ht⟩ := hs (globalHomEquiv R S.X₃ f)
  let t' : S.X₂.val.obj (op ⊤) := t
  have ht' : S.g.val.app (op ⊤) t' = globalHomEquiv R S.X₃ f := ht
  refine ⟨(globalHomEquiv R S.X₂).symm t', ?_⟩
  apply (globalHomEquiv R S.X₃).injective
  erw [globalHomEquiv_comp, Equiv.apply_symm_apply]
  exact ht'

instance moduleSheafHasExt : HasExt.{u+1} (SheafOfModules.{u} R) :=
  HasExt.standard _

theorem flasque_ext_zero (n : ℕ) (M : SheafOfModules.{u} R)
    [TopCat.Sheaf.IsFlasque ((SheafOfModules.toSheaf R).obj M)]
    (x : Ext.{u+1} (SheafOfModules.unit R) M (n+1)) : x = 0 := by
  induction n generalizing M with
  | zero =>
    let S := ShortComplex.mk _ _ (cokernel.condition (Injective.ι M))
    have hS : S.ShortExact :=
      { exact := ShortComplex.exact_of_g_is_cokernel _ (cokernelIsCokernel S.f) }
    obtain ⟨y, hy⟩ := Ext.covariant_sequence_exact₁ (SheafOfModules.unit R) hS x
      (Ext.eq_zero_of_injective _) rfl
    obtain ⟨f, rfl⟩ := (Ext.mk₀_bijective _ _).surjective y
    obtain ⟨g, rfl⟩ := globalHom_surjective R hS f
    rw [← Ext.mk₀_comp_mk₀, Ext.comp_assoc_of_second_deg_zero,
      hS.comp_extClass, Ext.comp_zero] at hy
    exact hy.symm
  | succ n ih =>
    let S := ShortComplex.mk _ _ (cokernel.condition (Injective.ι M))
    have hS : S.ShortExact :=
      { exact := ShortComplex.exact_of_g_is_cokernel _ (cokernelIsCokernel S.f) }
    let : TopCat.Sheaf.IsFlasque ((S.map (SheafOfModules.toSheaf R)).X₁) :=
      ‹TopCat.Sheaf.IsFlasque ((SheafOfModules.toSheaf R).obj M)›
    let : TopCat.Sheaf.IsFlasque ((S.map (SheafOfModules.toSheaf R)).X₂) :=
      ModuleFlasque.injective_isFlasque R (Injective.under M)
    have : TopCat.Sheaf.IsFlasque ((SheafOfModules.toSheaf R).obj S.X₃) :=
      TopCat.Sheaf.IsFlasque.of_shortExact_of_isFlasque₁₂
        (ModuleSheafExact.shortExact_map R hS)
    obtain ⟨y, hy⟩ := Ext.covariant_sequence_exact₁ (SheafOfModules.unit R) hS x
      (Ext.eq_zero_of_injective _) rfl
    rw [ih S.X₃ y, Ext.zero_comp] at hy
    exact hy.symm

end FlasqueCohomology

namespace AffineCohomology
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite Abelian
open FlasqueCohomology
universe u
variable {R : CommRingCat.{u}}

lemma globalHom_tilde_surjective {M N : ModuleCat.{u} R} (g : M ⟶ N) [Epi g] :
    Function.Surjective (fun f : schemeUnit (Spec R) ⟶ tilde M =>
      f ≫ tilde.map g) := by
  intro f
  obtain ⟨q,hq⟩ := (ConcreteCategory.bijective_of_isIso (tilde.toOpen N ⊤)).surjective
    (globalHomEquiv (Spec R).ringCatSheaf (tilde N) f)
  obtain ⟨p,hp⟩ := (ModuleCat.epi_iff_surjective g).mp inferInstance q
  refine ⟨(globalHomEquiv (Spec R).ringCatSheaf (tilde M)).symm (tilde.toOpen M ⊤ p), ?_⟩
  apply (globalHomEquiv (Spec R).ringCatSheaf (tilde N)).injective
  erw [globalHomEquiv_comp, Equiv.apply_symm_apply]
  change ((modulesSpecToSheaf.map (tilde.map g)).hom.app (op ⊤)) (tilde.toOpen M ⊤ p) = _
  have h := CategoryTheory.congr_fun (tilde.toOpen_map_app g ⊤) p
  exact h.trans (by change tilde.toOpen N ⊤ (g p) = _; rw [hp, hq])

local instance affineHasExt : HasExt.{u+1} (Spec R).Modules := HasExt.standard _

theorem tilde_ext_zero [IsNoetherianRing R] (n : ℕ) (M : ModuleCat.{u} R)
    (x : Ext.{u+1} (C := (Spec R).Modules) (schemeUnit (Spec R)) (tilde M) (n+1)) : x = 0 := by
  induction n generalizing M with
  | zero =>
    let S := ShortComplex.mk _ _ (cokernel.condition (Injective.ι M))
    have hS : S.ShortExact :=
      { exact := ShortComplex.exact_of_g_is_cokernel _ (cokernelIsCokernel S.f) }
    let T := S.map (tilde.functor R)
    have hT : T.ShortExact := hS.map (tilde.functor R)
    let : Injective S.X₂ := (inferInstance : Injective (Injective.under M))
    let : Module.Injective R S.X₂ := Module.injective_module_of_injective_object R S.X₂
    obtain ⟨y,hy⟩ := Ext.covariant_sequence_exact₁ _ hT x
      (flasque_ext_zero (Spec R).ringCatSheaf 0 (tilde S.X₂) _) rfl
    obtain ⟨f,rfl⟩ := (Ext.mk₀_bijective _ _).surjective y
    obtain ⟨g,rfl⟩ := globalHom_tilde_surjective S.g f
    erw [← Ext.mk₀_comp_mk₀, Ext.comp_assoc_of_second_deg_zero,
      show (Ext.mk₀ (tilde.map S.g)).comp hT.extClass rfl = 0 from hT.comp_extClass,
      Ext.comp_zero] at hy
    exact hy.symm
  | succ n ih =>
    let S := ShortComplex.mk _ _ (cokernel.condition (Injective.ι M))
    have hS : S.ShortExact :=
      { exact := ShortComplex.exact_of_g_is_cokernel _ (cokernelIsCokernel S.f) }
    let T := S.map (tilde.functor R)
    have hT : T.ShortExact := hS.map (tilde.functor R)
    let : Injective S.X₂ := (inferInstance : Injective (Injective.under M))
    let : Module.Injective R S.X₂ := Module.injective_module_of_injective_object R S.X₂
    obtain ⟨y,hy⟩ := Ext.covariant_sequence_exact₁ _ hT x
      (flasque_ext_zero (Spec R).ringCatSheaf (n+1) (tilde S.X₂) _) rfl
    erw [ih S.X₃ y, Ext.zero_comp] at hy
    exact hy.symm

theorem quasicoherent_ext_zero [IsNoetherianRing R] (n : ℕ) (M : (Spec R).Modules)
    [M.IsQuasicoherent]
    (x : Ext.{u+1} (C := (Spec R).Modules) (schemeUnit (Spec R)) M (n+1)) : x = 0 := by
  let e := asIso M.fromTildeΓ
  have hx := tilde_ext_zero n _ (x.comp (Ext.mk₀ e.inv) (add_zero _))
  have h := congrArg (fun y => y.comp (Ext.mk₀ e.hom) (add_zero (n+1))) hx
  simpa only [Ext.comp_assoc_of_third_deg_zero, Ext.mk₀_comp_mk₀,
    e.inv_hom_id, Ext.comp_mk₀_id, Ext.zero_comp] using h

end AffineCohomology

namespace RestrictionExact
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
universe u
variable {X Y : Scheme.{u}} (f : X ⟶ Y) [IsOpenImmersion f]

instance restriction_mono {M N : Y.Modules} (g : M ⟶ N) [Mono g] :
    Mono ((Scheme.Modules.restrictFunctor f).map g) := by
  apply (Scheme.Modules.toPresheafOfModules X).mono_of_mono_map
  apply PresheafOfModules.mono_of_injective
  intro U
  let : Mono g.val := inferInstanceAs (Mono ((Scheme.Modules.toPresheafOfModules Y).map g))
  exact PresheafOfModules.injective_of_mono g.val (op (f ''ᵁ U.unop))

instance restriction_preservesMonomorphisms :
    (Scheme.Modules.restrictFunctor f).PreservesMonomorphisms where
  preserves g _ := restriction_mono f g

instance restriction_additive : (Scheme.Modules.restrictFunctor f).Additive where
  map_add := by intros; ext; rfl

instance restriction_preservesHomology :
    (Scheme.Modules.restrictFunctor f).PreservesHomology :=
  (Scheme.Modules.restrictFunctor f).preservesHomology_of_preservesMonos_and_cokernels

instance restriction_preservesFiniteLimits :
    PreservesFiniteLimits (Scheme.Modules.restrictFunctor f) :=
  (Scheme.Modules.restrictFunctor f).preservesFiniteLimits_of_preservesHomology

instance restriction_flasque (M : Y.Modules)
    [TopCat.Sheaf.IsFlasque ((SheafOfModules.toSheaf Y.ringCatSheaf).obj M)] :
    TopCat.Sheaf.IsFlasque
      ((SheafOfModules.toSheaf X.ringCatSheaf).obj (M.restrict f)) where
  epi {U V} i := by
    change Epi (((SheafOfModules.toSheaf Y.ringCatSheaf).obj M).obj.map
      (f.opensFunctor.map i.unop).op)
    exact TopCat.Presheaf.IsFlasque.epi _

end RestrictionExact

namespace AffineSchemeCohomology
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Abelian
open Scheme.Modules
universe u

def restrictionEquivalence {X Y : Scheme.{u}} (e : X ≅ Y) : Y.Modules ≌ X.Modules :=
  CategoryTheory.Equivalence.mk (restrictFunctor e.hom) (restrictFunctor e.inv)
    ((restrictFunctorId (X := Y)).symm ≪≫ (restrictFunctorCongr e.inv_hom_id).symm ≪≫
      restrictFunctorComp e.inv e.hom)
    ((restrictFunctorComp e.hom e.inv).symm ≪≫ restrictFunctorCongr e.hom_inv_id ≪≫
      restrictFunctorId (X := X))

local instance hasExtScheme (X : Scheme.{u}) : HasExt.{u+1} X.Modules := HasExt.standard _

theorem affine_ext_zero (X : Scheme.{u}) [IsAffine X] [IsNoetherian X]
    (M : X.Modules) [M.IsQuasicoherent] (n : ℕ)
    (x : Ext.{u+1} (C := X.Modules) (schemeUnit X) M (n+1)) : x = 0 := by
  let : IsNoetherianRing Γ(X, ⊤) := IsLocallyNoetherian.component_noetherian ⟨⊤, isAffineOpen_top X⟩
  let E := restrictionEquivalence X.isoSpec.symm
  let F := E.functor
  let : F.Additive := RestrictionExact.restriction_additive _
  let : EnoughInjectives X.Modules := ModuleGrothendieck.enoughInjectives X.ringCatSheaf
  let e := restrictUnitIso X.isoSpec.inv
  let z : Ext.{u+1} (F.obj (schemeUnit X)) (F.obj M) (n+1) :=
    x.mapExactFunctor F
  have hz : z = 0 := by
    have hw := AffineCohomology.quasicoherent_ext_zero n (M.restrict X.isoSpec.inv)
      ((Ext.mk₀ e.inv).comp z (zero_add _))
    have h := congrArg (fun y => (Ext.mk₀ e.hom).comp y (zero_add (n+1))) hw
    erw [Ext.mk₀_comp_mk₀_assoc, e.hom_inv_id, Ext.mk₀_id_comp,
      Ext.comp_zero] at h
    exact h
  have hb : Function.Injective (F.mapExtAddHom (schemeUnit X) M (n+1) :
      Ext.{u+1} (C := X.Modules) (schemeUnit X) M (n+1) →
      Ext.{u+1} (F.obj (schemeUnit X)) (F.obj M) (n+1)) :=
    (F.mapExt_bijective_of_preservesInjectiveObjects _ _ (n+1)).injective
  apply hb
  simpa only [Functor.mapExtAddHom_apply, Ext.mapExactFunctor_zero] using hz

end AffineSchemeCohomology

namespace ExtSectionComparison
open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian
universe w w' v v' u u'
variable {C : Type u} [Category.{v} C] [Abelian C]
  {D : Type u'} [Category.{v'} D] [Abelian D]
  (F : C ⥤ D) [F.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F]
  [HasExt.{w} C] [HasExt.{w'} D] {A : C} {B : D} (e : B ⟶ F.obj A)

def mapFrom (Y : C) (n : ℕ) : Ext.{w} A Y n →+ Ext.{w'} B (F.obj Y) n :=
  ((Ext.mk₀ e).precomp (F.obj Y) (zero_add n)).comp (F.mapExtAddHom A Y n)

lemma mapFrom_apply (Y : C) (n : ℕ) (x : Ext.{w} A Y n) :
    mapFrom F e Y n x = (Ext.mk₀ e).comp (x.mapExactFunctor F) (zero_add n) := rfl

@[simp] lemma mapFrom_mk₀ {Y : C} (f : A ⟶ Y) :
    mapFrom F e Y 0 (Ext.mk₀ f) = Ext.mk₀ (e ≫ F.map f) := by
  simp only [mapFrom_apply, Ext.mapExactFunctor_mk₀, Ext.mk₀_comp_mk₀]

lemma mapFrom_comp {Y Z : C} {n m k : ℕ} (x : Ext.{w} A Y n)
    (y : Ext.{w} Y Z m) (h : n+m=k) :
    mapFrom F e Z k (x.comp y h) =
      (mapFrom F e Y n x).comp (y.mapExactFunctor F) h := by
  simp only [mapFrom_apply, Ext.mapExactFunctor_comp]
  exact (Ext.comp_assoc _ _ _ (zero_add _) h (by omega)).symm

theorem mapFrom_bijective [EnoughInjectives C]
    (hhom : ∀ Y : C, Function.Bijective (fun f : A ⟶ Y => e ≫ F.map f))
    (hacyclic : ∀ (I : C) [Injective I] (n : ℕ)
      (x : Ext.{w'} B (F.obj I) (n+1)), x = 0)
    (Y : C) (n : ℕ) : Function.Bijective (mapFrom F e Y n) := by
  induction n generalizing Y with
  | zero =>
    constructor
    · intro x y h
      obtain ⟨f, rfl⟩ := (Ext.mk₀_bijective _ _).surjective x
      obtain ⟨g, rfl⟩ := (Ext.mk₀_bijective _ _).surjective y
      rw [mapFrom_mk₀, mapFrom_mk₀] at h
      exact congrArg Ext.mk₀ ((hhom Y).injective ((Ext.mk₀_bijective _ _).injective h))
    · intro x
      obtain ⟨f, rfl⟩ := (Ext.mk₀_bijective _ _).surjective x
      obtain ⟨g, rfl⟩ := (hhom Y).surjective f
      exact ⟨Ext.mk₀ g, mapFrom_mk₀ F e g⟩
  | succ n ih =>
    let I : InjectivePresentation Y := Classical.arbitrary _
    let S := ShortComplex.mk _ _ (cokernel.condition I.f)
    have hS : S.ShortExact := { exact := ShortComplex.exact_cokernel I.f }
    let : Injective S.X₂ := I.injective
    refine AddMonoidHom.bijective_of_surjective_of_bijective_of_right_exact _ _ _ _
      (mapFrom F e S.X₂ n) (mapFrom F e S.X₃ n) (mapFrom F e S.X₁ (n+1))
      ?_ ?_
      ((ShortComplex.ab_exact_iff_function_exact _).mp
        (Ext.covariant_sequence_exact₃' A hS n (n+1) rfl))
      ((ShortComplex.ab_exact_iff_function_exact _).mp
        (Ext.covariant_sequence_exact₃' B (hS.map F) n (n+1) rfl))
      (ih _).surjective (ih _)
      (fun x => Ext.covariant_sequence_exact₁ A hS x (Ext.eq_zero_of_injective _) rfl)
      (fun x => Ext.covariant_sequence_exact₁ B (hS.map F) x (hacyclic S.X₂ n _) rfl)
    · ext x
      symm
      change mapFrom F e _ _ (x.comp (Ext.mk₀ S.g) (add_zero n)) =
        (mapFrom F e _ _ x).comp (Ext.mk₀ (F.map S.g)) (add_zero n)
      rw [mapFrom_comp, Ext.mapExactFunctor_mk₀]
    · ext x
      symm
      change mapFrom F e _ _ (x.comp hS.extClass rfl) =
        (mapFrom F e _ _ x).comp (hS.map F).extClass rfl
      rw [mapFrom_comp, Ext.mapExactFunctor_extClass]

end ExtSectionComparison

namespace RestrictionCohomology
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite Abelian
open ModuleFlasque FlasqueCohomology
universe u
variable {X : Scheme.{u}} (U : X.Opens)

local instance hasExtScheme (Y : Scheme.{u}) : HasExt.{u+1} Y.Modules := HasExt.standard _

lemma freeOpenEquiv_comp {M N : X.Modules}
    (f : schemeFreeOpen X U ⟶ M) (g : M ⟶ N) :
    freeOpenEquiv X.ringCatSheaf N U (f ≫ g) =
      g.val.app (op U) (freeOpenEquiv X.ringCatSheaf M U f) := rfl

def restrictionSectionsIso (M : X.Modules) : Γ(M.restrict U.ι,⊤) ≅ Γ(M,U) :=
  M.restrictAppIso U.ι ⊤ ≪≫ M.presheaf.mapIso (eqToIso U.ι_image_top.symm).op

def restrictionHomEquiv (M : X.Modules) :
    (schemeFreeOpen X U ⟶ M) ≃
      (schemeUnit U.toScheme ⟶ M.restrict U.ι) :=
  (freeOpenEquiv X.ringCatSheaf M U).trans
    ((restrictionSectionsIso U M).addCommGroupIsoToAddEquiv.toEquiv.symm.trans
      (globalHomEquiv U.toScheme.ringCatSheaf (M.restrict U.ι)).symm)

lemma restrictionHomEquiv_comp {M N : X.Modules}
    (f : schemeFreeOpen X U ⟶ M) (g : M ⟶ N) :
    restrictionHomEquiv U N (f ≫ g) =
      restrictionHomEquiv U M f ≫ (Scheme.Modules.restrictFunctor U.ι).map g := by
  have hsection (P : X.Modules) (h : schemeFreeOpen X U ⟶ P) :
      globalHomEquiv U.toScheme.ringCatSheaf (P.restrict U.ι) (restrictionHomEquiv U P h) =
        (restrictionSectionsIso U P).inv (freeOpenEquiv X.ringCatSheaf P U h) := by
    simp only [restrictionHomEquiv]
    exact (globalHomEquiv U.toScheme.ringCatSheaf (P.restrict U.ι)).apply_symm_apply _
  apply (globalHomEquiv U.toScheme.ringCatSheaf (N.restrict U.ι)).injective
  erw [globalHomEquiv_comp, hsection, hsection, freeOpenEquiv_comp]
  change (restrictionSectionsIso U N).inv (g.val.app (op U)
    (freeOpenEquiv X.ringCatSheaf M U f)) =
    ((Scheme.Modules.restrictFunctor U.ι).map g).val.app (op ⊤)
      ((restrictionSectionsIso U M).inv (freeOpenEquiv X.ringCatSheaf M U f))
  exact (CategoryTheory.congr_fun (g.mapPresheaf.naturality
    (eqToHom U.ι_image_top).op) _).symm

def restrictionGenerator : schemeUnit U.toScheme ⟶
    (Scheme.Modules.restrictFunctor U.ι).obj (schemeFreeOpen X U) :=
  restrictionHomEquiv U _ (𝟙 _)

lemma restrictionGenerator_comp {M : X.Modules}
    (f : schemeFreeOpen X U ⟶ M) :
    restrictionGenerator U ≫ (Scheme.Modules.restrictFunctor U.ι).map f =
      restrictionHomEquiv U M f := by
  simpa only [restrictionGenerator, Category.id_comp] using
    (restrictionHomEquiv_comp U (𝟙 _) f).symm

theorem restriction_ext_bijective (M : X.Modules) (n : ℕ) :
    Function.Bijective
      (ExtSectionComparison.mapFrom (Scheme.Modules.restrictFunctor U.ι)
        (restrictionGenerator U) M n :
        Ext.{u+1} (C := X.Modules) (schemeFreeOpen X U) M n →+
          Ext.{u+1} (C := U.toScheme.Modules) (schemeUnit U.toScheme) (M.restrict U.ι) n) := by
  let : EnoughInjectives X.Modules :=
    ModuleGrothendieck.enoughInjectives X.ringCatSheaf
  apply ExtSectionComparison.mapFrom_bijective
  · intro N
    have heq : (fun f : schemeFreeOpen X U ⟶ N =>
        restrictionGenerator U ≫ (Scheme.Modules.restrictFunctor U.ι).map f) =
        restrictionHomEquiv U N := funext (restrictionGenerator_comp U)
    change Function.Bijective (fun f : schemeFreeOpen X U ⟶ N =>
      restrictionGenerator U ≫ (Scheme.Modules.restrictFunctor U.ι).map f)
    rw [heq]
    exact (restrictionHomEquiv U N).bijective
  · intro I hI n x
    let : Injective (C := SheafOfModules X.ringCatSheaf) I := hI
    let : TopCat.Sheaf.IsFlasque ((SheafOfModules.toSheaf X.ringCatSheaf).obj I) :=
      ModuleFlasque.injective_isFlasque X.ringCatSheaf I
    exact flasque_ext_zero U.toScheme.ringCatSheaf n (I.restrict U.ι) x

end RestrictionCohomology

namespace ModuleMayerVietoris
open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace Abelian
open ModuleFlasque
universe u w
variable {X : TopCat.{u}} (R : Sheaf (Opens.grothendieckTopology X) RingCat.{u})

def freeOpenFunctor : Opens X ⥤ SheafOfModules.{u} R :=
  yoneda ⋙ PresheafOfModules.free R.obj ⋙ PresheafOfModules.sheafification (𝟙 R.obj)

lemma freeOpen_isPushout (U V : Opens X) :
    ((Opens.mayerVietorisSquare U V).toSquare.map (freeOpenFunctor R)).IsPushout := by
  rw [Square.isPushout_iff_op_map_yoneda_isPullback]
  intro M
  have h := (Opens.mayerVietorisSquare U V).sheafCondition_of_sheaf
    ((sheafCompose (Opens.grothendieckTopology X) (forget AddCommGrpCat)).obj
      ((SheafOfModules.toSheaf R).obj M))
  apply (Square.IsPullback.iff_of_equiv _ _
    (freeOpenEquiv R M (U ⊔ V)) (freeOpenEquiv R M U)
    (freeOpenEquiv R M V) (freeOpenEquiv R M (U ⊓ V))
    ?_ ?_ ?_ ?_).mpr h
  all_goals
    ext f
    exact freeOpenEquiv_naturality R M _ f

def shortComplex (U V : Opens X) : ShortComplex (SheafOfModules.{u} R) where
  X₁ := freeOpen R (U ⊓ V)
  X₂ := freeOpen R U ⊞ freeOpen R V
  X₃ := freeOpen R (U ⊔ V)
  f := biprod.lift (freeOpenMap R (homOfLE inf_le_left))
    (-(freeOpenMap R (homOfLE inf_le_right)))
  g := biprod.desc (freeOpenMap R (homOfLE le_sup_left))
    (freeOpenMap R (homOfLE le_sup_right))
  zero := ((Opens.mayerVietorisSquare U V).toSquare.map
    (freeOpenFunctor R)).cokernelCofork.condition

instance shortComplex_mono (U V : Opens X) : Mono (shortComplex R U V).f := by
  have : Mono ((shortComplex R U V).f ≫ biprod.snd) := by
    dsimp [shortComplex]
    simp only [biprod.lift_snd]
    infer_instance
  exact mono_of_mono _ biprod.snd

lemma shortComplex_shortExact (U V : Opens X) : (shortComplex R U V).ShortExact := by
  have h := (freeOpen_isPushout R U V).isColimitCokernelCofork
  have he : (shortComplex R U V).Exact ∧ Epi (shortComplex R U V).g :=
    (shortComplex R U V).exact_and_epi_g_iff_g_is_cokernel.mpr ⟨h⟩
  let := he.2
  exact ⟨he.1⟩

variable [HasExt.{w} (SheafOfModules.{u} R)]

lemma union_ext_zero (U V : Opens X) (M : SheafOfModules.{u} R) (n : ℕ)
    (hU : ∀ x : Ext (freeOpen R U) M (n+1), x = 0)
    (hV : ∀ x : Ext (freeOpen R V) M (n+1), x = 0)
    (hUV : ∀ x : Ext (freeOpen R (U ⊓ V)) M n, x = 0)
    (x : Ext (freeOpen R (U ⊔ V)) M (n+1)) : x = 0 := by
  have hS := shortComplex_shortExact R U V
  have hmid (y : Ext (freeOpen R U ⊞ freeOpen R V) M (n+1)) : y = 0 := by
    apply Ext.biprodAddEquiv.injective
    apply Prod.ext
    · simpa only [map_zero, Ext.biprodAddEquiv_apply_fst, Prod.fst_zero] using
        hU ((Ext.mk₀ biprod.inl).comp y (zero_add _))
    · simpa only [map_zero, Ext.biprodAddEquiv_apply_snd, Prod.snd_zero] using
        hV ((Ext.mk₀ biprod.inr).comp y (zero_add _))
  obtain ⟨z, hz⟩ := Ext.contravariant_sequence_exact₃ hS M x (hmid _) (n₀ := n) (by omega)
  have hz0 : z = 0 := hUV z
  rw [hz0, Ext.comp_zero] at hz
  exact hz.symm

end ModuleMayerVietoris

namespace FiniteCoverCohomology
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Abelian
open ModuleFlasque
universe u
variable {X : Scheme.{u}} [IsNoetherian X]

local instance hasExtScheme (Y : Scheme.{u}) : HasExt.{u+1} Y.Modules := HasExt.standard _

theorem affine_open_ext_zero (U : X.Opens) (hU : IsAffineOpen U)
    (M : X.Modules) [M.IsQuasicoherent] (n : ℕ)
    (x : Ext.{u+1} (C := X.Modules) (schemeFreeOpen X U) M (n+1)) : x = 0 := by
  let : IsAffine U := hU
  let : IsNoetherian U := ⟨⟩
  let f := ExtSectionComparison.mapFrom (Scheme.Modules.restrictFunctor U.ι)
    (RestrictionCohomology.restrictionGenerator U) M (n+1)
  apply (RestrictionCohomology.restriction_ext_bijective U M (n+1)).injective
  change f x = f 0
  rw [map_zero]
  exact AffineSchemeCohomology.affine_ext_zero U (M.restrict U.ι) n (f x)

variable [IsAffineHom (pullback.diagonal (terminal.from X))]

theorem affine_union_ext_zero (n : ℕ) (U : Fin (n+1) → X.Opens)
    (hU : ∀ i, IsAffineOpen (U i)) (M : X.Modules) [M.IsQuasicoherent] (k : ℕ)
    (x : Ext.{u+1} (C := X.Modules) (schemeFreeOpen X (⨆ i, U i)) M (n+k+1)) : x = 0 := by
  induction n generalizing k with
  | zero =>
    have hsup : (⨆ i, U i) = U 0 := by
      apply le_antisymm
      · apply iSup_le
        intro i
        have hi : i = 0 := Fin.ext (by omega)
        subst i
        exact le_rfl
      · exact le_iSup U 0
    revert x
    rw [hsup]
    exact affine_open_ext_zero (U 0) (hU 0) M (0+k)
  | succ n ih =>
    have hsup : (⨆ i, U i) = U 0 ⊔ ⨆ i : Fin (n+1), U i.succ :=
      le_antisymm (iSup_le (Fin.cases le_sup_left (fun i =>
        (le_iSup (fun i : Fin (n+1) => U i.succ) i).trans le_sup_right)))
        (sup_le (le_iSup U 0) (iSup_le (fun i => le_iSup U i.succ)))
    have hinf : U 0 ⊓ (⨆ i : Fin (n+1), U i.succ) =
        ⨆ i : Fin (n+1), U 0 ⊓ U i.succ := inf_iSup_eq _ _
    revert x
    rw [hsup, show n+1+k+1 = n+k+1+1 from by omega]
    intro x
    apply ModuleMayerVietoris.union_ext_zero X.ringCatSheaf (U 0)
      (⨆ i : Fin (n+1), U i.succ) M (n+k+1) ?_ ?_ ?_ x
    · intro y
      exact affine_open_ext_zero (U 0) (hU 0) M (n+k+1) y
    · intro y
      exact ih (fun i => U i.succ) (fun i => hU i.succ) (k+1) y
    · rw [hinf]
      intro y
      exact ih (fun i => U 0 ⊓ U i.succ) (fun i => (hU 0).inf (hU i.succ)) k y

end FiniteCoverCohomology

namespace FreeOpenUnit
open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace Abelian
open ModuleFlasque FlasqueCohomology
universe u v

def isoFromHomEquiv {C : Type u} [Category.{v} C] {A B : C}
    (e : ∀ M, (A ⟶ M) ≃ (B ⟶ M))
    (hnat : ∀ {M N} (f : A ⟶ M) (g : M ⟶ N), e N (f ≫ g) = e M f ≫ g) :
    A ≅ B where
  hom := (e B).symm (𝟙 B)
  inv := e A (𝟙 A)
  hom_inv_id := by
    apply (e A).injective
    rw [hnat, Equiv.apply_symm_apply, Category.id_comp]
  inv_hom_id := by
    rw [← hnat, Category.id_comp, Equiv.apply_symm_apply]

variable {X : TopCat.{u}} (R : Sheaf (Opens.grothendieckTopology X) RingCat.{u})

def freeTopIso : freeOpen R ⊤ ≅ SheafOfModules.unit R :=
  isoFromHomEquiv
    (fun M => (freeOpenEquiv R M ⊤).trans (globalHomEquiv R M).symm)
    (by
      intro M N f g
      apply (globalHomEquiv R N).injective
      simp only [Equiv.trans_apply, Equiv.apply_symm_apply, globalHomEquiv_comp]
      rfl)

end FreeOpenUnit

namespace FiniteCoverCohomology
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Abelian
open ModuleFlasque
universe u
variable {X : Scheme.{u}} [IsNoetherian X]
  [IsAffineHom (pullback.diagonal (terminal.from X))]

local instance hasExtScheme' (Y : Scheme.{u}) : HasExt.{u+1} Y.Modules := HasExt.standard _

theorem cover_ext_zero (n : ℕ) (U : Fin (n+1) → X.Opens)
    (hU : ∀ i, IsAffineOpen (U i)) (hcover : (⨆ i, U i) = ⊤)
    (M : X.Modules) [M.IsQuasicoherent] (k : ℕ)
    (x : Ext.{u+1} (C := X.Modules) (schemeUnit X) M (n+k+1)) : x = 0 := by
  let e := FreeOpenUnit.freeTopIso X.ringCatSheaf
  have hz : ∀ z : Ext.{u+1} (C := X.Modules) (schemeFreeOpen X ⊤) M (n+k+1), z = 0 := by
    rw [← hcover]
    exact affine_union_ext_zero n U hU M k
  have h := congrArg (fun y => (Ext.mk₀ e.inv).comp y (zero_add (n+k+1)))
    (hz ((Ext.mk₀ e.hom).comp x (zero_add _)))
  erw [Ext.mk₀_comp_mk₀_assoc, e.inv_hom_id, Ext.mk₀_id_comp,
    Ext.comp_zero] at h
  exact h

end FiniteCoverCohomology

end PiExponentSeshadri

end

end OAI
end Source0003

section Source0004
/-
Modification notice for the LogTwo project.
Derived from openai/math (Apache-2.0), revision adc7f1241b42e322a6451854ab7e4b4c146bf78a.
Original source: lean/OAI/NumberTheory/PiExponent/Geometry/LineBundleTensor.lean
Changes: Convert module/import declarations to the Lean 4.34 public module format.
See ../../../../../THIRD_PARTY_NOTICES.txt for provenance and the recorded changes.
-/




namespace OAI

noncomputable section

namespace PiExponentSeshadri

namespace Geometry
open CategoryTheory AlgebraicGeometry TopologicalSpace
open scoped AlgebraicGeometry

variable (X : Scheme)

structure LineBundle where
  sheaf : X.Modules
  locallyRankOne : ∀ x : X, ∃ U : X.Opens, x ∈ U ∧
    Nonempty (sheaf.restrict U.ι ≅ SheafOfModules.unit U.toScheme.ringCatSheaf)

def moduleTensor (M N : X.Modules) : X.Modules :=
  (PresheafOfModules.sheafification (𝟙 X.ringCatSheaf.obj)).obj
    (PresheafOfModulesOfCommRing.Monoidal.tensorObj (R := X.presheaf) M.val N.val)

def modulePow (M : X.Modules) : ℕ → X.Modules
  | 0 => SheafOfModules.unit X.ringCatSheaf
  | n + 1 => moduleTensor X M (modulePow M n)

def structureSheaf : X.Modules := SheafOfModules.unit X.ringCatSheaf

abbrev GlobalSections (M : X.Modules) := structureSheaf X ⟶ M

def sectionOpen {M : X.Modules} (s : GlobalSections X M) : X.Opens :=
  ⨆ (U : X.Opens) (_ : IsIso ((Scheme.Modules.restrictFunctor U.ι).map s)), U

def LineBundle.IsAmple (L : LineBundle X) : Prop :=
  ∀ (x : X) (V : X.Opens), x ∈ V → ∃ n : ℕ, 0 < n ∧
    ∃ s : GlobalSections X (modulePow X L.sheaf n),
      x ∈ sectionOpen X s ∧ sectionOpen X s ≤ V ∧ IsAffineOpen (sectionOpen X s)

end Geometry

open CategoryTheory
open CategoryTheory.Category CategoryTheory.Functor
universe v u v₁ v₂ u₁ u₂
namespace ModulePresheaf
open PresheafOfModules

variable {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D]
  {F G : C ⥤ D} {T : Cᵒᵖ ⥤ RingCat.{u}} {S : Dᵒᵖ ⥤ RingCat.{u}}

def pushforwardCongr {φ ψ : T ⟶ F.op ⋙ S} (h : φ = ψ) :
    pushforward.{v} φ ≅ pushforward.{v} ψ :=
  NatIso.ofComponents (fun M ↦
    PresheafOfModules.isoMk (fun U ↦
      (ModuleCat.restrictScalarsCongr (by subst h; rfl)).app _)
      (fun _ _ _ ↦ by subst h; rfl)) (fun _ ↦ by subst h; rfl)

@[simp] lemma pushforwardCongr_hom_app {φ ψ : T ⟶ F.op ⋙ S} (h : φ = ψ)
    (M : PresheafOfModules.{v} S) (U) (x) :
    ((pushforwardCongr h).hom.app M).app U x = x := by
  subst h
  rfl

def pushforwardNatTrans (φ : T ⟶ G.op ⋙ S) (α : F ⟶ G) :
    pushforward.{v} φ ⟶
      pushforward.{v} (φ ≫ whiskerRight (NatTrans.op α) S) where
  app M := {
    app U := (ModuleCat.restrictScalars (φ.app U).hom).map (M.map (α.app U.unop).op)
    naturality {U V} i := by
      ext x
      change (M.presheaf.map (G.map i.unop).op ≫ M.presheaf.map (α.app V.unop).op) _ =
        (M.presheaf.map (α.app U.unop).op ≫ M.presheaf.map (F.map i.unop).op) _
      simp only [← Functor.map_comp, ← op_comp, α.naturality] }
  naturality {M N} f := by
    ext U x
    exact congr($(f.naturality (α.app U.unop).op) x).symm

@[simp] lemma pushforwardNatTrans_app_app
    (φ : T ⟶ G.op ⋙ S) (α : F ⟶ G) (M U x) :
    ((pushforwardNatTrans φ α).app M).app U x = M.map (α.app U.unop).op x := rfl

variable {F : C ⥤ D} {G : D ⥤ C}
  (adj : F ⊣ G) (φ : T ⟶ F.op ⋙ S) (ψ : S ⟶ G.op ⋙ T)
  (H₁ : whiskerRight (NatTrans.op adj.counit) S = ψ ≫ G.op.whiskerLeft φ)
  (H₂ : φ ≫ F.op.whiskerLeft ψ ≫
    whiskerRight (NatTrans.op adj.unit) T = 𝟙 T)

def pushforwardPushforwardAdj : pushforward.{v} φ ⊣ pushforward.{v} ψ where
  unit := (pushforwardId _).inv ≫ pushforwardNatTrans (𝟙 _) adj.counit ≫
    (pushforwardCongr (by simpa using H₁)).hom ≫ (pushforwardComp _ _).inv
  counit := (pushforwardComp _ _).hom ≫ pushforwardNatTrans _ adj.unit ≫
    (pushforwardCongr (by simpa using H₂)).hom ≫ (pushforwardId _).hom
  left_triangle_components M := by
    ext U x
    simp only [comp_app, ModuleCat.comp_apply,
      pushforwardId, pushforwardComp, Iso.refl_hom, Iso.refl_inv]
    change M.map (F.map (adj.unit.app U.unop)).op
      (M.map (adj.counit.app (F.obj U.unop)).op x) = x
    change M.obj (Opposite.op (F.obj U.unop)) at x
    erw [← M.map_comp_apply, ← op_comp, adj.left_triangle_components, op_id, M.map_id]
    rfl
  right_triangle_components M := by
    ext U x
    simp only [comp_app, ModuleCat.comp_apply,
      pushforwardId, pushforwardComp, Iso.refl_hom, Iso.refl_inv]
    change M.map (adj.unit.app (G.obj U.unop)).op
      (M.map (G.map (adj.counit.app U.unop)).op x) = x
    change M.obj (Opposite.op (G.obj U.unop)) at x
    erw [← M.map_comp_apply, ← op_comp, adj.right_triangle_components, op_id, M.map_id]
    rfl

end ModulePresheaf

namespace Geometry

section
open AlgebraicGeometry TopologicalSpace
open scoped AlgebraicGeometry
variable {X Y : Scheme} (f : X ⟶ Y) [IsOpenImmersion f]

def modulePresheafRestrict : PresheafOfModules Y.ringCatSheaf.obj ⥤
    PresheafOfModules X.ringCatSheaf.obj :=
  let α : X.presheaf ⟶ f.opensFunctor.op ⋙ Y.presheaf :=
    { app U := (f.appIso U.unop).inv }
  PresheafOfModules.pushforward (Functor.whiskerRight α (forget₂ CommRingCat RingCat))

def modulePresheafRestrictAdjunction : modulePresheafRestrict f ⊣
    PresheafOfModules.pushforward f.toRingCatSheafHom.hom := by
  refine ModulePresheaf.pushforwardPushforwardAdj
    (by exact f.isOpenEmbedding.isOpenMap.adjunction) _ _ ?_ ?_
  · ext U x
    exact congr($((f.app_appIso_inv _).symm).hom x)
  · ext U x
    have h : (f.appIso U.unop).inv ≫ f.app _ ≫
        X.presheaf.map (eqToHom (f.preimage_image_eq U.unop).symm).op = 𝟙 _ := by
      rw [Scheme.Hom.appIso_inv_app_assoc, ← Functor.map_comp, ← X.presheaf.map_id]
      rfl
    exact congr($h x)

def moduleSheafificationRestrict :
    PresheafOfModules.sheafification (𝟙 Y.ringCatSheaf.obj) ⋙
      Scheme.Modules.restrictFunctor f ≅
    modulePresheafRestrict f ⋙
      PresheafOfModules.sheafification (𝟙 X.ringCatSheaf.obj) :=
  Adjunction.leftAdjointUniq
    ((PresheafOfModules.sheafificationAdjunction (𝟙 Y.ringCatSheaf.obj)).comp
      (Scheme.Modules.restrictAdjunction f))
    ((modulePresheafRestrictAdjunction f).comp
      (PresheafOfModules.sheafificationAdjunction (𝟙 X.ringCatSheaf.obj)))

end

section
open CategoryTheory AlgebraicGeometry TopologicalSpace
open scoped AlgebraicGeometry
open MonoidalCategory
variable {X : Scheme}

def modulePresheafRestrictOpensIso (U : X.Opens) :
    modulePresheafRestrict U.ι ≅
      PresheafOfModules.pushforward₀OfCommRingCat U.ι.opensFunctor X.presheaf := by
  let α : U.toScheme.presheaf ⟶ U.ι.opensFunctor.op ⋙ X.presheaf :=
    { app V := (U.ι.appIso V.unop).inv }
  have h : Functor.whiskerRight α (forget₂ CommRingCat RingCat) = 𝟙 _ := by
    ext V x
    simp only [Functor.whiskerRight_app, α, Scheme.Opens.ι_appIso, Iso.refl_inv]
    rfl
  exact ModulePresheaf.pushforwardCongr (F := U.ι.opensFunctor)
    (T := U.toScheme.ringCatSheaf.obj) (S := X.ringCatSheaf.obj) h

def modulePresheafTensorRestrict (U : X.Opens)
    (M N : PresheafOfModules X.ringCatSheaf.obj) :
    (modulePresheafRestrict U.ι).obj
        (PresheafOfModulesOfCommRing.Monoidal.tensorObj (R := X.presheaf) M N) ≅
      PresheafOfModulesOfCommRing.Monoidal.tensorObj (R := U.toScheme.presheaf)
        ((modulePresheafRestrict U.ι).obj M)
        ((modulePresheafRestrict U.ι).obj N) := by
  letI : MonoidalCategory (PresheafOfModules U.toScheme.ringCatSheaf.obj) :=
    PresheafOfModulesOfCommRing.monoidalCategory (R := U.toScheme.presheaf)
  exact (modulePresheafRestrictOpensIso U).app _ ≪≫
    (Functor.Monoidal.μIso
      (PresheafOfModules.pushforward₀OfCommRingCat U.ι.opensFunctor X.presheaf) M N).symm ≪≫
    tensorIso ((modulePresheafRestrictOpensIso U).symm.app M)
      ((modulePresheafRestrictOpensIso U).symm.app N)

end

open CategoryTheory AlgebraicGeometry TopologicalSpace MonoidalCategory
open scoped AlgebraicGeometry
variable {X : Scheme}

def moduleTensorRestrict (U : X.Opens) (M N : X.Modules) :
    (moduleTensor X M N).restrict U.ι ≅
      moduleTensor U.toScheme (M.restrict U.ι) (N.restrict U.ι) :=
  (moduleSheafificationRestrict U.ι).app _ ≪≫
    (PresheafOfModules.sheafification (𝟙 U.toScheme.ringCatSheaf.obj)).mapIso
      (modulePresheafTensorRestrict U M.val N.val)

def moduleTensorIso {M N P Q : X.Modules} (e : M ≅ N) (f : P ≅ Q) :
    moduleTensor X M P ≅ moduleTensor X N Q := by
  letI : MonoidalCategory (PresheafOfModules X.ringCatSheaf.obj) :=
    PresheafOfModulesOfCommRing.monoidalCategory (R := X.presheaf)
  exact (PresheafOfModules.sheafification (𝟙 X.ringCatSheaf.obj)).mapIso
    (tensorIso ((SheafOfModules.forget _).mapIso e) ((SheafOfModules.forget _).mapIso f))

def moduleTensorUnit (M : X.Modules) :
    moduleTensor X (structureSheaf X) M ≅ M := by
  letI : MonoidalCategory (PresheafOfModules X.ringCatSheaf.obj) :=
    PresheafOfModulesOfCommRing.monoidalCategory (R := X.presheaf)
  exact (PresheafOfModules.sheafification (𝟙 X.ringCatSheaf.obj)).mapIso (λ_ M.val) ≪≫
    (asIso (PresheafOfModules.sheafificationAdjunction (R := X.ringCatSheaf)
      (𝟙 X.ringCatSheaf.obj)).counit).app M

def modulePowFrame {M : X.Modules} (U : X.Opens)
    (e : M.restrict U.ι ≅ structureSheaf U.toScheme) :
    ∀ n, (modulePow X M n).restrict U.ι ≅ structureSheaf U.toScheme
  | 0 => Scheme.Modules.restrictUnitIso U.ι
  | n + 1 => moduleTensorRestrict U M (modulePow X M n) ≪≫
    moduleTensorIso e (modulePowFrame U e n) ≪≫ moduleTensorUnit _

def LineBundle.pow (L : LineBundle X) (n : ℕ) : LineBundle X where
  sheaf := modulePow X L.sheaf n
  locallyRankOne x := by
    obtain ⟨U, hx, ⟨frame⟩⟩ := L.locallyRankOne x
    exact ⟨U, hx, ⟨modulePowFrame U frame n⟩⟩

def moduleTensorMap {M N P Q : X.Modules} (f : M ⟶ N) (g : P ⟶ Q) :
    moduleTensor X M P ⟶ moduleTensor X N Q :=
  (PresheafOfModules.sheafification (𝟙 X.ringCatSheaf.obj)).map
    (PresheafOfModulesOfCommRing.Monoidal.tensorHom (R := X.presheaf) f.val g.val)

@[simp] lemma moduleTensorMap_id (M N : X.Modules) :
    moduleTensorMap (𝟙 M) (𝟙 N) = 𝟙 (moduleTensor X M N) := by
  let : MonoidalCategory (PresheafOfModules X.ringCatSheaf.obj) :=
    PresheafOfModulesOfCommRing.monoidalCategory (R := X.presheaf)
  change (PresheafOfModules.sheafification (𝟙 X.ringCatSheaf.obj)).map
    ((𝟙 M.val) ⊗ₘ (𝟙 N.val)) = _
  rw [id_tensorHom_id]
  exact (PresheafOfModules.sheafification (𝟙 X.ringCatSheaf.obj)).map_id _

@[reassoc] lemma moduleTensorMap_comp {M N P Q R T : X.Modules}
    (f : M ⟶ N) (g : N ⟶ P) (h : Q ⟶ R) (k : R ⟶ T) :
    moduleTensorMap (f ≫ g) (h ≫ k) = moduleTensorMap f h ≫ moduleTensorMap g k := by
  let : MonoidalCategory (PresheafOfModules X.ringCatSheaf.obj) :=
    PresheafOfModulesOfCommRing.monoidalCategory (R := X.presheaf)
  change (PresheafOfModules.sheafification (𝟙 X.ringCatSheaf.obj)).map
    ((f.val ≫ g.val) ⊗ₘ (h.val ≫ k.val)) = _
  rw [← tensorHom_comp_tensorHom]
  exact Functor.map_comp _ _ _

instance moduleTensorMap_isIso {M N P Q : X.Modules} (f : M ⟶ N)
    (g : P ⟶ Q) [IsIso f] [IsIso g] : IsIso (moduleTensorMap f g) := by
  refine ⟨⟨moduleTensorMap (inv f) (inv g), ?_, ?_⟩⟩ <;>
    rw [← moduleTensorMap_comp] <;> simp

def modulePowMap {M N : X.Modules} (f : M ⟶ N) :
    ∀ n, modulePow X M n ⟶ modulePow X N n
  | 0 => 𝟙 _
  | n + 1 => moduleTensorMap f (modulePowMap f n)

@[simp] lemma modulePowMap_id (M : X.Modules) (n : ℕ) :
    modulePowMap (𝟙 M) n = 𝟙 (modulePow X M n) := by
  induction n with
  | zero => rfl
  | succ n hn =>
    change moduleTensorMap (𝟙 M) (modulePowMap (𝟙 M) n) = 𝟙 (moduleTensor X M (modulePow X M n))
    rw [hn, moduleTensorMap_id]

@[reassoc] lemma modulePowMap_comp {M N P : X.Modules}
    (f : M ⟶ N) (g : N ⟶ P) (n : ℕ) :
    modulePowMap (f ≫ g) n = modulePowMap f n ≫ modulePowMap g n := by
  induction n with
  | zero => exact (Category.id_comp _).symm
  | succ n hn =>
    change moduleTensorMap (f ≫ g) (modulePowMap (f ≫ g) n) =
      moduleTensorMap f (modulePowMap f n) ≫ moduleTensorMap g (modulePowMap g n)
    rw [hn, moduleTensorMap_comp]

instance modulePowMap_isIso {M N : X.Modules} (f : M ⟶ N) [IsIso f] (n : ℕ) :
    IsIso (modulePowMap f n) := by
  induction n with
  | zero => change IsIso (𝟙 (structureSheaf X)); infer_instance
  | succ n hn => change IsIso (moduleTensorMap f (modulePowMap f n)); infer_instance

def modulePowFunctor (n : ℕ) : X.Modules ⥤ X.Modules where
  obj M := modulePow X M n
  map f := modulePowMap f n
  map_id := fun _ => modulePowMap_id _ n
  map_comp := fun _ _ => modulePowMap_comp _ _ n

def unitPowerIso : ∀ n, modulePow X (structureSheaf X) n ≅ structureSheaf X
  | 0 => Iso.refl _
  | n + 1 => moduleTensorUnit _ ≪≫ unitPowerIso n

def powerSection {M : X.Modules} (s : structureSheaf X ⟶ M) (n : ℕ) :
    structureSheaf X ⟶ modulePow X M n :=
  (unitPowerIso n).inv ≫ modulePowMap s n

@[simp] lemma powerSection_zero {M : X.Modules} (s : structureSheaf X ⟶ M) :
    powerSection s 0 = 𝟙 (structureSheaf X) := by
  change 𝟙 (structureSheaf X) ≫ 𝟙 (structureSheaf X) = 𝟙 (structureSheaf X)
  exact Category.id_comp _

lemma powerSection_natural {M N : X.Modules} (s : structureSheaf X ⟶ M)
    (f : M ⟶ N) (n : ℕ) :
    powerSection s n ≫ modulePowMap f n = powerSection (s ≫ f) n := by
  simp only [powerSection, modulePowMap_comp, Category.assoc]

instance powerSection_isIso {M : X.Modules} (s : structureSheaf X ⟶ M) [IsIso s] (n : ℕ) :
    IsIso (powerSection s n) := by unfold powerSection; infer_instance

def moduleTensorRightUnit (M : X.Modules) :
    moduleTensor X M (structureSheaf X) ≅ M := by
  let : MonoidalCategory (PresheafOfModules X.ringCatSheaf.obj) :=
    PresheafOfModulesOfCommRing.monoidalCategory (R := X.presheaf)
  exact (PresheafOfModules.sheafification (𝟙 X.ringCatSheaf.obj)).mapIso (ρ_ M.val) ≪≫
    (asIso (PresheafOfModules.sheafificationAdjunction (R := X.ringCatSheaf)
      (𝟙 X.ringCatSheaf.obj)).counit).app M

end Geometry

end PiExponentSeshadri

end

end OAI
end Source0004

section Source0005
/-
Modification notice for the LogTwo project.
Derived from openai/math (Apache-2.0), revision adc7f1241b42e322a6451854ab7e4b4c146bf78a.
Original source: lean/OAI/NumberTheory/PiExponent/Polynomials/FrameCoefficients.lean
Changes: Convert module/import declarations to the Lean 4.34 public module format.
See ../../../../../THIRD_PARTY_NOTICES.txt for provenance and the recorded changes.
-/




namespace OAI

universe u

namespace PiExponentSeshadri.Frames
noncomputable section
open AlgebraicGeometry CategoryTheory TopologicalSpace
open scoped AlgebraicGeometry
variable {X Y Z : Scheme.{u}}
def O (X : Scheme.{u}) : X.Modules := SheafOfModules.unit X.ringCatSheaf

def endValue (f : O X ⟶ O X) : Γ(X, ⊤) := f.app ⊤ (1 : Γ(X, ⊤))

lemma end_apply (f : O X ⟶ O X) (U : X.Opens) (a : Γ(X, U)) :
    f.app U a = a * (show Γ(X, U) from f.app U (1 : Γ(X, U))) := by
  have h := f.app_smul (r := a) (x := (1 : Γ(X, U)))
  change f.app U (a * 1 : Γ(X, U)) = a * (show Γ(X, U) from f.app U (1 : Γ(X, U))) at h
  simpa only [mul_one] using h

@[simp] lemma endValue_id : endValue (𝟙 (O X)) = 1 := rfl

lemma endValue_comp (f g : O X ⟶ O X) :
    endValue (f ≫ g) = endValue f * endValue g := by
  exact end_apply g ⊤ (endValue f)

def frameChange {M : X.Modules} (e f : M ≅ O X) : Γ(X, ⊤)ˣ where
  val := endValue (e.inv ≫ f.hom)
  inv := endValue (f.inv ≫ e.hom)
  val_inv := by rw [← endValue_comp]; simp
  inv_val := by rw [← endValue_comp]; simp

def coefficient {M : X.Modules} (e : M ≅ O X) (s : O X ⟶ M) : Γ(X, ⊤) :=
  endValue (s ≫ e.hom)

lemma coefficient_change {M : X.Modules} (e f : M ≅ O X) (s : O X ⟶ M) :
    coefficient f s = (frameChange e f : Γ(X, ⊤)) * coefficient e s := by
  change endValue (s ≫ f.hom) = endValue (e.inv ≫ f.hom) * endValue (s ≫ e.hom)
  rw [mul_comm, ← endValue_comp]
  simp

lemma coefficient_frame {M : X.Modules} (e : M ≅ O X) : coefficient e e.inv = 1 := by
  simp [coefficient]

def restrictSection (φ : Y ⟶ X) [IsOpenImmersion φ] {M : X.Modules}
    (s : O X ⟶ M) : O Y ⟶ M.restrict φ :=
  (Scheme.Modules.restrictUnitIso φ).inv ≫ (Scheme.Modules.restrictFunctor φ).map s

def restrictFrame (φ : Y ⟶ X) [IsOpenImmersion φ] {M : X.Modules}
    (e : M ≅ O X) : M.restrict φ ≅ O Y :=
  (Scheme.Modules.restrictFunctor φ).mapIso e ≪≫ Scheme.Modules.restrictUnitIso φ

lemma end_naturality (f : O X ⟶ O X) (U : X.Opens) :
    f.app U (1 : Γ(X, U)) =
      X.presheaf.map (homOfLE (show U ≤ ⊤ from le_top)).op (endValue f) := by
  have h := CategoryTheory.congr_fun (f.mapPresheaf.naturality
    (homOfLE (show U ≤ ⊤ from le_top)).op) (1 : Γ(X, ⊤))
  change f.app U (X.presheaf.map (homOfLE (show U ≤ ⊤ from le_top)).op (1 : Γ(X, ⊤))) =
    X.presheaf.map (homOfLE (show U ≤ ⊤ from le_top)).op (endValue f) at h
  simpa only [map_one] using h

lemma endValue_restrict (φ : Y ⟶ X) [IsOpenImmersion φ] (f : O X ⟶ O X) :
    endValue (restrictSection φ f ≫ (Scheme.Modules.restrictUnitIso φ).hom) =
      φ.appTop (endValue f) := by
  change (φ.appIso ⊤).hom (f.app (φ ''ᵁ ⊤) ((φ.appIso ⊤).inv 1)) = _
  rw [map_one, end_naturality]
  change (X.presheaf.map (homOfLE (show φ ''ᵁ ⊤ ≤ ⊤ from le_top)).op ≫
    (φ.appIso ⊤).hom) (endValue f) = _
  rw [Scheme.Hom.appIso_hom']
  simp only [Scheme.Hom.appTop, Scheme.Hom.appLE,
    Scheme.Hom.naturality_assoc, ← Functor.map_comp]
  congr 1
  rw [show ((Opens.map φ.base).map (homOfLE (show φ ''ᵁ ⊤ ≤ ⊤ from le_top)).op.unop).op ≫
      (homOfLE (show (⊤ : Y.Opens) ≤ φ ⁻¹ᵁ (φ ''ᵁ ⊤) from by intro x _; exact ⟨x, Set.mem_univ _, rfl⟩)).op = 𝟙 _ from Subsingleton.elim _ _]
  erw [CategoryTheory.Functor.map_id, Category.comp_id]

lemma coefficient_restrict (φ : Y ⟶ X) [IsOpenImmersion φ] {M : X.Modules}
    (e : M ≅ O X) (s : O X ⟶ M) :
    coefficient (restrictFrame φ e) (restrictSection φ s) = φ.appTop (coefficient e s) := by
  change endValue ((Scheme.Modules.restrictUnitIso φ).inv ≫
    (Scheme.Modules.restrictFunctor φ).map s ≫
    (Scheme.Modules.restrictFunctor φ).map e.hom ≫
    (Scheme.Modules.restrictUnitIso φ).hom) = _
  erw [← Functor.map_comp_assoc]
  exact endValue_restrict φ (s ≫ e.hom)

lemma restrictUnit_comp (φ : Y ⟶ X) (ψ : X ⟶ Z)
    [IsOpenImmersion φ] [IsOpenImmersion ψ] :
    (Scheme.Modules.restrictUnitIso (φ ≫ ψ)).inv ≫
      (Scheme.Modules.restrictFunctorComp φ ψ).hom.app (O Z) =
    (Scheme.Modules.restrictUnitIso φ).inv ≫
      (Scheme.Modules.restrictFunctor φ).map (Scheme.Modules.restrictUnitIso ψ).inv := by
  ext U a
  change Z.presheaf.map (eqToHom (show ψ ''ᵁ (φ ''ᵁ U) = (φ ≫ ψ) ''ᵁ U from by simp)).op
    ((φ ≫ ψ).appIso U |>.inv |>.hom |>.toFun <| a) =
      (ψ.appIso (φ ''ᵁ U)).inv ((φ.appIso U).inv a)
  rw [Scheme.Hom.comp_appIso]
  simp only [Iso.trans_inv, Functor.mapIso_inv, Iso.op_inv, eqToIso.inv]
  change ( (φ.appIso U).inv ≫ (ψ.appIso (φ ''ᵁ U)).inv ≫
    Z.presheaf.map _ ≫ Z.presheaf.map _) a = _
  rw [← CategoryTheory.Functor.map_comp]
  simp
  rfl

lemma restrictSection_comp (φ : Y ⟶ X) (ψ : X ⟶ Z)
    [IsOpenImmersion φ] [IsOpenImmersion ψ] {M : Z.Modules} (s : O Z ⟶ M) :
    restrictSection (φ ≫ ψ) s ≫ (Scheme.Modules.restrictFunctorComp φ ψ).hom.app M =
      restrictSection φ (restrictSection ψ s) := by
  let F := Scheme.Modules.restrictFunctor φ
  let G := Scheme.Modules.restrictFunctor ψ
  let H := Scheme.Modules.restrictFunctor (φ ≫ ψ)
  let e := Scheme.Modules.restrictFunctorComp φ ψ
  let a : O Y ⟶ H.obj (O Z) := (Scheme.Modules.restrictUnitIso (φ ≫ ψ)).inv
  let b : O Y ⟶ F.obj (O X) := (Scheme.Modules.restrictUnitIso φ).inv
  let c : O X ⟶ G.obj (O Z) := (Scheme.Modules.restrictUnitIso ψ).inv
  change (a ≫ H.map s) ≫ e.hom.app M = b ≫ F.map (c ≫ G.map s)
  calc
    _ = a ≫ (H.map s ≫ e.hom.app M) := Category.assoc _ _ _
    _ = a ≫ (e.hom.app (O Z) ≫ F.map (G.map s)) :=
      congrArg (fun t => a ≫ t) (e.hom.naturality s)
    _ = (a ≫ e.hom.app (O Z)) ≫ F.map (G.map s) := (Category.assoc _ _ _).symm
    _ = (b ≫ F.map c) ≫ F.map (G.map s) :=
      congrArg (fun t => t ≫ F.map (G.map s)) (restrictUnit_comp φ ψ)
    _ = b ≫ (F.map c ≫ F.map (G.map s)) := Category.assoc _ _ _
    _ = _ := congrArg (fun t => b ≫ t) (F.map_comp c (G.map s)).symm

lemma coefficient_transport {M N : X.Modules} (e : M ≅ N) (f : N ≅ O X)
    (s : O X ⟶ M) : coefficient (e ≪≫ f) s = coefficient f (s ≫ e.hom) := by
  simp only [coefficient, Iso.trans_hom, Category.assoc]

lemma coefficient_restrict_comp (φ : Y ⟶ X) (ψ : X ⟶ Z)
    [IsOpenImmersion φ] [IsOpenImmersion ψ] {M : Z.Modules}
    (e : M.restrict ψ ≅ O X) (s : O Z ⟶ M) :
    coefficient ((Scheme.Modules.restrictFunctorComp φ ψ).app M ≪≫ restrictFrame φ e)
      (restrictSection (φ ≫ ψ) s) = φ.appTop (coefficient e (restrictSection ψ s)) := by
  rw [coefficient_transport]
  change coefficient (restrictFrame φ e)
    (restrictSection (φ ≫ ψ) s ≫ (Scheme.Modules.restrictFunctorComp φ ψ).hom.app M) = _
  rw [restrictSection_comp, coefficient_restrict]

lemma restrictSection_congr {φ ψ : Y ⟶ X} (h : φ = ψ)
    [IsOpenImmersion φ] [IsOpenImmersion ψ] {M : X.Modules} (s : O X ⟶ M) :
    restrictSection φ s ≫ (Scheme.Modules.restrictFunctorCongr h).hom.app M =
      restrictSection ψ s := by
  subst ψ
  have H : (Scheme.Modules.restrictFunctorCongr (show φ = φ from rfl)).hom.app M = 𝟙 _ := by
    ext U a
    simp
    rfl
  rw [H, Category.comp_id]

lemma overlap_coefficients {W : Scheme.{u}} (φ : Y ⟶ X) (ψ : Z ⟶ X)
    (a : W ⟶ Y) (b : W ⟶ Z) [IsOpenImmersion φ] [IsOpenImmersion ψ]
    [IsOpenImmersion a] [IsOpenImmersion b] (h : a ≫ φ = b ≫ ψ)
    {M : X.Modules} (e : M.restrict φ ≅ O Y) (f : M.restrict ψ ≅ O Z) :
    ∃ c : Γ(W, ⊤)ˣ, ∀ s : O X ⟶ M,
      b.appTop (coefficient f (restrictSection ψ s)) =
      (c : Γ(W, ⊤)) * a.appTop (coefficient e (restrictSection φ s)) := by
  let E : M.restrict (a ≫ φ) ≅ O W :=
    (Scheme.Modules.restrictFunctorComp a φ).app M ≪≫ restrictFrame a e
  let F : M.restrict (a ≫ φ) ≅ O W :=
    (Scheme.Modules.restrictFunctorCongr h).app M ≪≫
      (Scheme.Modules.restrictFunctorComp b ψ).app M ≪≫ restrictFrame b f
  refine ⟨frameChange E F, fun s => ?_⟩
  have H := coefficient_change E F (restrictSection (a ≫ φ) s)
  have hE : coefficient E (restrictSection (a ≫ φ) s) =
      a.appTop (coefficient e (restrictSection φ s)) := coefficient_restrict_comp a φ e s
  have hF : coefficient F (restrictSection (a ≫ φ) s) =
      b.appTop (coefficient f (restrictSection ψ s)) := by
    change coefficient ((Scheme.Modules.restrictFunctorCongr h).app M ≪≫
      ((Scheme.Modules.restrictFunctorComp b ψ).app M ≪≫ restrictFrame b f)) _ = _
    rw [coefficient_transport]
    change coefficient _ (restrictSection (a ≫ φ) s ≫
      (Scheme.Modules.restrictFunctorCongr h).hom.app M) = _
    rw [restrictSection_congr]
    exact coefficient_restrict_comp b ψ f s
  rwa [hE, hF] at H

end
end PiExponentSeshadri.Frames

end OAI
end Source0005

section Source0006
/-
Modification notice for the LogTwo project.
Derived from openai/math (Apache-2.0), revision adc7f1241b42e322a6451854ab7e4b4c146bf78a.
Original source: lean/OAI/NumberTheory/PiExponent/Approximation/FrameSections.lean
Changes: Convert module/import declarations to the Lean 4.34 public module format.
See ../../../../../THIRD_PARTY_NOTICES.txt for provenance and the recorded changes.
-/




namespace OAI

noncomputable section

universe u

namespace PiExponentSeshadri.Frames

section
open AlgebraicGeometry CategoryTheory TopologicalSpace
open scoped AlgebraicGeometry
variable {X Y : Scheme.{u}}

def scalarEnd (r : Γ(X, ⊤)) : O X ⟶ O X where
  val.app U := by
    let S := X.ringCatSheaf.obj.obj U
    letI : CommRing S := inferInstanceAs (CommRing Γ(X, U.unop))
    exact ModuleCat.ofHom (LinearMap.mulLeft S
      ((X.presheaf.map (homOfLE le_top).op) r))
  val.naturality {U V} i := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro a
    change Γ(X, U.unop) at a
    change (X.presheaf.map (homOfLE le_top).op r) * (X.presheaf.map i a) =
      X.presheaf.map i (X.presheaf.map (homOfLE le_top).op r * a)
    rw [map_mul, ← CommRingCat.comp_apply, ← Functor.map_comp]
    rfl

@[simp] lemma endValue_scalarEnd (r : Γ(X, ⊤)) : endValue (scalarEnd r) = r := by
  change X.presheaf.map (𝟙 _) r * 1 = r
  simp

lemma endValue_injective : Function.Injective (endValue (X := X)) := by
  intro f g h
  ext U a
  change Γ(X, U) at a
  change f.app U a = g.app U a
  rw [end_apply f U a, end_apply g U a]
  rw [end_naturality f U, end_naturality g U, h]

lemma end_isIso_iff (f : O X ⟶ O X) : IsIso f ↔ IsUnit (endValue f) := by
  constructor
  · intro h
    let := h
    refine isUnit_iff_exists_inv.mpr ⟨endValue (inv f), ?_⟩
    rw [← endValue_comp]
    simp
  · rintro ⟨u, hu⟩
    refine ⟨⟨scalarEnd ↑u⁻¹, ?_, ?_⟩⟩
    · apply endValue_injective
      rw [endValue_comp, ← hu, endValue_scalarEnd, endValue_id]
      exact Units.val_inv u
    · apply endValue_injective
      rw [endValue_comp, ← hu, endValue_scalarEnd, endValue_id]
      exact Units.inv_val u

lemma coefficient_isUnit_iff {M : X.Modules} (e : M ≅ O X) (s : O X ⟶ M) :
    IsUnit (coefficient e s) ↔ IsIso s := by
  change IsUnit (endValue (s ≫ e.hom)) ↔ _
  rw [← end_isIso_iff]
  exact isIso_comp_right_iff s e.hom

end

section
open CategoryTheory AlgebraicGeometry TopologicalSpace Opposite
open scoped AlgebraicGeometry
variable {X : Scheme}

def moduleSectionsTopEquiv {T : TopCat} (R : Sheaf (Opens.grothendieckTopology T) RingCat)
    (M : SheafOfModules R) : M.sections ≃ M.val.obj (op ⊤) where
  toFun s := s.val (op ⊤)
  invFun t := PresheafOfModules.sectionsMk
    (fun U => M.val.map (homOfLE le_top).op t)
    (by
      intro U V i
      rw [← M.val.map_comp_apply]
      exact M.val.congr_map_apply (Subsingleton.elim _ _) t)
  left_inv s := by
    apply PresheafOfModules.sections_ext
    intro U
    exact s.property (homOfLE le_top).op
  right_inv t := by
    change M.val.map (𝟙 (op ⊤)) t = t
    rw [M.val.map_id]
    rfl

def moduleSectionEquiv (M : X.Modules) : (O X ⟶ M) ≃ Γ(M, ⊤) :=
  M.unitHomEquiv.trans (moduleSectionsTopEquiv X.ringCatSheaf M)

@[simp] lemma moduleSectionEquiv_apply (M : X.Modules) (s : O X ⟶ M) :
    moduleSectionEquiv M s = s.app ⊤ (1 : Γ(X, ⊤)) := rfl

def openSectionEquiv (M : X.Modules) (U : X.Opens) :
    (O U.toScheme ⟶ M.restrict U.ι) ≃ Γ(M, U) :=
  (moduleSectionEquiv (M.restrict U.ι)).trans
    (let e := M.presheaf.mapIso (eqToIso U.ι_image_top.symm).op
     { toFun := e.hom
       invFun := e.inv
       left_inv := fun t => Iso.hom_inv_id_apply e t
       right_inv := fun t => Iso.inv_hom_id_apply e t })

lemma section_value_natural {M : X.Modules} (s : O X ⟶ M) {U V : X.Opens} (i : U ⟶ V) :
    M.presheaf.map i.op (s.app V (1 : Γ(X, V))) = s.app U (1 : Γ(X, U)) := by
  have h := CategoryTheory.congr_fun (s.mapPresheaf.naturality i.op) (1 : Γ(X, V))
  change s.app U (X.presheaf.map i.op (1 : Γ(X, V))) =
    M.presheaf.map i.op (s.app V (1 : Γ(X, V))) at h
  simpa only [map_one] using h.symm

@[simp] lemma openSectionEquiv_restrict {M : X.Modules} (s : O X ⟶ M) (U : X.Opens) :
    openSectionEquiv M U (restrictSection U.ι s) = s.app U (1 : Γ(X, U)) := by
  change M.presheaf.map (eqToHom U.ι_image_top.symm).op
    (s.app (U.ι ''ᵁ ⊤) ((U.ι.appIso ⊤).inv (1 : Γ(U.toScheme, ⊤)))) = _
  rw [map_one]
  exact section_value_natural s (eqToHom U.ι_image_top.symm)

end

open CategoryTheory AlgebraicGeometry TopologicalSpace
open scoped AlgebraicGeometry
variable {X : Scheme}

lemma moduleSectionEquiv_scalar {M : X.Modules} (f : Γ(X, ⊤)) (s : O X ⟶ M) :
    moduleSectionEquiv M (scalarEnd f ≫ s) = f • moduleSectionEquiv M s := by
  change s.app ⊤ (endValue (scalarEnd f)) = f • s.app ⊤ (1 : Γ(X, ⊤))
  rw [endValue_scalarEnd]
  have h := s.app_smul (r := f) (x := (1 : Γ(X, ⊤)))
  change s.app ⊤ (f * 1 : Γ(X, ⊤)) = f • s.app ⊤ (1 : Γ(X, ⊤)) at h
  simpa only [mul_one] using h

lemma openSectionEquiv_scalar (M : X.Modules) (U : X.Opens)
    (f : Γ(U.toScheme, ⊤)) (s : O U.toScheme ⟶ M.restrict U.ι) :
    openSectionEquiv M U (scalarEnd f ≫ s) = U.topIso.hom f • openSectionEquiv M U s := by
  change M.presheaf.map (eqToHom U.ι_image_top.symm).op
    (moduleSectionEquiv (M.restrict U.ι) (scalarEnd f ≫ s)) = _
  rw [moduleSectionEquiv_scalar]
  change M.presheaf.map (eqToHom U.ι_image_top.symm).op
    ((U.ι.appIso ⊤).inv f • (show Γ(M, U.ι ''ᵁ ⊤) from moduleSectionEquiv (M.restrict U.ι) s)) = _
  rw [M.map_smul, U.ι_appIso]
  rfl

lemma openSectionEquiv_restrict_value (M : X.Modules) (U : X.Opens)
    (s : O U.toScheme ⟶ M.restrict U.ι) (W : U.toScheme.Opens) :
    M.presheaf.map (homOfLE (U.ι_image_le W)).op (openSectionEquiv M U s) =
      s.app W (1 : Γ(U.toScheme, W)) := by
  have h := section_value_natural s (homOfLE (show W ≤ ⊤ from le_top))
  change M.presheaf.map (U.ι.opensFunctor.map (homOfLE (show W ≤ ⊤ from le_top))).op
    (s.app ⊤ (1 : Γ(U.toScheme, ⊤))) = _ at h
  change M.presheaf.map (homOfLE (U.ι_image_le W)).op
    (M.presheaf.map (eqToHom U.ι_image_top.symm).op (s.app ⊤ (1 : Γ(U.toScheme, ⊤)))) = _
  erw [← ConcreteCategory.comp_apply, ← Functor.map_comp]
  exact h

lemma image_section_extension (M : X.Modules) (U : X.Opens)
    (s t : O U.toScheme ⟶ M.restrict U.ι) (W : U.toScheme.Opens)
    (f : Γ(W.toScheme, ⊤))
    (h : restrictSection W.ι t = scalarEnd f ≫ restrictSection W.ι s) :
    M.presheaf.map (homOfLE (U.ι_image_le W)).op (openSectionEquiv M U t) =
      (U.ι.appIso W).inv (W.topIso.hom f) • M.presheaf.map (homOfLE (U.ι_image_le W)).op
        (openSectionEquiv M U s) := by
  have hh := congrArg (openSectionEquiv (M.restrict U.ι) W) h
  rw [openSectionEquiv_restrict, openSectionEquiv_scalar, openSectionEquiv_restrict] at hh
  rw [openSectionEquiv_restrict_value, openSectionEquiv_restrict_value]
  exact hh

end PiExponentSeshadri.Frames

end

end OAI
end Source0006

section Source0007
/-
Modification notice for the LogTwo project.
Derived from openai/math (Apache-2.0), revision adc7f1241b42e322a6451854ab7e4b4c146bf78a.
Original source: lean/OAI/NumberTheory/PiExponent/LocalAlgebra/IdealModule.lean
Changes: Convert module/import declarations to the Lean 4.34 public module format.
See ../../../../../THIRD_PARTY_NOTICES.txt for provenance and the recorded changes.
-/




namespace OAI

noncomputable section

namespace PiExponentSeshadri.IdealModule

section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
universe u
variable {X Y : Scheme.{u}} (f : X ⟶ Y)

def unit (X : Scheme.{u}) : X.Modules := SheafOfModules.unit X.ringCatSheaf

def structureMap : unit Y ⟶
    (Scheme.Modules.pushforward f).obj (unit X) :=
  SheafOfModules.unitToPushforwardObjUnit f.toRingCatSheafHom

@[simp] lemma structureMap_app (U : Y.Opens) (x : Γ(Y, U)) :
    ((structureMap f).val.app (op U)) x = (f.app U) x := rfl

def idealModule : Y.Modules := kernel (structureMap f)

def inclusion : idealModule f ⟶ unit Y :=
  kernel.ι (structureMap f)

instance : Mono (inclusion f) := inferInstanceAs (Mono (kernel.ι (structureMap f)))

def sectionsKernelIso (U : Y.Opens) :
    (idealModule f).val.obj (op U) ≅
      ModuleCat.of (Y.ringCatSheaf.obj.obj (op U))
        ((structureMap f).val.app (op U)).hom.ker :=
  PreservesKernel.iso
    (Scheme.Modules.toPresheafOfModules Y ⋙
      PresheafOfModules.evaluation Y.ringCatSheaf.obj (op U)) (structureMap f) ≪≫
    ModuleCat.kernelIsoKer _

lemma sectionsKernelIso_inclusion (U : Y.Opens) :
    (sectionsKernelIso f U).hom ≫
      ModuleCat.ofHom ((structureMap f).val.app (op U)).hom.ker.subtype =
        (inclusion f).val.app (op U) := by
  let E := Scheme.Modules.toPresheafOfModules Y ⋙
    PresheafOfModules.evaluation Y.ringCatSheaf.obj (op U)
  change ((PreservesKernel.iso E (structureMap f)).hom ≫
    (ModuleCat.kernelIsoKer (E.map (structureMap f))).hom) ≫
      ModuleCat.ofHom (E.map (structureMap f)).hom.ker.subtype =
        E.map (kernel.ι (structureMap f))
  rw [Category.assoc, ModuleCat.kernelIsoKer_hom_ker_subtype,
    PreservesKernel.iso_hom, kernelComparison_comp_ι]

lemma image_eq_kernel (U : Y.Opens) :
    ((inclusion f).val.app (op U)).hom.range = RingHom.ker (f.app U).hom := by
  ext x
  constructor
  · rintro ⟨y, rfl⟩
    change (f.app U) (((inclusion f).val.app (op U)) y) = 0
    have h := congrArg (fun g => (g.val.app (op U)) y)
      (kernel.condition (structureMap f))
    exact h
  · intro hx
    let y : ((structureMap f).val.app (op U)).hom.ker := ⟨x, hx⟩
    refine ⟨(sectionsKernelIso f U).inv y, ?_⟩
    have h := congrArg (fun g => g ((sectionsKernelIso f U).inv y))
      (sectionsKernelIso_inclusion f U)
    simpa using h.symm

lemma image_eq_ideal [QuasiCompact f] (U : Y.affineOpens) :
    ((inclusion f).val.app (op U.1)).hom.range = f.ker.ideal U := by
  rw [image_eq_kernel, Scheme.Hom.ker_apply]

end

section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
universe u
variable {X Y : Scheme.{u}}

def closedModule (I : X.IdealSheafData) : X.Modules := idealModule I.subschemeι

def closedInclusion (I : X.IdealSheafData) : closedModule I ⟶ unit X :=
  inclusion I.subschemeι

lemma closed_image (I : X.IdealSheafData) (U : X.affineOpens) :
    ((closedInclusion I).val.app (op U.1)).hom.range = I.ideal U := by
  exact (image_eq_ideal I.subschemeι U).trans (congrArg (fun J => J.ideal U) I.ker_subschemeι)

lemma isIso_of_affine_app {M N : X.Modules} (g : M ⟶ N)
    (h : ∀ U : X.affineOpens, IsIso (g.app U.1)) : IsIso g := by
  let F := SheafOfModules.toSheaf X.ringCatSheaf
  have hb : TopologicalSpace.Opens.IsBasis (Set.range fun U : X.affineOpens => U.val) := by
    simpa using X.isBasis_affineOpens
  have hg : IsIso (F.map g) := TopCat.Sheaf.isIso_iff_isIso_basis hb h
  let : IsIso ((Scheme.Modules.toPresheaf X).map g) :=
    inferInstanceAs (IsIso ((sheafToPresheaf _ AddCommGrpCat).map (F.map g)))
  exact isIso_of_reflects_iso g (Scheme.Modules.toPresheaf X)

def multiply (r : Γ(X, ⊤)) : unit X ⟶ unit X where
  val.app U := by
    let S := X.ringCatSheaf.obj.obj U
    letI : CommRing S := inferInstanceAs (CommRing Γ(X, U.unop))
    exact ModuleCat.ofHom (LinearMap.mulLeft S
      ((X.presheaf.map (homOfLE le_top).op) r))
  val.naturality {U V} i := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro a
    change Γ(X, U.unop) at a
    change (X.presheaf.map (homOfLE le_top).op r) * (X.presheaf.map i a) =
      X.presheaf.map i (X.presheaf.map (homOfLE le_top).op r * a)
    rw [map_mul, ← CommRingCat.comp_apply, ← Functor.map_comp]
    rfl

@[simp] lemma multiply_app (r : Γ(X, ⊤)) (U : X.Opens) (a : Γ(X, U)) :
    (multiply r).val.app (op U) a = X.presheaf.map (homOfLE le_top).op r * a := rfl

lemma multiply_structure_zero (f : Y ⟶ X) (r : Γ(X, ⊤))
    (hr : (f.app ⊤) r = 0) : multiply r ≫ structureMap f = 0 := by
  ext U a
  change Γ(X, U) at a
  change (f.app U) ((X.presheaf.map (homOfLE (show U ≤ ⊤ from le_top)).op r) *
    (a : Γ(X, U))) = 0
  rw [map_mul]
  have he : (f.app U) (X.presheaf.map (homOfLE le_top).op r) = 0 := by
    rw [← CommRingCat.comp_apply, f.naturality, CommRingCat.comp_apply, hr, map_zero]
  rw [he, zero_mul]

def equationToIdeal (f : Y ⟶ X) (r : Γ(X, ⊤)) (hr : (f.app ⊤) r = 0) :
    unit X ⟶ idealModule f :=
  kernel.lift (structureMap f) (multiply r) (multiply_structure_zero f r hr)

@[reassoc (attr := simp)] lemma equationToIdeal_inclusion
    (f : Y ⟶ X) (r : Γ(X, ⊤)) (hr : (f.app ⊤) r = 0) :
    equationToIdeal f r hr ≫ inclusion f = multiply r := kernel.lift_ι _ _ _

lemma equationToIdeal_app (f : Y ⟶ X) (r : Γ(X, ⊤)) (hr : (f.app ⊤) r = 0)
    (U : X.Opens) (a : Γ(X, U)) :
    (inclusion f).val.app (op U) ((equationToIdeal f r hr).val.app (op U) a) =
      X.presheaf.map (homOfLE le_top).op r * a :=
  congrArg (fun g => g.val.app (op U) a) (equationToIdeal_inclusion f r hr)

lemma isIso_equationToIdeal (f : Y ⟶ X) [QuasiCompact f]
    (r : Γ(X, ⊤)) (hr : (f.app ⊤) r = 0)
    (hprincipal : ∀ U : X.affineOpens,
      f.ker.ideal U = Ideal.span {X.presheaf.map (homOfLE le_top).op r})
    (hregular : ∀ U : X.affineOpens,
      IsLeftRegular (X.presheaf.map (homOfLE (show U.1 ≤ ⊤ from le_top)).op r)) :
    IsIso (equationToIdeal f r hr) := by
  apply isIso_of_affine_app
  intro U
  have hinj : Function.Injective ((inclusion f).val.app (op U.1)) := by
    let : Mono (inclusion f).val :=
      inferInstanceAs (Mono ((Scheme.Modules.toPresheafOfModules X).map (inclusion f)))
    exact PresheafOfModules.injective_of_mono (inclusion f).val (op U.1)
  apply (ConcreteCategory.isIso_iff_bijective _).mpr
  constructor
  · intro a b hab
    apply hregular U
    have he := congrArg ((inclusion f).val.app (op U.1)) hab
    change (inclusion f).val.app (op U.1) ((equationToIdeal f r hr).val.app (op U.1) a) =
      (inclusion f).val.app (op U.1) ((equationToIdeal f r hr).val.app (op U.1) b) at he
    exact (equationToIdeal_app f r hr U.1 a).symm.trans
      (he.trans (equationToIdeal_app f r hr U.1 b))
  · intro y
    have hy : (inclusion f).val.app (op U.1) y ∈ f.ker.ideal U := by
      rw [← image_eq_ideal f U]
      exact ⟨y, rfl⟩
    rw [hprincipal U] at hy
    have hd : X.presheaf.map (homOfLE (show U.1 ≤ ⊤ from le_top)).op r ∣
        (show Γ(X, U.1) from (inclusion f).val.app (op U.1) y) :=
      Ideal.mem_span_singleton.mp hy
    obtain ⟨a, ha⟩ := hd
    refine ⟨a, hinj ?_⟩
    exact (equationToIdeal_app f r hr U.1 a).trans ha.symm

end

section
open CategoryTheory AlgebraicGeometry
variable {X : Scheme}
lemma regular_map_flat {R S : Type*} [CommRing R] [CommRing S]
    (f : R →+* S) (hf : f.Flat) {r : R} (hr : IsLeftRegular r) :
    IsLeftRegular (f r) := by
  let := f.toAlgebra
  let : Module.Flat R S := hf
  have hh : IsSMulRegular S r := Module.Flat.isSMulRegular_of_isRegular
    ⟨hr, hr.right_of_commute (fun a => mul_comm r a)⟩
  simpa only [IsSMulRegular, IsLeftRegular, Algebra.smul_def, RingHom.algebraMap_toAlgebra] using hh

lemma restriction_regular [IsAffine X] (r : Γ(X, ⊤)) (hr : IsLeftRegular r)
    (U : X.affineOpens) :
    IsLeftRegular (X.presheaf.map (homOfLE (show U.1 ≤ ⊤ from le_top)).op r) := by
  apply regular_map_flat _ _ hr
  simpa [Scheme.Hom.appLE] using
    Scheme.Hom.flat_appLE (𝟙 X) (isAffineOpen_top X) U.2 (show U.1 ≤ (𝟙 X) ⁻¹ᵁ ⊤ from le_top)

end

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite
variable {X Y : Scheme.{0}}

lemma structureMap_epi (f : X ⟶ Y) [IsClosedImmersion f] : Epi (structureMap f) := by
  let F := SheafOfModules.toSheaf Y.ringCatSheaf
  have hloc : TopCat.Presheaf.IsLocallySurjective (F.map (structureMap f)).hom := by
    apply (TopCat.Presheaf.isLocallySurjective_iff _).mpr
    intro U t y hy
    obtain ⟨_,⟨V,hA,rfl⟩,hyV,hVU⟩ :=
      Y.isBasis_affineOpens.exists_subset_of_mem_open hy U.isOpen
    obtain ⟨s,hs⟩ := f.app_surjective V hA
      (((F.obj ((Scheme.Modules.pushforward f).obj (unit X))).obj.map
        (homOfLE hVU).op) t)
    exact ⟨V,hVU,⟨s,hs⟩,hyV⟩
  let : Epi (F.map (structureMap f)) :=
    (TopCat.Sheaf.isLocallySurjective_iff_epi _).mp hloc
  exact F.epi_of_epi_map inferInstance

theorem closedSequence_exact (f : X ⟶ Y) [IsClosedImmersion f] :
    (ShortComplex.mk (inclusion f) (structureMap f) (kernel.condition _)).ShortExact := by
  let := structureMap_epi f
  exact { exact := ShortComplex.exact_kernel _ }

end PiExponentSeshadri.IdealModule

end

end OAI
end Source0007

section Source0008
/-
Modification notice for the LogTwo project.
Derived from openai/math (Apache-2.0), revision adc7f1241b42e322a6451854ab7e4b4c146bf78a.
Original source: lean/OAI/NumberTheory/PiExponent/Approximation/GlobalSectionClearing.lean
Changes: Convert module/import declarations to the Lean 4.34 public module format.
See ../../../../../THIRD_PARTY_NOTICES.txt for provenance and the recorded changes.
-/




namespace OAI

namespace PiExponent.GlobalSectionClearing
noncomputable section
open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite
universe u
variable {X Y : Scheme.{u}}

def restrictScalar (X : Scheme.{u}) (U : X.Opens) : Γ(X, ⊤) →+* Γ(X, U) :=
  (X.presheaf.map (homOfLE le_top).op).hom

lemma restrictScalar_naturality (X : Scheme.{u}) {U V : X.Opens} (i : U ⟶ V) (r : Γ(X, ⊤)) :
    X.presheaf.map i.op (restrictScalar X V r) = restrictScalar X U r := by
  change (X.presheaf.map (homOfLE le_top).op ≫ X.presheaf.map i.op) r = _
  rw [← X.presheaf.map_comp]
  rfl

def OpenSections (M : X.Modules) (U : X.Opens) := Γ(M,U)
instance (M : X.Modules) (U : X.Opens) : AddCommGroup (OpenSections M U) :=
  inferInstanceAs (AddCommGroup Γ(M,U))
instance (M : X.Modules) (U : X.Opens) : Module Γ(X,⊤) (OpenSections M U) :=
  Module.compHom Γ(M,U) (restrictScalar X U)

def openRestriction (M : X.Modules) {U V : X.Opens} (h : U ≤ V) :
    OpenSections M V →ₗ[Γ(X,⊤)] OpenSections M U where
  toFun := M.val.map (homOfLE h).op
  map_add' := map_add _
  map_smul' := by
    intro r m
    let : Module Γ(X,V) (OpenSections M V) := (M.val.obj (op V)).isModule
    let : Module Γ(X,U) (OpenSections M U) := (M.val.obj (op U)).isModule
    change M.presheaf.map (homOfLE h).op (restrictScalar X V r • (m : Γ(M,V))) =
      restrictScalar X U r • M.presheaf.map (homOfLE h).op m
    erw [M.map_smul, restrictScalar_naturality]

theorem quasicoherent_pushforward_iso (e : X ≅ Y) (M : X.Modules) [M.IsQuasicoherent] :
    ((Scheme.Modules.pushforward e.hom).obj M).IsQuasicoherent := by
  let N := (Scheme.Modules.pushforward e.hom).obj M
  let q : (Scheme.Modules.pushforward e.inv).obj N ≅ M :=
    (Scheme.Modules.pushforwardComp e.hom e.inv).app M ≪≫
      (Scheme.Modules.pushforwardCongr e.hom_inv_id).app M ≪≫
      (Scheme.Modules.pushforwardId X).app M
  let j : N ≅ M.restrict e.inv :=
    ((Scheme.Modules.restrictFunctorAdjCounitIso e.inv).app N).symm ≪≫
      (Scheme.Modules.restrictFunctor e.inv).mapIso q
  exact (SheafOfModules.isQuasicoherent Y.ringCatSheaf).prop_of_iso j.symm inferInstance

abbrev affineToSpecModule [IsAffine X] (M : X.Modules) :=
  (Scheme.Modules.pushforward X.toSpecΓ).obj M

instance affineToSpecModule_quasicoherent [IsAffine X] (M : X.Modules)
    [M.IsQuasicoherent] : (affineToSpecModule M).IsQuasicoherent :=
  quasicoherent_pushforward_iso X.isoSpec M

theorem affine_sections_localize [IsAffine X] (M : X.Modules) [M.IsQuasicoherent]
    (r : Γ(X,⊤)) :
    IsLocalizedModule.Away r
      (((modulesSpecToSheaf.obj (affineToSpecModule M)).obj.map
        (PrimeSpectrum.basicOpen r).leTop.op).hom) :=
  ((isIso_fromTildeΓ_iff_isLocalizing (affineToSpecModule M)).mp inferInstance) r

def affineSpecSections [IsAffine X] (M : X.Modules)
    (U : (Spec Γ(X,⊤)).Opens) :
    ((modulesSpecToSheaf.obj (affineToSpecModule M)).obj.obj (op U)) ≃ₗ[Γ(X,⊤)]
      OpenSections M (X.toSpecΓ ⁻¹ᵁ U) where
  toFun := fun x => x
  invFun := fun x => x
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' r m := by
    let : Module Γ(X,X.toSpecΓ ⁻¹ᵁ U) Γ(M,X.toSpecΓ ⁻¹ᵁ U) :=
      (M.val.obj (op (X.toSpecΓ ⁻¹ᵁ U))).isModule
    change @SMul.smul Γ(X,X.toSpecΓ ⁻¹ᵁ U) Γ(M,X.toSpecΓ ⁻¹ᵁ U) _
      ((X.toSpecΓ.app U).hom
        ((Spec Γ(X,⊤)).presheaf.map U.leTop.op ((Scheme.ΓSpecIso Γ(X,⊤)).inv r))) m =
      @SMul.smul Γ(X,X.toSpecΓ ⁻¹ᵁ U) Γ(M,X.toSpecΓ ⁻¹ᵁ U) _
        (restrictScalar X (X.toSpecΓ ⁻¹ᵁ U) r) m
    congr 1
    have h := congrArg (fun f : Γ(Spec Γ(X,⊤),⊤) ⟶ Γ(X,X.toSpecΓ ⁻¹ᵁ U) =>
      f ((Scheme.ΓSpecIso Γ(X,⊤)).inv r)) (X.toSpecΓ.naturality U.leTop.op)
    simp only [CommRingCat.comp_apply, Scheme.toSpecΓ_appTop] at h
    change _ = restrictScalar X (X.toSpecΓ ⁻¹ᵁ U)
      ((Scheme.ΓSpecIso Γ(X,⊤)).hom ((Scheme.ΓSpecIso Γ(X,⊤)).inv r)) at h
    rw [(Scheme.ΓSpecIso Γ(X,⊤)).inv_hom_id_apply r] at h
    exact h

def openSectionsCongr (M : X.Modules) {U V : X.Opens} (h : U = V) :
    OpenSections M U ≃ₗ[Γ(X,⊤)] OpenSections M V := by
  subst V
  exact LinearEquiv.refl _ _

lemma openSectionsCongr_restriction (M : X.Modules) {U V : X.Opens} (h : U = V)
    (m : OpenSections M ⊤) :
    openSectionsCongr M h (openRestriction M (show U ≤ ⊤ from le_top) m) = openRestriction M (show V ≤ ⊤ from le_top) m := by
  subst V
  rfl

theorem affine_openRestriction_localize [IsAffine X] (M : X.Modules) [M.IsQuasicoherent]
    (r : Γ(X,⊤)) :
    IsLocalizedModule.Away r (openRestriction M (X.basicOpen_le r)) := by
  let F := modulesSpecToSheaf.obj (affineToSpecModule M)
  let f := (F.obj.map (PrimeSpectrum.basicOpen r).leTop.op).hom
  let e0 : (F.obj.obj (op ⊤)) ≃ₗ[Γ(X,⊤)] OpenSections M ⊤ := affineSpecSections M ⊤
  let e1 := (affineSpecSections M (PrimeSpectrum.basicOpen r)).trans
    (openSectionsCongr M (Scheme.toSpecΓ_preimage_basicOpen X r))
  have hf : IsLocalizedModule.Away r f := affine_sections_localize M r
  have hq : IsLocalizedModule.Away r (e1.toLinearMap ∘ₗ f ∘ₗ e0.symm.toLinearMap) := by
    let := hf
    let := IsLocalizedModule.of_linearEquiv (.powers r) f e1
    exact IsLocalizedModule.of_linearEquiv_right (.powers r) (e1.toLinearMap ∘ₗ f) e0.symm
  have he : e1.toLinearMap ∘ₗ f ∘ₗ e0.symm.toLinearMap =
      openRestriction M (X.basicOpen_le r) := by
    ext m
    exact openSectionsCongr_restriction M (Scheme.toSpecΓ_preimage_basicOpen X r) m
  rwa [he] at hq

theorem affine_basicOpen_denominators [IsAffine X] (M : X.Modules) [M.IsQuasicoherent]
    (r : Γ(X,⊤)) (x : OpenSections M (X.basicOpen r)) :
    ∃ n : ℕ, ∃ y : OpenSections M ⊤,
      openRestriction M (X.basicOpen_le r) y = r^n • x := by
  let f := openRestriction M (X.basicOpen_le r)
  let : IsLocalizedModule.Away r f := affine_openRestriction_localize M r
  obtain ⟨n,y,hy⟩ := (inferInstance : IsLocalizedModule.Away r f).surj _ _ x
  exact ⟨n,y,hy.symm⟩

def openTopSections (M : X.Modules) :
    letI : Module Γ(X,⊤) Γ(M,⊤) := (M.val.obj (op ⊤)).isModule
    OpenSections M ⊤ ≃ₗ[Γ(X,⊤)] Γ(M,⊤) := by
  letI : Module Γ(X,⊤) Γ(M,⊤) := (M.val.obj (op ⊤)).isModule
  refine { toFun := fun x => x
           invFun := fun x => x
           left_inv := fun _ => rfl
           right_inv := fun _ => rfl
           map_add' := fun _ _ => rfl
           map_smul' := ?_ }
  intro r m
  change @SMul.smul Γ(X,⊤) Γ(M,⊤) _ (restrictScalar X ⊤ r) m =
    @SMul.smul Γ(X,⊤) Γ(M,⊤) _ r m
  congr 1
  change (X.presheaf.map (𝟙 (op ⊤))) r = r
  rw [X.presheaf.map_id]
  rfl

lemma restrictScalar_appIso (f : Y ⟶ X) [IsOpenImmersion f] (U : Y.Opens)
    (r : Γ(X,⊤)) :
    (f.appIso U).inv (restrictScalar Y U (f.appTop r)) =
      restrictScalar X (f ''ᵁ U) r := by
  have h := congrArg (fun g : Γ(X,⊤) ⟶ Γ(X,f ''ᵁ U) => g r)
    (Scheme.Hom.appLE_appIso_inv f (U := ⊤) (V := U) (by simp))
  change (f.appIso U).inv ((f.appLE ⊤ U (by simp)) r) = _ at h
  have he : f.appLE ⊤ U (by simp) = f.appTop ≫ Y.presheaf.map U.leTop.op := by
    erw [Scheme.Hom.appTop, Scheme.Hom.app_eq_appLE, Scheme.Hom.appLE_map]
  rw [he] at h
  exact h

def restrictedOpenSections (M : X.Modules) (f : Y ⟶ X) [IsOpenImmersion f]
    (U : Y.Opens) :
    letI := Module.compHom (OpenSections (M.restrict f) U) f.appTop.hom
    OpenSections (M.restrict f) U ≃ₗ[Γ(X,⊤)] OpenSections M (f ''ᵁ U) := by
  letI := Module.compHom (OpenSections (M.restrict f) U) f.appTop.hom
  letI : Module Γ(X,f ''ᵁ U) Γ(M,f ''ᵁ U) := (M.val.obj (op (f ''ᵁ U))).isModule
  refine { toFun := fun x => x
           invFun := fun x => x
           left_inv := fun _ => rfl
           right_inv := fun _ => rfl
           map_add' := fun _ _ => rfl
           map_smul' := ?_ }
  intro r m
  change @SMul.smul Γ(X,f ''ᵁ U) Γ(M,f ''ᵁ U) _
      ((f.appIso U).inv (restrictScalar Y U (f.appTop r))) m =
    @SMul.smul Γ(X,f ''ᵁ U) Γ(M,f ''ᵁ U) _ (restrictScalar X (f ''ᵁ U) r) m
  rw [restrictScalar_appIso]

lemma restrictedOpenSections_naturality (M : X.Modules) (f : Y ⟶ X) [IsOpenImmersion f]
    {U V : Y.Opens} (h : U ≤ V) (m : OpenSections (M.restrict f) V) :
    restrictedOpenSections M f U (openRestriction (M.restrict f) h m) =
      openRestriction M (f.image_mono h) (restrictedOpenSections M f V m) := rfl

theorem affine_basicOpen_zero [IsAffine X] (M : X.Modules) [M.IsQuasicoherent]
    (r : Γ(X,⊤)) (x : OpenSections M ⊤)
    (hx : openRestriction M (X.basicOpen_le r) x = 0) :
    ∃ N : ℕ, ∀ n ≥ N, r ^ n • x = 0 := by
  let := affine_openRestriction_localize M r
  obtain ⟨⟨_, N, rfl⟩, hN⟩ :=
    (IsLocalizedModule.eq_zero_iff (.powers r)
      (openRestriction M (X.basicOpen_le r))).mp hx
  change r ^ N • x = 0 at hN
  refine ⟨N, fun n hn => ?_⟩
  rw [← Nat.sub_add_cancel hn, pow_add, mul_smul, hN, smul_zero]

lemma openRestriction_comp_apply (M : X.Modules) {U V W : X.Opens}
    (hUV : U ≤ V) (hVW : V ≤ W) (x : OpenSections M W) :
    openRestriction M hUV (openRestriction M hVW x) =
      openRestriction M (hUV.trans hVW) x := by
  change M.presheaf.map _ (M.presheaf.map _ x) = M.presheaf.map _ x
  erw [← M.presheaf.map_comp_apply, ← op_comp, homOfLE_comp]

lemma openRestriction_zero_congr (M : X.Modules) {U V W : X.Opens}
    (e : U = V) (hU : U ≤ W) (hV : V ≤ W) (x : OpenSections M W)
    (h : openRestriction M hU x = 0) : openRestriction M hV x = 0 := by
  subst V
  exact h

lemma affine_immersion_zero_on [IsAffine Y] (M : X.Modules) [M.IsQuasicoherent]
    (f : Y ⟶ X) [IsOpenImmersion f] (r : Γ(X,⊤))
    (U : X.Opens) (hU : f ''ᵁ (⊤ : Y.Opens) ≤ U) (x : OpenSections M U)
    (hx : openRestriction M (show U ⊓ X.basicOpen r ≤ U from inf_le_left) x = 0) :
    ∃ N : ℕ, ∀ n ≥ N,
      openRestriction M hU (r ^ n • x) = 0 := by
  let x' := (restrictedOpenSections M f ⊤).symm
    (openRestriction M hU x)
  have hWD : f ''ᵁ (Y.basicOpen (f.appTop r)) ≤ U ⊓ X.basicOpen r := by
    apply le_inf
    · exact (f.image_mono le_top).trans hU
    · rw [← Scheme.preimage_basicOpen_top]
      exact f.image_preimage_le _
  have hx' : openRestriction (M.restrict f) (Y.basicOpen_le (f.appTop r)) x' = 0 := by
    apply (restrictedOpenSections M f _).injective
    rw [map_zero, restrictedOpenSections_naturality]
    simp only [x', LinearEquiv.apply_symm_apply]
    rw [openRestriction_comp_apply]
    rw [← openRestriction_comp_apply M hWD (show U ⊓ X.basicOpen r ≤ U from inf_le_left) x, hx, map_zero]
  obtain ⟨N, hN⟩ := affine_basicOpen_zero (M.restrict f) (f.appTop r) x' hx'
  refine ⟨N, fun n hn => ?_⟩
  have hi := congrArg (restrictedOpenSections M f ⊤) (hN n hn)
  let : Module Γ(X,⊤) (OpenSections (M.restrict f) ⊤) :=
    Module.compHom (OpenSections (M.restrict f) ⊤) f.appTop.hom
  have hscalar : (f.appTop r) ^ n • x' = (r ^ n) • x' := by
    change (f.appTop r) ^ n • x' = f.appTop (r ^ n) • x'
    rw [map_pow]
  rw [hscalar, map_smul, map_zero] at hi
  simpa only [x', LinearEquiv.apply_symm_apply, map_smul] using hi

theorem compact_open_section_zero (M : X.Modules) [M.IsQuasicoherent]
    (r : Γ(X,⊤)) (U : X.Opens) (hU : IsCompact (U : Set X))
    (x : OpenSections M U)
    (hx : openRestriction M (show U ⊓ X.basicOpen r ≤ U from inf_le_left) x = 0) :
    ∃ N : ℕ, ∀ n ≥ N, r ^ n • x = 0 := by
  classical
  obtain ⟨s, hs, e⟩ := isCompact_and_isOpen_iff_finite_and_eq_biUnion_affineOpens.mp
    ⟨hU, U.2⟩
  replace e : U = iSup fun i : s => (i : X.Opens) := by
    ext1
    simpa using e
  have h₁ (i : s) : i.1.1 ≤ U := by
    rw [e]
    exact le_iSup (fun i : s => (i : X.Opens)) i
  have H (i : s) : ∃ N : ℕ, ∀ n ≥ N,
      openRestriction M (h₁ i) (r ^ n • x) = 0 := by
    let : IsAffine i.1.1.toScheme := i.1.2
    have hh := affine_immersion_zero_on M i.1.1.ι r U
      (by simpa only [Scheme.Opens.ι_image_top] using h₁ i) x hx
    obtain ⟨N, hN⟩ := hh
    exact ⟨N, fun n hn => openRestriction_zero_congr M i.1.1.ι_image_top _ _ _ (hN n hn)⟩
  choose n hn using H
  have := hs.to_subtype
  let := Fintype.ofFinite s
  refine ⟨Finset.univ.sup n, fun k hk => ?_⟩
  apply TopCat.Sheaf.eq_of_locally_eq' ⟨_, M.isSheaf⟩ (fun i : s => (i : X.Opens)) U
    (fun i => homOfLE (h₁ i)) (by rw [e])
  intro i
  have hi := hn i k ((Finset.le_sup (f := n) (Finset.mem_univ i)).trans hk)
  change M.presheaf.map _ (r ^ k • x) = M.presheaf.map _ 0
  rw [map_zero]
  exact hi

theorem global_section_zero [CompactSpace X] (M : X.Modules) [M.IsQuasicoherent]
    (r : Γ(X,⊤)) (x : OpenSections M ⊤)
    (hx : openRestriction M (X.basicOpen_le r) x = 0) :
    ∃ N : ℕ, ∀ n ≥ N, r ^ n • x = 0 := by
  apply compact_open_section_zero M r ⊤ isCompact_univ x
  exact openRestriction_zero_congr M (top_inf_eq (a := X.basicOpen r)).symm _ _ _ hx

lemma openSectionsCongr_naturality (M : X.Modules) {U V U' V' : X.Opens}
    (eU : U = U') (eV : V = V') (h : U ≤ V) (h' : U' ≤ V')
    (x : OpenSections M V) :
    openSectionsCongr M eU (openRestriction M h x) =
      openRestriction M h' (openSectionsCongr M eV x) := by
  subst U' V'
  rfl

lemma principal_open_image (r : Γ(X,⊤)) (U : X.Opens) :
    U.ι ''ᵁ U.toScheme.basicOpen (U.ι.appTop r) = U ⊓ X.basicOpen r := by
  rw [← Scheme.preimage_basicOpen_top, Scheme.Hom.image_preimage_eq_opensRange_inf,
    Scheme.Opens.opensRange_ι]

def affineOpenPrincipalEquiv (M : X.Modules) (r : Γ(X,⊤)) (U : X.Opens) :
    letI := Module.compHom (OpenSections (M.restrict U.ι)
      (U.toScheme.basicOpen (U.ι.appTop r))) U.ι.appTop.hom
    OpenSections (M.restrict U.ι) (U.toScheme.basicOpen (U.ι.appTop r)) ≃ₗ[Γ(X,⊤)]
      OpenSections M (U ⊓ X.basicOpen r) :=
  (restrictedOpenSections M U.ι _).trans (openSectionsCongr M (principal_open_image r U))

def affineOpenTopEquiv (M : X.Modules) (U : X.Opens) :
    letI := Module.compHom (OpenSections (M.restrict U.ι) ⊤) U.ι.appTop.hom
    OpenSections (M.restrict U.ι) ⊤ ≃ₗ[Γ(X,⊤)] OpenSections M U :=
  (restrictedOpenSections M U.ι ⊤).trans (openSectionsCongr M U.ι_image_top)

lemma affineOpenPrincipalEquiv_restrict (M : X.Modules) (r : Γ(X,⊤)) (U : X.Opens)
    (y : OpenSections (M.restrict U.ι) ⊤) :
    affineOpenPrincipalEquiv M r U
      (openRestriction (M.restrict U.ι) (U.toScheme.basicOpen_le (U.ι.appTop r)) y) =
    openRestriction M (show U ⊓ X.basicOpen r ≤ U from inf_le_left)
      (affineOpenTopEquiv M U y) := by
  dsimp only [affineOpenPrincipalEquiv, affineOpenTopEquiv, LinearEquiv.trans_apply]
  rw [restrictedOpenSections_naturality]
  exact openSectionsCongr_naturality M (principal_open_image r U) U.ι_image_top _ _ _

theorem affine_open_section_extends (M : X.Modules) [M.IsQuasicoherent]
    (r : Γ(X,⊤)) (U : X.Opens) (hU : IsAffineOpen U)
    (x : OpenSections M (U ⊓ X.basicOpen r)) :
    ∃ n : ℕ, ∃ y : OpenSections M U,
      openRestriction M (show U ⊓ X.basicOpen r ≤ U from inf_le_left) y = r ^ n • x := by
  let : IsAffine U.toScheme := hU
  let : Module Γ(X,⊤) (OpenSections (M.restrict U.ι)
      (U.toScheme.basicOpen (U.ι.appTop r))) :=
    Module.compHom _ U.ι.appTop.hom
  let x' := (affineOpenPrincipalEquiv M r U).symm x
  obtain ⟨n, y, hy⟩ := affine_basicOpen_denominators (M.restrict U.ι) (U.ι.appTop r) x'
  refine ⟨n, affineOpenTopEquiv M U y, ?_⟩
  have hscalar : (U.ι.appTop r) ^ n • x' = (r ^ n) • x' := by
    change (U.ι.appTop r) ^ n • x' = U.ι.appTop (r ^ n) • x'
    rw [map_pow]
  have hh := congrArg (affineOpenPrincipalEquiv M r U) hy
  rw [hscalar, map_smul, affineOpenPrincipalEquiv_restrict] at hh
  simpa only [x', LinearEquiv.apply_symm_apply] using hh

def overlapDifference (M : X.Modules) {U V : X.Opens}
    (y : OpenSections M U) (z : OpenSections M V) : OpenSections M (U ⊓ V) :=
  openRestriction M inf_le_left y - openRestriction M inf_le_right z

lemma overlapDifference_restrict_zero (M : X.Modules) (r : Γ(X,⊤))
    (x : OpenSections M (X.basicOpen r)) (N : ℕ) {U V : X.Opens}
    (y : OpenSections M U) (z : OpenSections M V)
    (hy : openRestriction M (show U ⊓ X.basicOpen r ≤ U from inf_le_left) y =
      r ^ N • openRestriction M inf_le_right x)
    (hz : openRestriction M (show V ⊓ X.basicOpen r ≤ V from inf_le_left) z =
      r ^ N • openRestriction M inf_le_right x) :
    openRestriction M (show (U ⊓ V) ⊓ X.basicOpen r ≤ U ⊓ V from inf_le_left)
      (overlapDifference M y z) = 0 := by
  have hU : (U ⊓ V) ⊓ X.basicOpen r ≤ U ⊓ X.basicOpen r := inf_le_inf inf_le_left le_rfl
  have hV : (U ⊓ V) ⊓ X.basicOpen r ≤ V ⊓ X.basicOpen r := inf_le_inf inf_le_right le_rfl
  calc
    _ = openRestriction M hU (openRestriction M inf_le_left y) -
        openRestriction M hV (openRestriction M inf_le_left z) := by
      simp only [overlapDifference, map_sub, openRestriction_comp_apply]
    _ = 0 := by
      rw [hy, hz, map_smul, map_smul, openRestriction_comp_apply, openRestriction_comp_apply,
        sub_self]

lemma overlapDifference_smul_zero_iff (M : X.Modules) (r : Γ(X,⊤))
    {U V : X.Opens} (y : OpenSections M U) (z : OpenSections M V) (K : ℕ) :
    r ^ K • overlapDifference M y z = 0 ↔
      openRestriction M (show U ⊓ V ≤ U from inf_le_left) (r ^ K • y) =
      openRestriction M (show U ⊓ V ≤ V from inf_le_right) (r ^ K • z) := by
  simp only [overlapDifference, smul_sub, map_smul, sub_eq_zero]

theorem clear_finite_overlap_discrepancies (M : X.Modules) [M.IsQuasicoherent]
    (r : Γ(X,⊤)) {ι : Type*} [Fintype ι] (U : ι → X.Opens)
    (hcompact : ∀ i j, IsCompact ((U i ⊓ U j : X.Opens) : Set X))
    (x : OpenSections M (X.basicOpen r)) (N : ℕ) (y : ∀ i, OpenSections M (U i))
    (hy : ∀ i, openRestriction M (show U i ⊓ X.basicOpen r ≤ U i from inf_le_left) (y i) =
      r ^ N • openRestriction M inf_le_right x) :
    ∃ K : ℕ, ∀ i j,
      openRestriction M (show U i ⊓ U j ≤ U i from inf_le_left) (r ^ K • y i) =
      openRestriction M (show U i ⊓ U j ≤ U j from inf_le_right) (r ^ K • y j) := by
  classical
  have h (ij : ι × ι) := compact_open_section_zero M r (U ij.1 ⊓ U ij.2)
    (hcompact ij.1 ij.2) (overlapDifference M (y ij.1) (y ij.2))
    (overlapDifference_restrict_zero M r x N _ _ (hy ij.1) (hy ij.2))
  choose k hk using h
  let K := Finset.univ.sup k
  refine ⟨K, fun i j => ?_⟩
  apply (overlapDifference_smul_zero_iff M r (y i) (y j) K).mp
  exact hk (i,j) K (Finset.le_sup (f := k) (Finset.mem_univ (i,j)))

lemma restriction_of_glued_power (M : X.Modules) (r : Γ(X,⊤))
    {ι : Type*} (U : ι → X.Opens) (hcover : (⨆ i, U i) = ⊤)
    (x : OpenSections M (X.basicOpen r)) (N K : ℕ) (y : ∀ i, OpenSections M (U i))
    (hy : ∀ i, openRestriction M (show U i ⊓ X.basicOpen r ≤ U i from inf_le_left) (y i) =
      r ^ N • openRestriction M inf_le_right x)
    (z : OpenSections M ⊤)
    (hz : ∀ i, openRestriction M (show U i ≤ ⊤ from le_top) z = r ^ K • y i) :
    openRestriction M (X.basicOpen_le r) z = r ^ (N + K) • x := by
  apply TopCat.Sheaf.eq_of_locally_eq' ⟨_, M.isSheaf⟩ (fun i => U i ⊓ X.basicOpen r)
    (X.basicOpen r) (fun i => homOfLE inf_le_right)
    (by rw [← iSup_inf_eq, hcover, top_inf_eq])
  intro i
  change openRestriction M inf_le_right (openRestriction M (X.basicOpen_le r) z) =
    openRestriction M inf_le_right (r ^ (N + K) • x)
  rw [openRestriction_comp_apply,
    ← openRestriction_comp_apply M (show U i ⊓ X.basicOpen r ≤ U i from inf_le_left) le_top z,
    hz i, map_smul, hy i, map_smul, ← mul_smul, ← pow_add, Nat.add_comm K N]

theorem finite_cover_power_gluing (M : X.Modules) [M.IsQuasicoherent]
    (r : Γ(X,⊤)) {ι : Type*} [Fintype ι] (U : ι → X.Opens)
    (hcover : (⨆ i, U i) = ⊤)
    (hcompact : ∀ i j, IsCompact ((U i ⊓ U j : X.Opens) : Set X))
    (x : OpenSections M (X.basicOpen r)) (N : ℕ) (y : ∀ i, OpenSections M (U i))
    (hy : ∀ i, openRestriction M (show U i ⊓ X.basicOpen r ≤ U i from inf_le_left) (y i) =
      r ^ N • openRestriction M inf_le_right x) :
    ∃ K : ℕ, ∃ z : OpenSections M ⊤,
      openRestriction M (X.basicOpen_le r) z = r ^ (N + K) • x := by
  obtain ⟨K, hK⟩ := clear_finite_overlap_discrepancies M r U hcompact x N y hy
  have hh := TopCat.Sheaf.existsUnique_gluing' ⟨_, M.isSheaf⟩ U ⊤
    (fun i => homOfLE (show U i ≤ ⊤ from le_top)) (by rw [hcover]) (fun i => r ^ K • y i) ?_
  · obtain ⟨z, hz, _⟩ := hh
    exact ⟨K, z, restriction_of_glued_power M r U hcover x N K y hy z hz⟩
  · intro i j
    exact hK i j

theorem finite_affine_local_extensions (M : X.Modules) [M.IsQuasicoherent]
    (r : Γ(X,⊤)) {ι : Type*} [Fintype ι] (U : ι → X.Opens)
    (hU : ∀ i, IsAffineOpen (U i)) (x : OpenSections M (X.basicOpen r)) :
    ∃ N : ℕ, ∃ y : ∀ i, OpenSections M (U i),
      ∀ i, openRestriction M (show U i ⊓ X.basicOpen r ≤ U i from inf_le_left) (y i) =
        r ^ N • openRestriction M inf_le_right x := by
  classical
  choose n y hy using fun i => affine_open_section_extends M r (U i) (hU i)
    (openRestriction M (show U i ⊓ X.basicOpen r ≤ X.basicOpen r from inf_le_right) x)
  let N := Finset.univ.sup n
  refine ⟨N, fun i => r ^ (N - n i) • y i, fun i => ?_⟩
  rw [map_smul, hy i, ← mul_smul, ← pow_add,
    Nat.sub_add_cancel (Finset.le_sup (f := n) (Finset.mem_univ i))]

theorem global_section_extends [NoetherianSpace X] (M : X.Modules) [M.IsQuasicoherent]
    (r : Γ(X,⊤)) (x : OpenSections M (X.basicOpen r)) :
    ∃ N : ℕ, ∀ n ≥ N, ∃ y : OpenSections M ⊤,
      openRestriction M (X.basicOpen_le r) y = r ^ n • x := by
  classical
  obtain ⟨s, hs, e⟩ :=
    (isCompact_and_isOpen_iff_finite_and_eq_biUnion_affineOpens (X := X)
      (U := ((⊤ : X.Opens) : Set X))).mp
      ⟨NoetherianSpace.isCompact _, (⊤ : X.Opens).2⟩
  have hcover : (⨆ i : s, (i : X.Opens)) = ⊤ := by
    ext1
    simpa using e.symm
  have := hs.to_subtype
  let := Fintype.ofFinite s
  obtain ⟨N, y, hy⟩ := finite_affine_local_extensions M r (fun i : s => (i : X.Opens))
    (fun i => i.1.2) x
  obtain ⟨K, z, hz⟩ := finite_cover_power_gluing M r (fun i : s => (i : X.Opens)) hcover
    (fun i j => NoetherianSpace.isCompact _) x N y hy
  refine ⟨N + K, fun n hn => ⟨r ^ (n - (N + K)) • z, ?_⟩⟩
  rw [map_smul, hz, ← mul_smul, ← pow_add, Nat.sub_add_cancel hn]

theorem global_section_extends_native [NoetherianSpace X]
    (M : X.Modules) [M.IsQuasicoherent] (r : Γ(X,⊤)) (x : Γ(M, X.basicOpen r)) :
    letI : Module Γ(X, X.basicOpen r) Γ(M, X.basicOpen r) :=
      (M.val.obj (op (X.basicOpen r))).isModule
    ∃ N : ℕ, ∀ n ≥ N, ∃ y : Γ(M,⊤),
      M.presheaf.map (homOfLE (X.basicOpen_le r)).op y =
        (restrictScalar X (X.basicOpen r) r) ^ n • x := by
  let : Module Γ(X, X.basicOpen r) Γ(M, X.basicOpen r) :=
    (M.val.obj (op (X.basicOpen r))).isModule
  obtain ⟨N, hN⟩ := global_section_extends M r x
  refine ⟨N, fun n hn => ?_⟩
  obtain ⟨y, hy⟩ := hN n hn
  refine ⟨y, ?_⟩
  change M.presheaf.map (homOfLE (X.basicOpen_le r)).op y =
    (restrictScalar X (X.basicOpen r) (r ^ n)) • x at hy
  simpa only [map_pow] using hy

theorem global_section_zero_native [CompactSpace X]
    (M : X.Modules) [M.IsQuasicoherent] (r : Γ(X,⊤)) (x : Γ(M,⊤))
    (hx : M.presheaf.map (homOfLE (X.basicOpen_le r)).op x = 0) :
    letI : Module Γ(X,⊤) Γ(M,⊤) := (M.val.obj (op ⊤)).isModule
    ∃ N : ℕ, ∀ n ≥ N, r ^ n • x = 0 := by
  let : Module Γ(X,⊤) Γ(M,⊤) := (M.val.obj (op ⊤)).isModule
  obtain ⟨N, hN⟩ := global_section_zero M r x hx
  refine ⟨N, fun n hn => ?_⟩
  have hh := hN n hn
  change restrictScalar X ⊤ (r ^ n) • x = 0 at hh
  have hr : restrictScalar X ⊤ (r ^ n) = r ^ n := by
    change X.presheaf.map (𝟙 (op ⊤)) (r ^ n) = r ^ n
    rw [X.presheaf.map_id]
    rfl
  exact (congrArg (fun c : Γ(X, ⊤) => c • x) hr).symm.trans hh

end
end PiExponent.GlobalSectionClearing

end OAI
end Source0008

section Source0009
/-
Modification notice for the LogTwo project.
Derived from openai/math (Apache-2.0), revision adc7f1241b42e322a6451854ab7e4b4c146bf78a.
Original source: lean/OAI/NumberTheory/PiExponent/Ampleness/CoherentAffineFinite.lean
Changes: Convert module/import declarations to the Lean 4.34 public module format.
See ../../../../../THIRD_PARTY_NOTICES.txt for provenance and the recorded changes.
-/




namespace OAI

namespace PiExponent.CoherentAffineFinite
noncomputable section
universe u
open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite

private theorem epi_iso_comp_iso {C : Type*} [Category C] {A B D E : C}
    (i : A ≅ B) (p : B ⟶ D) (hp : Epi p) (j : D ≅ E) :
    Epi (i.hom ≫ p ≫ j.hom) := by
  let : Epi p := hp
  infer_instance

private theorem finitePresentation_quasicoherent {X : Scheme.{u}}
    (M : X.Modules) [M.IsFinitePresentation] : M.IsQuasicoherent :=
  (SheafOfModules.IsFinitePresentation.exists_quasicoherentData M).choose.isQuasicoherent

theorem spec_sections_finite_of_generators {R : CommRingCat.{u}}
    (M : (Spec R).Modules) [M.IsQuasicoherent]
    (s : M.GeneratingSections) [hs : s.IsFiniteType] :
    Module.Finite R ((modulesSpecToSheaf.obj M).obj.obj (op ⊤)) := by
  let : Finite s.I := hs.finite
  let : Fintype s.I := Fintype.ofFinite s.I
  let N : ModuleCat R := (modulesSpecToSheaf.obj M).obj.obj (op ⊤)
  let a : tilde (ModuleCat.of R (s.I →₀ R)) ⟶ tilde N :=
    (tildeFinsupp s.I).hom ≫ s.π ≫ (asIso M.fromTildeΓ).inv
  let f : ModuleCat.of R (s.I →₀ R) ⟶ N := (tilde.functor R).preimage a
  have : Epi s.π := s.epi
  have : Epi (asIso M.fromTildeΓ).inv := inferInstance
  have ha : Epi a := by
    change Epi ((tildeFinsupp s.I).hom ≫ s.π ≫ (asIso M.fromTildeΓ).inv)
    exact epi_iso_comp_iso (tildeFinsupp s.I) s.π s.epi (asIso M.fromTildeΓ).symm
  have hf : Epi f := (tilde.functor R).epi_of_epi_map (by
    change Epi ((tilde.functor R).map ((tilde.functor R).preimage a))
    exact (Functor.map_preimage (tilde.functor R) a).symm ▸ ha)
  exact Module.Finite.of_surjective f.hom ((ModuleCat.epi_iff_surjective f).mp hf)

theorem affine_sections_finite_of_generators {X : Scheme.{u}} [IsAffine X]
    (M : X.Modules) [M.IsQuasicoherent]
    (s : M.GeneratingSections) [hs : s.IsFiniteType] : Module.Finite Γ(X,⊤) Γ(M,⊤) := by
  let f := X.isoSpec.inv
  let F : SheafOfModules X.ringCatSheaf ⥤ SheafOfModules (Spec Γ(X,⊤)).ringCatSheaf :=
    Scheme.Modules.restrictFunctor f
  let : Limits.PreservesColimitsOfSize.{u, u} F :=
    (Scheme.Modules.restrictAdjunction f).leftAdjoint_preservesColimits
  let J := M.restrict f
  let t := s.map F (Scheme.Modules.restrictUnitIso f).symm
  let : t.IsFiniteType := ⟨hs.finite⟩
  let R := Γ(X,⊤)
  let N := (modulesSpecToSheaf.obj J).obj.obj (op ⊤)
  let : Module.Finite R N := spec_sections_finite_of_generators J t
  let σ : R →+* Γ(X,f ''ᵁ ⊤) := (f.appIso ⊤).inv.hom.comp (Scheme.ΓSpecIso R).inv.hom
  let φ : N →ₛₗ[σ] Γ(M,f ''ᵁ ⊤) := {
    toFun := (M.restrictAppIso f ⊤).hom
    map_add' := map_add _
    map_smul' := by intro r m; rfl }
  have hφ : Function.Surjective φ :=
    (ConcreteCategory.bijective_of_isIso (M.restrictAppIso f ⊤).hom).surjective
  have hf : f ''ᵁ (⊤ : (Spec R).Opens) = ⊤ := by
    ext x
    change (∃ y : Spec R, y ∈ (⊤ : (Spec R).Opens) ∧ f y = x) ↔ True
    simp only [Opens.mem_top, true_and, iff_true]
    exact (ConcreteCategory.bijective_of_isIso f.base).surjective x
  have h := Module.Finite.of_surjective φ hφ
  rw [hf] at h
  exact h

def LocallyFinitelyGenerated {X : Scheme.{u}} (M : X.Modules) : Prop :=
  ∀ x : X, ∃ U : X.Opens, x ∈ U ∧
    ∃ s : (M.restrict U.ι).GeneratingSections, s.IsFiniteType

theorem locallyFinitelyGenerated_of_finitePresentation {X : Scheme.{u}}
    (M : X.Modules) [M.IsFinitePresentation] : LocallyFinitelyGenerated M := by
  obtain ⟨q, hq⟩ := SheafOfModules.IsFinitePresentation.exists_quasicoherentData M
  intro x
  have hcov := q.coversTop
  rw [Opens.coversTop_iff] at hcov
  obtain ⟨i, hi⟩ := Opens.mem_iSup.mp (show x ∈ ⨆ i, q.X i by rw [hcov]; trivial)
  refine ⟨q.X i, hi, ?_⟩
  let F : SheafOfModules (Sheaf.over X.ringCatSheaf (q.X i)) ⥤
      SheafOfModules (Scheme.Opens.toScheme (X := X) (q.X i)).ringCatSheaf :=
    (Scheme.Modules.overEquiv (q.X i)).functor
  let : Limits.PreservesColimitsOfSize.{u, u} F :=
    (Scheme.Modules.overEquiv (q.X i)).toAdjunction.leftAdjoint_preservesColimits
  let t := (q.presentation i).generators.map F (Iso.refl _)
  let e := (Scheme.Modules.overFunctorEquiv (q.X i)).app M
  exact ⟨SheafOfModules.GeneratingSections.equivOfIso e t,
    ⟨(hq.isFinite_presentation i).isFiniteType_generators.finite⟩⟩

theorem finite_generators_of_le {X : Scheme.{u}} (M : X.Modules) {U V : X.Opens}
    (h : V ≤ U) (s : (M.restrict U.ι).GeneratingSections) [s.IsFiniteType] :
    ∃ t : (M.restrict V.ι).GeneratingSections, t.IsFiniteType := by
  let F : SheafOfModules U.toScheme.ringCatSheaf ⥤ SheafOfModules V.toScheme.ringCatSheaf :=
    Scheme.Modules.restrictFunctor (X.homOfLE h)
  let : Limits.PreservesColimitsOfSize.{u, u} F :=
    (Scheme.Modules.restrictAdjunction (X.homOfLE h)).leftAdjoint_preservesColimits
  let t := s.map F
    (Scheme.Modules.restrictUnitIso (X.homOfLE h)).symm
  let e := (Scheme.Modules.restrictFunctorComp (X.homOfLE h) U.ι).app M
  simp only [X.homOfLE_ι h] at e
  exact ⟨SheafOfModules.GeneratingSections.equivOfIso e.symm t,
    ⟨SheafOfModules.GeneratingSections.IsFiniteType.finite (σ := s)⟩⟩

theorem affine_open_sections_finite_of_generators {X : Scheme.{u}}
    (M : X.Modules) [M.IsQuasicoherent] (U : X.Opens) (hU : IsAffineOpen U)
    (s : (M.restrict U.ι).GeneratingSections) [s.IsFiniteType] :
    Module.Finite Γ(X,U) Γ(M,U) := by
  let : IsAffine U.toScheme := hU
  let : Module.Finite Γ(U.toScheme,⊤) Γ(M.restrict U.ι,⊤) :=
    affine_sections_finite_of_generators (M.restrict U.ι) s
  let σ := (U.ι.appIso ⊤).inv.hom
  let φ : Γ(M.restrict U.ι,⊤) →ₛₗ[σ] Γ(M,U.ι ''ᵁ ⊤) := {
    toFun := (M.restrictAppIso U.ι ⊤).hom
    map_add' := map_add _
    map_smul' := by intro r m; rfl }
  have hφ : Function.Surjective φ :=
    (ConcreteCategory.bijective_of_isIso (M.restrictAppIso U.ι ⊤).hom).surjective
  have h := Module.Finite.of_surjective φ hφ
  rwa [U.ι_image_top] at h

theorem spec_sections_finite_of_localGenerators {R : CommRingCat.{u}}
    (M : (Spec R).Modules) [M.IsQuasicoherent] (hM : LocallyFinitelyGenerated M) :
    Module.Finite R ((modulesSpecToSheaf.obj M).obj.obj (op ⊤)) := by
  classical
  let D (r : R) : (Spec R).Opens := PrimeSpectrum.basicOpen r
  let t : Set R := {r | ∃ s : (M.restrict (D r).ι).GeneratingSections, s.IsFiniteType}
  have ht : Ideal.span t = ⊤ := by
    rw [← PrimeSpectrum.iSup_basicOpen_eq_top_iff']
    apply top_unique
    intro x hx
    obtain ⟨U,hxU,s,hs⟩ := hM x
    obtain ⟨_,⟨_,⟨r,rfl⟩,rfl⟩,hxr,hrU⟩ :=
      PrimeSpectrum.isBasis_basic_opens.exists_subset_of_mem_open hxU U.isOpen
    exact Opens.mem_iSup.mpr ⟨r, Opens.mem_iSup.mpr
      ⟨finite_generators_of_le M hrU s,hxr⟩⟩
  let N := (modulesSpecToSheaf.obj M).obj.obj (op ⊤)
  let A (r : t) := Γ(Spec R, PrimeSpectrum.basicOpen r.val)
  let P (r : t) := Γ(M, PrimeSpectrum.basicOpen r.val)
  let (r : t) : Algebra R (A r) := StructureSheaf.openAlgebra (R := R) (op (PrimeSpectrum.basicOpen r.val))
  let (r : t) : IsLocalization.Away r.val (A r) := inferInstanceAs
    (IsLocalization.Away r.val ((Spec.structureSheaf R).obj.obj (op (PrimeSpectrum.basicOpen r.val))))
  let (r : t) : Module (A r) (P r) :=
    (M.val.obj (op (PrimeSpectrum.basicOpen r.val))).isModule
  let (r : t) : Module R (P r) :=
    ((modulesSpecToSheaf.obj M).obj.obj (op (PrimeSpectrum.basicOpen r.val))).isModule
  let (r : t) : IsScalarTower R (A r) (P r) :=
    IsScalarTower.of_compHom R (A r) (P r)
  let f (r : t) : N →ₗ[R] P r :=
    ((modulesSpecToSheaf.obj M).obj.map (homOfLE le_top).op).hom
  have hloc := (isIso_fromTildeΓ_iff_isLocalizing M).mp inferInstance
  let (r : t) : IsLocalizedModule.Away r.val (f r) := hloc r.val
  have hfin (r : t) : Module.Finite (A r) (P r) := by
    obtain ⟨s, hs⟩ := r.property
    exact affine_open_sections_finite_of_generators M (D r.val)
      (IsAffineOpen.Spec_basicOpen r.val) s
  exact Module.Finite.of_localizationSpan' t ht f hfin

theorem LocallyFinitelyGenerated.restrict {X Y : Scheme.{u}} {M : Y.Modules}
    (hM : LocallyFinitelyGenerated M) (f : X ⟶ Y) [IsOpenImmersion f] :
    LocallyFinitelyGenerated (M.restrict f) := by
  intro x
  obtain ⟨U, hxU, s, hs⟩ := hM (f x)
  let V := f ⁻¹ᵁ U
  let F : SheafOfModules U.toScheme.ringCatSheaf ⥤ SheafOfModules V.toScheme.ringCatSheaf :=
    Scheme.Modules.restrictFunctor (f ∣_ U)
  let : Limits.PreservesColimitsOfSize.{u, u} F :=
    (Scheme.Modules.restrictAdjunction (f ∣_ U)).leftAdjoint_preservesColimits
  let t := s.map F
    (Scheme.Modules.restrictUnitIso (f ∣_ U)).symm
  let e := (Scheme.Modules.restrictFunctorComp (f ∣_ U) U.ι).app M
  have e' : M.restrict (V.ι ≫ f) ≅ (M.restrict U.ι).restrict (f ∣_ U) := by
    change M.restrict ((f ∣_ U) ≫ U.ι) ≅ (M.restrict U.ι).restrict (f ∣_ U) at e
    simpa only [V, morphismRestrict_ι] using e
  let e'' := ((Scheme.Modules.restrictFunctorComp V.ι f).app M).symm ≪≫ e'
  exact ⟨V, hxU, SheafOfModules.GeneratingSections.equivOfIso e''.symm t,
    ⟨SheafOfModules.GeneratingSections.IsFiniteType.finite (σ := s)⟩⟩

theorem affine_sections_finite_of_localGenerators {X : Scheme.{u}} [IsAffine X]
    (M : X.Modules) [M.IsQuasicoherent] (hM : LocallyFinitelyGenerated M) :
    Module.Finite Γ(X,⊤) Γ(M,⊤) := by
  let f := X.isoSpec.inv
  let J := M.restrict f
  let R := Γ(X,⊤)
  let N := (modulesSpecToSheaf.obj J).obj.obj (op ⊤)
  let : Module.Finite R N := spec_sections_finite_of_localGenerators J
    (hM.restrict f)
  let σ : R →+* Γ(X,f ''ᵁ ⊤) := (f.appIso ⊤).inv.hom.comp (Scheme.ΓSpecIso R).inv.hom
  let φ : N →ₛₗ[σ] Γ(M,f ''ᵁ ⊤) := {
    toFun := (M.restrictAppIso f ⊤).hom
    map_add' := map_add _
    map_smul' := by intro r m; rfl }
  have hφ : Function.Surjective φ :=
    (ConcreteCategory.bijective_of_isIso (M.restrictAppIso f ⊤).hom).surjective
  have hf : f ''ᵁ (⊤ : (Spec R).Opens) = ⊤ := by
    ext x
    change (∃ y : Spec R, y ∈ (⊤ : (Spec R).Opens) ∧ f y = x) ↔ True
    simp only [Opens.mem_top, true_and, iff_true]
    exact (ConcreteCategory.bijective_of_isIso f.base).surjective x
  have h := Module.Finite.of_surjective φ hφ
  rw [hf] at h
  exact h

theorem affine_sections_finite {X : Scheme.{u}} [IsAffine X]
    (M : X.Modules) [M.IsFinitePresentation] : Module.Finite Γ(X,⊤) Γ(M,⊤) := by
  let := finitePresentation_quasicoherent M
  exact affine_sections_finite_of_localGenerators M (locallyFinitelyGenerated_of_finitePresentation M)

theorem finite_isoSpec_sections {X : Scheme.{u}} [IsAffine X]
    (M : X.Modules) [Module.Finite Γ(X,⊤) Γ(M,⊤)] :
    Module.Finite Γ(X,⊤)
      ((modulesSpecToSheaf.obj (M.restrict X.isoSpec.inv)).obj.obj (op ⊤)) := by
  let f := X.isoSpec.inv
  let R := Γ(X,⊤)
  let N : ModuleCat R := (modulesSpecToSheaf.obj (M.restrict f)).obj.obj (op ⊤)
  have hf : f ''ᵁ (⊤ : (Spec R).Opens) = ⊤ := by
    ext x
    change (∃ y : Spec R, y ∈ (⊤ : (Spec R).Opens) ∧ f y = x) ↔ True
    simp only [Opens.mem_top, true_and, iff_true]
    exact (ConcreteCategory.bijective_of_isIso f.base).surjective x
  have : Module.Finite Γ(X,f ''ᵁ ⊤) Γ(M,f ''ᵁ ⊤) := by
    rw [hf]
    infer_instance
  let σ : Γ(X,f ''ᵁ ⊤) →+* R := (Scheme.ΓSpecIso R).hom.hom.comp (f.appIso ⊤).hom.hom
  let φ : Γ(M,f ''ᵁ ⊤) →ₛₗ[σ] N := {
    toFun := (M.restrictAppIso f ⊤).inv
    map_add' := map_add _
    map_smul' := by
      intro r m
      change (M.restrictAppIso f ⊤).inv (r • m) =
        ((Scheme.ΓSpecIso R).inv ((Scheme.ΓSpecIso R).hom ((f.appIso ⊤).hom r))) •
          (M.restrictAppIso f ⊤).inv m
      rw [Iso.hom_inv_id_apply]
      exact congr($(M.smul_restrictAppIso_inv f ⊤ r) m) }
  exact Module.Finite.of_surjective φ
    (ConcreteCategory.bijective_of_isIso (M.restrictAppIso f ⊤).inv).surjective

theorem spec_exists_finite_generators {R : CommRingCat.{u}}
    (M : (Spec R).Modules) [M.IsQuasicoherent]
    [Module.Finite R ((modulesSpecToSheaf.obj M).obj.obj (op ⊤))] :
    ∃ s : M.GeneratingSections, s.IsFiniteType := by
  let N : ModuleCat R := (modulesSpecToSheaf.obj M).obj.obj (op ⊤)
  obtain ⟨I,hI,v,hv⟩ : ∃ (I : Type u) (_ : Finite I) (v : I → N),
      Submodule.span R (Set.range v) = ⊤ :=
    Submodule.fg_iff_exists_finite_generating_family.mp (Module.Finite.fg_top (R := R) (M := N))
  let f : ModuleCat.of R (I →₀ R) ⟶ N := ModuleCat.ofHom (X := I →₀ R) (Y := N) (Finsupp.linearCombination (M := N) R v)
  have : Epi f := (ModuleCat.epi_iff_surjective f).mpr <| by
    change Function.Surjective (Finsupp.linearCombination (M := N) R v)
    rw [← LinearMap.range_eq_top, Finsupp.range_linearCombination, hv]
  let p : SheafOfModules.free I ⟶ M :=
    (tildeFinsupp I).inv ≫ (tilde.functor R).map f ≫ M.fromTildeΓ
  have hmap : Epi ((tilde.functor R).map f) := inferInstance
  have : Epi M.fromTildeΓ := inferInstance
  have hp : Epi p := by
    change Epi ((tildeFinsupp I).inv ≫ (tilde.functor R).map f ≫ M.fromTildeΓ)
    let hΓ := Scheme.Modules.isIso_fromTildeΓ_of_isQuasicoherent M
    exact epi_iso_comp_iso (tildeFinsupp I).symm ((tilde.functor R).map f) hmap
      (@asIso _ _ _ _ M.fromTildeΓ hΓ)
  let s : M.GeneratingSections := {
    I := I
    s := M.freeHomEquiv p
    epi := by simpa only [Equiv.symm_apply_apply] using hp }
  exact ⟨s, ⟨hI⟩⟩

theorem affine_exists_finite_generators {X : Scheme.{u}} [IsAffine X]
    (M : X.Modules) [M.IsQuasicoherent] [Module.Finite Γ(X,⊤) Γ(M,⊤)] :
    ∃ s : M.GeneratingSections, s.IsFiniteType := by
  let f := X.isoSpec.inv
  let J := M.restrict f
  let : Module.Finite Γ(X,⊤) ((modulesSpecToSheaf.obj J).obj.obj (op ⊤)) :=
    finite_isoSpec_sections M
  obtain ⟨s,hs⟩ := spec_exists_finite_generators J
  let g := X.isoSpec.hom
  let F : SheafOfModules (Spec Γ(X,⊤)).ringCatSheaf ⥤ SheafOfModules X.ringCatSheaf :=
    Scheme.Modules.restrictFunctor g
  let : Limits.PreservesColimitsOfSize.{u, u} F :=
    (Scheme.Modules.restrictAdjunction g).leftAdjoint_preservesColimits
  let t := s.map F (Scheme.Modules.restrictUnitIso g).symm
  let e₁ := (Scheme.Modules.restrictFunctorComp g f).app M
  have e₂ : M.restrict (𝟙 X) ≅ J.restrict g := by
    change M.restrict (g ≫ f) ≅ J.restrict g at e₁
    simpa only [g, f, Iso.hom_inv_id] using e₁
  let e := e₂.symm ≪≫ Scheme.Modules.restrictFunctorId.app M
  exact ⟨SheafOfModules.GeneratingSections.equivOfIso e t,
    ⟨hs.finite⟩⟩

theorem affine_exists_finite_generators_of_finitePresentation {X : Scheme.{u}} [IsAffine X]
    (M : X.Modules) [M.IsFinitePresentation] :
    ∃ s : M.GeneratingSections, s.IsFiniteType := by
  let := finitePresentation_quasicoherent M
  have := affine_sections_finite M
  exact affine_exists_finite_generators M

theorem affine_open_sections_finite {X : Scheme.{u}} (M : X.Modules)
    [M.IsFinitePresentation] (U : X.Opens) (hU : IsAffineOpen U) :
    Module.Finite Γ(X,U) Γ(M,U) := by
  let : IsAffine U.toScheme := hU
  let := finitePresentation_quasicoherent M
  have := affine_sections_finite_of_localGenerators (M.restrict U.ι)
    ((locallyFinitelyGenerated_of_finitePresentation M).restrict U.ι)
  obtain ⟨s,hs⟩ := affine_exists_finite_generators (M.restrict U.ι)
  exact affine_open_sections_finite_of_generators M U hU s

end
end PiExponent.CoherentAffineFinite

end OAI
end Source0009

section Source0010
/-
Modification notice for the LogTwo project.
Derived from openai/math (Apache-2.0), revision adc7f1241b42e322a6451854ab7e4b4c146bf78a.
Original source: lean/OAI/NumberTheory/PiExponent/Approximation/CoherentTwistPresentation.lean
Changes: Convert module/import declarations to the Lean 4.34 public module format.
See ../../../../../THIRD_PARTY_NOTICES.txt for provenance and the recorded changes.
-/




namespace OAI

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite

namespace PiExponent.CoherentTwist

universe u
variable {R : CommRingCat.{u}} (M : (Spec R).Modules) [M.IsQuasicoherent]

abbrev affineSections (U : (Spec R).Opens) :=
  (modulesSpecToSheaf.obj M).obj.obj (op U)

abbrev principalRestriction (r : R) :=
  ((modulesSpecToSheaf.obj M).obj.map (PrimeSpectrum.basicOpen r).leTop.op).hom

theorem principalRestriction_localizes (r : R) :
    IsLocalizedModule.Away r (principalRestriction M r) :=
  ((isIso_fromTildeΓ_iff_isLocalizing M).mp inferInstance) r

theorem principal_section_extends (r : R)
    (x : affineSections M (PrimeSpectrum.basicOpen r)) :
    ∃ N : ℕ, ∀ n ≥ N, ∃ y : affineSections M ⊤,
      principalRestriction M r y = r ^ n • x := by
  let := principalRestriction_localizes M r
  obtain ⟨N, y, hy⟩ := (inferInstance : IsLocalizedModule.Away r
    (principalRestriction M r)).surj _ _ x
  refine ⟨N, fun n hn => ⟨r ^ (n - N) • y, ?_⟩⟩
  rw [map_smul, ← hy, ← mul_smul, ← pow_add, Nat.sub_add_cancel hn]

theorem principal_section_zero (r : R) (x : affineSections M ⊤)
    (hx : principalRestriction M r x = 0) :
    ∃ N : ℕ, ∀ n ≥ N, r ^ n • x = 0 := by
  let := principalRestriction_localizes M r
  obtain ⟨⟨_, N, rfl⟩, hN⟩ :=
    (IsLocalizedModule.eq_zero_iff (.powers r) (principalRestriction M r)).mp hx
  change r ^ N • x = 0 at hN
  refine ⟨N, fun n hn => ?_⟩
  rw [← Nat.sub_add_cancel hn, pow_add, mul_smul, hN, smul_zero]

theorem finite_principal_sections_extend {ι : Type*} [Fintype ι] (r : R)
    (x : ι → affineSections M (PrimeSpectrum.basicOpen r)) :
    ∃ N : ℕ, ∀ n ≥ N, ∃ y : ι → affineSections M ⊤,
      ∀ i, principalRestriction M r (y i) = r ^ n • x i := by
  classical
  choose N hN using fun i => principal_section_extends M r (x i)
  refine ⟨Finset.univ.sup N, fun n hn => ?_⟩
  have hn' (i : ι) : N i ≤ n :=
    (Finset.le_sup (f := N) (Finset.mem_univ i)).trans hn
  choose y hy using fun i => hN i n (hn' i)
  exact ⟨y, hy⟩

theorem finite_principal_sections_zero {ι : Type*} [Fintype ι] (r : R)
    (x : ι → affineSections M ⊤)
    (hx : ∀ i, principalRestriction M r (x i) = 0) :
    ∃ N : ℕ, ∀ n ≥ N, ∀ i, r ^ n • x i = 0 := by
  classical
  choose N hN using fun i => principal_section_zero M r (x i) (hx i)
  refine ⟨Finset.univ.sup N, fun n hn i => ?_⟩
  exact hN i n ((Finset.le_sup (f := N) (Finset.mem_univ i)).trans hn)

open TopologicalSpace
variable {X : Scheme.{u}} {P Q : X.Modules}

lemma app_zero_of_restrict (φ : P ⟶ Q) (U W : X.Opens) (hW : W ≤ U)
    (h : (Scheme.Modules.restrictFunctor U.ι).map φ = 0) : φ.app W = 0 := by
  have hz := congrArg (fun q : P.restrict U.ι ⟶ Q.restrict U.ι =>
    q.app (U.ι ⁻¹ᵁ W)) h
  have he : U.ι ''ᵁ U.ι ⁻¹ᵁ W = W := by
    rw [Scheme.Hom.image_preimage_eq_opensRange_inf, Scheme.Opens.opensRange_ι,
      inf_eq_right.mpr hW]
  change φ.app (U.ι ''ᵁ U.ι ⁻¹ᵁ W) = 0 at hz
  suffices hh : ∀ A : X.Opens, A = W → φ.app A = 0 → φ.app W = 0 from hh _ he hz
  intro A hA hφ
  subst A
  exact hφ

lemma eq_zero_of_local (φ : P ⟶ Q)
    (h : ∀ x : X, ∃ U : X.Opens, x ∈ U ∧
      (Scheme.Modules.restrictFunctor U.ι).map φ = 0) : φ = 0 := by
  ext W m
  change φ.app W m = 0
  let F : (X : TopCat).Sheaf AddCommGrpCat := (SheafOfModules.toSheaf X.ringCatSheaf).obj Q
  apply TopCat.Presheaf.section_ext F W (φ.app W m) 0
  intro x hx
  obtain ⟨U,hxU,hU⟩ := h x
  let V : X.Opens := W ⊓ U
  have hv : φ.app V = 0 := app_zero_of_restrict φ U V inf_le_right hU
  change Q.presheaf.germ W x hx (φ.app W m) = Q.presheaf.germ W x hx 0
  rw [← TopCat.Presheaf.germ_res_apply Q.presheaf (homOfLE (show V ≤ W from inf_le_left))
    x (show x ∈ V from ⟨hx,hxU⟩)]
  have hn := CategoryTheory.congr_fun (φ.mapPresheaf.naturality
    (homOfLE (show V ≤ W from inf_le_left)).op) m
  change φ.app V (P.presheaf.map (homOfLE inf_le_left).op m) =
    Q.presheaf.map (homOfLE inf_le_left).op (φ.app W m) at hn
  rw [← hn,hv]
  simp

lemma epi_of_local (φ : P ⟶ Q)
    (h : ∀ x : X, ∃ U : X.Opens, x ∈ U ∧
      Epi ((Scheme.Modules.restrictFunctor U.ι).map φ)) : Epi φ := by
  apply (Preadditive.epi_iff_cancel_zero _).mpr
  intro T g hg
  apply eq_zero_of_local
  intro x
  obtain ⟨U,hx,hU⟩ := h x
  let := hU
  refine ⟨U,hx,?_⟩
  apply (cancel_epi ((Scheme.Modules.restrictFunctor U.ι).map φ)).mp
  rw [← Functor.map_comp,hg,Functor.map_zero,comp_zero]

lemma mono_of_local (φ : P ⟶ Q)
    (h : ∀ x : X, ∃ U : X.Opens, x ∈ U ∧
      Mono ((Scheme.Modules.restrictFunctor U.ι).map φ)) : Mono φ := by
  apply (Preadditive.mono_iff_cancel_zero _).mpr
  intro T g hg
  apply eq_zero_of_local
  intro x
  obtain ⟨U, hx, hU⟩ := h x
  let := hU
  refine ⟨U, hx, ?_⟩
  apply (cancel_mono ((Scheme.Modules.restrictFunctor U.ι).map φ)).mp
  rw [← Functor.map_comp, hg, Functor.map_zero, zero_comp]

lemma exact_of_local (S : ShortComplex X.Modules)
    (h : ∀ x : X, ∃ U : X.Opens, x ∈ U ∧
      (S.map (Scheme.Modules.restrictFunctor U.ι)).Exact) : S.Exact := by
  rw [ShortComplex.exact_iff_isZero_homology]
  apply (IsZero.iff_id_eq_zero _).mpr
  apply eq_zero_of_local
  intro x
  obtain ⟨U, hx, hU⟩ := h x
  have hz : IsZero ((Scheme.Modules.restrictFunctor U.ι).obj S.homology) :=
    ((ShortComplex.exact_iff_isZero_homology _).mp hU).of_iso
      (S.mapHomologyIso (Scheme.Modules.restrictFunctor U.ι)).symm
  refine ⟨U, hx, ?_⟩
  rw [CategoryTheory.Functor.map_id]
  exact hz.eq_of_src _ _

end PiExponent.CoherentTwist

namespace PiExponentSeshadri.Geometry
open MonoidalCategory
variable {X : Scheme}

private lemma tensorRestrict_natural {C D : Type*} [Category C] [Category D]
    [mC : MonoidalCategory C] [mD : MonoidalCategory D] (R F : C ⥤ D) [F.OplaxMonoidal]
    (e : R ≅ F) {M N P Q : C} (f : M ⟶ N) (g : P ⟶ Q) :
    R.map (f ⊗ₘ g) ≫ (e.hom.app (N ⊗ Q) ≫
      Functor.OplaxMonoidal.δ F N Q ≫ (e.inv.app N ⊗ₘ e.inv.app Q)) =
    (e.hom.app (M ⊗ P) ≫ Functor.OplaxMonoidal.δ F M P ≫
      (e.inv.app M ⊗ₘ e.inv.app P)) ≫ (R.map f ⊗ₘ R.map g) := by
  rw [← Category.assoc, e.hom.naturality, Category.assoc,
    ← Category.assoc (F.map (f ⊗ₘ g)), ← Functor.OplaxMonoidal.δ_natural,
    Category.assoc, tensorHom_comp_tensorHom, e.inv.naturality,
    e.inv.naturality, ← tensorHom_comp_tensorHom]
  simp only [Category.assoc]

private lemma modulePresheafTensorRestrict_natural_aux (U : X.Opens)
    {M N P Q : PresheafOfModules X.ringCatSheaf.obj}
    (f : M ⟶ N) (g : P ⟶ Q) :
    type_of% (tensorRestrict_natural
    (C := PresheafOfModules (X.presheaf ⋙ forget₂ CommRingCat RingCat))
    (D := PresheafOfModules
      ((U.ι.opensFunctor.op ⋙ X.presheaf) ⋙ forget₂ CommRingCat RingCat))
    (mC := PresheafOfModulesOfCommRing.monoidalCategory (R := X.presheaf))
    (mD := PresheafOfModulesOfCommRing.monoidalCategory
      (R := U.ι.opensFunctor.op ⋙ X.presheaf))
    (modulePresheafRestrict U.ι)
    (PresheafOfModules.pushforward₀OfCommRingCat U.ι.opensFunctor X.presheaf)
    (modulePresheafRestrictOpensIso U) f g) :=
  tensorRestrict_natural
    (C := PresheafOfModules (X.presheaf ⋙ forget₂ CommRingCat RingCat))
    (D := PresheafOfModules
      ((U.ι.opensFunctor.op ⋙ X.presheaf) ⋙ forget₂ CommRingCat RingCat))
    (mC := PresheafOfModulesOfCommRing.monoidalCategory (R := X.presheaf))
    (mD := PresheafOfModulesOfCommRing.monoidalCategory
      (R := U.ι.opensFunctor.op ⋙ X.presheaf))
    (modulePresheafRestrict U.ι)
    (PresheafOfModules.pushforward₀OfCommRingCat U.ι.opensFunctor X.presheaf)
    (modulePresheafRestrictOpensIso U) f g

lemma modulePresheafTensorRestrict_natural (U : X.Opens)
    {M N P Q : PresheafOfModules X.ringCatSheaf.obj}
    (f : M ⟶ N) (g : P ⟶ Q) :
    (modulePresheafRestrict U.ι).map
        (PresheafOfModulesOfCommRing.Monoidal.tensorHom (R := X.presheaf) f g) ≫
      (modulePresheafTensorRestrict U N Q).hom =
    (modulePresheafTensorRestrict U M P).hom ≫
      PresheafOfModulesOfCommRing.Monoidal.tensorHom (R := U.toScheme.presheaf)
        ((modulePresheafRestrict U.ι).map f) ((modulePresheafRestrict U.ι).map g) := by
  dsimp only [modulePresheafTensorRestrict, Iso.trans_hom, Iso.symm_hom,
    Functor.Monoidal.μIso_inv, tensorIso_hom]
  exact modulePresheafTensorRestrict_natural_aux U f g

lemma moduleTensorRestrict_natural (U : X.Opens) {M N P Q : X.Modules}
    (f : M ⟶ N) (g : P ⟶ Q) :
    (Scheme.Modules.restrictFunctor U.ι).map (moduleTensorMap f g) ≫
      (moduleTensorRestrict U N Q).hom =
    (moduleTensorRestrict U M P).hom ≫
      moduleTensorMap ((Scheme.Modules.restrictFunctor U.ι).map f)
        ((Scheme.Modules.restrictFunctor U.ι).map g) := by
  let K : PresheafOfModules X.ringCatSheaf.obj ⥤ X.Modules :=
    PresheafOfModules.sheafification (𝟙 X.ringCatSheaf.obj)
  let R : X.Modules ⥤ U.toScheme.Modules := Scheme.Modules.restrictFunctor U.ι
  let Rpre : PresheafOfModules X.ringCatSheaf.obj ⥤
      PresheafOfModules U.toScheme.ringCatSheaf.obj := modulePresheafRestrict U.ι
  let S : PresheafOfModules U.toScheme.ringCatSheaf.obj ⥤ U.toScheme.Modules :=
    PresheafOfModules.sheafification (𝟙 U.toScheme.ringCatSheaf.obj)
  let e : K ⋙ R ≅ Rpre ⋙ S := moduleSheafificationRestrict U.ι
  let h := PresheafOfModulesOfCommRing.Monoidal.tensorHom (R := X.presheaf) f.val g.val
  let k := PresheafOfModulesOfCommRing.Monoidal.tensorHom (R := U.toScheme.presheaf)
    (Rpre.map f.val) (Rpre.map g.val)
  let a := (modulePresheafTensorRestrict U M.val P.val).hom
  let b := (modulePresheafTensorRestrict U N.val Q.val).hom
  change R.map (K.map h) ≫ (e.hom.app _ ≫ S.map b) =
    (e.hom.app _ ≫ S.map a) ≫ S.map k
  have ht : Rpre.map h ≫ b = a ≫ k := modulePresheafTensorRestrict_natural U f.val g.val
  calc
    _ = (R.map (K.map h) ≫ e.hom.app _) ≫ S.map b :=
      (Category.assoc _ _ _).symm
    _ = (e.hom.app _ ≫ S.map (Rpre.map h)) ≫ S.map b :=
      congrArg (· ≫ S.map b) (e.hom.naturality h)
    _ = e.hom.app _ ≫ (S.map (Rpre.map h) ≫ S.map b) := Category.assoc _ _ _
    _ = e.hom.app _ ≫ S.map (Rpre.map h ≫ b) :=
      congrArg (e.hom.app _ ≫ ·) (S.map_comp _ _).symm
    _ = e.hom.app _ ≫ S.map (a ≫ k) :=
      congrArg (fun t => e.hom.app _ ≫ S.map t) ht
    _ = e.hom.app _ ≫ (S.map a ≫ S.map k) :=
      congrArg (e.hom.app _ ≫ ·) (S.map_comp _ _)
    _ = _ := (Category.assoc _ _ _).symm

def moduleTensorRightFunctor (L : X.Modules) : X.Modules ⥤ X.Modules where
  obj M := moduleTensor X M L
  map f := moduleTensorMap f (𝟙 L)
  map_id M := moduleTensorMap_id M L
  map_comp f g := by simpa using moduleTensorMap_comp f g (𝟙 L) (𝟙 L)

@[simp] theorem moduleTensorIso_hom {M N P Q : X.Modules}
    (e : M ≅ N) (f : P ≅ Q) :
    (moduleTensorIso e f).hom = moduleTensorMap e.hom f.hom := rfl

@[reassoc] theorem moduleTensorRightUnit_natural {M N : X.Modules} (f : M ⟶ N) :
    moduleTensorMap f (𝟙 (structureSheaf X)) ≫ (moduleTensorRightUnit N).hom =
      (moduleTensorRightUnit M).hom ≫ f := by
  let : MonoidalCategory (PresheafOfModules X.ringCatSheaf.obj) :=
    PresheafOfModulesOfCommRing.monoidalCategory (R := X.presheaf)
  let S : PresheafOfModules X.ringCatSheaf.obj ⥤ X.Modules :=
    PresheafOfModules.sheafification (𝟙 X.ringCatSheaf.obj)
  let adj := PresheafOfModules.sheafificationAdjunction (R := X.ringCatSheaf)
    (𝟙 X.ringCatSheaf.obj)
  change S.map (f.val ⊗ₘ 𝟙 _) ≫ (S.map (ρ_ N.val).hom ≫ adj.counit.app N) =
    (S.map (ρ_ M.val).hom ≫ adj.counit.app M) ≫ f
  have hu : (f.val ⊗ₘ 𝟙 _) ≫ (ρ_ N.val).hom = (ρ_ M.val).hom ≫ f.val := by
    simpa only [tensorHom_id] using rightUnitor_naturality f.val
  have hS : S.map (f.val ⊗ₘ 𝟙 _) ≫ S.map (ρ_ N.val).hom =
      S.map (ρ_ M.val).hom ≫ S.map f.val :=
    (S.map_comp _ _).symm.trans ((congrArg S.map hu).trans (S.map_comp _ _))
  calc
    _ = (S.map (f.val ⊗ₘ 𝟙 _) ≫ S.map (ρ_ N.val).hom) ≫ adj.counit.app N :=
      (Category.assoc _ _ _).symm
    _ = (S.map (ρ_ M.val).hom ≫ S.map f.val) ≫ adj.counit.app N :=
      congrArg (· ≫ adj.counit.app N) hS
    _ = S.map (ρ_ M.val).hom ≫ (S.map f.val ≫ adj.counit.app N) :=
      Category.assoc _ _ _
    _ = S.map (ρ_ M.val).hom ≫ (adj.counit.app M ≫ f) :=
      congrArg (S.map (ρ_ M.val).hom ≫ ·) (adj.counit.naturality f)
    _ = _ := (Category.assoc _ _ _).symm

def moduleTensorFrame (M : X.Modules) {L : X.Modules}
    (e : L ≅ structureSheaf X) : moduleTensor X M L ≅ M :=
  moduleTensorIso (Iso.refl M) e ≪≫ moduleTensorRightUnit M

@[reassoc] theorem moduleTensorFrame_natural {M N L : X.Modules}
    (f : M ⟶ N) (e : L ≅ structureSheaf X) :
    moduleTensorMap f (𝟙 L) ≫ (moduleTensorFrame N e).hom =
      (moduleTensorFrame M e).hom ≫ f := by
  simp only [moduleTensorFrame, Iso.trans_hom, moduleTensorIso_hom, Iso.refl_hom]
  calc
    _ = moduleTensorMap f e.hom ≫ (moduleTensorRightUnit N).hom := by
      rw [← Category.assoc, ← moduleTensorMap_comp]
      simp only [Category.comp_id, Category.id_comp]
    _ = moduleTensorMap (𝟙 M) e.hom ≫
        moduleTensorMap f (𝟙 (structureSheaf X)) ≫ (moduleTensorRightUnit N).hom := by
      rw [← Category.assoc, ← moduleTensorMap_comp]
      simp only [Category.comp_id, Category.id_comp]
    _ = _ := by rw [moduleTensorRightUnit_natural, Category.assoc]

def moduleTensorRestrictFrame (U : X.Opens) (L : X.Modules)
    (e : L.restrict U.ι ≅ structureSheaf U.toScheme) :
    moduleTensorRightFunctor L ⋙ Scheme.Modules.restrictFunctor U.ι ≅
      Scheme.Modules.restrictFunctor U.ι :=
  NatIso.ofComponents
    (fun M => moduleTensorRestrict U M L ≪≫ moduleTensorFrame (M.restrict U.ι) e)
    (by
      intro M N f
      change (Scheme.Modules.restrictFunctor U.ι).map (moduleTensorMap f (𝟙 L)) ≫
          ((moduleTensorRestrict U N L).hom ≫ (moduleTensorFrame (N.restrict U.ι) e).hom) =
        ((moduleTensorRestrict U M L).hom ≫ (moduleTensorFrame (M.restrict U.ι) e).hom) ≫
          (Scheme.Modules.restrictFunctor U.ι).map f
      rw [← Category.assoc, moduleTensorRestrict_natural, Category.assoc,
        CategoryTheory.Functor.map_id, moduleTensorFrame_natural, Category.assoc])

theorem moduleTensorMap_epi {M N : X.Modules} (f : M ⟶ N) [Epi f]
    (L : LineBundle X) : Epi (moduleTensorMap f (𝟙 L.sheaf)) := by
  apply PiExponent.CoherentTwist.epi_of_local
  intro x
  obtain ⟨U, hx, ⟨e⟩⟩ := L.locallyRankOne x
  refine ⟨U, hx, ?_⟩
  let F : X.Modules ⥤ U.toScheme.Modules := Scheme.Modules.restrictFunctor U.ι
  let E : moduleTensorRightFunctor L.sheaf ⋙ F ≅ F := moduleTensorRestrictFrame U L.sheaf e
  have h : F.map (moduleTensorMap f (𝟙 L.sheaf)) =
      (E.app M).hom ≫ F.map f ≫ (E.app N).inv := by
    exact ((E.app N).eq_comp_inv.mpr (E.hom.naturality f)).trans
      (Category.assoc _ _ _)
  rw [h]
  let : Epi (F.map f) := inferInstanceAs
    (Epi ((Scheme.Modules.restrictFunctor U.ι).map f))
  let : IsIso (E.app M).hom := (E.app M).isIso_hom
  let : IsIso (E.app N).inv := (E.app N).isIso_inv
  exact (inferInstance : Epi (C := U.toScheme.Modules)
    ((E.app M).hom ≫ F.map f ≫ (E.app N).inv))

theorem moduleTensorMap_mono {M N : X.Modules} (f : M ⟶ N) [Mono f]
    (L : LineBundle X) : Mono (moduleTensorMap f (𝟙 L.sheaf)) := by
  apply PiExponent.CoherentTwist.mono_of_local
  intro x
  obtain ⟨U, hx, ⟨e⟩⟩ := L.locallyRankOne x
  refine ⟨U, hx, ?_⟩
  let F : X.Modules ⥤ U.toScheme.Modules := Scheme.Modules.restrictFunctor U.ι
  let E : moduleTensorRightFunctor L.sheaf ⋙ F ≅ F := moduleTensorRestrictFrame U L.sheaf e
  have h : F.map (moduleTensorMap f (𝟙 L.sheaf)) =
      (E.app M).hom ≫ F.map f ≫ (E.app N).inv := by
    exact ((E.app N).eq_comp_inv.mpr (E.hom.naturality f)).trans
      (Category.assoc _ _ _)
  rw [h]
  let : Mono (F.map f) := inferInstanceAs
    (Mono ((Scheme.Modules.restrictFunctor U.ι).map f))
  let : IsIso (E.app M).hom := (E.app M).isIso_hom
  let : IsIso (E.app N).inv := (E.app N).isIso_inv
  exact (inferInstance : Mono (C := U.toScheme.Modules)
    ((E.app M).hom ≫ F.map f ≫ (E.app N).inv))

instance moduleTensorRightFunctor_preservesZero (L : LineBundle X) :
    (moduleTensorRightFunctor L.sheaf).PreservesZeroMorphisms where
  map_zero M N := by
    apply PiExponent.CoherentTwist.eq_zero_of_local
    intro x
    obtain ⟨U, hx, ⟨e⟩⟩ := L.locallyRankOne x
    refine ⟨U, hx, ?_⟩
    let E := moduleTensorRestrictFrame U L.sheaf e
    apply (cancel_mono (E.app N).hom).mp
    rw [zero_comp]
    change ((moduleTensorRightFunctor L.sheaf ⋙ Scheme.Modules.restrictFunctor U.ι).map
      (0 : M ⟶ N)) ≫ E.hom.app N = 0
    rw [E.hom.naturality, CategoryTheory.Functor.map_zero, comp_zero]

theorem moduleTensorRightFunctor_exact (L : LineBundle X)
    (S : ShortComplex X.Modules) (hS : S.Exact) :
    (S.map (moduleTensorRightFunctor L.sheaf)).Exact := by
  apply PiExponent.CoherentTwist.exact_of_local
  intro x
  obtain ⟨U, hx, ⟨e⟩⟩ := L.locallyRankOne x
  refine ⟨U, hx, ?_⟩
  exact ShortComplex.exact_of_iso
    (S.mapNatIso (moduleTensorRestrictFrame U L.sheaf e)).symm
    (hS.map (Scheme.Modules.restrictFunctor U.ι))

theorem moduleTensorRightFunctor_shortExact (L : LineBundle X)
    (S : ShortComplex X.Modules) (hS : S.ShortExact) :
    (S.map (moduleTensorRightFunctor L.sheaf)).ShortExact where
  exact := moduleTensorRightFunctor_exact L S hS.exact
  mono_f := by
    have := hS.mono_f
    exact moduleTensorMap_mono S.f L
  epi_g := by
    have := hS.epi_g
    exact moduleTensorMap_epi S.g L

instance moduleTensorRightFunctor_additive (L : LineBundle X) :
    (moduleTensorRightFunctor L.sheaf).Additive where
  map_add {M N} {f g} := by
    apply sub_eq_zero.mp
    apply PiExponent.CoherentTwist.eq_zero_of_local
    intro x
    obtain ⟨U, hx, ⟨e⟩⟩ := L.locallyRankOne x
    refine ⟨U, hx, ?_⟩
    let F := Scheme.Modules.restrictFunctor U.ι
    let T := moduleTensorRightFunctor L.sheaf
    let E := moduleTensorRestrictFrame U L.sheaf e
    have h (a : M ⟶ N) : F.map (T.map a) =
        (E.app M).hom ≫ F.map a ≫ (E.app N).inv := by
      apply (cancel_mono (E.app N).hom).mp
      simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
      exact E.hom.naturality a
    change F.map (T.map (f + g) - (T.map f + T.map g)) = 0
    rw [F.map_sub, F.map_add, h (f+g), h f, h g, F.map_add,
      Preadditive.add_comp, Preadditive.comp_add, sub_self]

def moduleTwistFunctor (L : LineBundle X) : ℕ → X.Modules ⥤ X.Modules
  | 0 => 𝟭 _
  | n + 1 => moduleTwistFunctor L n ⋙ moduleTensorRightFunctor L.sheaf

instance moduleTwistFunctor_additive (L : LineBundle X) (n : ℕ) :
    (moduleTwistFunctor L n).Additive := by
  induction n with
  | zero => change (𝟭 X.Modules).Additive; infer_instance
  | succ n ih =>
    change (moduleTwistFunctor L n ⋙ moduleTensorRightFunctor L.sheaf).Additive
    infer_instance

theorem moduleTwistFunctor_add (L : LineBundle X) (m n : ℕ) :
    moduleTwistFunctor L (m+n) = moduleTwistFunctor L m ⋙ moduleTwistFunctor L n := by
  induction n with
  | zero =>
    change moduleTwistFunctor L m = moduleTwistFunctor L m ⋙ 𝟭 _
    rfl
  | succ n ih =>
    change moduleTwistFunctor L (m+n) ⋙ moduleTensorRightFunctor L.sheaf =
      moduleTwistFunctor L m ⋙ (moduleTwistFunctor L n ⋙ moduleTensorRightFunctor L.sheaf)
    rw [ih]
    rfl

theorem moduleTwistFunctor_shortExact (L : LineBundle X) (n : ℕ)
    (S : ShortComplex X.Modules) (hS : S.ShortExact) :
    (S.map (moduleTwistFunctor L n)).ShortExact := by
  induction n with
  | zero => exact hS
  | succ n ih =>
    change ((S.map (moduleTwistFunctor L n)).map
      (moduleTensorRightFunctor L.sheaf)).ShortExact
    exact moduleTensorRightFunctor_shortExact L (S.map (moduleTwistFunctor L n)) ih

def moduleTensorComm (M N : X.Modules) : moduleTensor X M N ≅ moduleTensor X N M := by
  let : MonoidalCategory (PresheafOfModules X.ringCatSheaf.obj) :=
    PresheafOfModulesOfCommRing.monoidalCategory (R := X.presheaf)
  let : SymmetricCategory (PresheafOfModules X.ringCatSheaf.obj) :=
    PresheafOfModulesOfCommRing.symmetricCategory (R := X.presheaf)
  exact (PresheafOfModules.sheafification (𝟙 X.ringCatSheaf.obj)).mapIso (β_ M.val N.val)

def moduleTwistUnitIso (L : LineBundle X) : ∀ n : ℕ,
    (moduleTwistFunctor L n).obj (structureSheaf X) ≅ modulePow X L.sheaf n
  | 0 => Iso.refl _
  | n+1 => moduleTensorIso (moduleTwistUnitIso L n) (Iso.refl L.sheaf) ≪≫
      moduleTensorComm (modulePow X L.sheaf n) L.sheaf

end PiExponentSeshadri.Geometry

end

end OAI
end Source0010

section Source0011
/-
Modification notice for the LogTwo project.
Derived from openai/math (Apache-2.0), revision adc7f1241b42e322a6451854ab7e4b4c146bf78a.
Original source: lean/OAI/NumberTheory/PiExponent/Approximation/TwistSections.lean
Changes: Convert module/import declarations to the Lean 4.34 public module format.
See ../../../../../THIRD_PARTY_NOTICES.txt for provenance and the recorded changes.
-/




namespace OAI

namespace PiExponentSeshadri.Geometry
noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
variable {X : Scheme}

def moduleSectionMultiplyRight (M : X.Modules) {L : X.Modules}
    (s : structureSheaf X ⟶ L) : M ⟶ moduleTensor X M L :=
  (moduleTensorRightUnit M).inv ≫ moduleTensorMap (𝟙 M) s

@[reassoc] theorem moduleSectionMultiplyRight_natural {M N L : X.Modules}
    (f : M ⟶ N) (s : structureSheaf X ⟶ L) :
    f ≫ moduleSectionMultiplyRight N s =
      moduleSectionMultiplyRight M s ≫ moduleTensorMap f (𝟙 L) := by
  have h : f ≫ (moduleTensorRightUnit N).inv =
      (moduleTensorRightUnit M).inv ≫ moduleTensorMap f (𝟙 (structureSheaf X)) := by
    apply (cancel_mono (moduleTensorRightUnit N).hom).mp
    simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
    rw [moduleTensorRightUnit_natural]
    simp
  unfold moduleSectionMultiplyRight
  rw [← Category.assoc, h, Category.assoc, ← moduleTensorMap_comp,
    Category.comp_id, Category.id_comp]
  rw [Category.assoc, ← moduleTensorMap_comp]
  simp

def moduleSectionMultiplyRightNat {L : X.Modules} (s : structureSheaf X ⟶ L) :
    𝟭 X.Modules ⟶ moduleTensorRightFunctor L where
  app M := moduleSectionMultiplyRight M s
  naturality _ _ f := moduleSectionMultiplyRight_natural f s

def moduleTwistStep (L : LineBundle X) (s : structureSheaf X ⟶ L.sheaf) (n : ℕ) :
    moduleTwistFunctor L n ⟶ moduleTwistFunctor L (n+1) where
  app M := moduleSectionMultiplyRight ((moduleTwistFunctor L n).obj M) s
  naturality _ _ f := moduleSectionMultiplyRight_natural ((moduleTwistFunctor L n).map f) s

def moduleTwistSection (L : LineBundle X) (s : structureSheaf X ⟶ L.sheaf) :
    ∀ n : ℕ, 𝟭 X.Modules ⟶ moduleTwistFunctor L n
  | 0 => 𝟙 _
  | n+1 => moduleTwistSection L s n ≫ moduleTwistStep L s n

def moduleTwistForward (L : LineBundle X) (s : structureSheaf X ⟶ L.sheaf) (n : ℕ) :
    ∀ k : ℕ, moduleTwistFunctor L n ⟶ moduleTwistFunctor L (n+k)
  | 0 => 𝟙 _
  | k+1 => moduleTwistForward L s n k ≫ moduleTwistStep L s (n+k)

@[simp] theorem moduleTwistSection_add (L : LineBundle X)
    (s : structureSheaf X ⟶ L.sheaf) (n k : ℕ) :
    moduleTwistSection L s (n+k) = moduleTwistSection L s n ≫ moduleTwistForward L s n k := by
  induction k with
  | zero => exact (Category.comp_id _).symm
  | succ k ih =>
    change moduleTwistSection L s (n+k) ≫ moduleTwistStep L s (n+k) =
      moduleTwistSection L s n ≫
        (moduleTwistForward L s n k ≫ moduleTwistStep L s (n+k))
    rw [ih, Category.assoc]

def moduleTwistRestrictFrame (L : LineBundle X) (U : X.Opens)
    (e : L.sheaf.restrict U.ι ≅ structureSheaf U.toScheme) :
    ∀ n : ℕ, moduleTwistFunctor L n ⋙ Scheme.Modules.restrictFunctor U.ι ≅
      Scheme.Modules.restrictFunctor U.ι
  | 0 => Iso.refl _
  | n+1 => Functor.isoWhiskerLeft (moduleTwistFunctor L n)
      (moduleTensorRestrictFrame U L.sheaf e) ≪≫ moduleTwistRestrictFrame L U e n

@[simp] theorem moduleTwistRestrictFrame_zero (L : LineBundle X) (U : X.Opens)
    (e : L.sheaf.restrict U.ι ≅ structureSheaf U.toScheme) (M : X.Modules) :
    ((moduleTwistRestrictFrame L U e 0).app M).hom = 𝟙 (M.restrict U.ι) := rfl

@[simp] theorem moduleTwistRestrictFrame_succ (L : LineBundle X) (U : X.Opens)
    (e : L.sheaf.restrict U.ι ≅ structureSheaf U.toScheme) (M : X.Modules) (n : ℕ) :
    ((moduleTwistRestrictFrame L U e (n+1)).app M).hom =
      ((moduleTensorRestrictFrame U L.sheaf e).app ((moduleTwistFunctor L n).obj M)).hom ≫
        ((moduleTwistRestrictFrame L U e n).app M).hom := rfl

end
end PiExponentSeshadri.Geometry

end OAI
end Source0011

section Source0012
/-
Modification notice for the LogTwo project.
Derived from openai/math (Apache-2.0), revision adc7f1241b42e322a6451854ab7e4b4c146bf78a.
Original source: lean/OAI/NumberTheory/PiExponent/LocalAlgebra/FiniteGlobalPresentation.lean
Changes: Convert module/import declarations to the Lean 4.34 public module format.
Expose private helpers and adjust helper names where needed for module compatibility.
See ../../../../../THIRD_PARTY_NOTICES.txt for provenance and the recorded changes.
-/




namespace OAI

namespace PiExponent.FiniteGlobalPresentation
noncomputable section
universe u v₁ v₂ u₁ u₂
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite
open PiExponent.CoherentAffineFinite

section PresentationMap
variable {C : Type u₁} [Category.{v₁} C] {J : GrothendieckTopology C}
  {R : Sheaf J RingCat.{u}} [HasSheafify J AddCommGrpCat.{u}]
  [J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  {C' : Type u₂} [Category.{v₂} C'] {J' : GrothendieckTopology C'}
  {S : Sheaf J' RingCat.{u}} [HasSheafify J' AddCommGrpCat.{u}]
  [J'.WEqualsLocallyBijective AddCommGrpCat.{u}]
  {M : SheafOfModules.{u} R}

instance presentation_map_isFinite (P : M.Presentation) [P.IsFinite]
    (F : SheafOfModules.{u} R ⥤ SheafOfModules.{u} S)
    [PreservesColimitsOfSize.{u,u} F]
    (η : SheafOfModules.unit S ≅ F.obj (SheafOfModules.unit R)) :
    (P.map F η).IsFinite where
  isFiniteType_generators := ⟨by
    rw [SheafOfModules.Presentation.map_generators_I]
    infer_instance⟩
  isFiniteType_relations := ⟨by
    rw [SheafOfModules.Presentation.map_relations_I]
    infer_instance⟩
def presentationOfIso {N : SheafOfModules.{u} R} (e : M ≅ N)
    (P : M.Presentation) : N.Presentation := by
  let : IsIso e.hom := e.isIso_hom
  exact P.ofIsIso e.hom

end PresentationMap

theorem isFinitePresentation_of_presentation {X : Scheme.{u}} {M : X.Modules}
    (P : M.Presentation) [hP : P.IsFinite] : M.IsFinitePresentation := by
  let q := P.quasicoherentData
  have : q.IsFinitePresentation := by
    constructor
    intro U
    exact ⟨⟨hP.isFiniteType_generators.finite⟩, ⟨hP.isFiniteType_relations.finite⟩⟩
  exact { exists_quasicoherentData := ⟨q, inferInstance⟩ }

theorem tilde_exists_finitePresentation {R : CommRingCat.{u}} [IsNoetherianRing R]
    (N : ModuleCat R) [Module.Finite R N] :
    ∃ P : (tilde N).Presentation, P.IsFinite := by
  classical
  obtain ⟨s,hs⟩ := Module.Finite.fg_top (R := R) (M := N)
  let K := LinearMap.ker (Finsupp.linearCombination (M := N) R ((↑) : s → N))
  obtain ⟨t,ht⟩ := IsNoetherian.noetherian K
  let P := presentationTilde N (s : Set N) hs (t : Set (s →₀ R)) ht
  have : P.IsFinite := by
    constructor
    · constructor
      change Finite s
      infer_instance
    · constructor
      change Finite t
      infer_instance
  exact ⟨P,inferInstance⟩

theorem tilde_finitePresentation {R : CommRingCat.{u}} [IsNoetherianRing R]
    (N : ModuleCat R) [Module.Finite R N] : (tilde N).IsFinitePresentation := by
  obtain ⟨P,hP⟩ := tilde_exists_finitePresentation N
  exact isFinitePresentation_of_presentation P

theorem spec_kernel_isQuasicoherent {R : CommRingCat.{u}} {M N : (Spec R).Modules}
    [M.IsQuasicoherent] [N.IsQuasicoherent] (f : M ⟶ N) :
    (kernel f).IsQuasicoherent := by
  let hm := Scheme.Modules.isIso_fromTildeΓ_of_isQuasicoherent M
  let hn := Scheme.Modules.isIso_fromTildeΓ_of_isQuasicoherent N
  let em := @asIso _ _ _ _ M.fromTildeΓ hm
  let en := @asIso _ _ _ _ N.fromTildeΓ hn
  let g := (tilde.functor R).preimage
    (em.hom ≫ f ≫ en.inv)
  let e : (tilde.functor R).obj (kernel g) ≅ kernel f :=
    PreservesKernel.iso (tilde.functor R) g ≪≫
      kernel.mapIso ((tilde.functor R).map g) f em
        en (by
          change (tilde.functor R).map ((tilde.functor R).preimage _) ≫ _ = _
          erw [Functor.map_preimage]
          exact (Category.assoc em.hom (f ≫ en.inv) en.hom).trans
            (congrArg (fun q => em.hom ≫ q)
              ((Category.assoc f en.inv en.hom).trans
                ((congrArg (fun q => f ≫ q) en.inv_hom_id).trans (Category.comp_id f)))))
  exact (SheafOfModules.isQuasicoherent (Spec R).ringCatSheaf).prop_of_iso e
    (inferInstanceAs (tilde (kernel g)).IsQuasicoherent)

theorem spec_exists_finitePresentation_of_sections {R : CommRingCat.{u}} [IsNoetherianRing R]
    (M : (Spec R).Modules) [M.IsQuasicoherent]
    [Module.Finite R ((modulesSpecToSheaf.obj M).obj.obj (op ⊤))] :
    ∃ P : M.Presentation, P.IsFinite := by
  let : IsIso M.fromTildeΓ := Scheme.Modules.isIso_fromTildeΓ_of_isQuasicoherent M
  obtain ⟨P,hP⟩ := tilde_exists_finitePresentation
    ((modulesSpecToSheaf.obj M).obj.obj (op ⊤))
  let h := Scheme.Modules.isIso_fromTildeΓ_of_isQuasicoherent M
  exact ⟨presentationOfIso (@asIso _ _ _ _ M.fromTildeΓ h) P,
    ⟨⟨hP.isFiniteType_generators.finite⟩, ⟨hP.isFiniteType_relations.finite⟩⟩⟩

theorem spec_kernel_exists_finitePresentation {R : CommRingCat.{u}} [IsNoetherianRing R]
    {M N : (Spec R).Modules} [M.IsQuasicoherent] [N.IsQuasicoherent]
    [Module.Finite R ((modulesSpecToSheaf.obj M).obj.obj (op ⊤))] (f : M ⟶ N) :
    ∃ P : (kernel f).Presentation, P.IsFinite := by
  have := spec_kernel_isQuasicoherent f
  have : (moduleSpecΓFunctor (R := R)).IsRightAdjoint := tilde.adjunction.isRightAdjoint
  have : Module.Finite R (moduleSpecΓFunctor.obj M) :=
    inferInstanceAs (Module.Finite R ((modulesSpecToSheaf.obj M).obj.obj (op ⊤)))
  let g := moduleSpecΓFunctor.map (kernel.ι f)
  have : Mono g := inferInstanceAs (Mono (moduleSpecΓFunctor.map (kernel.ι f)))
  have : Module.Finite R ((modulesSpecToSheaf.obj (kernel f)).obj.obj (op ⊤)) :=
    Module.Finite.of_injective g.hom ((ModuleCat.mono_iff_injective g).mp inferInstance)
  exact spec_exists_finitePresentation_of_sections (kernel f)

def presentationOver_of_restrict {X : Scheme.{u}} (M : X.Modules) (U : X.Opens)
    (P : (M.restrict U.ι).Presentation) : (M.over U).Presentation := by
  let E := Scheme.Modules.overEquiv U
  let F : SheafOfModules U.toScheme.ringCatSheaf ⥤
      SheafOfModules (Sheaf.over X.ringCatSheaf U) := E.inverse
  let : PreservesColimitsOfSize.{u,u} F :=
    E.symm.toAdjunction.leftAdjoint_preservesColimits
  let e : E.inverse.obj (M.restrict U.ι) ≅ M.over U :=
    E.inverse.mapIso ((Scheme.Modules.overFunctorEquiv U).app M).symm ≪≫
      (E.unitIso.app (M.over U)).symm
  let : IsIso e.hom := e.isIso_hom
  exact presentationOfIso e (P.map F (E.unitIso.app _))

instance presentationOver_of_restrict_isFinite {X : Scheme.{u}} (M : X.Modules)
    (U : X.Opens) (P : (M.restrict U.ι).Presentation) [hP : P.IsFinite] :
    (presentationOver_of_restrict M U P).IsFinite := by
  exact ⟨⟨hP.isFiniteType_generators.finite⟩, ⟨hP.isFiniteType_relations.finite⟩⟩

theorem isFinitePresentation_of_affine_presentations {X : Scheme.{u}} (M : X.Modules)
    (h : ∀ U : X.affineOpens, ∃ P : (M.restrict U.1.ι).Presentation, P.IsFinite) :
    M.IsFinitePresentation := by
  classical
  let pres (U : X.affineOpens) := (h U).choose
  have hpres (U : X.affineOpens) : (pres U).IsFinite := (h U).choose_spec
  let q : M.QuasicoherentData := {
    I := X.affineOpens
    X U := U.1
    coversTop := by
      rw [Opens.coversTop_iff]
      apply top_unique
      intro x hx
      obtain ⟨U,hU,hxU,hUt⟩ := exists_isAffineOpen_mem_and_subset
        (show x ∈ (⊤ : X.Opens) from trivial)
      exact Opens.mem_iSup.mpr ⟨⟨U,hU⟩,hxU⟩
    presentation U := presentationOver_of_restrict M U.1 (pres U) }
  have : q.IsFinitePresentation := by
    constructor
    intro U
    change (presentationOver_of_restrict M U.1 (pres U)).IsFinite
    infer_instance
  exact { exists_quasicoherentData := ⟨q, inferInstance⟩ }

theorem affine_kernel_exists_finitePresentation {X : Scheme.{u}}
    [IsAffine X] [IsLocallyNoetherian X] {M N : X.Modules}
    [M.IsQuasicoherent] [N.IsQuasicoherent] (f : M ⟶ N)
    (hM : LocallyFinitelyGenerated M) :
    ∃ P : (kernel f).Presentation, P.IsFinite := by
  let a := X.isoSpec.inv
  let F := Scheme.Modules.restrictFunctor a
  have : IsNoetherianRing Γ(X,⊤) :=
    IsLocallyNoetherian.component_noetherian ⟨⊤, isAffineOpen_top X⟩
  have : Module.Finite Γ(X,⊤) ((modulesSpecToSheaf.obj (M.restrict a)).obj.obj (op ⊤)) :=
    spec_sections_finite_of_localGenerators (M.restrict a) (hM.restrict a)
  obtain ⟨P,hP⟩ := spec_kernel_exists_finitePresentation (F.map f)
  let e := PreservesKernel.iso F f
  let : IsIso e.inv := e.isIso_inv
  let P' := presentationOfIso e.symm P
  let b := X.isoSpec.hom
  let G : SheafOfModules (Spec Γ(X,⊤)).ringCatSheaf ⥤ SheafOfModules X.ringCatSheaf :=
    Scheme.Modules.restrictFunctor b
  let : PreservesColimitsOfSize.{u,u} G :=
    (Scheme.Modules.restrictAdjunction b).leftAdjoint_preservesColimits
  let Q := P'.map G (Scheme.Modules.restrictUnitIso b).symm
  let e₁ := (Scheme.Modules.restrictFunctorComp b a).app (kernel f)
  have e₂ : (kernel f).restrict (𝟙 X) ≅ ((kernel f).restrict a).restrict b := by
    change (kernel f).restrict (b ≫ a) ≅ ((kernel f).restrict a).restrict b at e₁
    simpa only [b, a, Iso.hom_inv_id] using e₁
  let e₃ := e₂.symm ≪≫ Scheme.Modules.restrictFunctorId.app (kernel f)
  let : IsIso e₃.hom := e₃.isIso_hom
  exact ⟨presentationOfIso e₃ Q,
    ⟨⟨hP.isFiniteType_generators.finite⟩, ⟨hP.isFiniteType_relations.finite⟩⟩⟩

theorem free_isFinitePresentation (X : Scheme.{u}) (I : Type u) [Finite I] :
    (SheafOfModules.free (R := X.ringCatSheaf) I).IsFinitePresentation := by
  let f : SheafOfModules.free (R := X.ringCatSheaf) (ULift.{u} Empty) ⟶
      SheafOfModules.free I := 0
  let P := SheafOfModules.presentationOfIsCokernelFree f (𝟙 _) (by simp [f])
    (CokernelCofork.IsColimit.ofId f rfl)
  have : P.IsFinite := by
    constructor
    · constructor
      change Finite I
      infer_instance
    · constructor
      change Finite (ULift.{u} Empty)
      infer_instance
  exact isFinitePresentation_of_presentation P

theorem kernel_isFinitePresentation {X : Scheme.{u}} [IsLocallyNoetherian X]
    {M N : X.Modules} [M.IsFinitePresentation] [N.IsQuasicoherent] (f : M ⟶ N) :
    (kernel f).IsFinitePresentation := by
  apply isFinitePresentation_of_affine_presentations
  intro U
  have : IsAffine U.1.toScheme := U.2
  let F := Scheme.Modules.restrictFunctor U.1.ι
  let : M.IsQuasicoherent :=
    (SheafOfModules.IsFinitePresentation.exists_quasicoherentData M).choose.isQuasicoherent
  obtain ⟨P,hP⟩ := affine_kernel_exists_finitePresentation (F.map f)
    ((locallyFinitelyGenerated_of_finitePresentation M).restrict U.1.ι)
  let e := PreservesKernel.iso F f
  let : IsIso e.inv := e.isIso_inv
  exact ⟨presentationOfIso e.symm P,
    ⟨⟨hP.isFiniteType_generators.finite⟩, ⟨hP.isFiniteType_relations.finite⟩⟩⟩

theorem kernel_generators_isFinitePresentation {X : Scheme.{u}} [IsLocallyNoetherian X]
    (M : X.Modules) [M.IsQuasicoherent] (s : M.GeneratingSections) [hs : s.IsFiniteType] :
    (kernel s.π).IsFinitePresentation := by
  let : Finite s.I := hs.finite
  have := free_isFinitePresentation X s.I
  exact kernel_isFinitePresentation s.π

theorem exists_local_finitePresentation {X : Scheme.{u}} (M : X.Modules)
    [M.IsFinitePresentation] (x : X) :
    ∃ U : X.Opens, x ∈ U ∧ ∃ P : (M.restrict U.ι).Presentation, P.IsFinite := by
  obtain ⟨q,hq⟩ := SheafOfModules.IsFinitePresentation.exists_quasicoherentData M
  have hcov := q.coversTop
  rw [Opens.coversTop_iff] at hcov
  obtain ⟨i,hi⟩ := Opens.mem_iSup.mp (show x ∈ ⨆ i, q.X i by rw [hcov]; trivial)
  let F : SheafOfModules (Sheaf.over X.ringCatSheaf (q.X i)) ⥤
      SheafOfModules (Scheme.Opens.toScheme (X := X) (q.X i)).ringCatSheaf :=
    (Scheme.Modules.overEquiv (q.X i)).functor
  let : PreservesColimitsOfSize.{u,u} F :=
    (Scheme.Modules.overEquiv (q.X i)).toAdjunction.leftAdjoint_preservesColimits
  let : (q.presentation i).IsFinite := hq.isFinite_presentation i
  let P := (q.presentation i).map F (Iso.refl _)
  let e := (Scheme.Modules.overFunctorEquiv (q.X i)).app M
  let : IsIso e.hom := e.isIso_hom
  exact ⟨q.X i, hi, presentationOfIso e P,
    ⟨⟨(hq.isFinite_presentation i).isFiniteType_generators.finite⟩,
      ⟨(hq.isFinite_presentation i).isFiniteType_relations.finite⟩⟩⟩

theorem isFinitePresentation_of_localPresentations {X : Scheme.{u}} (M : X.Modules)
    (h : ∀ x : X, ∃ U : X.Opens, x ∈ U ∧
      ∃ P : (M.restrict U.ι).Presentation, P.IsFinite) : M.IsFinitePresentation := by
  classical
  choose U hx P hP using h
  have hP' (x : X) : (P x).IsFinite := hP x
  let q : M.QuasicoherentData := {
    I := X
    X := U
    coversTop := by
      rw [Opens.coversTop_iff]
      apply top_unique
      intro x hxtop
      exact Opens.mem_iSup.mpr ⟨x,hx x⟩
    presentation x := presentationOver_of_restrict M (U x) (P x) }
  have : q.IsFinitePresentation := by
    constructor
    intro x
    change (presentationOver_of_restrict M (U x) (P x)).IsFinite
    infer_instance
  exact { exists_quasicoherentData := ⟨q, inferInstance⟩ }

theorem finitePresentation_of_le {X : Scheme.{u}} (M : X.Modules) {U V : X.Opens}
    (h : V ≤ U) (P : (M.restrict U.ι).Presentation) [hP : P.IsFinite] :
    ∃ Q : (M.restrict V.ι).Presentation, Q.IsFinite := by
  let F : SheafOfModules U.toScheme.ringCatSheaf ⥤ SheafOfModules V.toScheme.ringCatSheaf :=
    Scheme.Modules.restrictFunctor (X.homOfLE h)
  let : PreservesColimitsOfSize.{u,u} F :=
    (Scheme.Modules.restrictAdjunction (X.homOfLE h)).leftAdjoint_preservesColimits
  let Q := P.map F
    (Scheme.Modules.restrictUnitIso (X.homOfLE h)).symm
  let e := (Scheme.Modules.restrictFunctorComp (X.homOfLE h) U.ι).app M
  simp only [X.homOfLE_ι h] at e
  let : IsIso e.inv := e.isIso_inv
  exact ⟨presentationOfIso e.symm Q,
    ⟨⟨hP.isFiniteType_generators.finite⟩, ⟨hP.isFiniteType_relations.finite⟩⟩⟩

def restrictIsoOfLE {X : Scheme.{u}} {M N : X.Modules} {U V : X.Opens}
    (h : V ≤ U) (e : M.restrict U.ι ≅ N.restrict U.ι) :
    M.restrict V.ι ≅ N.restrict V.ι := by
  let e' := (Scheme.Modules.restrictFunctorComp (X.homOfLE h) U.ι).app M ≪≫
    (Scheme.Modules.restrictFunctor (X.homOfLE h)).mapIso e ≪≫
    ((Scheme.Modules.restrictFunctorComp (X.homOfLE h) U.ι).app N).symm
  simp only [X.homOfLE_ι h] at e'
  exact e'

theorem isFinitePresentation_of_locally_iso {X : Scheme.{u}} (M N : X.Modules)
    [M.IsFinitePresentation]
    (h : ∀ x : X, ∃ V : X.Opens, x ∈ V ∧ Nonempty (N.restrict V.ι ≅ M.restrict V.ι)) :
    N.IsFinitePresentation := by
  apply isFinitePresentation_of_localPresentations
  intro x
  obtain ⟨V,hxV,⟨e⟩⟩ := h x
  obtain ⟨U,hxU,P,hP⟩ := exists_local_finitePresentation M x
  obtain ⟨Q,hQ⟩ := finitePresentation_of_le M (V := U ⊓ V) inf_le_left P
  let e' := restrictIsoOfLE (V := U ⊓ V) inf_le_right e
  let : IsIso e'.inv := e'.isIso_inv
  exact ⟨U ⊓ V, ⟨hxU,hxV⟩, presentationOfIso e'.symm Q,
    ⟨⟨hQ.isFiniteType_generators.finite⟩, ⟨hQ.isFiniteType_relations.finite⟩⟩⟩

theorem moduleTwist_isFinitePresentation {X : Scheme.{0}}
    (L : PiExponentSeshadri.Geometry.LineBundle X) (n : ℕ) (M : X.Modules)
    [M.IsFinitePresentation] :
    ((PiExponentSeshadri.Geometry.moduleTwistFunctor L n).obj M).IsFinitePresentation := by
  apply isFinitePresentation_of_locally_iso M
  intro x
  obtain ⟨U,hxU,⟨e⟩⟩ := L.locallyRankOne x
  exact ⟨U,hxU,⟨(PiExponentSeshadri.Geometry.moduleTwistRestrictFrame L U e n).app M⟩⟩

end
end PiExponent.FiniteGlobalPresentation

end OAI
end Source0012

section Source0013
/-
Modification notice for the LogTwo project.
Derived from openai/math (Apache-2.0), revision adc7f1241b42e322a6451854ab7e4b4c146bf78a.
Original source: lean/OAI/NumberTheory/PiExponent/Approximation/OpenBaseChange.lean
Changes: Convert module/import declarations to the Lean 4.34 public module format.
See ../../../../../THIRD_PARTY_NOTICES.txt for provenance and the recorded changes.
-/




namespace OAI

namespace PiExponentSeshadri.OpenBaseChange
noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite
variable {X Y : Scheme.{0}} (f : X ⟶ Y) (U : Y.Opens)

lemma restrict_unit_app {Z T : Scheme.{0}} (i : Z ⟶ T) [IsOpenImmersion i]
    (M : T.Modules) (W : T.Opens) :
    ((Scheme.Modules.restrictAdjunction i).unit.app M).app W =
      M.presheaf.map (homOfLE (i.image_preimage_le W)).op := rfl

lemma restrict_unit_app_iso {Z T : Scheme.{0}} (i : Z ⟶ T) [IsOpenImmersion i]
    (M : T.Modules) (W : T.Opens) (hW : W ≤ i.opensRange) :
    IsIso (((Scheme.Modules.restrictAdjunction i).unit.app M).app W) := by
  rw [restrict_unit_app]
  have he : i ''ᵁ i ⁻¹ᵁ W = W := by
    rw [i.image_preimage_eq_opensRange_inf, inf_eq_right.mpr hW]
  have hi : IsIso (homOfLE (i.image_preimage_le W)) :=
    homOfLE_isIso_of_eq _ he
  let e := @asIso _ _ _ _ (homOfLE (i.image_preimage_le W)) hi
  exact (M.presheaf.mapIso e.op).isIso_hom

def rightSquare :
    Scheme.Modules.pushforward (f ⁻¹ᵁ U).ι ⋙ Scheme.Modules.pushforward f ≅
      Scheme.Modules.pushforward (f ∣_ U) ⋙ Scheme.Modules.pushforward U.ι :=
  Scheme.Modules.pushforwardComp _ _ ≪≫
    Scheme.Modules.pushforwardCongr (morphismRestrict_ι f U).symm ≪≫
      (Scheme.Modules.pushforwardComp _ _).symm

def hom (M : X.Modules) :
    ((Scheme.Modules.pushforward f).obj M).restrict U.ι ⟶
      (Scheme.Modules.pushforward (f ∣_ U)).obj (M.restrict (f ⁻¹ᵁ U).ι) :=
  (Scheme.Modules.restrictFunctor U.ι).map
    ((Scheme.Modules.pushforward f).map
      ((Scheme.Modules.restrictAdjunction (f ⁻¹ᵁ U).ι).unit.app M)) ≫
  (Scheme.Modules.restrictFunctor U.ι).map
    ((rightSquare f U).hom.app (M.restrict (f ⁻¹ᵁ U).ι)) ≫
  (Scheme.Modules.restrictAdjunction U.ι).counit.app
    ((Scheme.Modules.pushforward (f ∣_ U)).obj (M.restrict (f ⁻¹ᵁ U).ι))

instance hom_isIso (M : X.Modules) : IsIso (hom f U M) := by
  have ha : IsIso ((Scheme.Modules.restrictFunctor U.ι).map
    ((Scheme.Modules.pushforward f).map
      ((Scheme.Modules.restrictAdjunction (f ⁻¹ᵁ U).ι).unit.app M))) := by
    apply Scheme.Modules.Hom.isIso_iff_isIso_app.mpr
    intro W
    change IsIso (((Scheme.Modules.restrictAdjunction (f ⁻¹ᵁ U).ι).unit.app M).app
      (f ⁻¹ᵁ (U.ι ''ᵁ W)))
    apply restrict_unit_app_iso
    rw [Scheme.Opens.opensRange_ι]
    apply (Opens.map f.base).monotone
    simpa only [Scheme.Opens.opensRange_ι] using U.ι.image_le_opensRange W
  unfold hom
  infer_instance

def iso (M : X.Modules) :
    ((Scheme.Modules.pushforward f).obj M).restrict U.ι ≅
      (Scheme.Modules.pushforward (f ∣_ U)).obj (M.restrict (f ⁻¹ᵁ U).ι) := asIso (hom f U M)

end
end PiExponentSeshadri.OpenBaseChange

end OAI
end Source0013

section Source0014
/-
Modification notice for the LogTwo project.
Derived from openai/math (Apache-2.0), revision adc7f1241b42e322a6451854ab7e4b4c146bf78a.
Original source: lean/OAI/NumberTheory/PiExponent/Geometry/LineBundleCoherent.lean
Changes: Convert module/import declarations to the Lean 4.34 public module format.
See ../../../../../THIRD_PARTY_NOTICES.txt for provenance and the recorded changes.
-/




namespace OAI

namespace PiExponent.GeometrySupport.LineBundleCoherent

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open PiExponentSeshadri.Geometry

variable {X : Scheme}

theorem structureSheaf_isFinitePresentation : (structureSheaf X).IsFinitePresentation := by
  let e : SheafOfModules.free (R := X.ringCatSheaf) PUnit ≅ structureSheaf X :=
    coproductUniqueIso (fun _ : PUnit => structureSheaf X)
  exact (SheafOfModules.isFinitePresentation X.ringCatSheaf).prop_of_iso e
    (PiExponent.FiniteGlobalPresentation.free_isFinitePresentation X PUnit)

theorem lineBundle_isFinitePresentation (L : LineBundle X) : L.sheaf.IsFinitePresentation := by
  let : (structureSheaf X).IsFinitePresentation := structureSheaf_isFinitePresentation
  apply PiExponent.FiniteGlobalPresentation.isFinitePresentation_of_locally_iso
    (structureSheaf X) L.sheaf
  intro x
  obtain ⟨U, hx, ⟨e⟩⟩ := L.locallyRankOne x
  exact ⟨U, hx, ⟨e ≪≫ (Scheme.Modules.restrictUnitIso U.ι).symm⟩⟩

theorem modulePow_isFinitePresentation (L : LineBundle X) (n : ℕ) :
    (modulePow X L.sheaf n).IsFinitePresentation :=
  lineBundle_isFinitePresentation (L.pow n)

theorem modulePow_isQuasicoherent (L : LineBundle X) (n : ℕ) :
    (modulePow X L.sheaf n).IsQuasicoherent := by
  have := modulePow_isFinitePresentation L n
  exact (SheafOfModules.IsFinitePresentation.exists_quasicoherentData
    (modulePow X L.sheaf n)).choose.isQuasicoherent

end
end PiExponent.GeometrySupport.LineBundleCoherent

end OAI
end Source0014

section Source0015
/-
Modification notice for the LogTwo project.
Derived from openai/math (Apache-2.0), revision adc7f1241b42e322a6451854ab7e4b4c146bf78a.
Original source: lean/OAI/NumberTheory/PiExponent/Approximation/SectionOpens.lean
Changes: Convert module/import declarations to the Lean 4.34 public module format.
See ../../../../../THIRD_PARTY_NOTICES.txt for provenance and the recorded changes.
-/




namespace OAI

noncomputable section

namespace PiExponentSeshadri

universe u

namespace SectionOpens

section
open AlgebraicGeometry CategoryTheory TopologicalSpace
open scoped AlgebraicGeometry
variable {X Y : Scheme.{u}} {M N : X.Modules}

lemma isIso_of_stalks (f : M ⟶ N)
    (h : ∀ x : X, IsIso ((TopCat.Presheaf.stalkFunctor Ab x).map f.mapPresheaf)) :
    IsIso f := by
  apply Scheme.Modules.Hom.isIso_iff_isIso_app.mpr
  intro U
  let A : TopCat.Sheaf Ab X := ⟨M.presheaf, M.isSheaf⟩
  let B : TopCat.Sheaf Ab X := ⟨N.presheaf, N.isSheaf⟩
  let φ : A ⟶ B := ⟨f.mapPresheaf⟩
  let (x : U) : IsIso ((TopCat.Presheaf.stalkFunctor Ab x.val).map φ.hom) := h x.val
  exact TopCat.Presheaf.app_isIso_of_stalkFunctor_map_iso φ U

lemma stalk_isIso_of_restrict (f : M ⟶ N) (φ : Y ⟶ X) [IsOpenImmersion φ]
    [IsIso ((Scheme.Modules.restrictFunctor φ).map f)] (y : Y) :
    IsIso ((TopCat.Presheaf.stalkFunctor Ab (φ y)).map f.mapPresheaf) := by
  apply (NatIso.isIso_map_iff (Scheme.Modules.restrictStalkNatIso φ y) f).mp
  change IsIso ((TopCat.Presheaf.stalkFunctor Ab y).map
    ((Scheme.Modules.toPresheaf Y).map ((Scheme.Modules.restrictFunctor φ).map f)))
  infer_instance

lemma restrict_isIso_of_stalks (f : M ⟶ N) (φ : Y ⟶ X) [IsOpenImmersion φ]
    (h : ∀ y : Y, IsIso ((TopCat.Presheaf.stalkFunctor Ab (φ y)).map f.mapPresheaf)) :
    IsIso ((Scheme.Modules.restrictFunctor φ).map f) := by
  apply isIso_of_stalks
  intro y
  exact (NatIso.isIso_map_iff (Scheme.Modules.restrictStalkNatIso φ y) f).mpr (h y)

lemma isIso_of_locally_isIso (f : M ⟶ N)
    (h : ∀ x : X, ∃ U : X.Opens, x ∈ U ∧
      IsIso ((Scheme.Modules.restrictFunctor U.ι).map f)) : IsIso f := by
  apply isIso_of_stalks
  intro x
  obtain ⟨U, hx, hU⟩ := h x
  let := hU
  exact stalk_isIso_of_restrict f U.ι ⟨x, hx⟩

def isoOpen (f : M ⟶ N) : X.Opens :=
  ⨆ (U : X.Opens) (_ : IsIso ((Scheme.Modules.restrictFunctor U.ι).map f)), U

lemma mem_isoOpen_iff (f : M ⟶ N) (x : X) :
    x ∈ isoOpen f ↔ ∃ U : X.Opens, x ∈ U ∧
      IsIso ((Scheme.Modules.restrictFunctor U.ι).map f) := by
  simp only [isoOpen, Opens.mem_iSup]
  aesop

theorem isIso_restrict_isoOpen (f : M ⟶ N) :
    IsIso ((Scheme.Modules.restrictFunctor (isoOpen f).ι).map f) := by
  apply restrict_isIso_of_stalks
  intro x
  obtain ⟨U, hx, hU⟩ := (mem_isoOpen_iff f x.val).mp x.property
  let := hU
  exact stalk_isIso_of_restrict f U.ι ⟨x.val, hx⟩

end

open AlgebraicGeometry CategoryTheory TopologicalSpace
open scoped AlgebraicGeometry
variable {X Y : Scheme.{u}} {M N P : X.Modules}

lemma isoOpen_postcomp (f : M ⟶ N) (e : N ≅ P) :
    isoOpen (f ≫ e.hom) = isoOpen f := by
  apply le_antisymm
  · intro x hx
    obtain ⟨U, hxU, hU⟩ := (mem_isoOpen_iff (f ≫ e.hom) x).mp hx
    refine (mem_isoOpen_iff f x).mpr ⟨U, hxU, ?_⟩
    rw [Functor.map_comp] at hU
    let := hU
    exact IsIso.of_isIso_comp_right
      ((Scheme.Modules.restrictFunctor U.ι).map f) ((Scheme.Modules.restrictFunctor U.ι).map e.hom)
  · intro x hx
    obtain ⟨U, hxU, hU⟩ := (mem_isoOpen_iff f x).mp hx
    refine (mem_isoOpen_iff (f ≫ e.hom) x).mpr ⟨U, hxU, ?_⟩
    rw [Functor.map_comp]
    let := hU
    infer_instance

lemma isoOpen_precomp (e : P ≅ M) (f : M ⟶ N) :
    isoOpen (e.hom ≫ f) = isoOpen f := by
  apply le_antisymm
  · intro x hx
    obtain ⟨U, hxU, hU⟩ := (mem_isoOpen_iff (e.hom ≫ f) x).mp hx
    refine (mem_isoOpen_iff f x).mpr ⟨U, hxU, ?_⟩
    rw [Functor.map_comp] at hU
    let := hU
    exact IsIso.of_isIso_comp_left
      ((Scheme.Modules.restrictFunctor U.ι).map e.hom) ((Scheme.Modules.restrictFunctor U.ι).map f)
  · intro x hx
    obtain ⟨U, hxU, hU⟩ := (mem_isoOpen_iff f x).mp hx
    refine (mem_isoOpen_iff (e.hom ≫ f) x).mpr ⟨U, hxU, ?_⟩
    rw [Functor.map_comp]
    let := hU
    infer_instance

lemma isoOpen_restrict (f : M ⟶ N) (φ : Y ⟶ X) [IsOpenImmersion φ] :
    isoOpen ((Scheme.Modules.restrictFunctor φ).map f) = φ ⁻¹ᵁ isoOpen f := by
  ext y
  constructor
  · intro hy
    obtain ⟨V, hyV, hV⟩ := (mem_isoOpen_iff _ y).mp hy
    let := hV
    apply (mem_isoOpen_iff f (φ y)).mpr
    refine ⟨φ ''ᵁ V, ⟨y, hyV, rfl⟩, ?_⟩
    apply restrict_isIso_of_stalks
    intro x
    obtain ⟨z, hz, he⟩ := x.property
    change φ z = x.val at he
    change IsIso ((TopCat.Presheaf.stalkFunctor Ab x.val).map f.mapPresheaf)
    rw [← he]
    apply (NatIso.isIso_map_iff (Scheme.Modules.restrictStalkNatIso φ z) f).mp
    exact stalk_isIso_of_restrict ((Scheme.Modules.restrictFunctor φ).map f) V.ι ⟨z, hz⟩
  · intro hy
    change φ y ∈ isoOpen f at hy
    let U := φ ⁻¹ᵁ isoOpen f
    apply (mem_isoOpen_iff _ y).mpr
    refine ⟨U, hy, ?_⟩
    apply restrict_isIso_of_stalks
    intro z
    apply (NatIso.isIso_map_iff (Scheme.Modules.restrictStalkNatIso φ z.val) f).mpr
    let := isIso_restrict_isoOpen f
    exact stalk_isIso_of_restrict f (isoOpen f).ι ⟨φ z.val, z.property⟩

end SectionOpens
namespace Frames
open AlgebraicGeometry CategoryTheory TopologicalSpace
open scoped AlgebraicGeometry
variable {X Y : Scheme.{u}}

lemma isUnit_iff_basicOpen_top (c : Γ(X, ⊤)) :
    IsUnit c ↔ X.basicOpen c = ⊤ := by
  refine ⟨X.basicOpen_of_isUnit, fun h => ?_⟩
  apply X.toRingedSpace.isUnit_of_isUnit_germ ⊤ c
  intro x hx
  apply (X.mem_basicOpen c x hx).mp
  rw [h]
  trivial

lemma coefficient_restrict_isUnit {M : X.Modules} (e : M ≅ O X)
    (s : O X ⟶ M) (φ : Y ⟶ X) [IsOpenImmersion φ] :
    IsUnit (φ.appTop (coefficient e s)) ↔
      IsIso ((Scheme.Modules.restrictFunctor φ).map s) := by
  rw [← coefficient_restrict, coefficient_isUnit_iff]
  let F : X.Modules ⥤ Y.Modules := Scheme.Modules.restrictFunctor φ
  let e : F.obj (O X) ≅ O Y := Scheme.Modules.restrictUnitIso φ
  exact isIso_comp_left_iff e.inv (F.map s)

theorem isoOpen_eq_basicOpen {M : X.Modules} (e : M ≅ O X) (s : O X ⟶ M) :
    SectionOpens.isoOpen s = X.basicOpen (coefficient e s) := by
  ext x
  constructor
  · intro hx
    obtain ⟨U, hxU, hU⟩ := (SectionOpens.mem_isoOpen_iff s x).mp hx
    have hc := (coefficient_restrict_isUnit e s U.ι).mpr hU
    have hb := U.toScheme.basicOpen_of_isUnit hc
    rw [← Scheme.preimage_basicOpen_top] at hb
    have H : (⟨x, hxU⟩ : U.toScheme) ∈ U.ι ⁻¹ᵁ X.basicOpen (coefficient e s) := by
      rw [hb]; trivial
    exact H
  · intro hx
    let U := X.basicOpen (coefficient e s)
    refine (SectionOpens.mem_isoOpen_iff s x).mpr ⟨U, hx, ?_⟩
    apply (coefficient_restrict_isUnit e s U.ι).mp
    apply (isUnit_iff_basicOpen_top _).mpr
    rw [← Scheme.preimage_basicOpen_top]
    ext z
    change z.val ∈ X.basicOpen (coefficient e s) ↔ True
    exact iff_true_intro z.property

lemma isoOpen_restrictSection {M : X.Modules} (s : O X ⟶ M)
    (φ : Y ⟶ X) [IsOpenImmersion φ] :
    SectionOpens.isoOpen (restrictSection φ s) = φ ⁻¹ᵁ SectionOpens.isoOpen s := by
  exact (SectionOpens.isoOpen_precomp (Scheme.Modules.restrictUnitIso φ).symm
    ((Scheme.Modules.restrictFunctor φ).map s)).trans (SectionOpens.isoOpen_restrict s φ)

theorem preimage_isoOpen {M : X.Modules} (s : O X ⟶ M)
    (φ : Y ⟶ X) [IsOpenImmersion φ] (e : M.restrict φ ≅ O Y) :
    φ ⁻¹ᵁ SectionOpens.isoOpen s =
      Y.basicOpen (coefficient e (restrictSection φ s)) := by
  rw [← isoOpen_restrictSection, isoOpen_eq_basicOpen e]

end Frames

end PiExponentSeshadri

end

end OAI
end Source0015

section Source0016
/-
Modification notice for the LogTwo project.
Derived from openai/math (Apache-2.0), revision adc7f1241b42e322a6451854ab7e4b4c146bf78a.
Original source: lean/OAI/NumberTheory/PiExponent/Approximation/IntegralLineSections.lean
Changes: Convert module/import declarations to the Lean 4.34 public module format.
See ../../../../../THIRD_PARTY_NOTICES.txt for provenance and the recorded changes.
-/




namespace OAI

noncomputable section

namespace PiExponentSeshadri

namespace Geometry
open CategoryTheory AlgebraicGeometry TopologicalSpace
open scoped AlgebraicGeometry
variable {X : Scheme}

lemma trivialModule_restriction_injective [IsIntegral X] (M : X.Modules)
    (e : M ≅ structureSheaf X) {U V : X.Opens} (i : U ⟶ V) [Nonempty U] :
    Function.Injective (M.presheaf.map i.op) := by
  intro s t h
  apply (ConcreteCategory.bijective_of_isIso
    (((Scheme.Modules.toPresheaf X).mapIso e).app (Opposite.op V)).hom).injective
  have hn := e.hom.mapPresheaf.naturality i.op
  have heq := congrArg (fun a => e.hom.app U a) h
  have hh (a : Γ(M, V)) :
      e.hom.app U (M.presheaf.map i.op a) =
        X.presheaf.map i.op (e.hom.app V a) := by
    exact CategoryTheory.congr_fun hn a
  rw [hh, hh] at heq
  exact map_injective_of_isIntegral X i heq

theorem LineBundle.restriction_injective [IsIntegral X] (L : LineBundle X)
    {U V : X.Opens} (i : U ⟶ V) [Nonempty U] :
    Function.Injective (L.sheaf.presheaf.map i.op) := by
  intro s t h
  apply L.sheaf.isSheaf.section_ext
  intro x hx
  obtain ⟨T, hxT, ⟨e⟩⟩ := L.locallyRankOne x
  let f := T.ι
  let U' : T.toScheme.Opens := f ⁻¹ᵁ U
  let V' : T.toScheme.Opens := f ⁻¹ᵁ V
  have hU' : Nonempty U' := by
    obtain ⟨y, hyT, hyU⟩ := nonempty_preirreducible_inter T.isOpen U.isOpen
      ⟨x, hxT⟩ (by obtain ⟨u⟩ := ‹Nonempty U›; exact ⟨u.val, u.property⟩)
    exact ⟨⟨⟨y, hyT⟩, hyU⟩⟩
  have : Nonempty U' := hU'
  have : Nonempty T := ⟨⟨x, hxT⟩⟩
  let j : U' ⟶ V' := homOfLE (fun _ h => leOfHom i h)
  let W := f ''ᵁ V'
  have hWV : W ≤ V := f.image_preimage_le V
  refine ⟨W, hWV, ?_, ?_⟩
  · exact ⟨⟨x, hxT⟩, hx, rfl⟩
  · apply trivialModule_restriction_injective (L.sheaf.restrict f) e j
    change L.sheaf.presheaf.map ((f.opensFunctor.map j).op)
        (L.sheaf.presheaf.map (homOfLE hWV).op s) =
      L.sheaf.presheaf.map ((f.opensFunctor.map j).op)
        (L.sheaf.presheaf.map (homOfLE hWV).op t)
    have hh := congrArg
      (fun a => L.sheaf.presheaf.map (homOfLE (f.image_preimage_le U)).op a) h
    simp only [← ConcreteCategory.comp_apply, ← Functor.map_comp] at hh ⊢
    have eq : i.op ≫ (homOfLE (f.image_preimage_le U)).op =
        (homOfLE hWV).op ≫ (f.opensFunctor.map j).op := Subsingleton.elim _ _
    rw [eq] at hh
    simpa only [Functor.map_comp, ConcreteCategory.comp_apply] using hh

theorem LineBundle.section_restriction_injective [IsIntegral X] (L : LineBundle X)
    (U : X.Opens) [Nonempty U] :
    Function.Injective (fun s : GlobalSections X L.sheaf => s.app U (1 : Γ(X, U))) := by
  intro s t h
  have natural (s : GlobalSections X L.sheaf) (V : X.Opens) :
      s.app V (1 : Γ(X, V)) = L.sheaf.presheaf.map
        (homOfLE (show V ≤ ⊤ from le_top)).op (s.app ⊤ (1 : Γ(X, ⊤))) := by
    have hs := CategoryTheory.congr_fun (s.mapPresheaf.naturality
      (homOfLE (show V ≤ ⊤ from le_top)).op) (1 : Γ(X, ⊤))
    change s.app V (X.presheaf.map (homOfLE (show V ≤ ⊤ from le_top)).op 1) =
      L.sheaf.presheaf.map (homOfLE (show V ≤ ⊤ from le_top)).op
        (s.app ⊤ (1 : Γ(X, ⊤))) at hs
    simpa only [map_one, ConcreteCategory.comp_apply] using hs
  have ht : s.app ⊤ (1 : Γ(X, ⊤)) = t.app ⊤ (1 : Γ(X, ⊤)) := by
    apply L.restriction_injective (homOfLE (show U ≤ ⊤ from le_top))
    rw [← natural s U, ← natural t U]
    exact h
  ext V a
  change Γ(X, V) at a
  have hv : s.app V (1 : Γ(X, V)) = t.app V (1 : Γ(X, V)) := by
    rw [natural s, natural t, ht]
  have scalar (s : GlobalSections X L.sheaf) :
      s.app V a = a • s.app V (1 : Γ(X, V)) := by
    have hs := s.app_smul (r := a) (x := (1 : Γ(X, V)))
    change s.app V (a * 1 : Γ(X, V)) = _ at hs
    simpa only [mul_one] using hs
  rw [scalar s, scalar t, hv]

variable [IsIntegral X]

theorem LineBundle.noZeroSMulDivisors (L : LineBundle X)
    (U : X.Opens) [Nonempty U] : NoZeroSMulDivisors Γ(X, U) Γ(L.sheaf, U) where
  eq_zero_or_eq_zero_of_smul_eq_zero {a m} h := by
    obtain ⟨x, hx⟩ := ‹Nonempty U›
    obtain ⟨T, hxT, ⟨e⟩⟩ := L.locallyRankOne x
    let V : T.toScheme.Opens := T.ι ⁻¹ᵁ U
    have : Nonempty V := ⟨⟨⟨x, hxT⟩, hx⟩⟩
    have : Nonempty T := ⟨⟨x, hxT⟩⟩
    let W : X.Opens := T.ι ''ᵁ V
    have : Nonempty W := ⟨⟨x, ⟨x, hxT⟩, hx, rfl⟩⟩
    let i : W ⟶ U := homOfLE (T.ι.image_preimage_le U)
    let ar : Γ(X, W) := X.presheaf.map i.op a
    let mr : Γ(L.sheaf, W) := L.sheaf.presheaf.map i.op m
    have hr : ar • mr = 0 := by
      have hh := congrArg (fun z => L.sheaf.presheaf.map i.op z) h
      simpa only [L.sheaf.map_smul, map_zero] using hh
    let ar' : Γ(T.toScheme, V) := (T.ι.appIso V).hom ar
    let mr' : Γ(L.sheaf.restrict T.ι, V) := (L.sheaf.restrictAppIso T.ι V).inv mr
    let cr : Γ(T.toScheme, V) := e.hom.app V mr'
    have hr' : ar' • mr' = 0 := by
      rw [← Scheme.Modules.smul_restrictAppIso_inv_apply]
      simp only [hr, map_zero]
    have hmul : ar' * cr = 0 := by
      have hh := e.hom.app_smul (r := ar') (x := mr')
      change e.hom.app V (ar' • mr') = ar' * cr at hh
      rw [hr', map_zero] at hh
      exact hh.symm
    rcases mul_eq_zero.mp hmul with ha | hm
    · left
      apply map_injective_of_isIntegral X i
      have hinj := (ConcreteCategory.bijective_of_isIso (T.ι.appIso V).hom).injective
      apply hinj
      simpa only [map_zero] using ha
    · right
      apply L.restriction_injective i
      have hinj := (ConcreteCategory.bijective_of_isIso
        (((Scheme.Modules.toPresheaf T.toScheme).mapIso e).app (Opposite.op V)).hom).injective
      apply (ConcreteCategory.bijective_of_isIso (L.sheaf.restrictAppIso T.ι V).inv).injective
      apply hinj
      change cr = e.hom.app V ((L.sheaf.restrictAppIso T.ι V).inv
        (L.sheaf.presheaf.map i.op 0))
      refine hm.trans ?_
      simp only [map_zero]
      rfl

theorem LineBundle.mono_section (L : LineBundle X)
    (s : GlobalSections X L.sheaf) (hs : s ≠ 0) : Mono s := by
  have hmono : Mono s.val := by
    apply PresheafOfModules.mono_of_injective
    intro U
    by_cases hU : Nonempty U.unop
    · let := hU
      let := L.noZeroSMulDivisors U.unop
      intro a b hab
      change Γ(X, U.unop) at a b
      have hc : s.app U.unop (1 : Γ(X, U.unop)) ≠ 0 := by
        intro h
        apply hs
        apply L.section_restriction_injective U.unop
        exact h
      have hscalar (a : Γ(X, U.unop)) : s.app U.unop a =
          a • s.app U.unop (1 : Γ(X, U.unop)) := by
        have hh := s.app_smul (r := a) (x := (1 : Γ(X, U.unop)))
        change s.app U.unop (a * 1 : Γ(X, U.unop)) = _ at hh
        simpa only [mul_one] using hh
      have heq : s.app U.unop a = s.app U.unop b := hab
      rw [hscalar a, hscalar b] at heq
      exact (smul_left_injective Γ(X, U.unop) hc) heq
    · have he : U.unop = ⊥ := by
        apply Opens.ext
        ext x
        exact ⟨fun hx => (hU ⟨⟨x, hx⟩⟩).elim, fun h => h.elim⟩
      have : Subsingleton Γ(X, U.unop) := by rw [he]; infer_instance
      intro a b _
      change Γ(X, U.unop) at a b
      exact Subsingleton.elim a b
  exact (SheafOfModules.forget X.ringCatSheaf).mono_of_mono_map hmono

end Geometry

namespace Frames
open CategoryTheory AlgebraicGeometry
variable {X Y : Scheme}
lemma coefficient_injective {M : X.Modules} (e : M ≅ O X) :
    Function.Injective (coefficient e) := by
  intro s t h
  apply (cancel_mono e.hom).1
  exact endValue_injective h
lemma coefficient_zero {M : X.Modules} (e : M ≅ O X) :
    coefficient e (0 : O X ⟶ M) = 0 := by
  rw [coefficient, CategoryTheory.Limits.zero_comp]
  rfl
lemma restrictSection_zero (φ : Y ⟶ X) [IsOpenImmersion φ] {M : X.Modules} :
    restrictSection φ (0 : O X ⟶ M) = 0 := by
  ext U a
  rfl
end Frames

namespace Geometry
open CategoryTheory AlgebraicGeometry TopologicalSpace
open PiExponentSeshadri.Frames
variable {X Y : Scheme}
lemma LineBundle.restrict_sections_injective [IsIntegral X] (L : LineBundle X)
    (f : Y ⟶ X) [IsOpenImmersion f] [Nonempty Y] :
    Function.Injective (fun s : GlobalSections X L.sheaf =>
      (Scheme.Modules.restrictFunctor f).map s) := by
  intro s t h
  let U : X.Opens := f ''ᵁ ⊤
  have : Nonempty U := by
    obtain ⟨y⟩ := ‹Nonempty Y›
    exact ⟨⟨f y, y, Set.mem_univ y, rfl⟩⟩
  apply L.section_restriction_injective U
  have he := congrArg (fun s : (structureSheaf X).restrict f ⟶ L.sheaf.restrict f =>
    s.app ⊤ (1 : Γ(X, U))) h
  exact he

lemma LineBundle.restricted_coefficient_injective [IsIntegral X] (L : LineBundle X)
    (f : Y ⟶ X) [IsOpenImmersion f] [Nonempty Y]
    (e : L.sheaf.restrict f ≅ O Y) :
    Function.Injective (fun s : GlobalSections X L.sheaf => coefficient e (restrictSection f s)) := by
  intro s t h
  apply L.restrict_sections_injective f
  let u : (structureSheaf X).restrict f ≅ structureSheaf Y :=
    Scheme.Modules.restrictUnitIso f
  apply (cancel_epi u.inv).mp
  exact coefficient_injective e h

lemma LineBundle.isoOpen_ne_bot [IsIntegral X] (L : LineBundle X)
    (s : O X ⟶ L.sheaf) (hs : s ≠ 0) : PiExponentSeshadri.SectionOpens.isoOpen s ≠ ⊥ := by
  obtain ⟨x⟩ : Nonempty X := inferInstance
  obtain ⟨V,hx,⟨e⟩⟩ := L.locallyRankOne x
  let : Nonempty V := ⟨⟨x,hx⟩⟩
  have hc : coefficient e (restrictSection V.ι s) ≠ 0 := by
    intro h
    apply hs
    apply L.restricted_coefficient_injective V.ι e
    have hz : coefficient e (restrictSection V.ι (0 : O X ⟶ L.sheaf)) = 0 :=
      (congrArg (coefficient e) (restrictSection_zero V.ι)).trans (coefficient_zero e)
    exact h.trans hz.symm
  intro hz
  have he := preimage_isoOpen s V.ι e
  rw [hz] at he
  have hb : V.toScheme.basicOpen (coefficient e (restrictSection V.ι s)) = ⊥ := by
    simpa only [Scheme.Hom.preimage_bot] using he.symm
  exact hc (eq_zero_of_basicOpen_eq_bot _ hb)

theorem LineBundle.sectionOpen_nonempty [IsIntegral X] (L : LineBundle X)
    (s : GlobalSections X L.sheaf) (hs : s ≠ 0) :
    Nonempty (sectionOpen X s) := by
  have h := L.isoOpen_ne_bot s hs
  by_contra hn
  apply h
  apply TopologicalSpace.Opens.ext
  ext x
  exact ⟨fun hx => hn ⟨⟨x,hx⟩⟩, fun hx => hx.elim⟩
end Geometry

end PiExponentSeshadri

end

end OAI
end Source0016

section Source0017
/-
Modification notice for the LogTwo project.
Derived from openai/math (Apache-2.0), revision adc7f1241b42e322a6451854ab7e4b4c146bf78a.
Original source: lean/OAI/NumberTheory/PiExponent/Approximation/TensorPure.lean
Changes: Convert module/import declarations to the Lean 4.34 public module format.
Expose private helpers and adjust helper names where needed for module compatibility.
See ../../../../../THIRD_PARTY_NOTICES.txt for provenance and the recorded changes.
-/




namespace OAI

noncomputable section

namespace PiExponentSeshadri.TensorPure

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite
open PiExponentSeshadri.Geometry
open MonoidalCategory

variable {X Y : Scheme.{0}}

local instance sectionModule {X : Scheme.{0}}
    (P : PresheafOfModules X.ringCatSheaf.obj) (U : X.Opens) :
    Module Γ(X, U) (P.obj (op U)) := (P.obj (op U)).isModule

abbrev presheaf (M N : X.Modules) :=
  PresheafOfModulesOfCommRing.Monoidal.tensorObj (R := X.presheaf) M.val N.val

abbrev adj (X : Scheme.{0}) :=
  PresheafOfModules.sheafificationAdjunction (R := X.ringCatSheaf) (𝟙 X.ringCatSheaf.obj)

def pure (M N : X.Modules) (U : X.Opens) (m : M.val.obj (op U)) (n : N.val.obj (op U)) :
    (moduleTensor X M N).val.obj (op U) :=
  (((adj X).unit.app (presheaf M N)).app (op U)).hom (m ⊗ₜ[Γ(X,U)] n)

@[simp] lemma pure_add_left (M N : X.Modules) (U : X.Opens) (m m' : M.val.obj (op U)) (n : N.val.obj (op U)) :
    pure M N U (m+m') n = pure M N U m n + pure M N U m' n := by
  unfold pure
  rw [TensorProduct.add_tmul]
  exact map_add _ _ _

@[simp] lemma pure_add_right (M N : X.Modules) (U : X.Opens) (m : M.val.obj (op U)) (n n' : N.val.obj (op U)) :
    pure M N U m (n+n') = pure M N U m n + pure M N U m n' := by
  unfold pure
  rw [TensorProduct.tmul_add]
  exact map_add _ _ _

@[simp] lemma pure_smul_left (M N : X.Modules) (U : X.Opens) (a : Γ(X,U)) (m : M.val.obj (op U)) (n : N.val.obj (op U)) :
    pure M N U (a • m) n = a • pure M N U m n := by
  unfold pure
  rw [← TensorProduct.smul_tmul']
  exact map_smul _ _ _

@[simp] lemma pure_smul_right (M N : X.Modules) (U : X.Opens) (a : Γ(X,U)) (m : M.val.obj (op U)) (n : N.val.obj (op U)) :
    pure M N U m (a • n) = a • pure M N U m n := by
  simp only [pure]
  rw [TensorProduct.tmul_smul]
  exact map_smul _ _ _

lemma pure_restrict (M N : X.Modules) {U V : X.Opens} (i : V ⟶ U)
    (m : M.val.obj (op U)) (n : N.val.obj (op U)) :
    (moduleTensor X M N).val.map i.op (pure M N U m n) =
      pure M N V (M.val.map i.op m) (N.val.map i.op n) := by
  exact (PresheafOfModules.naturality_apply ((adj X).unit.app (presheaf M N)) i.op
    (m ⊗ₜ[Γ(X,U)] n)).symm

lemma map_pure {M N P Q : X.Modules} (f : M ⟶ P) (g : N ⟶ Q)
    (U : X.Opens) (m : M.val.obj (op U)) (n : N.val.obj (op U)) :
    (moduleTensorMap f g).app U (pure M N U m n) =
      pure P Q U (f.app U m) (g.app U n) := by
  have h := (adj X).unit.naturality
    (PresheafOfModulesOfCommRing.Monoidal.tensorHom (R := X.presheaf) f.val g.val)
  exact (congrArg (fun q => q.app (op U) (m ⊗ₜ[Γ(X,U)] n)) h).symm

lemma hom_ext {M N P : X.Modules} {f g : moduleTensor X M N ⟶ P}
    (h : ∀ U m n, f.app U (pure M N U m n) = g.app U (pure M N U m n)) : f = g := by
  apply ((adj X).homEquiv (presheaf M N) P).injective
  ext U : 1
  apply ModuleCat.MonoidalCategory.tensor_ext
  intro m n
  exact h U.unop m n

lemma sheafify_restrict_unit (f : X ⟶ Y) [IsOpenImmersion f]
    (P : PresheafOfModules Y.ringCatSheaf.obj) :
    (modulePresheafRestrict f).map ((adj Y).unit.app P) ≫
      ((moduleSheafificationRestrict f).hom.app P).val =
    (adj X).unit.app ((modulePresheafRestrict f).obj P) := by
  let a := adj Y
  let b := Scheme.Modules.restrictAdjunction f
  let c := modulePresheafRestrictAdjunction f
  let d := adj X
  apply (c.homEquiv _ _).injective
  erw [Adjunction.homEquiv_unit,Functor.map_comp]
  have hn := c.unit_naturality (a.unit.app P)
  rw [← Category.assoc,hn]
  have he := Adjunction.unit_leftAdjointUniq_hom_app (a.comp b) (c.comp d) P
  have ha := a.comp_unit_app b P
  have hd := c.comp_unit_app d P
  let G : Y.Modules ⥤ PresheafOfModules Y.ringCatSheaf.obj :=
    SheafOfModules.forget Y.ringCatSheaf ⋙
      PresheafOfModules.restrictScalars (𝟙 Y.ringCatSheaf.obj)
  let I : X.Modules ⥤ Y.Modules := Scheme.Modules.pushforward f
  have hh := congrArg (fun h => h ≫ (I ⋙ G).map
    (((a.comp b).leftAdjointUniq (c.comp d)).hom.app P)) ha
  exact hh.symm.trans (he.trans hd)

lemma presheaf_restrict_pure (U : X.Opens) (M N : X.Modules)
    (V : U.toScheme.Opens)
    (m : M.val.obj (op (U.ι ''ᵁ V))) (n : N.val.obj (op (U.ι ''ᵁ V))) :
    ((modulePresheafTensorRestrict U M.val N.val).hom.app (op V)).hom
      (m ⊗ₜ[Γ(X,U.ι ''ᵁ V)] n) = (show ((modulePresheafRestrict U.ι).obj M.val).obj (op V) from m) ⊗ₜ[Γ(U.toScheme,V)]
      (show ((modulePresheafRestrict U.ι).obj N.val).obj (op V) from n) := by
  rfl

lemma restrict_pure (U : X.Opens) (M N : X.Modules) (V : U.toScheme.Opens)
    (m : M.val.obj (op (U.ι ''ᵁ V))) (n : N.val.obj (op (U.ι ''ᵁ V))) :
    (moduleTensorRestrict U M N).hom.app V
      (pure M N (U.ι ''ᵁ V) m n) =
      pure (M.restrict U.ι) (N.restrict U.ι) V m n := by
  have h := sheafify_restrict_unit U.ι (presheaf M N)
  have h' := congrArg (fun q => q.app (op V) (m ⊗ₜ[Γ(X,U.ι ''ᵁ V)] n)) h
  have hn := (adj U.toScheme).unit.naturality
    (modulePresheafTensorRestrict U M.val N.val).hom
  have hn' := congrArg (fun q => q.app (op V) (m ⊗ₜ[Γ(X,U.ι ''ᵁ V)] n)) hn
  change (((PresheafOfModules.sheafification (𝟙 U.toScheme.ringCatSheaf.obj)).map
    (modulePresheafTensorRestrict U M.val N.val).hom).val.app (op V))
    (((moduleSheafificationRestrict U.ι).hom.app (presheaf M N)).val.app (op V)
      (pure M N (U.ι ''ᵁ V) m n)) = _
  simp only [PresheafOfModules.comp_app] at h' hn'
  change (((moduleSheafificationRestrict U.ι).hom.app (presheaf M N)).val.app (op V))
    (pure M N (U.ι ''ᵁ V) m n) = _ at h'
  rw [h']
  refine hn'.symm.trans ?_
  change (((adj U.toScheme).unit.app (presheaf (M.restrict U.ι) (N.restrict U.ι))).app (op V))
    (((modulePresheafTensorRestrict U M.val N.val).hom.app (op V))
      (m ⊗ₜ[Γ(X,U.ι ''ᵁ V)] n)) = _
  exact congrArg (fun t => (((adj U.toScheme).unit.app
    (presheaf (M.restrict U.ι) (N.restrict U.ι))).app (op V)) t)
      (presheaf_restrict_pure U M N V m n)

lemma restrict_pure_inv (U : X.Opens) (M N : X.Modules) (V : U.toScheme.Opens)
    (m : M.val.obj (op (U.ι ''ᵁ V))) (n : N.val.obj (op (U.ι ''ᵁ V))) :
    (moduleTensorRestrict U M N).inv.app V (pure (M.restrict U.ι) (N.restrict U.ι) V m n) =
      pure M N (U.ι ''ᵁ V) m n := by
  have h := congrArg (fun t => (moduleTensorRestrict U M N).inv.app V t)
    (restrict_pure U M N V m n).symm
  refine h.trans ?_
  exact congrArg (fun q => q.app V (pure M N (U.ι ''ᵁ V) m n))
    (moduleTensorRestrict U M N).hom_inv_id

lemma restrict_hom_ext (U : X.Opens) {M N : X.Modules} {P : U.toScheme.Modules}
    {f g : (moduleTensor X M N).restrict U.ι ⟶ P}
    (h : ∀ (V : U.toScheme.Opens) (m : M.val.obj (op (U.ι ''ᵁ V)))
      (n : N.val.obj (op (U.ι ''ᵁ V))), f.app V (pure M N (U.ι ''ᵁ V) m n) =
      g.app V (pure M N (U.ι ''ᵁ V) m n)) : f = g := by
  apply (cancel_epi (moduleTensorRestrict U M N).inv).mp
  apply hom_ext (M := M.restrict U.ι) (N := N.restrict U.ι)
  intro V m n
  change f.app V ((moduleTensorRestrict U M N).inv.app V (pure _ _ V m n)) =
    g.app V ((moduleTensorRestrict U M N).inv.app V (pure _ _ V m n))
  exact (congrArg (fun x => f.app V x) (restrict_pure_inv U M N V m n)).trans
    ((h V m n).trans (congrArg (fun x => g.app V x) (restrict_pure_inv U M N V m n)).symm)

lemma restrict_map (U : X.Opens) {M N P Q : X.Modules}
    (a : M ⟶ P) (b : N ⟶ Q) :
    (Scheme.Modules.restrictFunctor U.ι).map (moduleTensorMap a b) ≫
      (moduleTensorRestrict U P Q).hom =
    (moduleTensorRestrict U M N).hom ≫
      moduleTensorMap ((Scheme.Modules.restrictFunctor U.ι).map a)
        ((Scheme.Modules.restrictFunctor U.ι).map b) := by
  apply restrict_hom_ext U
  intro V m n
  change (moduleTensorRestrict U P Q).hom.app V
    ((moduleTensorMap a b).app (U.ι ''ᵁ V) (pure M N (U.ι ''ᵁ V) m n)) =
    (moduleTensorMap _ _).app V ((moduleTensorRestrict U M N).hom.app V
      (pure M N (U.ι ''ᵁ V) m n))
  exact (congrArg (fun x => (moduleTensorRestrict U P Q).hom.app V x)
    (map_pure a b (U.ι ''ᵁ V) m n)).trans
    ((restrict_pure U P Q V (a.app (U.ι ''ᵁ V) m) (b.app (U.ι ''ᵁ V) n)).trans
      ((map_pure ((Scheme.Modules.restrictFunctor U.ι).map a)
        ((Scheme.Modules.restrictFunctor U.ι).map b) V m n).symm.trans
        (congrArg (fun x => (moduleTensorMap ((Scheme.Modules.restrictFunctor U.ι).map a)
          ((Scheme.Modules.restrictFunctor U.ι).map b)).app V x)
          (restrict_pure U M N V m n)).symm))

lemma unit_pure (M : X.Modules) (U : X.Opens) (a : Γ(X,U)) (m : M.val.obj (op U)) :
    (moduleTensorUnit M).hom.app U (pure (structureSheaf X) M U a m) = a • m := by
  let : MonoidalCategory (PresheafOfModules X.ringCatSheaf.obj) :=
    PresheafOfModulesOfCommRing.monoidalCategory (R := X.presheaf)
  have h := ((adj X).homEquiv _ _).apply_symm_apply (λ_ M.val).hom
  change (adj X).homEquiv _ M (moduleTensorUnit M).hom = (λ_ M.val).hom at h
  exact congrArg (fun q => q.app (op U) (a ⊗ₜ[Γ(X,U)] m)) h

lemma right_unit_pure (M : X.Modules) (U : X.Opens) (m : M.val.obj (op U)) (a : Γ(X,U)) :
    (moduleTensorRightUnit M).hom.app U (pure M (structureSheaf X) U m a) = a • m := by
  let : MonoidalCategory (PresheafOfModules X.ringCatSheaf.obj) :=
    PresheafOfModulesOfCommRing.monoidalCategory (R := X.presheaf)
  have h := ((adj X).homEquiv _ _).apply_symm_apply (ρ_ M.val).hom
  change (adj X).homEquiv _ M (moduleTensorRightUnit M).hom = (ρ_ M.val).hom at h
  exact congrArg (fun q => q.app (op U) (m ⊗ₜ[Γ(X,U)] a)) h

end PiExponentSeshadri.TensorPure

end

end OAI
end Source0017

section Source0018
/-
Modification notice for the LogTwo project.
Derived from openai/math (Apache-2.0), revision adc7f1241b42e322a6451854ab7e4b4c146bf78a.
Original source: lean/OAI/NumberTheory/PiExponent/Approximation/LinePullback.lean
Changes: Convert module/import declarations to the Lean 4.34 public module format.
See ../../../../../THIRD_PARTY_NOTICES.txt for provenance and the recorded changes.
-/




namespace OAI

namespace PiExponentSeshadri.Geometry
noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace
variable {X Y : Scheme.{0}}

instance opensMap_final (f : Y ⟶ X) : (Opens.map f.base).Final := by
  let : PreservesLimit (Functor.empty.{0} X.Opens) (Opens.map f.base) := by
    apply preservesLimit_of_preserves_limit_cone (isTerminalTop (α := X.Opens))
    exact (isLimitMapConeEmptyConeEquiv (Opens.map f.base) (⊤ : X.Opens)).symm isTerminalTop
  infer_instance

def pullbackRestrictIso (f : Y ⟶ X) (L : X.Modules) (U : X.Opens) :
    ((Scheme.Modules.pullback f).obj L).restrict (f ⁻¹ᵁ U).ι ≅
      (Scheme.Modules.pullback (f ∣_ U)).obj (L.restrict U.ι) :=
  (Scheme.Modules.restrictFunctorIsoPullback (f ⁻¹ᵁ U).ι).app _ ≪≫
  (Scheme.Modules.pullbackComp (f ⁻¹ᵁ U).ι f).app L ≪≫
  (Scheme.Modules.pullbackCongr (morphismRestrict_ι f U).symm).app L ≪≫
  ((Scheme.Modules.pullbackComp (f ∣_ U) U.ι).app L).symm ≪≫
  (Scheme.Modules.pullback (f ∣_ U)).mapIso
    ((Scheme.Modules.restrictFunctorIsoPullback U.ι).app L).symm

def LineBundle.pullback (L : LineBundle X) (f : Y ⟶ X) : LineBundle Y where
  sheaf := (Scheme.Modules.pullback f).obj L.sheaf
  locallyRankOne y := by
    obtain ⟨U,hy,⟨e⟩⟩ := L.locallyRankOne (f y)
    refine ⟨f ⁻¹ᵁ U,hy,⟨pullbackRestrictIso f L.sheaf U ≪≫
      (Scheme.Modules.pullback (f ∣_ U)).mapIso e ≪≫ ?_⟩⟩
    letI : (Opens.map (f ∣_ U).base).Final := opensMap_final (f ∣_ U)
    letI : (SheafOfModules.pushforward (f ∣_ U).toRingCatSheafHom).IsRightAdjoint :=
      inferInstanceAs (Scheme.Modules.pushforward (f ∣_ U)).IsRightAdjoint
    let hu : IsIso (SheafOfModules.pullbackObjUnitToUnit (f ∣_ U).toRingCatSheafHom) :=
      SheafOfModules.instIsIsoPullbackObjUnitToUnitOfFinal (f ∣_ U).toRingCatSheafHom
    let a : (SheafOfModules.pullback (f ∣_ U).toRingCatSheafHom).obj
        (SheafOfModules.unit U.toScheme.ringCatSheaf) ≅
        SheafOfModules.unit (f ⁻¹ᵁ U).toScheme.ringCatSheaf :=
      @asIso _ _ _ _ (SheafOfModules.pullbackObjUnitToUnit (f ∣_ U).toRingCatSheafHom) hu
    exact { hom := a.hom, inv := a.inv, hom_inv_id := a.hom_inv_id, inv_hom_id := a.inv_hom_id }

end
end PiExponentSeshadri.Geometry

end OAI
end Source0018

section Source0019
/-
Modification notice for the LogTwo project.
Derived from openai/math (Apache-2.0), revision adc7f1241b42e322a6451854ab7e4b4c146bf78a.
Original source: lean/OAI/NumberTheory/PiExponent/Approximation/PushforwardTensor.lean
Changes: Convert module/import declarations to the Lean 4.34 public module format.
See ../../../../../THIRD_PARTY_NOTICES.txt for provenance and the recorded changes.
-/




namespace OAI

noncomputable section

namespace PiExponentSeshadri

namespace PushforwardTensor
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite
open PiExponentSeshadri.Geometry PiExponentSeshadri.TensorPure
variable {X Y : Scheme.{0}} (f : X ⟶ Y)

def presheafHom (M N : X.Modules) :
    presheaf ((Scheme.Modules.pushforward f).obj M) ((Scheme.Modules.pushforward f).obj N) ⟶
      ((Scheme.Modules.pushforward f).obj (moduleTensor X M N)).val where
  app U := ModuleCat.MonoidalCategory.tensorLift
    (fun m n => pure M N (f ⁻¹ᵁ U.unop) m n)
    (fun m m' n => pure_add_left M N _ m m' n)
    (fun a m n => pure_smul_left M N _ ((f.app U.unop).hom a) m n)
    (fun m n n' => pure_add_right M N _ m n n')
    (fun a m n => pure_smul_right M N _ ((f.app U.unop).hom a) m n)
  naturality {U V} i := by
    apply ModuleCat.MonoidalCategory.tensor_ext
    intro m n
    exact (pure_restrict M N ((Opens.map f.base).map i.unop) m n).symm

def hom (M N : X.Modules) :
    moduleTensor Y ((Scheme.Modules.pushforward f).obj M) ((Scheme.Modules.pushforward f).obj N) ⟶
      (Scheme.Modules.pushforward f).obj (moduleTensor X M N) :=
  ((adj Y).homEquiv _ _).symm (presheafHom f M N)

lemma hom_pure (M N : X.Modules) (U : Y.Opens)
    (m : M.val.obj (op (f ⁻¹ᵁ U))) (n : N.val.obj (op (f ⁻¹ᵁ U))) :
    (hom f M N).app U
      (pure ((Scheme.Modules.pushforward f).obj M) ((Scheme.Modules.pushforward f).obj N) U m n) =
      pure M N (f ⁻¹ᵁ U) m n := by
  have h := ((adj Y).homEquiv
    (presheaf ((Scheme.Modules.pushforward f).obj M) ((Scheme.Modules.pushforward f).obj N))
    ((Scheme.Modules.pushforward f).obj (moduleTensor X M N))).apply_symm_apply (presheafHom f M N)
  exact congrArg (fun q => q.app (op U) (m ⊗ₜ[Γ(Y,U)] n)) h

@[reassoc] lemma naturality {M N P Q : X.Modules} (a : M ⟶ P) (b : N ⟶ Q) :
    moduleTensorMap ((Scheme.Modules.pushforward f).map a) ((Scheme.Modules.pushforward f).map b) ≫
      hom f P Q = hom f M N ≫ (Scheme.Modules.pushforward f).map (moduleTensorMap a b) := by
  apply TensorPure.hom_ext
  intro U m n
  change (hom f P Q).app U ((moduleTensorMap _ _).app U (pure _ _ U m n)) =
    (moduleTensorMap a b).app (f ⁻¹ᵁ U) ((hom f M N).app U (pure _ _ U m n))
  have h₁ := TensorPure.map_pure ((Scheme.Modules.pushforward f).map a)
    ((Scheme.Modules.pushforward f).map b) U m n
  have h₂ := hom_pure f P Q U (a.app (f ⁻¹ᵁ U) m) (b.app (f ⁻¹ᵁ U) n)
  have h₃ := hom_pure f M N U m n
  have h₄ := TensorPure.map_pure a b (f ⁻¹ᵁ U) m n
  exact ((congrArg (fun z => (hom f P Q).app U z) h₁).trans h₂).trans
    ((congrArg (fun z => (moduleTensorMap a b).app (f ⁻¹ᵁ U) z) h₃).trans h₄).symm

end PushforwardTensor

namespace Geometry
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace
open PiExponentSeshadri.Frames
variable {X Y Z : Scheme.{0}}

def pullbackUnitIso (f : Y ⟶ X) : (Scheme.Modules.pullback f).obj (O X) ≅ O Y := by
  letI : (Opens.map f.base).Final := opensMap_final f
  letI : (SheafOfModules.pushforward f.toRingCatSheafHom).IsRightAdjoint :=
    inferInstanceAs (Scheme.Modules.pushforward f).IsRightAdjoint
  let hu : IsIso (SheafOfModules.pullbackObjUnitToUnit f.toRingCatSheafHom) :=
    SheafOfModules.instIsIsoPullbackObjUnitToUnitOfFinal f.toRingCatSheafHom
  let a : (SheafOfModules.pullback f.toRingCatSheafHom).obj
      (SheafOfModules.unit X.ringCatSheaf) ≅ SheafOfModules.unit Y.ringCatSheaf :=
    @asIso _ _ _ _ (SheafOfModules.pullbackObjUnitToUnit f.toRingCatSheafHom) hu
  exact { hom := a.hom, inv := a.inv, hom_inv_id := a.hom_inv_id, inv_hom_id := a.inv_hom_id }

def pullbackSection (f : Y ⟶ X) {M : X.Modules} (s : O X ⟶ M) :
    O Y ⟶ (Scheme.Modules.pullback f).obj M :=
  (pullbackUnitIso f).inv ≫ (Scheme.Modules.pullback f).map s

def pullbackFrame (f : Y ⟶ X) {M : X.Modules} (e : M ≅ O X) :
    (Scheme.Modules.pullback f).obj M ≅ O Y :=
  (Scheme.Modules.pullback f).mapIso e ≪≫ pullbackUnitIso f

lemma pullbackUnit_adjunction (f : Y ⟶ X) :
    (Scheme.Modules.pullbackPushforwardAdjunction f).homEquiv _ _ (pullbackUnitIso f).hom =
      SheafOfModules.unitToPushforwardObjUnit f.toRingCatSheafHom := by
  let : (SheafOfModules.pushforward f.toRingCatSheafHom).IsRightAdjoint :=
    inferInstanceAs (Scheme.Modules.pushforward f).IsRightAdjoint
  change (SheafOfModules.pullbackPushforwardAdjunction f.toRingCatSheafHom).homEquiv _ _
    (SheafOfModules.pullbackObjUnitToUnit f.toRingCatSheafHom) = _
  exact SheafOfModules.pullbackPushforwardAdjunction_homEquiv_pullbackObjUnitToUnit _

end Geometry

end PiExponentSeshadri

end

end OAI
end Source0019

section Source0020
/-
Modification notice for the LogTwo project.
Derived from openai/math (Apache-2.0), revision adc7f1241b42e322a6451854ab7e4b4c146bf78a.
Original source: lean/OAI/NumberTheory/PiExponent/Approximation/TensorOpenBaseChange.lean
Changes: Convert module/import declarations to the Lean 4.34 public module format.
See ../../../../../THIRD_PARTY_NOTICES.txt for provenance and the recorded changes.
-/




namespace OAI

noncomputable section

namespace PiExponentSeshadri.OpenBaseChange

section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite
open PiExponentSeshadri.Geometry PiExponentSeshadri.Frames
variable {X Y : Scheme.{0}} (f : X ⟶ Y) (U : Y.Opens)

def leftSquare :
    Scheme.Modules.restrictFunctor U.ι ⋙ Scheme.Modules.pullback (f ∣_ U) ≅
      Scheme.Modules.pullback f ⋙ Scheme.Modules.restrictFunctor (f ⁻¹ᵁ U).ι :=
  (conjugateIsoEquiv
    ((Scheme.Modules.pullbackPushforwardAdjunction f).comp
      (Scheme.Modules.restrictAdjunction (f ⁻¹ᵁ U).ι))
    ((Scheme.Modules.restrictAdjunction U.ι).comp
      (Scheme.Modules.pullbackPushforwardAdjunction (f ∣_ U)))).symm (rightSquare f U)

lemma unit_compatibility (M : Y.Modules) :
    (Scheme.Modules.restrictFunctor U.ι).map
      ((Scheme.Modules.pullbackPushforwardAdjunction f).unit.app M) ≫
      (iso f U ((Scheme.Modules.pullback f).obj M)).hom =
    (Scheme.Modules.pullbackPushforwardAdjunction (f ∣_ U)).unit.app (M.restrict U.ι) ≫
      (Scheme.Modules.pushforward (f ∣_ U)).map ((leftSquare f U).hom.app M) := by
  let a := Scheme.Modules.pullbackPushforwardAdjunction f
  let b := Scheme.Modules.restrictAdjunction (f ⁻¹ᵁ U).ι
  let c := Scheme.Modules.restrictAdjunction U.ι
  let d := Scheme.Modules.pullbackPushforwardAdjunction (f ∣_ U)
  have h := unit_conjugateEquiv_symm (a.comp b) (c.comp d) (rightSquare f U).hom M
  rw [Adjunction.comp_unit_app, Adjunction.comp_unit_app] at h
  change (a.unit.app M ≫ (Scheme.Modules.pushforward f).map
    (b.unit.app ((Scheme.Modules.pullback f).obj M))) ≫
      (rightSquare f U).hom.app _ =
    (c.unit.app M ≫ (Scheme.Modules.pushforward U.ι).map
      (d.unit.app (M.restrict U.ι))) ≫
      (Scheme.Modules.pushforward U.ι).map
        ((Scheme.Modules.pushforward (f ∣_ U)).map ((leftSquare f U).hom.app M)) at h
  have hc := congrArg (fun q => (Scheme.Modules.restrictFunctor U.ι).map q ≫
    c.counit.app ((Scheme.Modules.pushforward (f ∣_ U)).obj
      (((Scheme.Modules.pullback f).obj M).restrict (f ⁻¹ᵁ U).ι))) h
  simp only [Functor.map_comp, Category.assoc] at hc
  change _ = _ at hc
  have hn := c.counit.naturality
    (d.unit.app (M.restrict U.ι) ≫
      (Scheme.Modules.pushforward (f ∣_ U)).map ((leftSquare f U).hom.app M))
  dsimp only [Functor.comp_map, Functor.id_map] at hn
  rw [Functor.map_comp, Functor.map_comp] at hn
  rw [Category.assoc] at hn
  dsimp only [Functor.comp_obj, Functor.id_obj] at hn
  rw [hn] at hc
  simp only [← Category.assoc] at hc
  have ht := c.left_triangle_components M
  change (Scheme.Modules.restrictFunctor U.ι).map (c.unit.app M) ≫
    c.counit.app (M.restrict U.ι) = 𝟙 _ at ht
  rw [ht, Category.id_comp] at hc
  simpa only [a, b, c, d, iso, asIso_hom, hom, Category.assoc] using hc

end

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite
open PiExponentSeshadri.Geometry PiExponentSeshadri.TensorPure
variable {X Y : Scheme.{0}} (f : X ⟶ Y) (U : Y.Opens)

lemma modules_comp_app {Z : Scheme.{0}} {M N P : Z.Modules} (a : M ⟶ N) (b : N ⟶ P)
    (W : Z.Opens) : (a ≫ b).app W = a.app W ≫ b.app W := rfl

lemma hom_app (M : X.Modules) (V : U.toScheme.Opens) :
    (hom f U M).app V = M.presheaf.map
      (eqToHom (image_morphismRestrict_preimage f U V)).op := by
  change ((Scheme.Modules.restrictAdjunction (f ⁻¹ᵁ U).ι).unit.app M).app
    (f ⁻¹ᵁ (U.ι ''ᵁ V)) ≫
      ((rightSquare f U).hom.app (M.restrict (f ⁻¹ᵁ U).ι)).app (U.ι ''ᵁ V) ≫
      ((Scheme.Modules.restrictAdjunction U.ι).counit.app
        ((Scheme.Modules.pushforward (f ∣_ U)).obj (M.restrict (f ⁻¹ᵁ U).ι))).app V = _
  simp only [rightSquare, Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app,
    Scheme.Modules.restrictAdjunction_unit_app_app,
    Scheme.Modules.restrictAdjunction_counit_app_app]
  simp only [modules_comp_app,Scheme.Modules.pushforwardComp_hom_app_app,
    Scheme.Modules.pushforwardComp_inv_app_app,
    Scheme.Modules.pushforwardCongr_hom_app_app]
  simp only [Scheme.Modules.pushforward_obj_presheaf_map, Scheme.Modules.restrict_map]
  erw [Category.id_comp, Category.comp_id, ← Functor.map_comp, ← Functor.map_comp]
  congr 1

lemma tensor_pure (M N : X.Modules) (V : U.toScheme.Opens)
    (m : M.val.obj (op (f ⁻¹ᵁ (U.ι ''ᵁ V))))
    (n : N.val.obj (op (f ⁻¹ᵁ (U.ι ''ᵁ V)))) :
    (moduleTensorRestrict (f ⁻¹ᵁ U) M N).hom.app ((f ∣_ U) ⁻¹ᵁ V)
      ((hom f U (moduleTensor X M N)).app V
        (pure M N (f ⁻¹ᵁ (U.ι ''ᵁ V)) m n)) =
    pure (M.restrict (f ⁻¹ᵁ U).ι) (N.restrict (f ⁻¹ᵁ U).ι) ((f ∣_ U) ⁻¹ᵁ V)
      ((hom f U M).app V m) ((hom f U N).app V n) := by
  rw [hom_app, hom_app, hom_app]
  change (moduleTensorRestrict (f ⁻¹ᵁ U) M N).hom.app _
    ((moduleTensor X M N).val.map _ (pure M N _ m n)) = _
  exact (congrArg (fun t => (moduleTensorRestrict (f ⁻¹ᵁ U) M N).hom.app
    ((f ∣_ U) ⁻¹ᵁ V) t) (pure_restrict M N
      (eqToHom (image_morphismRestrict_preimage f U V)) m n)).trans
    (restrict_pure (f ⁻¹ᵁ U) M N ((f ∣_ U) ⁻¹ᵁ V) _ _)

lemma tensor_square (M N : X.Modules) :
    (Scheme.Modules.restrictFunctor U.ι).map (PushforwardTensor.hom f M N) ≫
      (iso f U (moduleTensor X M N)).hom ≫
      (Scheme.Modules.pushforward (f ∣_ U)).map
        (moduleTensorRestrict (f ⁻¹ᵁ U) M N).hom =
    (moduleTensorRestrict U ((Scheme.Modules.pushforward f).obj M)
      ((Scheme.Modules.pushforward f).obj N)).hom ≫
      moduleTensorMap (iso f U M).hom (iso f U N).hom ≫
      PushforwardTensor.hom (f ∣_ U) (M.restrict (f ⁻¹ᵁ U).ι) (N.restrict (f ⁻¹ᵁ U).ι) := by
  apply TensorPure.restrict_hom_ext U
  intro V m n
  change (moduleTensorRestrict (f ⁻¹ᵁ U) M N).hom.app ((f ∣_ U) ⁻¹ᵁ V)
    ((hom f U (moduleTensor X M N)).app V
      ((PushforwardTensor.hom f M N).app (U.ι ''ᵁ V)
        (pure _ _ (U.ι ''ᵁ V) m n))) =
    (PushforwardTensor.hom (f ∣_ U) _ _).app V
      ((moduleTensorMap (iso f U M).hom (iso f U N).hom).app V
        ((moduleTensorRestrict U _ _).hom.app V (pure _ _ (U.ι ''ᵁ V) m n)))
  have hA := congrArg (fun z =>
    (moduleTensorRestrict (f ⁻¹ᵁ U) M N).hom.app ((f ∣_ U) ⁻¹ᵁ V)
      ((hom f U (moduleTensor X M N)).app V z))
    (PushforwardTensor.hom_pure f M N (U.ι ''ᵁ V) m n)
  have hB := congrArg (fun z => (PushforwardTensor.hom (f ∣_ U) _ _).app V
    ((moduleTensorMap (iso f U M).hom (iso f U N).hom).app V z))
    (restrict_pure U ((Scheme.Modules.pushforward f).obj M)
      ((Scheme.Modules.pushforward f).obj N) V m n)
  have hC := congrArg (fun z => (PushforwardTensor.hom (f ∣_ U) _ _).app V z)
    (map_pure (iso f U M).hom (iso f U N).hom V m n)
  have hD := PushforwardTensor.hom_pure (f ∣_ U)
    (M.restrict (f ⁻¹ᵁ U).ι) (N.restrict (f ⁻¹ᵁ U).ι) V
      ((hom f U M).app V m) ((hom f U N).app V n)
  exact hA.trans ((tensor_pure f U M N V m n).trans ((hB.trans (hC.trans hD)).symm))

@[reassoc] lemma naturality {M N : X.Modules} (a : M ⟶ N) :
    (Scheme.Modules.restrictFunctor U.ι).map ((Scheme.Modules.pushforward f).map a) ≫
      (iso f U N).hom =
    (iso f U M).hom ≫ (Scheme.Modules.pushforward (f ∣_ U)).map
      ((Scheme.Modules.restrictFunctor (f ⁻¹ᵁ U).ι).map a) := by
  ext V x
  change (hom f U N).app V (a.app (f ⁻¹ᵁ (U.ι ''ᵁ V)) x) =
    a.app ((f ⁻¹ᵁ U).ι ''ᵁ ((f ∣_ U) ⁻¹ᵁ V)) ((hom f U M).app V x)
  rw [hom_app,hom_app]
  exact (CategoryTheory.congr_fun (a.mapPresheaf.naturality
    (eqToHom (image_morphismRestrict_preimage f U V)).op) x).symm

end PiExponentSeshadri.OpenBaseChange

end

end OAI
end Source0020

section Source0021
/-
Modification notice for the LogTwo project.
Derived from openai/math (Apache-2.0), revision adc7f1241b42e322a6451854ab7e4b4c146bf78a.
Original source: lean/OAI/NumberTheory/PiExponent/Approximation/SectionPullback.lean
Changes: Convert module/import declarations to the Lean 4.34 public module format.
See ../../../../../THIRD_PARTY_NOTICES.txt for provenance and the recorded changes.
-/




namespace OAI

namespace PiExponentSeshadri.Geometry
noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace
open PiExponentSeshadri.Frames
variable {X Y Z : Scheme.{0}}

lemma pullback_endValue (f : Y ⟶ X) (a : O X ⟶ O X) :
    endValue ((pullbackUnitIso f).inv ≫ (Scheme.Modules.pullback f).map a ≫
      (pullbackUnitIso f).hom) = f.appTop (endValue a) := by
  let u := SheafOfModules.unitToPushforwardObjUnit f.toRingCatSheafHom
  let b := (pullbackUnitIso f).inv ≫ (Scheme.Modules.pullback f).map a ≫
      (pullbackUnitIso f).hom
  have he : a ≫ u = u ≫ (Scheme.Modules.pushforward f).map b := by
    have hn := (Scheme.Modules.pullbackPushforwardAdjunction f).homEquiv_naturality_left
      a (pullbackUnitIso f).hom
    have hr := (Scheme.Modules.pullbackPushforwardAdjunction f).homEquiv_naturality_right
      (pullbackUnitIso f).hom b
    rw [pullbackUnit_adjunction] at hn hr
    have hcomp : (pullbackUnitIso f).hom ≫ b =
        (Scheme.Modules.pullback f).map a ≫ (pullbackUnitIso f).hom := by simp [b]
    rw [hcomp] at hr
    exact hn.symm.trans hr
  have hev := congrArg (fun t : O X ⟶ (Scheme.Modules.pushforward f).obj (O Y) =>
      t.app ⊤ (1 : Γ(X,⊤))) he
  change f.app ⊤ (a.app ⊤ (1 : Γ(X,⊤))) = b.app (f ⁻¹ᵁ ⊤) (f.app ⊤ 1) at hev
  have hfOne : f.app ⊤ (1 : Γ(X,⊤)) = (1 : Γ(Y,f ⁻¹ᵁ ⊤)) := map_one (f.app ⊤).hom
  rw [hfOne] at hev
  exact hev.symm

lemma coefficient_pullback (f : Y ⟶ X) {M : X.Modules}
    (e : M ≅ O X) (s : O X ⟶ M) :
    coefficient (pullbackFrame f e) (pullbackSection f s) =
      f.appTop (coefficient e s) := by
  unfold coefficient pullbackFrame pullbackSection
  simp only [Iso.trans_hom, Functor.mapIso_hom, Category.assoc]
  rw [← Functor.map_comp_assoc]
  exact pullback_endValue f (s ≫ e.hom)

end
end PiExponentSeshadri.Geometry

end OAI
end Source0021

section Source0022
/-
Modification notice for the LogTwo project.
Derived from openai/math (Apache-2.0), revision adc7f1241b42e322a6451854ab7e4b4c146bf78a.
Original source: lean/OAI/NumberTheory/PiExponent/Cohomology/CurveEuler.lean
Changes: Convert module/import declarations to the Lean 4.34 public module format.
See ../../../../../THIRD_PARTY_NOTICES.txt for provenance and the recorded changes.
-/




namespace OAI

noncomputable section

namespace PiExponentSeshadri.Geometry

section
open CategoryTheory AlgebraicGeometry TopologicalSpace
open scoped AlgebraicGeometry
variable (X : Scheme)

def restrictScalar (U : X.Opens) : Γ(X, ⊤) →+* Γ(X, U) :=
  (X.presheaf.map (homOfLE le_top).op).hom

lemma restrictScalar_naturality {U V : X.Opens} (i : U ⟶ V) (r : Γ(X, ⊤)) :
    X.presheaf.map i.op (restrictScalar X V r) = restrictScalar X U r := by
  change (X.presheaf.map (homOfLE le_top).op ≫ X.presheaf.map i.op) r = _
  rw [← X.presheaf.map_comp]
  rfl

def sheafHomSMul {M N : X.Modules} (r : Γ(X, ⊤)) (f : M ⟶ N) : M ⟶ N where
  val := {
    app U := by
      letI : Module Γ(X, U.unop) (M.val.obj U) := (M.val.obj U).isModule
      letI : Module Γ(X, U.unop) (N.val.obj U) := (N.val.obj U).isModule
      let g : M.val.obj U →ₗ[Γ(X, U.unop)] N.val.obj U := (f.val.app U).hom
      exact ModuleCat.ofHom ((restrictScalar X U.unop r) • g)
    naturality {U V} g := by
      let : Module (X.presheaf.obj V) (N.presheaf.obj V) := (N.val.obj V).isModule
      ext m
      change restrictScalar X V.unop r • f.app V.unop (M.presheaf.map g m) =
        N.presheaf.map g (restrictScalar X U.unop r • f.app U.unop m)
      have hn := CategoryTheory.congr_fun (f.mapPresheaf.naturality g) m
      change f.app V.unop (M.presheaf.map g m) =
        N.presheaf.map g (f.app U.unop m) at hn
      rw [hn]
      calc
        _ = X.presheaf.map g (restrictScalar X U.unop r) •
            N.presheaf.map g (f.app U.unop m) := by
              exact congrArg (fun a : X.presheaf.obj V =>
                a • N.presheaf.map g (f.app U.unop m))
                (restrictScalar_naturality X g.unop r).symm
        _ = _ := (N.map_smul g.unop (restrictScalar X U.unop r) (f.app U.unop m)).symm }

instance sheafHomModule (M N : X.Modules) : Module Γ(X, ⊤) (M ⟶ N) where
  smul := sheafHomSMul X
  one_smul f := by
    ext U m
    change restrictScalar X U 1 • f.app U m = f.app U m
    simp
  mul_smul r s f := by
    ext U m
    change restrictScalar X U (r * s) • f.app U m =
      restrictScalar X U r • (restrictScalar X U s • f.app U m)
    simp [mul_smul]
  smul_zero r := by
    ext U m
    change restrictScalar X U r • (0 : Γ(N, U)) = 0
    exact smul_zero _
  smul_add r f g := by
    ext U m
    change restrictScalar X U r • (f.app U m + g.app U m) =
      restrictScalar X U r • f.app U m + restrictScalar X U r • g.app U m
    exact smul_add _ _ _
  zero_smul f := by
    ext U m
    change restrictScalar X U 0 • f.app U m = 0
    simp
  add_smul r s f := by
    ext U m
    change restrictScalar X U (r + s) • f.app U m =
      restrictScalar X U r • f.app U m + restrictScalar X U s • f.app U m
    simp [add_smul]

instance sheafLinear : Linear Γ(X, ⊤) X.Modules where
  smul_comp M N P r f g := by
    ext U m
    change g.app U (restrictScalar X U r • f.app U m) =
      restrictScalar X U r • g.app U (f.app U m)
    exact g.app_smul _ _
  comp_smul M N P f r g := by
    ext U m
    rfl

end

section
open CategoryTheory AlgebraicGeometry TopologicalSpace
open scoped AlgebraicGeometry

variable {X : Scheme.{0}}

instance schemeHasExt : HasExt.{1} X.Modules := HasExt.standard X.Modules

def baseScalars (f : X ⟶ Spec (CommRingCat.of ℂ)) : ℂ →+* Γ(X, ⊤) :=
  f.appTop.hom.comp (Scheme.ΓSpecIso (CommRingCat.of ℂ)).inv.hom

abbrev complexSectionModule (f : X ⟶ Spec (CommRingCat.of ℂ)) (M : X.Modules) :
    Module ℂ (GlobalSections X M) :=
  Module.compHom _ (baseScalars f)

abbrev cohomology (M : X.Modules) (n : ℕ) : Type 1 :=
  Abelian.Ext.{1} (C := X.Modules) (structureSheaf X) M n

def cohomologyDimension (f : X ⟶ Spec (CommRingCat.of ℂ))
    (M : X.Modules) (n : ℕ) : ℕ :=
  letI : Module ℂ (cohomology M n) :=
    Module.compHom (cohomology M n) (baseScalars f)
  Module.finrank ℂ (cohomology M n)

def eulerCharacteristic (f : X ⟶ Spec (CommRingCat.of ℂ)) (d : ℕ)
    (M : X.Modules) : ℤ :=
  ∑ n ∈ Finset.range (d + 1), (-1 : ℤ) ^ n * (cohomologyDimension f M n : ℤ)

end

open AlgebraicGeometry CategoryTheory TopologicalSpace Abelian Opposite
variable {X : Scheme}

def globalHomLinearEquiv (M : X.Modules) :
    GlobalSections X M ≃ₗ[Γ(X,⊤)] Γ(M,⊤) where
  toEquiv := FlasqueCohomology.globalHomEquiv X.ringCatSheaf M
  map_add' := by intro f g; rfl
  map_smul' := by
    intro r f
    change restrictScalar X ⊤ r • f.app ⊤ (1 : Γ(X,⊤)) = r • f.app ⊤ (1 : Γ(X,⊤))
    congr 1
    change (X.presheaf.map (𝟙 (op ⊤))) r = r
    rw [X.presheaf.map_id]
    rfl

def cohomologyZeroSections (f : X ⟶ Spec (CommRingCat.of ℂ)) (M : X.Modules) :
    let _ : Module ℂ (cohomology M 0) := Module.compHom _ (baseScalars f)
    let _ : Module ℂ Γ(M,⊤) := Module.compHom _ (baseScalars f)
    cohomology M 0 ≃ₗ[ℂ] Γ(M,⊤) := by
  dsimp only
  letI : Module ℂ (cohomology M 0) := Module.compHom _ (baseScalars f)
  letI : Module ℂ Γ(M,⊤) := Module.compHom _ (baseScalars f)
  let e := (Ext.linearEquiv₀ (R := Γ(X,⊤)) (X := structureSheaf X) (Y := M)).trans
    (globalHomLinearEquiv M)
  exact { e.toAddEquiv with map_smul' := fun r x => e.map_smul (baseScalars f r) x }

lemma cohomologyDimension_zero (f : X ⟶ Spec (CommRingCat.of ℂ)) (M : X.Modules) :
    cohomologyDimension f M 0 =
      let _ : Module ℂ Γ(M,⊤) := Module.compHom _ (baseScalars f)
      Module.finrank ℂ Γ(M,⊤) := by
  let : Module ℂ (cohomology M 0) := Module.compHom _ (baseScalars f)
  let : Module ℂ Γ(M,⊤) := Module.compHom _ (baseScalars f)
  exact (cohomologyZeroSections f M).finrank_eq

theorem affine_eulerCharacteristic (f : X ⟶ Spec (CommRingCat.of ℂ))
    [IsAffine X] [IsNoetherian X] (M : X.Modules) [M.IsQuasicoherent] (d : ℕ) :
    eulerCharacteristic f d M =
      let _ : Module ℂ Γ(M,⊤) := Module.compHom _ (baseScalars f)
      (Module.finrank ℂ Γ(M,⊤) : ℤ) := by
  unfold eulerCharacteristic
  rw [Finset.sum_eq_single 0]
  · simp only [pow_zero, one_mul, cohomologyDimension_zero]
  · intro n hn hn0
    obtain ⟨m,rfl⟩ := Nat.exists_eq_succ_of_ne_zero hn0
    have : Subsingleton (cohomology M (m+1)) :=
      ⟨fun x y => (AffineSchemeCohomology.affine_ext_zero X M m x).trans
        (AffineSchemeCohomology.affine_ext_zero X M m y).symm⟩
    simp [cohomologyDimension, Module.finrank_zero_of_subsingleton]
  · simp

end PiExponentSeshadri.Geometry

end

end OAI
end Source0022

section Source0023
/-
Modification notice for the LogTwo project.
Derived from openai/math (Apache-2.0), revision adc7f1241b42e322a6451854ab7e4b4c146bf78a.
Original source: lean/OAI/NumberTheory/PiExponent/Cohomology/CohomologyIso.lean
Changes: Convert module/import declarations to the Lean 4.34 public module format.
See ../../../../../THIRD_PARTY_NOTICES.txt for provenance and the recorded changes.
-/




namespace OAI

namespace PiExponentSeshadri.Geometry
noncomputable section
open CategoryTheory CategoryTheory.Abelian AlgebraicGeometry
variable {X : Scheme.{0}}

def cohomologyIso (f : X ⟶ Spec (CommRingCat.of ℂ))
    {M N : X.Modules} (e : M ≅ N) (n : ℕ) :
    let _ := Module.compHom (cohomology M n) (baseScalars f)
    let _ := Module.compHom (cohomology N n) (baseScalars f)
    cohomology M n ≃ₗ[ℂ] cohomology N n := by
  dsimp only
  letI := Module.compHom (cohomology M n) (baseScalars f)
  letI := Module.compHom (cohomology N n) (baseScalars f)
  let g := (Ext.mk₀ e.hom).postcompOfLinear Γ(X,⊤) (structureSheaf X) (add_zero n)
  let h := (Ext.mk₀ e.inv).postcompOfLinear Γ(X,⊤) (structureSheaf X) (add_zero n)
  refine
    { toFun := g
      invFun := h
      map_add' := g.map_add
      map_smul' := fun r x => g.map_smul (baseScalars f r) x
      left_inv := ?_
      right_inv := ?_ }
  · intro x
    change (x.comp (Ext.mk₀ e.hom) (add_zero n)).comp (Ext.mk₀ e.inv) (add_zero n) = x
    rw [Ext.comp_assoc_of_second_deg_zero, Ext.mk₀_comp_mk₀,
      e.hom_inv_id, Ext.comp_mk₀_id]
  · intro x
    change (x.comp (Ext.mk₀ e.inv) (add_zero n)).comp (Ext.mk₀ e.hom) (add_zero n) = x
    rw [Ext.comp_assoc_of_second_deg_zero, Ext.mk₀_comp_mk₀,
      e.inv_hom_id, Ext.comp_mk₀_id]

lemma eulerCharacteristic_iso (f : X ⟶ Spec (CommRingCat.of ℂ))
    {M N : X.Modules} (e : M ≅ N) (d : ℕ) :
    eulerCharacteristic f d M = eulerCharacteristic f d N := by
  apply Finset.sum_congr rfl
  intro n _
  congr 2
  let := Module.compHom (cohomology M n) (baseScalars f)
  let := Module.compHom (cohomology N n) (baseScalars f)
  exact (cohomologyIso f e n).finrank_eq

end
end PiExponentSeshadri.Geometry

end OAI
end Source0023

section Source0024
/-
Modification notice for the LogTwo project.
Derived from openai/math (Apache-2.0), revision adc7f1241b42e322a6451854ab7e4b4c146bf78a.
Original source: lean/OAI/NumberTheory/PiExponent/Cohomology/EulerExact.lean
Changes: Convert module/import declarations to the Lean 4.34 public module format.
See ../../../../../THIRD_PARTY_NOTICES.txt for provenance and the recorded changes.
-/




namespace OAI

noncomputable section

namespace PiExponentSeshadri

namespace Cohomology
open CategoryTheory CategoryTheory.Abelian

def alternatingTrunc (a : ℕ → ℤ) (d : ℕ) : ℤ :=
  ∑ i ∈ Finset.range (d+1), (-1 : ℤ)^i * a i

lemma alternatingTrunc_succ (a : ℕ → ℤ) (d : ℕ) :
    alternatingTrunc a (d+1) = alternatingTrunc a d + (-1 : ℤ)^(d+1) * a (d+1) := by
  exact Finset.sum_range_succ _ _

lemma alternating_rank_identity (a b c f g h : ℕ → ℤ)
    (hB : ∀ n, b n = f n + g n) (hC : ∀ n, c n = g n + h n)
    (hA0 : a 0 = f 0) (hA : ∀ n, a (n+1) = h n + f (n+1)) (d : ℕ) :
    alternatingTrunc b d - alternatingTrunc a d - alternatingTrunc c d =
      (-1 : ℤ)^(d+1) * h d := by
  induction d with
  | zero => simp [alternatingTrunc, hB, hC, hA0]
  | succ d ih =>
    simp only [alternatingTrunc_succ]
    calc
      _ = (alternatingTrunc b d - alternatingTrunc a d - alternatingTrunc c d) +
          (-1 : ℤ)^(d+1) * (b (d+1) - a (d+1) - c (d+1)) := by ring
      _ = _ := by rw [ih, hB, hC, hA, pow_succ _ (d+1)]; ring

lemma finrank_middle_of_exact {K U V W : Type*} [Field K]
    [AddCommGroup U] [Module K U] [AddCommGroup V] [Module K V]
    [AddCommGroup W] [Module K W] [FiniteDimensional K V]
    (f : U →ₗ[K] V) (g : V →ₗ[K] W) (hfg : Function.Exact f g) :
    Module.finrank K V = Module.finrank K f.range + Module.finrank K g.range := by
  have hh := LinearMap.finrank_range_add_finrank_ker g
  rw [hfg.linearMap_ker_eq] at hh
  omega

universe w v u t
variable {K : Type t} [Field K] {C : Type u} [Category.{v} C] [Abelian C]
  [Linear K C] [HasExt.{w} C]

def extEuler (E M : C) (d : ℕ) : ℤ :=
  alternatingTrunc (fun n => Module.finrank K (Ext E M n)) d

variable (E : C) {S : ShortComplex C} (hS : S.ShortExact)

def cohomologyMap₁ (n : ℕ) : Ext E S.X₁ n →ₗ[K] Ext E S.X₂ n :=
  (Ext.mk₀ S.f).postcompOfLinear K E (add_zero n)

def cohomologyMap₂ (n : ℕ) : Ext E S.X₂ n →ₗ[K] Ext E S.X₃ n :=
  (Ext.mk₀ S.g).postcompOfLinear K E (add_zero n)

def cohomologyBoundary (n : ℕ) : Ext E S.X₃ n →ₗ[K] Ext E S.X₁ (n+1) :=
  hS.extClass.postcompOfLinear K E rfl

include hS in
lemma cohomology_exact₂ (n : ℕ) :
    Function.Exact (cohomologyMap₁ (K := K) E (S := S) n)
      (cohomologyMap₂ (K := K) E (S := S) n) := by
  intro x
  constructor
  · exact Ext.covariant_sequence_exact₂ E hS x
  · rintro ⟨y, rfl⟩
    change (y.comp (Ext.mk₀ S.f) (add_zero n)).comp (Ext.mk₀ S.g) (add_zero n) = 0
    simp [Ext.mk₀_comp_mk₀]

lemma cohomology_exact₃ (n : ℕ) :
    Function.Exact (cohomologyMap₂ (K := K) E (S := S) n)
      (cohomologyBoundary (K := K) E hS n) := by
  intro x
  constructor
  · exact Ext.covariant_sequence_exact₃ E hS x rfl
  · rintro ⟨y, rfl⟩
    change (y.comp (Ext.mk₀ S.g) (add_zero n)).comp hS.extClass rfl = 0
    rw [Ext.comp_assoc_of_second_deg_zero, hS.comp_extClass, Ext.comp_zero]

lemma cohomology_exact₁ (n : ℕ) :
    Function.Exact (cohomologyBoundary (K := K) E hS n)
      (cohomologyMap₁ (K := K) E (S := S) (n+1)) := by
  intro x
  constructor
  · exact fun hx => Ext.covariant_sequence_exact₁ E hS x hx rfl
  · rintro ⟨y, rfl⟩
    change (y.comp hS.extClass rfl).comp (Ext.mk₀ S.f) (add_zero (n+1)) = 0
    rw [Ext.comp_assoc_of_third_deg_zero, hS.extClass_comp, Ext.comp_zero]

theorem extEuler_add_of_boundary_zero (d : ℕ)
    (hfinite₁ : ∀ n ≤ d, FiniteDimensional K (Ext E S.X₁ n))
    (hfinite₂ : ∀ n ≤ d, FiniteDimensional K (Ext E S.X₂ n))
    (hfinite₃ : ∀ n ≤ d, FiniteDimensional K (Ext E S.X₃ n))
    (hvan : cohomologyBoundary (K := K) E hS d = 0) :
    extEuler (K := K) E S.X₂ d =
      extEuler (K := K) E S.X₁ d + extEuler (K := K) E S.X₃ d := by
  classical
  let a (n : ℕ) : ℤ := Module.finrank K (Ext E S.X₁ n)
  let b (n : ℕ) : ℤ := Module.finrank K (Ext E S.X₂ n)
  let c (n : ℕ) : ℤ := Module.finrank K (Ext E S.X₃ n)
  let f (n : ℕ) : ℤ := Module.finrank K (cohomologyMap₁ (K := K) E (S := S) n).range
  let g (n : ℕ) : ℤ := Module.finrank K (cohomologyMap₂ (K := K) E (S := S) n).range
  let h (n : ℕ) : ℤ := Module.finrank K (cohomologyBoundary (K := K) E hS n).range
  have hB (n : ℕ) (hn : n ≤ d) : b n = f n + g n := by
    let := hfinite₂ n hn
    dsimp only [b, f, g]
    exact_mod_cast finrank_middle_of_exact _ _ (cohomology_exact₂ (K := K) E hS n)
  have hC (n : ℕ) (hn : n ≤ d) : c n = g n + h n := by
    let := hfinite₃ n hn
    dsimp only [c, g, h]
    exact_mod_cast finrank_middle_of_exact _ _ (cohomology_exact₃ (K := K) E hS n)
  have hA0 : a 0 = f 0 := by
    have : Mono S.f := hS.mono_f
    dsimp only [a, f]
    exact_mod_cast (LinearMap.finrank_range_of_inj
      (f := cohomologyMap₁ (K := K) E (S := S) 0)
      (Ext.postcomp_mk₀_injective_of_mono E S.f)).symm
  have hA (n : ℕ) (hn : n+1 ≤ d) : a (n+1) = h n + f (n+1) := by
    let := hfinite₁ (n+1) hn
    dsimp only [a, h, f]
    exact_mod_cast finrank_middle_of_exact _ _ (cohomology_exact₁ (K := K) E hS n)
  have hind (n : ℕ) (hn : n ≤ d) :
      alternatingTrunc b n - alternatingTrunc a n - alternatingTrunc c n =
        (-1 : ℤ)^(n+1) * h n := by
    induction n with
    | zero => simp [alternatingTrunc, hB 0 hn, hC 0 hn, hA0]
    | succ n ih =>
      have hi := ih (by omega)
      simp only [alternatingTrunc_succ]
      calc
        _ = (alternatingTrunc b n - alternatingTrunc a n - alternatingTrunc c n) +
          (-1 : ℤ)^(n+1) * (b (n+1) - a (n+1) - c (n+1)) := by ring
        _ = _ := by rw [hi, hB (n+1) hn, hC (n+1) hn, hA n hn, pow_succ _ (n+1)]; ring
  have hd : h d = 0 := by
    dsimp only [h]
    rw [hvan, LinearMap.range_zero]
    rw [finrank_bot]
    rfl
  have hh := hind d le_rfl
  rw [hd, mul_zero] at hh
  change alternatingTrunc b d = alternatingTrunc a d + alternatingTrunc c d
  omega

include hS in

theorem extEuler_add (d : ℕ)
    (hfinite₁ : ∀ n ≤ d, FiniteDimensional K (Ext E S.X₁ n))
    (hfinite₂ : ∀ n ≤ d, FiniteDimensional K (Ext E S.X₂ n))
    (hfinite₃ : ∀ n ≤ d, FiniteDimensional K (Ext E S.X₃ n))
    [Subsingleton (Ext E S.X₁ (d+1))] :
    extEuler (K := K) E S.X₂ d =
      extEuler (K := K) E S.X₁ d + extEuler (K := K) E S.X₃ d :=
  extEuler_add_of_boundary_zero E hS d hfinite₁ hfinite₂ hfinite₃ (Subsingleton.elim _ _)

end Cohomology

namespace Geometry
open CategoryTheory CategoryTheory.Abelian AlgebraicGeometry
open scoped AlgebraicGeometry
variable {X : Scheme.{0}} (f : X ⟶ Spec (CommRingCat.of ℂ))

@[instance_reducible]
def sheafComplexLinear : Linear ℂ X.Modules where
  homModule M N := Module.compHom _ (baseScalars f)
  smul_comp M N P r g h := by
    change ((baseScalars f r) • g) ≫ h = (baseScalars f r) • (g ≫ h)
    exact Linear.smul_comp _ _ _ _ _ _
  comp_smul M N P g r h := by
    change g ≫ ((baseScalars f r) • h) = (baseScalars f r) • (g ≫ h)
    exact Linear.comp_smul _ _ _ _ _ _

@[instance_reducible]
def complexExtModule (M : X.Modules) (n : ℕ) : Module ℂ (cohomology M n) :=
  letI := sheafComplexLinear f
  inferInstance

lemma complexExtModule_eq (M : X.Modules) (n : ℕ) :
    complexExtModule f M n = Module.compHom (cohomology M n) (baseScalars f) := by
  apply Module.ext'
  intro r x
  let := sheafComplexLinear f
  change r • x = (baseScalars f r) • x
  rw [Ext.smul_eq_comp_mk₀ (R := ℂ), Ext.smul_eq_comp_mk₀ (R := Γ(X, ⊤))]
  rfl

lemma eulerCharacteristic_eq_extEuler (M : X.Modules) (d : ℕ) :
    eulerCharacteristic f d M =
      letI := sheafComplexLinear f
      Cohomology.extEuler (K := ℂ) (structureSheaf X) M d := by
  unfold eulerCharacteristic Cohomology.extEuler Cohomology.alternatingTrunc
  apply Finset.sum_congr rfl
  intro n hn
  have hh := complexExtModule_eq f M n
  unfold cohomologyDimension
  rw [← hh]

theorem eulerCharacteristic_add {S : ShortComplex X.Modules} (hS : S.ShortExact)
    (d : ℕ)
    (hfinite₁ : ∀ n ≤ d, letI := Module.compHom (cohomology S.X₁ n) (baseScalars f)
      FiniteDimensional ℂ (cohomology S.X₁ n))
    (hfinite₂ : ∀ n ≤ d, letI := Module.compHom (cohomology S.X₂ n) (baseScalars f)
      FiniteDimensional ℂ (cohomology S.X₂ n))
    (hfinite₃ : ∀ n ≤ d, letI := Module.compHom (cohomology S.X₃ n) (baseScalars f)
      FiniteDimensional ℂ (cohomology S.X₃ n))
    [Subsingleton (cohomology S.X₁ (d+1))] :
    eulerCharacteristic f d S.X₂ =
      eulerCharacteristic f d S.X₁ + eulerCharacteristic f d S.X₃ := by
  let := sheafComplexLinear f
  rw [eulerCharacteristic_eq_extEuler, eulerCharacteristic_eq_extEuler,
    eulerCharacteristic_eq_extEuler]
  apply Cohomology.extEuler_add (K := ℂ) (structureSheaf X) hS d
  · intro n hn
    have hh := complexExtModule_eq f S.X₁ n
    change @FiniteDimensional ℂ (cohomology S.X₁ n) _ _ (complexExtModule f S.X₁ n)
    rw [hh]
    exact hfinite₁ n hn
  · intro n hn
    have hh := complexExtModule_eq f S.X₂ n
    change @FiniteDimensional ℂ (cohomology S.X₂ n) _ _ (complexExtModule f S.X₂ n)
    rw [hh]
    exact hfinite₂ n hn
  · intro n hn
    have hh := complexExtModule_eq f S.X₃ n
    change @FiniteDimensional ℂ (cohomology S.X₃ n) _ _ (complexExtModule f S.X₃ n)
    rw [hh]
    exact hfinite₃ n hn

end Geometry

end PiExponentSeshadri

end

end OAI
end Source0024

section Source0025
/-
Modification notice for the LogTwo project.
Derived from openai/math (Apache-2.0), revision adc7f1241b42e322a6451854ab7e4b4c146bf78a.
Original source: lean/OAI/NumberTheory/PiExponent/Cohomology/CurveZeroEuler.lean
Changes: Convert module/import declarations to the Lean 4.34 public module format.
See ../../../../../THIRD_PARTY_NOTICES.txt for provenance and the recorded changes.
-/




namespace OAI

noncomputable section
open CategoryTheory AlgebraicGeometry
open PiExponentSeshadri.Geometry

namespace PiExponent.CurveZeroEuler

def algebraStructureMap (B : Type) [CommRing B] [Algebra ℂ B] :
    Spec (CommRingCat.of B) ⟶ Spec (CommRingCat.of ℂ) :=
  Spec.map (CommRingCat.ofHom (algebraMap ℂ B))

def specStructureSectionsEquiv (B : Type) [CommRing B] [Algebra ℂ B] :
    letI : Module ℂ Γ(structureSheaf (Spec (CommRingCat.of B)), ⊤) :=
      Module.compHom _ (baseScalars (algebraStructureMap B))
    Γ(structureSheaf (Spec (CommRingCat.of B)), ⊤) ≃ₗ[ℂ] B := by
  letI : Module ℂ Γ(structureSheaf (Spec (CommRingCat.of B)), ⊤) :=
    Module.compHom _ (baseScalars (algebraStructureMap B))
  refine { ((Scheme.ΓSpecIso (CommRingCat.of B)).commRingCatIsoToRingEquiv).toAddEquiv with
    map_smul' := ?_ }
  intro c x
  change Γ(Spec (CommRingCat.of B), ⊤) at x
  change (Scheme.ΓSpecIso (CommRingCat.of B)).hom
    (baseScalars (algebraStructureMap B) c * x) =
      c • (Scheme.ΓSpecIso (CommRingCat.of B)).hom x
  rw [Algebra.smul_def]
  rw [map_mul]
  congr 1
  change ((Spec.map (CommRingCat.ofHom (algebraMap ℂ B))).appTop ≫
    (Scheme.ΓSpecIso (CommRingCat.of B)).hom)
      ((Scheme.ΓSpecIso (CommRingCat.of ℂ)).inv c) = _
  rw [Scheme.ΓSpecIso_naturality]
  simp

theorem affine_algebra_eulerCharacteristic (B : Type) [CommRing B] [Algebra ℂ B]
    [IsNoetherianRing B] (d : ℕ) :
    eulerCharacteristic (algebraStructureMap B) d
      (structureSheaf (Spec (CommRingCat.of B))) = (Module.finrank ℂ B : ℤ) := by
  let : (structureSheaf (Spec (CommRingCat.of B))).IsQuasicoherent :=
    (isQuasicoherent_iff_isIso_fromTildeΓ _).mpr (by
      change IsIso (Scheme.Modules.fromTildeΓ (SheafOfModules.unit (Spec (CommRingCat.of B)).ringCatSheaf))
      infer_instance)
  rw [affine_eulerCharacteristic]
  let : Module ℂ Γ(structureSheaf (Spec (CommRingCat.of B)), ⊤) :=
    Module.compHom _ (baseScalars (algebraStructureMap B))
  exact congrArg (fun n : ℕ => (n : ℤ)) (specStructureSectionsEquiv B).finrank_eq

theorem principal_zero_euler_eq_order
    {A : Type} [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
    [Algebra ℂ A] [Algebra.IsIntegral ℂ (IsLocalRing.ResidueField A)]
    {a : A} (ha : a ≠ 0) (d : ℕ) :
    eulerCharacteristic (algebraStructureMap (A ⧸ Ideal.span {a})) d
      (structureSheaf (Spec (CommRingCat.of (A ⧸ Ideal.span {a})))) =
        ((IsDiscreteValuationRing.addVal A a).toNat : ℤ) := by
  rw [affine_algebra_eulerCharacteristic]
  have h := CurveLocalOrder.principal_quotient_finrank_eq_order_of_algClosed (F := ℂ) ha
  rw [← h]
  simp

theorem rational_order_eq_euler_difference
    {A K : Type} [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
    [Algebra ℂ A] [Algebra.IsIntegral ℂ (IsLocalRing.ResidueField A)]
    [Field K] [Algebra A K] [IsFractionRing A K]
    {a b : A} (ha : a ≠ 0) (hb : b ≠ 0) (d : ℕ) :
    WeightedCurveDegree.integerOrder (CurveLocalOrder.fractionAddValuation A K)
      (Units.mk0 (algebraMap A K a)
        ((map_ne_zero_iff _ (IsFractionRing.injective A K)).mpr ha) /
       Units.mk0 (algebraMap A K b)
        ((map_ne_zero_iff _ (IsFractionRing.injective A K)).mpr hb)) =
      eulerCharacteristic (algebraStructureMap (A ⧸ Ideal.span {a})) d
        (structureSheaf (Spec (CommRingCat.of (A ⧸ Ideal.span {a})))) -
      eulerCharacteristic (algebraStructureMap (A ⧸ Ideal.span {b})) d
        (structureSheaf (Spec (CommRingCat.of (A ⧸ Ideal.span {b})))) := by
  rw [WeightedCurveDegree.integerOrder_div,
    CurveLocalOrder.integerOrder_field_image_eq_length ha,
    CurveLocalOrder.integerOrder_field_image_eq_length hb,
    principal_zero_euler_eq_order ha, principal_zero_euler_eq_order hb,
    CurveLocalOrder.length_quotient_span_eq_addVal ha,
    CurveLocalOrder.length_quotient_span_eq_addVal hb]

end PiExponent.CurveZeroEuler

end

end OAI
end Source0025

section Source0026
/-
Modification notice for the LogTwo project.
Derived from openai/math (Apache-2.0), revision adc7f1241b42e322a6451854ab7e4b4c146bf78a.
Original source: lean/OAI/NumberTheory/PiExponent/Cohomology/FiniteZeroEuler.lean
Changes: Convert module/import declarations to the Lean 4.34 public module format.
See ../../../../../THIRD_PARTY_NOTICES.txt for provenance and the recorded changes.
-/




namespace OAI

noncomputable section
open scoped BigOperators
open AlgebraicGeometry PiExponentSeshadri.Geometry

namespace PiExponent.FiniteZeroEuler

theorem finrank_eq_sum_localizations
    (B : Type*) [CommRing B] [IsArtinianRing B]
    (F : Type*) [Field F] [Algebra F B] [Module.Finite F B]
    [Fintype (MaximalSpectrum B)] :
    Module.finrank F B = ∑ m : MaximalSpectrum B,
      Module.finrank F (Localization.AtPrime m.asIdeal) := by
  let : ∀ m : MaximalSpectrum B, Module.Finite F (Localization.AtPrime m.asIdeal) :=
    fun m => Module.Finite.of_surjective (IsScalarTower.toAlgHom F B
      (Localization.AtPrime m.asIdeal)).toLinearMap
      (IsArtinianRing.localization_surjective m.asIdeal.primeCompl _)
  have e := (MaximalSpectrum.toPiLocalizationEquiv B).restrictScalars F
  rw [e.toLinearEquiv.finrank_eq, Module.finrank_pi_fintype]

theorem finite_algebra_euler_eq_sum_local_lengths
    (B : Type) [CommRing B] [Algebra ℂ B] [Module.Finite ℂ B] (d : ℕ) :
    letI : IsArtinianRing B := IsArtinianRing.of_finite ℂ B
    letI : Fintype (MaximalSpectrum B) := Fintype.ofFinite _
    eulerCharacteristic (CurveZeroEuler.algebraStructureMap B) d
      (structureSheaf (Spec (CommRingCat.of B))) =
        ∑ m : MaximalSpectrum B,
          ((Module.length (Localization.AtPrime m.asIdeal)
            (Localization.AtPrime m.asIdeal)).toNat : ℤ) := by
  let : IsArtinianRing B := IsArtinianRing.of_finite ℂ B
  let : Fintype (MaximalSpectrum B) := Fintype.ofFinite _
  let : IsNoetherianRing B := isNoetherian_of_tower ℂ (inferInstance : IsNoetherian ℂ B)
  rw [CurveZeroEuler.affine_algebra_eulerCharacteristic,
    finrank_eq_sum_localizations B ℂ, Nat.cast_sum]
  apply Finset.sum_congr rfl
  intro m _
  let : Module.Finite ℂ (Localization.AtPrime m.asIdeal) :=
    Module.Finite.of_surjective (IsScalarTower.toAlgHom ℂ B
      (Localization.AtPrime m.asIdeal)).toLinearMap
      (IsArtinianRing.localization_surjective m.asIdeal.primeCompl _)
  have h := PiExponentJets.W24.ring_length_eq_finrank_of_augmentation
    (CurveLocalOrder.residueAugmentation ℂ (Localization.AtPrime m.asIdeal))
    (CurveLocalOrder.residueAugmentation_algebraMap ℂ (Localization.AtPrime m.asIdeal))
  rw [h]
  simp

end PiExponent.FiniteZeroEuler

end

end OAI
end Source0026

section Source0027
/-
Modification notice for the LogTwo project.
Derived from openai/math (Apache-2.0), revision adc7f1241b42e322a6451854ab7e4b4c146bf78a.
Original source: lean/OAI/NumberTheory/PiExponent/Geometry/FiniteCurveZeros.lean
Changes: Convert module/import declarations to the Lean 4.34 public module format.
See ../../../../../THIRD_PARTY_NOTICES.txt for provenance and the recorded changes.
-/




namespace OAI

noncomputable section

namespace PiExponentSeshadri.Geometry

section
open AlgebraicGeometry CategoryTheory TopologicalSpace
variable {K : Type} [Field K] {X Y : Scheme}

lemma proper_finite_scheme_isFinite (f : X ⟶ Y) [IsProper f] [Finite X] : IsFinite f := by
  let : LocallyQuasiFinite f := .of_finite_preimage_singleton f (fun _ => Set.toFinite _)
  exact .of_isProper_of_locallyQuasiFinite f

lemma proper_finite_scheme_isAffine (f : X ⟶ Spec (CommRingCat.of K))
    [IsProper f] [Finite X] : IsAffine X := by
  let : IsFinite f := proper_finite_scheme_isFinite f
  exact isAffine_of_isAffineHom f

lemma proper_finite_functions (f : X ⟶ Spec (CommRingCat.of K))
    [IsProper f] [Finite X] :
    let _ : Algebra K Γ(X,⊤) :=
      (f.appTop.hom.comp (Scheme.ΓSpecIso (CommRingCat.of K)).inv.hom).toAlgebra
    FiniteDimensional K Γ(X,⊤) := by
  let : IsFinite f := proper_finite_scheme_isFinite f
  dsimp only
  exact f.finite_appTop.comp (RingHom.Finite.of_surjective
    (Scheme.ΓSpecIso (CommRingCat.of K)).inv.hom (by
      exact (Scheme.ΓSpecIso (CommRingCat.of K)).symm.commRingCatIsoToRingEquiv.surjective))

lemma proper_finite_germ_surjective (f : X ⟶ Spec (CommRingCat.of K))
    [IsProper f] [Finite X] (x : X) :
    Function.Surjective (X.presheaf.germ ⊤ x trivial) := by
  let : IsAffine X := proper_finite_scheme_isAffine f
  let : Algebra K Γ(X,⊤) :=
    (f.appTop.hom.comp (Scheme.ΓSpecIso (CommRingCat.of K)).inv.hom).toAlgebra
  let : FiniteDimensional K Γ(X,⊤) := proper_finite_functions f
  let : IsArtinianRing Γ(X,⊤) := IsArtinianRing.of_finite K Γ(X,⊤)
  let : Algebra Γ(X,⊤) (X.presheaf.stalk x) :=
    TopCat.Presheaf.algebra_section_stalk X.presheaf (⟨x,trivial⟩ : (⊤ : X.Opens))
  let p : PrimeSpectrum Γ(X,⊤) := (isAffineOpen_top X).isoSpec.hom ⟨x,trivial⟩
  let : IsLocalization.AtPrime (X.presheaf.stalk x) p.asIdeal :=
    (isAffineOpen_top X).isLocalization_stalk ⟨x,trivial⟩
  exact IsArtinianRing.localization_surjective p.asIdeal.primeCompl (X.presheaf.stalk x)

theorem proper_finite_stalk_finrank_le (f : X ⟶ Spec (CommRingCat.of K))
    [IsProper f] [Finite X] (x : X) :
    let _ : Algebra K Γ(X,⊤) :=
      (f.appTop.hom.comp (Scheme.ΓSpecIso (CommRingCat.of K)).inv.hom).toAlgebra
    let _ : Algebra Γ(X,⊤) (X.presheaf.stalk x) :=
      TopCat.Presheaf.algebra_section_stalk X.presheaf (⟨x,trivial⟩ : (⊤ : X.Opens))
    let _ : Algebra K (X.presheaf.stalk x) :=
      ((algebraMap Γ(X,⊤) (X.presheaf.stalk x)).comp
        (f.appTop.hom.comp (Scheme.ΓSpecIso (CommRingCat.of K)).inv.hom)).toAlgebra
    FiniteDimensional K (X.presheaf.stalk x) ∧
      Module.finrank K (X.presheaf.stalk x) ≤ Module.finrank K Γ(X,⊤) := by
  dsimp only
  let : Algebra K Γ(X,⊤) :=
    (f.appTop.hom.comp (Scheme.ΓSpecIso (CommRingCat.of K)).inv.hom).toAlgebra
  let : Algebra Γ(X,⊤) (X.presheaf.stalk x) :=
    TopCat.Presheaf.algebra_section_stalk X.presheaf (⟨x,trivial⟩ : (⊤ : X.Opens))
  let : Algebra K (X.presheaf.stalk x) :=
    ((algebraMap Γ(X,⊤) (X.presheaf.stalk x)).comp
      (f.appTop.hom.comp (Scheme.ΓSpecIso (CommRingCat.of K)).inv.hom)).toAlgebra
  let : IsScalarTower K Γ(X,⊤) (X.presheaf.stalk x) := IsScalarTower.of_algebraMap_eq' rfl
  let : FiniteDimensional K Γ(X,⊤) := proper_finite_functions f
  let φ := (IsScalarTower.toAlgHom K Γ(X,⊤) (X.presheaf.stalk x)).toLinearMap
  have hφ : Function.Surjective φ := proper_finite_germ_surjective f x
  exact ⟨Module.Finite.of_surjective φ hφ, φ.finrank_le_finrank_of_surjective hφ⟩

end

section
open TopologicalSpace Set

variable {X : Type*} [TopologicalSpace X] [T0Space X] [IrreducibleSpace X]

lemma proper_irreducible_closed_subsingleton
    (hd : topologicalKrullDim X ≤ 1) {Z : Set X} (hZ : IsClosed Z)
    (hi : IsIrreducible Z) (hp : Z ≠ Set.univ) : Z.Subsingleton := by
  let C : IrreducibleCloseds X := ⟨Z, hi, hZ⟩
  let T : IrreducibleCloseds X := ⟨Set.univ, IrreducibleSpace.isIrreducible_univ X, isClosed_univ⟩
  have hmin : IsMin C := by
    rcases Order.krullDim_le_one_iff.mp hd C with hm | hm
    · exact hm
    · have he : C = T := le_antisymm (Set.subset_univ _) (hm (Set.subset_univ _))
      exact (hp (congrArg SetLike.coe he)).elim
  have hg (x : X) (hx : x ∈ Z) : IsGenericPoint x Z := by
    let D : IrreducibleCloseds X :=
      ⟨closure {x}, isIrreducible_singleton.closure, isClosed_closure⟩
    have hle : D ≤ C := closure_minimal (Set.singleton_subset_iff.mpr hx) hZ
    have he : D = C := le_antisymm hle (hmin hle)
    exact congrArg SetLike.coe he
  intro x hx y hy
  exact (hg x hx).eq (hg y hy)

theorem proper_closed_finite_of_dimension_one [NoetherianSpace X]
    (hd : topologicalKrullDim X ≤ 1) {Z : Set X} (hZ : IsClosed Z)
    (hp : Z ≠ Set.univ) : Z.Finite := by
  obtain ⟨F, hF, hFc, hFi, hZF⟩ :=
    NoetherianSpace.exists_finite_set_isClosed_irreducible hZ
  rw [hZF]
  apply hF.sUnion
  intro C hC
  apply Set.Subsingleton.finite
  apply proper_irreducible_closed_subsingleton hd (hFc C hC) (hFi C hC)
  intro hc
  apply hp
  apply Set.eq_univ_of_univ_subset
  rw [hZF]
  exact hc ▸ Set.subset_sUnion_of_mem hC

open AlgebraicGeometry in

theorem integral_curve_proper_closed_finite (C : Scheme)
    [IsIntegral C] [IsNoetherian C] (hd : topologicalKrullDim C = 1)
    {Z : Set C} (hZ : IsClosed Z) (hp : Z ≠ Set.univ) : Z.Finite :=
  proper_closed_finite_of_dimension_one hd.le hZ hp

end

section
open AlgebraicGeometry CategoryTheory TopologicalSpace
variable {K : Type} [Field K] {X : Scheme}

theorem finite_subscheme_of_curve [IsIntegral X]
    (f : X ⟶ Spec (CommRingCat.of K)) [IsProper f]
    (hd : topologicalKrullDim X ≤ 1) (I : X.IdealSheafData) (hI : I ≠ ⊥) :
    Finite I.subscheme := by
  let : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace f
  let : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian f
  let : IsNoetherian X := ⟨⟩
  have hp : (I.support : Set X) ≠ Set.univ := by
    intro he
    apply hI
    exact Scheme.IdealSheafData.support_eq_top_iff.mp (SetLike.coe_injective he)
  have hf := proper_closed_finite_of_dimension_one hd I.support.isClosed hp
  have hr : (Set.range I.subschemeι).Finite := I.range_subschemeι ▸ hf
  let : Finite (Set.range I.subschemeι) := hr.to_subtype
  exact Finite.of_injective (fun x : I.subscheme =>
    (⟨I.subschemeι x, ⟨x,rfl⟩⟩ : Set.range I.subschemeι))
    (fun a b h => I.subschemeι.isEmbedding.injective (congrArg (fun z : Set.range I.subschemeι => (z : X)) h))

theorem curve_subscheme_isFinite [IsIntegral X]
    (f : X ⟶ Spec (CommRingCat.of K)) [IsProper f]
    (hd : topologicalKrullDim X ≤ 1) (I : X.IdealSheafData) (hI : I ≠ ⊥) :
    IsFinite (I.subschemeι ≫ f) := by
  let : Finite I.subscheme := finite_subscheme_of_curve f hd I hI
  exact proper_finite_scheme_isFinite (I.subschemeι ≫ f)

abbrev structuralStalkAlgebra (f : X ⟶ Spec (CommRingCat.of K)) (x : X) :
    Algebra K (X.presheaf.stalk x) :=
  ((X.presheaf.germ ⊤ x trivial).hom.comp
    (f.appTop.hom.comp (Scheme.ΓSpecIso (CommRingCat.of K)).inv.hom)).toAlgebra

theorem proper_finite_finrank_eq_sum_stalks (f : X ⟶ Spec (CommRingCat.of K))
    [IsProper f] [Fintype X] :
    let _ : Algebra K Γ(X,⊤) :=
      (f.appTop.hom.comp (Scheme.ΓSpecIso (CommRingCat.of K)).inv.hom).toAlgebra
    Module.finrank K Γ(X,⊤) = ∑ x : X,
      let _ := structuralStalkAlgebra f x
      Module.finrank K (X.presheaf.stalk x) := by
  classical
  dsimp only
  let : IsAffine X := proper_finite_scheme_isAffine f
  let : Algebra K Γ(X,⊤) :=
    (f.appTop.hom.comp (Scheme.ΓSpecIso (CommRingCat.of K)).inv.hom).toAlgebra
  let : FiniteDimensional K Γ(X,⊤) := proper_finite_functions f
  let : IsArtinianRing Γ(X,⊤) := IsArtinianRing.of_finite K Γ(X,⊤)
  let : Fintype (MaximalSpectrum Γ(X,⊤)) := Fintype.ofFinite _
  let e : X ≃ MaximalSpectrum Γ(X,⊤) :=
    (Equiv.Set.univ X).symm.trans ((isAffineOpen_top X).isoSpec.hom.homeomorph.toEquiv.trans
      IsArtinianRing.primeSpectrumEquivMaximalSpectrum)
  rw [PiExponent.FiniteZeroEuler.finrank_eq_sum_localizations Γ(X,⊤) K, ← e.sum_comp]
  apply Finset.sum_congr rfl
  intro x _
  let : Algebra Γ(X,⊤) (X.presheaf.stalk x) :=
    TopCat.Presheaf.algebra_section_stalk X.presheaf (⟨x,trivial⟩ : (⊤ : X.Opens))
  let : Algebra K (X.presheaf.stalk x) := structuralStalkAlgebra f x
  let : IsScalarTower K Γ(X,⊤) (X.presheaf.stalk x) := IsScalarTower.of_algebraMap_eq' rfl
  let : IsLocalization.AtPrime (X.presheaf.stalk x) (e x).asIdeal :=
    (isAffineOpen_top X).isLocalization_stalk ⟨x,trivial⟩
  exact ((IsLocalization.algEquiv (e x).asIdeal.primeCompl
    (Localization.AtPrime (e x).asIdeal) (X.presheaf.stalk x)).restrictScalars K).toLinearEquiv.finrank_eq

end

open AlgebraicGeometry CategoryTheory
variable {X : Scheme.{0}}

theorem proper_finite_euler (f : X ⟶ Spec (CommRingCat.of ℂ))
    [IsProper f] [Finite X] (d : ℕ) :
    eulerCharacteristic f d (structureSheaf X) =
      let _ : Algebra ℂ Γ(X,⊤) := (baseScalars f).toAlgebra
      (Module.finrank ℂ Γ(X,⊤) : ℤ) := by
  let : IsAffine X := proper_finite_scheme_isAffine f
  let : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian f
  let : IsNoetherian X := ⟨⟩
  let L : LineBundle X := ⟨structureSheaf X, fun x =>
    ⟨⊤, trivial, ⟨Scheme.Modules.restrictUnitIso (⊤ : X.Opens).ι⟩⟩⟩
  let : (structureSheaf X).IsQuasicoherent :=
    PiExponent.GeometrySupport.LineBundleCoherent.modulePow_isQuasicoherent L 0
  exact affine_eulerCharacteristic f (structureSheaf X) d

theorem proper_finite_euler_eq_sum_stalk_finrank
    (f : X ⟶ Spec (CommRingCat.of ℂ)) [IsProper f] [Fintype X] (d : ℕ) :
    eulerCharacteristic f d (structureSheaf X) = ∑ x : X,
      letI := structuralStalkAlgebra f x
      (Module.finrank ℂ (X.presheaf.stalk x) : ℤ) := by
  rw [proper_finite_euler]
  dsimp only
  have h := proper_finite_finrank_eq_sum_stalks f
  dsimp only at h
  exact_mod_cast h

theorem proper_finite_euler_eq_sum_stalk_lengths
    (f : X ⟶ Spec (CommRingCat.of ℂ)) [IsProper f] [Fintype X] (d : ℕ) :
    eulerCharacteristic f d (structureSheaf X) = ∑ x : X,
      ((Module.length (X.presheaf.stalk x) (X.presheaf.stalk x)).toNat : ℤ) := by
  rw [proper_finite_euler_eq_sum_stalk_finrank]
  apply Finset.sum_congr rfl
  intro x _
  let : Algebra ℂ Γ(X, ⊤) := (baseScalars f).toAlgebra
  let : Algebra Γ(X, ⊤) (X.presheaf.stalk x) :=
    TopCat.Presheaf.algebra_section_stalk X.presheaf (⟨x, trivial⟩ : (⊤ : X.Opens))
  let : Algebra ℂ (X.presheaf.stalk x) := structuralStalkAlgebra f x
  let : IsScalarTower ℂ Γ(X, ⊤) (X.presheaf.stalk x) :=
    IsScalarTower.of_algebraMap_eq' rfl
  let : Module.Finite ℂ Γ(X, ⊤) := proper_finite_functions f
  let φ := (IsScalarTower.toAlgHom ℂ Γ(X, ⊤) (X.presheaf.stalk x)).toLinearMap
  let : Module.Finite ℂ (X.presheaf.stalk x) :=
    Module.Finite.of_surjective φ (proper_finite_germ_surjective f x)
  have h := PiExponentJets.W24.ring_length_eq_finrank_of_augmentation
    (PiExponent.CurveLocalOrder.residueAugmentation ℂ (X.presheaf.stalk x))
    (PiExponent.CurveLocalOrder.residueAugmentation_algebraMap ℂ (X.presheaf.stalk x))
  rw [h]
  simp

end PiExponentSeshadri.Geometry

end

end OAI
end Source0027

section Source0028
/-
Modification notice for the LogTwo project.
Derived from openai/math (Apache-2.0), revision adc7f1241b42e322a6451854ab7e4b4c146bf78a.
Original source: lean/OAI/NumberTheory/PiExponent/Cohomology/FiniteSupportCohomology.lean
Changes: Convert module/import declarations to the Lean 4.34 public module format.
See ../../../../../THIRD_PARTY_NOTICES.txt for provenance and the recorded changes.
-/




namespace OAI

noncomputable section

namespace PiExponentSeshadri.FiniteSupport

section
open CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite AlgebraicGeometry
lemma discrete_restriction_surjective {X : TopCat.{0}} [DiscreteTopology X]
    (F : X.Sheaf AddCommGrpCat.{0}) {U V : Opens X} (i : V ⟶ U) :
    Function.Surjective (F.obj.map i.op) := by
  classical
  intro s
  let W : Opens X := ⟨(U : Set X) \ V, isOpen_discrete _⟩
  let D : Bool → Opens X := fun b => if b then V else W
  let e : ∀ b, D b ⟶ U := fun b => homOfLE (by
    cases b
    · exact fun x hx => hx.1
    · exact i.le)
  have hcover : U ≤ ⨆ b, D b := by
    intro x hx
    by_cases hV : x ∈ V
    · exact Opens.mem_iSup.mpr ⟨true,hV⟩
    · exact Opens.mem_iSup.mpr ⟨false,hx,hV⟩
  let t : ∀ b, F.obj.obj (op (D b)) := fun b => match b with
    | true => s
    | false => 0
  have hc : TopCat.Presheaf.IsCompatible F.obj D t := by
    intro b c
    cases b <;> cases c
    · rfl
    · have h : D false ⊓ D true = ⊥ := by
        ext x
        change ((x ∈ U ∧ x ∉ V) ∧ x ∈ V) ↔ False
        tauto
      let : Subsingleton (F.obj.obj (op (D false ⊓ D true))) :=
        AddCommGrpCat.subsingleton_of_isZero (F.isTerminalOfEqEmpty h).isZero
      exact Subsingleton.elim _ _
    · have h : D true ⊓ D false = ⊥ := by
        ext x
        change (x ∈ V ∧ x ∈ U ∧ x ∉ V) ↔ False
        tauto
      let : Subsingleton (F.obj.obj (op (D true ⊓ D false))) :=
        AddCommGrpCat.subsingleton_of_isZero (F.isTerminalOfEqEmpty h).isZero
      exact Subsingleton.elim _ _
    · rfl
  obtain ⟨a,ha,_⟩ := F.existsUnique_gluing' D U e hcover t hc
  exact ⟨a,ha true⟩

lemma discrete_flasque {X : TopCat.{0}} [DiscreteTopology X]
    (F : X.Sheaf AddCommGrpCat.{0}) : F.IsFlasque where
  epi i := (AddCommGrpCat.epi_iff_surjective _).mpr
    (discrete_restriction_surjective F i.unop)

variable {X Y : Scheme.{0}}

lemma proper_finite_discrete (p : X ⟶ Spec (CommRingCat.of ℂ))
    [IsProper p] [Finite X] : DiscreteTopology X := by
  let : IsFinite p := Geometry.proper_finite_scheme_isFinite p
  have he : p ⁻¹' ({⟨⊥, Ideal.isPrime_bot⟩} : Set (Spec (CommRingCat.of ℂ))) = Set.univ := by
    ext x
    simp only [Set.mem_preimage, Set.mem_univ, iff_true]
    exact Subsingleton.elim _ _
  have h := p.isDiscrete_preimage_singleton (⟨⊥, Ideal.isPrime_bot⟩ : PrimeSpectrum ℂ)
  rw [he] at h
  exact isDiscrete_univ_iff.mp h

lemma pushforward_flasque (f : X ⟶ Y) [DiscreteTopology X] (M : X.Modules) :
    TopCat.Sheaf.IsFlasque ((SheafOfModules.toSheaf Y.ringCatSheaf).obj
      ((Scheme.Modules.pushforward f).obj M)) where
  epi i := by
    apply (AddCommGrpCat.epi_iff_surjective _).mpr
    exact discrete_restriction_surjective
      ((SheafOfModules.toSheaf X.ringCatSheaf).obj M)
      ((Opens.map f.base).map i.unop)

theorem finite_pushforward_ext_zero (p : X ⟶ Spec (CommRingCat.of ℂ))
    [IsProper p] [Finite X] (f : X ⟶ Y) (M : X.Modules) (n : ℕ)
    (z : Geometry.cohomology ((Scheme.Modules.pushforward f).obj M) (n+1)) : z = 0 := by
  let : DiscreteTopology X := proper_finite_discrete p
  let := pushforward_flasque f M
  exact FlasqueCohomology.flasque_ext_zero Y.ringCatSheaf n _ z

def pushforwardUnitSections (f : X ⟶ Y) (g : Y ⟶ Spec (CommRingCat.of ℂ)) :
    let _ : Module ℂ Γ((Scheme.Modules.pushforward f).obj (Geometry.structureSheaf X),⊤) :=
      Module.compHom _ (Geometry.baseScalars g)
    let _ : Algebra ℂ Γ(X,⊤) := (Geometry.baseScalars (f ≫ g)).toAlgebra
    Γ((Scheme.Modules.pushforward f).obj (Geometry.structureSheaf X),⊤) ≃ₗ[ℂ] Γ(X,⊤) := by
  dsimp only
  letI : Module ℂ Γ((Scheme.Modules.pushforward f).obj (Geometry.structureSheaf X),⊤) :=
    Module.compHom _ (Geometry.baseScalars g)
  letI : Algebra ℂ Γ(X,⊤) := (Geometry.baseScalars (f ≫ g)).toAlgebra
  refine { Equiv.refl _ with map_add' := fun _ _ => rfl, map_smul' := ?_ }
  intro r a
  change Γ(X,⊤) at a
  change (f.appTop) (Geometry.baseScalars g r) * a = Geometry.baseScalars (f ≫ g) r * a
  congr 1

theorem finite_pushforward_euler (f : X ⟶ Y) (g : Y ⟶ Spec (CommRingCat.of ℂ))
    [IsProper (f ≫ g)] [Finite X] (d : ℕ) :
    Geometry.eulerCharacteristic g d
      ((Scheme.Modules.pushforward f).obj (Geometry.structureSheaf X)) =
      let _ : Algebra ℂ Γ(X,⊤) := (Geometry.baseScalars (f ≫ g)).toAlgebra
      (Module.finrank ℂ Γ(X,⊤) : ℤ) := by
  let M := (Scheme.Modules.pushforward f).obj (Geometry.structureSheaf X)
  unfold Geometry.eulerCharacteristic
  rw [Finset.sum_eq_single 0]
  · simp only [pow_zero, one_mul, Geometry.cohomologyDimension_zero]
    let : Module ℂ Γ(M,⊤) := Module.compHom _ (Geometry.baseScalars g)
    let : Algebra ℂ Γ(X,⊤) := (Geometry.baseScalars (f ≫ g)).toAlgebra
    exact_mod_cast (pushforwardUnitSections f g).finrank_eq
  · intro n hn hn0
    obtain ⟨m,rfl⟩ := Nat.exists_eq_succ_of_ne_zero hn0
    have : Subsingleton (Geometry.cohomology M (m+1)) :=
      ⟨fun x y => (finite_pushforward_ext_zero (f ≫ g) f _ m x).trans
        (finite_pushforward_ext_zero (f ≫ g) f _ m y).symm⟩
    simp [Geometry.cohomologyDimension, Module.finrank_zero_of_subsingleton]
  · simp

end

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry PiExponentSeshadri.Geometry
variable {X Y : Scheme.{0}}

theorem finite_pushforward_finiteDimensional (f : X ⟶ Y)
    (g : Y ⟶ Spec (CommRingCat.of ℂ)) [IsProper (f ≫ g)] [Finite X] (n : ℕ) :
    let M := (Scheme.Modules.pushforward f).obj (structureSheaf X)
    let _ := Module.compHom (cohomology M n) (baseScalars g)
    FiniteDimensional ℂ (cohomology M n) := by
  let M := (Scheme.Modules.pushforward f).obj (structureSheaf X)
  let := Module.compHom (cohomology M n) (baseScalars g)
  cases n with
  | zero =>
    let : Module ℂ Γ(M,⊤) := Module.compHom _ (baseScalars g)
    let : Algebra ℂ Γ(X,⊤) := (baseScalars (f ≫ g)).toAlgebra
    let : FiniteDimensional ℂ Γ(X,⊤) := proper_finite_functions (f ≫ g)
    let e := (cohomologyZeroSections g M).trans (pushforwardUnitSections f g)
    exact Module.Finite.of_surjective e.symm.toLinearMap e.symm.surjective
  | succ n =>
    let : Subsingleton (cohomology M (n+1)) :=
      ⟨fun x y => (finite_pushforward_ext_zero (f ≫ g) f _ n x).trans
        (finite_pushforward_ext_zero (f ≫ g) f _ n y).symm⟩
    infer_instance

end PiExponentSeshadri.FiniteSupport

end

end OAI
end Source0028

section Source0029
/-
Modification notice for the LogTwo project.
Derived from openai/math (Apache-2.0), revision adc7f1241b42e322a6451854ab7e4b4c146bf78a.
Original source: lean/OAI/NumberTheory/PiExponent/Cohomology/FiniteLineEuler.lean
Changes: Convert module/import declarations to the Lean 4.34 public module format.
See ../../../../../THIRD_PARTY_NOTICES.txt for provenance and the recorded changes.
-/




namespace OAI

noncomputable section

namespace PiExponentSeshadri.Geometry
open AlgebraicGeometry CategoryTheory TopologicalSpace
variable {X : Scheme.{0}}

def overFrame {M : X.Modules} {U : X.Opens}
    (e : M.restrict U.ι ≅ structureSheaf U.toScheme) :
    M.over U ≅ SheafOfModules.unit (X.ringCatSheaf.over U) :=
  (Scheme.Modules.overEquiv U).fullyFaithfulFunctor.preimageIso
    ((Scheme.Modules.overFunctorEquiv U).app M ≪≫ e ≪≫
      (Opens.sheafOfModulesEquivOverUnit U X.ringCatSheaf).symm)
end PiExponentSeshadri.Geometry

namespace PiExponentSeshadri.FiniteSupport

section
open CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite AlgebraicGeometry
open PiExponentSeshadri.Geometry
variable {X : Scheme.{0}} [DiscreteTopology X]

def pointOpen (x : X) : X.Opens := ⟨{x}, isOpen_discrete _⟩

lemma pointOpen_basis : Opens.IsBasis (Set.range (pointOpen (X := X))) := by
  apply Opens.isBasis_iff_nbhd.mpr
  intro U x hx
  exact ⟨pointOpen x, ⟨x,rfl⟩, rfl, fun y hy => by cases hy; exact hx⟩

def pointFrame (L : LineBundle X) (x : X) :
    L.sheaf.val.obj (op (pointOpen x)) ≅
      (structureSheaf X).val.obj (op (pointOpen x)) := by
  let U := (L.locallyRankOne x).choose
  have hx := (L.locallyRankOne x).choose_spec.1
  let e := (L.locallyRankOne x).choose_spec.2.some
  let h : pointOpen x ≤ U := fun y hy => by cases hy; exact hx
  let e' := overFrame e
  exact (SheafOfModules.evaluation (X.ringCatSheaf.over U) (op (Over.mk (homOfLE h)))).mapIso e'

theorem lineBundle_trivial (L : LineBundle X) : Nonempty (L.sheaf ≅ structureSheaf X) := by
  classical
  let F : TopCat.Sheaf AddCommGrpCat.{0} X.toTopCat :=
    (SheafOfModules.toSheaf.{0} X.ringCatSheaf).obj L.sheaf
  let B := pointOpen (X := X)
  let t : ∀ x, Γ(L.sheaf,B x) := fun x => (pointFrame L x).inv (1 : Γ(X,B x))
  have hc : TopCat.Presheaf.IsCompatible F.obj B t := by
    intro x y
    by_cases h : x = y
    · subst y; rfl
    · have he : B x ⊓ B y = ⊥ := by
        ext z
        change (z = x ∧ z = y) ↔ False
        constructor
        · rintro ⟨rfl,h'⟩; exact h h'
        · tauto
      let : Subsingleton (F.obj.obj (op (B x ⊓ B y))) :=
        AddCommGrpCat.subsingleton_of_isZero (F.isTerminalOfEqEmpty he).isZero
      exact Subsingleton.elim _ _
  have hcover : (⊤ : X.Opens) ≤ ⨆ x, B x := by
    intro x _
    exact Opens.mem_iSup.mpr ⟨x,rfl⟩
  obtain ⟨a,ha,_⟩ := F.existsUnique_gluing' B ⊤ (fun _ => homOfLE le_top) hcover t hc
  let s : structureSheaf X ⟶ L.sheaf :=
    (FlasqueCohomology.globalHomEquiv X.ringCatSheaf L.sheaf).symm a
  have hs (x : X) : s.val.app (op (B x)) = (pointFrame L x).inv := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro r
    change Γ(X,B x) at r
    have hs1 : s.val.app (op (B x)) (1 : Γ(X,B x)) = t x := by
      have htop : s.app ⊤ (1 : Γ(X,⊤)) = a :=
        (FlasqueCohomology.globalHomEquiv X.ringCatSheaf L.sheaf).apply_symm_apply a
      have hn := CategoryTheory.congr_fun (s.mapPresheaf.naturality
        (homOfLE (show B x ≤ ⊤ from le_top)).op) (1 : Γ(X,⊤))
      change s.app (B x) (X.presheaf.map (homOfLE le_top).op 1) =
        L.sheaf.presheaf.map (homOfLE le_top).op (s.app ⊤ (1 : Γ(X,⊤))) at hn
      have hax : L.sheaf.presheaf.map (homOfLE (show B x ≤ ⊤ from le_top)).op a = t x := ha x
      have hn' : s.app (B x) (1 : Γ(X,B x)) =
          L.sheaf.presheaf.map (homOfLE le_top).op a := by
        simpa only [map_one, htop] using hn
      exact hn'.trans hax
    let : Module Γ(X,B x) (L.sheaf.val.obj (op (B x))) :=
      (L.sheaf.val.obj (op (B x))).isModule
    calc
      s.val.app (op (B x)) r = r • s.val.app (op (B x)) (1 : Γ(X,B x)) := by
        exact (congrArg (s.val.app (op (B x))) (mul_one r).symm).trans
          ((s.val.app (op (B x))).hom.map_smul r (1 : Γ(X,B x)))
      _ = r • (pointFrame L x).inv (1 : Γ(X,B x)) := by rw [hs1]
      _ = (pointFrame L x).inv r := by
        exact ((pointFrame L x).inv.hom.map_smul r (1 : Γ(X,B x))).symm.trans
          (congrArg (pointFrame L x).inv (mul_one r))
  have hiso : IsIso ((SheafOfModules.toSheaf.{0} X.ringCatSheaf).map s) := by
    apply TopCat.Sheaf.isIso_iff_isIso_basis pointOpen_basis
    intro x
    change IsIso ((forget₂ (ModuleCat _) AddCommGrpCat).map (s.val.app (op (B x))))
    rw [hs]
    infer_instance
  let : Mono s := (SheafOfModules.toSheaf.{0} X.ringCatSheaf).mono_of_mono_map inferInstance
  let : Epi s := (SheafOfModules.toSheaf.{0} X.ringCatSheaf).epi_of_epi_map inferInstance
  let : IsIso s := isIso_of_mono_of_epi s
  exact ⟨(asIso s).symm⟩

end

open CategoryTheory AlgebraicGeometry PiExponentSeshadri.Geometry
variable {X Y : Scheme.{0}}

theorem finite_line_pushforward_euler (f : X ⟶ Y)
    (g : Y ⟶ Spec (CommRingCat.of ℂ)) [IsProper (f ≫ g)] [Finite X]
    (L : LineBundle X) (d : ℕ) :
    eulerCharacteristic g d ((Scheme.Modules.pushforward f).obj L.sheaf) =
      let _ : Algebra ℂ Γ(X,⊤) := (baseScalars (f ≫ g)).toAlgebra
      (Module.finrank ℂ Γ(X,⊤) : ℤ) := by
  let : DiscreteTopology X := proper_finite_discrete (f ≫ g)
  obtain ⟨e⟩ := lineBundle_trivial L
  rw [eulerCharacteristic_iso g ((Scheme.Modules.pushforward f).mapIso e) d]
  exact finite_pushforward_euler f g d

theorem finite_line_pushforward_finiteDimensional (f : X ⟶ Y)
    (g : Y ⟶ Spec (CommRingCat.of ℂ)) [IsProper (f ≫ g)] [Finite X]
    (L : LineBundle X) (n : ℕ) :
    let M := (Scheme.Modules.pushforward f).obj L.sheaf
    let _ := Module.compHom (cohomology M n) (baseScalars g)
    FiniteDimensional ℂ (cohomology M n) := by
  let : DiscreteTopology X := proper_finite_discrete (f ≫ g)
  obtain ⟨e⟩ := lineBundle_trivial L
  let M := (Scheme.Modules.pushforward f).obj L.sheaf
  let N := (Scheme.Modules.pushforward f).obj (structureSheaf X)
  let := Module.compHom (cohomology M n) (baseScalars g)
  let := Module.compHom (cohomology N n) (baseScalars g)
  let : FiniteDimensional ℂ (cohomology N n) := finite_pushforward_finiteDimensional f g n
  exact Module.Finite.of_surjective
    (cohomologyIso g ((Scheme.Modules.pushforward f).mapIso e) n).symm.toLinearMap
    (cohomologyIso g ((Scheme.Modules.pushforward f).mapIso e) n).symm.surjective

theorem finite_line_euler_eq_sum_stalks (f : X ⟶ Y)
    (g : Y ⟶ Spec (CommRingCat.of ℂ)) [IsProper (f ≫ g)] [Fintype X]
    (L : LineBundle X) (d : ℕ) :
    eulerCharacteristic g d ((Scheme.Modules.pushforward f).obj L.sheaf) =
      ∑ x : X, let _ := structuralStalkAlgebra (f ≫ g) x
        (Module.finrank ℂ (X.presheaf.stalk x) : ℤ) := by
  rw [finite_line_pushforward_euler]
  dsimp only
  have h := proper_finite_finrank_eq_sum_stalks (f ≫ g)
  dsimp only at h
  exact_mod_cast h

theorem finite_line_euler_eq_sum_stalk_lengths (f : X ⟶ Y)
    (g : Y ⟶ Spec (CommRingCat.of ℂ)) [IsProper (f ≫ g)] [Fintype X]
    (L : LineBundle X) (d : ℕ) :
    eulerCharacteristic g d ((Scheme.Modules.pushforward f).obj L.sheaf) =
      ∑ x : X, ((Module.length (X.presheaf.stalk x) (X.presheaf.stalk x)).toNat : ℤ) := by
  calc
    _ = eulerCharacteristic (f ≫ g) d (structureSheaf X) :=
      (finite_line_pushforward_euler f g L d).trans (proper_finite_euler (f ≫ g) d).symm
    _ = _ := proper_finite_euler_eq_sum_stalk_lengths (f ≫ g) d

end PiExponentSeshadri.FiniteSupport

end

end OAI
end Source0029

section Source0030
/-
Modification notice for the LogTwo project.
Derived from openai/math (Apache-2.0), revision adc7f1241b42e322a6451854ab7e4b4c146bf78a.
Original source: lean/OAI/NumberTheory/PiExponent/Approximation/OpenPullbackUnit.lean
Changes: Convert module/import declarations to the Lean 4.34 public module format.
See ../../../../../THIRD_PARTY_NOTICES.txt for provenance and the recorded changes.
-/
end Source0030

section Source0031
/-
Modification notice for the LogTwo project.
Derived from openai/math (Apache-2.0), revision adc7f1241b42e322a6451854ab7e4b4c146bf78a.
Original source: lean/OAI/NumberTheory/PiExponent/Approximation/LineClosedUnit.lean
Changes: Convert module/import declarations to the Lean 4.34 public module format.
See ../../../../../THIRD_PARTY_NOTICES.txt for provenance and the recorded changes.
-/




namespace OAI


namespace PiExponentSeshadri.LineClosedUnit
noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite
open PiExponentSeshadri.Geometry PiExponentSeshadri.Frames
variable {X Y : Scheme.{0}} (f : X ⟶ Y)

def map (L : LineBundle Y) : L.sheaf ⟶
    (Scheme.Modules.pushforward f).obj ((Scheme.Modules.pullback f).obj L.sheaf) :=
  (Scheme.Modules.pullbackPushforwardAdjunction f).unit.app L.sheaf

def frame (L : LineBundle Y) (U : Y.Opens) (e : L.sheaf.restrict U.ι ≅ O U.toScheme) :
    ((Scheme.Modules.pushforward f).obj ((Scheme.Modules.pullback f).obj L.sheaf)).restrict U.ι ≅
      (Scheme.Modules.pushforward (f ∣_ U)).obj (O (f ⁻¹ᵁ U).toScheme) :=
  OpenBaseChange.iso f U _ ≪≫
    (Scheme.Modules.pushforward (f ∣_ U)).mapIso
      ((OpenBaseChange.leftSquare f U).app L.sheaf).symm ≪≫
    (Scheme.Modules.pushforward (f ∣_ U)).mapIso (pullbackFrame (f ∣_ U) e)

lemma framed_map (L : LineBundle Y) (U : Y.Opens)
    (e : L.sheaf.restrict U.ι ≅ O U.toScheme) :
    e.inv ≫ (Scheme.Modules.restrictFunctor U.ι).map (map f L) ≫
      (frame f L U e).hom = IdealModule.structureMap (f ∣_ U) := by
  dsimp only [map, IdealModule.structureMap]
  have hu := OpenBaseChange.unit_compatibility f U L.sheaf
  have hn := (Scheme.Modules.pullbackPushforwardAdjunction (f ∣_ U)).unit_naturality e.hom
  have hb := pullbackUnit_adjunction (f ∣_ U)
  rw [Adjunction.homEquiv_unit] at hb
  dsimp only [frame, Iso.trans_hom, Functor.mapIso_hom, Iso.symm_hom]
  simp only [← Category.assoc]
  rw [Category.assoc e.inv, hu]
  simp only [Category.assoc]
  have hec : (OpenBaseChange.leftSquare f U).hom.app L.sheaf ≫
      ((OpenBaseChange.leftSquare f U).app L.sheaf).inv = 𝟙 _ :=
    ((OpenBaseChange.leftSquare f U).app L.sheaf).hom_inv_id
  rw [← Functor.map_comp_assoc, hec]
  erw [CategoryTheory.Functor.map_id, Category.id_comp]
  change e.inv ≫ (Scheme.Modules.pullbackPushforwardAdjunction (f ∣_ U)).unit.app _ ≫
    (Scheme.Modules.pushforward (f ∣_ U)).map
      ((Scheme.Modules.pullback (f ∣_ U)).map e.hom ≫ (pullbackUnitIso (f ∣_ U)).hom) = _
  rw [Functor.map_comp]
  have hn' := congrArg (fun t => e.inv ≫ t ≫
    (Scheme.Modules.pushforward (f ∣_ U)).map (pullbackUnitIso (f ∣_ U)).hom) hn
  simp only [Category.assoc, hb] at hn'
  exact hn'.trans (e.inv_hom_id_assoc _)

theorem epi [IsClosedImmersion f] (L : LineBundle Y) : Epi (map f L) := by
  apply PiExponent.CoherentTwist.epi_of_local
  intro y
  obtain ⟨U,hy,⟨e⟩⟩ := L.locallyRankOne y
  refine ⟨U,hy,?_⟩
  have hg : Epi (IdealModule.structureMap (f ∣_ U)) := IdealModule.structureMap_epi _
  have he := framed_map f L U e
  have : Epi (e.inv ≫ (Scheme.Modules.restrictFunctor U.ι).map (map f L) ≫
    (frame f L U e).hom) := he.symm ▸ hg
  have h1 : Epi ((Scheme.Modules.restrictFunctor U.ι).map (map f L) ≫
      (frame f L U e).hom) := epi_of_epi e.inv _
  exact (epi_comp_iff_of_isIso _ _).mp h1

end
end PiExponentSeshadri.LineClosedUnit

end OAI
end Source0031

section Source0032
/-
Modification notice for the LogTwo project.
Derived from openai/math (Apache-2.0), revision adc7f1241b42e322a6451854ab7e4b4c146bf78a.
Original source: lean/OAI/NumberTheory/PiExponent/Geometry/PrincipalCartierSequence.lean
Changes: Convert module/import declarations to the Lean 4.34 public module format.
See ../../../../../THIRD_PARTY_NOTICES.txt for provenance and the recorded changes.
-/




namespace OAI

namespace PiExponentSeshadri.PrincipalSequence
noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite
open PiExponentSeshadri.Geometry PiExponentSeshadri.Frames
variable {X Y : Scheme.{0}}

lemma scalarEnd_eq_multiply (r : Γ(X,⊤)) : scalarEnd r = IdealModule.multiply r := rfl

lemma end_regular_of_mono (a : O X ⟶ O X) [Mono a] : IsLeftRegular (endValue a) := by
  have hinj : Function.Injective (a.val.app (op ⊤)) :=
    PresheafOfModules.injective_of_mono
      ((Scheme.Modules.toPresheafOfModules X).map a) (op ⊤)
  intro r s hrs
  apply hinj
  change a.app ⊤ r = a.app ⊤ s
  rw [end_apply a ⊤ r, end_apply a ⊤ s]
  change r * endValue a = s * endValue a
  simpa only [mul_comm] using hrs

theorem exact [IsAffine Y] (f : X ⟶ Y) [IsClosedImmersion f]
    (a : O Y ⟶ O Y) [Mono a]
    (h : f.ker.ideal ⟨⊤,isAffineOpen_top Y⟩ = Ideal.span {endValue a}) :
    ∃ hz : a ≫ IdealModule.structureMap f = 0,
      (ShortComplex.mk a (IdealModule.structureMap f) hz).ShortExact := by
  let r := endValue a
  have hr : f.appTop r = 0 := by
    change r ∈ RingHom.ker f.appTop.hom
    erw [← Scheme.Hom.ker_apply f ⟨⊤,isAffineOpen_top Y⟩, h]
    exact Ideal.subset_span (Set.mem_singleton r)
  have hreg : IsLeftRegular r := end_regular_of_mono a
  have hprincipal (U : Y.affineOpens) : f.ker.ideal U =
      Ideal.span {Y.presheaf.map (homOfLE (show U.1 ≤ ⊤ from le_top)).op r} := by
    rw [← f.ker.map_ideal (U := U) (V := ⟨⊤,isAffineOpen_top Y⟩) (by change U.1 ≤ ⊤; exact le_top), h]
    simp only [Ideal.map_span, Set.image_singleton]
    rfl
  have hi : IsIso (IdealModule.equationToIdeal f r hr) :=
    IdealModule.isIso_equationToIdeal f r hr hprincipal
      (IdealModule.restriction_regular r hreg)
  have he : a = IdealModule.multiply r := by
    rw [← scalarEnd_eq_multiply]
    apply endValue_injective
    simp [r]
  have hz : a ≫ IdealModule.structureMap f = 0 := by
    rw [he]
    exact IdealModule.multiply_structure_zero f r hr
  refine ⟨hz,?_⟩
  let S := ShortComplex.mk a (IdealModule.structureMap f) hz
  let T := ShortComplex.mk (IdealModule.inclusion f) (IdealModule.structureMap f)
    (kernel.condition (IdealModule.structureMap f))
  let e : S ≅ T := ShortComplex.isoMk (@asIso Y.Modules _ _ _ (IdealModule.equationToIdeal f r hr) hi)
    (Iso.refl _) (Iso.refl _) (by
      change IdealModule.equationToIdeal f r hr ≫ IdealModule.inclusion f = a ≫ 𝟙 _
      exact (IdealModule.equationToIdeal_inclusion f r hr).trans
        (he.symm.trans (Category.comp_id a).symm)) (by exact (Category.id_comp _).trans (Category.comp_id _).symm)
  have hg : Epi (IdealModule.structureMap f) := IdealModule.structureMap_epi f
  exact { exact := ShortComplex.exact_of_iso e.symm (ShortComplex.exact_kernel _), epi_g := hg }

end
end PiExponentSeshadri.PrincipalSequence

end OAI
end Source0032

section Source0033
/-
Modification notice for the LogTwo project.
Derived from openai/math (Apache-2.0), revision adc7f1241b42e322a6451854ab7e4b4c146bf78a.
Original source: lean/OAI/NumberTheory/PiExponent/Geometry/CartierSequence.lean
Changes: Convert module/import declarations to the Lean 4.34 public module format.
See ../../../../../THIRD_PARTY_NOTICES.txt for provenance and the recorded changes.
-/




namespace OAI


namespace PiExponentSeshadri.CartierSequence
noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite
open PiExponentSeshadri.Geometry PiExponentSeshadri.Frames
variable {X : Scheme.{0}}

lemma chart_topIso_naturality {Y : Scheme.{0}} (j : Y ⟶ X) (U : X.Opens) :
    U.topIso.hom ≫ j.app U ≫ (j ⁻¹ᵁ U).topIso.inv = (j ∣_ U).appTop := by
  have H := (arrowResLEAppIso j U (j ⁻¹ᵁ U) le_rfl).hom.w
  change U.topIso.hom ≫ j.appLE U (j ⁻¹ᵁ U) le_rfl =
    (j.resLE U (j ⁻¹ᵁ U) le_rfl).appTop ≫ (j ⁻¹ᵁ U).topIso.hom at H
  rw [Scheme.Hom.resLE_eq_morphismRestrict, Scheme.Hom.appLE_eq_app] at H
  apply (cancel_mono (j ⁻¹ᵁ U).topIso.hom).mp
  simpa only [Category.assoc, Iso.inv_hom_id, Category.comp_id] using H

lemma restriction_principal (_p : X ⟶ Spec (CommRingCat.of ℂ))
    (I : X.IdealSheafData) (U : X.affineOpens) (r : Γ(U.1.toScheme,⊤))
    (hI : I.ideal U = Ideal.span {U.1.topIso.hom r}) :
    (I.subschemeι ∣_ U.1).ker.ideal ⟨⊤,isAffineOpen_top U.1.toScheme⟩ =
      Ideal.span {r} := by
  ext z
  rw [Scheme.Hom.ker_apply,RingHom.mem_ker]
  change (I.subschemeι ∣_ U.1).appTop z = 0 ↔ z ∈ Ideal.span {r}
  have hz : (I.subschemeι ∣_ U.1).appTop z = 0 ↔
      U.1.topIso.hom z ∈ I.ideal U := by
    rw [← chart_topIso_naturality]
    simp only [CommRingCat.comp_apply]
    rw [← I.ker_subschemeι_app U]
    change (I.subschemeι ⁻¹ᵁ U.1).topIso.inv
      (I.subschemeι.app U.1 (U.1.topIso.hom z)) = 0 ↔
      I.subschemeι.app U.1 (U.1.topIso.hom z) = 0
    exact map_eq_zero_iff _ (ConcreteCategory.bijective_of_isIso
      (I.subschemeι ⁻¹ᵁ U.1).topIso.inv).injective
  rw [hz,hI,Ideal.mem_span_singleton,Ideal.mem_span_singleton]
  constructor
  · rintro ⟨a,ha⟩
    refine ⟨U.1.topIso.inv a,?_⟩
    have h := congrArg U.1.topIso.inv ha
    simpa only [map_mul,U.1.topIso.hom_inv_id_apply] using h
  · rintro ⟨a,ha⟩
    refine ⟨U.1.topIso.hom a,?_⟩
    simpa only [map_mul] using congrArg U.1.topIso.hom ha

theorem exact (p : X ⟶ Spec (CommRingCat.of ℂ))
    (M N : LineBundle X) (φ : M.sheaf ⟶ N.sheaf) [Mono φ]
    (I : X.IdealSheafData)
    (heq : ∀ x : X, ∃ U : X.affineOpens, x ∈ U.1 ∧
      ∃ e : M.sheaf.restrict U.1.ι ≅ O U.1.toScheme,
      ∃ d : N.sheaf.restrict U.1.ι ≅ O U.1.toScheme,
        I.ideal U = Ideal.span (Set.singleton (U.1.topIso.hom
          (endValue (e.inv ≫ (Scheme.Modules.restrictFunctor U.1.ι).map φ ≫ d.hom))))) :
    ∃ hz : φ ≫ LineClosedUnit.map I.subschemeι N = 0,
      (ShortComplex.mk φ (LineClosedUnit.map I.subschemeι N) hz).ShortExact := by
  have local_exact (U : X.affineOpens)
      (e : M.sheaf.restrict U.1.ι ≅ O U.1.toScheme)
      (d : N.sheaf.restrict U.1.ι ≅ O U.1.toScheme)
      (hI : I.ideal U = Ideal.span (Set.singleton (U.1.topIso.hom
        (endValue (e.inv ≫ (Scheme.Modules.restrictFunctor U.1.ι).map φ ≫ d.hom))))) :=
    PrincipalSequence.exact (I.subschemeι ∣_ U.1)
      (e.inv ≫ (Scheme.Modules.restrictFunctor U.1.ι).map φ ≫ d.hom)
      (restriction_principal p I U _ hI)
  have hz : φ ≫ LineClosedUnit.map I.subschemeι N = 0 := by
    apply PiExponent.CoherentTwist.eq_zero_of_local
    intro x
    obtain ⟨U,hx,e,d,hI⟩ := heq x
    obtain ⟨hzero,hex⟩ := local_exact U e d hI
    refine ⟨U.1,hx,?_⟩
    apply (cancel_epi e.inv).mp
    apply (cancel_mono (LineClosedUnit.frame I.subschemeι N U.1 d).hom).mp
    rw [Functor.map_comp,comp_zero,zero_comp]
    rw [Category.assoc,Category.assoc]
    rw [← d.hom_inv_id_assoc ((Scheme.Modules.restrictFunctor U.1.ι).map
      (LineClosedUnit.map I.subschemeι N))]
    simp only [Category.assoc]
    rw [LineClosedUnit.framed_map]
    simpa only [Category.assoc] using! hzero
  refine ⟨hz,{ exact := ?_, epi_g := LineClosedUnit.epi _ _ }⟩
  apply PiExponent.CoherentTwist.exact_of_local
  intro x
  obtain ⟨U,hx,e,d,hI⟩ := heq x
  obtain ⟨hzero,hex⟩ := local_exact U e d hI
  refine ⟨U.1,hx,?_⟩
  let S := (ShortComplex.mk φ (LineClosedUnit.map I.subschemeι N) hz).map
    (Scheme.Modules.restrictFunctor U.1.ι)
  let T := ShortComplex.mk (e.inv ≫ (Scheme.Modules.restrictFunctor U.1.ι).map φ ≫ d.hom)
    (IdealModule.structureMap (I.subschemeι ∣_ U.1)) hzero
  let ee : S ≅ T := ShortComplex.isoMk e d (LineClosedUnit.frame I.subschemeι N U.1 d)
    (by simp [S,T]) (by
      change d.hom ≫ IdealModule.structureMap (I.subschemeι ∣_ U.1) =
        (Scheme.Modules.restrictFunctor U.1.ι).map (LineClosedUnit.map I.subschemeι N) ≫ _
      rw [← LineClosedUnit.framed_map I.subschemeι N U.1 d]
      exact d.hom_inv_id_assoc _)
  exact ShortComplex.exact_of_iso ee.symm hex.exact

end
end PiExponentSeshadri.CartierSequence

end OAI
end Source0033

section Source0034
/-
Modification notice for the LogTwo project.
Derived from openai/math (Apache-2.0), revision adc7f1241b42e322a6451854ab7e4b4c146bf78a.
Original source: lean/OAI/NumberTheory/PiExponent/Geometry/CartierDegreeLength.lean
Changes: Convert module/import declarations to the Lean 4.34 public module format.
See ../../../../../THIRD_PARTY_NOTICES.txt for provenance and the recorded changes.
-/




namespace OAI

noncomputable section
open CategoryTheory AlgebraicGeometry TopologicalSpace
open PiExponentSeshadri.Geometry PiExponentSeshadri.Frames

namespace PiExponent.CartierDegreeLength


theorem cartier_euler_difference_eq_sum_local_lengths
    {X : Scheme.{0}} [IsIntegral X]
    (p : X ⟶ Spec (CommRingCat.of ℂ)) [IsProper p]
    (hd : topologicalKrullDim X ≤ 1)
    (M N : LineBundle X) (φ : M.sheaf ⟶ N.sheaf) [Mono φ]
    (I : X.IdealSheafData) (hI : I ≠ ⊥)
    (heq : ∀ x : X, ∃ U : X.affineOpens, x ∈ U.1 ∧
      ∃ e : M.sheaf.restrict U.1.ι ≅ O U.1.toScheme,
      ∃ d : N.sheaf.restrict U.1.ι ≅ O U.1.toScheme,
        I.ideal U = Ideal.span (Set.singleton (U.1.topIso.hom
          (endValue (e.inv ≫ (Scheme.Modules.restrictFunctor U.1.ι).map φ ≫ d.hom)))))
    (hfiniteM : ∀ n ≤ 1, letI := Module.compHom (cohomology M.sheaf n) (baseScalars p)
      FiniteDimensional ℂ (cohomology M.sheaf n))
    (hfiniteN : ∀ n ≤ 1, letI := Module.compHom (cohomology N.sheaf n) (baseScalars p)
      FiniteDimensional ℂ (cohomology N.sheaf n))
    [Subsingleton (cohomology M.sheaf 2)] :
    letI : Finite I.subscheme := finite_subscheme_of_curve p hd I hI
    letI : Fintype I.subscheme := Fintype.ofFinite _
    eulerCharacteristic p 1 N.sheaf - eulerCharacteristic p 1 M.sheaf =
      ∑ x : I.subscheme,
        ((Module.length (I.subscheme.presheaf.stalk x)
          (I.subscheme.presheaf.stalk x)).toNat : ℤ) := by
  let : Finite I.subscheme := finite_subscheme_of_curve p hd I hI
  let : Fintype I.subscheme := Fintype.ofFinite _
  obtain ⟨hz, hseq⟩ := PiExponentSeshadri.CartierSequence.exact p M N φ I heq
  have hfiniteZ (n : ℕ) (_hn : n ≤ 1) :=
    PiExponentSeshadri.FiniteSupport.finite_line_pushforward_finiteDimensional
      I.subschemeι p (N.pullback I.subschemeι) n
  have h := eulerCharacteristic_add p hseq 1 hfiniteM hfiniteN hfiniteZ
  have hdiff : eulerCharacteristic p 1 N.sheaf - eulerCharacteristic p 1 M.sheaf =
      eulerCharacteristic p 1
        ((Scheme.Modules.pushforward I.subschemeι).obj
          ((Scheme.Modules.pullback I.subschemeι).obj N.sheaf)) := by
    exact sub_eq_iff_eq_add.mpr (by simpa [add_comm] using h)
  exact hdiff.trans
    (PiExponentSeshadri.FiniteSupport.finite_line_euler_eq_sum_stalk_lengths
      I.subschemeι p (N.pullback I.subschemeι) 1)

end PiExponent.CartierDegreeLength

end

end OAI
end Source0034

section Source0035
/-
Modification notice for the LogTwo project.
Derived from openai/math (Apache-2.0), revision adc7f1241b42e322a6451854ab7e4b4c146bf78a.
Original source: lean/OAI/NumberTheory/PiExponent/Approximation/TwistSectionScalars.lean
Changes: Convert module/import declarations to the Lean 4.34 public module format.
See ../../../../../THIRD_PARTY_NOTICES.txt for provenance and the recorded changes.
-/




namespace OAI

namespace PiExponentSeshadri.Geometry
noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
open PiExponentSeshadri.TensorPure PiExponentSeshadri.Frames
variable {X : Scheme}

lemma moduleSectionMultiplyRight_pure (M : X.Modules) {L : X.Modules}
    (s : structureSheaf X ⟶ L) (U : X.Opens) (m : Γ(M,U)) :
    (moduleSectionMultiplyRight M s).app U m =
      pure M L U m (s.app U (1 : Γ(X,U))) := by
  have h : (moduleTensorRightUnit M).hom.app U
      (pure M (structureSheaf X) U m (1 : Γ(X,U))) = m := by
    erw [right_unit_pure, one_smul]
  have hi : (moduleTensorRightUnit M).inv.app U m =
      pure M (structureSheaf X) U m (1 : Γ(X,U)) := by
    calc
      _ = (moduleTensorRightUnit M).inv.app U
          ((moduleTensorRightUnit M).hom.app U
            (pure M (structureSheaf X) U m (1 : Γ(X,U)))) := congrArg _ h.symm
      _ = _ := congrArg (fun q => q.app U
        (pure M (structureSheaf X) U m (1 : Γ(X,U)))) (moduleTensorRightUnit M).hom_inv_id
  change (moduleTensorMap (𝟙 M) s).app U ((moduleTensorRightUnit M).inv.app U m) = _
  erw [hi, TensorPure.map_pure]
  rfl

lemma moduleTensorFrame_pure (M : X.Modules) {L : X.Modules}
    (e : L ≅ structureSheaf X) (U : X.Opens) (m : Γ(M,U)) (l : Γ(L,U)) :
    (moduleTensorFrame M e).hom.app U (pure M L U m l) =
      (show Γ(X,U) from e.hom.app U l) • m := by
  change (moduleTensorRightUnit M).hom.app U
    ((moduleTensorMap (𝟙 M) e.hom).app U (pure M L U m l)) = _
  have h := TensorPure.map_pure (𝟙 M) e.hom U m l
  exact (congrArg (fun t => (moduleTensorRightUnit M).hom.app U t) h).trans
    (right_unit_pure M U m (e.hom.app U l))

lemma moduleSectionMultiplyRight_frame (M : X.Modules) {L : X.Modules}
    (s : structureSheaf X ⟶ L) (e : L ≅ structureSheaf X)
    (U : X.Opens) (m : Γ(M,U)) :
    (moduleTensorFrame M e).hom.app U ((moduleSectionMultiplyRight M s).app U m) =
      X.presheaf.map (homOfLE (show U ≤ ⊤ from le_top)).op (coefficient e s) • m := by
  rw [moduleSectionMultiplyRight_pure, moduleTensorFrame_pure]
  exact congrArg (fun a : Γ(X,U) => a • m) (end_naturality (s ≫ e.hom) U)

lemma moduleSectionMultiplyRight_restrict_frame (M : X.Modules) {L : X.Modules}
    (s : structureSheaf X ⟶ L) (U : X.Opens)
    (e : L.restrict U.ι ≅ structureSheaf U.toScheme) (V : U.toScheme.Opens)
    (m : Γ(M,U.ι ''ᵁ V)) :
    ((moduleTensorRestrictFrame U L e).app M).hom.app V
      ((moduleSectionMultiplyRight M s).app (U.ι ''ᵁ V) m) =
      U.toScheme.presheaf.map (homOfLE (show V ≤ ⊤ from le_top)).op (coefficient e (restrictSection U.ι s)) •
        (show Γ(M.restrict U.ι,V) from m) := by
  change (moduleTensorFrame (M.restrict U.ι) e).hom.app V
    ((moduleTensorRestrict U M L).hom.app V
      ((moduleSectionMultiplyRight M s).app (U.ι ''ᵁ V) m)) = _
  have h₁ := moduleSectionMultiplyRight_pure M s (U.ι ''ᵁ V) m
  have h₂ := restrict_pure U M L V m (s.app (U.ι ''ᵁ V) (1 : Γ(X, U.ι ''ᵁ V)))
  have h₃ := moduleTensorFrame_pure (M.restrict U.ι) e V m
    (s.app (U.ι ''ᵁ V) (1 : Γ(X, U.ι ''ᵁ V)))
  refine ((congrArg (fun t => (moduleTensorFrame (M.restrict U.ι) e).hom.app V
      ((moduleTensorRestrict U M L).hom.app V t)) h₁).trans
    ((congrArg (fun t => (moduleTensorFrame (M.restrict U.ι) e).hom.app V t) h₂).trans h₃)).trans ?_
  have h := end_naturality (restrictSection U.ι s ≫ e.hom) V
  apply congrArg (fun a : Γ(U.toScheme,V) => a • (show Γ(M.restrict U.ι,V) from m))
  calc
    _ = (show Γ(U.toScheme,V) from e.hom.app V ((restrictSection U.ι s).app V
        (1 : Γ(U.toScheme,V)))) := by
      change e.hom.app V (s.app (U.ι ''ᵁ V) (1 : Γ(X,U.ι ''ᵁ V))) =
        e.hom.app V (s.app (U.ι ''ᵁ V) ((U.ι.appIso V).inv (1 : Γ(U.toScheme,V))))
      rw [show (U.ι.appIso V).inv (1 : Γ(U.toScheme,V)) =
        (1 : Γ(X,U.ι ''ᵁ V)) from (U.ι.appIso V).inv.hom.map_one]
    _ = _ := h

lemma moduleTwistForward_frame (L : LineBundle X)
    (s : structureSheaf X ⟶ L.sheaf) (U : X.Opens)
    (e : L.sheaf.restrict U.ι ≅ structureSheaf U.toScheme)
    (M : X.Modules) (V : U.toScheme.Opens) (n k : ℕ)
    (m : Γ((moduleTwistFunctor L n).obj M,U.ι ''ᵁ V)) :
    ((moduleTwistRestrictFrame L U e (n+k)).app M).hom.app V
      (((moduleTwistForward L s n k).app M).app (U.ι ''ᵁ V) m) =
      (U.toScheme.presheaf.map (homOfLE (show V ≤ ⊤ from le_top)).op
        (coefficient e (restrictSection U.ι s))) ^ k •
          ((moduleTwistRestrictFrame L U e n).app M).hom.app V m := by
  induction k with
  | zero => simp only [moduleTwistForward, NatTrans.id_app, pow_zero, one_smul]; rfl
  | succ k ih =>
    change ((moduleTwistRestrictFrame L U e (n+k)).app M).hom.app V
      (((moduleTensorRestrictFrame U L.sheaf e).app ((moduleTwistFunctor L (n+k)).obj M)).hom.app V
        ((moduleSectionMultiplyRight ((moduleTwistFunctor L (n+k)).obj M) s).app
          (U.ι ''ᵁ V) (((moduleTwistForward L s n k).app M).app (U.ι ''ᵁ V) m))) = _
    rw [moduleSectionMultiplyRight_restrict_frame, Scheme.Modules.Hom.app_smul,
      ih, smul_smul, pow_succ']

lemma moduleTwistSection_frame (L : LineBundle X)
    (s : structureSheaf X ⟶ L.sheaf) (U : X.Opens)
    (e : L.sheaf.restrict U.ι ≅ structureSheaf U.toScheme)
    (M : X.Modules) (V : U.toScheme.Opens) (n : ℕ) (m : Γ(M,U.ι ''ᵁ V)) :
    ((moduleTwistRestrictFrame L U e n).app M).hom.app V
      (((moduleTwistSection L s n).app M).app (U.ι ''ᵁ V) m) =
      (U.toScheme.presheaf.map (homOfLE (show V ≤ ⊤ from le_top)).op
        (coefficient e (restrictSection U.ι s))) ^ n •
          (show Γ(M.restrict U.ι,V) from m) := by
  induction n with
  | zero =>
      simp only [moduleTwistSection, moduleTwistRestrictFrame, NatTrans.id_app, pow_zero]
      exact (one_smul Γ(U.toScheme, V) (show Γ(M.restrict U.ι, V) from m)).symm
  | succ n ih =>
    change ((moduleTwistRestrictFrame L U e n).app M).hom.app V
      (((moduleTensorRestrictFrame U L.sheaf e).app ((moduleTwistFunctor L n).obj M)).hom.app V
        ((moduleSectionMultiplyRight ((moduleTwistFunctor L n).obj M) s).app
          (U.ι ''ᵁ V) (((moduleTwistSection L s n).app M).app (U.ι ''ᵁ V) m))) = _
    rw [moduleSectionMultiplyRight_restrict_frame, Scheme.Modules.Hom.app_smul,
      ih, smul_smul, pow_succ']

end
end PiExponentSeshadri.Geometry

end OAI
end Source0035

section Source0036
/-
Modification notice for the LogTwo project.
Derived from openai/math (Apache-2.0), revision adc7f1241b42e322a6451854ab7e4b4c146bf78a.
Original source: lean/OAI/NumberTheory/PiExponent/Approximation/TwistSectionClearing.lean
Changes: Convert module/import declarations to the Lean 4.34 public module format.
See ../../../../../THIRD_PARTY_NOTICES.txt for provenance and the recorded changes.
-/




namespace OAI

namespace PiExponent.TwistSectionClearing
noncomputable section
open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite
open PiExponentSeshadri.Geometry PiExponentSeshadri.Frames
open PiExponent.GlobalSectionClearing
variable {X : Scheme}

lemma iso_section_restrict_zero {P Q : X.Modules} (e : P ≅ Q) (V : X.Opens)
    (x : Γ(P,⊤)) (hx : P.presheaf.map (homOfLE (show V ≤ ⊤ from le_top)).op x = 0) :
    Q.presheaf.map (homOfLE (show V ≤ ⊤ from le_top)).op (e.hom.app ⊤ x) = 0 := by
  have h := CategoryTheory.congr_fun (e.hom.mapPresheaf.naturality
    (homOfLE (show V ≤ ⊤ from le_top)).op) x
  change e.hom.app V (P.presheaf.map (homOfLE le_top).op x) =
    Q.presheaf.map (homOfLE le_top).op (e.hom.app ⊤ x) at h
  rw [hx, map_zero] at h
  exact h.symm

lemma frame_local_input_zero (L : LineBundle X) (s : structureSheaf X ⟶ L.sheaf)
    (U : X.Opens) (e : L.sheaf.restrict U.ι ≅ structureSheaf U.toScheme)
    (P : X.Modules) (x : Γ(P,⊤))
    (hx : P.presheaf.map (homOfLE (show PiExponentSeshadri.SectionOpens.isoOpen s ≤ ⊤ from le_top)).op x = 0) :
    (P.restrict U.ι).presheaf.map
      (homOfLE (U.toScheme.basicOpen_le (coefficient e (restrictSection U.ι s)))).op
      (P.presheaf.map (homOfLE (show U.ι ''ᵁ (⊤ : U.toScheme.Opens) ≤ ⊤ from le_top)).op x) = 0 := by
  have hD : U.ι ''ᵁ U.toScheme.basicOpen (coefficient e (restrictSection U.ι s)) ≤
      PiExponentSeshadri.SectionOpens.isoOpen s := by
    rw [← preimage_isoOpen s U.ι e]
    exact U.ι.image_preimage_le _
  change openRestriction P (U.ι.image_mono
    (U.toScheme.basicOpen_le (coefficient e (restrictSection U.ι s))))
    (openRestriction P (show U.ι ''ᵁ (⊤ : U.toScheme.Opens) ≤ ⊤ from le_top) x) = 0
  erw [openRestriction_comp_apply]
  erw [← openRestriction_comp_apply P hD le_top x]
  change openRestriction P hD (P.presheaf.map (homOfLE le_top).op x) = 0
  rw [hx]
  exact map_zero (openRestriction P hD)

lemma section_zero_of_imageTop (P : X.Modules) (U : X.Opens) (x : Γ(P,⊤))
    (hx : P.presheaf.map (homOfLE (show U.ι ''ᵁ (⊤ : U.toScheme.Opens) ≤ ⊤ from le_top)).op x = 0) :
    P.presheaf.map (homOfLE (show U ≤ ⊤ from le_top)).op x = 0 :=
  openRestriction_zero_congr P U.ι_image_top _ _ _ hx

lemma iso_section_restrict_zero_on {P Q : X.Modules} (e : P ≅ Q)
    {V W : X.Opens} (hVW : V ≤ W) (x : Γ(P,W))
    (hx : P.presheaf.map (homOfLE hVW).op x = 0) :
    Q.presheaf.map (homOfLE hVW).op (e.hom.app W x) = 0 := by
  have h := CategoryTheory.congr_fun (e.hom.mapPresheaf.naturality (homOfLE hVW).op) x
  change e.hom.app V (P.presheaf.map (homOfLE hVW).op x) =
    Q.presheaf.map (homOfLE hVW).op (e.hom.app W x) at h
  rw [hx, map_zero] at h
  exact h.symm

lemma frame_local_input_zero_on (L : LineBundle X) (s : structureSheaf X ⟶ L.sheaf)
    (U : X.Opens) (e : L.sheaf.restrict U.ι ≅ structureSheaf U.toScheme)
    (P : X.Modules) (W : X.Opens) (V : U.toScheme.Opens) (hVW : U.ι ''ᵁ V ≤ W)
    (x : Γ(P,W))
    (hx : P.presheaf.map (homOfLE
      (show W ⊓ PiExponentSeshadri.SectionOpens.isoOpen s ≤ W from inf_le_left)).op x = 0) :
    (P.restrict U.ι).presheaf.map (homOfLE
      (show V ⊓ U.toScheme.basicOpen (coefficient e (restrictSection U.ι s)) ≤ V from inf_le_left)).op
      (P.presheaf.map (homOfLE hVW).op x) = 0 := by
  have hD : U.ι ''ᵁ (V ⊓ U.toScheme.basicOpen (coefficient e (restrictSection U.ι s))) ≤
      W ⊓ PiExponentSeshadri.SectionOpens.isoOpen s := by
    apply le_inf
    · exact (U.ι.image_mono inf_le_left).trans hVW
    · apply (U.ι.image_mono inf_le_right).trans
      rw [← preimage_isoOpen s U.ι e]
      exact U.ι.image_preimage_le _
  change openRestriction P (U.ι.image_mono
    (show V ⊓ U.toScheme.basicOpen (coefficient e (restrictSection U.ι s)) ≤ V from inf_le_left))
    (openRestriction P hVW x) = 0
  erw [openRestriction_comp_apply]
  erw [← openRestriction_comp_apply P hD inf_le_left x]
  change openRestriction P hD (P.presheaf.map (homOfLE inf_le_left).op x) = 0
  rw [hx]
  exact map_zero (openRestriction P hD)

theorem frame_twistForward_zero_on (L : LineBundle X)
    (s : structureSheaf X ⟶ L.sheaf) (U : X.Opens)
    (e : L.sheaf.restrict U.ι ≅ structureSheaf U.toScheme)
    (M : X.Modules) [M.IsQuasicoherent] (n : ℕ)
    (V : U.toScheme.Opens) (hV : IsCompact (V : Set U.toScheme))
    (x : Γ(((moduleTwistFunctor L n).obj M).restrict U.ι, V))
    (hx : (((moduleTwistFunctor L n).obj M).restrict U.ι).presheaf.map (homOfLE
      (show V ⊓ U.toScheme.basicOpen (coefficient e (restrictSection U.ι s)) ≤ V from inf_le_left)).op x = 0) :
    ∃ K : ℕ, ∀ k ≥ K,
      (((moduleTwistForward L s n k).app M).app (U.ι ''ᵁ V)) x = 0 := by
  let c := coefficient e (restrictSection U.ι s)
  let E := (moduleTwistRestrictFrame L U e n).app M
  have hz := iso_section_restrict_zero_on E
    (show V ⊓ U.toScheme.basicOpen c ≤ V from inf_le_left) x hx
  obtain ⟨K, hK⟩ := compact_open_section_zero (M.restrict U.ι) c V hV (E.hom.app V x) hz
  refine ⟨K, fun k hk => ?_⟩
  apply (ConcreteCategory.bijective_of_isIso
    (((moduleTwistRestrictFrame L U e (n+k)).app M).hom.app V)).injective
  refine (moduleTwistForward_frame L s U e M V n k x).trans ?_
  have hh := hK k hk
  change (OAI.PiExponent.GlobalSectionClearing.restrictScalar U.toScheme V (c ^ k)) • E.hom.app V x = 0 at hh
  rw [map_pow] at hh
  exact hh.trans (map_zero (((moduleTwistRestrictFrame L U e (n+k)).app M).hom.app V).hom).symm

lemma hom_section_restriction {P Q : X.Modules} (f : P ⟶ Q)
    {V W : X.Opens} (hVW : V ≤ W) (x : Γ(P,W)) :
    Q.presheaf.map (homOfLE hVW).op (f.app W x) =
      f.app V (P.presheaf.map (homOfLE hVW).op x) := by
  have h := CategoryTheory.congr_fun (f.mapPresheaf.naturality (homOfLE hVW).op) x
  exact h.symm

theorem frame_twistForward_ambient_zero [NoetherianSpace X] (L : LineBundle X)
    (s : structureSheaf X ⟶ L.sheaf) (U : X.Opens)
    (e : L.sheaf.restrict U.ι ≅ structureSheaf U.toScheme)
    (M : X.Modules) [M.IsQuasicoherent] (n : ℕ) (W : X.Opens)
    (x : Γ((moduleTwistFunctor L n).obj M, W))
    (hx : ((moduleTwistFunctor L n).obj M).presheaf.map (homOfLE
      (show W ⊓ PiExponentSeshadri.SectionOpens.isoOpen s ≤ W from inf_le_left)).op x = 0) :
    ∃ K : ℕ, ∀ k ≥ K,
      ((moduleTwistFunctor L (n+k)).obj M).presheaf.map
        (homOfLE (show U ⊓ W ≤ W from inf_le_right)).op
        (((moduleTwistForward L s n k).app M).app W x) = 0 := by
  let : NoetherianSpace U.toScheme := NoetherianSpace.set (U : Set X)
  let V := U.ι ⁻¹ᵁ W
  have hVW : U.ι ''ᵁ V ≤ W := U.ι.image_preimage_le W
  have hlocal := frame_local_input_zero_on L s U e ((moduleTwistFunctor L n).obj M) W V hVW x hx
  obtain ⟨K, hK⟩ := frame_twistForward_zero_on L s U e M n V
    (NoetherianSpace.isCompact _) _ hlocal
  refine ⟨K, fun k hk => ?_⟩
  have hh : ((moduleTwistFunctor L (n+k)).obj M).presheaf.map (homOfLE hVW).op
      (((moduleTwistForward L s n k).app M).app W x) = 0 := by
    rw [hom_section_restriction]
    exact hK k hk
  have he : U.ι ''ᵁ V = U ⊓ W := by
    dsimp only [V]
    rw [Scheme.Hom.image_preimage_eq_opensRange_inf, Scheme.Opens.opensRange_ι]
  exact openRestriction_zero_congr ((moduleTwistFunctor L (n+k)).obj M) he _ _ _ hh

theorem twistForward_section_zero [NoetherianSpace X] (L : LineBundle X)
    (s : structureSheaf X ⟶ L.sheaf) (M : X.Modules) [M.IsQuasicoherent]
    (n : ℕ) (W : X.Opens) (x : Γ((moduleTwistFunctor L n).obj M, W))
    (hx : ((moduleTwistFunctor L n).obj M).presheaf.map (homOfLE
      (show W ⊓ PiExponentSeshadri.SectionOpens.isoOpen s ≤ W from inf_le_left)).op x = 0) :
    ∃ K : ℕ, ∀ k ≥ K, ((moduleTwistForward L s n k).app M).app W x = 0 := by
  classical
  choose U hxU he using L.locallyRankOne
  let e (a : X) := Classical.choice (he a)
  have hcover : IsOpenCover U := by
    rw [IsOpenCover]
    apply top_unique
    intro a ha
    exact Opens.mem_iSup.mpr ⟨a, hxU a⟩
  obtain ⟨I, hI⟩ := hcover.exists_finite_of_compactSpace
  have hI' : (⨆ i : I, U i.val) = ⊤ := hI
  choose K hK using fun i : I => frame_twistForward_ambient_zero L s (U i.val)
    (e i.val) M n W x hx
  refine ⟨Finset.univ.sup K, fun k hk => ?_⟩
  let P := (moduleTwistFunctor L (n+k)).obj M
  apply TopCat.Sheaf.eq_of_locally_eq' ⟨P.presheaf, P.isSheaf⟩
    (fun i : I => U i.val ⊓ W) W (fun i => homOfLE inf_le_right)
    (by rw [← iSup_inf_eq, hI', top_inf_eq])
  intro i
  have hi := hK i k ((Finset.le_sup (f := K) (Finset.mem_univ i)).trans hk)
  change P.presheaf.map _ (((moduleTwistForward L s n k).app M).app W x) = P.presheaf.map _ 0
  rw [map_zero]
  exact hi

theorem twistSection_zero [NoetherianSpace X] (L : LineBundle X)
    (s : structureSheaf X ⟶ L.sheaf) (M : X.Modules) [M.IsQuasicoherent]
    (W : X.Opens) (x : Γ(M,W))
    (hx : M.presheaf.map (homOfLE
      (show W ⊓ PiExponentSeshadri.SectionOpens.isoOpen s ≤ W from inf_le_left)).op x = 0) :
    ∃ K : ℕ, ∀ k ≥ K, ((moduleTwistSection L s k).app M).app W x = 0 := by
  obtain ⟨K, hK⟩ := twistForward_section_zero L s M 0 W x hx
  refine ⟨K, fun k hk => ?_⟩
  have he := moduleTwistSection_add L s 0 k
  simp only [moduleTwistSection] at he
  have he' : moduleTwistSection L s (0+k) = moduleTwistForward L s 0 k :=
    he.trans (Category.id_comp _)
  have hh := (congrArg (fun t => (t.app M).app W x) he').trans (hK k hk)
  let P (j : ℕ) : Prop := ((moduleTwistSection L s j).app M).app W x = 0
  exact Eq.mp (congrArg P (Nat.zero_add k)) hh

end
end PiExponent.TwistSectionClearing

end OAI
end Source0036

#print axioms OAI.PiExponentSeshadri.CartierSequence.exact
#print axioms OAI.PiExponent.CartierDegreeLength.cartier_euler_difference_eq_sum_local_lengths
#print axioms OAI.PiExponent.TwistSectionClearing.frame_twistForward_zero_on

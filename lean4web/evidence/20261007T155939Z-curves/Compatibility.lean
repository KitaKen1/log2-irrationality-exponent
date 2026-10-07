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
Original source: lean/OAI/NumberTheory/PiExponent/Ampleness/BlowupIdeal.lean
Changes: Convert module/import declarations to the Lean 4.34 public module format.
See ../../../../../THIRD_PARTY_NOTICES.txt for provenance and the recorded changes.
-/




namespace OAI

noncomputable section

namespace PiExponentSeshadri

namespace Geometry
open CategoryTheory AlgebraicGeometry

def sectionImageIdeal {X : Scheme} (J : LineBundle X)
    (ι : J.sheaf ⟶ structureSheaf X) (U : X.Opens) : Ideal Γ(X, U) := by
  letI : Module Γ(X, U) (J.sheaf.val.obj (Opposite.op U)) :=
    (J.sheaf.val.obj (Opposite.op U)).isModule
  let φ : J.sheaf.val.obj (Opposite.op U) →ₗ[Γ(X, U)] Γ(X, U) :=
    (ι.val.app (Opposite.op U)).hom
  exact φ.range

def PresentsPullbackIdeal {X Y : Scheme} (I : X.IdealSheafData) (f : Y ⟶ X)
    (J : LineBundle Y) (ι : J.sheaf ⟶ structureSheaf Y) : Prop :=
  Mono ι ∧ ∀ (U : Y.affineOpens) (V : X.affineOpens)
    (e : U.1 ≤ f ⁻¹ᵁ V.1),
    sectionImageIdeal J ι U.1 = (I.ideal V).map (f.appLE V.1 U.1 e).hom

def InvertiblePullbackIdeal {X Y : Scheme} (I : X.IdealSheafData) (f : Y ⟶ X) : Prop :=
  ∃ (J : LineBundle Y) (ι : J.sheaf ⟶ structureSheaf Y), PresentsPullbackIdeal I f J ι

def IsBlowup {X B : Scheme} (I : X.IdealSheafData) (π : B ⟶ X) : Prop :=
  InvertiblePullbackIdeal I π ∧ ∀ (Y : Scheme) (f : Y ⟶ X),
    InvertiblePullbackIdeal I f → ∃! h : Y ⟶ B, h ≫ π = f

end Geometry

namespace IdealModule

section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
universe u
variable {X : Scheme.{u}}

def sectionFamily {M : X.Modules} (s : Γ(M, ⊤)) : M.sections where
  val U := M.presheaf.map (homOfLE (show U.unop ≤ ⊤ from le_top)).op s
  property {U V} i := by
    change (M.presheaf.map (homOfLE le_top).op ≫ M.presheaf.map i) s = _
    rw [← Functor.map_comp]
    rfl

def fromSection {M : X.Modules} (s : Γ(M, ⊤)) : unit X ⟶ M :=
  M.unitHomEquiv.symm (sectionFamily s)

@[simp] lemma fromSection_app {M : X.Modules} (s : Γ(M, ⊤))
    (U : X.Opens) (a : Γ(X, U)) :
    (fromSection s).val.app (op U) a = a • M.presheaf.map (homOfLE le_top).op s := rfl

lemma fromSection_inclusion_app {M : X.Modules} (g : M ⟶ unit X)
    (s : Γ(M, ⊤)) (r : Γ(X, ⊤)) (hs : g.val.app (op ⊤) s = r)
    (U : X.Opens) (a : Γ(X, U)) :
    g.val.app (op U) ((fromSection s).val.app (op U) a) =
      X.presheaf.map (homOfLE le_top).op r * a := by
  rw [fromSection_app]
  have hn := PresheafOfModules.naturality_apply g.val (homOfLE (show U ≤ ⊤ from le_top)).op s
  change g.val.app (op U) (M.presheaf.map (homOfLE le_top).op s) =
    X.presheaf.map (homOfLE le_top).op (g.val.app (op ⊤) s) at hn
  have he := ((g.val.app (op U)).hom).map_smul a (M.presheaf.map (homOfLE le_top).op s)
  change _ = a * (show Γ(X, U) from g.val.app (op U) (M.presheaf.map (homOfLE le_top).op s)) at he
  exact he.trans ((congrArg (fun b : Γ(X, U) => a * b)
    (hn.trans (congrArg (fun b : Γ(X, ⊤) => X.presheaf.map (homOfLE le_top).op b) hs))).trans
      (mul_comm _ _))

lemma isIso_fromSection {M : X.Modules} (g : M ⟶ unit X) [Mono g]
    (s : Γ(M, ⊤)) (r : Γ(X, ⊤)) (hs : g.val.app (op ⊤) s = r)
    (hprincipal : ∀ U : X.affineOpens,
      (g.val.app (op U.1)).hom.range = Ideal.span {X.presheaf.map (homOfLE le_top).op r})
    (hregular : ∀ U : X.affineOpens,
      IsLeftRegular (X.presheaf.map (homOfLE (show U.1 ≤ ⊤ from le_top)).op r)) :
    IsIso (fromSection s) := by
  apply isIso_of_affine_app
  intro U
  have hinj : Function.Injective (g.val.app (op U.1)) := by
    let : Mono g.val := inferInstanceAs (Mono ((Scheme.Modules.toPresheafOfModules X).map g))
    exact PresheafOfModules.injective_of_mono g.val (op U.1)
  apply (ConcreteCategory.isIso_iff_bijective _).mpr
  constructor
  · intro a b hab
    apply hregular U
    have he := congrArg (g.val.app (op U.1)) hab
    change g.val.app (op U.1) ((fromSection s).val.app (op U.1) a) =
      g.val.app (op U.1) ((fromSection s).val.app (op U.1) b) at he
    exact (fromSection_inclusion_app g s r hs U.1 a).symm.trans
      (he.trans (fromSection_inclusion_app g s r hs U.1 b))
  · intro y
    have hy : (show Γ(X, U.1) from g.val.app (op U.1) y) ∈
        Ideal.span {X.presheaf.map (homOfLE le_top).op r} := by
      rw [← hprincipal U]
      exact ⟨y, rfl⟩
    obtain ⟨a, ha⟩ := Ideal.mem_span_singleton.mp hy
    refine ⟨a, hinj ?_⟩
    exact (fromSection_inclusion_app g s r hs U.1 a).trans ha.symm

end

section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
universe u
variable {X Y : Scheme.{u}}

def restrictedInclusion (I : Y.IdealSheafData) (f : X ⟶ Y) [IsOpenImmersion f] :
    (closedModule I).restrict f ⟶ unit X :=
  (Scheme.Modules.restrictFunctor f).map (closedInclusion I) ≫
    (Scheme.Modules.restrictUnitIso f).hom

instance restrictedInclusion_mono (I : Y.IdealSheafData) (f : X ⟶ Y)
    [IsOpenImmersion f] : Mono (restrictedInclusion I f) := by
  let : Mono (closedInclusion I) := inferInstanceAs (Mono (inclusion I.subschemeι))
  let : Mono ((Scheme.Modules.restrictFunctor f).map (closedInclusion I)) :=
    PiExponentSeshadri.RestrictionExact.restriction_mono f (closedInclusion I)
  exact mono_comp' (C := X.Modules) inferInstance
    ⟨fun a b h => (Iso.cancel_iso_hom_right a b (Scheme.Modules.restrictUnitIso f)).mp h⟩

lemma restrictedInclusion_app (I : Y.IdealSheafData) (f : X ⟶ Y)
    [IsOpenImmersion f] (U : X.Opens) (s : Γ((closedModule I).restrict f, U)) :
    (restrictedInclusion I f).val.app (op U) s =
      (f.appIso U).hom ((closedInclusion I).val.app (op (f ''ᵁ U)) s) := rfl

lemma restricted_image (I : Y.IdealSheafData) (f : X ⟶ Y)
    [IsOpenImmersion f] (U : X.affineOpens) :
    ((restrictedInclusion I f).val.app (op U.1)).hom.range = (I.comap f).ideal U := by
  rw [I.ideal_comap_of_isOpenImmersion f U]
  ext r
  change Γ(X, U.1) at r
  change (∃ s, (restrictedInclusion I f).val.app (op U.1) s = r) ↔
    (f.appIso U.1).inv r ∈ I.ideal ⟨f ''ᵁ U.1, U.2.image_of_isOpenImmersion f⟩
  rw [← closed_image I ⟨f ''ᵁ U.1, U.2.image_of_isOpenImmersion f⟩]
  change (∃ s, _) ↔ ∃ s, (closedInclusion I).val.app (op (f ''ᵁ U.1)) s = (f.appIso U.1).inv r
  constructor
  · rintro ⟨s, hs⟩
    refine ⟨s, ?_⟩
    exact (congrArg (fun k : Γ(Y, f ''ᵁ U.1) ⟶ Γ(Y, f ''ᵁ U.1) => k ((closedInclusion I).val.app (op (f ''ᵁ U.1)) s))
      (f.appIso U.1).hom_inv_id).symm.trans
        (congrArg (fun z : Γ(X, U.1) => (f.appIso U.1).inv z)
          ((restrictedInclusion_app I f U.1 s).symm.trans hs))
  · rintro ⟨s, hs⟩
    refine ⟨s, ?_⟩
    exact (restrictedInclusion_app I f U.1 s).trans
      ((congrArg (fun z : Γ(Y, f ''ᵁ U.1) => (f.appIso U.1).hom z) hs).trans
        (congrArg (fun k : Γ(X, U.1) ⟶ Γ(X, U.1) => k r) (f.appIso U.1).inv_hom_id))

lemma frame_restriction (I : Y.IdealSheafData) (f : X ⟶ Y)
    [IsOpenImmersion f] [IsAffine X] (r : Γ(X, ⊤))
    (hprincipal : (I.comap f).ideal ⟨⊤, isAffineOpen_top X⟩ = Ideal.span {r})
    (hregular : IsLeftRegular r) :
    Nonempty ((closedModule I).restrict f ≅ unit X) := by
  have hr' : r ∈ (I.comap f).ideal ⟨⊤, isAffineOpen_top X⟩ := by
    rw [hprincipal]
    exact Ideal.subset_span (Set.mem_singleton r)
  have hr : r ∈ ((restrictedInclusion I f).val.app (op ⊤)).hom.range := by
    rw [restricted_image I f ⟨⊤, isAffineOpen_top X⟩]
    exact hr'
  obtain ⟨s, hs⟩ := hr
  have hi : IsIso (fromSection (M := (closedModule I).restrict f) s) := isIso_fromSection (restrictedInclusion I f) s r hs
    (fun U => ?_) (restriction_regular r hregular)
  · exact ⟨(asIso (fromSection (M := (closedModule I).restrict f) s)).symm⟩
  · rw [restricted_image I f U, ← (I.comap f).map_ideal (U := U)
      (V := ⟨⊤, isAffineOpen_top X⟩) (by change U.1 ≤ ⊤; exact le_top), hprincipal]
    simp only [Ideal.map_span, Set.image_singleton]
    rfl

end
open CategoryTheory AlgebraicGeometry
universe u
variable {X Y : Scheme.{u}}

def frameOnRange (M : Y.Modules) (f : X ⟶ Y) [IsOpenImmersion f]
    (e : M.restrict f ≅ unit X) : M.restrict f.opensRange.ι ≅ unit f.opensRange.toScheme :=
  ((Scheme.Modules.restrictFunctorCongr f.isoOpensRange_inv_comp).app M).symm ≪≫
    (Scheme.Modules.restrictFunctorComp f.isoOpensRange.inv f).app M ≪≫
    (Scheme.Modules.restrictFunctor f.isoOpensRange.inv).mapIso e ≪≫
    Scheme.Modules.restrictUnitIso f.isoOpensRange.inv

end IdealModule
namespace IdealPullback

section
open CategoryTheory AlgebraicGeometry
universe u
variable {X Y : Scheme.{u}} [IsAffine X] [IsAffine Y]

lemma map_top (J : X.IdealSheafData) (f : X ⟶ Y) :
    (J.map f).ideal ⟨⊤, isAffineOpen_top Y⟩ =
      (J.ideal ⟨⊤, isAffineOpen_top X⟩).comap f.appTop.hom :=
  J.ideal_map f ⟨⊤, isAffineOpen_top Y⟩ (isAffineOpen_top X)

lemma comap_top (I : Y.IdealSheafData) (f : X ⟶ Y) :
    (I.comap f).ideal ⟨⊤, isAffineOpen_top X⟩ =
      (I.ideal ⟨⊤, isAffineOpen_top Y⟩).map f.appTop.hom := by
  apply le_antisymm
  · let J : X.IdealSheafData := Scheme.IdealSheafData.ofIdealTop
      ((I.ideal ⟨⊤, isAffineOpen_top Y⟩).map f.appTop.hom)
    have h : I ≤ J.map f := by
      apply Scheme.IdealSheafData.le_of_isAffine
      rw [map_top]
      simpa [J] using Ideal.le_comap_map
    have hh := (Scheme.IdealSheafData.le_map_iff_comap_le.mp h) ⟨⊤, isAffineOpen_top X⟩
    simpa [J] using hh
  · rw [Ideal.map_le_iff_le_comap]
    have h := (I.le_map_comap f) ⟨⊤, isAffineOpen_top Y⟩
    rwa [map_top] at h

end
section
open CategoryTheory AlgebraicGeometry Opposite
universe u
variable {R S : Type u} [CommRing R] [CommRing S]

def specIdeal (I : Ideal R) : (Spec (CommRingCat.of R)).IdealSheafData :=
  Scheme.IdealSheafData.ofIdealTop (I.map (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom)

@[simp] lemma specIdeal_top (I : Ideal R) :
    (specIdeal I).ideal ⟨⊤, isAffineOpen_top _⟩ =
      I.map (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom := by
  simp [specIdeal]

lemma specIdeal_comap (I : Ideal R) (f : R →+* S) :
    (specIdeal I).comap (Spec.map (CommRingCat.ofHom f)) = specIdeal (I.map f) := by
  apply Scheme.IdealSheafData.ext_of_isAffine
  rw [comap_top, specIdeal_top, specIdeal_top, Ideal.map_map, Ideal.map_map]
  congr 1
  exact congrArg CommRingCat.Hom.hom (Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom f)).symm

end
open CategoryTheory AlgebraicGeometry
universe u
variable {X Y : Scheme.{u}}

lemma comap_ι_top (I : X.IdealSheafData) (U : X.affineOpens) :
    (I.comap U.1.ι).ideal ⟨⊤, isAffineOpen_top _⟩ =
      (I.ideal U).map U.1.topIso.inv.hom := by
  rw [I.ideal_comap_of_isOpenImmersion]
  simp only [Scheme.Opens.ι_appIso, Iso.refl_inv]
  exact (I.map_ideal (U := ⟨U.1.ι ''ᵁ ⊤, (isAffineOpen_top U.1.toScheme).image_of_isOpenImmersion U.1.ι⟩)
    (V := U) (show U.1.ι ''ᵁ ⊤ ≤ U.1 from U.1.ι_image_top.le)).symm

lemma comap_ideal (I : Y.IdealSheafData) (f : X ⟶ Y)
    (U : X.affineOpens) (V : Y.affineOpens) (e : U.1 ≤ f ⁻¹ᵁ V.1) :
    (I.comap f).ideal U = (I.ideal V).map (f.appLE V.1 U.1 e).hom := by
  suffices hh : ((I.comap f).ideal U).map U.1.topIso.inv.hom =
      ((I.ideal V).map (f.appLE V.1 U.1 e).hom).map U.1.topIso.inv.hom by
    have hh' := congrArg (Ideal.map U.1.topIso.hom.hom) hh
    simpa only [Ideal.map_map, ← CommRingCat.hom_comp, Iso.inv_hom_id, Iso.inv_hom_id_assoc, Category.assoc, Category.comp_id, CommRingCat.hom_id,
      Ideal.map_id] using hh'
  rw [← comap_ι_top, ← Scheme.IdealSheafData.comap_comp,
    ← Scheme.Hom.resLE_comp_ι f e, Scheme.IdealSheafData.comap_comp,
    comap_top, comap_ι_top, Ideal.map_map, Ideal.map_map]
  simp only [Scheme.Hom.appTop, Scheme.Hom.resLE_app_top, ← CommRingCat.hom_comp,
    Iso.inv_hom_id_assoc]

end IdealPullback
namespace InvertibleLocal

section
open CategoryTheory AlgebraicGeometry Opposite
open PiExponentSeshadri.Geometry
variable {X Y : Scheme} {I : X.IdealSheafData} {f : Y ⟶ X}
lemma invertible_of_local_equations
    (hf : ∀ y : Y, ∃ U : Y.affineOpens, y ∈ U.1 ∧
      ∃ r : Γ(U.1.toScheme, ⊤), IsRegular r ∧
      ((I.comap f).comap U.1.ι).ideal ⟨⊤, isAffineOpen_top _⟩ = Ideal.span {r}) :
    InvertiblePullbackIdeal I f := by
  let J : LineBundle Y := {
    sheaf := IdealModule.closedModule (I.comap f)
    locallyRankOne y := by
      obtain ⟨U, hyU, r, hr, hIr⟩ := hf y
      exact ⟨U.1, hyU, IdealModule.frame_restriction (I.comap f) U.1.ι r hIr hr.1⟩ }
  have : Mono (IdealModule.closedInclusion (I.comap f)) :=
    inferInstanceAs (Mono (IdealModule.inclusion (I.comap f).subschemeι))
  refine ⟨J, IdealModule.closedInclusion (I.comap f), this, ?_⟩
  intro U V e
  change ((IdealModule.closedInclusion (I.comap f)).val.app (op U.1)).hom.range = _
  rw [IdealModule.closed_image]
  exact IdealPullback.comap_ideal I f U V e

end
open CategoryTheory AlgebraicGeometry Opposite
open PiExponentSeshadri.Geometry

theorem invertible_of_affine_equations {X : Scheme} (I : X.IdealSheafData)
    (hI : ∀ x : X, ∃ U : X.affineOpens, x ∈ U.1 ∧ ∃ r : Γ(X, U.1),
      IsRegular r ∧ I.ideal U = Ideal.span {r}) :
    InvertiblePullbackIdeal I (𝟙 X) := by
  apply invertible_of_local_equations
  intro x
  obtain ⟨U, hx, r, hr, he⟩ := hI x
  let e := U.1.topIso.commRingCatIsoToRingEquiv
  have hreg : IsLeftRegular (e.symm r) := by
    intro a b hab
    apply e.injective
    apply hr.1
    simpa only [map_mul, e.apply_symm_apply] using congrArg e hab
  refine ⟨U, hx, e.symm r, ⟨hreg, hreg.right_of_commute (fun a => mul_comm _ a)⟩, ?_⟩
  rw [Scheme.IdealSheafData.comap_id, IdealPullback.comap_ι_top, he,
    Ideal.map_span, Set.image_singleton]
  rfl

end InvertibleLocal

end PiExponentSeshadri

end

end OAI
end Source0008

section Source0009
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
end Source0009

section Source0010
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
end Source0010

section Source0011
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
end Source0011

section Source0012
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
end Source0012

section Source0013
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
end Source0013

section Source0014
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
end Source0014

section Source0015
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
end Source0015

section Source0016
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
end Source0016

section Source0017
/-
Modification notice for the LogTwo project.
Derived from openai/math (Apache-2.0), revision adc7f1241b42e322a6451854ab7e4b4c146bf78a.
Original source: lean/OAI/NumberTheory/PiExponent/Geometry/ProjectiveCharts.lean
Changes: Convert module/import declarations to the Lean 4.34 public module format.
See ../../../../../THIRD_PARTY_NOTICES.txt for provenance and the recorded changes.
-/




namespace OAI

noncomputable section

namespace PiExponentSeshadri.Projective

section
open AlgebraicGeometry CategoryTheory TopologicalSpace
open MvPolynomial HomogeneousLocalization
attribute [local instance] Classical.propDecidable

lemma homogeneous_eval₂_scale {R S σ : Type*} [CommRing R] [CommRing S]
    {p : MvPolynomial σ R} {n : ℕ} (hp : p.IsHomogeneous n)
    (f : R →+* S) (u : σ → S) (a : S) :
    eval₂ f (fun j => a * u j) p = a ^ n * eval₂ f u p := by
  classical
  rw [p.as_sum]
  simp only [eval₂_sum, eval₂_monomial, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro d hd
  simp only [mul_pow, Finsupp.prod, Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum]
  rw [← hp.degree_eq_sum_deg_support hd]
  ring

variable {R σ : Type*} [CommRing R] (i : σ)
attribute [local instance] MvPolynomial.gradedAlgebra

abbrev PolyGrade (R σ : Type*) [CommRing R] := MvPolynomial.homogeneousSubmodule σ R
lemma poly_X_mem : X (R := R) i ∈ PolyGrade R σ 1 := isHomogeneous_X R i

abbrev PolyChart := HomogeneousLocalization.Away (PolyGrade R σ) (X i)
abbrev ChartVariables := {j : σ // j ≠ i}

def chartConstants : R →+* PolyChart (R := R) i :=
  (HomogeneousLocalization.fromZeroRingHom _ _).comp
    { toFun := fun r => ⟨C r, isHomogeneous_C _ _⟩
      map_one' := Subtype.ext C_1
      map_mul' := fun _ _ => Subtype.ext C_mul
      map_zero' := Subtype.ext C_0
      map_add' := fun _ _ => Subtype.ext C_add }

def chartCoordinate (j : σ) : PolyChart (R := R) i :=
  Away.mk _ (poly_X_mem (R := R) i) 1 (X j) (by simpa using poly_X_mem (R := R) j)

def dehomogenize : MvPolynomial σ R →+* MvPolynomial (ChartVariables i) R :=
  eval₂Hom C (fun j => if h : j = i then 1 else X ⟨j, h⟩)

@[simp] lemma dehomogenize_X_self : dehomogenize (R := R) i (X i) = 1 := by
  classical
  simp [dehomogenize]

def chartToPoly : PolyChart (R := R) i →+* MvPolynomial (ChartVariables i) R :=
  (Localization.awayLift (dehomogenize i) (X i) (by simp)).comp (algebraMap _ _)

def polyToChart : MvPolynomial (ChartVariables i) R →+* PolyChart (R := R) i :=
  eval₂Hom (chartConstants i) (fun j => chartCoordinate i j.val)

@[simp] lemma chartToPoly_mk (n : ℕ) (p : MvPolynomial σ R)
    (hp : p ∈ PolyGrade R σ (n • 1)) :
    chartToPoly i (Away.mk _ (poly_X_mem (R := R) i) n p hp) = dehomogenize i p := by
  have h := Localization.awayLift_mk (dehomogenize (R := R) i) (X i) p 1
    (by simp) n
  simpa only [chartToPoly, RingHom.comp_apply, HomogeneousLocalization.algebraMap_apply,
    Away.val_mk, one_pow, mul_one] using h

@[simp] lemma chartToPoly_constants (r : R) :
    chartToPoly i (chartConstants i r) = C r := by
  exact (chartToPoly_mk i 0 (C r) (by simp)).trans
    (by simp [dehomogenize])

@[simp] lemma chartToPoly_coordinate (j : σ) :
    chartToPoly (R := R) i (chartCoordinate i j) =
      if h : j = i then 1 else X ⟨j, h⟩ := by
  rw [chartCoordinate, chartToPoly_mk]
  simp [dehomogenize]

lemma chartToPoly_comp_polyToChart :
    (chartToPoly (R := R) i).comp (polyToChart i) = RingHom.id _ := by
  classical
  apply MvPolynomial.ringHom_ext
  · intro r
    simp [polyToChart]
  · intro j
    simp [polyToChart, j.property]

lemma chart_val_mk (n : ℕ) (p : MvPolynomial σ R)
    (hp : p ∈ PolyGrade R σ (n • 1)) :
    (Away.mk _ (poly_X_mem (R := R) i) n p hp).val =
      algebraMap (MvPolynomial σ R) (Localization.Away (X (R := R) i)) p *
        (IsLocalization.Away.invSelf (X (R := R) i)) ^ n := by
  rw [Away.val_mk, Localization.mk_eq_mk', IsLocalization.mk'_eq_mul_mk'_one]
  congr 1
  rw [IsLocalization.Away.invSelf, ← IsLocalization.mk'_pow]
  simp only [one_pow]
  rfl

lemma chart_val_constants (r : R) :
    (chartConstants i r).val =
      algebraMap (MvPolynomial σ R) (Localization.Away (X (R := R) i)) (C r) := by
  exact (chart_val_mk i 0 (C r) (by simp)).trans
    (by simp only [pow_zero, mul_one])

lemma chart_val_coordinate (j : σ) :
    (chartCoordinate (R := R) i j).val =
      algebraMap (MvPolynomial σ R) (Localization.Away (X (R := R) i)) (X j) *
        IsLocalization.Away.invSelf (X (R := R) i) := by
  rw [chartCoordinate, chart_val_mk, pow_one]

lemma chart_dehomogenize_val :
    (algebraMap (PolyChart (R := R) i) (Localization.Away (X i))).comp
      ((polyToChart i).comp (dehomogenize i)) =
    eval₂Hom ((algebraMap (MvPolynomial σ R) (Localization.Away (X (R := R) i))).comp C)
      (fun j => IsLocalization.Away.invSelf (X (R := R) i) *
        algebraMap (MvPolynomial σ R) (Localization.Away (X (R := R) i)) (X j)) := by
  apply MvPolynomial.ringHom_ext
  · intro r
    simp [dehomogenize, polyToChart, chart_val_constants]
  · intro j
    by_cases h : j = i
    · subst j
      simp only [RingHom.comp_apply, dehomogenize_X_self, map_one, eval₂Hom_X']
      symm
      rw [mul_comm]
      exact IsLocalization.Away.mul_invSelf (X i)
    · simp [dehomogenize, polyToChart, h, chart_val_coordinate, mul_comm]

lemma polyToChart_comp_chartToPoly :
    (polyToChart (R := R) i).comp (chartToPoly i) = RingHom.id _ := by
  apply RingHom.ext
  intro x
  obtain ⟨n, p, hp, rfl⟩ := Away.mk_surjective _ (poly_X_mem (R := R) i) x
  apply HomogeneousLocalization.val_injective _
  simp only [RingHom.comp_apply, RingHom.id_apply, chartToPoly_mk, chart_val_mk]
  have he := RingHom.congr_fun (chart_dehomogenize_val (R := R) i) p
  change (polyToChart i (dehomogenize i p)).val = _ at he
  rw [he]
  change eval₂ _ _ p = _
  rw [homogeneous_eval₂_scale (by simpa using hp)]
  have hid : eval₂Hom ((algebraMap (MvPolynomial σ R) (Localization.Away (X (R := R) i))).comp C)
      (fun j => algebraMap (MvPolynomial σ R) (Localization.Away (X (R := R) i)) (X j)) =
      algebraMap (MvPolynomial σ R) (Localization.Away (X (R := R) i)) := by
    apply MvPolynomial.ringHom_ext <;> intro r <;> simp
  change _ * (eval₂Hom _ _ p) = _
  rw [hid]
  exact mul_comm _ _

def polynomialChartEquiv : PolyChart (R := R) i ≃+* MvPolynomial (ChartVariables i) R :=
  { chartToPoly i with
    invFun := polyToChart i
    left_inv := fun p => RingHom.congr_fun (polyToChart_comp_chartToPoly i) p
    right_inv := fun p => RingHom.congr_fun (chartToPoly_comp_polyToChart i) p }

def projectiveChartIso :
    (Proj.basicOpen (PolyGrade R σ) (X i)).toScheme ≅
      Spec (CommRingCat.of (MvPolynomial (ChartVariables i) R)) :=
  Proj.basicOpenIsoSpec _ (X i) (poly_X_mem (R := R) i) (by decide) ≪≫
    Scheme.Spec.mapIso ((polynomialChartEquiv i).toCommRingCatIso.symm.op)

end

open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite
open MvPolynomial
attribute [local instance] Classical.propDecidable
attribute [local instance] MvPolynomial.gradedAlgebra
variable {R σ : Type*} [CommRing R] (i : σ)

def chartSectionRingEquiv :
    Γ(Proj (PolyGrade R σ), Proj.basicOpen (PolyGrade R σ) (X i)) ≃+*
      MvPolynomial (ChartVariables i) R :=
  ((Proj.basicOpen (PolyGrade R σ) (X i)).topIso.symm ≪≫
    Scheme.Γ.mapIso (projectiveChartIso (R := R) i).symm.op ≪≫
    Scheme.ΓSpecIso (CommRingCat.of (MvPolynomial (ChartVariables i) R))).commRingCatIsoToRingEquiv

lemma standardChart_isAffineOpen :
    IsAffineOpen (Proj.basicOpen (PolyGrade R σ) (X i)) :=
  Proj.isAffineOpen_basicOpen _ _ (poly_X_mem i) (by decide)

lemma standardChart_cover :
    (⨆ i : σ, Proj.basicOpen (PolyGrade R σ) (X i)) = ⊤ := by
  apply Proj.iSup_basicOpen_eq_top
  rw [HomogeneousIdeal.toIdeal_irrelevant_le]
  intro n hn p hp
  change p ∈ idealOfVars σ R
  rw [← pow_one (idealOfVars σ R), mem_pow_idealOfVars_iff]
  intro d hd
  change 1 ≤ d.sum fun _ v => v
  rw [Finsupp.sum, ← hp.degree_eq_sum_deg_support hd]
  exact hn

end PiExponentSeshadri.Projective

end

end OAI
end Source0017

section Source0018
/-
Modification notice for the LogTwo project.
Derived from openai/math (Apache-2.0), revision adc7f1241b42e322a6451854ab7e4b4c146bf78a.
Original source: lean/OAI/NumberTheory/PiExponent/Approximation/LinePowerLaws.lean
Changes: Convert module/import declarations to the Lean 4.34 public module format.
See ../../../../../THIRD_PARTY_NOTICES.txt for provenance and the recorded changes.
-/




namespace OAI

noncomputable section

universe u v

namespace PiExponent.NumericalAmpleness
open CategoryTheory AlgebraicGeometry
lemma isIso_of_locally_isIso {X : Scheme} {M N : X.Modules} (f : M ⟶ N)
    (h : ∀ x : X, ∃ U : X.Opens, x ∈ U ∧ IsIso ((Scheme.Modules.restrictFunctor U.ι).map f)) :
    IsIso f := by
  have : Mono f := PiExponent.CoherentTwist.mono_of_local f (fun x => by
    obtain ⟨U,hx,hi⟩ := h x
    have := hi
    exact ⟨U,hx,inferInstance⟩)
  have : Epi f := PiExponent.CoherentTwist.epi_of_local f (fun x => by
    obtain ⟨U,hx,hi⟩ := h x
    have := hi
    exact ⟨U,hx,inferInstance⟩)
  exact isIso_of_mono_of_epi f
end PiExponent.NumericalAmpleness

namespace PiExponentSeshadri.TensorLocalization
open CategoryTheory MonoidalCategory
universe v' u'
variable {C : Type u} [Category.{v} C] [MonoidalCategory C]
  {D : Type u'} [Category.{v'} D] (F : C ⥤ D)

lemma map_tensor_right_unit {P Q L : C} (f : P ⟶ Q) (e : L ≅ 𝟙_ C)
    [IsIso (F.map f)] : IsIso (F.map (f ⊗ₘ 𝟙 L)) := by
  let ε (A : C) : A ⊗ L ≅ A := tensorIso (Iso.refl A) e ≪≫ ρ_ A
  have h : (f ⊗ₘ 𝟙 L) ≫ (ε Q).hom = (ε P).hom ≫ f := by
    simp only [ε, Iso.trans_hom, tensorIso_hom, Iso.refl_hom]
    rw [← Category.assoc, tensorHom_comp_tensorHom, Category.comp_id, Category.id_comp]
    have ht : f ⊗ₘ e.hom = (𝟙 P ⊗ₘ e.hom) ≫ (f ⊗ₘ 𝟙 (𝟙_ C)) := by
      rw [tensorHom_comp_tensorHom]
      simp only [Category.id_comp, Category.comp_id]
    rw [ht, Category.assoc, tensorHom_id, rightUnitor_naturality, Category.assoc]
  have hh : IsIso (F.map ((f ⊗ₘ 𝟙 L) ≫ (ε Q).hom)) := by
    rw [h, F.map_comp]
    infer_instance
  rw [F.map_comp] at hh
  exact (isIso_comp_right_iff _ _).mp hh

end PiExponentSeshadri.TensorLocalization

namespace PiExponentSeshadri.Geometry

section
open CategoryTheory AlgebraicGeometry TopologicalSpace MonoidalCategory
open scoped AlgebraicGeometry
variable {X : Scheme}

lemma sheafification_tensor_right_isIso
    {P Q : PresheafOfModules X.ringCatSheaf.obj} (f : P ⟶ Q) (L : LineBundle X)
    [IsIso ((PresheafOfModules.sheafification (𝟙 X.ringCatSheaf.obj)).map f)] :
    IsIso ((PresheafOfModules.sheafification (𝟙 X.ringCatSheaf.obj)).map
      (PresheafOfModulesOfCommRing.Monoidal.tensorHom (R := X.presheaf) f (𝟙 L.sheaf.val))) := by
  let F : PresheafOfModules X.ringCatSheaf.obj ⥤ X.Modules :=
    PresheafOfModules.sheafification (𝟙 X.ringCatSheaf.obj)
  apply PiExponent.NumericalAmpleness.isIso_of_locally_isIso
  intro x
  obtain ⟨U, hx, ⟨e⟩⟩ := L.locallyRankOne x
  refine ⟨U, hx, ?_⟩
  let R : PresheafOfModules X.ringCatSheaf.obj ⥤
      PresheafOfModules U.toScheme.ringCatSheaf.obj := modulePresheafRestrict U.ι
  let S : PresheafOfModules U.toScheme.ringCatSheaf.obj ⥤ U.toScheme.Modules :=
    PresheafOfModules.sheafification (𝟙 U.toScheme.ringCatSheaf.obj)
  let : MonoidalCategory (PresheafOfModules U.toScheme.ringCatSheaf.obj) :=
    PresheafOfModulesOfCommRing.monoidalCategory (R := U.toScheme.presheaf)
  have hf : IsIso (S.map (R.map f)) := by
    apply (NatIso.isIso_map_iff (moduleSheafificationRestrict U.ι) f).mp
    change IsIso ((Scheme.Modules.restrictFunctor U.ι).map (F.map f))
    let : IsIso (F.map f) := inferInstanceAs
      (IsIso ((PresheafOfModules.sheafification (𝟙 X.ringCatSheaf.obj)).map f))
    exact (Scheme.Modules.restrictFunctor U.ι).map_isIso (F.map f)
  let ep : R.obj L.sheaf.val ≅ 𝟙_ (PresheafOfModules U.toScheme.ringCatSheaf.obj) :=
    (SheafOfModules.forget _).mapIso e
  have ht : IsIso (S.map ((R.map f) ⊗ₘ 𝟙 (R.obj L.sheaf.val))) :=
    TensorLocalization.map_tensor_right_unit S (R.map f) ep
  apply (NatIso.isIso_map_iff (moduleSheafificationRestrict U.ι) _).mpr
  let g := PresheafOfModulesOfCommRing.Monoidal.tensorHom (R := X.presheaf) f (𝟙 L.sheaf.val)
  change IsIso (S.map (R.map g))
  have heq := modulePresheafTensorRestrict_natural U f (𝟙 L.sheaf.val)
  let : IsIso (S.map (modulePresheafTensorRestrict U P L.sheaf.val).hom) :=
    (S.mapIso (modulePresheafTensorRestrict U P L.sheaf.val)).isIso_hom
  let : IsIso (S.map (modulePresheafTensorRestrict U Q L.sheaf.val).hom) :=
    (S.mapIso (modulePresheafTensorRestrict U Q L.sheaf.val)).isIso_hom
  have hcomp : IsIso (S.map (R.map g ≫
      (modulePresheafTensorRestrict U Q L.sheaf.val).hom)) := by
    erw [heq, S.map_comp]
    have ht' : IsIso (S.map
        (PresheafOfModulesOfCommRing.Monoidal.tensorHom (R := U.toScheme.presheaf)
          (R.map f) (R.map (𝟙 L.sheaf.val)))) := by
      rw [R.map_id]
      exact ht
    exact (inferInstance : IsIso (C := U.toScheme.Modules)
      (S.map (modulePresheafTensorRestrict U P L.sheaf.val).hom ≫ S.map
        (PresheafOfModulesOfCommRing.Monoidal.tensorHom (R := U.toScheme.presheaf)
          (R.map f) (R.map (𝟙 L.sheaf.val)))))
  erw [S.map_comp] at hcomp
  exact (isIso_comp_right_iff (C := U.toScheme.Modules) _ _).mp hcomp

end

open CategoryTheory AlgebraicGeometry TopologicalSpace MonoidalCategory BraidedCategory
open scoped AlgebraicGeometry
variable {X : Scheme}

lemma sheafification_tensor_left_isIso
    {P Q : PresheafOfModules X.ringCatSheaf.obj} (f : P ⟶ Q) (L : LineBundle X)
    [IsIso ((PresheafOfModules.sheafification (𝟙 X.ringCatSheaf.obj)).map f)] :
    IsIso ((PresheafOfModules.sheafification (𝟙 X.ringCatSheaf.obj)).map
      (PresheafOfModulesOfCommRing.Monoidal.tensorHom (R := X.presheaf) (𝟙 L.sheaf.val) f)) := by
  let : MonoidalCategory (PresheafOfModules X.ringCatSheaf.obj) :=
    PresheafOfModulesOfCommRing.monoidalCategory (R := X.presheaf)
  let : SymmetricCategory (PresheafOfModules X.ringCatSheaf.obj) :=
    PresheafOfModulesOfCommRing.symmetricCategory (R := X.presheaf)
  let F : PresheafOfModules X.ringCatSheaf.obj ⥤ X.Modules :=
    PresheafOfModules.sheafification (𝟙 X.ringCatSheaf.obj)
  have : IsIso (F.map (f ⊗ₘ 𝟙 L.sheaf.val)) := sheafification_tensor_right_isIso f L
  let : IsIso (F.map (β_ L.sheaf.val P).hom) :=
    (F.mapIso (β_ L.sheaf.val P)).isIso_hom
  have h : IsIso (F.map ((𝟙 L.sheaf.val ⊗ₘ f) ≫ (β_ L.sheaf.val Q).hom)) := by
    rw [braiding_naturality, F.map_comp]
    exact (inferInstance : IsIso (C := X.Modules)
      (F.map (β_ L.sheaf.val P).hom ≫ F.map (f ⊗ₘ 𝟙 L.sheaf.val)))
  rw [F.map_comp] at h
  exact (isIso_comp_right_iff _ _).mp h

def sheafificationTensorRight (P : PresheafOfModules X.ringCatSheaf.obj)
    (L : LineBundle X) :
    (PresheafOfModules.sheafification (𝟙 X.ringCatSheaf.obj)).obj
      (PresheafOfModulesOfCommRing.Monoidal.tensorObj (R := X.presheaf) P L.sheaf.val) ≅
    moduleTensor X ((PresheafOfModules.sheafification (𝟙 X.ringCatSheaf.obj)).obj P)
      L.sheaf := by
  let F := PresheafOfModules.sheafification (𝟙 X.ringCatSheaf.obj)
  let η := (PresheafOfModules.sheafificationAdjunction (𝟙 X.ringCatSheaf.obj)).unit.app P
  have : IsIso (F.map η) :=
    isIso_of_comp_hom_eq_id _
      ((PresheafOfModules.sheafificationAdjunction (𝟙 X.ringCatSheaf.obj)).left_triangle_components P)
  let ht : IsIso (F.map (PresheafOfModulesOfCommRing.Monoidal.tensorHom
      (R := X.presheaf) η (𝟙 L.sheaf.val))) := sheafification_tensor_right_isIso η L
  exact @asIso _ _ _ _ (F.map (PresheafOfModulesOfCommRing.Monoidal.tensorHom (R := X.presheaf)
    η (𝟙 L.sheaf.val))) ht

def sheafificationTensorLeft (P : PresheafOfModules X.ringCatSheaf.obj)
    (L : LineBundle X) :
    (PresheafOfModules.sheafification (𝟙 X.ringCatSheaf.obj)).obj
      (PresheafOfModulesOfCommRing.Monoidal.tensorObj (R := X.presheaf) L.sheaf.val P) ≅
    moduleTensor X L.sheaf
      ((PresheafOfModules.sheafification (𝟙 X.ringCatSheaf.obj)).obj P) := by
  let F := PresheafOfModules.sheafification (𝟙 X.ringCatSheaf.obj)
  let η := (PresheafOfModules.sheafificationAdjunction (𝟙 X.ringCatSheaf.obj)).unit.app P
  have : IsIso (F.map η) :=
    isIso_of_comp_hom_eq_id _
      ((PresheafOfModules.sheafificationAdjunction (𝟙 X.ringCatSheaf.obj)).left_triangle_components P)
  let ht : IsIso (F.map (PresheafOfModulesOfCommRing.Monoidal.tensorHom
      (R := X.presheaf) (𝟙 L.sheaf.val) η)) := sheafification_tensor_left_isIso η L
  exact @asIso _ _ _ _ (F.map (PresheafOfModulesOfCommRing.Monoidal.tensorHom (R := X.presheaf)
    (𝟙 L.sheaf.val) η)) ht

def lineTensorAssoc (L M N : LineBundle X) :
    moduleTensor X (moduleTensor X L.sheaf M.sheaf) N.sheaf ≅
      moduleTensor X L.sheaf (moduleTensor X M.sheaf N.sheaf) := by
  let : MonoidalCategory (PresheafOfModules X.ringCatSheaf.obj) :=
    PresheafOfModulesOfCommRing.monoidalCategory (R := X.presheaf)
  exact (sheafificationTensorRight (L.sheaf.val ⊗ M.sheaf.val) N).symm ≪≫
    (PresheafOfModules.sheafification (𝟙 X.ringCatSheaf.obj)).mapIso
      (α_ L.sheaf.val M.sheaf.val N.sheaf.val) ≪≫
    sheafificationTensorLeft (M.sheaf.val ⊗ N.sheaf.val) L

def linePowerAdd (L : LineBundle X) : ∀ m n : ℕ,
    modulePow X L.sheaf (m + n) ≅
      moduleTensor X (modulePow X L.sheaf m) (modulePow X L.sheaf n)
  | 0, n => by
      simpa only [Nat.zero_add, modulePow, structureSheaf] using (moduleTensorUnit (modulePow X L.sheaf n)).symm
  | m + 1, n => by
      rw [Nat.succ_add]
      exact moduleTensorIso (Iso.refl _) (linePowerAdd L m n) ≪≫
        (lineTensorAssoc L (L.pow m) (L.pow n)).symm

def linePowerMul (L : LineBundle X) (m : ℕ) : ∀ n : ℕ,
    modulePow X (modulePow X L.sheaf m) n ≅ modulePow X L.sheaf (m * n)
  | 0 => Iso.refl _
  | n + 1 => by
      rw [Nat.mul_succ, Nat.add_comm (m * n) m]
      exact moduleTensorIso (Iso.refl _) (linePowerMul L m n) ≪≫
        (linePowerAdd L m (m * n)).symm

end PiExponentSeshadri.Geometry

end

end OAI
end Source0018

section Source0019
/-
Modification notice for the LogTwo project.
Derived from openai/math (Apache-2.0), revision adc7f1241b42e322a6451854ab7e4b4c146bf78a.
Original source: lean/OAI/NumberTheory/PiExponent/Approximation/FrameTensorPowers.lean
Changes: Convert module/import declarations to the Lean 4.34 public module format.
See ../../../../../THIRD_PARTY_NOTICES.txt for provenance and the recorded changes.
-/




namespace OAI

namespace PiExponentSeshadri.Geometry
noncomputable section
open CategoryTheory AlgebraicGeometry TopologicalSpace MonoidalCategory
open scoped AlgebraicGeometry
open PiExponentSeshadri.Frames
variable {X : Scheme}

lemma tensor_unit_end {C : Type*} [Category C] [MonoidalCategory C]
    (f g : 𝟙_ C ⟶ 𝟙_ C) :
    (f ⊗ₘ g) ≫ (λ_ (𝟙_ C)).hom = (λ_ (𝟙_ C)).hom ≫ (f ≫ g) := by
  rw [MonoidalCategory.tensorHom_def, Category.assoc, leftUnitor_naturality, ← Category.assoc,
    unitors_equal, rightUnitor_naturality, Category.assoc]

lemma moduleTensorUnit_scalar (f g : structureSheaf X ⟶ structureSheaf X) :
    moduleTensorMap f g ≫ (moduleTensorUnit (structureSheaf X)).hom =
      (moduleTensorUnit (structureSheaf X)).hom ≫ (f ≫ g) := by
  let : MonoidalCategory (PresheafOfModules X.ringCatSheaf.obj) :=
    PresheafOfModulesOfCommRing.monoidalCategory (R := X.presheaf)
  let F : PresheafOfModules X.ringCatSheaf.obj ⥤ X.Modules :=
    PresheafOfModules.sheafification (𝟙 X.ringCatSheaf.obj)
  let G : X.Modules ⥤ PresheafOfModules X.ringCatSheaf.obj :=
    SheafOfModules.forget X.ringCatSheaf ⋙
      PresheafOfModules.restrictScalars (𝟙 X.ringCatSheaf.obj)
  let ε : G ⋙ F ⟶ 𝟭 X.Modules :=
    (PresheafOfModules.sheafificationAdjunction (𝟙 X.ringCatSheaf.obj)).counit
  have h : (f.val ⊗ₘ g.val) ≫ (λ_ (structureSheaf X).val).hom =
      (λ_ (structureSheaf X).val).hom ≫ (f ≫ g).val := by
    let f₀ : 𝟙_ (PresheafOfModules X.ringCatSheaf.obj) ⟶
        𝟙_ (PresheafOfModules X.ringCatSheaf.obj) := f.val
    let g₀ : 𝟙_ (PresheafOfModules X.ringCatSheaf.obj) ⟶
        𝟙_ (PresheafOfModules X.ringCatSheaf.obj) := g.val
    exact tensor_unit_end f₀ g₀
  change F.map (f.val ⊗ₘ g.val) ≫ (F.map (λ_ (structureSheaf X).val).hom ≫ ε.app (structureSheaf X)) =
    (F.map (λ_ (structureSheaf X).val).hom ≫ ε.app (structureSheaf X)) ≫ (f ≫ g)
  erw [← Category.assoc, ← F.map_comp, h, F.map_comp, Category.assoc, Category.assoc]
  congr 1
  exact ε.naturality (f ≫ g)

def endPower (f : structureSheaf X ⟶ structureSheaf X) : ℕ → (structureSheaf X ⟶ structureSheaf X)
  | 0 => 𝟙 _
  | n + 1 => f ≫ endPower f n

lemma endValue_endPower (f : structureSheaf X ⟶ structureSheaf X) (n : ℕ) :
    endValue (endPower f n) = endValue f ^ n := by
  induction n with
  | zero =>
    change (1 : Γ(X, ⊤)) = endValue f ^ 0
    exact (pow_zero _).symm
  | succ n hn =>
    calc
      endValue (endPower f (n + 1)) = endValue f * endValue (endPower f n) :=
        endValue_comp f (endPower f n)
      _ = endValue f * endValue f ^ n := congrArg (endValue f * ·) hn
      _ = _ := (pow_succ' _ _).symm

lemma moduleTensorUnit_natural {M N : X.Modules} (g : M ⟶ N) :
    moduleTensorMap (𝟙 (structureSheaf X)) g ≫ (moduleTensorUnit N).hom =
      (moduleTensorUnit M).hom ≫ g := by
  let : MonoidalCategory (PresheafOfModules X.ringCatSheaf.obj) :=
    PresheafOfModulesOfCommRing.monoidalCategory (R := X.presheaf)
  let F : PresheafOfModules X.ringCatSheaf.obj ⥤ X.Modules :=
    PresheafOfModules.sheafification (𝟙 X.ringCatSheaf.obj)
  let G : X.Modules ⥤ PresheafOfModules X.ringCatSheaf.obj :=
    SheafOfModules.forget X.ringCatSheaf ⋙
      PresheafOfModules.restrictScalars (𝟙 X.ringCatSheaf.obj)
  let ε : G ⋙ F ⟶ 𝟭 X.Modules :=
    (PresheafOfModules.sheafificationAdjunction (𝟙 X.ringCatSheaf.obj)).counit
  change F.map ((𝟙 (structureSheaf X).val) ⊗ₘ g.val) ≫
    (F.map (λ_ N.val).hom ≫ ε.app N) =
    (F.map (λ_ M.val).hom ≫ ε.app M) ≫ g
  have h : ((𝟙 (structureSheaf X).val) ⊗ₘ g.val) ≫ (λ_ N.val).hom =
      (λ_ M.val).hom ≫ g.val := by
    rw [id_tensorHom]
    exact leftUnitor_naturality g.val
  have hF : F.map (𝟙 (structureSheaf X).val ⊗ₘ g.val) ≫ F.map (λ_ N.val).hom =
      F.map (λ_ M.val).hom ≫ F.map g.val :=
    (F.map_comp _ _).symm.trans ((congrArg F.map h).trans (F.map_comp _ _))
  refine (Category.assoc _ _ _).symm.trans ?_
  refine (congrArg (· ≫ ε.app N) hF).trans ?_
  refine (Category.assoc _ _ _).trans ?_
  refine (congrArg (F.map (λ_ M.val).hom ≫ ·) (ε.naturality g)).trans ?_
  exact (Category.assoc _ _ _).symm

lemma modulePowMap_unitPower (f : structureSheaf X ⟶ structureSheaf X) (n : ℕ) :
    modulePowMap f n ≫ (unitPowerIso n).hom =
      (unitPowerIso n).hom ≫ endPower f n := by
  induction n with
  | zero =>
    change 𝟙 (structureSheaf X) ≫ 𝟙 (structureSheaf X) = 𝟙 (structureSheaf X) ≫ 𝟙 (structureSheaf X)
    rfl
  | succ n hn =>
    change moduleTensorMap f (modulePowMap f n) ≫
      ((moduleTensorUnit _).hom ≫ (unitPowerIso n).hom) =
        ((moduleTensorUnit _).hom ≫ (unitPowerIso n).hom) ≫ (f ≫ endPower f n)
    calc
      _ = moduleTensorMap f (modulePowMap f n) ≫
          moduleTensorMap (𝟙 (structureSheaf X)) (unitPowerIso n).hom ≫
            (moduleTensorUnit (structureSheaf X)).hom := by
        rw [moduleTensorUnit_natural]
      _ = moduleTensorMap f ((unitPowerIso n).hom ≫ endPower f n) ≫
            (moduleTensorUnit (structureSheaf X)).hom := by
        rw [← Category.assoc, ← moduleTensorMap_comp, Category.comp_id, hn]
      _ = moduleTensorMap (𝟙 (structureSheaf X)) (unitPowerIso n).hom ≫
          moduleTensorMap f (endPower f n) ≫ (moduleTensorUnit (structureSheaf X)).hom := by
        rw [← Category.assoc, ← moduleTensorMap_comp, Category.id_comp]
      _ = (moduleTensorUnit (modulePow X (structureSheaf X) n)).hom ≫
          (unitPowerIso n).hom ≫ (f ≫ endPower f n) := by
        rw [moduleTensorUnit_scalar, ← Category.assoc, moduleTensorUnit_natural,
          Category.assoc]
      _ = _ := by simp only [Category.assoc]

def globalPowerFrame {M : X.Modules} (e : M ≅ structureSheaf X) (n : ℕ) :
    modulePow X M n ≅ structureSheaf X :=
  (modulePowFunctor n).mapIso e ≪≫ unitPowerIso n

lemma powerSection_coefficient {M : X.Modules} (e : M ≅ structureSheaf X)
    (s : structureSheaf X ⟶ M) (n : ℕ) :
    coefficient (globalPowerFrame e n) (powerSection s n) = coefficient e s ^ n := by
  change endValue ((unitPowerIso n).inv ≫ modulePowMap s n ≫
    (modulePowMap e.hom n ≫ (unitPowerIso n).hom)) = _
  erw [← Category.assoc (modulePowMap s n), ← modulePowMap_comp,
    modulePowMap_unitPower, Iso.inv_hom_id_assoc, endValue_endPower]
  rfl

lemma frameChange_globalPowerFrame {M : X.Modules}
    (e f : M ≅ structureSheaf X) (n : ℕ) :
    (frameChange (globalPowerFrame e n) (globalPowerFrame f n) : Γ(X,⊤)) =
      (frameChange e f : Γ(X,⊤)) ^ n := by
  have h := powerSection_coefficient f e.inv n
  exact h

end
end PiExponentSeshadri.Geometry

end OAI
end Source0019

section Source0020
/-
Modification notice for the LogTwo project.
Derived from openai/math (Apache-2.0), revision adc7f1241b42e322a6451854ab7e4b4c146bf78a.
Original source: lean/OAI/NumberTheory/PiExponent/Approximation/TensorPowerRestriction.lean
Changes: Convert module/import declarations to the Lean 4.34 public module format.
See ../../../../../THIRD_PARTY_NOTICES.txt for provenance and the recorded changes.
-/




namespace OAI

noncomputable section

namespace PiExponentSeshadri.Geometry

section
open CategoryTheory AlgebraicGeometry TopologicalSpace MonoidalCategory
open scoped AlgebraicGeometry
variable {X : Scheme}

def modulePowRestrict (U : X.Opens) (M : X.Modules) :
    ∀ n, (modulePow X M n).restrict U.ι ≅ modulePow U.toScheme (M.restrict U.ι) n
  | 0 => Scheme.Modules.restrictUnitIso U.ι
  | n + 1 => moduleTensorRestrict U M (modulePow X M n) ≪≫
      moduleTensorIso (Iso.refl _) (modulePowRestrict U M n)

lemma modulePowRestrict_natural (U : X.Opens) {M N : X.Modules} (f : M ⟶ N) (n : ℕ) :
    (Scheme.Modules.restrictFunctor U.ι).map (modulePowMap f n) ≫
      (modulePowRestrict U N n).hom =
    (modulePowRestrict U M n).hom ≫
      modulePowMap ((Scheme.Modules.restrictFunctor U.ι).map f) n := by
  induction n with
  | zero =>
    change (Scheme.Modules.restrictFunctor U.ι).map (𝟙 (structureSheaf X)) ≫
      (Scheme.Modules.restrictUnitIso U.ι).hom =
      (Scheme.Modules.restrictUnitIso U.ι).hom ≫ 𝟙 _
    erw [(Scheme.Modules.restrictFunctor U.ι).map_id, Category.id_comp]
  | succ n hn =>
    change (Scheme.Modules.restrictFunctor U.ι).map (moduleTensorMap f (modulePowMap f n)) ≫
      ((moduleTensorRestrict U N (modulePow X N n)).hom ≫
        (moduleTensorIso (Iso.refl _) (modulePowRestrict U N n)).hom) =
      ((moduleTensorRestrict U M (modulePow X M n)).hom ≫
        (moduleTensorIso (Iso.refl _) (modulePowRestrict U M n)).hom) ≫
          moduleTensorMap ((Scheme.Modules.restrictFunctor U.ι).map f)
            (modulePowMap ((Scheme.Modules.restrictFunctor U.ι).map f) n)
    simp only [moduleTensorIso_hom, Iso.refl_hom]
    rw [← Category.assoc, moduleTensorRestrict_natural, Category.assoc,
      ← moduleTensorMap_comp, Category.comp_id, hn]
    rw [Category.assoc, ← moduleTensorMap_comp, Category.id_comp]

lemma modulePowMap_restrict_isIso (U : X.Opens) {M N : X.Modules} (f : M ⟶ N)
    [IsIso ((Scheme.Modules.restrictFunctor U.ι).map f)] (n : ℕ) :
    IsIso ((Scheme.Modules.restrictFunctor U.ι).map (modulePowMap f n)) := by
  have h := modulePowRestrict_natural U f n
  have heq : (Scheme.Modules.restrictFunctor U.ι).map (modulePowMap f n) =
      (modulePowRestrict U M n).hom ≫
        modulePowMap ((Scheme.Modules.restrictFunctor U.ι).map f) n ≫
          (modulePowRestrict U N n).inv := by
    rw [← Category.assoc, ← h, Category.assoc, Iso.hom_inv_id, Category.comp_id]
  rw [heq]
  infer_instance

lemma powerSection_restrict_isIso (U : X.Opens) {M : X.Modules}
    (s : structureSheaf X ⟶ M)
    [IsIso ((Scheme.Modules.restrictFunctor U.ι).map s)] (n : ℕ) :
    IsIso ((Scheme.Modules.restrictFunctor U.ι).map (powerSection s n)) := by
  let := modulePowMap_restrict_isIso U s n
  unfold powerSection
  rw [(Scheme.Modules.restrictFunctor U.ι).map_comp]
  infer_instance

lemma sectionOpen_le_powerSection {M : X.Modules} (s : structureSheaf X ⟶ M) (n : ℕ) :
    sectionOpen X s ≤ sectionOpen X (powerSection s n) := by
  refine iSup_le fun U => iSup_le fun hU => ?_
  let := hU
  exact le_iSup_of_le U (le_iSup_of_le (powerSection_restrict_isIso U s n) le_rfl)

end

open CategoryTheory AlgebraicGeometry TopologicalSpace
open scoped AlgebraicGeometry
open PiExponentSeshadri.Frames
variable {X : Scheme}

def powerRestrictionUnit (U : X.Opens) (n : ℕ) :
    structureSheaf U.toScheme ≅ structureSheaf U.toScheme :=
  (Scheme.Modules.restrictUnitIso U.ι).symm ≪≫
    (Scheme.Modules.restrictFunctor U.ι).mapIso (unitPowerIso n).symm ≪≫
      modulePowRestrict U (structureSheaf X) n ≪≫
        (modulePowFunctor n).mapIso (Scheme.Modules.restrictUnitIso U.ι) ≪≫
          unitPowerIso n

lemma restrictPowerSection_factor (U : X.Opens) {M : X.Modules}
    (s : structureSheaf X ⟶ M) (n : ℕ) :
    restrictSection U.ι (powerSection s n) ≫ (modulePowRestrict U M n).hom =
      (powerRestrictionUnit U n).hom ≫
        powerSection (restrictSection U.ι s) n := by
  have hs : (Scheme.Modules.restrictUnitIso U.ι).hom ≫ restrictSection U.ι s =
      (Scheme.Modules.restrictFunctor U.ι).map s := by
    let F : X.Modules ⥤ U.toScheme.Modules := Scheme.Modules.restrictFunctor U.ι
    let e : F.obj (structureSheaf X) ≅ structureSheaf U.toScheme :=
      Scheme.Modules.restrictUnitIso U.ι
    exact e.hom_inv_id_assoc (F.map s)
  dsimp only [restrictSection, powerSection, powerRestrictionUnit, Iso.trans_hom,
    Iso.symm_hom, Functor.mapIso_hom, modulePowFunctor]
  erw [(Scheme.Modules.restrictFunctor U.ι).map_comp]
  repeat' erw [Category.assoc]
  erw [modulePowRestrict_natural]
  erw [Iso.hom_inv_id_assoc, ← modulePowMap_comp]
  erw [show (Scheme.Modules.restrictUnitIso U.ι).hom ≫
      ((Scheme.Modules.restrictUnitIso U.ι).inv ≫
        (Scheme.Modules.restrictFunctor U.ι).map s) =
        (Scheme.Modules.restrictFunctor U.ι).map s from hs]
  rfl

end PiExponentSeshadri.Geometry

end

end OAI
end Source0020

section Source0021
/-
Modification notice for the LogTwo project.
Derived from openai/math (Apache-2.0), revision adc7f1241b42e322a6451854ab7e4b4c146bf78a.
Original source: lean/OAI/NumberTheory/PiExponent/Approximation/SectionPowerOpens.lean
Changes: Convert module/import declarations to the Lean 4.34 public module format.
See ../../../../../THIRD_PARTY_NOTICES.txt for provenance and the recorded changes.
-/




namespace OAI

noncomputable section

namespace PiExponentSeshadri

namespace Frames
open CategoryTheory AlgebraicGeometry
lemma coefficient_precompose {X : Scheme} {M : X.Modules} (e : M ≅ O X)
    (a : O X ⟶ O X) (s : O X ⟶ M) :
    coefficient e (a ≫ s) = endValue a * coefficient e s := by
  change endValue ((a ≫ s) ≫ e.hom) = _
  rw [Category.assoc]
  exact endValue_comp a (s ≫ e.hom)
end Frames

namespace Geometry
open CategoryTheory AlgebraicGeometry TopologicalSpace
open scoped AlgebraicGeometry
open PiExponentSeshadri.Frames
variable {X : Scheme}

def localPowerFrame (U : X.Opens) {M : X.Modules}
    (e : M.restrict U.ι ≅ structureSheaf U.toScheme) (n : ℕ) :
    (modulePow X M n).restrict U.ι ≅ structureSheaf U.toScheme :=
  modulePowRestrict U M n ≪≫ globalPowerFrame e n

lemma local_powerSection_coefficient (U : X.Opens) {M : X.Modules}
    (e : M.restrict U.ι ≅ structureSheaf U.toScheme)
    (s : structureSheaf X ⟶ M) (n : ℕ) :
    coefficient (localPowerFrame U e n) (restrictSection U.ι (powerSection s n)) =
      endValue (powerRestrictionUnit U n).hom *
        coefficient e (restrictSection U.ι s) ^ n := by
  change coefficient (globalPowerFrame e n)
    (restrictSection U.ι (powerSection s n) ≫ (modulePowRestrict U M n).hom) = _
  calc
    _ = coefficient (globalPowerFrame e n)
        ((powerRestrictionUnit U n).hom ≫ powerSection (restrictSection U.ι s) n) :=
      congrArg (coefficient (globalPowerFrame e n)) (restrictPowerSection_factor U s n)
    _ = endValue (powerRestrictionUnit U n).hom *
        coefficient (globalPowerFrame e n) (powerSection (restrictSection U.ι s) n) :=
      coefficient_precompose _ _ _
    _ = _ := congrArg (endValue (powerRestrictionUnit U n).hom * ·)
      (powerSection_coefficient e _ n)

lemma local_powerSection_coefficient_unit (U : X.Opens) (n : ℕ) :
    IsUnit (endValue (powerRestrictionUnit U n).hom) := by
  have h : IsIso (powerRestrictionUnit U n).hom := inferInstance
  exact (end_isIso_iff (powerRestrictionUnit U n).hom).mp h

theorem LineBundle.sectionOpen_power (L : LineBundle X) (s : GlobalSections X L.sheaf)
    {n : ℕ} (hn : 0 < n) :
    sectionOpen X (powerSection s n) = sectionOpen X s := by
  have hlocal (U : X.Opens) (e : L.sheaf.restrict U.ι ≅ structureSheaf U.toScheme) :
      U.ι ⁻¹ᵁ sectionOpen X (powerSection s n) = U.ι ⁻¹ᵁ sectionOpen X s := by
    change U.ι ⁻¹ᵁ SectionOpens.isoOpen (powerSection s n) =
      U.ι ⁻¹ᵁ SectionOpens.isoOpen s
    calc
      _ = U.toScheme.basicOpen (coefficient (localPowerFrame U e n)
          (restrictSection U.ι (powerSection s n))) :=
        preimage_isoOpen (powerSection s n) U.ι (localPowerFrame U e n)
      _ = U.toScheme.basicOpen (endValue (powerRestrictionUnit U n).hom *
          coefficient e (restrictSection U.ι s) ^ n) :=
        congrArg U.toScheme.basicOpen (local_powerSection_coefficient U e s n)
      _ = U.toScheme.basicOpen (coefficient e (restrictSection U.ι s)) := by
        rw [Scheme.basicOpen_mul,
          Scheme.basicOpen_of_isUnit _ (local_powerSection_coefficient_unit U n),
          top_inf_eq]
        exact U.toScheme.basicOpen_pow (coefficient e (restrictSection U.ι s)) hn
      _ = _ := (preimage_isoOpen s U.ι e).symm
  ext x
  obtain ⟨U, hxU, ⟨e⟩⟩ := L.locallyRankOne x
  have h := congrArg (fun V : U.toScheme.Opens => (⟨x, hxU⟩ : U.toScheme) ∈ V) (hlocal U e)
  exact Iff.of_eq h

end Geometry

end PiExponentSeshadri

end

end OAI
end Source0021

section Source0022
/-
Modification notice for the LogTwo project.
Derived from openai/math (Apache-2.0), revision adc7f1241b42e322a6451854ab7e4b4c146bf78a.
Original source: lean/OAI/NumberTheory/PiExponent/Ampleness/AmpleCommonDegree.lean
Changes: Convert module/import declarations to the Lean 4.34 public module format.
See ../../../../../THIRD_PARTY_NOTICES.txt for provenance and the recorded changes.
-/




namespace OAI

namespace PiExponentSeshadri.Geometry
noncomputable section
open CategoryTheory AlgebraicGeometry TopologicalSpace TopologicalSpace.Opens
open scoped AlgebraicGeometry
variable {X : Scheme}

theorem LineBundle.common_degree (L : LineBundle X) {ι : Type} [Fintype ι]
    (d : ι → ℕ) (hd : ∀ i, 0 < d i)
    (s : ∀ i, GlobalSections X (modulePow X L.sheaf (d i))) :
    ∃ n : ℕ, 0 < n ∧ ∃ t : ι → GlobalSections X (modulePow X L.sheaf n),
      ∀ i, sectionOpen X (t i) = sectionOpen X (s i) := by
  classical
  let n := ∏ i, d i
  have hn : 0 < n := Finset.prod_pos (fun i _ => hd i)
  have hdiv (i : ι) : d i ∣ n := Finset.dvd_prod_of_mem d (Finset.mem_univ i)
  have heq (i : ι) : d i * (n / d i) = n := Nat.mul_div_cancel' (hdiv i)
  let e (i : ι) : modulePow X (modulePow X L.sheaf (d i)) (n / d i) ≅
      modulePow X L.sheaf n :=
    linePowerMul L (d i) (n / d i) ≪≫ eqToIso (congrArg (modulePow X L.sheaf) (heq i))
  refine ⟨n, hn, fun i => powerSection (s i) (n / d i) ≫ (e i).hom, ?_⟩
  intro i
  change SectionOpens.isoOpen (powerSection (s i) (n / d i) ≫ (e i).hom) = _
  rw [SectionOpens.isoOpen_postcomp]
  exact (L.pow (d i)).sectionOpen_power (s i)
    (Nat.div_pos (Nat.le_of_dvd hn (hdiv i)) (hd i))

theorem LineBundle.ample_common_degree_cover [CompactSpace X] (L : LineBundle X)
    (hL : L.IsAmple) :
    ∃ n : ℕ, 0 < n ∧ ∃ l : ℕ,
      ∃ s : Fin l → GlobalSections X (modulePow X L.sheaf n),
        (⨆ i, sectionOpen X (s i)) = ⊤ ∧
        (∀ i, IsAffineOpen (sectionOpen X (s i))) ∧
        (∀ i, (sectionOpen X (s i) : Set X).Nonempty) := by
  classical
  have hex (x : X) := hL x ⊤ (by trivial)
  choose d hd s hs hst ha using hex
  obtain ⟨I, hI⟩ := isCompact_univ.elim_finite_subcover
    (fun x => (sectionOpen X (s x) : Set X)) (fun x => (sectionOpen X (s x)).isOpen)
    (by intro x _; exact Set.mem_iUnion.mpr ⟨x, hs x⟩)
  obtain ⟨n, hn, t, ht⟩ := L.common_degree (fun i : I => d i.val)
    (fun i => hd i.val) (fun i => s i.val)
  let e := (Fintype.equivFin I).symm
  refine ⟨n, hn, Fintype.card I, fun i => t (e i), ?_, ?_, ?_⟩
  · apply top_unique
    intro x _
    obtain ⟨i, hi⟩ := Set.mem_iUnion.mp (hI (show x ∈ Set.univ from trivial))
    obtain ⟨hi, hx⟩ := Set.mem_iUnion.mp hi
    apply Opens.mem_iSup.mpr
    refine ⟨e.symm ⟨i, hi⟩, ?_⟩
    change x ∈ sectionOpen X (t (e (e.symm ⟨i, hi⟩)))
    rw [Equiv.apply_symm_apply, ht]
    exact hx
  · intro i
    rw [ht]
    exact ha (e i).val
  · intro i
    rw [ht]
    exact ⟨(e i).val, hs (e i).val⟩

end
end PiExponentSeshadri.Geometry

end OAI
end Source0022

section Source0023
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
end Source0023

section Source0024
/-
Modification notice for the LogTwo project.
Derived from openai/math (Apache-2.0), revision adc7f1241b42e322a6451854ab7e4b4c146bf78a.
Original source: lean/OAI/NumberTheory/PiExponent/Approximation/PowerSectionExtension.lean
Changes: Convert module/import declarations to the Lean 4.34 public module format.
See ../../../../../THIRD_PARTY_NOTICES.txt for provenance and the recorded changes.
-/




namespace OAI

noncomputable section

namespace PiExponentSeshadri

namespace Frames
open CategoryTheory AlgebraicGeometry
@[simp] lemma coefficient_scalarEnd {X : Scheme} {M : X.Modules}
    (e : M ≅ O X) (a : Γ(X, ⊤)) :
    coefficient e (scalarEnd a ≫ e.inv) = a := by
  simp only [coefficient, Category.assoc, Iso.inv_hom_id, Category.comp_id,
    endValue_scalarEnd]
end Frames

namespace Geometry

section
open CategoryTheory AlgebraicGeometry TopologicalSpace
open scoped AlgebraicGeometry
open PiExponentSeshadri.Frames
variable {X : Scheme}

lemma affine_function_denom [IsAffine X] (a : Γ(X, ⊤))
    (f : Γ((X.basicOpen a).toScheme, ⊤)) :
    ∃ N : ℕ, ∀ n ≥ N, ∃ g : Γ(X, ⊤),
      (X.basicOpen a).ι.appTop g = f * (X.basicOpen a).ι.appTop a ^ n := by
  obtain ⟨N, g, hg⟩ := IsLocalization.Away.surj a f
  refine ⟨N, fun n hn => ⟨g * a ^ (n - N), ?_⟩⟩
  change algebraMap Γ(X, ⊤) Γ((X.basicOpen a).toScheme, ⊤) (g * a ^ (n - N)) =
    f * algebraMap Γ(X, ⊤) Γ((X.basicOpen a).toScheme, ⊤) a ^ n
  rw [map_mul, map_pow, ← hg, mul_assoc, ← pow_add, Nat.add_sub_of_le hn]

theorem local_affine_power_extension (U : X.Opens) [IsAffine U.toScheme]
    {M : X.Modules} (e : M.restrict U.ι ≅ structureSheaf U.toScheme)
    (s : GlobalSections X M)
    (f : Γ((U.toScheme.basicOpen (coefficient e (restrictSection U.ι s))).toScheme, ⊤)) :
    ∃ N : ℕ, ∀ n ≥ N, ∃ t : structureSheaf U.toScheme ⟶ (modulePow X M n).restrict U.ι,
      restrictSection (U.toScheme.basicOpen (coefficient e (restrictSection U.ι s))).ι t =
        scalarEnd f ≫ restrictSection
          (U.toScheme.basicOpen (coefficient e (restrictSection U.ι s))).ι
          (restrictSection U.ι (powerSection s n)) := by
  let a := coefficient e (restrictSection U.ι s)
  obtain ⟨N, hN⟩ := affine_function_denom a f
  refine ⟨N, fun n hn => ?_⟩
  obtain ⟨g, hg⟩ := hN n hn
  let eₙ := localPowerFrame U e n
  let c := endValue (powerRestrictionUnit U n).hom
  let φ := (U.toScheme.basicOpen a).ι
  refine ⟨scalarEnd (c * g) ≫ eₙ.inv, ?_⟩
  apply coefficient_injective (restrictFrame φ eₙ)
  calc
    _ = φ.appTop (c * g) := (coefficient_restrict φ eₙ _).trans
      (congrArg φ.appTop (coefficient_scalarEnd eₙ (c * g)))
    _ = φ.appTop c * φ.appTop g := map_mul φ.appTop.hom c g
    _ = φ.appTop c * (f * φ.appTop a ^ n) := congrArg (φ.appTop c * ·) hg
    _ = f * φ.appTop (c * a ^ n) := by
      simp only [map_mul, map_pow]
      ring
    _ = f * φ.appTop (coefficient eₙ (restrictSection U.ι (powerSection s n))) :=
      congrArg (fun z => f * φ.appTop z) (local_powerSection_coefficient U e s n).symm
    _ = endValue (scalarEnd f) * coefficient (restrictFrame φ eₙ)
        (restrictSection φ (restrictSection U.ι (powerSection s n))) :=
      congrArg₂ (· * ·) (endValue_scalarEnd f).symm (coefficient_restrict φ eₙ _).symm
    _ = _ := (coefficient_precompose _ _ _).symm

end

section
open CategoryTheory AlgebraicGeometry TopologicalSpace TopologicalSpace.Opens
open scoped AlgebraicGeometry
variable {X : Scheme}

theorem LineBundle.glue_dense_subopens [IsIntegral X] (L : LineBundle X)
    (D : X.Opens) {ι : Type*} [Nonempty ι] (U W : ι → X.Opens)
    (hcover : (⊤ : X.Opens) ≤ iSup U)
    (hWU : ∀ i, W i ≤ U i) (hWD : ∀ i, W i ≤ D)
    (hW : ∀ i, (W i : Set X).Nonempty)
    (sf : ∀ i, Γ(L.sheaf, U i)) (target : Γ(L.sheaf, D))
    (heq : ∀ i, L.sheaf.presheaf.map (homOfLE (hWU i)).op (sf i) =
      L.sheaf.presheaf.map (homOfLE (hWD i)).op target) :
    ∃! g : Γ(L.sheaf, ⊤),
      (∀ i, L.sheaf.presheaf.map (homOfLE le_top).op g = sf i) ∧
        L.sheaf.presheaf.map (homOfLE le_top).op g = target := by
  let F : TopCat.Sheaf AddCommGrpCat X := ⟨L.sheaf.presheaf, L.sheaf.isSheaf⟩
  have hc : TopCat.Presheaf.IsCompatible L.sheaf.presheaf U sf := by
    intro i j
    have : Nonempty (W i ⊓ W j : X.Opens) := by
      obtain ⟨x, hi, hj⟩ := nonempty_preirreducible_inter (W i).isOpen (W j).isOpen
        (hW i) (hW j)
      exact ⟨⟨x, hi, hj⟩⟩
    apply L.restriction_injective (homOfLE
      (show W i ⊓ W j ≤ U i ⊓ U j from fun _ hx => ⟨hWU i hx.1, hWU j hx.2⟩))
    have hi := congrArg (L.sheaf.presheaf.map (infLELeft (W i) (W j)).op) (heq i)
    have hj := congrArg (L.sheaf.presheaf.map (infLERight (W i) (W j)).op) (heq j)
    simp only [← ConcreteCategory.comp_apply, ← Functor.map_comp] at hi hj ⊢
    exact hi.trans hj.symm
  obtain ⟨g, hg, hguniq⟩ := F.existsUnique_gluing' U ⊤
    (fun _ => homOfLE le_top) hcover sf hc
  have hD : L.sheaf.presheaf.map (homOfLE (show D ≤ ⊤ from le_top)).op g = target := by
    obtain ⟨i⟩ := ‹Nonempty ι›
    have : Nonempty (W i) := by obtain ⟨x, hx⟩ := hW i; exact ⟨⟨x, hx⟩⟩
    apply L.restriction_injective (homOfLE (hWD i))
    have hi : L.sheaf.presheaf.map (homOfLE (show U i ≤ ⊤ from le_top)).op g = sf i := hg i
    have hgi := congrArg (L.sheaf.presheaf.map (homOfLE (hWU i)).op) hi
    simp only [← ConcreteCategory.comp_apply, ← Functor.map_comp] at hgi ⊢
    exact hgi.trans (heq i)
  exact ⟨g, ⟨hg, hD⟩, fun g' h' => hguniq g' h'.1⟩

end

open CategoryTheory AlgebraicGeometry TopologicalSpace TopologicalSpace.Opens
open scoped AlgebraicGeometry
open PiExponentSeshadri.Frames
variable {X : Scheme}

theorem LineBundle.finite_cover_power_extension [IsIntegral X] (L : LineBundle X)
    {ι : Type*} [Fintype ι] [Nonempty ι] (U : ι → X.Opens)
    (hcover : (⊤ : X.Opens) ≤ iSup U)
    (haff : ∀ i, IsAffine (U i).toScheme)
    (hU : ∀ i, (U i : Set X).Nonempty)
    (e : ∀ i, L.sheaf.restrict (U i).ι ≅ structureSheaf (U i).toScheme)
    (s : GlobalSections X L.sheaf) (hD : (sectionOpen X s : Set X).Nonempty)
    (f : Γ(X, sectionOpen X s)) :
    ∃ N : ℕ, ∀ n ≥ N, ∃ t : GlobalSections X (modulePow X L.sheaf n),
      t.app (sectionOpen X s) (1 : Γ(X, sectionOpen X s)) =
        f • (powerSection s n).app (sectionOpen X s) (1 : Γ(X, sectionOpen X s)) := by
  classical
  let D := sectionOpen X s
  let V (i : ι) := (U i).toScheme.basicOpen (coefficient (e i) (restrictSection (U i).ι s))
  let W (i : ι) := (U i).ι ''ᵁ V i
  have hV (i : ι) : V i = (U i).ι ⁻¹ᵁ D :=
    (preimage_isoOpen s (U i).ι (e i)).symm
  have hW_eq (i : ι) : W i = U i ⊓ D := by
    simp only [W, hV, Scheme.Hom.image_preimage_eq_opensRange_inf, Scheme.Opens.opensRange_ι]
  have hWU (i : ι) : W i ≤ U i := (U i).ι_image_le (V i)
  have hWD (i : ι) : W i ≤ D := (hW_eq i).le.trans inf_le_right
  have hW (i : ι) : (W i : Set X).Nonempty := by
    rw [hW_eq]
    exact nonempty_preirreducible_inter (U i).isOpen D.isOpen (hU i) hD
  let fi (i : ι) : Γ((V i).toScheme, ⊤) :=
    (V i).topIso.inv (((U i).ι.appIso (V i)).hom (X.presheaf.map (homOfLE (hWD i)).op f))
  have hf (i : ι) : ∃ N : ℕ, ∀ n ≥ N,
      ∃ t : structureSheaf (U i).toScheme ⟶ (modulePow X L.sheaf n).restrict (U i).ι,
        restrictSection (V i).ι t = scalarEnd (fi i) ≫
          restrictSection (V i).ι (restrictSection (U i).ι (powerSection s n)) := by
    let := haff i
    exact local_affine_power_extension (U i) (e i) s (fi i)
  choose N hN using hf
  refine ⟨Finset.univ.sup N, fun n hn => ?_⟩
  have hn' (i : ι) : N i ≤ n := (Finset.le_sup (f := N) (Finset.mem_univ i)).trans hn
  choose t ht using fun i => hN i n (hn' i)
  let M := modulePow X L.sheaf n
  let target : Γ((L.pow n).sheaf, D) := f • (powerSection s n).app D (1 : Γ(X, D))
  have heq (i : ι) : M.presheaf.map (homOfLE (hWU i)).op (openSectionEquiv M (U i) (t i)) =
      M.presheaf.map (homOfLE (hWD i)).op target := by
    have hi := image_section_extension M (U i) (restrictSection (U i).ι (powerSection s n))
      (t i) (V i) (fi i) (ht i)
    have hfi : ((U i).ι.appIso (V i)).inv ((V i).topIso.hom (fi i)) =
        X.presheaf.map (homOfLE (hWD i)).op f := by
      dsimp only [fi]
      rw [Iso.inv_hom_id_apply, Iso.hom_inv_id_apply]
    rw [hfi] at hi
    have hp : openSectionEquiv M (U i) (restrictSection (U i).ι (powerSection s n)) =
        (powerSection s n).app (U i) (1 : Γ(X, U i)) := openSectionEquiv_restrict _ _
    have hs : M.presheaf.map (homOfLE (hWU i)).op
        (openSectionEquiv M (U i) (restrictSection (U i).ι (powerSection s n))) =
        (powerSection s n).app (W i) (1 : Γ(X, W i)) :=
      (congrArg (M.presheaf.map (homOfLE (hWU i)).op) hp).trans
        (section_value_natural (powerSection s n) (homOfLE (hWU i)))
    have hr : M.presheaf.map (homOfLE (hWD i)).op target =
        X.presheaf.map (homOfLE (hWD i)).op f •
          (powerSection s n).app (W i) (1 : Γ(X, W i)) :=
      (M.map_smul (homOfLE (hWD i)) f _).trans
        (congrArg (X.presheaf.map (homOfLE (hWD i)).op f • ·)
          (section_value_natural (powerSection s n) (homOfLE (hWD i))))
    exact (hi.trans (congrArg (X.presheaf.map (homOfLE (hWD i)).op f • ·) hs)).trans hr.symm
  obtain ⟨g, hg, -⟩ := (L.pow n).glue_dense_subopens D U W hcover hWU hWD hW
    (fun i => openSectionEquiv M (U i) (t i)) target heq
  refine ⟨(moduleSectionEquiv M).symm g, ?_⟩
  have H := section_value_natural ((moduleSectionEquiv M).symm g)
    (homOfLE (show D ≤ ⊤ from le_top))
  have Htop : ((moduleSectionEquiv M).symm g).app ⊤ (1 : Γ(X, ⊤)) = g :=
    (moduleSectionEquiv M).apply_symm_apply g
  rw [Htop] at H
  exact H.symm.trans hg.2

end Geometry

namespace InvertibleLocal
open CategoryTheory AlgebraicGeometry
open PiExponentSeshadri.Geometry
variable {X Y : Scheme}

def frameOfLE (M : Y.Modules) {U V : Y.Opens} (h : V ≤ U)
    (e : M.restrict U.ι ≅ structureSheaf U.toScheme) :
    M.restrict V.ι ≅ structureSheaf V.toScheme := by
  let e' := (Scheme.Modules.restrictFunctorComp (Y.homOfLE h) U.ι).app M ≪≫
    (Scheme.Modules.restrictFunctor (Y.homOfLE h)).mapIso e ≪≫
    Scheme.Modules.restrictUnitIso (Y.homOfLE h)
  simp only [Y.homOfLE_ι h] at e'
  exact e'

lemma affine_frame (J : LineBundle Y) (y : Y) :
    ∃ U : Y.affineOpens, y ∈ U.1 ∧
      Nonempty (J.sheaf.restrict U.1.ι ≅ structureSheaf U.1.toScheme) := by
  obtain ⟨V, hyV, ⟨e⟩⟩ := J.locallyRankOne y
  obtain ⟨U, hU, hyU, hUV⟩ := exists_isAffineOpen_mem_and_subset hyV
  exact ⟨⟨U, hU⟩, hyU, ⟨frameOfLE J.sheaf hUV e⟩⟩

end InvertibleLocal

namespace Geometry
open CategoryTheory AlgebraicGeometry TopologicalSpace TopologicalSpace.Opens
open scoped AlgebraicGeometry
open PiExponentSeshadri.Frames
variable {X : Scheme}

theorem LineBundle.power_extension [IsIntegral X] [CompactSpace X] (L : LineBundle X)
    (s : GlobalSections X L.sheaf) (hD : (sectionOpen X s : Set X).Nonempty)
    (f : Γ(X, sectionOpen X s)) :
    ∃ N : ℕ, ∀ n ≥ N, ∃ t : GlobalSections X (modulePow X L.sheaf n),
      t.app (sectionOpen X s) (1 : Γ(X, sectionOpen X s)) =
        f • (powerSection s n).app (sectionOpen X s) (1 : Γ(X, sectionOpen X s)) := by
  classical
  choose U hUx he using InvertibleLocal.affine_frame L
  obtain ⟨I, hI⟩ := isCompact_univ.elim_finite_subcover
    (fun x => (U x).1 : X → Set X) (fun x => (U x).1.isOpen)
    (by intro x _; exact Set.mem_iUnion.mpr ⟨x, hUx x⟩)
  have hic (x : X) : ∃ i ∈ I, x ∈ (U i).1 := by
    obtain ⟨i, hi⟩ := Set.mem_iUnion.mp (hI (show x ∈ Set.univ from trivial))
    obtain ⟨hi, hx⟩ := Set.mem_iUnion.mp hi
    exact ⟨i, hi, hx⟩
  have : Nonempty I := by
    obtain ⟨x, -⟩ := hD
    obtain ⟨i, hi, -⟩ := hic x
    exact ⟨⟨i, hi⟩⟩
  exact L.finite_cover_power_extension (fun i : I => (U i.val).1)
    (by
      intro x _
      obtain ⟨i, hi, hx⟩ := hic x
      exact TopologicalSpace.Opens.mem_iSup.mpr ⟨⟨i, hi⟩, hx⟩)
    (fun i => (U i.val).2) (fun i => ⟨i.val, hUx i.val⟩)
    (fun i => Classical.choice (he i.val)) s hD f

end Geometry

end PiExponentSeshadri

end

end OAI
end Source0024

section Source0025
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
end Source0025

section Source0026
/-
Modification notice for the LogTwo project.
Derived from openai/math (Apache-2.0), revision adc7f1241b42e322a6451854ab7e4b4c146bf78a.
Original source: lean/OAI/NumberTheory/PiExponent/Approximation/FrameSubopens.lean
Changes: Convert module/import declarations to the Lean 4.34 public module format.
See ../../../../../THIRD_PARTY_NOTICES.txt for provenance and the recorded changes.
-/




namespace OAI

namespace PiExponentSeshadri.Frames
noncomputable section
open AlgebraicGeometry CategoryTheory TopologicalSpace
variable {X : Scheme} {M : X.Modules}

def restrictOpenFrame {U V : X.Opens} (h : V ≤ U) (e : M.restrict U.ι ≅ O U.toScheme) :
    M.restrict V.ι ≅ O V.toScheme :=
  ((Scheme.Modules.restrictFunctorCongr (X.homOfLE_ι h)).app M).symm ≪≫
    (Scheme.Modules.restrictFunctorComp (X.homOfLE h) U.ι).app M ≪≫
      restrictFrame (X.homOfLE h) e

lemma restrictOpenFrame_coefficient_global {U V : X.Opens} (h : V ≤ U)
    (e : M.restrict U.ι ≅ O U.toScheme) (s : O X ⟶ M) :
    coefficient (restrictOpenFrame h e) (restrictSection V.ι s) =
      (X.homOfLE h).appTop (coefficient e (restrictSection U.ι s)) := by
  unfold restrictOpenFrame
  rw [coefficient_transport]
  rw [← restrictSection_congr (X.homOfLE_ι h) s, Category.assoc]
  have he : (Scheme.Modules.restrictFunctorCongr (X.homOfLE_ι h)).hom.app M ≫
      ((Scheme.Modules.restrictFunctorCongr (X.homOfLE_ι h)).app M).symm.hom = 𝟙 _ :=
    Iso.hom_inv_id ((Scheme.Modules.restrictFunctorCongr (X.homOfLE_ι h)).app M)
  rw [he, Category.comp_id]
  exact coefficient_restrict_comp (X.homOfLE h) U.ι e s

lemma frameChange_restrictOpenFrame {U V W : X.Opens} (hWU : W ≤ U) (hWV : W ≤ V)
    (e : M.restrict U.ι ≅ O U.toScheme) (f : M.restrict V.ι ≅ O V.toScheme)
    (s : O X ⟶ M) (hs : coefficient e (restrictSection U.ι s) = 1) :
    (frameChange (restrictOpenFrame hWU e) (restrictOpenFrame hWV f) : Γ(W.toScheme,⊤)) =
      (X.homOfLE hWV).appTop (coefficient f (restrictSection V.ι s)) := by
  have h := coefficient_change (restrictOpenFrame hWU e) (restrictOpenFrame hWV f)
    (restrictSection W.ι s)
  rw [restrictOpenFrame_coefficient_global, restrictOpenFrame_coefficient_global,
    hs, map_one, mul_one] at h
  exact h.symm

end
end PiExponentSeshadri.Frames

end OAI
end Source0026

section Source0027
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
end Source0027

section Source0028
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
end Source0028

section Source0029
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
end Source0029

section Source0030
/-
Modification notice for the LogTwo project.
Derived from openai/math (Apache-2.0), revision adc7f1241b42e322a6451854ab7e4b4c146bf78a.
Original source: lean/OAI/NumberTheory/PiExponent/Approximation/LinePullbackPowers.lean
Changes: Convert module/import declarations to the Lean 4.34 public module format.
See ../../../../../THIRD_PARTY_NOTICES.txt for provenance and the recorded changes.
-/




namespace OAI

noncomputable section

namespace PiExponentSeshadri.PullbackTensor
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite MonoidalCategory
open PiExponentSeshadri.Geometry PiExponentSeshadri.TensorPure PiExponentSeshadri.Frames
variable {X Y : Scheme.{0}} (f : X ⟶ Y) (U : Y.Opens)

def hom (M N : Y.Modules) : (Scheme.Modules.pullback f).obj (moduleTensor Y M N) ⟶
    moduleTensor X ((Scheme.Modules.pullback f).obj M) ((Scheme.Modules.pullback f).obj N) :=
  ((Scheme.Modules.pullbackPushforwardAdjunction f).homEquiv _ _).symm
    (moduleTensorMap ((Scheme.Modules.pullbackPushforwardAdjunction f).unit.app M)
      ((Scheme.Modules.pullbackPushforwardAdjunction f).unit.app N) ≫
      PushforwardTensor.hom f _ _)

lemma unit_hom (M N : Y.Modules) :
    (Scheme.Modules.pullbackPushforwardAdjunction f).unit.app (moduleTensor Y M N) ≫
      (Scheme.Modules.pushforward f).map (hom f M N) =
    moduleTensorMap ((Scheme.Modules.pullbackPushforwardAdjunction f).unit.app M)
      ((Scheme.Modules.pullbackPushforwardAdjunction f).unit.app N) ≫
      PushforwardTensor.hom f _ _ :=
  ((Scheme.Modules.pullbackPushforwardAdjunction f).homEquiv _ _).apply_symm_apply _

@[reassoc] lemma naturality {M N P Q : Y.Modules} (a : M ⟶ P) (b : N ⟶ Q) :
    (Scheme.Modules.pullback f).map (moduleTensorMap a b) ≫ hom f P Q =
      hom f M N ≫ moduleTensorMap ((Scheme.Modules.pullback f).map a)
        ((Scheme.Modules.pullback f).map b) := by
  apply ((Scheme.Modules.pullbackPushforwardAdjunction f).homEquiv _ _).injective
  rw [Adjunction.homEquiv_naturality_left,Adjunction.homEquiv_naturality_right]
  simp only [hom,Equiv.apply_symm_apply]
  rw [← Category.assoc,← moduleTensorMap_comp]
  rw [Category.assoc,← PushforwardTensor.naturality,← Category.assoc,← moduleTensorMap_comp]
  rw [← (Scheme.Modules.pullbackPushforwardAdjunction f).unit_naturality,
    ← (Scheme.Modules.pullbackPushforwardAdjunction f).unit_naturality]

lemma unit_pure_structure (Z : Scheme.{0}) (U : Z.Opens)
    (a b : (O Z).val.obj (op U)) :
    (moduleTensorUnit (O Z)).hom.app U (pure (O Z) (O Z) U a b) =
      (show Γ(Z,U) from a) * (show Γ(Z,U) from b) :=
  TensorPure.unit_pure (O Z) U a b

lemma unit_compatibility :
    hom f (O Y) (O Y) ≫
      (moduleTensorIso (pullbackUnitIso f) (pullbackUnitIso f)).hom ≫
      (moduleTensorUnit (O X)).hom =
    (Scheme.Modules.pullback f).map (moduleTensorUnit (O Y)).hom ≫
      (pullbackUnitIso f).hom := by
  apply ((Scheme.Modules.pullbackPushforwardAdjunction f).homEquiv _ _).injective
  let adj := Scheme.Modules.pullbackPushforwardAdjunction f
  have hl := adj.homEquiv_naturality_left (moduleTensorUnit (O Y)).hom
    (pullbackUnitIso f).hom
  have hr := adj.homEquiv_naturality_right (hom f (O Y) (O Y))
    ((moduleTensorIso (pullbackUnitIso f) (pullbackUnitIso f)).hom ≫
      (moduleTensorUnit (O X)).hom)
  have hu := congrArg (fun q => (moduleTensorUnit (O Y)).hom ≫ q)
    (pullbackUnit_adjunction f)
  refine hr.trans (Eq.trans ?_ (hu.symm.trans hl.symm))
  simp only [adj, hom, Equiv.apply_symm_apply]
  apply TensorPure.hom_ext
  intro U a b
  change (moduleTensorUnit (O X)).hom.app (f ⁻¹ᵁ U)
    ((moduleTensorMap (pullbackUnitIso f).hom (pullbackUnitIso f).hom).app (f ⁻¹ᵁ U)
      ((PushforwardTensor.hom f _ _).app U ((moduleTensorMap _ _).app U
        (pure (O Y) (O Y) U a b)))) =
    (f.app U) ((moduleTensorUnit (O Y)).hom.app U (pure (O Y) (O Y) U a b))
  let η := (Scheme.Modules.pullbackPushforwardAdjunction f).unit.app (O Y)
  let m := η.app U a
  let n := η.app U b
  have h₁ := congrArg (fun z => (moduleTensorUnit (O X)).hom.app (f ⁻¹ᵁ U)
    ((moduleTensorMap (pullbackUnitIso f).hom (pullbackUnitIso f).hom).app (f ⁻¹ᵁ U)
      ((PushforwardTensor.hom f _ _).app U z)))
    (TensorPure.map_pure η η U a b)
  have h₂ := congrArg (fun z => (moduleTensorUnit (O X)).hom.app (f ⁻¹ᵁ U)
    ((moduleTensorMap (pullbackUnitIso f).hom (pullbackUnitIso f).hom).app (f ⁻¹ᵁ U) z))
    (PushforwardTensor.hom_pure f ((Scheme.Modules.pullback f).obj (O Y))
      ((Scheme.Modules.pullback f).obj (O Y)) U m n)
  have h₃ := congrArg (fun z => (moduleTensorUnit (O X)).hom.app (f ⁻¹ᵁ U) z)
    (TensorPure.map_pure (pullbackUnitIso f).hom (pullbackUnitIso f).hom (f ⁻¹ᵁ U) m n)
  refine h₁.trans (h₂.trans (h₃.trans ((unit_pure_structure X (f ⁻¹ᵁ U) _ _).trans ?_)))
  have hy := congrArg (fun z => (f.app U) z) (unit_pure_structure Y U a b)
  refine Eq.trans ?_ hy.symm
  have hu := congrArg (fun q => q.app U) (pullbackUnit_adjunction f)
  have ha := congrArg (fun q => q a) hu
  have hb := congrArg (fun q => q b) hu
  change (pullbackUnitIso f).hom.app (f ⁻¹ᵁ U)
    (((Scheme.Modules.pullbackPushforwardAdjunction f).unit.app (O Y)).app U a) =
    (f.app U) a at ha
  change (pullbackUnitIso f).hom.app (f ⁻¹ᵁ U)
    (((Scheme.Modules.pullbackPushforwardAdjunction f).unit.app (O Y)).app U b) =
    (f.app U) b at hb
  exact (congrArg₂ (fun a b : Γ(X,f ⁻¹ᵁ U) => a * b) ha hb).trans
    (map_mul (f.app U).hom (show Γ(Y,U) from a) (show Γ(Y,U) from b)).symm

instance unit_isIso : IsIso (hom f (O Y) (O Y)) := by
  let e := (Scheme.Modules.pullback f).mapIso (moduleTensorUnit (O Y)) ≪≫
    pullbackUnitIso f
  let d := moduleTensorIso (pullbackUnitIso f) (pullbackUnitIso f) ≪≫
    moduleTensorUnit (O X)
  have hi : IsIso (hom f (O Y) (O Y) ≫ d.hom) := by
    change IsIso (hom f (O Y) (O Y) ≫
      (moduleTensorIso (pullbackUnitIso f) (pullbackUnitIso f)).hom ≫
      (moduleTensorUnit (O X)).hom)
    rw [unit_compatibility]
    exact e.isIso_hom
  let hd : IsIso (C := X.Modules) d.hom := d.isIso_hom
  exact (@isIso_comp_right_iff X.Modules _ _ _ _ _ _ hd).mp hi

lemma open_transpose (M : Y.Modules) :
    (Scheme.Modules.pullbackPushforwardAdjunction (f ∣_ U)).homEquiv _ _
      ((OpenBaseChange.leftSquare f U).hom.app M) =
    (Scheme.Modules.restrictFunctor U.ι).map
      ((Scheme.Modules.pullbackPushforwardAdjunction f).unit.app M) ≫
        (OpenBaseChange.iso f U ((Scheme.Modules.pullback f).obj M)).hom :=
  (OpenBaseChange.unit_compatibility f U M).symm

lemma restrict_compatibility (M N : Y.Modules) :
    (OpenBaseChange.leftSquare f U).hom.app (moduleTensor Y M N) ≫
      (Scheme.Modules.restrictFunctor (f ⁻¹ᵁ U).ι).map (hom f M N) ≫
      (moduleTensorRestrict (f ⁻¹ᵁ U) ((Scheme.Modules.pullback f).obj M)
        ((Scheme.Modules.pullback f).obj N)).hom =
    (Scheme.Modules.pullback (f ∣_ U)).map (moduleTensorRestrict U M N).hom ≫
      hom (f ∣_ U) (M.restrict U.ι) (N.restrict U.ι) ≫
      moduleTensorMap ((OpenBaseChange.leftSquare f U).hom.app M)
        ((OpenBaseChange.leftSquare f U).hom.app N) := by
  apply ((Scheme.Modules.pullbackPushforwardAdjunction (f ∣_ U)).homEquiv _ _).injective
  conv_rhs => rw [Adjunction.homEquiv_naturality_left,
    Adjunction.homEquiv_naturality_right]
  conv_lhs => rw [Adjunction.homEquiv_naturality_right]
  rw [open_transpose]
  have ht : (Scheme.Modules.pullbackPushforwardAdjunction (f ∣_ U)).homEquiv _ _
      (hom (f ∣_ U) (M.restrict U.ι) (N.restrict U.ι)) =
      moduleTensorMap ((Scheme.Modules.pullbackPushforwardAdjunction (f ∣_ U)).unit.app (M.restrict U.ι))
        ((Scheme.Modules.pullbackPushforwardAdjunction (f ∣_ U)).unit.app (N.restrict U.ι)) ≫
        PushforwardTensor.hom (f ∣_ U) _ _ := Equiv.apply_symm_apply _ _
  rw [ht]
  simp only [Functor.map_comp, Category.assoc]
  rw [← OpenBaseChange.naturality_assoc]
  rw [← Functor.map_comp_assoc, unit_hom, Functor.map_comp]
  simp only [Category.assoc]
  rw [OpenBaseChange.tensor_square]
  rw [← Category.assoc]
  refine (congrArg (fun q => q ≫
    moduleTensorMap (OpenBaseChange.iso f U ((Scheme.Modules.pullback f).obj M)).hom
      (OpenBaseChange.iso f U ((Scheme.Modules.pullback f).obj N)).hom ≫
    PushforwardTensor.hom (f ∣_ U)
      (((Scheme.Modules.pullback f).obj M).restrict (f ⁻¹ᵁ U).ι)
      (((Scheme.Modules.pullback f).obj N).restrict (f ⁻¹ᵁ U).ι))
    (TensorPure.restrict_map U
      ((Scheme.Modules.pullbackPushforwardAdjunction f).unit.app M)
      ((Scheme.Modules.pullbackPushforwardAdjunction f).unit.app N))).trans ?_
  simp only [Category.assoc]
  rw [← moduleTensorMap_comp_assoc]
  rw [OpenBaseChange.unit_compatibility,OpenBaseChange.unit_compatibility]
  rw [moduleTensorMap_comp]
  simp only [Category.assoc]
  exact congrArg (fun q => (moduleTensorRestrict U M N).hom ≫
    moduleTensorMap ((Scheme.Modules.pullbackPushforwardAdjunction (f ∣_ U)).unit.app (M.restrict U.ι))
      ((Scheme.Modules.pullbackPushforwardAdjunction (f ∣_ U)).unit.app (N.restrict U.ι)) ≫ q)
    (PushforwardTensor.naturality (f ∣_ U)
      ((OpenBaseChange.leftSquare f U).hom.app M) ((OpenBaseChange.leftSquare f U).hom.app N))

lemma framed_isIso (M N : Y.Modules) (e : M ≅ O Y) (d : N ≅ O Y) :
    IsIso (hom f M N) := by
  have h := naturality f e.hom d.hom
  have : IsIso ((Scheme.Modules.pullback f).map (moduleTensorMap e.hom d.hom) ≫
      hom f (O Y) (O Y)) := by
    change IsIso ((Scheme.Modules.pullback f).map (moduleTensorIso e d).hom ≫ _)
    infer_instance
  have : IsIso (moduleTensorMap ((Scheme.Modules.pullback f).map e.hom)
      ((Scheme.Modules.pullback f).map d.hom)) := by
    change IsIso (moduleTensorIso ((Scheme.Modules.pullback f).mapIso e)
      ((Scheme.Modules.pullback f).mapIso d)).hom
    infer_instance
  have hi : IsIso (hom f M N ≫ moduleTensorMap ((Scheme.Modules.pullback f).map e.hom)
      ((Scheme.Modules.pullback f).map d.hom)) := h ▸ inferInstance
  exact (isIso_comp_right_iff _ _).mp hi

instance power_step_isIso (L : LineBundle Y) (n : ℕ) :
    IsIso (hom f L.sheaf (L.pow n).sheaf) := by
  apply PiExponentSeshadri.SectionOpens.isIso_of_locally_isIso
  intro x
  obtain ⟨U,hx,⟨e⟩⟩ := L.locallyRankOne (f x)
  let d := modulePowFrame U e n
  refine ⟨f ⁻¹ᵁ U,hx,?_⟩
  let : IsIso (hom (f ∣_ U) (L.sheaf.restrict U.ι) ((L.pow n).sheaf.restrict U.ι)) :=
    framed_isIso (f ∣_ U) _ _ e d
  have : IsIso (moduleTensorMap ((OpenBaseChange.leftSquare f U).hom.app L.sheaf)
      ((OpenBaseChange.leftSquare f U).hom.app (L.pow n).sheaf)) := by
    change IsIso (moduleTensorIso ((OpenBaseChange.leftSquare f U).app L.sheaf)
      ((OpenBaseChange.leftSquare f U).app (L.pow n).sheaf)).hom
    infer_instance
  have h := restrict_compatibility f U L.sheaf (L.pow n).sheaf
  have : IsIso ((OpenBaseChange.leftSquare f U).hom.app (moduleTensor Y L.sheaf (L.pow n).sheaf) ≫
      (Scheme.Modules.restrictFunctor (f ⁻¹ᵁ U).ι).map (hom f L.sheaf (L.pow n).sheaf) ≫
      (moduleTensorRestrict (f ⁻¹ᵁ U) ((Scheme.Modules.pullback f).obj L.sheaf)
        ((Scheme.Modules.pullback f).obj (L.pow n).sheaf)).hom) := by rw [h]; infer_instance
  have hi : IsIso ((Scheme.Modules.restrictFunctor (f ⁻¹ᵁ U).ι).map
      (hom f L.sheaf (L.pow n).sheaf) ≫
      (moduleTensorRestrict (f ⁻¹ᵁ U) ((Scheme.Modules.pullback f).obj L.sheaf)
        ((Scheme.Modules.pullback f).obj (L.pow n).sheaf)).hom) :=
    (isIso_comp_left_iff ((OpenBaseChange.leftSquare f U).hom.app
      (moduleTensor Y L.sheaf (L.pow n).sheaf)) _).mp inferInstance
  exact (isIso_comp_right_iff _ _).mp hi

def powIso (L : LineBundle Y) : ∀ n : ℕ,
    (Scheme.Modules.pullback f).obj (L.pow n).sheaf ≅ ((L.pullback f).pow n).sheaf
  | 0 => pullbackUnitIso f
  | n+1 => @asIso _ _ _ _ (hom f L.sheaf (L.pow n).sheaf) (power_step_isIso f L n) ≪≫
      moduleTensorIso (Iso.refl _) (powIso L n)

end PiExponentSeshadri.PullbackTensor

end

end OAI
end Source0030

section Source0031
/-
Modification notice for the LogTwo project.
Derived from openai/math (Apache-2.0), revision adc7f1241b42e322a6451854ab7e4b4c146bf78a.
Original source: lean/OAI/NumberTheory/PiExponent/Geometry/LineBundleProduct.lean
Changes: Convert module/import declarations to the Lean 4.34 public module format.
See ../../../../../THIRD_PARTY_NOTICES.txt for provenance and the recorded changes.
-/




namespace OAI

noncomputable section

namespace PiExponentSeshadri

namespace Geometry
open AlgebraicGeometry CategoryTheory TopologicalSpace
open PiExponentSeshadri.Frames
variable {X : Scheme.{0}}

theorem common_affine_frames (L M : LineBundle X) (x : X) :
    ∃ U : X.affineOpens, x ∈ U.1 ∧
      Nonempty (L.sheaf.restrict U.1.ι ≅ structureSheaf U.1.toScheme) ∧
      Nonempty (M.sheaf.restrict U.1.ι ≅ structureSheaf U.1.toScheme) := by
  obtain ⟨U, hxU, ⟨e⟩⟩ := L.locallyRankOne x
  obtain ⟨V, hxV, ⟨d⟩⟩ := M.locallyRankOne x
  obtain ⟨W, hW, hxW, hWUV⟩ := exists_isAffineOpen_mem_and_subset
    (show x ∈ U ⊓ V from ⟨hxU, hxV⟩)
  exact ⟨⟨W, hW⟩, hxW,
    ⟨restrictOpenFrame (fun _ hx => (hWUV hx).1) e⟩,
    ⟨restrictOpenFrame (fun _ hx => (hWUV hx).2) d⟩⟩

def LineBundle.tensor (L M : LineBundle X) : LineBundle X where
  sheaf := moduleTensor X L.sheaf M.sheaf
  locallyRankOne x := by
    obtain ⟨U, hx, ⟨e⟩, ⟨d⟩⟩ := common_affine_frames L M x
    exact ⟨U.1, hx, ⟨moduleTensorRestrict U.1 L.sheaf M.sheaf ≪≫
      moduleTensorIso e d ≪≫ moduleTensorUnit (structureSheaf U.1.toScheme)⟩⟩

end Geometry

namespace PullbackTensor
open AlgebraicGeometry CategoryTheory TopologicalSpace
open PiExponentSeshadri.Geometry PiExponentSeshadri.Frames
variable {X Y : Scheme.{0}} (f : X ⟶ Y)

instance line_isIso (L M : LineBundle Y) : IsIso (hom f L.sheaf M.sheaf) := by
  apply PiExponentSeshadri.SectionOpens.isIso_of_locally_isIso
  intro x
  obtain ⟨U, hx, ⟨e⟩, ⟨d⟩⟩ := common_affine_frames L M (f x)
  refine ⟨f ⁻¹ᵁ U.1, hx, ?_⟩
  have := framed_isIso (f ∣_ U.1) _ _ e d
  have : IsIso (moduleTensorMap ((OpenBaseChange.leftSquare f U.1).hom.app L.sheaf)
      ((OpenBaseChange.leftSquare f U.1).hom.app M.sheaf)) := by
    change IsIso (moduleTensorIso ((OpenBaseChange.leftSquare f U.1).app L.sheaf)
      ((OpenBaseChange.leftSquare f U.1).app M.sheaf)).hom
    infer_instance
  have h := restrict_compatibility f U.1 L.sheaf M.sheaf
  have : IsIso ((OpenBaseChange.leftSquare f U.1).hom.app (moduleTensor Y L.sheaf M.sheaf) ≫
      (Scheme.Modules.restrictFunctor (f ⁻¹ᵁ U.1).ι).map (hom f L.sheaf M.sheaf) ≫
      (moduleTensorRestrict (f ⁻¹ᵁ U.1) ((Scheme.Modules.pullback f).obj L.sheaf)
        ((Scheme.Modules.pullback f).obj M.sheaf)).hom) := by rw [h]; infer_instance
  have hi : IsIso ((Scheme.Modules.restrictFunctor (f ⁻¹ᵁ U.1).ι).map (hom f L.sheaf M.sheaf) ≫
      (moduleTensorRestrict (f ⁻¹ᵁ U.1) ((Scheme.Modules.pullback f).obj L.sheaf)
        ((Scheme.Modules.pullback f).obj M.sheaf)).hom) :=
    (isIso_comp_left_iff ((OpenBaseChange.leftSquare f U.1).hom.app
      (moduleTensor Y L.sheaf M.sheaf)) _).mp inferInstance
  exact (isIso_comp_right_iff _ _).mp hi

def iso (L M : LineBundle Y) :
    (Scheme.Modules.pullback f).obj (L.tensor M).sheaf ≅
      ((L.pullback f).tensor (M.pullback f)).sheaf :=
  @asIso _ _ _ _ (hom f L.sheaf M.sheaf) (line_isIso f L M)

end PullbackTensor

end PiExponentSeshadri

end

end OAI
end Source0031

section Source0032
/-
Modification notice for the LogTwo project.
Derived from openai/math (Apache-2.0), revision adc7f1241b42e322a6451854ab7e4b4c146bf78a.
Original source: lean/OAI/NumberTheory/PiExponent/Approximation/TensorSectionOpen.lean
Changes: Convert module/import declarations to the Lean 4.34 public module format.
See ../../../../../THIRD_PARTY_NOTICES.txt for provenance and the recorded changes.
-/




namespace OAI

noncomputable section

namespace PiExponentSeshadri

namespace Geometry
open AlgebraicGeometry CategoryTheory
open PiExponentSeshadri.Frames
variable {X : Scheme.{0}}
def tensorFrame (L M : LineBundle X) (U : X.Opens)
    (e : L.sheaf.restrict U.ι ≅ O U.toScheme)
    (f : M.sheaf.restrict U.ι ≅ O U.toScheme) :
    (L.tensor M).sheaf.restrict U.ι ≅ O U.toScheme :=
  moduleTensorRestrict U L.sheaf M.sheaf ≪≫ moduleTensorIso e f ≪≫
    moduleTensorUnit (O U.toScheme)

end Geometry

namespace TensorPure

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite
open PiExponentSeshadri.Geometry PiExponentSeshadri.Frames PiExponentSeshadri.SectionOpens
variable {X : Scheme.{0}}

def tensorSection {M N : X.Modules} (s : O X ⟶ M) (t : O X ⟶ N) :
    O X ⟶ moduleTensor X M N :=
  (moduleTensorUnit (O X)).inv ≫ moduleTensorMap s t

lemma section_apply {M N : X.Modules} (s : O X ⟶ M) (t : O X ⟶ N) (U : X.Opens) :
    (tensorSection s t).app U (1 : Γ(X,U)) = pure M N U (s.app U (1 : Γ(X,U))) (t.app U (1 : Γ(X,U))) := by
  have h : (moduleTensorUnit (O X)).inv.app U (1 : Γ(X,U)) =
      pure (O X) (O X) U (1 : Γ(X,U)) (1 : Γ(X,U)) := by
    have he := unit_pure (O X) U (1 : Γ(X,U)) (1 : Γ(X,U))
    have he : (moduleTensorUnit (O X)).hom.app U (pure (O X) (O X) U (1 : Γ(X,U)) (1 : Γ(X,U))) = (1 : Γ(X,U)) := by
      simp only [O, structureSheaf] at he
      exact he.trans (by change (1 : Γ(X,U)) * 1 = 1; exact one_mul _)
    have hi := congrArg ((moduleTensorUnit (O X)).inv.app U) he
    change ((moduleTensorUnit (O X)).hom ≫ (moduleTensorUnit (O X)).inv).app U
      (pure (O X) (O X) U (1 : Γ(X,U)) (1 : Γ(X,U))) = _ at hi
    rw [Iso.hom_inv_id] at hi
    exact hi.symm
  change (moduleTensorMap s t).app U ((moduleTensorUnit (O X)).inv.app U (1 : Γ(X,U))) = _
  rw [h]
  exact map_pure s t U (1 : Γ(X,U)) (1 : Γ(X,U))

lemma framed_pure {M N : X.Modules} (e : M ≅ O X) (d : N ≅ O X) (U : X.Opens)
    (m : M.val.obj (op U)) (n : N.val.obj (op U)) :
    (moduleTensorIso e d ≪≫ moduleTensorUnit (O X)).hom.app U (pure M N U m n) =
      (show Γ(X,U) from e.hom.app U m) * (show Γ(X,U) from d.hom.app U n) := by
  change (moduleTensorUnit (O X)).hom.app U ((moduleTensorMap e.hom d.hom).app U
    (pure M N U m n)) = _
  exact (congrArg ((moduleTensorUnit (O X)).hom.app U) (map_pure e.hom d.hom U m n)).trans
    (unit_pure (O X) U _ _)

lemma local_framed_pure (L M : LineBundle X) (U : X.Opens)
    (e : L.sheaf.restrict U.ι ≅ O U.toScheme) (d : M.sheaf.restrict U.ι ≅ O U.toScheme)
    (V : U.toScheme.Opens) (m : L.sheaf.val.obj (op (U.ι ''ᵁ V)))
    (n : M.sheaf.val.obj (op (U.ι ''ᵁ V))) :
    (tensorFrame L M U e d).hom.app V (pure L.sheaf M.sheaf (U.ι ''ᵁ V) m n) =
      (show Γ(U.toScheme,V) from e.hom.app V m) * (show Γ(U.toScheme,V) from d.hom.app V n) := by
  change (moduleTensorIso e d ≪≫ moduleTensorUnit (O U.toScheme)).hom.app V
    ((moduleTensorRestrict U L.sheaf M.sheaf).hom.app V
      (pure L.sheaf M.sheaf (U.ι ''ᵁ V) m n)) = _
  exact (congrArg ((moduleTensorIso e d ≪≫ moduleTensorUnit (O U.toScheme)).hom.app V)
    (restrict_pure U L.sheaf M.sheaf V m n)).trans (framed_pure e d V m n)

lemma local_section_coefficient (L M : LineBundle X) (U : X.Opens)
    (e : L.sheaf.restrict U.ι ≅ O U.toScheme) (d : M.sheaf.restrict U.ι ≅ O U.toScheme)
    (s : O X ⟶ L.sheaf) (t : O X ⟶ M.sheaf) :
    coefficient (tensorFrame L M U e d) (restrictSection U.ι (tensorSection s t)) =
      coefficient e (restrictSection U.ι s) * coefficient d (restrictSection U.ι t) := by
  change (tensorFrame L M U e d).hom.app ⊤
    ((tensorSection s t).app (U.ι ''ᵁ ⊤) ((U.ι.appIso ⊤).inv (1 : Γ(U.toScheme,⊤)))) =
    (show Γ(U.toScheme,⊤) from e.hom.app ⊤ (s.app (U.ι ''ᵁ ⊤)
      ((U.ι.appIso ⊤).inv (1 : Γ(U.toScheme,⊤))))) *
    (show Γ(U.toScheme,⊤) from d.hom.app ⊤ (t.app (U.ι ''ᵁ ⊤)
      ((U.ι.appIso ⊤).inv (1 : Γ(U.toScheme,⊤)))))
  rw [map_one]
  exact (congrArg ((tensorFrame L M U e d).hom.app ⊤) (section_apply s t _)).trans
    (local_framed_pure L M U e d ⊤ _ _)

lemma section_open (L M : LineBundle X) (s : O X ⟶ L.sheaf) (t : O X ⟶ M.sheaf) :
    isoOpen (tensorSection s t) = isoOpen s ⊓ isoOpen t := by
  apply SetLike.coe_injective
  ext x
  obtain ⟨U,hx,⟨e⟩,⟨d⟩⟩ := common_affine_frames L M x
  have h : U.1.ι ⁻¹ᵁ isoOpen (tensorSection s t) =
      U.1.ι ⁻¹ᵁ (isoOpen s ⊓ isoOpen t) := by
    calc
      _ = U.1.toScheme.basicOpen (coefficient (tensorFrame L M U.1 e d)
          (restrictSection U.1.ι (tensorSection s t))) :=
        preimage_isoOpen (tensorSection s t) U.1.ι (tensorFrame L M U.1 e d)
      _ = U.1.toScheme.basicOpen (coefficient e (restrictSection U.1.ι s) *
          coefficient d (restrictSection U.1.ι t)) :=
        congrArg U.1.toScheme.basicOpen (local_section_coefficient L M U.1 e d s t)
      _ = U.1.toScheme.basicOpen (coefficient e (restrictSection U.1.ι s)) ⊓
          U.1.toScheme.basicOpen (coefficient d (restrictSection U.1.ι t)) :=
        U.1.toScheme.basicOpen_mul _ _
      _ = _ := congrArg₂ (· ⊓ ·) (preimage_isoOpen s U.1.ι e).symm
        (preimage_isoOpen t U.1.ι d).symm
  exact SetLike.ext_iff.mp h ⟨x,hx⟩

end TensorPure

end PiExponentSeshadri

end

end OAI
end Source0032

section Source0033
/-
Modification notice for the LogTwo project.
Derived from openai/math (Apache-2.0), revision adc7f1241b42e322a6451854ab7e4b4c146bf78a.
Original source: lean/OAI/NumberTheory/PiExponent/Ampleness/AmpleIso.lean
Changes: Convert module/import declarations to the Lean 4.34 public module format.
See ../../../../../THIRD_PARTY_NOTICES.txt for provenance and the recorded changes.
-/




namespace OAI

namespace PiExponent.AmpleIso

noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace
open PiExponentSeshadri.Geometry

variable {X : Scheme}

theorem sectionOpen_postcomp_iso {M N : X.Modules}
    (s : GlobalSections X M) (e : M ≅ N) :
    sectionOpen X (s ≫ e.hom) = sectionOpen X s := by
  simp only [sectionOpen, Functor.map_comp, isIso_comp_right_iff]

theorem isAmple_of_sheaf_iso (L M : LineBundle X) (e : L.sheaf ≅ M.sheaf)
    (hL : L.IsAmple) : M.IsAmple := by
  intro x V hx
  obtain ⟨n, hn, s, hsx, hsV, hsa⟩ := hL x V hx
  let ePow : modulePow X L.sheaf n ≅ modulePow X M.sheaf n :=
    (modulePowFunctor n).mapIso e
  refine ⟨n, hn, s ≫ ePow.hom, ?_, ?_, ?_⟩
  · rwa [sectionOpen_postcomp_iso]
  · rwa [sectionOpen_postcomp_iso]
  · rwa [sectionOpen_postcomp_iso]

theorem isAmple_iff_sheaf_iso (L M : LineBundle X) (e : L.sheaf ≅ M.sheaf) :
    L.IsAmple ↔ M.IsAmple :=
  ⟨isAmple_of_sheaf_iso L M e, isAmple_of_sheaf_iso M L e.symm⟩

end
end PiExponent.AmpleIso

end OAI
end Source0033

section Source0034
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
end Source0034

section Source0035
/-
Modification notice for the LogTwo project.
Derived from openai/math (Apache-2.0), revision adc7f1241b42e322a6451854ab7e4b4c146bf78a.
Original source: lean/OAI/NumberTheory/PiExponent/Approximation/FramedPullback.lean
Changes: Convert module/import declarations to the Lean 4.34 public module format.
See ../../../../../THIRD_PARTY_NOTICES.txt for provenance and the recorded changes.
-/




namespace OAI

namespace PiExponentSeshadri.Geometry
noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace
open PiExponentSeshadri.Frames
variable {X Y : Scheme.{0}}

lemma endValue_conjugation (b : O Y ≅ O Y) (a : O Y ⟶ O Y) :
    endValue (b.hom ≫ a ≫ b.inv) = endValue a := by
  rw [endValue_comp, endValue_comp]
  have hb : endValue b.hom * endValue b.inv = 1 := by
    rw [← endValue_comp, b.hom_inv_id, endValue_id]
  calc
    endValue b.hom * (endValue a * endValue b.inv) =
      endValue a * (endValue b.hom * endValue b.inv) := by ring
    _ = endValue a := by rw [hb, mul_one]

lemma exists_frame_natIso (F G : X.Modules ⥤ Y.Modules) (v : F ≅ G)
    (uF : F.obj (O X) ≅ O Y) (uG : G.obj (O X) ≅ O Y)
    {M : X.Modules} (e : G.obj M ≅ O Y) (s : O X ⟶ M) :
    ∃ eF : F.obj M ≅ O Y,
      coefficient eF (uF.inv ≫ F.map s) = coefficient e (uG.inv ≫ G.map s) := by
  let b : O Y ≅ O Y := uF.symm ≪≫ v.app (O X) ≪≫ uG
  refine ⟨v.app M ≪≫ e ≪≫ b.symm, ?_⟩
  have h : (uF.inv ≫ F.map s) ≫ (v.app M).hom =
      b.hom ≫ (uG.inv ≫ G.map s) := by
    simp only [b, Iso.trans_hom, Iso.symm_hom, Category.assoc]
    simp only [Iso.hom_inv_id_assoc]
    exact congrArg (fun q => uF.inv ≫ q) (v.hom.naturality s)
  change endValue (((uF.inv ≫ F.map s) ≫ (v.app M).hom) ≫ e.hom ≫ b.inv) = _
  rw [h]
  change endValue (b.hom ≫ (uG.inv ≫ G.map s ≫ e.hom) ≫ b.inv) = _
  exact endValue_conjugation b _

def pullbackRestrictNatIso (f : Y ⟶ X) (U : X.Opens) :
    Scheme.Modules.pullback f ⋙ Scheme.Modules.restrictFunctor (f ⁻¹ᵁ U).ι ≅
      Scheme.Modules.restrictFunctor U.ι ⋙ Scheme.Modules.pullback (f ∣_ U) :=
  Functor.isoWhiskerLeft (Scheme.Modules.pullback f)
    (Scheme.Modules.restrictFunctorIsoPullback (f ⁻¹ᵁ U).ι) ≪≫
  Scheme.Modules.pullbackComp (f ⁻¹ᵁ U).ι f ≪≫
  Scheme.Modules.pullbackCongr (morphismRestrict_ι f U).symm ≪≫
  (Scheme.Modules.pullbackComp (f ∣_ U) U.ι).symm ≪≫
  Functor.isoWhiskerRight (Scheme.Modules.restrictFunctorIsoPullback U.ι).symm
    (Scheme.Modules.pullback (f ∣_ U))

theorem exists_restricted_pullback_frame (f : Y ⟶ X) (U : X.Opens)
    {M : X.Modules} (e : M.restrict U.ι ≅ O U.toScheme) (s : O X ⟶ M) :
    ∃ eF : ((Scheme.Modules.pullback f).obj M).restrict (f ⁻¹ᵁ U).ι ≅
        O (f ⁻¹ᵁ U).toScheme,
      coefficient eF (restrictSection (f ⁻¹ᵁ U).ι (pullbackSection f s)) =
        (f ∣_ U).appTop (coefficient e (restrictSection U.ι s)) := by
  let F : X.Modules ⥤ (f ⁻¹ᵁ U).toScheme.Modules :=
    Scheme.Modules.pullback f ⋙ Scheme.Modules.restrictFunctor (f ⁻¹ᵁ U).ι
  let G : X.Modules ⥤ (f ⁻¹ᵁ U).toScheme.Modules :=
    Scheme.Modules.restrictFunctor U.ι ⋙ Scheme.Modules.pullback (f ∣_ U)
  let uF : F.obj (O X) ≅ O (f ⁻¹ᵁ U).toScheme :=
    (Scheme.Modules.restrictFunctor (f ⁻¹ᵁ U).ι).mapIso (pullbackUnitIso f) ≪≫
      Scheme.Modules.restrictUnitIso (f ⁻¹ᵁ U).ι
  let uG : G.obj (O X) ≅ O (f ⁻¹ᵁ U).toScheme :=
    (Scheme.Modules.pullback (f ∣_ U)).mapIso (Scheme.Modules.restrictUnitIso U.ι) ≪≫
      pullbackUnitIso (f ∣_ U)
  obtain ⟨eF,he⟩ := exists_frame_natIso F G (pullbackRestrictNatIso f U) uF uG
    (pullbackFrame (f ∣_ U) e) s
  refine ⟨eF, ?_⟩
  have he' : coefficient eF (restrictSection (f ⁻¹ᵁ U).ι (pullbackSection f s)) =
      coefficient (pullbackFrame (f ∣_ U) e)
        (pullbackSection (f ∣_ U) (restrictSection U.ι s)) := by
    let P : X.Modules ⥤ Y.Modules := Scheme.Modules.pullback f
    let R : Y.Modules ⥤ (f ⁻¹ᵁ U).toScheme.Modules :=
      Scheme.Modules.restrictFunctor (f ⁻¹ᵁ U).ι
    let S : X.Modules ⥤ U.toScheme.Modules := Scheme.Modules.restrictFunctor U.ι
    let Q : U.toScheme.Modules ⥤ (f ⁻¹ᵁ U).toScheme.Modules :=
      Scheme.Modules.pullback (f ∣_ U)
    let p : P.obj (O X) ≅ O Y := pullbackUnitIso f
    let r : R.obj (O Y) ≅ O (f ⁻¹ᵁ U).toScheme :=
      Scheme.Modules.restrictUnitIso (f ⁻¹ᵁ U).ι
    let a : S.obj (O X) ≅ O U.toScheme := Scheme.Modules.restrictUnitIso U.ι
    let q : Q.obj (O U.toScheme) ≅ O (f ⁻¹ᵁ U).toScheme := pullbackUnitIso (f ∣_ U)
    have hl : restrictSection (f ⁻¹ᵁ U).ι (pullbackSection f s) = uF.inv ≫ F.map s := by
      simp only [restrictSection, pullbackSection]
      change r.inv ≫ R.map (p.inv ≫ P.map s) = (r.inv ≫ R.map p.inv) ≫ R.map (P.map s)
      exact (congrArg (fun k => r.inv ≫ k) (R.map_comp p.inv (P.map s))).trans
        (Category.assoc r.inv (R.map p.inv) (R.map (P.map s))).symm
    have hr : pullbackSection (f ∣_ U) (restrictSection U.ι s) = uG.inv ≫ G.map s := by
      change q.inv ≫ Q.map (a.inv ≫ S.map s) = (q.inv ≫ Q.map a.inv) ≫ Q.map (S.map s)
      exact (congrArg (fun k => q.inv ≫ k) (Q.map_comp a.inv (S.map s))).trans
        (Category.assoc q.inv (Q.map a.inv) (Q.map (S.map s))).symm
    exact (congrArg (coefficient eF) hl).trans
      (he.trans (congrArg (coefficient (pullbackFrame (f ∣_ U) e)) hr).symm)
  rw [he', coefficient_pullback]

end
end PiExponentSeshadri.Geometry

end OAI
end Source0035

section Source0036
/-
Modification notice for the LogTwo project.
Derived from openai/math (Apache-2.0), revision adc7f1241b42e322a6451854ab7e4b4c146bf78a.
Original source: lean/OAI/NumberTheory/PiExponent/Ampleness/ClosedAmpleRestriction.lean
Changes: Convert module/import declarations to the Lean 4.34 public module format.
See ../../../../../THIRD_PARTY_NOTICES.txt for provenance and the recorded changes.
-/




namespace OAI

namespace PiExponentSeshadri.Geometry
noncomputable section
open AlgebraicGeometry CategoryTheory TopologicalSpace
open PiExponentSeshadri.Frames PiExponentSeshadri.SectionOpens
variable {X Y : Scheme.{0}}

theorem pullback_isoOpen_eq (L : LineBundle X) (s : O X ⟶ L.sheaf) (f : Y ⟶ X) :
    isoOpen (pullbackSection f s) = f ⁻¹ᵁ isoOpen s := by
  ext y
  obtain ⟨U,hy,⟨e⟩⟩ := L.locallyRankOne (f y)
  obtain ⟨eF,he⟩ := exists_restricted_pullback_frame f U e s
  calc
    y ∈ isoOpen (pullbackSection f s) ↔
        (⟨y,hy⟩ : (f ⁻¹ᵁ U).toScheme) ∈ (f ⁻¹ᵁ U).toScheme.basicOpen
          (coefficient eF (restrictSection (f ⁻¹ᵁ U).ι (pullbackSection f s))) :=
      (congrArg (fun V => (⟨y,hy⟩ : (f ⁻¹ᵁ U).toScheme) ∈ V)
        (preimage_isoOpen (pullbackSection f s) (f ⁻¹ᵁ U).ι eF)).to_iff
    _ ↔ (⟨f y,hy⟩ : U.toScheme) ∈ U.toScheme.basicOpen
          (coefficient e (restrictSection U.ι s)) := by
      rw [he,← Scheme.preimage_basicOpen_top]
      change (f ∣_ U) ⟨y,hy⟩ ∈ U.toScheme.basicOpen
        (coefficient e (restrictSection U.ι s)) ↔ _
      rw [morphismRestrict_base]
      rfl
    _ ↔ f y ∈ isoOpen s :=
      (congrArg (fun V => (⟨f y,hy⟩ : U.toScheme) ∈ V)
        (preimage_isoOpen s U.ι e)).to_iff.symm

def pullbackPowerSection (L : LineBundle X) (f : Y ⟶ X) (n : ℕ)
    (s : GlobalSections X (modulePow X L.sheaf n)) :
    GlobalSections Y (modulePow Y (L.pullback f).sheaf n) :=
  pullbackSection f s ≫ (PiExponentSeshadri.PullbackTensor.powIso f L n).hom

theorem sectionOpen_pullbackPowerSection (L : LineBundle X) (f : Y ⟶ X) (n : ℕ)
    (s : GlobalSections X (modulePow X L.sheaf n)) :
    sectionOpen Y (pullbackPowerSection L f n s) = f ⁻¹ᵁ sectionOpen X s := by
  unfold pullbackPowerSection
  erw [PiExponent.AmpleIso.sectionOpen_postcomp_iso]
  exact pullback_isoOpen_eq (L.pow n) s f

theorem LineBundle.IsAmple.pullback_closedImmersion (L : LineBundle X) (hL : L.IsAmple)
    (f : Y ⟶ X) [IsClosedImmersion f] : (L.pullback f).IsAmple := by
  intro y V hy
  obtain ⟨W,hW,hWV⟩ := f.isClosedEmbedding.isInducing.isOpen_iff.mp V.isOpen
  let U : X.Opens := ⟨W,hW⟩
  have hfV : f ⁻¹ᵁ U = V := TopologicalSpace.Opens.ext hWV
  have hfy : f y ∈ U := by
    change y ∈ f ⁻¹ᵁ U
    rwa [hfV]
  obtain ⟨n,hn,s,hys,hsU,hsa⟩ := hL (f y) U hfy
  refine ⟨n,hn,pullbackPowerSection L f n s,?_,?_,?_⟩
  · rw [sectionOpen_pullbackPowerSection]
    exact hys
  · rw [sectionOpen_pullbackPowerSection, ← hfV]
    exact (Opens.map f.base).monotone hsU
  · rw [sectionOpen_pullbackPowerSection]
    exact hsa.preimage f

end
end PiExponentSeshadri.Geometry

end OAI
end Source0036

section Source0037
/-
Modification notice for the LogTwo project.
Derived from openai/math (Apache-2.0), revision adc7f1241b42e322a6451854ab7e4b4c146bf78a.
Original source: lean/OAI/NumberTheory/PiExponent/Cohomology/ProjectiveMonomialCech.lean
Changes: Convert module/import declarations to the Lean 4.34 public module format.
See ../../../../../THIRD_PARTY_NOTICES.txt for provenance and the recorded changes.
-/




namespace OAI

namespace PiExponent.ProjectiveMonomialCech

noncomputable section

open scoped BigOperators

variable {ι K : Type*} [Fintype ι] [AddCommGroup K]

def Monomial (ι : Type*) [Fintype ι] (d : ℤ) :=
  {a : ι → ℤ // ∑ i, a i = d}

abbrev Laurent (ι K : Type*) [Fintype ι] [Zero K] (d : ℤ) :=
  Monomial ι d →₀ K

def RegularOn {d : ℤ} (s : Set ι) (f : Laurent ι K d) : Prop :=
  ∀ a, f a ≠ 0 → ∀ k, a.val k < 0 → k ∈ s

def overlapSupport {d : ℤ} (c : ι → ι → Laurent ι K d) (i : ι) :
    Finset (Monomial ι d) := by
  classical
  exact Finset.univ.biUnion fun j => (c j i).support

def primitive {d : ℤ} (pivot : Monomial ι d → ι)
    (c : ι → ι → Laurent ι K d) (i : ι) : Laurent ι K d := by
  classical
  exact Finsupp.onFinset (overlapSupport c i)
    (fun a => c (pivot a) i a)
    (fun a ha => Finset.mem_biUnion.mpr
      ⟨pivot a, Finset.mem_univ _, Finsupp.mem_support_iff.mpr ha⟩)

@[simp] theorem primitive_apply {d : ℤ} (pivot : Monomial ι d → ι)
    (c : ι → ι → Laurent ι K d) (i : ι) (a : Monomial ι d) :
    primitive pivot c i a = c (pivot a) i a := rfl

theorem primitive_support_subset {d : ℤ} (pivot : Monomial ι d → ι)
    (c : ι → ι → Laurent ι K d) (i : ι) :
    (primitive pivot c i).support ⊆ overlapSupport c i := by
  classical
  exact Finsupp.support_onFinset_subset

theorem primitive_regular {d : ℤ} (pivot : Monomial ι d → ι)
    (hpivot : ∀ a : Monomial ι d, 0 ≤ a.val (pivot a))
    (c : ι → ι → Laurent ι K d)
    (hregular : ∀ i j, RegularOn {i, j} (c i j)) (i : ι) :
    RegularOn {i} (primitive pivot c i) := by
  intro a ha k hk
  have hmem := hregular (pivot a) i a ha k hk
  rcases hmem with h | h
  · subst k
    exact False.elim ((not_lt_of_ge (hpivot a)) hk)
  · exact h

theorem primitive_coboundary {d : ℤ} (pivot : Monomial ι d → ι)
    (c : ι → ι → Laurent ι K d)
    (hcocycle : ∀ i j k, c i j + c j k = c i k) (i j : ι) :
    c i j = primitive pivot c j - primitive pivot c i := by
  ext a
  have h := congrArg (fun f : Laurent ι K d => f a) (hcocycle (pivot a) i j)
  simp only [Finsupp.add_apply] at h
  simp only [Finsupp.sub_apply, primitive_apply]
  exact eq_sub_iff_add_eq.mpr (by simpa [add_comm] using h)

theorem exists_primitive_of_pivot {d : ℤ} (pivot : Monomial ι d → ι)
    (hpivot : ∀ a : Monomial ι d, 0 ≤ a.val (pivot a))
    (c : ι → ι → Laurent ι K d)
    (hregular : ∀ i j, RegularOn {i, j} (c i j))
    (hcocycle : ∀ i j k, c i j + c j k = c i k) :
    ∃ b : ι → Laurent ι K d,
      (∀ i, RegularOn {i} (b i)) ∧ (∀ i j, c i j = b j - b i) := by
  exact ⟨primitive pivot c, primitive_regular pivot hpivot c hregular,
    primitive_coboundary pivot c hcocycle⟩

theorem exists_nonnegative_coordinate [Nonempty ι] {d : ℤ}
    (hd : 0 ≤ d) (a : Monomial ι d) : ∃ i, 0 ≤ a.val i := by
  by_contra h
  have hneg : ∀ i, a.val i < 0 := fun i => lt_of_not_ge (fun hi => h ⟨i, hi⟩)
  have htotal : (∑ i, a.val i) < 0 :=
    Finset.sum_neg (fun i _ => hneg i) Finset.univ_nonempty
  rw [a.property] at htotal
  exact (not_lt_of_ge hd) htotal

theorem nonnegative_twist_cech_exact {d : ℤ} (hd : 0 ≤ d)
    (c : ι → ι → Laurent ι K d)
    (hregular : ∀ i j, RegularOn {i, j} (c i j))
    (hcocycle : ∀ i j k, c i j + c j k = c i k) :
    ∃ b : ι → Laurent ι K d,
      (∀ i, RegularOn {i} (b i)) ∧ (∀ i j, c i j = b j - b i) := by
  classical
  cases isEmpty_or_nonempty ι with
  | inl h => exact ⟨fun i => isEmptyElim i, fun i => isEmptyElim i, fun i => isEmptyElim i⟩
  | inr h =>
      let pivot : Monomial ι d → ι :=
        fun a => Classical.choose (exists_nonnegative_coordinate hd a)
      have hpivot : ∀ a : Monomial ι d, 0 ≤ a.val (pivot a) :=
        fun a => Classical.choose_spec (exists_nonnegative_coordinate hd a)
      exact exists_primitive_of_pivot pivot hpivot c hregular hcocycle

end
end PiExponent.ProjectiveMonomialCech

end OAI
end Source0037

section Source0038
/-
Modification notice for the LogTwo project.
Derived from openai/math (Apache-2.0), revision adc7f1241b42e322a6451854ab7e4b4c146bf78a.
Original source: lean/OAI/NumberTheory/PiExponent/Cohomology/ProjectiveLaurentVertex.lean
Changes: Convert module/import declarations to the Lean 4.34 public module format.
Remove redundant rfl steps after simp closes the goal.
See ../../../../../THIRD_PARTY_NOTICES.txt for provenance and the recorded changes.
-/




namespace OAI

noncomputable section

namespace PiExponent.GeometrySupport.ProjectiveLaurentVertex

section

attribute [local instance] Classical.propDecidable
open scoped BigOperators
open PiExponent.ProjectiveMonomialCech

variable {ι : Type*} [Fintype ι]

abbrev ChartExponent (i : ι) := {j : ι // j ≠ i} →₀ ℕ

def VertexMonomialSet (i : ι) (d : ℤ) : Set (Monomial ι d) :=
  {a | ∀ j, j ≠ i → 0 ≤ a.val j}

def encode (i : ι) (d : ℤ) (b : ChartExponent i) : Monomial ι d := by
  classical
  let a : ι → ℤ := fun j => if h : j = i then
    d - ∑ k : {j : ι // j ≠ i}, (b k : ℤ) else (b ⟨j, h⟩ : ℤ)
  have hi : a i = d - ∑ k : {j : ι // j ≠ i}, (b k : ℤ) := by simp [a]
  have ho : ∀ j : {j : ι // j ≠ i}, a j = (b j : ℤ) := by
    intro j
    simp [a, j.property]
  refine ⟨a, ?_⟩
  rw [Fintype.sum_eq_add_sum_subtype_ne _ i, hi]
  simp_rw [ho]
  omega

@[simp] theorem encode_self (i : ι) (d : ℤ) (b : ChartExponent i) :
    (encode i d b).val i = d - ∑ k : {j : ι // j ≠ i}, (b k : ℤ) := by
  classical
  simp [encode]

@[simp] theorem encode_other (i : ι) (d : ℤ) (b : ChartExponent i)
    (j : {j : ι // j ≠ i}) : (encode i d b).val j = (b j : ℤ) := by
  classical
  simp [encode, j.property]

theorem encode_regular (i : ι) (d : ℤ) (b : ChartExponent i) :
    encode i d b ∈ VertexMonomialSet i d := by
  intro j hj
  simpa only [encode_other i d b ⟨j, hj⟩] using Int.natCast_nonneg (b ⟨j, hj⟩)

def decode (i : ι) (d : ℤ) (a : VertexMonomialSet i d) : ChartExponent i :=
  Finsupp.equivFunOnFinite.symm (fun j => (a.val.val j).toNat)

@[simp] theorem decode_apply (i : ι) (d : ℤ) (a : VertexMonomialSet i d)
    (j : {j : ι // j ≠ i}) : decode i d a j = (a.val.val j).toNat := rfl

@[simp] theorem decode_encode (i : ι) (d : ℤ) (b : ChartExponent i) :
    decode i d ⟨encode i d b, encode_regular i d b⟩ = b := by
  ext j
  simp

@[simp] theorem encode_decode (i : ι) (d : ℤ) (a : VertexMonomialSet i d) :
    encode i d (decode i d a) = a.val := by
  classical
  apply Subtype.ext
  funext j
  by_cases hj : j = i
  · subst j
    rw [encode_self]
    have h := a.val.property
    rw [Fintype.sum_eq_add_sum_subtype_ne _ i] at h
    have hs : (∑ k : {j : ι // j ≠ i}, ((decode i d a k : ℕ) : ℤ)) =
        ∑ k : {j : ι // j ≠ i}, a.val.val k := by
      apply Finset.sum_congr rfl
      intro k hk
      exact Int.toNat_of_nonneg (a.property k k.property)
    rw [hs]
    omega
  · change (encode i d (decode i d a)).val (⟨j, hj⟩ : {j : ι // j ≠ i}) = _
    rw [encode_other, decode_apply, Int.toNat_of_nonneg (a.property j hj)]

def exponentEquiv (i : ι) (d : ℤ) : ChartExponent i ≃ VertexMonomialSet i d where
  toFun b := ⟨encode i d b, encode_regular i d b⟩
  invFun := decode i d
  left_inv := decode_encode i d
  right_inv a := Subtype.ext (encode_decode i d a)

variable {R : Type*} [CommRing R]

def vertexPolynomialEquiv (i : ι) (d : ℤ) :
    MvPolynomial {j : ι // j ≠ i} R ≃ₗ[R]
      Finsupp.supported R R (VertexMonomialSet i d) :=
  (AddMonoidAlgebra.coeffLinearEquiv R).trans <|
    (Finsupp.domLCongr (exponentEquiv i d)).trans
      (Finsupp.supportedEquivFinsupp (VertexMonomialSet i d)).symm

def vertexLaurent (i : ι) (d : ℤ) :
    MvPolynomial {j : ι // j ≠ i} R →ₗ[R] Laurent ι R d :=
  (Finsupp.supported R R (VertexMonomialSet i d)).subtype.comp
    (vertexPolynomialEquiv i d).toLinearMap

@[simp] theorem vertexLaurent_monomial (i : ι) (d : ℤ) (b : ChartExponent i) (r : R) :
    vertexLaurent i d (MvPolynomial.monomial b r) = Finsupp.single (encode i d b) r := by
  classical
  simp [vertexLaurent, vertexPolynomialEquiv, MvPolynomial.monomial, exponentEquiv]

@[simp] theorem vertexLaurent_coefficient (i : ι) (d : ℤ) (b : ChartExponent i)
    (p : MvPolynomial {j : ι // j ≠ i} R) :
    vertexLaurent i d p (encode i d b) = p.coeff b := by
  classical
  simp [vertexLaurent, vertexPolynomialEquiv, Finsupp.extendDomain_apply,
    encode_regular, exponentEquiv]

theorem mem_supported_iff_regular (i : ι) (d : ℤ) (p : Laurent ι R d) :
    p ∈ Finsupp.supported R R (VertexMonomialSet i d) ↔ RegularOn {i} p := by
  classical
  rw [Finsupp.mem_supported]
  constructor
  · intro hp a ha j hj
    have h := hp (Finsupp.mem_support_iff.mpr ha)
    by_contra hji
    exact not_lt_of_ge (h j hji) hj
  · intro hp a ha j hj
    by_contra hneg
    exact hj (hp a (Finsupp.mem_support_iff.mp ha) j (lt_of_not_ge hneg))

theorem vertexLaurent_regular (i : ι) (d : ℤ)
    (p : MvPolynomial {j : ι // j ≠ i} R) : RegularOn {i} (vertexLaurent i d p) :=
  (mem_supported_iff_regular i d _).mp (vertexPolynomialEquiv i d p).property

theorem vertexLaurent_injective (i : ι) (d : ℤ) :
    Function.Injective (vertexLaurent (R := R) i d) :=
  Subtype.val_injective.comp (vertexPolynomialEquiv i d).injective

theorem vertexLaurent_surjective_regular (i : ι) (d : ℤ) (p : Laurent ι R d)
    (hp : RegularOn {i} p) :
    ∃ b : MvPolynomial {j : ι // j ≠ i} R, vertexLaurent i d b = p := by
  let a : Finsupp.supported R R (VertexMonomialSet i d) :=
    ⟨p, (mem_supported_iff_regular i d p).mpr hp⟩
  refine ⟨(vertexPolynomialEquiv i d).symm a, ?_⟩
  change ((vertexPolynomialEquiv i d) ((vertexPolynomialEquiv i d).symm a)).val = p
  rw [LinearEquiv.apply_symm_apply]

end

section
attribute [local instance] Classical.propDecidable
open scoped BigOperators
open PiExponent.ProjectiveMonomialCech
variable {ι R : Type*} [Fintype ι] [CommRing R]

def fullEncode (i : ι) (d : ℤ) (b : {j : ι // j ≠ i} → ℤ) : Monomial ι d := by
  classical
  let a : ι → ℤ := fun j => if h : j = i then
    d - ∑ k : {j : ι // j ≠ i}, b k else b ⟨j, h⟩
  have hi : a i = d - ∑ k : {j : ι // j ≠ i}, b k := by simp [a]
  have ho : ∀ j : {j : ι // j ≠ i}, a j = b j := by
    intro j
    simp [a, j.property]
  refine ⟨a, ?_⟩
  rw [Fintype.sum_eq_add_sum_subtype_ne _ i, hi]
  simp_rw [ho]
  omega

@[simp] theorem fullEncode_self (i : ι) (d : ℤ) (b : {j : ι // j ≠ i} → ℤ) :
    (fullEncode i d b).val i = d - ∑ k : {j : ι // j ≠ i}, b k := by
  classical
  simp [fullEncode]

@[simp] theorem fullEncode_other (i : ι) (d : ℤ) (b : {j : ι // j ≠ i} → ℤ)
    (j : {j : ι // j ≠ i}) : (fullEncode i d b).val j = b j := by
  classical
  simp [fullEncode, j.property]

def fullExponentEquiv (i : ι) (d : ℤ) : ({j : ι // j ≠ i} → ℤ) ≃ Monomial ι d where
  toFun := fullEncode i d
  invFun a j := a.val j
  left_inv b := by funext j; simp
  right_inv a := by
    apply Subtype.ext
    funext j
    by_cases hj : j = i
    · subst j
      rw [fullEncode_self]
      have h := a.property
      rw [Fintype.sum_eq_add_sum_subtype_ne _ i] at h
      change d - (∑ k : {j : ι // j ≠ i}, a.val k) = a.val i
      omega
    · exact fullEncode_other i d _ ⟨j, hj⟩

abbrev chartGroupAlgebra (i : ι) := AddMonoidAlgebra R ({j : ι // j ≠ i} → ℤ)

def natExponentHom (i : ι) : ChartExponent i →+ ({j : ι // j ≠ i} → ℤ) where
  toFun b j := b j
  map_zero' := by ext j; simp
  map_add' := by intro a b; ext j; simp

def polynomialToGroupAlgebra (i : ι) :
    MvPolynomial {j : ι // j ≠ i} R →+* chartGroupAlgebra (R := R) i :=
  AddMonoidAlgebra.mapDomainRingHom R (natExponentHom i)

omit [Fintype ι] in
theorem polynomialToGroupAlgebra_injective (i : ι) :
    Function.Injective (polynomialToGroupAlgebra (R := R) i) := by
  apply AddMonoidAlgebra.mapDomain_injective
  intro a b hab
  ext j
  exact Int.natCast_inj.mp (congrFun hab j)

def groupAlgebraToLaurent (i : ι) (d : ℤ) : chartGroupAlgebra (R := R) i ≃+ Laurent ι R d :=
  (AddMonoidAlgebra.coeffAddEquiv).trans (Finsupp.domCongr (fullExponentEquiv i d))

def chartProduct (i : ι) (s : Finset {j : ι // j ≠ i}) : MvPolynomial {j : ι // j ≠ i} R :=
  ∏ j ∈ s, MvPolynomial.X j

omit [Fintype ι] in
theorem groupAlgebra_single_isUnit (i : ι) (a : {j : ι // j ≠ i} → ℤ) :
    IsUnit (AddMonoidAlgebra.single a (1 : R) : chartGroupAlgebra (R := R) i) := by
  apply isUnit_iff_exists_inv.mpr
  refine ⟨AddMonoidAlgebra.single (-a) 1, ?_⟩
  rw [AddMonoidAlgebra.single_mul_single]
  simp only [add_neg_cancel, one_mul]
  rfl

omit [Fintype ι] in
@[simp] theorem polynomialToGroupAlgebra_X (i : ι) (j : {j : ι // j ≠ i}) :
    polynomialToGroupAlgebra (R := R) i (MvPolynomial.X j) =
      AddMonoidAlgebra.single (natExponentHom i (Finsupp.single j 1)) 1 := by
  change AddMonoidAlgebra.mapDomain _ (AddMonoidAlgebra.single _ _) = _
  exact AddMonoidAlgebra.mapDomain_single

omit [Fintype ι] in
theorem groupAlgebra_product_isUnit (i : ι) (s : Finset {j : ι // j ≠ i}) :
    IsUnit (polynomialToGroupAlgebra (R := R) i (chartProduct i s)) := by
  rw [chartProduct, map_prod]
  exact IsUnit.prod_iff.mpr fun j _ => by
    rw [polynomialToGroupAlgebra_X]
    exact groupAlgebra_single_isUnit i _

def overlapToGroupAlgebra (i : ι) (s : Finset {j : ι // j ≠ i}) :
    Localization.Away (chartProduct (R := R) i s) →+* chartGroupAlgebra (R := R) i :=
  Localization.awayLift (polynomialToGroupAlgebra i) (chartProduct i s)
    (groupAlgebra_product_isUnit i s)

omit [Fintype ι] in
@[simp] theorem overlapToGroupAlgebra_base (i : ι) (s : Finset {j : ι // j ≠ i})
    (p : MvPolynomial {j : ι // j ≠ i} R) :
    overlapToGroupAlgebra i s (algebraMap _ _ p) = polynomialToGroupAlgebra i p := by
  exact IsLocalization.Away.lift_eq (chartProduct i s) (groupAlgebra_product_isUnit i s) p

omit [Fintype ι] in
theorem overlapToGroupAlgebra_injective (i : ι) (s : Finset {j : ι // j ≠ i}) :
    Function.Injective (overlapToGroupAlgebra (R := R) i s) := by
  apply (IsLocalization.injective_iff_map_algebraMap_eq
    (Submonoid.powers (chartProduct (R := R) i s)) (overlapToGroupAlgebra i s)).mpr
  intro x y
  constructor
  · exact congrArg _
  · intro h
    rw [overlapToGroupAlgebra_base, overlapToGroupAlgebra_base] at h
    exact congrArg _ (polynomialToGroupAlgebra_injective i h)

def overlapLaurent (i : ι) (d : ℤ) (s : Finset {j : ι // j ≠ i}) :
    Localization.Away (chartProduct (R := R) i s) →+ Laurent ι R d :=
  (groupAlgebraToLaurent i d).toAddMonoidHom.comp (overlapToGroupAlgebra i s).toAddMonoidHom

theorem overlapLaurent_injective (i : ι) (d : ℤ) (s : Finset {j : ι // j ≠ i}) :
    Function.Injective (overlapLaurent (R := R) i d s) :=
  (groupAlgebraToLaurent i d).injective.comp (overlapToGroupAlgebra_injective i s)

def productExponent (i : ι) (s : Finset {j : ι // j ≠ i}) : {j : ι // j ≠ i} → ℤ :=
  ∑ j ∈ s, natExponentHom i (Finsupp.single j 1)

omit [Fintype ι] in
@[simp] theorem polynomialToGroupAlgebra_product (i : ι)
    (s : Finset {j : ι // j ≠ i}) :
    polynomialToGroupAlgebra (R := R) i (chartProduct i s) =
      AddMonoidAlgebra.single (productExponent i s) 1 := by
  classical
  induction s using Finset.induction_on with
  | empty =>
      simp only [chartProduct, productExponent, Finset.prod_empty, Finset.sum_empty, map_one]
      rfl
  | @insert j s hj ih =>
      simp only [chartProduct, Finset.prod_insert hj, map_mul] at *
      rw [polynomialToGroupAlgebra_X, ih, AddMonoidAlgebra.single_mul_single]
      simp [productExponent, hj]

omit [Fintype ι] in
@[simp] theorem productExponent_outside (i : ι) (s : Finset {j : ι // j ≠ i})
    (k : {j : ι // j ≠ i}) (hk : k ∉ s) : productExponent i s k = 0 := by
  classical
  simp only [productExponent, Finset.sum_apply]
  apply Finset.sum_eq_zero
  intro j hj
  have hne : j ≠ k := fun h => hk (h ▸ hj)
  simp [natExponentHom, Ne.symm hne]

omit [Fintype ι] in
theorem polynomialToGroupAlgebra_nonnegative (i : ι)
    (p : MvPolynomial {j : ι // j ≠ i} R) (a : {j : ι // j ≠ i} → ℤ)
    (ha : (polynomialToGroupAlgebra i p).coeff a ≠ 0)
    (k : {j : ι // j ≠ i}) : 0 ≤ a k := by
  obtain ⟨b, rfl⟩ := Finsupp.mem_range_of_mapDomain_ne_zero ha
  exact Int.natCast_nonneg _

omit [Fintype ι] in
theorem overlapToGroupAlgebra_nonnegative (i : ι) (s : Finset {j : ι // j ≠ i})
    (z : Localization.Away (chartProduct (R := R) i s))
    (a : {j : ι // j ≠ i} → ℤ) (ha : (overlapToGroupAlgebra i s z).coeff a ≠ 0)
    (k : {j : ι // j ≠ i}) (hk : k ∉ s) : 0 ≤ a k := by
  obtain ⟨n, p, hp⟩ := IsLocalization.Away.surj (chartProduct (R := R) i s) z
  have h := congrArg (overlapToGroupAlgebra i s) hp
  simp only [map_mul, map_pow, overlapToGroupAlgebra_base,
    polynomialToGroupAlgebra_product, AddMonoidAlgebra.single_pow, one_pow] at h
  have hc := congrArg (fun q : chartGroupAlgebra (R := R) i =>
    q.coeff (a + n • productExponent i s)) h
  simp only [AddMonoidAlgebra.coeff_mul_single_add, mul_one] at hc
  have hn := polynomialToGroupAlgebra_nonnegative i p (a + n • productExponent i s)
    (hc ▸ ha) k
  simpa only [Pi.add_apply, Pi.smul_apply, productExponent_outside i s k hk,
    smul_zero, add_zero] using hn

@[simp] theorem groupAlgebraToLaurent_coefficient (i : ι) (d : ℤ)
    (p : chartGroupAlgebra (R := R) i) (a : Monomial ι d) :
    groupAlgebraToLaurent i d p a = p.coeff (fun j => a.val j) := by
  simp [groupAlgebraToLaurent, fullExponentEquiv]

theorem overlapLaurent_regular (i : ι) (d : ℤ) (s : Finset {j : ι // j ≠ i})
    (z : Localization.Away (chartProduct (R := R) i s)) :
    RegularOn ({i} ∪ (Subtype.val '' (s : Set {j : ι // j ≠ i})))
      (overlapLaurent i d s z) := by
  intro a ha k hk
  by_cases hki : k = i
  · exact Or.inl hki
  · apply Or.inr
    by_contra hks
    have hn : (⟨k, hki⟩ : {j : ι // j ≠ i}) ∉ s := by
      intro hm
      exact hks ⟨⟨k, hki⟩, hm, rfl⟩
    change groupAlgebraToLaurent i d (overlapToGroupAlgebra i s z) a ≠ 0 at ha
    rw [groupAlgebraToLaurent_coefficient] at ha
    exact not_lt_of_ge (overlapToGroupAlgebra_nonnegative i s z _ ha ⟨k, hki⟩ hn) hk

@[simp] theorem fullEncode_nat (i : ι) (d : ℤ) (b : ChartExponent i) :
    fullEncode i d (natExponentHom i b) = encode i d b := rfl

theorem groupAlgebraToLaurent_polynomial (i : ι) (d : ℤ)
    (p : MvPolynomial {j : ι // j ≠ i} R) :
    groupAlgebraToLaurent i d (polynomialToGroupAlgebra i p) = vertexLaurent i d p := by
  induction p using MvPolynomial.induction_on'
  case add a b ha hb =>
    simp only [map_add, ha, hb]
  case monomial b r =>
    rw [vertexLaurent_monomial]
    change groupAlgebraToLaurent i d
      (AddMonoidAlgebra.mapDomain _ (AddMonoidAlgebra.single b r)) = _
    rw [AddMonoidAlgebra.mapDomain_single]
    simp [groupAlgebraToLaurent, fullExponentEquiv]

@[simp] theorem overlapLaurent_base (i : ι) (d : ℤ) (s : Finset {j : ι // j ≠ i})
    (p : MvPolynomial {j : ι // j ≠ i} R) :
    overlapLaurent i d s (algebraMap _ _ p) = vertexLaurent i d p := by
  change groupAlgebraToLaurent i d (overlapToGroupAlgebra i s (algebraMap _ _ p)) = _
  rw [overlapToGroupAlgebra_base, groupAlgebraToLaurent_polynomial]

end

section
variable {ι R : Type*} [Fintype ι] [CommRing R]
theorem overlapLaurent_natural (i : ι) (d : ℤ)
    (s t : Finset {j : ι // j ≠ i})
    (f : Localization.Away (chartProduct (R := R) i s) →+*
      Localization.Away (chartProduct (R := R) i t))
    (hf : ∀ p : MvPolynomial {j : ι // j ≠ i} R,
      f (algebraMap _ _ p) = algebraMap _ _ p)
    (z : Localization.Away (chartProduct (R := R) i s)) :
    overlapLaurent i d t (f z) = overlapLaurent i d s z := by
  have h : (overlapToGroupAlgebra i t).comp f = overlapToGroupAlgebra i s := by
    apply IsLocalization.ringHom_ext (Submonoid.powers (chartProduct (R := R) i s))
    apply RingHom.ext
    intro p
    simp only [RingHom.comp_apply, hf, overlapToGroupAlgebra_base]
  change groupAlgebraToLaurent i d (((overlapToGroupAlgebra i t).comp f) z) = _
  rw [h]
  rfl
end

attribute [local instance] Classical.propDecidable
open scoped BigOperators
open PiExponent.ProjectiveMonomialCech
variable {ι R : Type*} [Fintype ι] [CommRing R]

omit [Fintype ι] in
@[simp] theorem productExponent_inside (i : ι) (s : Finset {j : ι // j ≠ i})
    (k : {j : ι // j ≠ i}) (hk : k ∈ s) : productExponent i s k = 1 := by
  classical
  simp [productExponent, Finset.sum_apply, natExponentHom, Finsupp.single_apply, hk]

theorem exists_cleared_exponent (i : ι) (s : Finset {j : ι // j ≠ i})
    (a : {j : ι // j ≠ i} → ℤ) (ha : ∀ k, k ∉ s → 0 ≤ a k) :
    ∃ (n : ℕ) (b : ChartExponent i), natExponentHom i b = a + n • productExponent i s := by
  classical
  let n : ℕ := ∑ j : {j : ι // j ≠ i}, (-a j).toNat
  have hnn : ∀ k, 0 ≤ a k + (n : ℤ) := by
    intro k
    have hn : (-a k).toNat ≤ n :=
      Finset.single_le_sum (fun j _ => Nat.zero_le ((-a j).toNat)) (Finset.mem_univ k)
    have hn' : ((-a k).toNat : ℤ) ≤ (n : ℤ) := by exact_mod_cast hn
    omega
  have hnonneg : ∀ k, 0 ≤ (a + n • productExponent i s) k := by
    intro k
    by_cases hk : k ∈ s
    · simpa [Pi.add_apply, Pi.smul_apply, nsmul_eq_mul, productExponent_inside i s k hk] using hnn k
    · simpa only [Pi.add_apply, Pi.smul_apply, productExponent_outside i s k hk,
        smul_zero, add_zero] using ha k hk
  refine ⟨n, Finsupp.equivFunOnFinite.symm (fun k => ((a + n • productExponent i s) k).toNat), ?_⟩
  funext k
  exact Int.toNat_of_nonneg (hnonneg k)

theorem groupAlgebra_single_in_overlap_range (i : ι) (s : Finset {j : ι // j ≠ i})
    (a : {j : ι // j ≠ i} → ℤ) (r : R) (ha : ∀ k, k ∉ s → 0 ≤ a k) :
    ∃ z : Localization.Away (chartProduct (R := R) i s),
      overlapToGroupAlgebra i s z = AddMonoidAlgebra.single a r := by
  classical
  obtain ⟨n, b, hb⟩ := exists_cleared_exponent i s a ha
  have hinv : polynomialToGroupAlgebra (R := R) i (chartProduct i s) *
      AddMonoidAlgebra.single (-productExponent i s) 1 = 1 := by
    rw [polynomialToGroupAlgebra_product, AddMonoidAlgebra.single_mul_single]
    simp only [add_neg_cancel, one_mul]
    rfl
  refine ⟨Localization.mk (MvPolynomial.monomial b r) ⟨(chartProduct i s)^n, n, rfl⟩, ?_⟩
  change Localization.awayLift (polynomialToGroupAlgebra i) (chartProduct i s)
    (isUnit_iff_exists_inv.mpr ⟨_, hinv⟩) _ = _
  rw [Localization.awayLift_mk (polynomialToGroupAlgebra i) (chartProduct i s)
    (MvPolynomial.monomial b r) (AddMonoidAlgebra.single (-productExponent i s) 1) hinv n]
  change AddMonoidAlgebra.mapDomain _ (AddMonoidAlgebra.single b r) * _ = _
  rw [AddMonoidAlgebra.mapDomain_single, AddMonoidAlgebra.single_pow,
    AddMonoidAlgebra.single_mul_single, hb]
  simp

theorem laurent_single_in_overlap_range (i : ι) (d : ℤ)
    (s : Finset {j : ι // j ≠ i}) (a : Monomial ι d) (r : R)
    (ha : ∀ k : {j : ι // j ≠ i}, k ∉ s → 0 ≤ a.val k) :
    ∃ z : Localization.Away (chartProduct (R := R) i s),
      overlapLaurent i d s z = Finsupp.single a r := by
  obtain ⟨z, hz⟩ := groupAlgebra_single_in_overlap_range i s (fun j => a.val j) r ha
  refine ⟨z, ?_⟩
  change groupAlgebraToLaurent i d (overlapToGroupAlgebra i s z) = _
  rw [hz]
  change (Finsupp.domCongr (fullExponentEquiv i d))
    (Finsupp.single ((fullExponentEquiv i d).symm a) r) = _
  simp

theorem overlapLaurent_surjective_regular (i : ι) (d : ℤ)
    (s : Finset {j : ι // j ≠ i}) (p : Laurent ι R d)
    (hp : RegularOn ({i} ∪ (Subtype.val '' (s : Set {j : ι // j ≠ i}))) p) :
    ∃ z : Localization.Away (chartProduct (R := R) i s), overlapLaurent i d s z = p := by
  classical
  have hs : ∀ a ∈ p.support, ∃ z : Localization.Away (chartProduct (R := R) i s),
      overlapLaurent i d s z = Finsupp.single a (p a) := by
    intro a ha
    apply laurent_single_in_overlap_range
    intro k hk
    by_contra hn
    have hmem := hp a (Finsupp.mem_support_iff.mp ha) k (lt_of_not_ge hn)
    rcases hmem with hmem | ⟨j, hj, heq⟩
    · exact k.property hmem
    · exact hk ((Subtype.ext heq) ▸ hj)
  choose z hz using hs
  refine ⟨∑ a ∈ p.support, if h : a ∈ p.support then z a h else 0, ?_⟩
  rw [map_sum]
  calc
    _ = ∑ a ∈ p.support, Finsupp.single a (p a) := by
      apply Finset.sum_congr rfl
      intro a ha
      simp only [dite_eq_left ha, hz]
    _ = p := p.sum_single
end PiExponent.GeometrySupport.ProjectiveLaurentVertex

end

end OAI
end Source0038

section Source0039
/-
Modification notice for the LogTwo project.
Derived from openai/math (Apache-2.0), revision adc7f1241b42e322a6451854ab7e4b4c146bf78a.
Original source: lean/OAI/NumberTheory/PiExponent/Geometry/ProjectiveChartSections.lean
Changes: Convert module/import declarations to the Lean 4.34 public module format.
Expose private helpers and adjust helper names where needed for module compatibility.
See ../../../../../THIRD_PARTY_NOTICES.txt for provenance and the recorded changes.
-/




namespace OAI

noncomputable section

namespace PiExponentSeshadri.ProjectiveChartSections

open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite
open PiExponentSeshadri.Geometry ModuleFlasque RestrictionCohomology
abbrev schemeFreeOpen (X : Scheme) (U : X.Opens) : X.Modules :=
  freeOpen X.ringCatSheaf U

variable {X : Scheme} (U : X.Opens) (M : X.Modules)

def framedSectionsEquiv (e : M.restrict U.ι ≅ structureSheaf U.toScheme) :
    Γ(M,U) ≃+ Γ(U.toScheme,⊤) :=
  (restrictionSectionsIso U M).addCommGroupIsoToAddEquiv.symm.trans
    { toFun := fun x => e.hom.val.app (op ⊤) x
      invFun := fun x => e.inv.val.app (op ⊤) x
      left_inv := fun x => by
        have h := congrArg (fun f => f.val.app (op ⊤) x) e.hom_inv_id
        exact h
      right_inv := fun x => by
        have h := congrArg (fun f => f.val.app (op ⊤) x) e.inv_hom_id
        exact h
      map_add' := fun x y => map_add _ _ _ }

def framedCoefficientsEquiv (e : M.restrict U.ι ≅ structureSheaf U.toScheme) :
    Γ(M,U) ≃+ Γ(X,U) :=
  (framedSectionsEquiv U M e).trans U.topIso.commRingCatIsoToRingEquiv.toAddEquiv

def freeOpenAddEquiv : (schemeFreeOpen X U ⟶ M) ≃+ Γ(M,U) :=
  { freeOpenEquiv X.ringCatSheaf M U with
    map_add' := fun f g => by rfl }

def framedHomCoefficientsEquiv (e : M.restrict U.ι ≅ structureSheaf U.toScheme) :
    (schemeFreeOpen X U ⟶ M) ≃+ Γ(X,U) :=
  (freeOpenAddEquiv U M).trans (framedCoefficientsEquiv U M e)

def framedHomRingEquiv {A : Type*} [CommRing A]
    (e : M.restrict U.ι ≅ structureSheaf U.toScheme) (r : Γ(X,U) ≃+* A) :
    (schemeFreeOpen X U ⟶ M) ≃+ A :=
  (framedHomCoefficientsEquiv U M e).trans r.toAddEquiv

open PiExponent.ProjectiveMonomialCech
open PiExponent.GeometrySupport.ProjectiveLaurentVertex
variable {R ι : Type} [CommRing R] [Fintype ι] (i : ι) (d : ℤ)

def framedLaurentVertex (e : M.restrict U.ι ≅ structureSheaf U.toScheme)
    (r : Γ(X,U) ≃+* MvPolynomial {j : ι // j ≠ i} R) :
    (schemeFreeOpen X U ⟶ M) →+ Laurent ι R d :=
  (vertexLaurent i d).toAddMonoidHom.comp (framedHomRingEquiv U M e r).toAddMonoidHom

theorem framedLaurentVertex_regular (e : M.restrict U.ι ≅ structureSheaf U.toScheme)
    (r : Γ(X,U) ≃+* MvPolynomial {j : ι // j ≠ i} R)
    (s : schemeFreeOpen X U ⟶ M) :
    RegularOn {i} (framedLaurentVertex U M i d e r s) :=
  vertexLaurent_regular i d _

theorem framedLaurentVertex_injective (e : M.restrict U.ι ≅ structureSheaf U.toScheme)
    (r : Γ(X,U) ≃+* MvPolynomial {j : ι // j ≠ i} R) :
    Function.Injective (framedLaurentVertex U M i d e r) :=
  (vertexLaurent_injective i d).comp (framedHomRingEquiv U M e r).injective

theorem framedLaurentVertex_surjective_regular
    (e : M.restrict U.ι ≅ structureSheaf U.toScheme)
    (r : Γ(X,U) ≃+* MvPolynomial {j : ι // j ≠ i} R)
    (p : Laurent ι R d) (hp : RegularOn {i} p) :
    ∃ s : schemeFreeOpen X U ⟶ M, framedLaurentVertex U M i d e r s = p := by
  obtain ⟨b, hb⟩ := vertexLaurent_surjective_regular i d p hp
  refine ⟨(framedHomRingEquiv U M e r).symm b, ?_⟩
  change vertexLaurent i d ((framedHomRingEquiv U M e r)
    ((framedHomRingEquiv U M e r).symm b)) = p
  rw [AddEquiv.apply_symm_apply, hb]

def powerHomRingEquiv {A : Type*} [CommRing A]
    (e : M.restrict U.ι ≅ structureSheaf U.toScheme) (r : Γ(X,U) ≃+* A) (n : ℕ) :
    (schemeFreeOpen X U ⟶ modulePow X M n) ≃+ A :=
  framedHomRingEquiv U (modulePow X M n) (modulePowFrame U e n) r

def framedLaurentOverlap (s : Finset {j : ι // j ≠ i})
    (e : M.restrict U.ι ≅ structureSheaf U.toScheme)
    (r : Γ(X,U) ≃+* Localization.Away (chartProduct (R := R) i s)) :
    (schemeFreeOpen X U ⟶ M) →+ Laurent ι R d :=
  (overlapLaurent i d s).comp (framedHomRingEquiv U M e r).toAddMonoidHom

theorem framedLaurentOverlap_injective (s : Finset {j : ι // j ≠ i})
    (e : M.restrict U.ι ≅ structureSheaf U.toScheme)
    (r : Γ(X,U) ≃+* Localization.Away (chartProduct (R := R) i s)) :
    Function.Injective (framedLaurentOverlap U M i d s e r) :=
  (overlapLaurent_injective i d s).comp (framedHomRingEquiv U M e r).injective

theorem framedLaurentOverlap_regular (s : Finset {j : ι // j ≠ i})
    (e : M.restrict U.ι ≅ structureSheaf U.toScheme)
    (r : Γ(X,U) ≃+* Localization.Away (chartProduct (R := R) i s))
    (b : schemeFreeOpen X U ⟶ M) :
    RegularOn ({i} ∪ (Subtype.val '' (s : Set {j : ι // j ≠ i})))
      (framedLaurentOverlap U M i d s e r b) :=
  overlapLaurent_regular i d s _

theorem framedLaurentOverlap_surjective_regular (s : Finset {j : ι // j ≠ i})
    (e : M.restrict U.ι ≅ structureSheaf U.toScheme)
    (r : Γ(X,U) ≃+* Localization.Away (chartProduct (R := R) i s))
    (p : Laurent ι R d)
    (hp : RegularOn ({i} ∪ (Subtype.val '' (s : Set {j : ι // j ≠ i}))) p) :
    ∃ b : schemeFreeOpen X U ⟶ M,
      framedLaurentOverlap U M i d s e r b = p := by
  obtain ⟨a, ha⟩ := overlapLaurent_surjective_regular i d s p hp
  refine ⟨(framedHomRingEquiv U M e r).symm a, ?_⟩
  change overlapLaurent i d s ((framedHomRingEquiv U M e r)
    ((framedHomRingEquiv U M e r).symm a)) = p
  rw [AddEquiv.apply_symm_apply, ha]

end PiExponentSeshadri.ProjectiveChartSections

end

end OAI
end Source0039

section Source0040
/-
Modification notice for the LogTwo project.
Derived from openai/math (Apache-2.0), revision adc7f1241b42e322a6451854ab7e4b4c146bf78a.
Original source: lean/OAI/NumberTheory/PiExponent/Geometry/ProjectiveFrameNaturality.lean
Changes: Convert module/import declarations to the Lean 4.34 public module format.
See ../../../../../THIRD_PARTY_NOTICES.txt for provenance and the recorded changes.
-/




namespace OAI

namespace PiExponentSeshadri.ProjectiveChartSections
noncomputable section
open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite
open PiExponentSeshadri.Geometry ModuleFlasque RestrictionCohomology Frames
variable {X : Scheme} {U V : X.Opens} (M : X.Modules)
lemma framedSectionsEquiv_restrict (h : V ≤ U)
    (e : M.restrict U.ι ≅ structureSheaf U.toScheme) (s : Γ(M,U)) :
    framedSectionsEquiv V M (restrictOpenFrame h e) (M.presheaf.map (homOfLE h).op s) =
      (X.homOfLE h).appTop (framedSectionsEquiv U M e s) := by
  change (restrictOpenFrame h e).hom.app ⊤
    ((restrictionSectionsIso V M).inv (M.presheaf.map (homOfLE h).op s)) =
    (X.homOfLE h).appTop (e.hom.app ⊤ ((restrictionSectionsIso U M).inv s))
  simp only [restrictOpenFrame, Iso.trans_hom, Iso.symm_hom,
    Scheme.Modules.Hom.comp_app, Iso.app_inv, Iso.app_hom,
    Scheme.Modules.restrictFunctorCongr_inv_app_app,
    Scheme.Modules.restrictFunctorComp_hom_app_app,
    restrictionSectionsIso,
    Scheme.Modules.restrictAppIso]
  let φ := X.homOfLE h
  let W := φ ''ᵁ (⊤ : V.toScheme.Opens)
  let y := (restrictionSectionsIso U M).inv s
  have hn : e.hom.app W ((M.restrict U.ι).presheaf.map (homOfLE (show W ≤ ⊤ from le_top)).op y) =
      U.toScheme.presheaf.map (homOfLE (show W ≤ ⊤ from le_top)).op (e.hom.app ⊤ y) :=
    CategoryTheory.congr_fun (e.hom.mapPresheaf.naturality (homOfLE (show W ≤ ⊤ from le_top)).op) y
  calc
    _ = (φ.appIso ⊤).hom (e.hom.app W
        ((M.restrict U.ι).presheaf.map (homOfLE (show W ≤ ⊤ from le_top)).op y)) := by
      change (φ.appIso ⊤).hom (e.hom.app W _) = _
      apply congrArg (φ.appIso ⊤).hom
      apply congrArg (e.hom.app W)
      change (M.presheaf.map _ ≫ M.presheaf.map _ ≫ M.presheaf.map _ ≫ M.presheaf.map _) s =
        (M.presheaf.map _ ≫ M.presheaf.map _) s
      simp only [← Functor.map_comp]
      congr 2
    _ = (φ.appIso ⊤).hom (U.toScheme.presheaf.map
        (homOfLE (show W ≤ ⊤ from le_top)).op (e.hom.app ⊤ y)) := congrArg _ hn
    _ = _ := by
      change (U.toScheme.presheaf.map _ ≫ (φ.appIso ⊤).hom) (e.hom.app ⊤ y) = _
      rw [Scheme.Hom.appIso_hom']
      simp only [φ, Scheme.Hom.appTop, Scheme.homOfLE_app, Scheme.homOfLE_appLE,
        Scheme.Opens.toScheme_presheaf_map]
      erw [← Functor.map_comp]
      congr 2

lemma topIso_hom_restrict (h : V ≤ U) (x : Γ(U.toScheme, ⊤)) :
    V.topIso.hom ((X.homOfLE h).appTop x) =
      X.presheaf.map (homOfLE h).op (U.topIso.hom x) := by
  simp only [Scheme.homOfLE_appTop, Scheme.Opens.topIso_hom]
  change (X.presheaf.map _ ≫ X.presheaf.map _) x =
    (X.presheaf.map _ ≫ X.presheaf.map _) x
  erw [← Functor.map_comp, ← Functor.map_comp]
  congr 2

lemma framedCoefficientsEquiv_restrict (h : V ≤ U)
    (e : M.restrict U.ι ≅ structureSheaf U.toScheme) (s : Γ(M,U)) :
    framedCoefficientsEquiv V M (restrictOpenFrame h e)
      (M.presheaf.map (homOfLE h).op s) =
      X.presheaf.map (homOfLE h).op (framedCoefficientsEquiv U M e s) := by
  change V.topIso.hom (framedSectionsEquiv V M (restrictOpenFrame h e)
    (M.presheaf.map (homOfLE h).op s)) =
    X.presheaf.map (homOfLE h).op (U.topIso.hom (framedSectionsEquiv U M e s))
  erw [framedSectionsEquiv_restrict, topIso_hom_restrict]

lemma framedHomCoefficientsEquiv_restrict (h : V ≤ U)
    (e : M.restrict U.ι ≅ structureSheaf U.toScheme)
    (b : freeOpen X.ringCatSheaf U ⟶ M) :
    framedHomCoefficientsEquiv V M (restrictOpenFrame h e)
      (freeOpenMap X.ringCatSheaf (homOfLE h) ≫ b) =
      X.presheaf.map (homOfLE h).op (framedHomCoefficientsEquiv U M e b) := by
  change framedCoefficientsEquiv V M (restrictOpenFrame h e)
    (freeOpenEquiv X.ringCatSheaf M V
      (freeOpenMap X.ringCatSheaf (homOfLE h) ≫ b)) =
    X.presheaf.map (homOfLE h).op
      (framedCoefficientsEquiv U M e (freeOpenEquiv X.ringCatSheaf M U b))
  erw [freeOpenEquiv_naturality]
  exact framedCoefficientsEquiv_restrict M h e _

end
end PiExponentSeshadri.ProjectiveChartSections

end OAI
end Source0040

section Source0041
/-
Modification notice for the LogTwo project.
Derived from openai/math (Apache-2.0), revision adc7f1241b42e322a6451854ab7e4b4c146bf78a.
Original source: lean/OAI/NumberTheory/PiExponent/Geometry/LineBundleGluing.lean
Changes: Convert module/import declarations to the Lean 4.34 public module format.
See ../../../../../THIRD_PARTY_NOTICES.txt for provenance and the recorded changes.
-/




namespace OAI

noncomputable section

namespace PiExponentSeshadri.LineBundleGluing

section
open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite
open PiExponentSeshadri.Geometry

variable {X : Scheme} {ι : Type} (U : ι → X.Opens)

structure Cocycle where
  transition (i j : ι) (W : X.Opens) (hi : W ≤ U i) (hj : W ≤ U j) : Γ(X,W)ˣ
  restriction (i j : ι) {V W : X.Opens} (h : V ≤ W) (hi : W ≤ U i) (hj : W ≤ U j) :
    X.presheaf.map (homOfLE h).op (transition i j W hi hj : Γ(X,W)) =
      (transition i j V (h.trans hi) (h.trans hj) : Γ(X,V))
  identity (i : ι) (W : X.Opens) (hi : W ≤ U i) :
    transition i i W hi hi = 1
  cocycle (i j k : ι) (W : X.Opens) (hi : W ≤ U i) (hj : W ≤ U j) (hk : W ≤ U k) :
    transition i j W hi hj * transition j k W hj hk = transition i k W hi hk

def LocalIndex (V : X.Opens) := Σ i : ι, {W : X.Opens // W ≤ V ∧ W ≤ U i}

abbrev Family (V : X.Opens) := ∀ p : LocalIndex U V, Γ(X,p.2.val)

@[instance_reducible]
def localModule (V : X.Opens) (p : LocalIndex U V) :
    Module Γ(X,V) Γ(X,p.2.val) :=
  Module.compHom _ (X.presheaf.map (homOfLE p.2.property.1).op).hom

instance familyModule (V : X.Opens) : Module Γ(X,V) (Family U V) := by
  letI (p : LocalIndex U V) : Module Γ(X,V) Γ(X,p.2.val) := localModule U V p
  exact Pi.module _ _ _

variable {U} (c : Cocycle U)

def sections (V : X.Opens) : Submodule Γ(X,V) (Family U V) where
  carrier := {s | (∀ (i : ι) (W W' : X.Opens) (hW : W ≤ V) (hi : W ≤ U i)
    (h : W' ≤ W), X.presheaf.map (homOfLE h).op (s ⟨i,W,hW,hi⟩) =
      s ⟨i,W',h.trans hW,h.trans hi⟩) ∧
    (∀ (i j : ι) (W : X.Opens) (hW : W ≤ V) (hi : W ≤ U i) (hj : W ≤ U j),
      s ⟨i,W,hW,hi⟩ = (c.transition i j W hi hj : Γ(X,W)) * s ⟨j,W,hW,hj⟩)}
  zero_mem' := by
    constructor
    · intro i W W' hW hi h
      change X.presheaf.map (homOfLE h).op (0 : Γ(X, W)) = 0
      exact map_zero _
    · intro i j W hW hi hj
      change (0 : Γ(X, W)) = (c.transition i j W hi hj : Γ(X, W)) * 0
      simp only [mul_zero]
  add_mem' := by
    intro a b ha hb
    constructor
    · intro i W W' hW hi h
      change X.presheaf.map (homOfLE h).op (a ⟨i,W,hW,hi⟩ + b ⟨i,W,hW,hi⟩) = _
      rw [map_add, ha.1 i W W' hW hi h, hb.1 i W W' hW hi h]
      rfl
    · intro i j W hW hi hj
      change a ⟨i,W,hW,hi⟩ + b ⟨i,W,hW,hi⟩ = _
      rw [ha.2 i j W hW hi hj, hb.2 i j W hW hi hj, ← mul_add]
      rfl
  smul_mem' := by
    intro a s hs
    constructor
    · intro i W W' hW hi h
      change X.presheaf.map (homOfLE h).op
        (X.presheaf.map (homOfLE hW).op a * s ⟨i,W,hW,hi⟩) =
        X.presheaf.map (homOfLE (h.trans hW)).op a * s ⟨i,W',h.trans hW,h.trans hi⟩
      rw [map_mul, hs.1 i W W' hW hi h]
      congr 1
      change (X.presheaf.map _ ≫ X.presheaf.map _) a = _
      rw [← Functor.map_comp]
      rfl
    · intro i j W hW hi hj
      change X.presheaf.map (homOfLE hW).op a * s ⟨i,W,hW,hi⟩ =
        (c.transition i j W hi hj : Γ(X,W)) *
          (X.presheaf.map (homOfLE hW).op a * s ⟨j,W,hW,hj⟩)
      rw [hs.2 i j W hW hi hj]
      ring

def restrict {V W : X.Opens} (h : V ≤ W) : sections c W →+ sections c V where
  toFun s := ⟨fun p => s.val ⟨p.1,p.2.val,p.2.property.1.trans h,p.2.property.2⟩,
    ⟨fun i A B hA hi hBA => s.property.1 i A B (hA.trans h) hi hBA,
     fun i j A hA hi hj => s.property.2 i j A (hA.trans h) hi hj⟩⟩
  map_zero' := rfl
  map_add' _ _ := rfl

lemma restrict_smul {V W : X.Opens} (h : V ≤ W) (a : Γ(X,W)) (s : sections c W) :
    restrict c h (a • s) = X.presheaf.map (homOfLE h).op a • restrict c h s := by
  apply Subtype.ext
  funext p
  change X.presheaf.map (homOfLE (p.2.property.1.trans h)).op a * _ =
    X.presheaf.map (homOfLE p.2.property.1).op
      (X.presheaf.map (homOfLE h).op a) * _
  congr 1
  change _ = (X.presheaf.map _ ≫ X.presheaf.map _) a
  rw [← Functor.map_comp]
  rfl

def presheaf : PresheafOfModules X.ringCatSheaf.obj where
  obj V := ModuleCat.of Γ(X, V.unop) (sections c V.unop)
  map {V W} f := ModuleCat.ofHom
    (Y := (ModuleCat.restrictScalars (X.presheaf.map f).hom).obj
      (ModuleCat.of Γ(X, W.unop) (sections c W.unop)))
    { toFun := restrict c (leOfHom f.unop)
      map_add' := fun a b => (restrict c (leOfHom f.unop)).map_add a b
      map_smul' := fun a s => restrict_smul c _ a s }
  map_id V := by ext; rfl
  map_comp f g := by ext; rfl

def fromChart {V : X.Opens} (i : ι) (hi : V ≤ U i) (a : Γ(X,V)) : sections c V :=
  ⟨fun p => (c.transition p.1 i p.2.val p.2.property.2 (p.2.property.1.trans hi) :
      Γ(X,p.2.val)) * X.presheaf.map (homOfLE p.2.property.1).op a,
    by
      constructor
      · intro j W W' hW hj h
        change X.presheaf.map (homOfLE h).op
          ((c.transition j i W hj (hW.trans hi) : Γ(X,W)) *
            X.presheaf.map (homOfLE hW).op a) = _
        rw [map_mul, c.restriction]
        congr 1
        change (X.presheaf.map _ ≫ X.presheaf.map _) a = _
        rw [← Functor.map_comp]
        rfl
      · intro j k W hW hj hk
        change (c.transition j i W hj (hW.trans hi) : Γ(X,W)) *
            X.presheaf.map (homOfLE hW).op a =
          (c.transition j k W hj hk : Γ(X,W)) *
            ((c.transition k i W hk (hW.trans hi) : Γ(X,W)) *
              X.presheaf.map (homOfLE hW).op a)
        rw [← mul_assoc, ← Units.val_mul, c.cocycle]⟩

def chartEquiv {V : X.Opens} (i : ι) (hi : V ≤ U i) :
    sections c V ≃ₗ[Γ(X,V)] Γ(X,V) where
  toFun s := s.val ⟨i,V,le_rfl,hi⟩
  invFun := fromChart c i hi
  left_inv s := by
    apply Subtype.ext
    funext p
    change (c.transition p.1 i p.2.val p.2.property.2 (p.2.property.1.trans hi) :
      Γ(X,p.2.val)) * X.presheaf.map (homOfLE p.2.property.1).op
        (s.val ⟨i,V,le_rfl,hi⟩) = s.val p
    rw [s.property.1 i V p.2.val le_rfl hi p.2.property.1]
    exact (s.property.2 p.1 i p.2.val p.2.property.1 p.2.property.2
      (p.2.property.1.trans hi)).symm
  right_inv a := by
    change (c.transition i i V hi hi : Γ(X,V)) *
      X.presheaf.map (homOfLE (show V ≤ V from le_rfl)).op a = a
    rw [c.identity]
    simp
  map_add' _ _ := rfl
  map_smul' a s := by
    change X.presheaf.map (homOfLE (show V ≤ V from le_rfl)).op a * _ = a * _
    simp

lemma chartEquiv_restrict {V W : X.Opens} (h : V ≤ W) (i : ι) (hi : W ≤ U i)
    (s : sections c W) :
    chartEquiv c i (h.trans hi) (restrict c h s) =
      X.presheaf.map (homOfLE h).op (chartEquiv c i hi s) :=
  (s.property.1 i W V le_rfl hi h).symm

lemma chartEquiv_change {V : X.Opens} (i j : ι) (hi : V ≤ U i) (hj : V ≤ U j)
    (s : sections c V) :
    chartEquiv c i hi s = (c.transition i j V hi hj : Γ(X,V)) * chartEquiv c j hj s :=
  s.property.2 i j V le_rfl hi hj

def openPresheafFrame (i : ι) (W : X.Opens) (hW : W ≤ U i) :
    (modulePresheafRestrict W.ι).obj (presheaf c) ≅
      (SheafOfModules.unit W.toScheme.ringCatSheaf).val :=
  (modulePresheafRestrictOpensIso W).app _ ≪≫
    PresheafOfModules.isoMk
      (fun V => (chartEquiv c i ((W.ι_image_le V.unop).trans hW)).toModuleIso)
      (fun {V V'} f => by
        ext s
        exact chartEquiv_restrict c
          (Scheme.Hom.image_mono W.ι (leOfHom f.unop)) i
          ((W.ι_image_le V.unop).trans hW) s)

def chartPresheafFrame (i : ι) :
    (modulePresheafRestrict (U i).ι).obj (presheaf c) ≅
      (SheafOfModules.unit (U i).toScheme.ringCatSheaf).val :=
  openPresheafFrame c i (U i) le_rfl

def sheaf : X.Modules :=
  (PresheafOfModules.sheafification (𝟙 X.ringCatSheaf.obj)).obj (presheaf c)

def openFrame (i : ι) (W : X.Opens) (hW : W ≤ U i) :
    (sheaf c).restrict W.ι ≅ SheafOfModules.unit W.toScheme.ringCatSheaf :=
  (moduleSheafificationRestrict W.ι).app (presheaf c) ≪≫
    (PresheafOfModules.sheafification (𝟙 W.toScheme.ringCatSheaf.obj)).mapIso
      (openPresheafFrame c i W hW) ≪≫
    (asIso (PresheafOfModules.sheafificationAdjunction (R := W.toScheme.ringCatSheaf)
      (𝟙 W.toScheme.ringCatSheaf.obj)).counit).app
      (SheafOfModules.unit W.toScheme.ringCatSheaf)

def lineBundle (hcover : ⊤ ≤ ⨆ i, U i) : LineBundle X where
  sheaf := sheaf c
  locallyRankOne x := by
    have hx : x ∈ ⨆ i, U i := hcover (show x ∈ (⊤ : X.Opens) from trivial)
    obtain ⟨i, hi⟩ := Opens.mem_iSup.mp hx
    exact ⟨U i,hi,⟨openFrame c i (U i) le_rfl⟩⟩

end

open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite

variable {X : Scheme}

def restrictUnit {V W : X.Opens} (h : V ≤ W) : Γ(X,W)ˣ →* Γ(X,V)ˣ :=
  Units.map (X.presheaf.map (homOfLE h).op).hom.toMonoidHom

@[simp] lemma restrictUnit_val {V W : X.Opens} (h : V ≤ W) (a : Γ(X,W)ˣ) :
    (restrictUnit h a : Γ(X,V)) = X.presheaf.map (homOfLE h).op (a : Γ(X,W)) := rfl

@[simp] lemma restrictUnit_trans {V W Z : X.Opens}
    (h : V ≤ W) (k : W ≤ Z) (a : Γ(X,Z)ˣ) :
    restrictUnit h (restrictUnit k a) = restrictUnit (h.trans k) a := by
  apply Units.ext
  change (X.presheaf.map (homOfLE k).op ≫ X.presheaf.map (homOfLE h).op) _ = _
  rw [← Functor.map_comp]
  rfl

@[simp] lemma restrictUnit_refl (V : X.Opens) (a : Γ(X,V)ˣ) :
    restrictUnit (le_refl V) a = a := by
  apply Units.ext
  simp [restrictUnit]

variable {ι : Type} (U : ι → X.Opens)

structure PairCocycle where
  pair (i j : ι) : Γ(X,U i ⊓ U j)ˣ
  identity (i : ι) :
    restrictUnit (show U i ≤ U i ⊓ U i from le_inf le_rfl le_rfl) (pair i i) = 1
  cocycle (i j k : ι) :
    restrictUnit (show (U i ⊓ U j) ⊓ U k ≤ U i ⊓ U j from inf_le_left) (pair i j) *
      restrictUnit (show (U i ⊓ U j) ⊓ U k ≤ U j ⊓ U k from
        le_inf (inf_le_left.trans inf_le_right) inf_le_right) (pair j k) =
      restrictUnit (show (U i ⊓ U j) ⊓ U k ≤ U i ⊓ U k from
        le_inf (inf_le_left.trans inf_le_left) inf_le_right) (pair i k)

variable {U}

def PairCocycle.toCocycle (g : PairCocycle U) : Cocycle U where
  transition i j W hi hj := restrictUnit (le_inf hi hj) (g.pair i j)
  restriction i j {V W} h hi hj := by
    exact congrArg Units.val (restrictUnit_trans h (le_inf hi hj) (g.pair i j))
  identity i W hi := by
    have h := congrArg (restrictUnit hi) (g.identity i)
    simpa only [map_one, restrictUnit_trans] using h
  cocycle i j k W hi hj hk := by
    have h := congrArg (restrictUnit (le_inf (le_inf hi hj) hk)) (g.cocycle i j k)
    simpa only [map_mul, restrictUnit_trans] using h

@[simp] lemma PairCocycle.toCocycle_transition (g : PairCocycle U)
    (i j : ι) (W : X.Opens) (hi : W ≤ U i) (hj : W ≤ U j) :
    g.toCocycle.transition i j W hi hj = restrictUnit (le_inf hi hj) (g.pair i j) := rfl

def PairCocycle.lineBundle (g : PairCocycle U) (hcover : ⊤ ≤ ⨆ i, U i) :
    PiExponentSeshadri.Geometry.LineBundle X :=
  LineBundleGluing.lineBundle g.toCocycle hcover

end PiExponentSeshadri.LineBundleGluing

end

end OAI
end Source0041

section Source0042
/-
Modification notice for the LogTwo project.
Derived from openai/math (Apache-2.0), revision adc7f1241b42e322a6451854ab7e4b4c146bf78a.
Original source: lean/OAI/NumberTheory/PiExponent/Geometry/LineBundleGluingTransitions.lean
Changes: Convert module/import declarations to the Lean 4.34 public module format.
See ../../../../../THIRD_PARTY_NOTICES.txt for provenance and the recorded changes.
-/




namespace OAI

namespace PiExponentSeshadri.LineBundleGluing
noncomputable section
open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite
open PiExponentSeshadri.Geometry PiExponentSeshadri.Frames
variable {X : Scheme} {ι : Type} {U : ι → X.Opens}

def multiply (W : X.Opens) (a : Γ(X,W)) :
    SheafOfModules.unit W.toScheme.ringCatSheaf ⟶
      SheafOfModules.unit W.toScheme.ringCatSheaf :=
  (SheafOfModules.unit W.toScheme.ringCatSheaf).unitHomEquiv.symm
    (PresheafOfModules.sectionsMk
      (fun V => X.presheaf.map (homOfLE (W.ι_image_le V.unop)).op a)
      (fun {V V'} f => by
        change (X.presheaf.map _ ≫ X.presheaf.map _) a = _
        erw [← Functor.map_comp]
        rfl))

lemma multiply_endValue (W : X.Opens) (a : Γ(X,W)) :
    W.topIso.hom (endValue (multiply W a)) = a := by
  change W.topIso.hom ((1 : Γ(X,W.ι ''ᵁ ⊤)) * X.presheaf.map (homOfLE (W.ι_image_le ⊤)).op a) = a
  rw [one_mul]
  simp only [Scheme.Opens.topIso_hom]
  change (X.presheaf.map _ ≫ X.presheaf.map _) a = a
  erw [← Functor.map_comp]
  change X.presheaf.map (𝟙 (op W)) a = a
  exact congrArg (fun q => q a) (X.presheaf.map_id (op W))

variable (c : Cocycle U)

lemma openPresheafFrame_change (i j : ι) (W : X.Opens) (hi : W ≤ U i) (hj : W ≤ U j) :
    (openPresheafFrame c i W hi).hom =
      (openPresheafFrame c j W hj).hom ≫
        (multiply W (c.transition i j W hi hj : Γ(X,W))).val := by
  ext V s
  change chartEquiv c i ((W.ι_image_le V.unop).trans hi) s =
    chartEquiv c j ((W.ι_image_le V.unop).trans hj) s *
      X.presheaf.map (homOfLE (W.ι_image_le V.unop)).op
        (c.transition i j W hi hj : Γ(X,W))
  rw [c.restriction]
  exact (chartEquiv_change c i j ((W.ι_image_le V.unop).trans hi)
    ((W.ι_image_le V.unop).trans hj) s).trans (mul_comm _ _)

lemma openFrame_change (i j : ι) (W : X.Opens) (hi : W ≤ U i) (hj : W ≤ U j) :
    (openFrame c i W hi).hom =
      (openFrame c j W hj).hom ≫ multiply W (c.transition i j W hi hj : Γ(X,W)) := by
  simp only [openFrame]
  let F : PresheafOfModules W.toScheme.ringCatSheaf.obj ⥤ W.toScheme.Modules :=
    PresheafOfModules.sheafification (𝟙 W.toScheme.ringCatSheaf.obj)
  let O : W.toScheme.Modules := SheafOfModules.unit W.toScheme.ringCatSheaf
  let a : (sheaf c).restrict W.ι ⟶ F.obj ((modulePresheafRestrict W.ι).obj (presheaf c)) :=
    (moduleSheafificationRestrict W.ι).hom.app (presheaf c)
  let b : F.obj O.val ⟶ O :=
    (PresheafOfModules.sheafificationAdjunction (𝟙 W.toScheme.ringCatSheaf.obj)).counit.app O
  let f := (openPresheafFrame c i W hi).hom
  let g := (openPresheafFrame c j W hj).hom
  let t : O ⟶ O := multiply W (c.transition i j W hi hj : Γ(X, W))
  have hf : f = g ≫ t.val := openPresheafFrame_change c i j W hi hj
  have hb : F.map t.val ≫ b = b ≫ t :=
    (PresheafOfModules.sheafificationAdjunction (𝟙 W.toScheme.ringCatSheaf.obj)).counit.naturality t
  change a ≫ F.map f ≫ b = (a ≫ F.map g ≫ b) ≫ t
  calc
    _ = a ≫ F.map (g ≫ t.val) ≫ b := congrArg (fun h => a ≫ F.map h ≫ b) hf
    _ = a ≫ F.map g ≫ (F.map t.val ≫ b) := by rw [F.map_comp, Category.assoc]
    _ = a ≫ F.map g ≫ (b ≫ t) := congrArg (fun h => a ≫ F.map g ≫ h) hb
    _ = _ := by simp only [Category.assoc]

lemma openFrame_frameChange (i j : ι) (W : X.Opens) (hi : W ≤ U i) (hj : W ≤ U j) :
    W.topIso.hom (frameChange (openFrame c j W hj) (openFrame c i W hi) : Γ(W.toScheme,⊤)) =
      (c.transition i j W hi hj : Γ(X,W)) := by
  change W.topIso.hom (endValue ((openFrame c j W hj).inv ≫ (openFrame c i W hi).hom)) = _
  have h := congrArg (fun t => (openFrame c j W hj).inv ≫ t)
    (openFrame_change c i j W hi hj)
  have he := h.trans ((openFrame c j W hj).inv_hom_id_assoc
    (multiply W (c.transition i j W hi hj : Γ(X, W))))
  exact (congrArg (fun t => W.topIso.hom (endValue t)) he).trans (multiply_endValue W _)

end
end PiExponentSeshadri.LineBundleGluing

end OAI
end Source0042

section Source0043
/-
Modification notice for the LogTwo project.
Derived from openai/math (Apache-2.0), revision adc7f1241b42e322a6451854ab7e4b4c146bf78a.
Original source: lean/OAI/NumberTheory/PiExponent/Ampleness/NumericalAmpleness.lean
Changes: Convert module/import declarations to the Lean 4.34 public module format.
See ../../../../../THIRD_PARTY_NOTICES.txt for provenance and the recorded changes.
-/




namespace OAI

namespace PiExponent.NumericalAmpleness
noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace
open PiExponentSeshadri.Geometry PiExponentSeshadri.Frames
open scoped AlgebraicGeometry

theorem open_eq_top_of_subsingleton {X : Scheme} [Subsingleton X]
    (U : X.Opens) (x : X) (hx : x ∈ U) : U = ⊤ := by
  apply top_unique
  intro y _
  simpa only [Subsingleton.elim y x] using hx

theorem exists_global_frame_of_top_frame {X : Scheme} (M : X.Modules)
    (e : M.restrict (⊤ : X.Opens).ι ≅ O (⊤ : X.Opens).toScheme) :
    ∃ s : GlobalSections X M, sectionOpen X s = ⊤ := by
  let s := (moduleSectionEquiv M).symm (openSectionEquiv M ⊤ e.inv)
  have hs : restrictSection (⊤ : X.Opens).ι s = e.inv := by
    apply (openSectionEquiv M ⊤).injective
    rw [openSectionEquiv_restrict]
    exact (moduleSectionEquiv M).apply_symm_apply _
  have hi : IsIso (restrictSection (⊤ : X.Opens).ι s) := by rw [hs]; infer_instance
  let := (Scheme.Modules.restrictUnitIso (⊤ : X.Opens).ι).isIso_inv
  have hi' : IsIso ((Scheme.Modules.restrictFunctor (⊤ : X.Opens).ι).map s) := by
    exact (isIso_comp_left_iff (Scheme.Modules.restrictUnitIso (⊤ : X.Opens).ι).inv _).mp hi
  refine ⟨s, top_unique ?_⟩
  exact le_iSup_of_le ⊤ (le_iSup_of_le hi' le_rfl)

theorem isAmple_of_subsingleton {X : Scheme} [Subsingleton X]
    (L : LineBundle X) : L.IsAmple := by
  intro x V hx
  have hV : V = ⊤ := open_eq_top_of_subsingleton V x hx
  obtain ⟨U, hxU, ⟨e⟩⟩ := (L.pow 1).locallyRankOne x
  have hU : U = ⊤ := open_eq_top_of_subsingleton U x hxU
  subst U
  obtain ⟨s, hs⟩ := exists_global_frame_of_top_frame (L.pow 1).sheaf e
  change GlobalSections X (modulePow X L.sheaf 1) at s
  change sectionOpen X s = ⊤ at hs
  obtain ⟨W, hWa, hxW, -⟩ := exists_isAffineOpen_mem_and_subset (Opens.mem_top x)
  have hW : W = ⊤ := open_eq_top_of_subsingleton W x hxW
  refine ⟨1, by decide, s, ?_, ?_, ?_⟩
  · rw [hs]; trivial
  · rw [hs, hV]
  · rw [hs, ← hW]; exact hWa

theorem isAmple_of_integral_dimension_zero {X : Scheme}
    [IsIntegral X] [IsLocallyNoetherian X] (hdim : topologicalKrullDim X ≤ 0)
    (L : LineBundle X) : L.IsAmple := by
  let : IsLocallyArtinian X := IsLocallyArtinian.of_topologicalKrullDim_le_zero hdim
  let : Subsingleton X := ⟨fun x y =>
    (PreirreducibleSpace.isPreirreducible_univ (X := X)).subsingleton
      (Set.mem_univ x) (Set.mem_univ y)⟩
  exact isAmple_of_subsingleton L

structure IntegralCurve (X : Scheme) where
  scheme : Scheme
  embedding : scheme ⟶ X
  closedImmersion : IsClosedImmersion embedding
  integral : IsIntegral scheme
  dimension : topologicalKrullDim scheme = 1

attribute [instance] IntegralCurve.closedImmersion IntegralCurve.integral

theorem no_integralCurve_of_dimension_zero {X : Scheme}
    (hdim : topologicalKrullDim X ≤ 0) : IsEmpty (IntegralCurve X) := by
  refine ⟨fun C => ?_⟩
  have hh := C.embedding.isClosedEmbedding.isEmbedding.topologicalKrullDim_le
  rw [C.dimension] at hh
  have : (1 : WithBot ℕ∞) ≤ 0 := hh.trans hdim
  norm_num at this

end
end PiExponent.NumericalAmpleness

end OAI
end Source0043

section Source0044
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
end Source0044

section Source0045
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
end Source0045

section Source0046
/-
Modification notice for the LogTwo project.
Derived from openai/math (Apache-2.0), revision adc7f1241b42e322a6451854ab7e4b4c146bf78a.
Original source: lean/OAI/NumberTheory/PiExponent/Approximation/NumericalMarginRestriction.lean
Changes: Convert module/import declarations to the Lean 4.34 public module format.
See ../../../../../THIRD_PARTY_NOTICES.txt for provenance and the recorded changes.
-/




namespace OAI

namespace PiExponent.NumericalAmpleness
noncomputable section
open CategoryTheory AlgebraicGeometry TopologicalSpace
open PiExponentSeshadri.Geometry

def curveDegree {X : Scheme.{0}} (p : X ⟶ Spec (CommRingCat.of ℂ))
    (L : LineBundle X) (C : IntegralCurve X) : ℤ :=
  eulerCharacteristic (C.embedding ≫ p) 1
    ((Scheme.Modules.pullback C.embedding).obj L.sheaf) -
  eulerCharacteristic (C.embedding ≫ p) 1 (structureSheaf C.scheme)

def IntegralCurve.mapClosed {X Y : Scheme.{0}} (C : IntegralCurve Y)
    (i : Y ⟶ X) [IsClosedImmersion i] : IntegralCurve X where
  scheme := C.scheme
  embedding := C.embedding ≫ i
  closedImmersion := inferInstance
  integral := C.integral
  dimension := C.dimension

theorem curveDegree_mapClosed {X Y : Scheme.{0}} (p : X ⟶ Spec (CommRingCat.of ℂ))
    (L : LineBundle X) (i : Y ⟶ X) [IsClosedImmersion i] (C : IntegralCurve Y) :
    curveDegree p L (C.mapClosed i) = curveDegree (i ≫ p) (L.pullback i) C := by
  unfold curveDegree IntegralCurve.mapClosed LineBundle.pullback
  simp only [Category.assoc]
  congr 1
  exact eulerCharacteristic_iso (C.embedding ≫ i ≫ p)
    ((Scheme.Modules.pullbackComp C.embedding i).app L.sheaf).symm 1

theorem uniform_curve_margin_restrict {X Y : Scheme.{0}}
    (p : X ⟶ Spec (CommRingCat.of ℂ)) (L H : LineBundle X) (ε : ℝ)
    (hmargin : ∀ C : IntegralCurve X,
      ε * (curveDegree p H C : ℝ) ≤ (curveDegree p L C : ℝ))
    (i : Y ⟶ X) [IsClosedImmersion i] :
    ∀ C : IntegralCurve Y,
      ε * (curveDegree (i ≫ p) (H.pullback i) C : ℝ) ≤
        (curveDegree (i ≫ p) (L.pullback i) C : ℝ) := by
  intro C
  simpa only [curveDegree_mapClosed] using hmargin (C.mapClosed i)

theorem proper_closed_dimension_succ_le {X Y : Type*}
    [TopologicalSpace X] [TopologicalSpace Y] [IrreducibleSpace X] [Nonempty Y]
    (f : Y → X) (hf : Topology.IsClosedEmbedding f)
    (hproper : Set.range f ≠ Set.univ) :
    topologicalKrullDim Y + 1 ≤ topologicalKrullDim X := by
  let T : IrreducibleCloseds X := ⟨Set.univ, IrreducibleSpace.isIrreducible_univ X, isClosed_univ⟩
  let g := IrreducibleCloseds.map f hf.continuous
  have hg : StrictMono g := IrreducibleCloseds.map_strictMono_of_isInducing hf.isEmbedding.isInducing
  have hlt (Z : IrreducibleCloseds Y) : g Z < T := by
    apply lt_of_le_of_ne
    · intro x hx; trivial
    · intro he
      apply hproper
      apply Set.eq_univ_of_forall
      intro x
      have hx : x ∈ (g Z : Set X) := by rw [he]; trivial
      exact closure_minimal (Set.image_subset_range f _) hf.isClosed_range hx
  let k : WithTop (IrreducibleCloseds Y) → IrreducibleCloseds X := WithTop.recTopCoe T g
  have hk : StrictMono k := WithTop.strictMono_iff.mpr ⟨hg, hlt⟩
  have : Nonempty (IrreducibleCloseds Y) := by
    obtain ⟨y⟩ := ‹Nonempty Y›
    exact ⟨⟨closure {y}, isIrreducible_singleton.closure, isClosed_closure⟩⟩
  have hh := Order.krullDim_le_of_strictMono k hk
  simpa only [Order.krullDim_WithTop, topologicalKrullDim] using hh

theorem proper_closed_subscheme_dimension_succ_le {X Y : Scheme.{0}}
    [IsIntegral X] [Nonempty Y] (i : Y ⟶ X) [IsClosedImmersion i]
    (hproper : ¬ Function.Surjective i) :
    topologicalKrullDim Y + 1 ≤ topologicalKrullDim X :=
  proper_closed_dimension_succ_le i i.isClosedEmbedding
    (fun h => hproper (Set.range_eq_univ.mp h))

end
end PiExponent.NumericalAmpleness

end OAI
end Source0046

section Source0047
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
end Source0047

section Source0048
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
end Source0048

section Source0049
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
end Source0049

section Source0050
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
end Source0050

section Source0051
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
end Source0051

section Source0052
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
end Source0052

section Source0053
/-
Modification notice for the LogTwo project.
Derived from openai/math (Apache-2.0), revision adc7f1241b42e322a6451854ab7e4b4c146bf78a.
Original source: lean/OAI/NumberTheory/PiExponent/Approximation/OpenPullbackUnit.lean
Changes: Convert module/import declarations to the Lean 4.34 public module format.
See ../../../../../THIRD_PARTY_NOTICES.txt for provenance and the recorded changes.
-/
end Source0053

section Source0054
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
end Source0054

section Source0055
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
end Source0055

section Source0056
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
end Source0056

section Source0057
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
end Source0057

section Source0058
/-
Modification notice for the LogTwo project.
Derived from openai/math (Apache-2.0), revision adc7f1241b42e322a6451854ab7e4b4c146bf78a.
Original source: lean/OAI/NumberTheory/PiExponent/Cohomology/NakaiCohomology.lean
Changes: Convert module/import declarations to the Lean 4.34 public module format.
See ../../../../../THIRD_PARTY_NOTICES.txt for provenance and the recorded changes.
-/




namespace OAI

namespace PiExponent.NumericalAmpleness
noncomputable section
open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian AlgebraicGeometry
open PiExponentSeshadri.Geometry
variable {X : Scheme.{0}}

def cohomologyMap (p : X ⟶ Spec (CommRingCat.of ℂ)) {M N : X.Modules}
    (f : M ⟶ N) (n : ℕ) :
    let _ := Module.compHom (cohomology M n) (baseScalars p)
    let _ := Module.compHom (cohomology N n) (baseScalars p)
    cohomology M n →ₗ[ℂ] cohomology N n := by
  dsimp only
  letI := Module.compHom (cohomology M n) (baseScalars p)
  letI := Module.compHom (cohomology N n) (baseScalars p)
  let g := (Ext.mk₀ f).postcompOfLinear Γ(X,⊤) (structureSheaf X) (add_zero n)
  exact { g.toAddHom with map_smul' := fun r x => g.map_smul (baseScalars p r) x }

theorem globalSections_surjective_of_h1_stationary
    (p : X ⟶ Spec (CommRingCat.of ℂ)) (S : ShortComplex X.Modules) (hS : S.ShortExact)
    (hfinite₁ : let _ := Module.compHom (cohomology S.X₁ 1) (baseScalars p)
      FiniteDimensional ℂ (cohomology S.X₁ 1))
    (hfinite₂ : let _ := Module.compHom (cohomology S.X₂ 1) (baseScalars p)
      FiniteDimensional ℂ (cohomology S.X₂ 1))
    (hrank : cohomologyDimension p S.X₁ 1 = cohomologyDimension p S.X₂ 1)
    (hzero : ∀ z : cohomology S.X₃ 1, z = 0) :
    Function.Surjective (fun s : GlobalSections X S.X₂ => s ≫ S.g) := by
  let := Module.compHom (cohomology S.X₁ 1) (baseScalars p)
  let := Module.compHom (cohomology S.X₂ 1) (baseScalars p)
  have : FiniteDimensional ℂ (cohomology S.X₁ 1) := hfinite₁
  have : FiniteDimensional ℂ (cohomology S.X₂ 1) := hfinite₂
  let f := cohomologyMap p S.f 1
  have hsurj : Function.Surjective f := by
    intro b
    obtain ⟨a,ha⟩ := Ext.covariant_sequence_exact₂ (structureSheaf X) hS b (hzero _)
    exact ⟨a,ha⟩
  have hinj : Function.Injective f :=
    (LinearMap.injective_iff_surjective_of_finrank_eq_finrank hrank).mpr hsurj
  intro s
  have hboundary : (Ext.mk₀ s).comp hS.extClass rfl = 0 := by
    apply hinj
    change ((Ext.mk₀ s).comp hS.extClass rfl).comp (Ext.mk₀ S.f) (add_zero 1) = f 0
    rw [map_zero]
    rw [Ext.comp_assoc_of_third_deg_zero, hS.extClass_comp, Ext.comp_zero]
  obtain ⟨a,ha⟩ := Ext.covariant_sequence_exact₃ (structureSheaf X) hS (Ext.mk₀ s) rfl hboundary
  refine ⟨Ext.homEquiv₀ a, ?_⟩
  apply (Ext.mk₀_bijective (structureSheaf X) S.X₃).injective
  rw [← Ext.mk₀_comp_mk₀, Ext.mk₀_homEquiv₀_apply]
  exact ha

theorem eventually_constant_of_antitone_nat (a : ℕ → ℕ) (ha : Antitone a) :
    ∃ N, ∀ n, N ≤ n → a n = a N := by
  classical
  have he : ∃ k : ℕ, ∃ n, a n = k := ⟨a 0,0,rfl⟩
  obtain ⟨N,hN⟩ := Nat.find_spec he
  refine ⟨N,fun n hn => le_antisymm (ha hn) ?_⟩
  rw [hN]
  exact Nat.find_min' he ⟨n,rfl⟩

theorem eventual_globalSections_surjective
    (p : X ⟶ Spec (CommRingCat.of ℂ)) (F Q : ℕ → X.Modules)
    (f : ∀ n, F n ⟶ F (n+1)) (g : ∀ n, F (n+1) ⟶ Q n)
    (hcomp : ∀ n, f n ≫ g n = 0)
    (hshort : ∀ n, (ShortComplex.mk (f n) (g n) (hcomp n)).ShortExact)
    (hfinite : ∀ n, let _ := Module.compHom (cohomology (F n) 1) (baseScalars p)
      FiniteDimensional ℂ (cohomology (F n) 1))
    (hzero : ∃ N, ∀ n, N ≤ n → ∀ z : cohomology (Q n) 1, z = 0) :
    ∃ N, ∀ n, N ≤ n →
      Function.Surjective (fun s : GlobalSections X (F (n+1)) => s ≫ g n) := by
  obtain ⟨N₀,hN₀⟩ := hzero
  have hdim (n : ℕ) (hn : N₀ ≤ n) :
      cohomologyDimension p (F (n+1)) 1 ≤ cohomologyDimension p (F n) 1 := by
    let := Module.compHom (cohomology (F n) 1) (baseScalars p)
    let := Module.compHom (cohomology (F (n+1)) 1) (baseScalars p)
    have : FiniteDimensional ℂ (cohomology (F n) 1) := hfinite n
    have hsurj : Function.Surjective (cohomologyMap p (f n) 1) := by
      intro b
      exact Ext.covariant_sequence_exact₂ (structureSheaf X) (hshort n) b (hN₀ n hn _)
    exact LinearMap.finrank_le_finrank_of_surjective hsurj
  let a : ℕ → ℕ := fun n => cohomologyDimension p (F (N₀+n)) 1
  have ha : Antitone a := antitone_nat_of_succ_le (fun n => by
    simpa only [a, Nat.add_assoc] using hdim (N₀+n) (Nat.le_add_right _ _))
  obtain ⟨N,hN⟩ := eventually_constant_of_antitone_nat a ha
  refine ⟨N₀+N,fun n hn => ?_⟩
  have hn₀ : N₀ ≤ n := by omega
  obtain ⟨k,rfl⟩ := Nat.exists_eq_add_of_le hn₀
  have hk : N ≤ k := by omega
  have he : cohomologyDimension p (F (N₀+k)) 1 =
      cohomologyDimension p (F (N₀+k+1)) 1 := by
    exact (hN k hk).trans (by simpa only [a, Nat.add_assoc] using (hN (k+1) (by omega)).symm)
  exact globalSections_surjective_of_h1_stationary p
    (ShortComplex.mk (f (N₀+k)) (g (N₀+k)) (hcomp (N₀+k)))
    (hshort (N₀+k)) (hfinite _) (hfinite _) he (hN₀ _ (by omega))

theorem cohomologyMap_bijective_of_quotient_vanishing
    (p : X ⟶ Spec (CommRingCat.of ℂ)) (S : ShortComplex X.Modules) (hS : S.ShortExact)
    (n : ℕ) (hprev : ∀ z : cohomology S.X₃ n, z = 0)
    (hnext : ∀ z : cohomology S.X₃ (n+1), z = 0) :
    Function.Bijective (cohomologyMap p S.f (n+1)) := by
  let := Module.compHom (cohomology S.X₁ (n+1)) (baseScalars p)
  let := Module.compHom (cohomology S.X₂ (n+1)) (baseScalars p)
  constructor
  · apply (injective_iff_map_eq_zero (cohomologyMap p S.f (n+1))).mpr
    intro a ha
    obtain ⟨b,hb⟩ := Ext.covariant_sequence_exact₁ (structureSheaf X) hS a ha rfl
    rw [hprev b, Ext.zero_comp] at hb
    exact hb.symm
  · intro b
    exact Ext.covariant_sequence_exact₂ (structureSheaf X) hS b (hnext _)

theorem cohomologyDimension_eq_of_quotient_vanishing
    (p : X ⟶ Spec (CommRingCat.of ℂ)) (S : ShortComplex X.Modules) (hS : S.ShortExact)
    (n : ℕ) (hprev : ∀ z : cohomology S.X₃ n, z = 0)
    (hnext : ∀ z : cohomology S.X₃ (n+1), z = 0) :
    cohomologyDimension p S.X₁ (n+1) = cohomologyDimension p S.X₂ (n+1) := by
  let := Module.compHom (cohomology S.X₁ (n+1)) (baseScalars p)
  let := Module.compHom (cohomology S.X₂ (n+1)) (baseScalars p)
  exact (LinearEquiv.ofBijective (cohomologyMap p S.f (n+1))
    (cohomologyMap_bijective_of_quotient_vanishing p S hS n hprev hnext)).finrank_eq

theorem eventual_cohomologyDimension_constant_of_two_sequences
    (p : X ⟶ Spec (CommRingCat.of ℂ)) (F B Q R : ℕ → X.Modules)
    (f : ∀ n, F n ⟶ B n) (g : ∀ n, B n ⟶ Q n)
    (f' : ∀ n, F (n+1) ⟶ B n) (g' : ∀ n, B n ⟶ R n)
    (hcomp : ∀ n, f n ≫ g n = 0) (hcomp' : ∀ n, f' n ≫ g' n = 0)
    (hshort : ∀ n, (ShortComplex.mk (f n) (g n) (hcomp n)).ShortExact)
    (hshort' : ∀ n, (ShortComplex.mk (f' n) (g' n) (hcomp' n)).ShortExact)
    (q : ℕ)
    (hzero : ∃ N, ∀ n, N ≤ n →
      (∀ z : cohomology (Q n) q, z = 0) ∧
      (∀ z : cohomology (Q n) (q+1), z = 0) ∧
      (∀ z : cohomology (R n) q, z = 0) ∧
      (∀ z : cohomology (R n) (q+1), z = 0)) :
    ∃ N, ∀ n, N ≤ n → cohomologyDimension p (F n) (q+1) =
      cohomologyDimension p (F N) (q+1) := by
  obtain ⟨N,hN⟩ := hzero
  have hstep (n : ℕ) (hn : N ≤ n) :
      cohomologyDimension p (F n) (q+1) = cohomologyDimension p (F (n+1)) (q+1) := by
    obtain ⟨hQ₀,hQ₁,hR₀,hR₁⟩ := hN n hn
    exact (cohomologyDimension_eq_of_quotient_vanishing p _ (hshort n) q hQ₀ hQ₁).trans
      (cohomologyDimension_eq_of_quotient_vanishing p _ (hshort' n) q hR₀ hR₁).symm
  refine ⟨N, fun n hn => ?_⟩
  obtain ⟨k,rfl⟩ := Nat.exists_eq_add_of_le hn
  induction k with
  | zero => simp
  | succ k ih =>
    exact (hstep (N+k) (by omega)).symm.trans (ih (by omega))

end
end PiExponent.NumericalAmpleness

end OAI
end Source0058

section Source0059
/-
Modification notice for the LogTwo project.
Derived from openai/math (Apache-2.0), revision adc7f1241b42e322a6451854ab7e4b4c146bf78a.
Original source: lean/OAI/NumberTheory/PiExponent/Cohomology/NakaiEulerGrowth.lean
Changes: Convert module/import declarations to the Lean 4.34 public module format.
See ../../../../../THIRD_PARTY_NOTICES.txt for provenance and the recorded changes.
-/




namespace OAI

namespace PiExponent.NumericalAmpleness

noncomputable section

open CategoryTheory CategoryTheory.Abelian AlgebraicGeometry Filter
open PiExponentSeshadri.Geometry
open scoped BigOperators

variable {X : Scheme.{0}}

theorem exists_nonzero_globalSection_of_cohomologyDimension_pos
    (p : X ⟶ Spec (CommRingCat.of ℂ)) (M : X.Modules)
    (hpos : 0 < cohomologyDimension p M 0) :
    ∃ s : GlobalSections X M, s ≠ 0 := by
  let := Module.compHom (cohomology M 0) (baseScalars p)
  have : Nontrivial (cohomology M 0) := Module.nontrivial_of_finrank_pos hpos
  obtain ⟨z,hz⟩ := exists_ne (0 : cohomology M 0)
  refine ⟨Ext.homEquiv₀ z, ?_⟩
  intro hs
  apply hz
  have hzero := congrArg (fun s : GlobalSections X M => Ext.mk₀ s) hs
  simpa only [Ext.mk₀_homEquiv₀_apply, Ext.mk₀_zero] using hzero

theorem eulerCharacteristic_eq_zero_sub_one_add_tail
    (p : X ⟶ Spec (CommRingCat.of ℂ)) (M : X.Modules) (d : ℕ) (hd : 1 ≤ d) :
    eulerCharacteristic p d M =
      (cohomologyDimension p M 0 : ℤ) - (cohomologyDimension p M 1 : ℤ) +
        ∑ i ∈ Finset.range (d - 1),
          (-1 : ℤ) ^ (i + 2) * (cohomologyDimension p M (i + 2) : ℤ) := by
  unfold eulerCharacteristic
  rw [show d + 1 = 2 + (d - 1) by omega, Finset.sum_range_add]
  simp only [Finset.sum_range_succ, Finset.range_zero, Finset.sum_empty,
    pow_zero, one_mul, zero_add, pow_one, neg_one_mul]
  simp only [Nat.add_comm 2, sub_eq_add_neg]

theorem eventually_nonzero_globalSection_of_euler_growth
    (p : X ⟶ Spec (CommRingCat.of ℂ)) (F : ℕ → X.Modules)
    (d : ℕ) (hd : 1 ≤ d)
    (hgrowth : Tendsto (fun n => eulerCharacteristic p d (F n)) atTop atTop)
    (hconstant : ∀ i, 2 ≤ i → i ≤ d →
      ∃ c : ℕ, ∀ᶠ n in atTop, cohomologyDimension p (F n) i = c) :
    ∀ᶠ n in atTop, ∃ s : GlobalSections X (F n), s ≠ 0 := by
  classical
  have hh (i : Fin (d - 1)) :
      ∃ c : ℕ, ∀ᶠ n in atTop, cohomologyDimension p (F n) (i.val + 2) = c := by
    apply hconstant (i.val + 2) (by omega) (by have := i.isLt; omega)
  choose c hc using hh
  let C : ℤ := ∑ i : Fin (d - 1), (-1 : ℤ) ^ (i.val + 2) * (c i : ℤ)
  have hall : ∀ᶠ n in atTop,
      ∀ i : Fin (d - 1), cohomologyDimension p (F n) (i.val + 2) = c i :=
    Filter.eventually_all.mpr hc
  have hlarge : ∀ᶠ n in atTop, C < eulerCharacteristic p d (F n) :=
    hgrowth.eventually (eventually_gt_atTop C)
  filter_upwards [hall, hlarge] with n hn hχ
  apply exists_nonzero_globalSection_of_cohomologyDimension_pos p (F n)
  have htail : (∑ i ∈ Finset.range (d - 1),
      (-1 : ℤ) ^ (i + 2) * (cohomologyDimension p (F n) (i + 2) : ℤ)) = C := by
    rw [← Fin.sum_univ_eq_sum_range]
    apply Finset.sum_congr rfl
    intro i _
    rw [hn i]
  rw [eulerCharacteristic_eq_zero_sub_one_add_tail p (F n) d hd, htail] at hχ
  have hnonneg : (0 : ℤ) ≤ (cohomologyDimension p (F n) 1 : ℤ) := Int.natCast_nonneg _
  omega

theorem eventually_nonzero_globalSection_of_eventually_stationary
    (p : X ⟶ Spec (CommRingCat.of ℂ)) (F : ℕ → X.Modules)
    (d : ℕ) (hd : 1 ≤ d)
    (hgrowth : Tendsto (fun n => eulerCharacteristic p d (F n)) atTop atTop)
    (hstationary : ∀ i, 2 ≤ i → i ≤ d →
      ∃ N, ∀ n, N ≤ n → cohomologyDimension p (F n) i =
        cohomologyDimension p (F N) i) :
    ∀ᶠ n in atTop, ∃ s : GlobalSections X (F n), s ≠ 0 := by
  apply eventually_nonzero_globalSection_of_euler_growth p F d hd hgrowth
  intro i hi hid
  obtain ⟨N,hN⟩ := hstationary i hi hid
  refine ⟨cohomologyDimension p (F N) i, ?_⟩
  filter_upwards [eventually_ge_atTop N] with n hn
  exact hN n hn

end
end PiExponent.NumericalAmpleness

end OAI
end Source0059

section Source0060
/-
Modification notice for the LogTwo project.
Derived from openai/math (Apache-2.0), revision adc7f1241b42e322a6451854ab7e4b4c146bf78a.
Original source: lean/OAI/NumberTheory/PiExponent/Ampleness/NakaiCartier.lean
Changes: Convert module/import declarations to the Lean 4.34 public module format.
See ../../../../../THIRD_PARTY_NOTICES.txt for provenance and the recorded changes.
-/




namespace OAI

namespace PiExponent.NumericalAmpleness
noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open PiExponentSeshadri.Geometry
variable {X : Scheme.{0}}

private lemma mono_iso_inv_comp {C : Type*} [Category C] {A B D : C}
    (e : A ≅ B) (f : A ⟶ D) [Mono f] : Mono (e.inv ≫ f) := inferInstance

def cartierPowerMultiply (L : LineBundle X) (s : GlobalSections X L.sheaf) (n : ℕ) :
    modulePow X L.sheaf n ⟶ modulePow X L.sheaf (n+1) :=
  (moduleTensorUnit (modulePow X L.sheaf n)).inv ≫
    moduleTensorMap s (𝟙 (modulePow X L.sheaf n))

theorem cartierPowerMultiply_mono [IsIntegral X] (L : LineBundle X)
    (s : GlobalSections X L.sheaf) (hs : s ≠ 0) (n : ℕ) :
    Mono (cartierPowerMultiply L s n) := by
  let := L.mono_section s hs
  have hm : Mono (moduleTensorMap s (𝟙 (modulePow X L.sheaf n))) :=
    moduleTensorMap_mono s (L.pow n)
  exact @mono_iso_inv_comp X.Modules _ _ _ _
    (moduleTensorUnit (modulePow X L.sheaf n)) _ hm

def cartierPowerQuotient (L : LineBundle X) (s : GlobalSections X L.sheaf) (n : ℕ) :
    X.Modules := cokernel (cartierPowerMultiply L s n)

def cartierPowerSequence (L : LineBundle X) (s : GlobalSections X L.sheaf) (n : ℕ) :
    ShortComplex X.Modules :=
  ShortComplex.mk (cartierPowerMultiply L s n) (cokernel.π _) (cokernel.condition _)

theorem cartierPowerSequence_shortExact [IsIntegral X] (L : LineBundle X)
    (s : GlobalSections X L.sheaf) (hs : s ≠ 0) (n : ℕ) :
    (cartierPowerSequence L s n).ShortExact := by
  have := cartierPowerMultiply_mono L s hs n
  change (ShortComplex.mk (cartierPowerMultiply L s n) (cokernel.π _)
    (cokernel.condition _)).ShortExact
  exact { exact := ShortComplex.exact_cokernel _ }

theorem cartierPowerMultiply_restrict_isIso (L : LineBundle X)
    (s : GlobalSections X L.sheaf) (n : ℕ) (U : X.Opens)
    [IsIso ((Scheme.Modules.restrictFunctor U.ι).map s)] :
    IsIso ((Scheme.Modules.restrictFunctor U.ι).map (cartierPowerMultiply L s n)) := by
  let R := Scheme.Modules.restrictFunctor U.ι
  have h : IsIso (R.map (moduleTensorMap s (𝟙 (modulePow X L.sheaf n)))) := by
    apply (isIso_comp_right_iff _ (moduleTensorRestrict U L.sheaf _).hom).mp
    rw [moduleTensorRestrict_natural]
    infer_instance
  change IsIso (R.map ((moduleTensorUnit _).inv ≫ moduleTensorMap s (𝟙 _)))
  rw [Functor.map_comp]
  infer_instance

theorem cartierPowerQuotient_restrict_isZero (L : LineBundle X)
    (s : GlobalSections X L.sheaf) (n : ℕ) :
    IsZero ((cartierPowerQuotient L s n).restrict (sectionOpen X s).ι) := by
  let R := Scheme.Modules.restrictFunctor (sectionOpen X s).ι
  have : IsIso (R.map s) := PiExponentSeshadri.SectionOpens.isIso_restrict_isoOpen s
  have : IsIso (R.map (cartierPowerMultiply L s n)) :=
    cartierPowerMultiply_restrict_isIso L s n (sectionOpen X s)
  have hz : R.map (cokernel.π (cartierPowerMultiply L s n)) = 0 := by
    apply (cancel_epi (R.map (cartierPowerMultiply L s n))).mp
    rw [← R.map_comp, cokernel.condition, Functor.map_zero, comp_zero]
  have hπ : Epi (R.map (cokernel.π (cartierPowerMultiply L s n))) :=
    R.map_epi (cokernel.π (cartierPowerMultiply L s n))
  exact @IsZero.of_epi_eq_zero (sectionOpen X s).toScheme.Modules _ _ _ _
    (R.map (cokernel.π (cartierPowerMultiply L s n))) hπ hz

theorem eventual_cartierPower_sections_lift [IsIntegral X]
    (p : X ⟶ Spec (CommRingCat.of ℂ)) (L : LineBundle X)
    (s : GlobalSections X L.sheaf) (hs : s ≠ 0)
    (hfinite : ∀ n,
      let _ := Module.compHom (cohomology (modulePow X L.sheaf n) 1) (baseScalars p)
      FiniteDimensional ℂ (cohomology (modulePow X L.sheaf n) 1))
    (hzero : ∃ N, ∀ n, N ≤ n → ∀ z : cohomology (cartierPowerQuotient L s n) 1,
      z = 0) :
    ∃ N, ∀ n, N ≤ n → Function.Surjective
      (fun t : GlobalSections X (modulePow X L.sheaf (n+1)) =>
        t ≫ cokernel.π (cartierPowerMultiply L s n)) := by
  exact eventual_globalSections_surjective p (fun n => modulePow X L.sheaf n)
    (cartierPowerQuotient L s) (cartierPowerMultiply L s) (fun n => cokernel.π _)
    (fun n => cokernel.condition _) (fun n => cartierPowerSequence_shortExact L s hs n)
    hfinite hzero

end
end PiExponent.NumericalAmpleness

end OAI
end Source0060

section Source0061
/-
Modification notice for the LogTwo project.
Derived from openai/math (Apache-2.0), revision adc7f1241b42e322a6451854ab7e4b4c146bf78a.
Original source: lean/OAI/NumberTheory/PiExponent/Geometry/CartierPowerFrames.lean
Changes: Convert module/import declarations to the Lean 4.34 public module format.
See ../../../../../THIRD_PARTY_NOTICES.txt for provenance and the recorded changes.
-/




namespace OAI

namespace PiExponent.CartierPowerFrames
noncomputable section
open AlgebraicGeometry CategoryTheory TopologicalSpace
open PiExponentSeshadri.Geometry PiExponentSeshadri.Frames
variable {X : Scheme.{0}}
def sectionMultiplyLeft (L M : X.Modules) (s : structureSheaf X ⟶ L) :
    M ⟶ moduleTensor X L M :=
  (moduleTensorUnit M).inv ≫ moduleTensorMap s (𝟙 M)

def tensorFrame (L M : X.Modules) (U : X.Opens)
    (e : L.restrict U.ι ≅ O U.toScheme)
    (f : M.restrict U.ι ≅ O U.toScheme) :
    (moduleTensor X L M).restrict U.ι ≅ O U.toScheme :=
  moduleTensorRestrict U L M ≪≫ moduleTensorIso e f ≪≫
    moduleTensorUnit (O U.toScheme)

def tensorUnitTwist (M : X.Modules) (U : X.Opens)
    (f : M.restrict U.ι ≅ O U.toScheme) : O U.toScheme ≅ O U.toScheme :=
  f.symm ≪≫ (Scheme.Modules.restrictFunctor U.ι).mapIso (moduleTensorUnit M).symm ≪≫
    moduleTensorRestrict U (O X) M ≪≫
      moduleTensorIso (Scheme.Modules.restrictUnitIso U.ι) f ≪≫ moduleTensorUnit (O U.toScheme)

private lemma frame_section {C : Type*} [Category C] {A B D : C}
    (u : A ≅ B) (s : A ⟶ D) (e : D ≅ B) :
    s ≫ e.hom = u.hom ≫ ((u.inv ≫ s) ≫ e.hom) := by
  simp

private lemma framed_multiply {C : Type*} [Category C] {A B D P Q T O : C}
    (g : O ⟶ A) (k : A ⟶ B) (m : B ⟶ D) (r : B ⟶ P) (r' : D ⟶ Q)
    (e : P ⟶ T) (e' : Q ⟶ T) (u : T ⟶ O) (a : O ⟶ O)
    (p : P ⟶ Q) (b : T ⟶ T)
    (hn : m ≫ r' = r ≫ p) (ht : p ≫ e' = e ≫ b) (hs : b ≫ u = u ≫ a) :
    g ≫ (k ≫ m) ≫ (r' ≫ e' ≫ u) = (g ≫ k ≫ r ≫ e ≫ u) ≫ a := by
  simp only [Category.assoc]
  rw [← Category.assoc m r', hn]
  simp only [Category.assoc]
  rw [← Category.assoc p e', ht]
  simp only [Category.assoc]
  rw [hs]

lemma tensor_multiply_framed (L M : X.Modules) (s : O X ⟶ L) (U : X.Opens)
    (e : L.restrict U.ι ≅ O U.toScheme)
    (f : M.restrict U.ι ≅ O U.toScheme) :
    f.inv ≫ (Scheme.Modules.restrictFunctor U.ι).map (sectionMultiplyLeft L M s) ≫
      (tensorFrame L M U e f).hom = (tensorUnitTwist M U f).hom ≫
        (restrictSection U.ι s ≫ e.hom) := by
  let F := Scheme.Modules.restrictFunctor U.ι
  let R := moduleTensorRestrict U (O X) M
  let R' := moduleTensorRestrict U L M
  let E := moduleTensorIso (Scheme.Modules.restrictUnitIso U.ι) f
  let E' := moduleTensorIso e f
  let T := moduleTensorUnit (O U.toScheme)
  let a : O U.toScheme ⟶ O U.toScheme := restrictSection U.ι s ≫ e.hom
  let p := moduleTensorMap (F.map s) (𝟙 (M.restrict U.ι))
  have hn : F.map (moduleTensorMap s (𝟙 M)) ≫ R'.hom = R.hom ≫ p :=
    (moduleTensorRestrict_natural U s (𝟙 M)).trans
      (congrArg (fun q => R.hom ≫ moduleTensorMap (F.map s) q) (F.map_id M))
  have he : F.map s ≫ e.hom = (Scheme.Modules.restrictUnitIso U.ι).hom ≫ a := by
    simpa only [a, restrictSection] using!
      frame_section (Scheme.Modules.restrictUnitIso U.ι) (F.map s) e
  have h₁ := (moduleTensorMap_comp (F.map s) e.hom (𝟙 (M.restrict U.ι)) f.hom).symm.trans
    (congrArg (moduleTensorMap (F.map s ≫ e.hom)) (Category.id_comp f.hom))
  have h₂ := (moduleTensorMap_comp (Scheme.Modules.restrictUnitIso U.ι).hom a
      f.hom (𝟙 (O U.toScheme))).symm.trans
    (congrArg (moduleTensorMap ((Scheme.Modules.restrictUnitIso U.ι).hom ≫ a))
      (Category.comp_id f.hom))
  have ht : p ≫ E'.hom = E.hom ≫ moduleTensorMap a (𝟙 (O U.toScheme)) :=
    h₁.trans ((congrArg (fun q : F.obj (O X) ⟶ O U.toScheme => moduleTensorMap q f.hom)
      he).trans h₂.symm)
  have hs : moduleTensorMap a (𝟙 (O U.toScheme)) ≫ T.hom = T.hom ≫ a :=
    (moduleTensorUnit_scalar (X := U.toScheme) a (𝟙 (O U.toScheme))).trans
      (congrArg (fun q => T.hom ≫ q) (Category.comp_id a))
  have hfinal := framed_multiply f.inv (F.map (moduleTensorUnit M).inv)
    (F.map (moduleTensorMap s (𝟙 M))) R.hom R'.hom E.hom E'.hom T.hom a p _ hn ht hs
  simpa only [sectionMultiplyLeft, tensorFrame, tensorUnitTwist] using!
    (congrArg (fun q => f.inv ≫ q ≫ (tensorFrame L M U e f).hom)
      (F.map_comp (moduleTensorUnit M).inv (moduleTensorMap s (𝟙 M)))).trans hfinal

lemma tensor_multiply_ideal (L M : X.Modules) (s : O X ⟶ L)
    (U : X.affineOpens) (e : L.restrict U.1.ι ≅ O U.1.toScheme)
    (f : M.restrict U.1.ι ≅ O U.1.toScheme) :
    Ideal.span {U.1.topIso.hom (endValue (f.inv ≫
      (Scheme.Modules.restrictFunctor U.1.ι).map (sectionMultiplyLeft L M s) ≫
        (tensorFrame L M U.1 e f).hom))} =
    Ideal.span {U.1.topIso.hom (coefficient e (restrictSection U.1.ι s))} := by
  rw [tensor_multiply_framed,endValue_comp,map_mul,← Ideal.span_singleton_mul_span_singleton]
  have hu : IsUnit (endValue (tensorUnitTwist M U.1 f).hom) :=
    (end_isIso_iff _).mp inferInstance
  rw [Ideal.span_singleton_eq_top.mpr (hu.map U.1.topIso.hom.hom),Ideal.top_mul]
  rfl

theorem cartierPowerMultiply_ideal (L : LineBundle X) (s : GlobalSections X L.sheaf)
    (n : ℕ) (U : X.affineOpens)
    (e : L.sheaf.restrict U.1.ι ≅ structureSheaf U.1.toScheme) :
    Ideal.span {U.1.topIso.hom (endValue ((modulePowFrame U.1 e n).inv ≫
      (Scheme.Modules.restrictFunctor U.1.ι).map
        (PiExponent.NumericalAmpleness.cartierPowerMultiply L s n) ≫
      (modulePowFrame U.1 e (n+1)).hom))} =
    Ideal.span {U.1.topIso.hom (coefficient e (restrictSection U.1.ι s))} :=
  tensor_multiply_ideal L.sheaf (modulePow X L.sheaf n) s U e (modulePowFrame U.1 e n)
end
end PiExponent.CartierPowerFrames

end OAI
end Source0061

section Source0062
/-
Modification notice for the LogTwo project.
Derived from openai/math (Apache-2.0), revision adc7f1241b42e322a6451854ab7e4b4c146bf78a.
Original source: lean/OAI/NumberTheory/PiExponent/Approximation/GlueGlobalGenerators.lean
Changes: Convert module/import declarations to the Lean 4.34 public module format.
See ../../../../../THIRD_PARTY_NOTICES.txt for provenance and the recorded changes.
-/




namespace OAI

namespace PiExponent.GlueGlobalGenerators
noncomputable section
universe u
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace
open PiExponentSeshadri.Geometry PiExponentSeshadri.Frames

variable {X : Scheme.{u}} (M : X.Modules) {ι : Type u}
  (U : ι → X.Opens) (hcover : (⨆ i, U i) = ⊤)
  (σ : ∀ i, (M.restrict (U i).ι).GeneratingSections)
  (t : ∀ i, (σ i).I → GlobalSections X M)
  (ht : ∀ i j, restrictSection (U i).ι (t i j) =
    (M.restrict (U i).ι).unitHomEquiv.symm ((σ i).s j))

include hcover ht

theorem globalEvaluation_epi : Epi
    (M.freeHomEquiv.symm (fun ij : Σ i, (σ i).I => M.unitHomEquiv (t ij.1 ij.2))) := by
  let q := M.freeHomEquiv.symm (fun ij : Σ i, (σ i).I => M.unitHomEquiv (t ij.1 ij.2))
  have hq (i : ι) (j : (σ i).I) : SheafOfModules.ιFree ⟨i,j⟩ ≫ q = t i j := by
    erw [← SheafOfModules.unitHomEquiv_symm_freeHomEquiv_apply]
    simp only [q, Equiv.apply_symm_apply]
    exact M.unitHomEquiv.symm_apply_apply (t i j)
  change Epi (C := X.Modules) q
  apply (Preadditive.epi_iff_cancel_zero (C := X.Modules) q).mpr
  intro N g hg
  have hz (i : ι) (j : (σ i).I) : t i j ≫ g = 0 := by
    erw [← hq i j, Category.assoc, hg, comp_zero]
  apply CoherentTwist.eq_zero_of_local
  intro x
  have hx : x ∈ ⨆ i, U i := by rw [hcover]; trivial
  obtain ⟨i, hxi⟩ := Opens.mem_iSup.mp hx
  refine ⟨U i,hxi,?_⟩
  apply (@cancel_epi _ _ _ _ _ (σ i).π (σ i).epi _ _).mp
  erw [comp_zero]
  apply (SheafOfModules.isColimitFreeCofan (σ i).I).hom_ext
  intro j
  change SheafOfModules.ιFree j.as ≫ ((σ i).π ≫
    (Scheme.Modules.restrictFunctor (U i).ι).map g) = SheafOfModules.ιFree j.as ≫ 0
  erw [comp_zero, ← Category.assoc,
    ← SheafOfModules.unitHomEquiv_symm_freeHomEquiv_apply]
  simp only [SheafOfModules.GeneratingSections.π, Equiv.apply_symm_apply]
  erw [← ht i j.as]
  let R : X.Modules ⥤ (U i).toScheme.Modules := Scheme.Modules.restrictFunctor (U i).ι
  let e : R.obj (O X) ≅ O (U i).toScheme := Scheme.Modules.restrictUnitIso (U i).ι
  change (e.inv ≫ R.map (t i j.as)) ≫ R.map g = 0
  erw [Category.assoc, ← Functor.map_comp, hz, Functor.map_zero, comp_zero]

def globalGenerators : M.GeneratingSections where
  I := Σ i, (σ i).I
  s ij := M.unitHomEquiv (t ij.1 ij.2)
  epi := globalEvaluation_epi M U hcover σ t ht

instance [Finite ι] [hσ : ∀ i, (σ i).IsFiniteType] :
    (globalGenerators M U hcover σ t ht).IsFiniteType where
  finite := by
    let (i : ι) : Finite (σ i).I := (hσ i).finite
    exact inferInstanceAs (Finite (Σ i, (σ i).I))

theorem exists_finite_global_generators [Finite ι] [∀ i, (σ i).IsFiniteType] :
    ∃ q : M.GeneratingSections, q.IsFiniteType :=
  ⟨globalGenerators M U hcover σ t ht, inferInstance⟩

end
end PiExponent.GlueGlobalGenerators

end OAI
end Source0062

section Source0063
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
end Source0063

section Source0064
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
end Source0064

section Source0065
/-
Modification notice for the LogTwo project.
Derived from openai/math (Apache-2.0), revision adc7f1241b42e322a6451854ab7e4b4c146bf78a.
Original source: lean/OAI/NumberTheory/PiExponent/Geometry/SheafSectionGluing.lean
Changes: Convert module/import declarations to the Lean 4.34 public module format.
See ../../../../../THIRD_PARTY_NOTICES.txt for provenance and the recorded changes.
-/




namespace OAI

namespace PiExponent.SheafSectionGluing
noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open PiExponent.GlobalSectionClearing
universe u
variable {X : Scheme.{u}} {P Q : X.Modules}

def mapSection (f : P ⟶ Q) (U : X.Opens) :
    OpenSections P U →ₗ[Γ(X,⊤)] OpenSections Q U where
  toFun := f.app U
  map_add' := map_add _
  map_smul' r x := by
    exact f.app_smul (r := restrictScalar X U r) (x := x)

lemma mapSection_naturality (f : P ⟶ Q) {U V : X.Opens} (h : U ≤ V)
    (x : OpenSections P V) :
    mapSection f U (openRestriction P h x) = openRestriction Q h (mapSection f V x) :=
  CategoryTheory.congr_fun (f.mapPresheaf.naturality (homOfLE h).op) x

@[simp] lemma mapSection_comp {R : X.Modules} (f : P ⟶ Q) (g : Q ⟶ R)
    (U : X.Opens) (x : OpenSections P U) :
    mapSection (f ≫ g) U x = mapSection g U (mapSection f U x) := rfl

lemma mapSection_congr (f : P ⟶ Q) {U V : X.Opens} (h : U = V)
    (x : OpenSections P U) :
    openSectionsCongr Q h (mapSection f U x) = mapSection f V (openSectionsCongr P h x) := by
  subst V
  rfl

theorem glue_after_map (f : P ⟶ Q) {ι : Type*} (U : ι → X.Opens)
    (hcover : (⨆ i, U i) = ⊤) (y : ∀ i, OpenSections P (U i))
    (hy : ∀ i j,
      mapSection f (U i ⊓ U j) (openRestriction P inf_le_left (y i)) =
        mapSection f (U i ⊓ U j) (openRestriction P inf_le_right (y j))) :
    ∃ z : OpenSections Q ⊤,
      ∀ i, openRestriction Q (show U i ≤ ⊤ from le_top) z = mapSection f (U i) (y i) := by
  have h := TopCat.Sheaf.existsUnique_gluing' ⟨_, Q.isSheaf⟩ U ⊤
    (fun i => homOfLE (show U i ≤ ⊤ from le_top)) (by rw [hcover])
    (fun i => mapSection f (U i) (y i)) ?_
  · obtain ⟨z, hz, _⟩ := h
    exact ⟨z, hz⟩
  · intro i j
    change openRestriction Q (show U i ⊓ U j ≤ U i from inf_le_left) (mapSection f (U i) (y i)) =
      openRestriction Q (show U i ⊓ U j ≤ U j from inf_le_right) (mapSection f (U j) (y j))
    rw [← mapSection_naturality, ← mapSection_naturality]
    exact hy i j

theorem restriction_of_glued_map (f : P ⟶ Q) {ι : Type*} (U : ι → X.Opens)
    (hcover : (⨆ i, U i) = ⊤) (D : X.Opens) (x : OpenSections P D)
    (y : ∀ i, OpenSections P (U i))
    (hy : ∀ i, openRestriction P (show U i ⊓ D ≤ U i from inf_le_left) (y i) =
      openRestriction P inf_le_right x)
    (z : OpenSections Q ⊤)
    (hz : ∀ i, openRestriction Q (show U i ≤ ⊤ from le_top) z = mapSection f (U i) (y i)) :
    openRestriction Q (show D ≤ ⊤ from le_top) z = mapSection f D x := by
  apply TopCat.Sheaf.eq_of_locally_eq' ⟨_, Q.isSheaf⟩ (fun i => U i ⊓ D) D
    (fun i => homOfLE inf_le_right) (by rw [← iSup_inf_eq, hcover, top_inf_eq])
  intro i
  change openRestriction Q inf_le_right (openRestriction Q (show D ≤ ⊤ from le_top) z) =
    openRestriction Q inf_le_right (mapSection f D x)
  rw [openRestriction_comp_apply,
    ← openRestriction_comp_apply Q (show U i ⊓ D ≤ U i from inf_le_left) le_top z,
    hz i, ← mapSection_naturality, hy i, mapSection_naturality]

theorem overlap_difference_zero {ι : Type*} (U : ι → X.Opens) (D : X.Opens)
    (x : OpenSections P D) (y : ∀ i, OpenSections P (U i))
    (hy : ∀ i, openRestriction P (show U i ⊓ D ≤ U i from inf_le_left) (y i) =
      openRestriction P inf_le_right x) (i j : ι) :
    openRestriction P (show (U i ⊓ U j) ⊓ D ≤ U i ⊓ U j from inf_le_left)
      (openRestriction P inf_le_left (y i) - openRestriction P inf_le_right (y j)) = 0 := by
  rw [map_sub, openRestriction_comp_apply, openRestriction_comp_apply]
  have hi := congrArg (openRestriction P
    (show (U i ⊓ U j) ⊓ D ≤ U i ⊓ D from inf_le_inf inf_le_left le_rfl)) (hy i)
  have hj := congrArg (openRestriction P
    (show (U i ⊓ U j) ⊓ D ≤ U j ⊓ D from inf_le_inf inf_le_right le_rfl)) (hy j)
  simp only [openRestriction_comp_apply] at hi hj
  rw [hi, hj, sub_self]

end
end PiExponent.SheafSectionGluing

end OAI
end Source0065

section Source0066
/-
Modification notice for the LogTwo project.
Derived from openai/math (Apache-2.0), revision adc7f1241b42e322a6451854ab7e4b4c146bf78a.
Original source: lean/OAI/NumberTheory/PiExponent/LocalAlgebra/TwistLocalExtension.lean
Changes: Convert module/import declarations to the Lean 4.34 public module format.
See ../../../../../THIRD_PARTY_NOTICES.txt for provenance and the recorded changes.
-/




namespace OAI

namespace PiExponentSeshadri.Geometry
noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open PiExponentSeshadri.Frames PiExponent.GlobalSectionClearing
variable {X : Scheme}

theorem local_twist_extension (L : LineBundle X)
    (s : structureSheaf X ⟶ L.sheaf) (U : X.Opens) [NoetherianSpace U.toScheme]
    (e : L.sheaf.restrict U.ι ≅ structureSheaf U.toScheme)
    (M : X.Modules) [M.IsQuasicoherent]
    (x : Γ(M.restrict U.ι, U.toScheme.basicOpen (coefficient e (restrictSection U.ι s)))) :
    let a := coefficient e (restrictSection U.ι s)
    let D := U.toScheme.basicOpen a
    ∃ N : ℕ, ∀ n ≥ N, ∃ y : Γ(((moduleTwistFunctor L n).obj M).restrict U.ι,⊤),
      (((moduleTwistFunctor L n).obj M).restrict U.ι).presheaf.map
        (homOfLE (U.toScheme.basicOpen_le a)).op y =
      ((moduleTwistRestrictFrame L U e n).app M).inv.app D
        ((restrictScalar U.toScheme D a)^n • x) := by
  dsimp only
  obtain ⟨N, hN⟩ := global_section_extends_native (M.restrict U.ι)
    (coefficient e (restrictSection U.ι s)) x
  refine ⟨N, fun n hn => ?_⟩
  obtain ⟨y, hy⟩ := hN n hn
  let E := (moduleTwistRestrictFrame L U e n).app M
  refine ⟨E.inv.app ⊤ y, ?_⟩
  have h := CategoryTheory.congr_fun (E.inv.mapPresheaf.naturality
    (homOfLE (U.toScheme.basicOpen_le (coefficient e (restrictSection U.ι s)))).op) y
  exact h.symm.trans (congrArg (E.inv.app _) hy)

theorem local_twist_extension_section (L : LineBundle X)
    (s : structureSheaf X ⟶ L.sheaf) (U : X.Opens) [NoetherianSpace U.toScheme]
    (e : L.sheaf.restrict U.ι ≅ structureSheaf U.toScheme)
    (M : X.Modules) [M.IsQuasicoherent]
    (x : Γ(M.restrict U.ι, U.toScheme.basicOpen (coefficient e (restrictSection U.ι s)))) :
    let a := coefficient e (restrictSection U.ι s)
    let D := U.toScheme.basicOpen a
    ∃ N : ℕ, ∀ n ≥ N, ∃ y : Γ(((moduleTwistFunctor L n).obj M).restrict U.ι,⊤),
      (((moduleTwistFunctor L n).obj M).restrict U.ι).presheaf.map
        (homOfLE (U.toScheme.basicOpen_le a)).op y =
      ((moduleTwistSection L s n).app M).app (U.ι ''ᵁ D) x := by
  dsimp only
  obtain ⟨N, hN⟩ := local_twist_extension L s U e M x
  refine ⟨N, fun n hn => ?_⟩
  obtain ⟨y, hy⟩ := hN n hn
  refine ⟨y, hy.trans ?_⟩
  let D := U.toScheme.basicOpen (coefficient e (restrictSection U.ι s))
  let E := (moduleTwistRestrictFrame L U e n).app M
  have h := moduleTwistSection_frame L s U e M D n x
  calc
    _ = E.inv.app D (E.hom.app D (((moduleTwistSection L s n).app M).app (U.ι ''ᵁ D) x)) :=
      congrArg (E.inv.app D) h.symm
    _ = _ := congrArg (fun q => q.app D
      (((moduleTwistSection L s n).app M).app (U.ι ''ᵁ D) x)) E.hom_inv_id

end
end PiExponentSeshadri.Geometry

end OAI
end Source0066

section Source0067
/-
Modification notice for the LogTwo project.
Derived from openai/math (Apache-2.0), revision adc7f1241b42e322a6451854ab7e4b4c146bf78a.
Original source: lean/OAI/NumberTheory/PiExponent/Approximation/TwistGlobalExtension.lean
Changes: Convert module/import declarations to the Lean 4.34 public module format.
See ../../../../../THIRD_PARTY_NOTICES.txt for provenance and the recorded changes.
-/




namespace OAI

namespace PiExponent.TwistGlobalExtension
noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open PiExponentSeshadri.Geometry PiExponentSeshadri.Frames
open PiExponent.GlobalSectionClearing PiExponent.SheafSectionGluing
variable {X : Scheme}

lemma section_open_image {L : X.Modules} (s : structureSheaf X ⟶ L)
    (U : X.Opens) (e : L.restrict U.ι ≅ structureSheaf U.toScheme) :
    U.ι ''ᵁ U.toScheme.basicOpen (coefficient e (restrictSection U.ι s)) =
      U ⊓ sectionOpen X s := by
  change U.ι ''ᵁ U.toScheme.basicOpen (coefficient e (restrictSection U.ι s)) =
    U ⊓ PiExponentSeshadri.SectionOpens.isoOpen s
  rw [← preimage_isoOpen s U.ι e, Scheme.Hom.image_preimage_eq_opensRange_inf,
    Scheme.Opens.opensRange_ι]
  rfl

theorem local_twist_extension_ambient (L : LineBundle X)
    (s : structureSheaf X ⟶ L.sheaf) (U : X.Opens) [NoetherianSpace U.toScheme]
    (e : L.sheaf.restrict U.ι ≅ structureSheaf U.toScheme)
    (M : X.Modules) [M.IsQuasicoherent] (x : OpenSections M (sectionOpen X s)) :
    ∃ N : ℕ, ∀ n ≥ N, ∃ y : OpenSections ((moduleTwistFunctor L n).obj M) U,
      openRestriction ((moduleTwistFunctor L n).obj M)
        (show U ⊓ sectionOpen X s ≤ U from inf_le_left) y =
      mapSection ((moduleTwistSection L s n).app M) (U ⊓ sectionOpen X s)
        (openRestriction M inf_le_right x) := by
  let V := U.toScheme.basicOpen (coefficient e (restrictSection U.ι s))
  let W := U.ι ''ᵁ V
  have hWU : W ≤ U := U.ι_image_le V
  have hW : W = U ⊓ sectionOpen X s := section_open_image s U e
  have hWD : W ≤ sectionOpen X s := hW.le.trans inf_le_right
  let x0 : Γ(M.restrict U.ι,V) := M.presheaf.map (homOfLE hWD).op x
  obtain ⟨N, hN⟩ := local_twist_extension_section L s U e M x0
  refine ⟨N, fun n hn => ?_⟩
  obtain ⟨z, hz⟩ := hN n hn
  let P := (moduleTwistFunctor L n).obj M
  let z0 : OpenSections P (U.ι ''ᵁ ⊤) := z
  let y : OpenSections P U := openSectionsCongr P U.ι_image_top z0
  refine ⟨y, ?_⟩
  have ht := openSectionsCongr_naturality P (rfl : W = W) U.ι_image_top
    (U.ι.image_mono (show V ≤ ⊤ from le_top)) hWU z0
  have hres : openRestriction P hWU y =
      mapSection ((moduleTwistSection L s n).app M) W (openRestriction M hWD x) := by
    exact ht.symm.trans hz
  have hh := congrArg (openSectionsCongr P hW) hres
  rw [openSectionsCongr_naturality P hW rfl hWU inf_le_left, mapSection_congr] at hh
  change openRestriction P (show U ⊓ sectionOpen X s ≤ U from inf_le_left) y =
    mapSection ((moduleTwistSection L s n).app M) (U ⊓ sectionOpen X s)
      (openSectionsCongr M hW (openRestriction M hWD x)) at hh
  rw [openSectionsCongr_naturality M hW rfl hWD inf_le_right] at hh
  exact hh

theorem finite_local_twist_extensions [NoetherianSpace X] (L : LineBundle X)
    (s : structureSheaf X ⟶ L.sheaf) (M : X.Modules) [M.IsQuasicoherent]
    {ι : Type*} [Fintype ι] (U : ι → X.Opens)
    (e : ∀ i, L.sheaf.restrict (U i).ι ≅ structureSheaf (U i).toScheme)
    (x : OpenSections M (sectionOpen X s)) :
    ∃ N : ℕ, ∃ y : ∀ i, OpenSections ((moduleTwistFunctor L N).obj M) (U i),
      ∀ i, openRestriction ((moduleTwistFunctor L N).obj M)
        (show U i ⊓ sectionOpen X s ≤ U i from inf_le_left) (y i) =
      mapSection ((moduleTwistSection L s N).app M) (U i ⊓ sectionOpen X s)
        (openRestriction M inf_le_right x) := by
  classical
  have H (i : ι) := by
    letI : NoetherianSpace (U i).toScheme := NoetherianSpace.set (U i : Set X)
    exact local_twist_extension_ambient L s (U i) (e i) M x
  choose N hN using H
  let m := Finset.univ.sup N
  choose y hy using fun i => hN i m (Finset.le_sup (f := N) (Finset.mem_univ i))
  exact ⟨m, y, hy⟩

lemma mapSection_twistSection_add (L : LineBundle X) (s : structureSheaf X ⟶ L.sheaf)
    (M : X.Modules) (D : X.Opens) (x : OpenSections M D) (n k : ℕ) :
    mapSection ((moduleTwistForward L s n k).app M) D
      (mapSection ((moduleTwistSection L s n).app M) D x) =
    mapSection ((moduleTwistSection L s (n+k)).app M) D x := by
  exact congrArg (fun t => mapSection (t.app M) D x) (moduleTwistSection_add L s n k).symm

theorem finite_cover_twist_gluing [NoetherianSpace X] (L : LineBundle X)
    (s : structureSheaf X ⟶ L.sheaf) (M : X.Modules) [M.IsQuasicoherent]
    {ι : Type*} [Fintype ι] (U : ι → X.Opens) (hcover : (⨆ i, U i) = ⊤)
    (x : OpenSections M (sectionOpen X s)) (N : ℕ)
    (y : ∀ i, OpenSections ((moduleTwistFunctor L N).obj M) (U i))
    (hy : ∀ i, openRestriction ((moduleTwistFunctor L N).obj M)
        (show U i ⊓ sectionOpen X s ≤ U i from inf_le_left) (y i) =
      mapSection ((moduleTwistSection L s N).app M) (U i ⊓ sectionOpen X s)
        (openRestriction M inf_le_right x)) :
    ∃ K : ℕ, ∃ z : OpenSections ((moduleTwistFunctor L (N+K)).obj M) ⊤,
      openRestriction ((moduleTwistFunctor L (N+K)).obj M)
        (show sectionOpen X s ≤ ⊤ from le_top) z =
      mapSection ((moduleTwistSection L s (N+K)).app M) (sectionOpen X s) x := by
  classical
  let P := (moduleTwistFunctor L N).obj M
  let a := mapSection ((moduleTwistSection L s N).app M) (sectionOpen X s) x
  have hya (i : ι) : openRestriction P (show U i ⊓ sectionOpen X s ≤ U i from inf_le_left) (y i) =
      openRestriction P inf_le_right a :=
    (hy i).trans (mapSection_naturality ((moduleTwistSection L s N).app M) inf_le_right x)
  let diff (ij : ι × ι) := openRestriction P (show U ij.1 ⊓ U ij.2 ≤ U ij.1 from inf_le_left) (y ij.1) -
    openRestriction P (show U ij.1 ⊓ U ij.2 ≤ U ij.2 from inf_le_right) (y ij.2)
  have H (ij : ι × ι) :=
    PiExponent.TwistSectionClearing.twistForward_section_zero L s M N (U ij.1 ⊓ U ij.2)
      (diff ij) (overlap_difference_zero U (sectionOpen X s) a y hya ij.1 ij.2)
  choose K hK using H
  let k := Finset.univ.sup K
  have hcompat (i j : ι) :
      mapSection ((moduleTwistForward L s N k).app M) (U i ⊓ U j)
        (openRestriction P inf_le_left (y i)) =
      mapSection ((moduleTwistForward L s N k).app M) (U i ⊓ U j)
        (openRestriction P inf_le_right (y j)) := by
    have h := hK (i,j) k (Finset.le_sup (f := K) (Finset.mem_univ (i,j)))
    change mapSection ((moduleTwistForward L s N k).app M) (U i ⊓ U j)
      (openRestriction P inf_le_left (y i) - openRestriction P inf_le_right (y j)) = 0 at h
    rwa [map_sub, sub_eq_zero] at h
  obtain ⟨z, hz⟩ := glue_after_map ((moduleTwistForward L s N k).app M) U hcover y hcompat
  refine ⟨k, z, ?_⟩
  exact (restriction_of_glued_map ((moduleTwistForward L s N k).app M) U hcover
    (sectionOpen X s) a y hya z hz).trans (mapSection_twistSection_add L s M _ x N k)

theorem exists_global_twist_extension [NoetherianSpace X] (L : LineBundle X)
    (s : structureSheaf X ⟶ L.sheaf) (M : X.Modules) [M.IsQuasicoherent]
    (x : OpenSections M (sectionOpen X s)) :
    ∃ N : ℕ, ∃ z : OpenSections ((moduleTwistFunctor L N).obj M) ⊤,
      openRestriction ((moduleTwistFunctor L N).obj M)
        (show sectionOpen X s ≤ ⊤ from le_top) z =
      mapSection ((moduleTwistSection L s N).app M) (sectionOpen X s) x := by
  classical
  choose U hUx he using L.locallyRankOne
  obtain ⟨I, hI⟩ := isCompact_univ.elim_finite_subcover
    (fun x => (U x : Set X)) (fun x => (U x).isOpen)
    (by intro x _; exact Set.mem_iUnion.mpr ⟨x, hUx x⟩)
  have hcover : (⨆ i : I, U i.val) = ⊤ := by
    apply le_antisymm le_top
    intro x hx
    obtain ⟨i, hi⟩ := Set.mem_iUnion.mp (hI hx)
    obtain ⟨hi, hxU⟩ := Set.mem_iUnion.mp hi
    exact Opens.mem_iSup.mpr ⟨⟨i, hi⟩, hxU⟩
  let e (i : I) := Classical.choice (he i.val)
  obtain ⟨N, y, hy⟩ := finite_local_twist_extensions L s M (fun i : I => U i.val) e x
  obtain ⟨K, z, hz⟩ := finite_cover_twist_gluing L s M (fun i : I => U i.val) hcover x N y hy
  exact ⟨N+K, z, hz⟩

theorem global_twist_extension [NoetherianSpace X] (L : LineBundle X)
    (s : structureSheaf X ⟶ L.sheaf) (M : X.Modules) [M.IsQuasicoherent]
    (x : OpenSections M (sectionOpen X s)) :
    ∃ N : ℕ, ∀ n ≥ N, ∃ z : OpenSections ((moduleTwistFunctor L n).obj M) ⊤,
      openRestriction ((moduleTwistFunctor L n).obj M)
        (show sectionOpen X s ≤ ⊤ from le_top) z =
      mapSection ((moduleTwistSection L s n).app M) (sectionOpen X s) x := by
  obtain ⟨N, z, hz⟩ := exists_global_twist_extension L s M x
  refine ⟨N, fun n hn => ?_⟩
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hn
  refine ⟨mapSection ((moduleTwistForward L s N k).app M) ⊤ z, ?_⟩
  rw [← mapSection_naturality, hz]
  exact mapSection_twistSection_add L s M _ x N k

theorem global_twist_extension_native [NoetherianSpace X] (L : LineBundle X)
    (s : structureSheaf X ⟶ L.sheaf) (M : X.Modules) [M.IsQuasicoherent]
    (x : Γ(M,sectionOpen X s)) :
    ∃ N : ℕ, ∀ n ≥ N, ∃ z : Γ((moduleTwistFunctor L n).obj M,⊤),
      ((moduleTwistFunctor L n).obj M).presheaf.map
        (homOfLE (show sectionOpen X s ≤ ⊤ from le_top)).op z =
      ((moduleTwistSection L s n).app M).app (sectionOpen X s) x :=
  global_twist_extension L s M x

end
end PiExponent.TwistGlobalExtension

end OAI
end Source0067

section Source0068
/-
Modification notice for the LogTwo project.
Derived from openai/math (Apache-2.0), revision adc7f1241b42e322a6451854ab7e4b4c146bf78a.
Original source: lean/OAI/NumberTheory/PiExponent/Ampleness/AmpleGlobalGeneration.lean
Changes: Convert module/import declarations to the Lean 4.34 public module format.
See ../../../../../THIRD_PARTY_NOTICES.txt for provenance and the recorded changes.
-/




namespace OAI

namespace PiExponent.AmpleGlobalGeneration
noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite
open PiExponentSeshadri.Geometry PiExponentSeshadri.Frames
open PiExponent.CoherentAffineFinite
variable {X : Scheme.{0}}

theorem sectionMultiply_isIso_restrict (M : X.Modules) {L : X.Modules}
    (s : structureSheaf X ⟶ L) (U : X.Opens)
    [IsIso ((Scheme.Modules.restrictFunctor U.ι).map s)] :
    IsIso ((Scheme.Modules.restrictFunctor U.ι).map (moduleSectionMultiplyRight M s)) := by
  let R := Scheme.Modules.restrictFunctor U.ι
  have h : IsIso (R.map (moduleTensorMap (𝟙 M) s)) := by
    apply (isIso_comp_right_iff _ (moduleTensorRestrict U M L).hom).mp
    rw [moduleTensorRestrict_natural]
    infer_instance
  change IsIso (R.map ((moduleTensorRightUnit M).inv ≫ moduleTensorMap (𝟙 M) s))
  rw [Functor.map_comp]
  infer_instance

theorem twistSection_isIso_restrict (L : LineBundle X)
    (s : structureSheaf X ⟶ L.sheaf) (M : X.Modules) (n : ℕ) :
    IsIso ((Scheme.Modules.restrictFunctor (sectionOpen X s).ι).map
      ((moduleTwistSection L s n).app M)) := by
  have : IsIso ((Scheme.Modules.restrictFunctor (sectionOpen X s).ι).map s) :=
    PiExponentSeshadri.SectionOpens.isIso_restrict_isoOpen s
  induction n with
  | zero => change IsIso ((Scheme.Modules.restrictFunctor (sectionOpen X s).ι).map (𝟙 M)); infer_instance
  | succ n ih =>
    change IsIso ((Scheme.Modules.restrictFunctor (sectionOpen X s).ι).map
      (((moduleTwistSection L s n).app M) ≫
        moduleSectionMultiplyRight ((moduleTwistFunctor L n).obj M) s))
    rw [Functor.map_comp]
    have := sectionMultiply_isIso_restrict ((moduleTwistFunctor L n).obj M) s (sectionOpen X s)
    infer_instance

lemma openSectionEquiv_restrict_from_top (M : X.Modules) (U : X.Opens)
    (z : Γ(M,⊤)) :
    openSectionEquiv M U (restrictSection U.ι ((moduleSectionEquiv M).symm z)) =
      M.presheaf.map (homOfLE (show U ≤ ⊤ from le_top)).op z := by
  rw [openSectionEquiv_restrict]
  have h := section_value_natural ((moduleSectionEquiv M).symm z)
    (homOfLE (show U ≤ ⊤ from le_top))
  rw [← moduleSectionEquiv_apply, Equiv.apply_symm_apply] at h
  exact h.symm

lemma openSectionEquiv_postcomp {M N : X.Modules} (f : M ⟶ N) (U : X.Opens)
    (a : structureSheaf U.toScheme ⟶ M.restrict U.ι) :
    openSectionEquiv N U (a ≫ (Scheme.Modules.restrictFunctor U.ι).map f) =
      f.app U (openSectionEquiv M U a) := by
  change N.presheaf.map (eqToHom U.ι_image_top.symm).op
    (f.app (U.ι ''ᵁ ⊤) (a.app ⊤ (1 : Γ(U.toScheme,⊤)))) =
    f.app U (M.presheaf.map (eqToHom U.ι_image_top.symm).op
      (a.app ⊤ (1 : Γ(U.toScheme,⊤))))
  exact (congr($(f.mapPresheaf.naturality (eqToHom U.ι_image_top.symm).op)
    (a.app ⊤ (1 : Γ(U.toScheme,⊤))))).symm

theorem affine_local_generators (M : X.Modules) [M.IsFinitePresentation]
    (U : X.Opens) (hU : IsAffineOpen U) :
    ∃ σ : (M.restrict U.ι).GeneratingSections, σ.IsFiniteType := by
  have : IsAffine U.toScheme := hU
  let : M.IsQuasicoherent :=
    (SheafOfModules.IsFinitePresentation.exists_quasicoherentData M).choose.isQuasicoherent
  have := affine_sections_finite_of_localGenerators (M.restrict U.ι)
    ((locallyFinitelyGenerated_of_finitePresentation M).restrict U.ι)
  exact affine_exists_finite_generators (M.restrict U.ι)

theorem eventual_global_generators_of_section_cover [NoetherianSpace X]
    (L : LineBundle X) (M : X.Modules) [M.IsFinitePresentation]
    {ι : Type} [Finite ι] (s : ι → (structureSheaf X ⟶ L.sheaf))
    (hcover : (⨆ i, sectionOpen X (s i)) = ⊤)
    (haffine : ∀ i, IsAffineOpen (sectionOpen X (s i))) :
    ∃ N : ℕ, ∀ n ≥ N,
      ∃ G : ((moduleTwistFunctor L n).obj M).GeneratingSections, G.IsFiniteType := by
  classical
  let : M.IsQuasicoherent :=
    (SheafOfModules.IsFinitePresentation.exists_quasicoherentData M).choose.isQuasicoherent
  let U (i : ι) := sectionOpen X (s i)
  choose σ hσ using fun i => affine_local_generators M (U i) (haffine i)
  let (i : ι) : (σ i).IsFiniteType := hσ i
  let (i : ι) : Finite (σ i).I := (hσ i).finite
  let a (i : ι) (j : (σ i).I) :=
    (M.restrict (U i).ι).unitHomEquiv.symm ((σ i).s j)
  let x (i : ι) (j : (σ i).I) : Γ(M,U i) := openSectionEquiv M (U i) (a i j)
  choose d hd using fun ij : Σ i, (σ i).I =>
    PiExponent.TwistGlobalExtension.global_twist_extension_native L (s ij.1) M (x ij.1 ij.2)
  let : Fintype (Σ i, (σ i).I) := Fintype.ofFinite _
  let N := Finset.univ.sup d
  refine ⟨N, fun n hn => ?_⟩
  let Q := (moduleTwistFunctor L n).obj M
  have hn' (ij : Σ i, (σ i).I) : d ij ≤ n :=
    (Finset.le_sup (f := d) (Finset.mem_univ ij)).trans hn
  choose z hz using fun ij : Σ i, (σ i).I => hd ij n (hn' ij)
  let f (i : ι) : M.restrict (U i).ι ⟶ Q.restrict (U i).ι :=
    (Scheme.Modules.restrictFunctor (U i).ι).map ((moduleTwistSection L (s i) n).app M)
  have hf (i : ι) : IsIso (f i) := twistSection_isIso_restrict L (s i) M n
  let τ (i : ι) : (Q.restrict (U i).ι).GeneratingSections :=
    SheafOfModules.GeneratingSections.equivOfIso
      (@asIso _ _ _ _ (f i) (hf i)) (σ i)
  let (i : ι) : (τ i).IsFiniteType := ⟨(hσ i).finite⟩
  let t (i : ι) (j : (τ i).I) : GlobalSections X Q :=
    (moduleSectionEquiv Q).symm (z ⟨i,j⟩)
  have ht (i : ι) (j : (τ i).I) : restrictSection (U i).ι (t i j) =
      (Q.restrict (U i).ι).unitHomEquiv.symm ((τ i).s j) := by
    apply (openSectionEquiv Q (U i)).injective
    change openSectionEquiv Q (U i)
      (restrictSection (U i).ι ((moduleSectionEquiv Q).symm (z ⟨i,j⟩))) =
      openSectionEquiv Q (U i) ((Q.restrict (U i).ι).unitHomEquiv.symm
        (SheafOfModules.sectionsMap (f i) ((σ i).s j)))
    erw [openSectionEquiv_restrict_from_top, ← SheafOfModules.unitHomEquiv_symm_comp]
    erw [openSectionEquiv_postcomp]
    exact hz ⟨i,j⟩
  exact PiExponent.GlueGlobalGenerators.exists_finite_global_generators Q U hcover τ t ht

theorem ample_power_eventual_global_generators [NoetherianSpace X]
    (L : LineBundle X) (hL : L.IsAmple) (M : X.Modules) [M.IsFinitePresentation] :
    ∃ d : ℕ, 0 < d ∧ ∃ N : ℕ, ∀ n ≥ N,
      ∃ G : ((moduleTwistFunctor (L.pow d) n).obj M).GeneratingSections, G.IsFiniteType := by
  obtain ⟨d, hd, l, s, hcover, haffine, _⟩ := L.ample_common_degree_cover hL
  exact ⟨d, hd, eventual_global_generators_of_section_cover (L.pow d) M s hcover haffine⟩

end
end PiExponent.AmpleGlobalGeneration

end OAI
end Source0068

section Source0069
/-
Modification notice for the LogTwo project.
Derived from openai/math (Apache-2.0), revision adc7f1241b42e322a6451854ab7e4b4c146bf78a.
Original source: lean/OAI/NumberTheory/PiExponent/Geometry/SheafificationUnitIso.lean
Changes: Convert module/import declarations to the Lean 4.34 public module format.
See ../../../../../THIRD_PARTY_NOTICES.txt for provenance and the recorded changes.
-/




namespace OAI

namespace PiExponentSeshadri.Geometry
noncomputable section
open AlgebraicGeometry CategoryTheory
variable {X : Scheme}

theorem sheafification_unit_isIso (M : X.Modules) :
    IsIso ((PiExponentSeshadri.TensorPure.adj X).unit.app M.val) := by
  exact (PiExponentSeshadri.TensorPure.adj X).isIso_unit_app_of_iso (Iso.refl M.val)

theorem sheafification_unit_isIso_of_iso (P : PresheafOfModules X.ringCatSheaf.obj)
    (M : X.Modules) (e : P ≅ M.val) :
    IsIso ((PiExponentSeshadri.TensorPure.adj X).unit.app P) :=
  (PiExponentSeshadri.TensorPure.adj X).isIso_unit_app_of_iso e

end
end PiExponentSeshadri.Geometry

end OAI
end Source0069

section Source0070
/-
Modification notice for the LogTwo project.
Derived from openai/math (Apache-2.0), revision adc7f1241b42e322a6451854ab7e4b4c146bf78a.
Original source: lean/OAI/NumberTheory/PiExponent/Approximation/ModuleLinePowerLaws.lean
Changes: Convert module/import declarations to the Lean 4.34 public module format.
See ../../../../../THIRD_PARTY_NOTICES.txt for provenance and the recorded changes.
-/




namespace OAI

namespace PiExponentSeshadri.Geometry
noncomputable section
open CategoryTheory AlgebraicGeometry TopologicalSpace MonoidalCategory
open PiExponentSeshadri.TensorPure
variable {X : Scheme}

def lineTensorPresheafRestrictFrame (L : LineBundle X) (N : X.Modules)
    (U : X.Opens) (e : L.sheaf.restrict U.ι ≅ structureSheaf U.toScheme) :
    (modulePresheafRestrict U.ι).obj
      (PresheafOfModulesOfCommRing.Monoidal.tensorObj (R := X.presheaf) L.sheaf.val N.val) ≅
        (N.restrict U.ι).val := by
  let : MonoidalCategory (PresheafOfModules U.toScheme.ringCatSheaf.obj) :=
    PresheafOfModulesOfCommRing.monoidalCategory (R := U.toScheme.presheaf)
  let ep : (modulePresheafRestrict U.ι).obj L.sheaf.val ≅
      𝟙_ (PresheafOfModules U.toScheme.ringCatSheaf.obj) :=
    (SheafOfModules.forget _).mapIso e
  exact modulePresheafTensorRestrict U L.sheaf.val N.val ≪≫
    tensorIso ep (Iso.refl _) ≪≫ λ_ _

lemma lineTensorPresheaf_unit_restrict_isIso (L : LineBundle X) (N : X.Modules)
    (U : X.Opens) (e : L.sheaf.restrict U.ι ≅ structureSheaf U.toScheme) :
    IsIso ((modulePresheafRestrict U.ι).map
      ((adj X).unit.app
        (PresheafOfModulesOfCommRing.Monoidal.tensorObj (R := X.presheaf) L.sheaf.val N.val))) := by
  let P := PresheafOfModulesOfCommRing.Monoidal.tensorObj (R := X.presheaf) L.sheaf.val N.val
  let R : PresheafOfModules X.ringCatSheaf.obj ⥤
      PresheafOfModules U.toScheme.ringCatSheaf.obj := modulePresheafRestrict U.ι
  have hη : IsIso ((adj U.toScheme).unit.app (R.obj P)) :=
    sheafification_unit_isIso_of_iso (R.obj P) (N.restrict U.ι)
      (lineTensorPresheafRestrictFrame L N U e)
  have hh : IsIso (R.map ((adj X).unit.app P) ≫
      ((moduleSheafificationRestrict U.ι).hom.app P).val) := by
    erw [sheafify_restrict_unit]
    exact hη
  let V : U.toScheme.Modules ⥤ PresheafOfModules U.toScheme.ringCatSheaf.obj :=
    SheafOfModules.forget U.toScheme.ringCatSheaf
  let hv : IsIso (C := PresheafOfModules U.toScheme.ringCatSheaf.obj)
      (((moduleSheafificationRestrict U.ι).hom.app P).val) :=
    (V.mapIso ((moduleSheafificationRestrict U.ι).app P)).isIso_hom
  exact (@isIso_comp_right_iff (PresheafOfModules U.toScheme.ringCatSheaf.obj)
    _ _ _ _ _ _ hv).mp hh

lemma sheafification_tensor_left_line_unit_isIso (M : X.Modules) (L : LineBundle X)
    (N : X.Modules) :
    IsIso ((PresheafOfModules.sheafification (𝟙 X.ringCatSheaf.obj)).map
      (PresheafOfModulesOfCommRing.Monoidal.tensorHom (R := X.presheaf) (𝟙 M.val)
        ((adj X).unit.app
          (PresheafOfModulesOfCommRing.Monoidal.tensorObj (R := X.presheaf) L.sheaf.val N.val)))) := by
  let P := PresheafOfModulesOfCommRing.Monoidal.tensorObj (R := X.presheaf) L.sheaf.val N.val
  let F : PresheafOfModules X.ringCatSheaf.obj ⥤ X.Modules :=
    PresheafOfModules.sheafification (𝟙 X.ringCatSheaf.obj)
  let η := (adj X).unit.app P
  let Q := (F ⋙ SheafOfModules.forget X.ringCatSheaf ⋙
    PresheafOfModules.restrictScalars (𝟙 X.ringCatSheaf.obj)).obj P
  let g := PresheafOfModulesOfCommRing.Monoidal.tensorHom (R := X.presheaf) (𝟙 M.val) η
  apply PiExponent.NumericalAmpleness.isIso_of_locally_isIso
  intro x
  obtain ⟨U,hx,⟨e⟩⟩ := L.locallyRankOne x
  refine ⟨U,hx,?_⟩
  let R : PresheafOfModules X.ringCatSheaf.obj ⥤
      PresheafOfModules U.toScheme.ringCatSheaf.obj := modulePresheafRestrict U.ι
  let S : PresheafOfModules U.toScheme.ringCatSheaf.obj ⥤ U.toScheme.Modules :=
    PresheafOfModules.sheafification (𝟙 U.toScheme.ringCatSheaf.obj)
  let : MonoidalCategory (PresheafOfModules U.toScheme.ringCatSheaf.obj) :=
    PresheafOfModulesOfCommRing.monoidalCategory (R := U.toScheme.presheaf)
  have : IsIso (R.map η) := lineTensorPresheaf_unit_restrict_isIso L N U e
  apply (NatIso.isIso_map_iff (moduleSheafificationRestrict U.ι) g).mpr
  change IsIso (S.map (R.map g))
  have heq := modulePresheafTensorRestrict_natural U (𝟙 M.val) η
  let : IsIso (S.map (modulePresheafTensorRestrict U M.val P).hom) :=
    (S.mapIso (modulePresheafTensorRestrict U M.val P)).isIso_hom
  let : IsIso (S.map (modulePresheafTensorRestrict U M.val Q).hom) :=
    (S.mapIso (modulePresheafTensorRestrict U M.val Q)).isIso_hom
  have hcomp : IsIso (S.map (R.map g ≫
      (modulePresheafTensorRestrict U M.val Q).hom)) := by
    erw [heq, S.map_comp]
    have ht : IsIso (S.map
      (PresheafOfModulesOfCommRing.Monoidal.tensorHom (R := U.toScheme.presheaf)
        (R.map (𝟙 M.val)) (R.map η))) := by
      rw [R.map_id]
      change IsIso (S.map ((𝟙 (R.obj M.val)) ⊗ₘ (R.map η)))
      infer_instance
    exact (inferInstance : IsIso (C := U.toScheme.Modules)
      (S.map (modulePresheafTensorRestrict U M.val P).hom ≫ S.map
        (PresheafOfModulesOfCommRing.Monoidal.tensorHom (R := U.toScheme.presheaf)
          (R.map (𝟙 M.val)) (R.map η))))
  erw [S.map_comp] at hcomp
  exact (isIso_comp_right_iff (C := U.toScheme.Modules) _ _).mp hcomp

def sheafificationTensorLeftLinePair (M : X.Modules) (L N : LineBundle X) :
    (PresheafOfModules.sheafification (𝟙 X.ringCatSheaf.obj)).obj
      (PresheafOfModulesOfCommRing.Monoidal.tensorObj (R := X.presheaf) M.val
        (PresheafOfModulesOfCommRing.Monoidal.tensorObj (R := X.presheaf) L.sheaf.val N.sheaf.val)) ≅
    moduleTensor X M (moduleTensor X L.sheaf N.sheaf) := by
  let P := PresheafOfModulesOfCommRing.Monoidal.tensorObj (R := X.presheaf) L.sheaf.val N.sheaf.val
  let F := PresheafOfModules.sheafification (𝟙 X.ringCatSheaf.obj)
  let η := (adj X).unit.app P
  let ht : IsIso (F.map (PresheafOfModulesOfCommRing.Monoidal.tensorHom
      (R := X.presheaf) (𝟙 M.val) η)) := sheafification_tensor_left_line_unit_isIso M L N.sheaf
  exact @asIso _ _ _ _ (F.map (PresheafOfModulesOfCommRing.Monoidal.tensorHom (R := X.presheaf)
    (𝟙 M.val) η)) ht

def moduleLineTensorAssoc (M : X.Modules) (L N : LineBundle X) :
    moduleTensor X (moduleTensor X M L.sheaf) N.sheaf ≅
      moduleTensor X M (moduleTensor X L.sheaf N.sheaf) := by
  let : MonoidalCategory (PresheafOfModules X.ringCatSheaf.obj) :=
    PresheafOfModulesOfCommRing.monoidalCategory (R := X.presheaf)
  exact (sheafificationTensorRight (M.val ⊗ L.sheaf.val) N).symm ≪≫
    (PresheafOfModules.sheafification (𝟙 X.ringCatSheaf.obj)).mapIso
      (α_ M.val L.sheaf.val N.sheaf.val) ≪≫
    sheafificationTensorLeftLinePair M L N

def moduleTwistPowerIso (L : LineBundle X) (M : X.Modules) : ∀ n : ℕ,
    (moduleTwistFunctor L n).obj M ≅ moduleTensor X M (modulePow X L.sheaf n)
  | 0 => (moduleTensorRightUnit M).symm
  | n+1 => moduleTensorIso (moduleTwistPowerIso L M n) (Iso.refl L.sheaf) ≪≫
      moduleLineTensorAssoc M (L.pow n) L ≪≫
      moduleTensorIso (Iso.refl M) (moduleTensorComm (modulePow X L.sheaf n) L.sheaf)

def moduleTwistPowerMulIso (L : LineBundle X) (M : X.Modules) (d n : ℕ) :
    (moduleTwistFunctor (L.pow d) n).obj M ≅ (moduleTwistFunctor L (d*n)).obj M :=
  moduleTwistPowerIso (L.pow d) M n ≪≫
    moduleTensorIso (Iso.refl M) (linePowerMul L d n) ≪≫
      (moduleTwistPowerIso L M (d*n)).symm

end
end PiExponentSeshadri.Geometry

end OAI
end Source0070

section Source0071
/-
Modification notice for the LogTwo project.
Derived from openai/math (Apache-2.0), revision adc7f1241b42e322a6451854ab7e4b4c146bf78a.
Original source: lean/OAI/NumberTheory/PiExponent/Geometry/CurveEffectiveTwist.lean
Changes: Convert module/import declarations to the Lean 4.34 public module format.
See ../../../../../THIRD_PARTY_NOTICES.txt for provenance and the recorded changes.
-/




namespace OAI

namespace PiExponent.CurveDegree
noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace
open PiExponentSeshadri.Geometry PiExponentSeshadri.Frames PiExponentSeshadri.SectionOpens
variable {X : Scheme.{0}} [IsIntegral X]

private theorem id_eq_zero_of_iso {C : Type*} [Category C] [Preadditive C]
    {A B : C} (e : A ≅ B) (h : 𝟙 A = 0) : 𝟙 B = 0 := by
  have he := congrArg (fun f : A ⟶ A => e.inv ≫ f ≫ e.hom) h
  simpa only [Category.id_comp, comp_zero, zero_comp, Iso.inv_hom_id] using he

private theorem generators_isZero {T : TopCat.{0}} (R : Sheaf (Opens.grothendieckTopology T) RingCat.{0})
    (M : SheafOfModules.{0} R) (G : M.GeneratingSections)
    (h : ∀ s : SheafOfModules.unit.{0} R ⟶ M, s = 0) : IsZero M := by
  have hπ : G.π = 0 := by
    apply M.freeHomEquiv.injective
    funext i
    apply M.unitHomEquiv.symm.injective
    rw [SheafOfModules.unitHomEquiv_symm_freeHomEquiv_apply,
      SheafOfModules.unitHomEquiv_symm_freeHomEquiv_apply]
    simpa only [comp_zero] using h (SheafOfModules.ιFree i ≫ G.π)
  let : Epi G.π := G.epi
  exact IsZero.of_epi_eq_zero G.π hπ

theorem lineBundle_not_isZero (L : LineBundle X) : ¬ IsZero L.sheaf := by
  intro h
  obtain ⟨x⟩ : Nonempty X := inferInstance
  obtain ⟨U, hx, ⟨e⟩⟩ := L.locallyRankOne x
  let : Nonempty U := ⟨⟨x, hx⟩⟩
  let : IsIntegral U.toScheme := isIntegral_of_isOpenImmersion U.ι
  have hL : (𝟙 L.sheaf) = 0 := h.eq_of_src _ _
  have hr := congrArg (Scheme.Modules.restrictFunctor U.ι).map hL
  rw [CategoryTheory.Functor.map_id, CategoryTheory.Functor.map_zero] at hr
  have hid : (𝟙 (O U.toScheme)) = 0 := by
    simpa only [O] using! id_eq_zero_of_iso e hr
  have hh := congrArg (endValue (X := U.toScheme)) hid
  simp only [endValue] at hh
  exact one_ne_zero (show (1 : Γ(U.toScheme, ⊤)) = 0 from hh)

omit [IsIntegral X] in

theorem section_ne_zero_of_mem_isoOpen (L : LineBundle X) (s : O X ⟶ L.sheaf)
    (x : X) (hx : x ∈ isoOpen s) : s ≠ 0 := by
  obtain ⟨U, hxU, ⟨e⟩⟩ := L.locallyRankOne x
  have hm : (⟨x, hxU⟩ : U.toScheme) ∈ U.ι ⁻¹ᵁ isoOpen s := hx
  rw [preimage_isoOpen s U.ι e] at hm
  intro hz
  subst s
  have hrestrict : restrictSection U.ι (0 : O X ⟶ L.sheaf) = 0 := by
    simpa only [restrictSection] using restrictSection_zero (M := L.sheaf) U.ι
  have hz := (congrArg (coefficient e) hrestrict).trans (coefficient_zero e)
  erw [hz, Scheme.basicOpen_zero] at hm
  exact hm

theorem nonzero_section_of_generators (L : LineBundle X) (G : L.sheaf.GeneratingSections) :
    ∃ s : GlobalSections X L.sheaf, s ≠ 0 := by
  classical
  by_contra h
  push Not at h
  exact lineBundle_not_isZero L (generators_isZero X.ringCatSheaf L.sheaf G h)

def twistLineIso (H L : LineBundle X) (n : ℕ) :
    (moduleTwistFunctor H n).obj L.sheaf ≅ ((H.pow n).tensor L).sheaf :=
  moduleTwistPowerIso H L.sheaf n ≪≫
    moduleTensorComm L.sheaf (modulePow X H.sheaf n)

theorem exists_effective_twist [NoetherianSpace X]
    (H : LineBundle X) (hH : H.IsAmple) (L : LineBundle X) :
    ∃ A : LineBundle X,
      (∃ t : GlobalSections X A.sheaf, t ≠ 0) ∧
      (∃ u : GlobalSections X (A.tensor L).sheaf, u ≠ 0) := by
  obtain ⟨d, hd, k, s, hcover, haffine, hcoverData⟩ := H.ample_common_degree_cover hH
  let := PiExponent.GeometrySupport.LineBundleCoherent.lineBundle_isFinitePresentation L
  obtain ⟨N, hN⟩ := AmpleGlobalGeneration.eventual_global_generators_of_section_cover
    (H.pow d) L.sheaf s hcover haffine
  obtain ⟨G, hG⟩ := hN N le_rfl
  let A := (H.pow d).pow N
  obtain ⟨x⟩ : Nonempty X := inferInstance
  have hx : x ∈ ⨆ i, sectionOpen X (s i) := by rw [hcover]; trivial
  obtain ⟨i, hi⟩ := Opens.mem_iSup.mp hx
  let t := powerSection (s i) N
  have ht : t ≠ 0 := section_ne_zero_of_mem_isoOpen A t x
    (sectionOpen_le_powerSection (s i) N hi)
  have hu := nonzero_section_of_generators (A.tensor L)
    (SheafOfModules.GeneratingSections.equivOfIso (twistLineIso (H.pow d) L N) G)
  exact ⟨A, ⟨t, ht⟩, hu⟩

end
end PiExponent.CurveDegree

end OAI
end Source0071

section Source0072
/-
Modification notice for the LogTwo project.
Derived from openai/math (Apache-2.0), revision adc7f1241b42e322a6451854ab7e4b4c146bf78a.
Original source: lean/OAI/NumberTheory/PiExponent/Approximation/InverseFrames.lean
Changes: Convert module/import declarations to the Lean 4.34 public module format.
See ../../../../../THIRD_PARTY_NOTICES.txt for provenance and the recorded changes.
-/




namespace OAI

namespace PiExponent.InverseFrames
noncomputable section
open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite
open PiExponentSeshadri.Geometry PiExponentSeshadri.Frames PiExponentSeshadri.TensorPure
variable {X : Scheme.{0}} {M N : X.Modules}

def regularValue {P : X.Modules} (f : P ⟶ O X) (U : X.Opens)
    (x : P.val.obj (op U)) : Γ(X,U) := f.app U x

def pairingFrame (E : moduleTensor X M N ≅ O X) (e : M ≅ O X) : N ≅ O X :=
  (moduleTensorUnit N).symm ≪≫ moduleTensorIso e.symm (Iso.refl N) ≪≫ E

lemma unit_inv_pure (N : X.Modules) (U : X.Opens) (x : N.val.obj (op U)) :
    (moduleTensorUnit N).inv.app U x = PiExponentSeshadri.TensorPure.pure (O X) N U (1 : Γ(X,U)) x := by
  have h : (moduleTensorUnit N).hom.app U (PiExponentSeshadri.TensorPure.pure (O X) N U (1 : Γ(X,U)) x) = x := by
    change (moduleTensorUnit N).hom.app U
      (PiExponentSeshadri.TensorPure.pure (structureSheaf X) N U (1 : Γ(X,U)) x) = x
    exact (unit_pure N U (1 : Γ(X,U)) x).trans (one_smul Γ(X,U) (show Γ(N,U) from x))
  calc
    (moduleTensorUnit N).inv.app U x =
        (moduleTensorUnit N).inv.app U
          ((moduleTensorUnit N).hom.app U (PiExponentSeshadri.TensorPure.pure (O X) N U (1 : Γ(X,U)) x)) :=
      congrArg (fun z => (moduleTensorUnit N).inv.app U z) h.symm
    _ = _ := congrArg (fun f => f.app U (PiExponentSeshadri.TensorPure.pure (O X) N U (1 : Γ(X,U)) x))
      (moduleTensorUnit N).hom_inv_id

lemma pairingFrame_apply (E : moduleTensor X M N ≅ O X) (e : M ≅ O X)
    (U : X.Opens) (x : N.val.obj (op U)) :
    (pairingFrame E e).hom.app U x =
      E.hom.app U (PiExponentSeshadri.TensorPure.pure M N U (e.inv.app U (1 : Γ(X,U))) x) := by
  change E.hom.app U ((moduleTensorMap e.inv (𝟙 N)).app U
    ((moduleTensorUnit N).inv.app U x)) = _
  rw [unit_inv_pure]
  exact congrArg (fun z => E.hom.app U z)
    (PiExponentSeshadri.TensorPure.map_pure e.inv (𝟙 N) U (1 : Γ(X,U)) x)

lemma frame_generator_change (e f : M ≅ O X) :
    f.inv.app ⊤ (1 : Γ(X,⊤)) = (frameChange f e : Γ(X,⊤)) • e.inv.app ⊤ (1 : Γ(X,⊤)) := by
  have h := e.inv.app_smul (r := (frameChange f e : Γ(X,⊤)))
    (x := (1 : Γ(X,⊤)))
  change e.inv.app ⊤ ((frameChange f e : Γ(X,⊤)) * (1 : Γ(X,⊤)) : Γ(X,⊤)) = _ at h
  rw [mul_one] at h
  rw [← h]
  change f.inv.app ⊤ (1 : Γ(X,⊤)) = e.inv.app ⊤ (e.hom.app ⊤ (f.inv.app ⊤ (1 : Γ(X,⊤))))
  exact (congrArg (fun t => t.app ⊤ (f.inv.app ⊤ (1 : Γ(X,⊤)))) e.hom_inv_id).symm

lemma pairingFrame_change_apply (E : moduleTensor X M N ≅ O X)
    (e f : M ≅ O X) (x : N.val.obj (op (⊤ : X.Opens))) :
    regularValue (pairingFrame E f).hom ⊤ x =
      (frameChange f e : Γ(X,⊤)) * regularValue (pairingFrame E e).hom ⊤ x := by
  dsimp only [regularValue]
  have hf := pairingFrame_apply E f ⊤ x
  have he := pairingFrame_apply E e ⊤ x
  have hg := congrArg (fun m => E.hom.app ⊤ (PiExponentSeshadri.TensorPure.pure M N ⊤ m x))
    (frame_generator_change e f)
  have hs := congrArg (fun z => E.hom.app ⊤ z)
    (pure_smul_left M N ⊤ (frameChange f e : Γ(X,⊤)) (e.inv.app ⊤ (1 : Γ(X,⊤))) x)
  have hm := E.hom.app_smul (r := (frameChange f e : Γ(X,⊤)))
    (x := PiExponentSeshadri.TensorPure.pure M N ⊤ (e.inv.app ⊤ (1 : Γ(X,⊤))) x)
  exact hf.trans (hg.trans (hs.trans (hm.trans
    (congrArg (fun a : Γ(X,⊤) => (frameChange f e : Γ(X,⊤)) * a) he.symm))))

lemma pairingFrame_frameChange (E : moduleTensor X M N ≅ O X)
    (e f : M ≅ O X) :
    frameChange (pairingFrame E e) (pairingFrame E f) = frameChange f e := by
  apply Units.ext
  change (pairingFrame E f).hom.app ⊤ ((pairingFrame E e).inv.app ⊤ (1 : Γ(X,⊤))) = _
  change regularValue (pairingFrame E f).hom ⊤ ((pairingFrame E e).inv.app ⊤ (1 : Γ(X,⊤))) = _
  erw [pairingFrame_change_apply]
  have h := congrArg (fun t => t.app ⊤ (1 : Γ(X,⊤))) (pairingFrame E e).inv_hom_id
  change (pairingFrame E e).hom.app ⊤ ((pairingFrame E e).inv.app ⊤ (1 : Γ(X,⊤))) = (1 : Γ(X,⊤)) at h
  have hv : regularValue (pairingFrame E e).hom ⊤
      ((pairingFrame E e).inv.app ⊤ (1 : Γ(X,⊤))) = 1 := h
  rw [hv, mul_one]

lemma pairing_apply (E : moduleTensor X M N ≅ O X) (e : M ≅ O X)
    (U : X.Opens) (m : M.val.obj (op U)) (n : N.val.obj (op U)) :
    regularValue E.hom U (PiExponentSeshadri.TensorPure.pure M N U m n) =
      regularValue e.hom U m * regularValue (pairingFrame E e).hom U n := by
  have hm : m = (regularValue e.hom U m) • e.inv.app U (1 : Γ(X,U)) := by
    have h := e.inv.app_smul (r := (regularValue e.hom U m))
      (x := (1 : Γ(X,U)))
    change e.inv.app U (regularValue e.hom U m * (1 : Γ(X,U)) : Γ(X,U)) = _ at h
    rw [mul_one] at h
    rw [← h]
    exact (congrArg (fun t => t.app U m) e.hom_inv_id).symm
  calc
    regularValue E.hom U (PiExponentSeshadri.TensorPure.pure M N U m n) =
        regularValue E.hom U (PiExponentSeshadri.TensorPure.pure M N U ((regularValue e.hom U m) • e.inv.app U (1 : Γ(X,U))) n) :=
      congrArg (fun z => regularValue E.hom U (PiExponentSeshadri.TensorPure.pure M N U z n)) hm
    _ = (regularValue e.hom U m) * regularValue E.hom U (PiExponentSeshadri.TensorPure.pure M N U (e.inv.app U (1 : Γ(X,U))) n) := by
      erw [pure_smul_left]
      exact E.hom.app_smul _ _
    _ = _ := by
      dsimp only [regularValue]
      rw [pairingFrame_apply]

lemma pairing_inverse_generator (E : moduleTensor X M N ≅ O X) (e : M ≅ O X)
    (U : X.Opens) (m : M.val.obj (op U)) :
    E.hom.app U (PiExponentSeshadri.TensorPure.pure M N U m ((pairingFrame E e).inv.app U (1 : Γ(X,U)))) = e.hom.app U m := by
  change regularValue E.hom U _ = regularValue e.hom U m
  erw [pairing_apply]
  have h := congrArg (fun t => t.app U (1 : Γ(X,U))) (pairingFrame E e).inv_hom_id
  change (pairingFrame E e).hom.app U ((pairingFrame E e).inv.app U (1 : Γ(X,U))) = (1 : Γ(X,U)) at h
  have hv : regularValue (pairingFrame E e).hom U
      ((pairingFrame E e).inv.app U (1 : Γ(X,U))) = 1 := h
  rw [hv, mul_one]

def dualMap (E : moduleTensor X M N ≅ O X) (s : O X ⟶ M) : N ⟶ O X :=
  (moduleTensorUnit N).inv ≫ moduleTensorMap s (𝟙 N) ≫ E.hom

lemma dualMap_apply (E : moduleTensor X M N ≅ O X) (s : O X ⟶ M)
    (U : X.Opens) (n : N.val.obj (op U)) :
    (dualMap E s).app U n = E.hom.app U (PiExponentSeshadri.TensorPure.pure M N U (s.app U (1 : Γ(X,U))) n) := by
  change E.hom.app U ((moduleTensorMap s (𝟙 N)).app U
    ((moduleTensorUnit N).inv.app U n)) = _
  rw [unit_inv_pure]
  exact congrArg (fun z => E.hom.app U z)
    (PiExponentSeshadri.TensorPure.map_pure s (𝟙 N) U (1 : Γ(X,U)) n)

lemma dualMap_coefficient (E : moduleTensor X M N ≅ O X) (e : M ≅ O X)
    (s : O X ⟶ M) :
    endValue ((pairingFrame E e).inv ≫ dualMap E s) = coefficient e s := by
  change (dualMap E s).app ⊤ ((pairingFrame E e).inv.app ⊤ (1 : Γ(X,⊤))) = e.hom.app ⊤ (s.app ⊤ (1 : Γ(X,⊤)))
  exact (dualMap_apply E s ⊤ ((pairingFrame E e).inv.app ⊤ (1 : Γ(X,⊤)))).trans
    (pairing_inverse_generator E e ⊤ (s.app ⊤ (1 : Γ(X,⊤))))

def restrictPairing (E : moduleTensor X M N ≅ O X) (U : X.Opens) :
    moduleTensor U.toScheme (M.restrict U.ι) (N.restrict U.ι) ≅ O U.toScheme :=
  (moduleTensorRestrict U M N).symm ≪≫
    (Scheme.Modules.restrictFunctor U.ι).mapIso E ≪≫ Scheme.Modules.restrictUnitIso U.ι

def inverseOpenFrame (E : moduleTensor X M N ≅ O X) (U : X.Opens)
    (e : M.restrict U.ι ≅ O U.toScheme) : N.restrict U.ι ≅ O U.toScheme :=
  pairingFrame (restrictPairing E U) e

lemma inverseOpenFrame_frameChange (E : moduleTensor X M N ≅ O X) (U : X.Opens)
    (e f : M.restrict U.ι ≅ O U.toScheme) :
    frameChange (inverseOpenFrame E U e) (inverseOpenFrame E U f) = frameChange f e :=
  pairingFrame_frameChange (restrictPairing E U) e f

end
end PiExponent.InverseFrames

end OAI
end Source0072

section Source0073
/-
Modification notice for the LogTwo project.
Derived from openai/math (Apache-2.0), revision adc7f1241b42e322a6451854ab7e4b4c146bf78a.
Original source: lean/OAI/NumberTheory/PiExponent/Approximation/CocycleTensor.lean
Changes: Convert module/import declarations to the Lean 4.34 public module format.
See ../../../../../THIRD_PARTY_NOTICES.txt for provenance and the recorded changes.
-/




namespace OAI

noncomputable section

namespace PiExponentSeshadri.LineBundleGluing
open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite MonoidalCategory
open PiExponentSeshadri.Geometry PiExponentSeshadri.TensorPure
variable {X : Scheme} {ι : Type} {U : ι → X.Opens}

def Cocycle.one : Cocycle U where
  transition _ _ _ _ _ := 1
  restriction _ _ _ _ _ := by simp
  identity _ _ _ := rfl
  cocycle _ _ _ _ _ _ _ := one_mul _

def Cocycle.inverse (c : Cocycle U) : Cocycle U where
  transition i j W hi hj := (c.transition i j W hi hj)⁻¹
  restriction := by
    intro i j V W h hi hj
    have h' : restrictUnit h (c.transition i j _ hi hj) =
        c.transition i j _ (h.trans hi) (h.trans hj) := Units.ext (c.restriction i j h hi hj)
    exact congrArg Units.val ((map_inv (restrictUnit h) _).symm.trans (congrArg Inv.inv h'))
  identity i W hi := by rw [c.identity, inv_one]
  cocycle i j k W hi hj hk := by rw [← mul_inv, c.cocycle]

def inverseProduct (c : Cocycle U) (V : X.Opens)
    (s : sections c V) (t : sections c.inverse V) : sections (Cocycle.one (U := U)) V :=
  ⟨fun p => s.val p * t.val p, by
    constructor
    · intro i W W' hW hi h
      change X.presheaf.map (homOfLE h).op (_ * _) = _
      rw [map_mul, s.property.1 i W W' hW hi h, t.property.1 i W W' hW hi h]
    · intro i j W hW hi hj
      change s.val ⟨i,W,hW,hi⟩ * t.val ⟨i,W,hW,hi⟩ = 1 * _
      rw [s.property.2 i j W hW hi hj, t.property.2 i j W hW hi hj, one_mul]
      change (_ * _) * ((↑((c.transition i j W hi hj)⁻¹ : Γ(X,W)ˣ) : Γ(X,W)) * _) = _
      rw [mul_mul_mul_comm, Units.mul_inv, one_mul]⟩

def inverseProductMap (c : Cocycle U) :
    PresheafOfModulesOfCommRing.Monoidal.tensorObj (R := X.presheaf)
      (presheaf c) (presheaf c.inverse) ⟶ presheaf (Cocycle.one (U := U)) where
  app V := ModuleCat.MonoidalCategory.tensorLift (inverseProduct c V.unop)
    (by intros; apply Subtype.ext; funext p; exact add_mul _ _ _)
    (by intros; apply Subtype.ext; funext p; exact mul_assoc _ _ _)
    (by intros; apply Subtype.ext; funext p; exact mul_add _ _ _)
    (by intros; apply Subtype.ext; funext p; exact mul_left_comm _ _ _)
  naturality {V W} f := by
    apply ModuleCat.MonoidalCategory.tensor_ext
    intro s t
    rfl

def trivialCoefficientMap : (structureSheaf X).val ⟶ presheaf (Cocycle.one (U := U)) where
  app V := ModuleCat.ofHom (R := Γ(X, V.unop))
    (X := ModuleCat.of Γ(X, V.unop) Γ(X, V.unop))
    (Y := ModuleCat.of Γ(X, V.unop) (sections (Cocycle.one (U := U)) V.unop)) {
    toFun a := ⟨fun p => X.presheaf.map (homOfLE p.2.property.1).op a, by
      constructor
      · intro i W W' hW hi h
        change (X.presheaf.map _ ≫ X.presheaf.map _) a = _
        rw [← Functor.map_comp]
        rfl
      · intros; exact (one_mul _).symm⟩
    map_add' a b := by apply Subtype.ext; funext p; exact map_add _ _ _
    map_smul' a b := by apply Subtype.ext; funext p; exact map_mul _ _ _ }
  naturality {V W} f := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro a
    apply Subtype.ext
    funext p
    change (X.presheaf.map _ ≫ X.presheaf.map _) a = _
    rw [← Functor.map_comp]
    rfl

lemma cocycleUnit_restrict_isIso (c : Cocycle U) (i : ι) :
    IsIso ((modulePresheafRestrict (U i).ι).map ((adj X).unit.app (presheaf c))) := by
  let R : PresheafOfModules X.ringCatSheaf.obj ⥤
      PresheafOfModules (U i).toScheme.ringCatSheaf.obj := modulePresheafRestrict (U i).ι
  have hη : IsIso ((adj (U i).toScheme).unit.app (R.obj (presheaf c))) :=
    sheafification_unit_isIso_of_iso _ (structureSheaf (U i).toScheme)
      (chartPresheafFrame c i)
  have hh : IsIso (R.map ((adj X).unit.app (presheaf c)) ≫
      ((moduleSheafificationRestrict (U i).ι).hom.app (presheaf c)).val) := by
    erw [sheafify_restrict_unit]
    exact hη
  let V : (U i).toScheme.Modules ⥤ PresheafOfModules (U i).toScheme.ringCatSheaf.obj :=
    SheafOfModules.forget (U i).toScheme.ringCatSheaf
  let hv : IsIso (C := PresheafOfModules (U i).toScheme.ringCatSheaf.obj)
      (((moduleSheafificationRestrict (U i).ι).hom.app (presheaf c)).val) :=
    (V.mapIso ((moduleSheafificationRestrict (U i).ι).app (presheaf c))).isIso_hom
  exact (@isIso_comp_right_iff (PresheafOfModules (U i).toScheme.ringCatSheaf.obj)
    _ _ _ _ _ _ hv).mp hh

lemma trivialCoefficientMap_frame (i : ι) :
    (modulePresheafRestrict (U i).ι).map (trivialCoefficientMap (U := U)) ≫
      (chartPresheafFrame (Cocycle.one (U := U)) i).hom =
    (Scheme.Modules.restrictUnitIso (U i).ι).hom.val := by
  ext V a
  change X.presheaf.map (homOfLE (show (U i).ι ''ᵁ V.unop ≤ (U i).ι ''ᵁ V.unop from le_rfl)).op a = _
  simp only [homOfLE_refl, op_id, CategoryTheory.Functor.map_id]
  change a = ((U i).ι.appIso V.unop).hom a
  simp only [Scheme.Opens.ι_appIso, Iso.refl_hom]
  rfl

lemma trivialCoefficientMap_restrict_isIso (i : ι) :
    IsIso ((modulePresheafRestrict (U i).ι).map (trivialCoefficientMap (U := U))) := by
  let V : (U i).toScheme.Modules ⥤ PresheafOfModules (U i).toScheme.ringCatSheaf.obj :=
    SheafOfModules.forget (U i).toScheme.ringCatSheaf
  have hv : IsIso (C := PresheafOfModules (U i).toScheme.ringCatSheaf.obj)
      ((Scheme.Modules.restrictUnitIso (U i).ι).hom.val) :=
    (V.mapIso (Scheme.Modules.restrictUnitIso (U i).ι)).isIso_hom
  have hh : IsIso ((modulePresheafRestrict (U i).ι).map (trivialCoefficientMap (U := U)) ≫
      (chartPresheafFrame (Cocycle.one (U := U)) i).hom) := by
    rw [trivialCoefficientMap_frame]
    exact hv
  let hc : IsIso (C := PresheafOfModules (U i).toScheme.ringCatSheaf.obj)
      (chartPresheafFrame (Cocycle.one (U := U)) i).hom :=
    (chartPresheafFrame (Cocycle.one (U := U)) i).isIso_hom
  exact (@isIso_comp_right_iff (PresheafOfModules (U i).toScheme.ringCatSheaf.obj)
    _ _ _ _ _ _ hc).mp hh

lemma inverseProductMap_frame (c : Cocycle U) (i : ι) :
    (modulePresheafRestrict (U i).ι).map (inverseProductMap c) ≫
      (chartPresheafFrame (Cocycle.one (U := U)) i).hom =
    (modulePresheafTensorRestrict (U i) (presheaf c) (presheaf c.inverse)).hom ≫
      PresheafOfModulesOfCommRing.Monoidal.tensorHom (R := (U i).toScheme.presheaf)
        (chartPresheafFrame c i).hom (chartPresheafFrame c.inverse i).hom ≫
      (by
        let : MonoidalCategory (PresheafOfModules (U i).toScheme.ringCatSheaf.obj) :=
          PresheafOfModulesOfCommRing.monoidalCategory (R := (U i).toScheme.presheaf)
        exact (λ_ (structureSheaf (U i).toScheme).val).hom) := by
  let : MonoidalCategory (PresheafOfModules (U i).toScheme.ringCatSheaf.obj) :=
    PresheafOfModulesOfCommRing.monoidalCategory (R := (U i).toScheme.presheaf)
  let l := (modulePresheafRestrict (U i).ι).map (inverseProductMap c) ≫
    (chartPresheafFrame (Cocycle.one (U := U)) i).hom
  let r := (modulePresheafTensorRestrict (U i) (presheaf c) (presheaf c.inverse)).hom ≫
    PresheafOfModulesOfCommRing.Monoidal.tensorHom (R := (U i).toScheme.presheaf)
      (chartPresheafFrame c i).hom (chartPresheafFrame c.inverse i).hom ≫
    (λ_ (structureSheaf (U i).toScheme).val).hom
  change l = r
  ext V : 1
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro z
  induction z using TensorProduct.inductionOn with
  | tmul s t => rfl
  | add a b ha hb =>
      exact ((l.app V).hom.map_add a b).trans
        ((congrArg₂ (· + ·) ha hb).trans ((r.app V).hom.map_add a b).symm)

lemma inverseProductMap_restrict_isIso (c : Cocycle U) (i : ι) :
    IsIso ((modulePresheafRestrict (U i).ι).map (inverseProductMap c)) := by
  let : MonoidalCategory (PresheafOfModules (U i).toScheme.ringCatSheaf.obj) :=
    PresheafOfModulesOfCommRing.monoidalCategory (R := (U i).toScheme.presheaf)
  let e := modulePresheafTensorRestrict (U i) (presheaf c) (presheaf c.inverse) ≪≫
    tensorIso (chartPresheafFrame c i) (chartPresheafFrame c.inverse i) ≪≫
      λ_ (structureSheaf (U i).toScheme).val
  have hh : IsIso ((modulePresheafRestrict (U i).ι).map (inverseProductMap c) ≫
      (chartPresheafFrame (Cocycle.one (U := U)) i).hom) := by
    rw [inverseProductMap_frame]
    exact e.isIso_hom
  let hc : IsIso (C := PresheafOfModules (U i).toScheme.ringCatSheaf.obj)
      (chartPresheafFrame (Cocycle.one (U := U)) i).hom :=
    (chartPresheafFrame (Cocycle.one (U := U)) i).isIso_hom
  exact (@isIso_comp_right_iff (PresheafOfModules (U i).toScheme.ringCatSheaf.obj)
    _ _ _ _ _ _ hc).mp hh

lemma sheafification_isIso_of_chart {P Q : PresheafOfModules X.ringCatSheaf.obj}
    (f : P ⟶ Q) (hcover : ⊤ ≤ ⨆ i, U i)
    (hf : ∀ i, IsIso ((modulePresheafRestrict (U i).ι).map f)) :
    IsIso ((PresheafOfModules.sheafification (𝟙 X.ringCatSheaf.obj)).map f) := by
  apply PiExponent.NumericalAmpleness.isIso_of_locally_isIso
  intro x
  obtain ⟨i, hi⟩ := Opens.mem_iSup.mp (hcover (show x ∈ (⊤ : X.Opens) from trivial))
  refine ⟨U i, hi, ?_⟩
  apply (NatIso.isIso_map_iff (moduleSheafificationRestrict (U i).ι) f).mpr
  have := hf i
  change IsIso ((PresheafOfModules.sheafification (𝟙 (U i).toScheme.ringCatSheaf.obj)).map
    ((modulePresheafRestrict (U i).ι).map f))
  infer_instance

end PiExponentSeshadri.LineBundleGluing

end

end OAI
end Source0073

section Source0074
/-
Modification notice for the LogTwo project.
Derived from openai/math (Apache-2.0), revision adc7f1241b42e322a6451854ab7e4b4c146bf78a.
Original source: lean/OAI/NumberTheory/PiExponent/Approximation/CocycleTensorIso.lean
Changes: Convert module/import declarations to the Lean 4.34 public module format.
See ../../../../../THIRD_PARTY_NOTICES.txt for provenance and the recorded changes.
-/




namespace OAI

namespace PiExponentSeshadri.LineBundleGluing
noncomputable section
open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite MonoidalCategory
open PiExponentSeshadri.Geometry PiExponentSeshadri.TensorPure
variable {X : Scheme} {ι : Type} {U : ι → X.Opens}

lemma tensorHom_restrict_isIso (W : X.Opens)
    {P P' Q Q' : PresheafOfModules X.ringCatSheaf.obj} (f : P ⟶ P') (g : Q ⟶ Q')
    [IsIso ((modulePresheafRestrict W.ι).map f)]
    [IsIso ((modulePresheafRestrict W.ι).map g)] :
    IsIso ((modulePresheafRestrict W.ι).map
      (PresheafOfModulesOfCommRing.Monoidal.tensorHom (R := X.presheaf) f g)) := by
  let R := modulePresheafRestrict W.ι
  let : MonoidalCategory (PresheafOfModules W.toScheme.ringCatSheaf.obj) :=
    PresheafOfModulesOfCommRing.monoidalCategory (R := W.toScheme.presheaf)
  have hh : IsIso (R.map (PresheafOfModulesOfCommRing.Monoidal.tensorHom (R := X.presheaf) f g) ≫
      (modulePresheafTensorRestrict W P' Q').hom) := by
    rw [modulePresheafTensorRestrict_natural]
    change IsIso (_ ≫ (R.map f ⊗ₘ R.map g))
    infer_instance
  let hc : IsIso (C := PresheafOfModules W.toScheme.ringCatSheaf.obj)
      (modulePresheafTensorRestrict W P' Q').hom :=
    (modulePresheafTensorRestrict W P' Q').isIso_hom
  exact (@isIso_comp_right_iff (PresheafOfModules W.toScheme.ringCatSheaf.obj)
    _ _ _ _ _ _ hc).mp hh

def cocycleTensorComparison (c d : Cocycle U) (hcover : ⊤ ≤ ⨆ i, U i) :
    (PresheafOfModules.sheafification (𝟙 X.ringCatSheaf.obj)).obj
      (PresheafOfModulesOfCommRing.Monoidal.tensorObj (R := X.presheaf)
        (presheaf c) (presheaf d)) ≅ moduleTensor X (sheaf c) (sheaf d) := by
  let f := PresheafOfModulesOfCommRing.Monoidal.tensorHom (R := X.presheaf)
    ((adj X).unit.app (presheaf c)) ((adj X).unit.app (presheaf d))
  have ht : IsIso ((PresheafOfModules.sheafification (𝟙 X.ringCatSheaf.obj)).map f) := by
    apply sheafification_isIso_of_chart f hcover
    intro i
    have := cocycleUnit_restrict_isIso c i
    have := cocycleUnit_restrict_isIso d i
    exact tensorHom_restrict_isIso (U i) _ _
  exact @asIso _ _ _ _ ((PresheafOfModules.sheafification (𝟙 X.ringCatSheaf.obj)).map f) ht

def trivialSheafIso (hcover : ⊤ ≤ ⨆ i, U i) :
    sheaf (Cocycle.one (U := U)) ≅ structureSheaf X := by
  have ht : IsIso ((PresheafOfModules.sheafification (𝟙 X.ringCatSheaf.obj)).map
      (trivialCoefficientMap (U := U))) :=
    sheafification_isIso_of_chart _ hcover trivialCoefficientMap_restrict_isIso
  exact (@asIso _ _ _ _ ((PresheafOfModules.sheafification (𝟙 X.ringCatSheaf.obj)).map
    (trivialCoefficientMap (U := U))) ht).symm ≪≫
      (asIso (adj X).counit).app (structureSheaf X)

def tensorInverseIso (c : Cocycle U) (hcover : ⊤ ≤ ⨆ i, U i) :
    moduleTensor X (sheaf c) (sheaf c.inverse) ≅ structureSheaf X := by
  have ht : IsIso ((PresheafOfModules.sheafification (𝟙 X.ringCatSheaf.obj)).map
      (inverseProductMap c)) :=
    sheafification_isIso_of_chart _ hcover (inverseProductMap_restrict_isIso c)
  exact (cocycleTensorComparison c c.inverse hcover).symm ≪≫
    @asIso _ _ _ _ ((PresheafOfModules.sheafification (𝟙 X.ringCatSheaf.obj)).map
      (inverseProductMap c)) ht ≪≫
      trivialSheafIso hcover

end
end PiExponentSeshadri.LineBundleGluing

end OAI
end Source0074

section Source0075
/-
Modification notice for the LogTwo project.
Derived from openai/math (Apache-2.0), revision adc7f1241b42e322a6451854ab7e4b4c146bf78a.
Original source: lean/OAI/NumberTheory/PiExponent/Approximation/FrameSubopensCoherence.lean
Changes: Convert module/import declarations to the Lean 4.34 public module format.
See ../../../../../THIRD_PARTY_NOTICES.txt for provenance and the recorded changes.
-/




namespace OAI

namespace PiExponentSeshadri.Frames
noncomputable section
open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite
variable {X : Scheme} {M : X.Modules} {U V W : X.Opens}

lemma restrictOpenFrame_app (h : V ≤ U) (e : M.restrict U.ι ≅ O U.toScheme)
    (A : V.toScheme.Opens) (x : Γ(M.restrict V.ι,A)) :
    (restrictOpenFrame h e).hom.app A x =
      X.presheaf.map (homOfLE (show V.ι ''ᵁ A ≤ U.ι ''ᵁ (X.homOfLE h ''ᵁ A) from by
        simp [← Scheme.Hom.comp_image])).op
        (e.hom.app (X.homOfLE h ''ᵁ A)
          (M.presheaf.map (homOfLE
            (show U.ι ''ᵁ (X.homOfLE h ''ᵁ A) ≤ V.ι ''ᵁ A from by
              simp [← Scheme.Hom.comp_image])).op x)) := by
  simp only [restrictOpenFrame, Iso.trans_hom, Iso.symm_hom,
    Scheme.Modules.Hom.comp_app, Iso.app_inv, Iso.app_hom,
    Scheme.Modules.restrictFunctorCongr_inv_app_app,
    Scheme.Modules.restrictFunctorComp_hom_app_app]
  change ((X.homOfLE h).appIso A).hom (e.hom.app (X.homOfLE h ''ᵁ A)
    ((M.presheaf.map _ ≫ M.presheaf.map _) x)) = _
  simp only [Scheme.Hom.appIso_hom', Scheme.homOfLE_appLE]
  erw [← Functor.map_comp]
  rfl

lemma restrictOpenFrame_trans (h : W ≤ V) (k : V ≤ U)
    (e : M.restrict U.ι ≅ O U.toScheme) :
    restrictOpenFrame h (restrictOpenFrame k e) = restrictOpenFrame (h.trans k) e := by
  apply Iso.ext
  ext A x
  have hh := restrictOpenFrame_app h (restrictOpenFrame k e) A x
  let y := M.presheaf.map (homOfLE
    (show V.ι ''ᵁ (X.homOfLE h ''ᵁ A) ≤ W.ι ''ᵁ A from by
      simp [← Scheme.Hom.comp_image])).op x
  have hk := restrictOpenFrame_app k e (X.homOfLE h ''ᵁ A) y
  have hhk := congrArg (X.presheaf.map (homOfLE
    (show W.ι ''ᵁ A ≤ V.ι ''ᵁ (X.homOfLE h ''ᵁ A) from by
      simp [← Scheme.Hom.comp_image])).op) hk
  have hc := restrictOpenFrame_app (h.trans k) e A x
  refine hh.trans (hhk.trans (Eq.trans ?_ hc.symm))
  change (X.presheaf.map _ ≫ X.presheaf.map _)
    (e.hom.app (X.homOfLE k ''ᵁ (X.homOfLE h ''ᵁ A))
      ((M.presheaf.map _ ≫ M.presheaf.map _) x)) =
    X.presheaf.map _ (e.hom.app (X.homOfLE (h.trans k) ''ᵁ A)
      (M.presheaf.map _ x))
  erw [← Functor.map_comp, ← Functor.map_comp]
  let B := X.homOfLE k ''ᵁ (X.homOfLE h ''ᵁ A)
  let C := X.homOfLE (h.trans k) ''ᵁ A
  have hA : C ≤ B := by
    simp only [B, C, ← Scheme.Hom.comp_image, Scheme.homOfLE_homOfLE]
    exact le_rfl
  have hB : U.ι ''ᵁ B ≤ W.ι ''ᵁ A := by
    simp [B, ← Scheme.Hom.comp_image]
  have hC : W.ι ''ᵁ A ≤ U.ι ''ᵁ C := by
    simp [C, ← Scheme.Hom.comp_image]
  have hn := CategoryTheory.congr_fun
    (e.hom.mapPresheaf.naturality (homOfLE hA).op)
    (M.presheaf.map (homOfLE hB).op x)
  change e.hom.app C ((M.restrict U.ι).presheaf.map (homOfLE hA).op
    (M.presheaf.map (homOfLE hB).op x)) =
    U.toScheme.presheaf.map (homOfLE hA).op
      (e.hom.app B (M.presheaf.map (homOfLE hB).op x)) at hn
  refine Eq.trans ?_ (Eq.trans (congrArg (X.presheaf.map (homOfLE hC).op) hn).symm ?_)
  · change X.presheaf.map _ (e.hom.app B (M.presheaf.map _ x)) =
      (X.presheaf.map _ ≫ X.presheaf.map _) (e.hom.app B (M.presheaf.map _ x))
    erw [← Functor.map_comp]
    rfl
  · apply congrArg (X.presheaf.map (homOfLE hC).op)
    apply congrArg (e.hom.app C)
    change (M.presheaf.map _ ≫ M.presheaf.map _) x = M.presheaf.map _ x
    erw [← Functor.map_comp]
    rfl
end
end PiExponentSeshadri.Frames

end OAI
end Source0075

section Source0076
/-
Modification notice for the LogTwo project.
Derived from openai/math (Apache-2.0), revision adc7f1241b42e322a6451854ab7e4b4c146bf78a.
Original source: lean/OAI/NumberTheory/PiExponent/Polynomials/FrameCoefficientLaws.lean
Changes: Convert module/import declarations to the Lean 4.34 public module format.
See ../../../../../THIRD_PARTY_NOTICES.txt for provenance and the recorded changes.
-/




namespace OAI

namespace PiExponentSeshadri.ProjectiveChartSections
noncomputable section
open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite
open PiExponentSeshadri.Geometry ModuleFlasque RestrictionCohomology Frames
variable {X : Scheme} (U : X.Opens) (M : X.Modules)

lemma framedCoefficientsEquiv_smul
    (e : M.restrict U.ι ≅ structureSheaf U.toScheme)
    (a : Γ(X,U)) (s : Γ(M,U)) :
    framedCoefficientsEquiv U M e (a • s) =
      a * framedCoefficientsEquiv U M e s := by
  have hs : (restrictionSectionsIso U M).inv (a • s) =
      U.topIso.inv a • (restrictionSectionsIso U M).inv s := by
    change M.presheaf.map (eqToHom U.ι_image_top).op (a • s) =
      (U.ι.appIso ⊤).inv (U.topIso.inv a) •
        M.presheaf.map (eqToHom U.ι_image_top).op s
    rw [M.map_smul, U.ι_appIso]
    rfl
  change U.topIso.hom (e.hom.app ⊤ ((restrictionSectionsIso U M).inv (a • s))) =
    a * U.topIso.hom (e.hom.app ⊤ ((restrictionSectionsIso U M).inv s))
  rw [hs, e.hom.app_smul]
  change U.topIso.hom (U.topIso.inv a * _) = _
  erw [map_mul]
  erw [Iso.inv_hom_id_apply]

lemma framedCoefficientsEquiv_change
    (e f : M.restrict U.ι ≅ structureSheaf U.toScheme) (s : Γ(M,U)) :
    framedCoefficientsEquiv U M f s =
      U.topIso.hom (frameChange e f : Γ(U.toScheme,⊤)) *
        framedCoefficientsEquiv U M e s := by
  let t := (restrictionSectionsIso U M).inv s
  have he : e.inv.app ⊤ (e.hom.app ⊤ t) = t := by
    exact congrArg (fun q => q.app ⊤ t) e.hom_inv_id
  have h := end_apply (e.inv ≫ f.hom) ⊤ (e.hom.app ⊤ t)
  change f.hom.app ⊤ (e.inv.app ⊤ (e.hom.app ⊤ t)) =
    (show Γ(U.toScheme,⊤) from e.hom.app ⊤ t) *
      (frameChange e f : Γ(U.toScheme,⊤)) at h
  rw [he, mul_comm] at h
  change U.topIso.hom (f.hom.app ⊤ t) =
    U.topIso.hom (frameChange e f : Γ(U.toScheme,⊤)) * U.topIso.hom (e.hom.app ⊤ t)
  rw [h, map_mul]

end
end PiExponentSeshadri.ProjectiveChartSections

end OAI
end Source0076

section Source0077
/-
Modification notice for the LogTwo project.
Derived from openai/math (Apache-2.0), revision adc7f1241b42e322a6451854ab7e4b4c146bf78a.
Original source: lean/OAI/NumberTheory/PiExponent/Geometry/LineBundleFrameCocycle.lean
Changes: Convert module/import declarations to the Lean 4.34 public module format.
See ../../../../../THIRD_PARTY_NOTICES.txt for provenance and the recorded changes.
-/




namespace OAI

namespace PiExponentSeshadri.LineBundleFrameCocycle
noncomputable section
open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite
open PiExponentSeshadri.Geometry PiExponentSeshadri.Frames
open PiExponentSeshadri.ProjectiveChartSections

variable {X : Scheme} {ι : Type} (M : X.Modules) (U : ι → X.Opens)
  (e : ∀ i, M.restrict (U i).ι ≅ structureSheaf (U i).toScheme)

abbrev frame (i : ι) (W : X.Opens) (hi : W ≤ U i) := restrictOpenFrame hi (e i)

abbrev coeff (i : ι) (W : X.Opens) (hi : W ≤ U i) :=
  framedCoefficientsEquiv W M (frame M U e i W hi)

lemma coeff_restrict {V W : X.Opens} (h : V ≤ W) (i : ι) (hi : W ≤ U i)
    (s : Γ(M,W)) :
    coeff M U e i V (h.trans hi) (M.presheaf.map (homOfLE h).op s) =
      X.presheaf.map (homOfLE h).op (coeff M U e i W hi s) := by
  change framedCoefficientsEquiv V M (restrictOpenFrame (h.trans hi) (e i)) _ = _
  rw [← restrictOpenFrame_trans h hi (e i)]
  exact framedCoefficientsEquiv_restrict M h _ s

def transition (i j : ι) (W : X.Opens) (hi : W ≤ U i) (hj : W ≤ U j) : Γ(X,W)ˣ :=
  Units.map W.topIso.hom.hom.toMonoidHom
    (frameChange (frame M U e j W hj) (frame M U e i W hi))

lemma coeff_change (i j : ι) (W : X.Opens) (hi : W ≤ U i) (hj : W ≤ U j)
    (s : Γ(M,W)) :
    coeff M U e i W hi s = (transition M U e i j W hi hj : Γ(X,W)) *
      coeff M U e j W hj s := by
  exact framedCoefficientsEquiv_change W M (frame M U e j W hj) (frame M U e i W hi) s

def ofFrames : LineBundleGluing.Cocycle U where
  transition := transition M U e
  restriction i j {V W} h hi hj := by
    let s := (coeff M U e j W hj).symm 1
    have hj1 : coeff M U e j W hj s = (1 : Γ(X,W)) :=
      (coeff M U e j W hj).apply_symm_apply 1
    have hi1 : coeff M U e i W hi s = (transition M U e i j W hi hj : Γ(X,W)) := by
      rw [coeff_change M U e i j W hi hj, hj1, mul_one]
    have hjV : coeff M U e j V (h.trans hj) (M.presheaf.map (homOfLE h).op s) = 1 := by
      rw [coeff_restrict M U e h j hj, hj1]
      exact map_one (X.presheaf.map (homOfLE h).op).hom
    calc
      _ = X.presheaf.map (homOfLE h).op (coeff M U e i W hi s) := congrArg _ hi1.symm
      _ = coeff M U e i V (h.trans hi) (M.presheaf.map (homOfLE h).op s) :=
        (coeff_restrict M U e h i hi s).symm
      _ = _ := by rw [coeff_change M U e i j V (h.trans hi) (h.trans hj), hjV, mul_one]
  identity i W hi := by
    apply Units.ext
    change W.topIso.hom (endValue ((frame M U e i W hi).inv ≫
      (frame M U e i W hi).hom)) = 1
    simp
  cocycle i j k W hi hj hk := by
    apply Units.ext
    change W.topIso.hom (endValue ((frame M U e j W hj).inv ≫
      (frame M U e i W hi).hom)) *
      W.topIso.hom (endValue ((frame M U e k W hk).inv ≫
        (frame M U e j W hj).hom)) =
      W.topIso.hom (endValue ((frame M U e k W hk).inv ≫
        (frame M U e i W hi).hom))
    rw [← map_mul, mul_comm, ← endValue_comp]
    simp

def toSections (V : X.Opens) (s : Γ(M,V)) : LineBundleGluing.sections (ofFrames M U e) V :=
  ⟨fun p => coeff M U e p.1 p.2.val p.2.property.2
    (M.presheaf.map (homOfLE p.2.property.1).op s), by
    constructor
    · intro i W W' hW hi h
      change X.presheaf.map (homOfLE h).op
        (coeff M U e i W hi (M.presheaf.map (homOfLE hW).op s)) = _
      rw [← coeff_restrict]
      congr 1
      change (M.presheaf.map _ ≫ M.presheaf.map _) s = _
      rw [← Functor.map_comp]
      rfl
    · intro i j W hW hi hj
      exact coeff_change M U e i j W hi hj _⟩

lemma chartEquiv_toSections (i : ι) (V : X.Opens) (hi : V ≤ U i) (s : Γ(M,V)) :
    LineBundleGluing.chartEquiv (ofFrames M U e) i hi (toSections M U e V s) =
      coeff M U e i V hi s := by
  change coeff M U e i V hi (M.presheaf.map (homOfLE (le_refl V)).op s) = _
  simp

lemma toSections_bijective (i : ι) (V : X.Opens) (hi : V ≤ U i) :
    Function.Bijective (toSections M U e V) := by
  constructor
  · intro s t h
    apply (coeff M U e i V hi).injective
    simpa only [chartEquiv_toSections] using
      congrArg (LineBundleGluing.chartEquiv (ofFrames M U e) i hi) h
  · intro t
    refine ⟨(coeff M U e i V hi).symm
      (LineBundleGluing.chartEquiv (ofFrames M U e) i hi t), ?_⟩
    apply (LineBundleGluing.chartEquiv (ofFrames M U e) i hi).injective
    rw [chartEquiv_toSections, AddEquiv.apply_symm_apply]

def presheafHom : M.val ⟶ LineBundleGluing.presheaf (ofFrames M U e) where
  app V := ModuleCat.ofHom
    (X := M.val.obj V)
    (Y := (LineBundleGluing.presheaf (ofFrames M U e)).obj V)
    { toFun := toSections M U e V.unop
      map_add' := by
        intro s t
        apply Subtype.ext
        funext p
        change coeff M U e p.1 p.2.val p.2.property.2
          (M.presheaf.map (homOfLE p.2.property.1).op (s + t)) = _
        erw [map_add]
        exact map_add _ _ _
      map_smul' := by
        intro a s
        apply Subtype.ext
        funext p
        change coeff M U e p.1 p.2.val p.2.property.2
          (M.presheaf.map (homOfLE p.2.property.1).op (a • s)) =
          X.presheaf.map (homOfLE p.2.property.1).op a *
            coeff M U e p.1 p.2.val p.2.property.2
              (M.presheaf.map (homOfLE p.2.property.1).op s)
        erw [M.map_smul]
        exact framedCoefficientsEquiv_smul _ _ _ _ _ }
  naturality {V W} f := by
    ext s
    apply Subtype.ext
    funext p
    change coeff M U e p.1 p.2.val p.2.property.2
      (M.presheaf.map (homOfLE p.2.property.1).op (M.presheaf.map f s)) =
      coeff M U e p.1 p.2.val p.2.property.2 (M.presheaf.map _ s)
    congr 1
    change (M.presheaf.map _ ≫ M.presheaf.map _) s = _
    rw [← Functor.map_comp]
    rfl

lemma restrict_presheafHom_isIso (i : ι) :
    IsIso ((modulePresheafRestrict (U i).ι).map (presheafHom M U e)) := by
  let f := (modulePresheafRestrict (U i).ι).map (presheafHom M U e)
  have (V : (U i).toScheme.Opensᵒᵖ) : IsIso (f.app V) := by
    apply (ConcreteCategory.isIso_iff_bijective (f.app V)).mpr
    exact toSections_bijective M U e i ((U i).ι ''ᵁ V.unop) ((U i).ι_image_le V.unop)
  let a := PresheafOfModules.isoMk (fun V => asIso (f.app V))
    (fun {_ _} k => f.naturality k)
  change IsIso a.hom
  infer_instance

lemma sheafification_presheafHom_isIso (hcover : ⊤ ≤ ⨆ i, U i) :
    IsIso ((PresheafOfModules.sheafification (𝟙 X.ringCatSheaf.obj)).map
      (presheafHom M U e)) := by
  apply SectionOpens.isIso_of_locally_isIso
  intro x
  have hx : x ∈ ⨆ i, U i := hcover (show x ∈ (⊤ : X.Opens) from trivial)
  obtain ⟨i, hi⟩ := Opens.mem_iSup.mp hx
  refine ⟨U i, hi, ?_⟩
  let := restrict_presheafHom_isIso M U e i
  apply (NatIso.isIso_map_iff (moduleSheafificationRestrict (U i).ι)
    (presheafHom M U e)).mpr
  change IsIso ((PresheafOfModules.sheafification (𝟙 (U i).toScheme.ringCatSheaf.obj)).map
    ((modulePresheafRestrict (U i).ι).map (presheafHom M U e)))
  infer_instance

def isoSheaf (hcover : ⊤ ≤ ⨆ i, U i) :
    M ≅ LineBundleGluing.sheaf (ofFrames M U e) := by
  letI := sheafification_presheafHom_isIso M U e hcover
  exact ((asIso (PresheafOfModules.sheafificationAdjunction (R := X.ringCatSheaf)
    (𝟙 X.ringCatSheaf.obj)).counit).app M).symm ≪≫
    @asIso _ _ _ _
      ((PresheafOfModules.sheafification (𝟙 X.ringCatSheaf.obj)).map (presheafHom M U e))
      (sheafification_presheafHom_isIso M U e hcover)

end
end PiExponentSeshadri.LineBundleFrameCocycle

end OAI
end Source0077

section Source0078
/-
Modification notice for the LogTwo project.
Derived from openai/math (Apache-2.0), revision adc7f1241b42e322a6451854ab7e4b4c146bf78a.
Original source: lean/OAI/NumberTheory/PiExponent/Geometry/LineBundleInverse.lean
Changes: Convert module/import declarations to the Lean 4.34 public module format.
See ../../../../../THIRD_PARTY_NOTICES.txt for provenance and the recorded changes.
-/




namespace OAI

namespace PiExponentSeshadri.Geometry
noncomputable section
open AlgebraicGeometry CategoryTheory TopologicalSpace
variable {X : Scheme}

def LineBundle.inverseCover (L : LineBundle X) (x : X) : X.Opens :=
  (L.locallyRankOne x).choose

lemma LineBundle.mem_inverseCover (L : LineBundle X) (x : X) :
    x ∈ L.inverseCover x := (L.locallyRankOne x).choose_spec.1

def LineBundle.inverseCoverFrame (L : LineBundle X) (x : X) :
    L.sheaf.restrict (L.inverseCover x).ι ≅ structureSheaf (L.inverseCover x).toScheme :=
  (L.locallyRankOne x).choose_spec.2.some

lemma LineBundle.inverseCover_covers (L : LineBundle X) :
    ⊤ ≤ ⨆ x, L.inverseCover x := by
  intro x _
  exact Opens.mem_iSup.mpr ⟨x, L.mem_inverseCover x⟩

def LineBundle.inverseCocycle (L : LineBundle X) :
    LineBundleGluing.Cocycle L.inverseCover :=
  LineBundleFrameCocycle.ofFrames L.sheaf L.inverseCover L.inverseCoverFrame

def LineBundle.inverse (L : LineBundle X) : LineBundle X :=
  LineBundleGluing.lineBundle L.inverseCocycle.inverse L.inverseCover_covers

def lineTensorInverseIso (L : LineBundle X) :
    moduleTensor X L.sheaf L.inverse.sheaf ≅ structureSheaf X :=
  moduleTensorIso
    (LineBundleFrameCocycle.isoSheaf L.sheaf L.inverseCover L.inverseCoverFrame
      L.inverseCover_covers) (Iso.refl _) ≪≫
    LineBundleGluing.tensorInverseIso L.inverseCocycle L.inverseCover_covers

def moduleTensorInverseCancelIso (M : X.Modules) (L : LineBundle X) :
    moduleTensor X (moduleTensor X M L.sheaf) L.inverse.sheaf ≅ M :=
  moduleLineTensorAssoc M L L.inverse ≪≫
    moduleTensorIso (Iso.refl M) (lineTensorInverseIso L) ≪≫ moduleTensorRightUnit M

def LineBundle.dualSection (L : LineBundle X) (s : structureSheaf X ⟶ L.sheaf) :
    L.inverse.sheaf ⟶ structureSheaf X :=
  (moduleTensorUnit L.inverse.sheaf).inv ≫ moduleTensorMap s (𝟙 _) ≫
    (lineTensorInverseIso L).hom

end
end PiExponentSeshadri.Geometry

end OAI
end Source0078

section Source0079
/-
Modification notice for the LogTwo project.
Derived from openai/math (Apache-2.0), revision adc7f1241b42e322a6451854ab7e4b4c146bf78a.
Original source: lean/OAI/NumberTheory/PiExponent/Approximation/InverseDualRestriction.lean
Changes: Convert module/import declarations to the Lean 4.34 public module format.
See ../../../../../THIRD_PARTY_NOTICES.txt for provenance and the recorded changes.
-/




namespace OAI

namespace PiExponent.InverseFrames
noncomputable section
open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite
open PiExponentSeshadri.Geometry PiExponentSeshadri.Frames PiExponentSeshadri.TensorPure
variable {X : Scheme.{0}} {M N : X.Modules}

lemma dualMap_restrict (E : moduleTensor X M N ≅ O X) (s : O X ⟶ M) (U : X.Opens) :
    (Scheme.Modules.restrictFunctor U.ι).map (dualMap E s) ≫
      (Scheme.Modules.restrictUnitIso U.ι).hom =
    dualMap (restrictPairing E U) (restrictSection U.ι s) := by
  ext A n
  change Γ(N, U.ι ''ᵁ A) at n
  change (U.ι.appIso A).hom ((dualMap E s).app (U.ι ''ᵁ A) n) =
    (dualMap (restrictPairing E U) (restrictSection U.ι s)).app A n
  erw [dualMap_apply E s (U.ι ''ᵁ A) n,
    dualMap_apply (restrictPairing E U) (restrictSection U.ι s) A n]
  change (U.ι.appIso A).hom (E.hom.app (U.ι ''ᵁ A)
      (PiExponentSeshadri.TensorPure.pure M N (U.ι ''ᵁ A)
        (s.app (U.ι ''ᵁ A) (1 : Γ(X,U.ι ''ᵁ A))) n)) =
    (U.ι.appIso A).hom (E.hom.app (U.ι ''ᵁ A)
      ((moduleTensorRestrict U M N).inv.app A
        (PiExponentSeshadri.TensorPure.pure (M.restrict U.ι) (N.restrict U.ι) A
          ((restrictSection U.ι s).app A (1 : Γ(U.toScheme,A))) n)))
  erw [restrict_pure_inv U M N A
    ((restrictSection U.ι s).app A (1 : Γ(U.toScheme,A))) n]
  change (U.ι.appIso A).hom (E.hom.app (U.ι ''ᵁ A)
      (PiExponentSeshadri.TensorPure.pure M N (U.ι ''ᵁ A)
        (s.app (U.ι ''ᵁ A) (1 : Γ(X,U.ι ''ᵁ A))) n)) =
    (U.ι.appIso A).hom (E.hom.app (U.ι ''ᵁ A)
      (PiExponentSeshadri.TensorPure.pure M N (U.ι ''ᵁ A)
        (s.app (U.ι ''ᵁ A) ((U.ι.appIso A).inv (1 : Γ(U.toScheme,A)))) n))
  rw [show (U.ι.appIso A).inv (1 : Γ(U.toScheme,A)) = (1 : Γ(X,U.ι ''ᵁ A)) from
    (U.ι.appIso A).inv.hom.map_one]

lemma dualMap_restrict_coefficient (E : moduleTensor X M N ≅ O X)
    (s : O X ⟶ M) (U : X.Opens) (e : M.restrict U.ι ≅ O U.toScheme) :
    endValue ((inverseOpenFrame E U e).inv ≫
      (Scheme.Modules.restrictFunctor U.ι).map (dualMap E s) ≫
      (Scheme.Modules.restrictUnitIso U.ι).hom) =
    coefficient e (restrictSection U.ι s) := by
  erw [dualMap_restrict]
  exact dualMap_coefficient (restrictPairing E U) e (restrictSection U.ι s)

lemma dualSection_restrict_coefficient (L : LineBundle X)
    (s : structureSheaf X ⟶ L.sheaf) (U : X.Opens)
    (e : L.sheaf.restrict U.ι ≅ structureSheaf U.toScheme) :
    endValue ((inverseOpenFrame (lineTensorInverseIso L) U e).inv ≫
      (Scheme.Modules.restrictFunctor U.ι).map (L.dualSection s) ≫
      (Scheme.Modules.restrictUnitIso U.ι).hom) =
    coefficient e (restrictSection U.ι s) :=
  dualMap_restrict_coefficient (lineTensorInverseIso L) s U e

end
end PiExponent.InverseFrames

end OAI
end Source0079

section Source0080
/-
Modification notice for the LogTwo project.
Derived from openai/math (Apache-2.0), revision adc7f1241b42e322a6451854ab7e4b4c146bf78a.
Original source: lean/OAI/NumberTheory/PiExponent/LocalAlgebra/SectionImageIdeal.lean
Changes: Convert module/import declarations to the Lean 4.34 public module format.
See ../../../../../THIRD_PARTY_NOTICES.txt for provenance and the recorded changes.
-/




namespace OAI

namespace PiExponent.SectionImageIdeal
noncomputable section
open CategoryTheory AlgebraicGeometry TopologicalSpace Opposite
open PiExponentSeshadri.Geometry
variable {X : Scheme.{0}} {M : X.Modules}

def imageIdeal (φ : M ⟶ structureSheaf X) (U : X.Opens) : Ideal Γ(X,U) :=
  (φ.val.app (op U)).hom.range

lemma map_imageIdeal_le (φ : M ⟶ structureSheaf X) {U V : X.Opens} (h : U ≤ V) :
    (imageIdeal φ V).map (X.presheaf.map (homOfLE h).op).hom ≤ imageIdeal φ U := by
  apply Ideal.map_le_iff_le_comap.mpr
  rintro x ⟨m,rfl⟩
  refine ⟨M.presheaf.map (homOfLE h).op m, ?_⟩
  exact congr($(φ.mapPresheaf.naturality (homOfLE h).op) m)

theorem affine_map_imageIdeal [IsAffine X] [M.IsQuasicoherent]
    (φ : M ⟶ structureSheaf X) (r : Γ(X,⊤)) :
    (imageIdeal φ ⊤).map (X.presheaf.map (homOfLE (X.basicOpen_le r)).op).hom =
      imageIdeal φ (X.basicOpen r) := by
  apply le_antisymm (map_imageIdeal_le φ _)
  rintro x ⟨m,rfl⟩
  change Γ(M, X.basicOpen r) at m
  obtain ⟨n,z,hz⟩ := GlobalSectionClearing.affine_basicOpen_denominators M r m
  let ρ : Γ(X,⊤) →+* Γ(X,X.basicOpen r) :=
    (X.presheaf.map (homOfLE (X.basicOpen_le r)).op).hom
  have he : ρ (φ.app ⊤ z) = ρ r ^ n * (show Γ(X,X.basicOpen r) from φ.app (X.basicOpen r) m) := by
    have hn := congr($(φ.mapPresheaf.naturality (homOfLE (X.basicOpen_le r)).op) z)
    change φ.app (X.basicOpen r)
      (GlobalSectionClearing.openRestriction M (X.basicOpen_le r) z) = ρ (φ.app ⊤ z) at hn
    rw [← hn, hz]
    change φ.app (X.basicOpen r) (ρ (r^n) • m) = _
    rw [map_pow, φ.app_smul]
    rfl
  have hm : ρ (φ.app ⊤ z) ∈ (imageIdeal φ ⊤).map ρ :=
    Ideal.mem_map_of_mem ρ ⟨z,rfl⟩
  rw [he] at hm
  exact (Ideal.unit_mul_mem_iff_mem _
    ((X.toRingedSpace.isUnit_res_basicOpen r).pow n)).mp hm

theorem imageIdeal_restrict {Y : Scheme.{0}} (f : Y ⟶ X) [IsOpenImmersion f]
    (φ : M ⟶ structureSheaf X) (V : Y.Opens) :
    (imageIdeal ((Scheme.Modules.restrictFunctor f).map φ ≫
      (Scheme.Modules.restrictUnitIso f).hom) V).map (f.appIso V).inv.hom =
      imageIdeal φ (f ''ᵁ V) := by
  apply le_antisymm
  · apply Ideal.map_le_iff_le_comap.mpr
    rintro y ⟨m,rfl⟩
    refine ⟨m,?_⟩
    change φ.app (f ''ᵁ V) m = (f.appIso V).inv ((f.appIso V).hom (φ.app (f ''ᵁ V) m))
    exact ((f.appIso V).hom_inv_id_apply _).symm
  · rintro y ⟨m,rfl⟩
    have h := Ideal.mem_map_of_mem (f.appIso V).inv.hom
      (show ((f.appIso V).hom (φ.app (f ''ᵁ V) m)) ∈
        imageIdeal ((Scheme.Modules.restrictFunctor f).map φ ≫
          (Scheme.Modules.restrictUnitIso f).hom) V from ⟨m,rfl⟩)
    change (show Γ(X,f ''ᵁ V) from φ.app (f ''ᵁ V) m) ∈
      (imageIdeal ((Scheme.Modules.restrictFunctor f).map φ ≫
        (Scheme.Modules.restrictUnitIso f).hom) V).map (f.appIso V).inv.hom
    erw [(f.appIso V).hom_inv_id_apply] at h
    exact h

theorem map_imageIdeal_affine_image {Y : Scheme.{0}} [IsAffine Y]
    [M.IsQuasicoherent] (f : Y ⟶ X) [IsOpenImmersion f]
    (φ : M ⟶ structureSheaf X) (r : Γ(Y,⊤)) :
    (imageIdeal φ (f ''ᵁ ⊤)).map
      (X.presheaf.map (f.opensFunctor.map (homOfLE (Y.basicOpen_le r))).op).hom =
      imageIdeal φ (f ''ᵁ Y.basicOpen r) := by
  let ψ : M.restrict f ⟶ structureSheaf Y :=
    (Scheme.Modules.restrictFunctor f).map φ ≫ (Scheme.Modules.restrictUnitIso f).hom
  rw [← imageIdeal_restrict f φ ⊤, Ideal.map_map]
  have hn := congrArg CommRingCat.Hom.hom
    (f.appIso_inv_naturality (homOfLE (Y.basicOpen_le r)).op)
  change (f.appIso (Y.basicOpen r)).inv.hom.comp
      (Y.presheaf.map (homOfLE (Y.basicOpen_le r)).op).hom =
    (X.presheaf.map (f.opensFunctor.map (homOfLE (Y.basicOpen_le r))).op).hom.comp
      (f.appIso ⊤).inv.hom at hn
  rw [← hn, ← Ideal.map_map]
  rw [affine_map_imageIdeal ψ r, imageIdeal_restrict]

theorem map_imageIdeal_basicOpen [M.IsQuasicoherent]
    (φ : M ⟶ structureSheaf X) (U : X.affineOpens) (r : Γ(X,U.1)) :
    (imageIdeal φ U.1).map (X.presheaf.map (homOfLE (X.basicOpen_le r)).op).hom =
      imageIdeal φ (X.basicOpen r) := by
  let : IsAffine U.1.toScheme := U.2
  have h (V W : X.Opens) (hV : U.1.ι ''ᵁ (⊤ : U.1.toScheme.Opens) = V)
      (hW : U.1.ι ''ᵁ U.1.toScheme.basicOpen (U.1.topIso.inv r) = W) (hWV : W ≤ V) :
      (imageIdeal φ V).map (X.presheaf.map (homOfLE hWV).op).hom = imageIdeal φ W := by
    subst V
    subst W
    exact map_imageIdeal_affine_image U.1.ι φ (U.1.topIso.inv r)
  exact h U.1 (X.basicOpen r) U.1.ι_image_top (U.1.ι_image_basicOpen_topIso_inv r)
    (X.basicOpen_le r)

def imageIdealSheaf [M.IsQuasicoherent] (φ : M ⟶ structureSheaf X) : X.IdealSheafData where
  ideal U := imageIdeal φ U.1
  map_ideal_basicOpen U r := map_imageIdeal_basicOpen φ U r

@[simp] theorem imageIdealSheaf_ideal [M.IsQuasicoherent]
    (φ : M ⟶ structureSheaf X) (U : X.affineOpens) :
    (imageIdealSheaf φ).ideal U = imageIdeal φ U.1 := rfl

theorem imageIdeal_top_of_frame (φ : M ⟶ structureSheaf X)
    (e : M ≅ structureSheaf X) :
    imageIdeal φ ⊤ = Ideal.span {PiExponentSeshadri.Frames.endValue (e.inv ≫ φ)} := by
  apply le_antisymm
  · rintro x ⟨m,rfl⟩
    change Γ(M,⊤) at m
    apply Ideal.mem_span_singleton.mpr
    refine ⟨e.hom.app ⊤ m, ?_⟩
    have he : (e.inv ≫ φ).app ⊤ (e.hom.app ⊤ m) = φ.app ⊤ m := by
      change (e.hom ≫ e.inv ≫ φ).app ⊤ m = _
      rw [e.hom_inv_id_assoc]
    exact he.symm.trans ((PiExponentSeshadri.Frames.end_apply (e.inv ≫ φ) ⊤
      (e.hom.app ⊤ m)).trans (mul_comm (show Γ(X,⊤) from e.hom.app ⊤ m)
        (PiExponentSeshadri.Frames.endValue (e.inv ≫ φ))))
  · apply Ideal.span_le.mpr
    rintro x (rfl : x = _)
    exact ⟨e.inv.app ⊤ (1 : Γ(X,⊤)), rfl⟩

lemma imageIdeal_map_eq (φ : M ⟶ structureSheaf X) {U V : X.Opens} (h : U = V) :
    (imageIdeal φ U).map (X.presheaf.map (eqToHom h.symm).op).hom = imageIdeal φ V := by
  subst V
  change (imageIdeal φ U).map (X.presheaf.map (𝟙 (op U))).hom = imageIdeal φ U
  rw [X.presheaf.map_id]
  exact Ideal.map_id _

theorem imageIdealSheaf_on_frame [M.IsQuasicoherent]
    (φ : M ⟶ structureSheaf X) (U : X.affineOpens)
    (e : M.restrict U.1.ι ≅ structureSheaf U.1.toScheme) :
    (imageIdealSheaf φ).ideal U = Ideal.span
      {U.1.topIso.hom (PiExponentSeshadri.Frames.endValue
        (e.inv ≫ (Scheme.Modules.restrictFunctor U.1.ι).map φ ≫
          (Scheme.Modules.restrictUnitIso U.1.ι).hom))} := by
  let ψ := (Scheme.Modules.restrictFunctor U.1.ι).map φ ≫
    (Scheme.Modules.restrictUnitIso U.1.ι).hom
  have h : (imageIdeal ψ ⊤).map U.1.topIso.hom.hom = imageIdeal φ U.1 := by
    have hi := congrArg (fun J : Ideal Γ(X,U.1.ι ''ᵁ ⊤) =>
      J.map (X.presheaf.map (eqToHom U.1.ι_image_top.symm).op).hom)
      (imageIdeal_restrict U.1.ι φ ⊤)
    rw [imageIdeal_map_eq φ U.1.ι_image_top] at hi
    rw [Ideal.map_map] at hi
    convert hi using 1
    congr 1
    ext a
    simp only [Scheme.Opens.topIso_hom, Scheme.Opens.ι_appIso, Iso.refl_inv, RingHom.comp_apply]
    rfl
  rw [imageIdeal_top_of_frame ψ e, Ideal.map_span, Set.image_singleton] at h
  exact h.symm

end
end PiExponent.SectionImageIdeal

end OAI
end Source0080

section Source0081
/-
Modification notice for the LogTwo project.
Derived from openai/math (Apache-2.0), revision adc7f1241b42e322a6451854ab7e4b4c146bf78a.
Original source: lean/OAI/NumberTheory/PiExponent/LocalAlgebra/SectionZeroIdeal.lean
Changes: Convert module/import declarations to the Lean 4.34 public module format.
See ../../../../../THIRD_PARTY_NOTICES.txt for provenance and the recorded changes.
-/




namespace OAI

namespace PiExponent.SectionZeroIdeal
noncomputable section
open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite
open PiExponentSeshadri.Geometry PiExponentSeshadri.Frames
open PiExponent.SectionImageIdeal PiExponent.InverseFrames
variable {X : Scheme.{0}}

def zeroIdeal (L : LineBundle X) (s : GlobalSections X L.sheaf) : X.IdealSheafData := by
  letI := PiExponent.GeometrySupport.LineBundleCoherent.lineBundle_isFinitePresentation L.inverse
  letI : L.inverse.sheaf.IsQuasicoherent :=
    (SheafOfModules.IsFinitePresentation.exists_quasicoherentData L.inverse.sheaf).choose.isQuasicoherent
  exact imageIdealSheaf (L.dualSection s)

theorem zeroIdeal_on_frame (L : LineBundle X) (s : GlobalSections X L.sheaf)
    (U : X.affineOpens) (e : L.sheaf.restrict U.1.ι ≅ structureSheaf U.1.toScheme) :
    (zeroIdeal L s).ideal U =
      Ideal.span {U.1.topIso.hom (coefficient e (restrictSection U.1.ι s))} := by
  let := PiExponent.GeometrySupport.LineBundleCoherent.lineBundle_isFinitePresentation L.inverse
  let : L.inverse.sheaf.IsQuasicoherent :=
    (SheafOfModules.IsFinitePresentation.exists_quasicoherentData L.inverse.sheaf).choose.isQuasicoherent
  change (imageIdealSheaf (L.dualSection s)).ideal U = _
  rw [imageIdealSheaf_on_frame (L.dualSection s) U
    (inverseOpenFrame (lineTensorInverseIso L) U.1 e), dualSection_restrict_coefficient]

theorem zeroIdeal_ne_bot [IsIntegral X] (L : LineBundle X)
    (s : GlobalSections X L.sheaf) (hs : s ≠ 0) : zeroIdeal L s ≠ ⊥ := by
  obtain ⟨x⟩ : Nonempty X := inferInstance
  obtain ⟨V,hxV,⟨eV⟩⟩ := L.locallyRankOne x
  obtain ⟨U,hU,hxU,hUV⟩ := exists_isAffineOpen_mem_and_subset hxV
  let e := restrictOpenFrame hUV eV
  let : Nonempty U := ⟨⟨x,hxU⟩⟩
  intro h
  have hi := zeroIdeal_on_frame L s ⟨U,hU⟩ e
  rw [h] at hi
  have hz : U.topIso.hom (coefficient e (restrictSection U.ι s)) = 0 := by
    have hm := Ideal.subset_span (Set.mem_singleton
      (U.topIso.hom (coefficient e (restrictSection U.ι s))))
    rw [← hi] at hm
    exact hm
  have hc : coefficient e (restrictSection U.ι s) = 0 := by
    exact (map_eq_zero_iff _ (ConcreteCategory.bijective_of_isIso U.topIso.hom).injective).mp hz
  apply hs
  apply L.restricted_coefficient_injective U.ι e
  exact hc.trans ((congrArg (coefficient e) (restrictSection_zero U.ι)).trans
    (coefficient_zero e)).symm

theorem zeroIdeal_not_surjective [IsIntegral X] (L : LineBundle X)
    (s : GlobalSections X L.sheaf) (hs : s ≠ 0) :
    ¬ Function.Surjective (zeroIdeal L s).subschemeι := by
  intro h
  apply zeroIdeal_ne_bot L s hs
  apply Scheme.IdealSheafData.support_eq_top_iff.mp
  apply TopologicalSpace.Closeds.ext
  rw [← Scheme.IdealSheafData.range_subschemeι]
  exact Set.range_eq_univ.mpr h

end
end PiExponent.SectionZeroIdeal

end OAI
end Source0081

section Source0082
/-
Modification notice for the LogTwo project.
Derived from openai/math (Apache-2.0), revision adc7f1241b42e322a6451854ab7e4b4c146bf78a.
Original source: lean/OAI/NumberTheory/PiExponent/Geometry/CurveDegreeAdditivity.lean
Changes: Convert module/import declarations to the Lean 4.34 public module format.
See ../../../../../THIRD_PARTY_NOTICES.txt for provenance and the recorded changes.
-/




namespace OAI

namespace PiExponent.CurveDegree
noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace
open PiExponentSeshadri.Geometry PiExponentSeshadri.Frames
open PiExponent.SectionZeroIdeal PiExponent.CartierPowerFrames
variable {X : Scheme.{0}}

def FiniteLineCohomology (p : X ⟶ Spec (CommRingCat.of ℂ)) : Prop :=
  ∀ L : LineBundle X, ∀ n ≤ 1,
    let := Module.compHom (cohomology L.sheaf n) (baseScalars p)
    FiniteDimensional ℂ (cohomology L.sheaf n)

def LineCohomologyTwoZero (X : Scheme.{0}) : Prop :=
  ∀ L : LineBundle X, Subsingleton (cohomology L.sheaf 2)

theorem section_tensor_euler_add [IsIntegral X]
    (p : X ⟶ Spec (CommRingCat.of ℂ)) [IsProper p]
    (hd : topologicalKrullDim X ≤ 1)
    (hfinite : FiniteLineCohomology p) (hH2 : LineCohomologyTwoZero X)
    (L M : LineBundle X) (s : GlobalSections X L.sheaf) (hs : s ≠ 0) :
    eulerCharacteristic p 1 (L.tensor M).sheaf - eulerCharacteristic p 1 M.sheaf =
      eulerCharacteristic p 1 L.sheaf - eulerCharacteristic p 1 (structureSheaf X) := by
  let hsMono : Mono s := L.mono_section s hs
  let I := zeroIdeal L s
  have hI : I ≠ ⊥ := zeroIdeal_ne_bot L s hs
  let φ := sectionMultiplyLeft L.sheaf M.sheaf s
  let : Mono (moduleTensorMap s (𝟙 M.sheaf)) := moduleTensorMap_mono s M
  let hφMono : Mono φ := mono_comp _ _
  have heqTensor : ∀ x : X, ∃ U : X.affineOpens, x ∈ U.1 ∧
      ∃ f : M.sheaf.restrict U.1.ι ≅ O U.1.toScheme,
      ∃ e : (L.tensor M).sheaf.restrict U.1.ι ≅ O U.1.toScheme,
        I.ideal U = Ideal.span (Set.singleton (U.1.topIso.hom
          (endValue (f.inv ≫ (Scheme.Modules.restrictFunctor U.1.ι).map φ ≫ e.hom)))) := by
    intro x
    obtain ⟨U, hx, ⟨e⟩, ⟨f⟩⟩ := common_affine_frames L M x
    refine ⟨U, hx, f, tensorFrame L.sheaf M.sheaf U.1 e f, ?_⟩
    exact (zeroIdeal_on_frame L s U e).trans
      (tensor_multiply_ideal L.sheaf M.sheaf s U e f).symm
  have heqSection : ∀ x : X, ∃ U : X.affineOpens, x ∈ U.1 ∧
      ∃ f : (L.pow 0).sheaf.restrict U.1.ι ≅ O U.1.toScheme,
      ∃ e : L.sheaf.restrict U.1.ι ≅ O U.1.toScheme,
        I.ideal U = Ideal.span (Set.singleton (U.1.topIso.hom
          (endValue (f.inv ≫ (Scheme.Modules.restrictFunctor U.1.ι).map s ≫ e.hom)))) := by
    intro x
    obtain ⟨U, hx, ⟨e⟩, ⟨f⟩⟩ := common_affine_frames L M x
    refine ⟨U, hx, Scheme.Modules.restrictUnitIso U.1.ι, e, ?_⟩
    simpa only [coefficient, restrictSection, Category.assoc] using! zeroIdeal_on_frame L s U e
  let : Subsingleton (cohomology M.sheaf 2) := hH2 M
  let : Subsingleton (cohomology (L.pow 0).sheaf 2) := hH2 (L.pow 0)
  have hTensor := @CartierDegreeLength.cartier_euler_difference_eq_sum_local_lengths
    X inferInstance p inferInstance hd M (L.tensor M) φ hφMono I hI heqTensor (hfinite M) (hfinite (L.tensor M))
  have hSection := @CartierDegreeLength.cartier_euler_difference_eq_sum_local_lengths
    X inferInstance p inferInstance hd (L.pow 0) L s hsMono I hI heqSection (hfinite (L.pow 0)) (hfinite L)
  exact hTensor.trans hSection.symm

theorem tensor_euler_add [IsIntegral X]
    (p : X ⟶ Spec (CommRingCat.of ℂ)) [IsProper p]
    (hd : topologicalKrullDim X ≤ 1) (H : LineBundle X) (hH : H.IsAmple)
    (hfinite : FiniteLineCohomology p) (hH2 : LineCohomologyTwoZero X)
    (L M : LineBundle X) :
    eulerCharacteristic p 1 (L.tensor M).sheaf - eulerCharacteristic p 1 M.sheaf =
      eulerCharacteristic p 1 L.sheaf - eulerCharacteristic p 1 (structureSheaf X) := by
  let : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian p
  let : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace p
  let : IsNoetherian X := ⟨⟩
  obtain ⟨A, ⟨t, ht⟩, ⟨u, hu⟩⟩ := exists_effective_twist H hH L
  have h₀ := section_tensor_euler_add p hd hfinite hH2 A L t ht
  have h₁ := section_tensor_euler_add p hd hfinite hH2 (A.tensor L) M u hu
  have h₂ := section_tensor_euler_add p hd hfinite hH2 A (L.tensor M) t ht
  have he := eulerCharacteristic_iso p (lineTensorAssoc A L M) 1
  change eulerCharacteristic p 1 ((A.tensor L).tensor M).sheaf =
    eulerCharacteristic p 1 (A.tensor (L.tensor M)).sheaf at he
  omega

theorem power_euler [IsIntegral X]
    (p : X ⟶ Spec (CommRingCat.of ℂ)) [IsProper p]
    (hd : topologicalKrullDim X ≤ 1) (H : LineBundle X) (hH : H.IsAmple)
    (hfinite : FiniteLineCohomology p) (hH2 : LineCohomologyTwoZero X)
    (L : LineBundle X) (n : ℕ) :
    eulerCharacteristic p 1 (L.pow n).sheaf - eulerCharacteristic p 1 (structureSheaf X) =
      (n : ℤ) * (eulerCharacteristic p 1 L.sheaf - eulerCharacteristic p 1 (structureSheaf X)) := by
  induction n with
  | zero => simp [LineBundle.pow, modulePow, structureSheaf]
  | succ n ih =>
    have he := tensor_euler_add p hd H hH hfinite hH2 L (L.pow n)
    change eulerCharacteristic p 1 (L.pow (n+1)).sheaf -
      eulerCharacteristic p 1 (L.pow n).sheaf = _ at he
    push_cast
    nlinarith

theorem inverse_euler [IsIntegral X]
    (p : X ⟶ Spec (CommRingCat.of ℂ)) [IsProper p]
    (hd : topologicalKrullDim X ≤ 1) (H : LineBundle X) (hH : H.IsAmple)
    (hfinite : FiniteLineCohomology p) (hH2 : LineCohomologyTwoZero X)
    (L : LineBundle X) :
    eulerCharacteristic p 1 L.inverse.sheaf - eulerCharacteristic p 1 (structureSheaf X) =
      -(eulerCharacteristic p 1 L.sheaf - eulerCharacteristic p 1 (structureSheaf X)) := by
  have h := tensor_euler_add p hd H hH hfinite hH2 L L.inverse
  have he := eulerCharacteristic_iso p (lineTensorInverseIso L) 1
  change eulerCharacteristic p 1 (L.tensor L.inverse).sheaf =
    eulerCharacteristic p 1 (structureSheaf X) at he
  omega

end
end PiExponent.CurveDegree

namespace PiExponent.NumericalAmpleness
noncomputable section
open AlgebraicGeometry CategoryTheory TopologicalSpace
open PiExponentSeshadri.Geometry
variable {X : Scheme.{0}}

theorem curveDegree_tensor (p : X ⟶ Spec (CommRingCat.of ℂ)) [IsProper p]
    (H : LineBundle X) (hH : H.IsAmple) (L M : LineBundle X) (C : IntegralCurve X)
    (hfinite : CurveDegree.FiniteLineCohomology (C.embedding ≫ p))
    (hH2 : CurveDegree.LineCohomologyTwoZero C.scheme) :
    curveDegree p (L.tensor M) C = curveDegree p L C + curveDegree p M C := by
  have he := CurveDegree.tensor_euler_add (C.embedding ≫ p) C.dimension.le
    (H.pullback C.embedding) (LineBundle.IsAmple.pullback_closedImmersion H hH C.embedding)
    hfinite hH2 (L.pullback C.embedding) (M.pullback C.embedding)
  have hi := eulerCharacteristic_iso (C.embedding ≫ p)
    (PiExponentSeshadri.PullbackTensor.iso C.embedding L M) 1
  unfold curveDegree
  rw [hi]
  change _ - _ = (_ - _) + (_ - _)
  dsimp only [LineBundle.pullback, LineBundle.tensor] at he ⊢
  omega

theorem curveDegree_pow (p : X ⟶ Spec (CommRingCat.of ℂ)) [IsProper p]
    (H : LineBundle X) (hH : H.IsAmple) (L : LineBundle X) (C : IntegralCurve X)
    (hfinite : CurveDegree.FiniteLineCohomology (C.embedding ≫ p))
    (hH2 : CurveDegree.LineCohomologyTwoZero C.scheme) (n : ℕ) :
    curveDegree p (L.pow n) C = (n : ℤ) * curveDegree p L C := by
  have hi := eulerCharacteristic_iso (C.embedding ≫ p)
    (PiExponentSeshadri.PullbackTensor.powIso C.embedding L n) 1
  unfold curveDegree
  rw [hi]
  exact CurveDegree.power_euler (C.embedding ≫ p) C.dimension.le
    (H.pullback C.embedding) (LineBundle.IsAmple.pullback_closedImmersion H hH C.embedding)
    hfinite hH2 (L.pullback C.embedding) n

theorem curveDegree_iso (p : X ⟶ Spec (CommRingCat.of ℂ))
    (L M : LineBundle X) (C : IntegralCurve X) (e : L.sheaf ≅ M.sheaf) :
    curveDegree p L C = curveDegree p M C := by
  unfold curveDegree
  rw [eulerCharacteristic_iso (C.embedding ≫ p)
    ((Scheme.Modules.pullback C.embedding).mapIso e) 1]

theorem curveDegree_inverse (p : X ⟶ Spec (CommRingCat.of ℂ)) [IsProper p]
    (H : LineBundle X) (hH : H.IsAmple) (L : LineBundle X) (C : IntegralCurve X)
    (hfinite : CurveDegree.FiniteLineCohomology (C.embedding ≫ p))
    (hH2 : CurveDegree.LineCohomologyTwoZero C.scheme) :
    curveDegree p L.inverse C = -curveDegree p L C := by
  have h := curveDegree_tensor p H hH L L.inverse C hfinite hH2
  have hi := eulerCharacteristic_iso (C.embedding ≫ p)
    (((Scheme.Modules.pullback C.embedding).mapIso (lineTensorInverseIso L)) ≪≫
      PiExponentSeshadri.Geometry.pullbackUnitIso C.embedding) 1
  change eulerCharacteristic (C.embedding ≫ p) 1
    ((Scheme.Modules.pullback C.embedding).obj (L.tensor L.inverse).sheaf) =
      eulerCharacteristic (C.embedding ≫ p) 1 (structureSheaf C.scheme) at hi
  have hz : curveDegree p (L.tensor L.inverse) C = 0 := by
    unfold curveDegree
    rw [hi]
    exact sub_self _
  omega

theorem curveDegree_eq_rat_of_power_iso
    (p : X ⟶ Spec (CommRingCat.of ℂ)) [IsProper p]
    (H : LineBundle X) (hH : H.IsAmple) (L A B : LineBundle X) (C : IntegralCurve X)
    (hfinite : CurveDegree.FiniteLineCohomology (C.embedding ≫ p))
    (hH2 : CurveDegree.LineCohomologyTwoZero C.scheme)
    (n a b : ℕ) (hn : 0 < n)
    (e : (L.pow n).sheaf ≅ ((A.pow a).tensor (B.inverse.pow b)).sheaf) :
    (curveDegree p L C : ℚ) =
      ((a : ℚ) / n) * (curveDegree p A C : ℚ) -
        ((b : ℚ) / n) * (curveDegree p B C : ℚ) := by
  have hd := curveDegree_iso p (L.pow n) ((A.pow a).tensor (B.inverse.pow b)) C e
  rw [curveDegree_pow p H hH L C hfinite hH2 n,
    curveDegree_tensor p H hH (A.pow a) (B.inverse.pow b) C hfinite hH2,
    curveDegree_pow p H hH A C hfinite hH2 a,
    curveDegree_pow p H hH B.inverse C hfinite hH2 b,
    curveDegree_inverse p H hH B C hfinite hH2] at hd
  have hq := congrArg (fun z : ℤ => (z : ℚ)) hd
  push_cast at hq
  have hnq : (n : ℚ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hn)
  calc
    (curveDegree p L C : ℚ) =
        ((a : ℚ) * (curveDegree p A C : ℚ) - (b : ℚ) * (curveDegree p B C : ℚ)) / n :=
      (eq_div_iff hnq).mpr (by nlinarith [hq])
    _ = _ := by ring

end
end PiExponent.NumericalAmpleness

end OAI
end Source0082

section Source0083
/-
Modification notice for the LogTwo project.
Derived from openai/math (Apache-2.0), revision adc7f1241b42e322a6451854ab7e4b4c146bf78a.
Original source: lean/OAI/NumberTheory/PiExponent/Geometry/SectionZeroStalk.lean
Changes: Convert module/import declarations to the Lean 4.34 public module format.
See ../../../../../THIRD_PARTY_NOTICES.txt for provenance and the recorded changes.
-/




namespace OAI

noncomputable section
open CategoryTheory AlgebraicGeometry TopologicalSpace
open PiExponentSeshadri.Geometry PiExponentSeshadri.Frames

namespace PiExponent.SectionZeroStalk


theorem stalkMap_ker_eq_map_affine_ker
    {X Y : Scheme} (f : Y ⟶ X) [IsClosedImmersion f]
    (U : X.Opens) (hU : IsAffineOpen U) (y : Y) (hy : f y ∈ U) :
    RingHom.ker (f.stalkMap y).hom =
      (RingHom.ker (f.app U).hom).map (X.presheaf.germ U (f y) hy).hom := by
  let V := f ⁻¹ᵁ U
  have hV : IsAffineOpen V := hU.preimage f
  let q := hU.primeIdealOf ⟨f y, hy⟩
  let p := hV.primeIdealOf ⟨y, hy⟩
  let φ := (f.app U).hom
  let := X.presheaf.algebra_section_stalk ⟨f y, hy⟩
  let := Y.presheaf.algebra_section_stalk (⟨y, hy⟩ : V)
  let := hU.isLocalization_stalk ⟨f y, hy⟩
  let := hV.isLocalization_stalk ⟨y, hy⟩
  have hqp : p.asIdeal.comap φ = q.asIdeal := by
    have h := IsAffineOpen.comap_primeIdealOf_appLE U hU V hV le_rfl hy (f := f)
    simpa only [V, Scheme.Hom.appLE_eq_app, PrimeSpectrum.comap_asIdeal, φ, p, q] using congrArg PrimeSpectrum.asIdeal h
  have hmon : q.asIdeal.primeCompl.map φ = p.asIdeal.primeCompl := by
    simpa only [hqp] using p.asIdeal.map_primeCompl_comap_of_surjective φ (f.app_surjective U hU)
  have hf : (f.stalkMap y).hom =
      (IsLocalization.map (Y.presheaf.stalk y) φ
        (hmon.symm ▸ q.asIdeal.primeCompl.le_comap_map) : X.presheaf.stalk (f y) →+* Y.presheaf.stalk y) := by
    apply IsLocalization.ringHom_ext q.asIdeal.primeCompl
    ext a
    rw [RingHom.comp_apply, RingHom.comp_apply, IsLocalization.map_eq]
    exact Scheme.Hom.germ_stalkMap_apply f U y hy a
  rw [hf, IsLocalization.ker_map (Y.presheaf.stalk y) φ hmon]
  rfl

variable {X : Scheme.{0}}

theorem zero_stalk_kernel (L : LineBundle X) (s : GlobalSections X L.sheaf)
    (U : X.affineOpens) (e : L.sheaf.restrict U.1.ι ≅ O U.1.toScheme)
    (y : (SectionZeroIdeal.zeroIdeal L s).subscheme)
    (hy : (SectionZeroIdeal.zeroIdeal L s).subschemeι y ∈ U.1) :
    RingHom.ker ((SectionZeroIdeal.zeroIdeal L s).subschemeι.stalkMap y).hom =
      Ideal.span (Set.singleton ((X.presheaf.germ U.1 _ hy)
        (U.1.topIso.hom (coefficient e (restrictSection U.1.ι s))))) := by
  rw [stalkMap_ker_eq_map_affine_ker _ U.1 U.2 y hy,
    (SectionZeroIdeal.zeroIdeal L s).ker_subschemeι_app U,
    SectionZeroIdeal.zeroIdeal_on_frame L s U e,
    Ideal.map_span, Set.image_singleton]

def sectionGerm (L : LineBundle X) (s : GlobalSections X L.sheaf)
    (U : X.affineOpens) (e : L.sheaf.restrict U.1.ι ≅ O U.1.toScheme)
    (x : X) (hx : x ∈ U.1) : X.presheaf.stalk x :=
  (X.presheaf.germ U.1 x hx) (U.1.topIso.hom (coefficient e (restrictSection U.1.ι s)))

def zeroStalkQuotientEquiv (L : LineBundle X) (s : GlobalSections X L.sheaf)
    (U : X.affineOpens) (e : L.sheaf.restrict U.1.ι ≅ O U.1.toScheme)
    (y : (SectionZeroIdeal.zeroIdeal L s).subscheme)
    (hy : (SectionZeroIdeal.zeroIdeal L s).subschemeι y ∈ U.1) :
    (X.presheaf.stalk ((SectionZeroIdeal.zeroIdeal L s).subschemeι y) ⧸
      Ideal.span {sectionGerm L s U e _ hy}) ≃+*
      (SectionZeroIdeal.zeroIdeal L s).subscheme.presheaf.stalk y :=
  (Ideal.quotEquivOfEq (zero_stalk_kernel L s U e y hy).symm).trans
    (RingHom.quotientKerEquivOfSurjective
      ((SectionZeroIdeal.zeroIdeal L s).subschemeι.stalkMap_surjective y))

theorem intrinsic_length_eq_of_ringEquiv {A B : Type*} [CommRing A] [CommRing B]
    (e : A ≃+* B) : Module.length A A = Module.length B B := by
  apply WithBot.coe_injective
  rw [Module.coe_length, Module.coe_length]
  exact Order.krullDim_eq_of_orderIso e.idealComapOrderIso.symm

theorem sectionGerm_ne_zero [IsIntegral X]
    (L : LineBundle X) (s : GlobalSections X L.sheaf) (hs : s ≠ 0)
    (U : X.affineOpens) (e : L.sheaf.restrict U.1.ι ≅ O U.1.toScheme)
    (x : X) (hx : x ∈ U.1) : sectionGerm L s U e x hx ≠ 0 := by
  let : Nonempty U.1.toScheme := ⟨⟨x,hx⟩⟩
  intro h
  have hg : U.1.topIso.hom (coefficient e (restrictSection U.1.ι s)) = 0 :=
    (map_eq_zero_iff _ (germ_injective_of_isIntegral X x hx)).mp h
  have hc : coefficient e (restrictSection U.1.ι s) = 0 :=
    (map_eq_zero_iff _ (ConcreteCategory.bijective_of_isIso U.1.topIso.hom).injective).mp hg
  apply hs
  apply L.restricted_coefficient_injective U.1.ι e
  exact hc.trans ((congrArg (coefficient e)
    (restrictSection_zero (M := L.sheaf) U.1.ι)).trans (coefficient_zero e)).symm

theorem zero_stalk_length_eq_order [IsIntegral X]
    (L : LineBundle X) (s : GlobalSections X L.sheaf) (hs : s ≠ 0)
    (U : X.affineOpens) (e : L.sheaf.restrict U.1.ι ≅ O U.1.toScheme)
    (y : (SectionZeroIdeal.zeroIdeal L s).subscheme)
    (hy : (SectionZeroIdeal.zeroIdeal L s).subschemeι y ∈ U.1)
    [IsDiscreteValuationRing (X.presheaf.stalk ((SectionZeroIdeal.zeroIdeal L s).subschemeι y))] :
    Module.length ((SectionZeroIdeal.zeroIdeal L s).subscheme.presheaf.stalk y)
      ((SectionZeroIdeal.zeroIdeal L s).subscheme.presheaf.stalk y) =
      IsDiscreteValuationRing.addVal
        (X.presheaf.stalk ((SectionZeroIdeal.zeroIdeal L s).subschemeι y))
        (sectionGerm L s U e _ hy) := by
  let A := X.presheaf.stalk ((SectionZeroIdeal.zeroIdeal L s).subschemeι y)
  let c : A := sectionGerm L s U e _ hy
  have hlen := intrinsic_length_eq_of_ringEquiv (zeroStalkQuotientEquiv L s U e y hy)
  have hsc : Module.length A (A ⧸ Ideal.span {c}) =
      Module.length (A ⧸ Ideal.span {c}) (A ⧸ Ideal.span {c}) :=
    Module.length_eq_of_surjective (M := A ⧸ Ideal.span {c}) Ideal.Quotient.mk_surjective
  exact hlen.symm.trans (hsc.symm.trans
    (CurveLocalOrder.length_quotient_span_eq_addVal (sectionGerm_ne_zero L s hs U e _ hy)))

end PiExponent.SectionZeroStalk

end

end OAI
end Source0083

section Source0084
/-
Modification notice for the LogTwo project.
Derived from openai/math (Apache-2.0), revision adc7f1241b42e322a6451854ab7e4b4c146bf78a.
Original source: lean/OAI/NumberTheory/PiExponent/Geometry/CurveSectionDegree.lean
Changes: Convert module/import declarations to the Lean 4.34 public module format.
See ../../../../../THIRD_PARTY_NOTICES.txt for provenance and the recorded changes.
-/




namespace OAI

noncomputable section
open CategoryTheory AlgebraicGeometry TopologicalSpace
open PiExponentSeshadri.Geometry PiExponentSeshadri.Frames

namespace PiExponent.CurveSectionDegree


variable {X : Scheme.{0}}

structure AffineFrameAt (L : LineBundle X) (x : X) where
  openSet : X.affineOpens
  mem : x ∈ openSet.1
  frame : L.sheaf.restrict openSet.1.ι ≅ O openSet.1.toScheme

 theorem nonempty_affineFrameAt (L : LineBundle X) (x : X) : Nonempty (AffineFrameAt L x) := by
  obtain ⟨V, hxV, ⟨eV⟩⟩ := L.locallyRankOne x
  obtain ⟨U, hU, hxU, hUV⟩ := exists_isAffineOpen_mem_and_subset hxV
  exact ⟨⟨⟨U,hU⟩, hxU, restrictOpenFrame hUV eV⟩⟩

def affineFrameAt (L : LineBundle X) (x : X) : AffineFrameAt L x :=
  Classical.choice (nonempty_affineFrameAt L x)

def coefficientGermAt (L : LineBundle X) (s : GlobalSections X L.sheaf) (x : X) :
    X.presheaf.stalk x :=
  SectionZeroStalk.sectionGerm L s (affineFrameAt L x).openSet
    (affineFrameAt L x).frame x (affineFrameAt L x).mem

theorem zeroPoint_ne_generic [IsIntegral X]
    (L : LineBundle X) (s : GlobalSections X L.sheaf) (hs : s ≠ 0)
    (y : (SectionZeroIdeal.zeroIdeal L s).subscheme) :
    (SectionZeroIdeal.zeroIdeal L s).subschemeι y ≠ genericPoint X := by
  let I := SectionZeroIdeal.zeroIdeal L s
  intro hy
  have hg : genericPoint X ∈ (I.support : Set X) := by
    rw [← I.range_subschemeι]
    exact ⟨y,hy⟩
  have htop : (Set.univ : Set X) ⊆ I.support := by
    rw [← genericPoint_spec X]
    exact closure_minimal (Set.singleton_subset_iff.mpr hg) I.support.isClosed
  apply SectionZeroIdeal.zeroIdeal_ne_bot L s hs
  apply Scheme.IdealSheafData.support_eq_top_iff.mp
  exact TopologicalSpace.Closeds.ext (Set.Subset.antisymm (Set.subset_univ _) htop)

theorem euler_difference_eq_sum_zero_orders [IsIntegral X]
    (p : X ⟶ Spec (CommRingCat.of ℂ)) [IsProper p]
    (hd : topologicalKrullDim X ≤ 1)
    (L : LineBundle X) (s : GlobalSections X L.sheaf) (hs : s ≠ 0)
    (hDVR : ∀ x : X, x ≠ genericPoint X → IsDiscreteValuationRing (X.presheaf.stalk x))
    (hfiniteO : ∀ n ≤ 1, letI := Module.compHom (cohomology (structureSheaf X) n) (baseScalars p)
      FiniteDimensional ℂ (cohomology (structureSheaf X) n))
    (hfiniteL : ∀ n ≤ 1, letI := Module.compHom (cohomology L.sheaf n) (baseScalars p)
      FiniteDimensional ℂ (cohomology L.sheaf n))
    [Subsingleton (cohomology (structureSheaf X) 2)] :
    letI : Finite (SectionZeroIdeal.zeroIdeal L s).subscheme :=
      finite_subscheme_of_curve p hd _ (SectionZeroIdeal.zeroIdeal_ne_bot L s hs)
    letI : Fintype (SectionZeroIdeal.zeroIdeal L s).subscheme := Fintype.ofFinite _
    eulerCharacteristic p 1 L.sheaf - eulerCharacteristic p 1 (structureSheaf X) =
      ∑ y : (SectionZeroIdeal.zeroIdeal L s).subscheme,
        letI := hDVR _ (zeroPoint_ne_generic L s hs y)
        ((IsDiscreteValuationRing.addVal
          (X.presheaf.stalk ((SectionZeroIdeal.zeroIdeal L s).subschemeι y))
          (coefficientGermAt L s ((SectionZeroIdeal.zeroIdeal L s).subschemeι y))).toNat : ℤ) := by
  let I := SectionZeroIdeal.zeroIdeal L s
  have hI : I ≠ ⊥ := SectionZeroIdeal.zeroIdeal_ne_bot L s hs
  let : Finite I.subscheme := finite_subscheme_of_curve p hd I hI
  let : Fintype I.subscheme := Fintype.ofFinite _
  let : Mono s := L.mono_section s hs
  have heq : ∀ x : X, ∃ U : X.affineOpens, x ∈ U.1 ∧
      ∃ e : (L.pow 0).sheaf.restrict U.1.ι ≅ O U.1.toScheme,
      ∃ d : L.sheaf.restrict U.1.ι ≅ O U.1.toScheme,
        I.ideal U = Ideal.span (Set.singleton (U.1.topIso.hom
          (endValue (e.inv ≫ (Scheme.Modules.restrictFunctor U.1.ι).map s ≫ d.hom)))) := by
    intro x
    let F := affineFrameAt L x
    refine ⟨F.openSet, F.mem, Scheme.Modules.restrictUnitIso F.openSet.1.ι, F.frame, ?_⟩
    have h := SectionZeroIdeal.zeroIdeal_on_frame L s F.openSet F.frame
    simp only [coefficient, restrictSection] at h
    erw [Category.assoc] at h
    exact h
  let : Subsingleton (cohomology (L.pow 0).sheaf 2) := by
    change Subsingleton (cohomology (structureSheaf X) 2)
    infer_instance
  have hh := @CartierDegreeLength.cartier_euler_difference_eq_sum_local_lengths
    X inferInstance p inferInstance hd (L.pow 0) L s (L.mono_section s hs)
    I hI heq hfiniteO hfiniteL inferInstance
  refine hh.trans (Finset.sum_congr rfl fun y _ => ?_)
  let := hDVR _ (zeroPoint_ne_generic L s hs y)
  have h := SectionZeroStalk.zero_stalk_length_eq_order L s hs
    (affineFrameAt L (I.subschemeι y)).openSet
    (affineFrameAt L (I.subschemeι y)).frame y
    (affineFrameAt L (I.subschemeι y)).mem
  exact congrArg (fun n : ℕ∞ => (n.toNat : ℤ)) h

end PiExponent.CurveSectionDegree

end

end OAI
end Source0084

section Source0085
/-
Modification notice for the LogTwo project.
Derived from openai/math (Apache-2.0), revision adc7f1241b42e322a6451854ab7e4b4c146bf78a.
Original source: lean/OAI/NumberTheory/PiExponent/LocalAlgebra/InvertibleIdealLocal.lean
Changes: Convert module/import declarations to the Lean 4.34 public module format.
See ../../../../../THIRD_PARTY_NOTICES.txt for provenance and the recorded changes.
-/




namespace OAI

noncomputable section

namespace PiExponentSeshadri.UnitEndomorphism
open CategoryTheory AlgebraicGeometry Opposite
universe u
variable {X : Scheme.{u}}
abbrev unit (X : Scheme.{u}) : X.Modules := SheafOfModules.unit X.ringCatSheaf
variable (g : unit X ⟶ unit X)

def equation (U : X.Opens) : Γ(X, U) := g.val.app (op U) (1 : Γ(X, U))

lemma app_eq_mul (U : X.Opens) (a : Γ(X, U)) :
    g.val.app (op U) a = equation g U * a := by
  let F : Γ(X, U) →ₗ[Γ(X, U)] Γ(X, U) := (g.val.app (op U)).hom
  have h := F.map_smul a (1 : Γ(X, U))
  simpa only [smul_eq_mul, mul_one, mul_comm a, one_mul, F, equation] using! h

lemma image_principal (U : X.Opens) :
    (show Ideal Γ(X, U) from (g.val.app (op U)).hom.range) = Ideal.span {equation g U} := by
  ext a
  constructor
  · rintro ⟨b, rfl⟩
    exact Ideal.mem_span_singleton.mpr ⟨b, app_eq_mul g U b⟩
  · intro ha
    obtain ⟨b, hb⟩ := Ideal.mem_span_singleton.mp ha
    exact ⟨b, (app_eq_mul g U b).trans hb.symm⟩

lemma equation_regular [Mono g] (U : X.Opens) : IsRegular (equation g U) := by
  let : Mono g.val := inferInstanceAs (Mono ((Scheme.Modules.toPresheafOfModules X).map g))
  have hinj := PresheafOfModules.injective_of_mono g.val (op U)
  apply (Commute.isRegular_iff (fun a => Commute.all _ a)).mpr
  intro a b hab
  apply hinj
  simpa only [app_eq_mul] using! hab

end PiExponentSeshadri.UnitEndomorphism
namespace PiExponentSeshadri.InvertibleLocal

section
open CategoryTheory AlgebraicGeometry Opposite
open PiExponentSeshadri.Geometry
universe u
variable {X Y Z : Scheme} (I : X.IdealSheafData) (f : Y ⟶ X)
variable (J : LineBundle Y) (ι : J.sheaf ⟶ structureSheaf Y)

lemma image_eq_comap [IsAffine X] (h : PresentsPullbackIdeal I f J ι) (U : Y.affineOpens) :
    sectionImageIdeal J ι U.1 = (I.comap f).ideal U := by
  let V : X.affineOpens := ⟨⊤, isAffineOpen_top X⟩
  have e : U.1 ≤ f ⁻¹ᵁ V.1 := by simp [V]
  exact (h.2 U V e).trans (IdealPullback.comap_ideal I f U V e).symm

variable {I f}

private theorem mono_comp_iso {C : Type*} [Category C] {A B D : C}
    (g : A ⟶ B) (e : B ≅ D) [Mono g] : Mono (g ≫ e.hom) := inferInstance

private theorem mono_iso_inv_comp {C : Type*} [Category C] {A B D : C}
    (e : A ≅ B) (g : A ⟶ D) [Mono g] : Mono (e.inv ≫ g) := inferInstance

def restrictedInclusion (j : Z ⟶ Y) [IsOpenImmersion j] :
    J.sheaf.restrict j ⟶ structureSheaf Z :=
  (Scheme.Modules.restrictFunctor j).map ι ≫ (Scheme.Modules.restrictUnitIso j).hom

instance restrictedInclusion_mono (j : Z ⟶ Y) [IsOpenImmersion j] [Mono ι] :
    Mono (restrictedInclusion J ι j) := by
  exact mono_comp_iso ((Scheme.Modules.restrictFunctor j).map ι)
    (Scheme.Modules.restrictUnitIso j)

lemma restricted_image [IsAffine X] (h : PresentsPullbackIdeal I f J ι)
    (j : Z ⟶ Y) [IsOpenImmersion j] (U : Z.affineOpens) :
    ((restrictedInclusion J ι j).val.app (op U.1)).hom.range =
      ((I.comap f).comap j).ideal U := by
  rw [(I.comap f).ideal_comap_of_isOpenImmersion j U]
  ext r
  change Γ(Z, U.1) at r
  change (∃ s, (restrictedInclusion J ι j).val.app (op U.1) s = r) ↔ _
  erw [Ideal.mem_comap, ← image_eq_comap I f J ι h
    ⟨j ''ᵁ U.1, U.2.image_of_isOpenImmersion j⟩]
  change (∃ s, _) ↔ ∃ s, ι.val.app (op (j ''ᵁ U.1)) s = (j.appIso U.1).inv r
  constructor
  · rintro ⟨s, hs⟩
    refine ⟨s, ?_⟩
    change (j.appIso U.1).hom (ι.val.app (op (j ''ᵁ U.1)) s) = r at hs
    rw [← hs]
    exact (congrArg (fun k : Γ(Y, j ''ᵁ U.1) ⟶ Γ(Y, j ''ᵁ U.1) => k (ι.val.app (op (j ''ᵁ U.1)) s))
      (j.appIso U.1).hom_inv_id).symm
  · rintro ⟨s, hs⟩
    refine ⟨s, ?_⟩
    change (j.appIso U.1).hom (ι.val.app (op (j ''ᵁ U.1)) s) = r
    rw [hs]
    exact congrArg (fun k : Γ(Z, U.1) ⟶ Γ(Z, U.1) => k r) (j.appIso U.1).inv_hom_id

lemma local_equation [IsAffine X] (h : PresentsPullbackIdeal I f J ι)
    (j : Z ⟶ Y) [IsOpenImmersion j] [IsAffine Z]
    (e : J.sheaf.restrict j ≅ structureSheaf Z) :
    ∃ r : Γ(Z, ⊤), IsRegular r ∧
      ((I.comap f).comap j).ideal ⟨⊤, isAffineOpen_top Z⟩ = Ideal.span {r} := by
  let : Mono ι := h.1
  let g : UnitEndomorphism.unit Z ⟶ UnitEndomorphism.unit Z :=
    e.inv ≫ restrictedInclusion J ι j
  let : Mono (restrictedInclusion J ι j) := restrictedInclusion_mono J ι j
  have : Mono g := mono_iso_inv_comp e (restrictedInclusion J ι j)
  refine ⟨UnitEndomorphism.equation g ⊤, UnitEndomorphism.equation_regular g ⊤, ?_⟩
  rw [← UnitEndomorphism.image_principal g ⊤, ← restricted_image J ι h j ⟨⊤, isAffineOpen_top Z⟩]
  ext r
  change (∃ s, (restrictedInclusion J ι j).val.app (op ⊤) s = r) ↔
    ∃ s, (restrictedInclusion J ι j).val.app (op ⊤) (e.inv.val.app (op ⊤) s) = r
  constructor
  · rintro ⟨s, hs⟩
    refine ⟨e.hom.val.app (op ⊤) s, ?_⟩
    have ht : e.inv.val.app (op ⊤) (e.hom.val.app (op ⊤) s) = s := by
      exact congrArg (fun k : J.sheaf.restrict j ⟶ J.sheaf.restrict j => k.val.app (op ⊤) s)
        e.hom_inv_id
    rw [ht]; exact hs
  · rintro ⟨s, hs⟩
    exact ⟨e.inv.val.app (op ⊤) s, hs⟩

end

section
open CategoryTheory AlgebraicGeometry
open PiExponentSeshadri.Geometry
variable {X Y : Scheme}

lemma affine_local_equation [IsAffine X] (I : X.IdealSheafData) (f : Y ⟶ X)
    (hf : InvertiblePullbackIdeal I f) (y : Y) :
    ∃ U : Y.affineOpens, y ∈ U.1 ∧ ∃ r : Γ(U.1.toScheme, ⊤), IsRegular r ∧
      ((I.comap f).comap U.1.ι).ideal ⟨⊤, isAffineOpen_top U.1.toScheme⟩ =
        Ideal.span {r} := by
  obtain ⟨J, ι, h⟩ := hf
  obtain ⟨U, hyU, ⟨e⟩⟩ := affine_frame J y
  refine ⟨U, hyU, ?_⟩
  exact local_equation J ι h U.1.ι e

end

open CategoryTheory AlgebraicGeometry
open PiExponentSeshadri.Geometry
variable {X Y Z : Scheme}


def restrictLineBundle (J : LineBundle Y) (j : Z ⟶ Y) [IsOpenImmersion j] : LineBundle Z where
  sheaf := J.sheaf.restrict j
  locallyRankOne z := by
    obtain ⟨U, hzU, ⟨e⟩⟩ := J.locallyRankOne (j z)
    let V := j ⁻¹ᵁ U
    refine ⟨V, hzU, ⟨?_⟩⟩
    let e' := (Scheme.Modules.restrictFunctorComp (j ∣_ U) U.ι).app J.sheaf ≪≫
      (Scheme.Modules.restrictFunctor (j ∣_ U)).mapIso e ≪≫
      Scheme.Modules.restrictUnitIso (j ∣_ U)
    have e'' : J.sheaf.restrict (V.ι ≫ j) ≅ structureSheaf V.toScheme := by
      simp only [morphismRestrict_ι] at e'
      exact e'
    exact ((Scheme.Modules.restrictFunctorComp V.ι j).app J.sheaf).symm ≪≫ e''

lemma presents_restrict [IsAffine X] (I : X.IdealSheafData) (f : Y ⟶ X)
    (J : LineBundle Y) (ι : J.sheaf ⟶ structureSheaf Y)
    (hf : PresentsPullbackIdeal I f J ι) (j : Z ⟶ Y) [IsOpenImmersion j] :
    PresentsPullbackIdeal I (j ≫ f) (restrictLineBundle J j) (restrictedInclusion J ι j) := by
  let : Mono ι := hf.1
  refine ⟨restrictedInclusion_mono J ι j, ?_⟩
  intro U V e
  change ((restrictedInclusion J ι j).val.app (Opposite.op U.1)).hom.range = _
  rw [restricted_image J ι hf j U, ← Scheme.IdealSheafData.comap_comp]
  exact IdealPullback.comap_ideal I (j ≫ f) U V e

lemma invertible_restrict [IsAffine X] (I : X.IdealSheafData) (f : Y ⟶ X)
    (hf : InvertiblePullbackIdeal I f) (j : Z ⟶ Y) [IsOpenImmersion j] :
    InvertiblePullbackIdeal I (j ≫ f) := by
  obtain ⟨J, ι, h⟩ := hf
  exact ⟨restrictLineBundle J j, restrictedInclusion J ι j, presents_restrict I f J ι h j⟩

end PiExponentSeshadri.InvertibleLocal

end

end OAI
end Source0085

section Source0086
/-
Modification notice for the LogTwo project.
Derived from openai/math (Apache-2.0), revision adc7f1241b42e322a6451854ab7e4b4c146bf78a.
Original source: lean/OAI/NumberTheory/PiExponent/LocalAlgebra/TensorIdealInclusion.lean
Changes: Convert module/import declarations to the Lean 4.34 public module format.
See ../../../../../THIRD_PARTY_NOTICES.txt for provenance and the recorded changes.
-/




namespace OAI

namespace PiExponentSeshadri.Geometry
noncomputable section
open AlgebraicGeometry CategoryTheory TopologicalSpace
open PiExponentSeshadri.Frames
variable {X : Scheme.{0}}

def tensorUnitTwist (M : LineBundle X) (U : X.Opens)
    (f : M.sheaf.restrict U.ι ≅ O U.toScheme) : O U.toScheme ≅ O U.toScheme :=
  f.symm ≪≫ (Scheme.Modules.restrictFunctor U.ι).mapIso (moduleTensorUnit M.sheaf).symm ≪≫
    moduleTensorRestrict U (O X) M.sheaf ≪≫
      moduleTensorIso (Scheme.Modules.restrictUnitIso U.ι) f ≪≫ moduleTensorUnit (O U.toScheme)

lemma moduleTensorIso_inv {M N P Q : X.Modules} (e : M ≅ N) (f : P ≅ Q) :
    (moduleTensorIso e f).inv = moduleTensorMap e.inv f.inv := rfl

def tensorInclusion (J M : LineBundle X) (ι : J.sheaf ⟶ O X) :
    (J.tensor M).sheaf ⟶ M.sheaf :=
  moduleTensorMap ι (𝟙 M.sheaf) ≫ (moduleTensorUnit M.sheaf).hom

private lemma frame_square {C : Type*} [Category C]
    {A B A' B' T O : C} (r : A ≅ A') (r' : B ≅ B')
    (e : A' ≅ T) (e' : B' ≅ T) (u : T ≅ O)
    (m : A ⟶ B) (p : A' ⟶ B') (a : O ⟶ O)
    (hn : m ≫ r'.hom = r.hom ≫ p)
    (hs : e.inv ≫ p ≫ e'.hom ≫ u.hom = u.hom ≫ a) :
    (r ≪≫ e ≪≫ u).inv ≫ m ≫ (r' ≪≫ e' ≪≫ u).hom = a := by
  simp only [Iso.trans_inv, Iso.trans_hom, Category.assoc]
  rw [← Category.assoc m r'.hom, hn]
  simp only [Category.assoc, Iso.inv_hom_id_assoc]
  rw [hs]
  simp

private lemma frame_inclusion {C : Type*} [Category C]
    {A B D O : C} (e : A ≅ O) (e' : B ≅ O) (h : B ≅ D) (f : D ≅ O)
    (m : A ⟶ B) (a : O ⟶ O) (ha : e.inv ≫ m ≫ e'.hom = a) :
    e.inv ≫ (m ≫ h.hom) ≫ f.hom = a ≫ (f.symm ≪≫ h.symm ≪≫ e').inv := by
  rw [← ha]
  simp

private lemma mono_iso_sandwich {C : Type*} [Category C]
    {A B D E F : C} (e : A ≅ B) (m : B ⟶ D) (u : D ≅ E) (v : E ≅ F)
    [Mono m] : Mono ((e.hom ≫ m ≫ u.hom) ≫ v.hom) := inferInstance

lemma tensor_inclusion_framed (J M : LineBundle X) (ι : J.sheaf ⟶ O X)
    (U : X.Opens) (e : J.sheaf.restrict U.ι ≅ O U.toScheme)
    (f : M.sheaf.restrict U.ι ≅ O U.toScheme) :
    (tensorFrame J M U e f).inv ≫
        (Scheme.Modules.restrictFunctor U.ι).map (tensorInclusion J M ι) ≫ f.hom =
      (e.inv ≫ (Scheme.Modules.restrictFunctor U.ι).map ι ≫
        (Scheme.Modules.restrictUnitIso U.ι).hom) ≫ (tensorUnitTwist M U f).inv := by
  let F := Scheme.Modules.restrictFunctor U.ι
  let R := moduleTensorRestrict U J.sheaf M.sheaf
  let R' := moduleTensorRestrict U (O X) M.sheaf
  let E := moduleTensorIso e f
  let E' := moduleTensorIso (Scheme.Modules.restrictUnitIso U.ι) f
  let T := moduleTensorUnit (O U.toScheme)
  let a : O U.toScheme ⟶ O U.toScheme :=
    (e.inv ≫ F.map ι) ≫ (Scheme.Modules.restrictUnitIso U.ι).hom
  have hn : F.map (moduleTensorMap ι (𝟙 M.sheaf)) ≫ R'.hom =
      R.hom ≫ moduleTensorMap (F.map ι) (𝟙 (M.sheaf.restrict U.ι)) :=
    (moduleTensorRestrict_natural U ι (𝟙 M.sheaf)).trans
      (congrArg (fun q => R.hom ≫ moduleTensorMap (F.map ι) q) (F.map_id M.sheaf))
  have h₁ := (moduleTensorMap_comp e.inv (F.map ι) f.inv
    (𝟙 (M.sheaf.restrict U.ι))).symm.trans
      (congrArg (moduleTensorMap (e.inv ≫ F.map ι)) (Category.comp_id f.inv))
  have h₂ := (moduleTensorMap_comp (e.inv ≫ F.map ι)
    (Scheme.Modules.restrictUnitIso U.ι).hom f.inv f.hom).symm.trans
      (congrArg (moduleTensorMap a) f.inv_hom_id)
  have ht : E.inv ≫ moduleTensorMap (F.map ι) (𝟙 (M.sheaf.restrict U.ι)) ≫
      E'.hom = moduleTensorMap a (𝟙 (O U.toScheme)) :=
    (Category.assoc _ _ _).symm.trans
      ((congrArg (fun q => q ≫ E'.hom) h₁).trans h₂)
  have hs : E.inv ≫ moduleTensorMap (F.map ι) (𝟙 (M.sheaf.restrict U.ι)) ≫
      E'.hom ≫ T.hom = T.hom ≫ a := by
    have hscalar := moduleTensorUnit_scalar (X := U.toScheme) a (𝟙 (O U.toScheme))
    exact (Category.assoc _ _ _).symm.trans
      ((congrArg (fun q => q ≫ T.hom) ht).trans
        (hscalar.trans (congrArg (fun q => T.hom ≫ q) (Category.comp_id a))))
  have hframe := frame_square R R' E E' T
    (F.map (moduleTensorMap ι (𝟙 M.sheaf))) _ a hn hs
  have hfinal := frame_inclusion (R ≪≫ E ≪≫ T) (R' ≪≫ E' ≪≫ T)
    (F.mapIso (moduleTensorUnit M.sheaf)) f
    (F.map (moduleTensorMap ι (𝟙 M.sheaf))) a hframe
  simpa only [tensorInclusion, tensorUnitTwist, tensorFrame] using!
    (congrArg (fun q => (tensorFrame J M U e f).inv ≫ q ≫ f.hom)
      (F.map_comp (moduleTensorMap ι (𝟙 M.sheaf)) (moduleTensorUnit M.sheaf).hom)).trans hfinal

theorem tensorInclusion_mono (J M : LineBundle X) (ι : J.sheaf ⟶ O X) [Mono ι] :
    Mono (tensorInclusion J M ι) := by
  apply PiExponent.CoherentTwist.mono_of_local
  intro x
  obtain ⟨U,hx,⟨e⟩,⟨f⟩⟩ := common_affine_frames J M x
  refine ⟨U.1,hx,?_⟩
  have hm : Mono ((tensorFrame J M U.1 e f).inv ≫
      (Scheme.Modules.restrictFunctor U.1.ι).map (tensorInclusion J M ι) ≫ f.hom) := by
    erw [tensor_inclusion_framed]
    have hmap : Mono (C := U.1.toScheme.Modules)
        ((Scheme.Modules.restrictFunctor U.1.ι).map ι) :=
      @Functor.map_mono _ _ _ _ (Scheme.Modules.restrictFunctor U.1.ι)
        inferInstance _ _ ι (inferInstanceAs (Mono ι))
    exact @mono_iso_sandwich U.1.toScheme.Modules _ _ _ _ _ _ e.symm
      ((Scheme.Modules.restrictFunctor U.1.ι).map ι)
      (Scheme.Modules.restrictUnitIso U.1.ι) (tensorUnitTwist M U.1 f).symm hmap
  exact (mono_comp_iff_of_mono _ f.hom).mp
    ((mono_comp_iff_of_isIso (tensorFrame J M U.1 e f).inv _).mp hm)

lemma tensor_inclusion_ideal (J M : LineBundle X) (ι : J.sheaf ⟶ O X)
    (U : X.affineOpens) (e : J.sheaf.restrict U.1.ι ≅ O U.1.toScheme)
    (f : M.sheaf.restrict U.1.ι ≅ O U.1.toScheme) :
    Ideal.span {U.1.topIso.hom (endValue ((tensorFrame J M U.1 e f).inv ≫
      (Scheme.Modules.restrictFunctor U.1.ι).map (tensorInclusion J M ι) ≫ f.hom))} =
    Ideal.span {U.1.topIso.hom (endValue (e.inv ≫
      (Scheme.Modules.restrictFunctor U.1.ι).map ι ≫
        (Scheme.Modules.restrictUnitIso U.1.ι).hom))} := by
  erw [tensor_inclusion_framed,endValue_comp,map_mul,
    ← Ideal.span_singleton_mul_span_singleton]
  have hu : IsUnit (endValue (tensorUnitTwist M U.1 f).inv) :=
    (end_isIso_iff _).mp inferInstance
  erw [Ideal.span_singleton_eq_top.mpr (hu.map U.1.topIso.hom.hom),Ideal.mul_top]
  rfl

end
end PiExponentSeshadri.Geometry

end OAI
end Source0086

section Source0087
/-
Modification notice for the LogTwo project.
Derived from openai/math (Apache-2.0), revision adc7f1241b42e322a6451854ab7e4b4c146bf78a.
Original source: lean/OAI/NumberTheory/PiExponent/LocalAlgebra/IdealTensorPowers.lean
Changes: Convert module/import declarations to the Lean 4.34 public module format.
See ../../../../../THIRD_PARTY_NOTICES.txt for provenance and the recorded changes.
-/




namespace OAI


namespace PiExponentSeshadri.Geometry
noncomputable section
open AlgebraicGeometry CategoryTheory TopologicalSpace
open PiExponentSeshadri.Frames
variable {X : Scheme.{0}}

def idealPowerInclusion (J : LineBundle X) (ι : J.sheaf ⟶ O X) :
    ∀ n : ℕ, (J.pow n).sheaf ⟶ O X
  | 0 => 𝟙 _
  | n+1 => tensorInclusion J (J.pow n) ι ≫ idealPowerInclusion J ι n

lemma idealPowerInclusion_mono (J : LineBundle X) (ι : J.sheaf ⟶ O X) [Mono ι]
    (n : ℕ) : Mono (idealPowerInclusion J ι n) := by
  induction n with
  | zero => change Mono (𝟙 (O X)); infer_instance
  | succ n ih =>
    let := ih
    let := tensorInclusion_mono J (J.pow n) ι
    change Mono (tensorInclusion J (J.pow n) ι ≫ idealPowerInclusion J ι n)
    infer_instance

def idealPowerFrame (J : LineBundle X) (U : X.Opens)
    (e : J.sheaf.restrict U.ι ≅ O U.toScheme) :
    ∀ n : ℕ, (J.pow n).sheaf.restrict U.ι ≅ O U.toScheme
  | 0 => Scheme.Modules.restrictUnitIso U.ι
  | n+1 => tensorFrame J (J.pow n) U e (idealPowerFrame J U e n)

def affineMapCoefficient {M N : X.Modules} (U : X.affineOpens)
    (e : M.restrict U.1.ι ≅ O U.1.toScheme)
    (f : N.restrict U.1.ι ≅ O U.1.toScheme) (a : M ⟶ N) : Γ(X,U.1) :=
  U.1.topIso.hom (endValue (e.inv ≫ (Scheme.Modules.restrictFunctor U.1.ι).map a ≫ f.hom))

lemma affineMapCoefficient_comp {M N P : X.Modules} (U : X.affineOpens)
    (e : M.restrict U.1.ι ≅ O U.1.toScheme)
    (f : N.restrict U.1.ι ≅ O U.1.toScheme)
    (g : P.restrict U.1.ι ≅ O U.1.toScheme) (a : M ⟶ N) (b : N ⟶ P) :
    affineMapCoefficient U e g (a ≫ b) =
      affineMapCoefficient U e f a * affineMapCoefficient U f g b := by
  unfold affineMapCoefficient
  rw [← map_mul,← endValue_comp]
  simp only [Functor.map_comp,Category.assoc,Iso.hom_inv_id_assoc]

private lemma affineMapCoefficient_id {M : X.Modules} (U : X.affineOpens)
    (e : M.restrict U.1.ι ≅ O U.1.toScheme) :
    affineMapCoefficient U e e (𝟙 M) = 1 := by
  simp only [affineMapCoefficient]
  erw [CategoryTheory.Functor.map_id, Category.id_comp, Iso.inv_hom_id, endValue_id, map_one]

lemma idealPowerInclusion_ideal (J : LineBundle X) (ι : J.sheaf ⟶ O X)
    (U : X.affineOpens) (e : J.sheaf.restrict U.1.ι ≅ O U.1.toScheme) (n : ℕ) :
    Ideal.span (Set.singleton (affineMapCoefficient U (idealPowerFrame J U.1 e n)
      (Scheme.Modules.restrictUnitIso U.1.ι) (idealPowerInclusion J ι n))) =
      (Ideal.span {affineMapCoefficient U e (Scheme.Modules.restrictUnitIso U.1.ι) ι})^n := by
  induction n with
  | zero =>
    simp only [idealPowerFrame, idealPowerInclusion]
    exact (congrArg (fun r : Γ(X,U.1) => Ideal.span {r})
      (affineMapCoefficient_id U (Scheme.Modules.restrictUnitIso U.1.ι))).trans (by simp)
  | succ n ih =>
    change Ideal.span (Set.singleton (affineMapCoefficient U (tensorFrame J (J.pow n) U.1 e (idealPowerFrame J U.1 e n))
      (Scheme.Modules.restrictUnitIso U.1.ι) (tensorInclusion J (J.pow n) ι ≫ idealPowerInclusion J ι n))) = _
    erw [affineMapCoefficient_comp U _ (idealPowerFrame J U.1 e n),
      ← Ideal.span_singleton_mul_span_singleton,ih]
    rw [show Ideal.span (Set.singleton (affineMapCoefficient U (tensorFrame J (J.pow n) U.1 e (idealPowerFrame J U.1 e n))
      (idealPowerFrame J U.1 e n) (tensorInclusion J (J.pow n) ι))) =
      Ideal.span {affineMapCoefficient U e (Scheme.Modules.restrictUnitIso U.1.ι) ι} from
        tensor_inclusion_ideal J (J.pow n) ι U e (idealPowerFrame J U.1 e n)]
    rw [pow_succ']

end
end PiExponentSeshadri.Geometry

end OAI
end Source0087

#print axioms OAI.PiExponent.CurveDegree.section_tensor_euler_add
#print axioms OAI.PiExponent.SectionZeroStalk.zero_stalk_kernel

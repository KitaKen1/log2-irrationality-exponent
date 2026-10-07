/- Generated rc4 checkpoint for LogTwo.
Modified from the reduced edition: new imports, separate module compilation,
and synchronous elaboration. Original source blocks and notices are retained.
See ../../../THIRD_PARTY_NOTICES.txt and ../../reduction.json.
-/
module
public import LogTwoCheckpoints.Part000
public import Mathlib.Algebra.Order.Antidiag.FinsuppEquiv
public import Mathlib.Analysis.Complex.Polynomial.Basic
public import Mathlib.Analysis.SpecialFunctions.Choose
public import Mathlib.Data.FunLike.Basic
public import Mathlib.NumberTheory.FunctionField
public import Mathlib.RingTheory.MvPowerSeries.Equiv
public import Mathlib.RingTheory.PowerSeries.Log
public import Mathlib.RingTheory.RamificationInertia.Basic
public import Mathlib.RingTheory.Valuation.Integral
@[expose] public section
set_option Elab.async false

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
    FiniteDimensional (IntermediateField.adjoin F {g}) E := by
  have hind : AlgebraicIndependent F (fun z : ({g} : Set E) => (z : E)) := by
    rw [algebraicIndependent_singleton_iff ⟨g, rfl⟩]
    exact hg
  have hb := hind.isTranscendenceBasis_of_trdeg_le_of_finite (by simpa using htrdeg)
  have hrange : Set.range (fun z : ({g} : Set E) => (z : E)) = {g} :=
    Subtype.range_coe
  let : Algebra.IsAlgebraic (IntermediateField.adjoin F {g}) E := by
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
    fiberDegree S p = Module.finrank R S := by
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
    fiberDegree S p = Module.finrank K L := by
  rw [fiberDegree_eq_rank, IsFractionRing.finrank_eq R K S L]

theorem functionField_fiberDegree
    (F E : Type*) [Field F] [Field E]
    [Algebra F[X] E] [Algebra (RatFunc F) E]
    [IsScalarTower F[X] (RatFunc F) E]
    [FunctionField F E] [Algebra.IsSeparable (RatFunc F) E]
    (p : Ideal F[X]) [p.IsPrime] :
    fiberDegree (FunctionField.ringOfIntegers F E) p =
      Module.finrank (RatFunc F) E := by
  let : Module.IsTorsionFree F[X] (FunctionField.ringOfIntegers F E) :=
    Module.isTorsionFree_iff_algebraMap_injective.mpr
      (FunctionField.ringOfIntegers.algebraMap_injective F E)
  exact fiberDegree_eq_fractionField_rank F[X] (RatFunc F)
    (FunctionField.ringOfIntegers F E) E p

theorem adjoin_inverse_eq {F E : Type*} [Field F] [Field E] [Algebra F E] (f : E) :
    IntermediateField.adjoin F {f⁻¹} = IntermediateField.adjoin F {f} := by
  apply le_antisymm
  · exact IntermediateField.adjoin_simple_le_iff.mpr
      (IntermediateField.inv_mem _ (IntermediateField.subset_adjoin F {f} (by simp)))
  · apply IntermediateField.adjoin_simple_le_iff.mpr
    simpa using IntermediateField.inv_mem (IntermediateField.adjoin F {f⁻¹})
      (show f⁻¹ ∈ IntermediateField.adjoin F {f⁻¹} from
        IntermediateField.subset_adjoin F {f⁻¹} (Set.mem_singleton _))

theorem parameter_inverse_degree_eq
    {F E : Type*} [Field F] [Field E] [Algebra F E] (f : E) :
    Module.finrank (IntermediateField.adjoin F {f⁻¹}) E =
      Module.finrank (IntermediateField.adjoin F {f}) E := by
  rw [adjoin_inverse_eq]

def parameterEmbedding {F E : Type*} [Field F] [Field E] [Algebra F E]
    (f : E) (hf : Transcendental F f) : RatFunc F →ₐ[F] E :=
  (IntermediateField.val (IntermediateField.adjoin F {f})).comp
    (RatFunc.algEquivOfTranscendental f hf).toAlgHom

@[simp] theorem parameterEmbedding_X {F E : Type*} [Field F] [Field E] [Algebra F E]
    (f : E) (hf : Transcendental F f) : parameterEmbedding f hf RatFunc.X = f := by
  simp [parameterEmbedding]

abbrev parameterAlgebra {F E : Type*} [Field F] [Field E] [Algebra F E]
    (f : E) (hf : Transcendental F f) : Algebra (RatFunc F) E :=
  (parameterEmbedding f hf).toRingHom.toAlgebra

theorem parameter_finrank {F E : Type*} [Field F] [Field E] [Algebra F E]
    (f : E) (hf : Transcendental F f) :
    let := parameterAlgebra f hf
    Module.finrank (RatFunc F) E = Module.finrank (IntermediateField.adjoin F {f}) E := by
  let := parameterAlgebra f hf
  apply Algebra.finrank_eq_of_equiv_equiv
    (RatFunc.algEquivOfTranscendental f hf).toRingEquiv (RingEquiv.refl E)
  rfl

theorem parameter_finite {F E : Type*} [Field F] [Field E] [Algebra F E]
    (f : E) (hf : Transcendental F f)
    [FiniteDimensional (IntermediateField.adjoin F {f}) E] :
    let := parameterAlgebra f hf
    FiniteDimensional (RatFunc F) E := by
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
    IsScalarTower F[X] (RatFunc F) E := by
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
    parameterFiberDegree f hf = Module.finrank (IntermediateField.adjoin F {f}) E := by
  let := parameterAlgebra f hf
  let := parameterPolynomialAlgebra f hf
  let := parameter_scalarTower f hf
  let := parameter_finite f hf
  change fiberDegree (FunctionField.ringOfIntegers F E) (zeroPrime F) = _
  rw [functionField_fiberDegree]
  exact parameter_finrank f hf

theorem transcendental_inverse {F E : Type*} [Field F] [Field E] [Algebra F E]
    (f : E) (hf : Transcendental F f) : Transcendental F f⁻¹ := by
  simpa only [Transcendental, IsAlgebraic.inv_iff] using hf

theorem constantCoeff_surjective (F : Type*) [Field F] :
    Function.Surjective (Polynomial.constantCoeff : F[X] →+* F) := by
  intro x
  exact ⟨Polynomial.C x, by simp⟩

instance zeroPrime_isMaximal (F : Type*) [Field F] : (zeroPrime F).IsMaximal :=
  RingHom.ker_isMaximal_of_surjective Polynomial.constantCoeff (constantCoeff_surjective F)

def zeroPrimeQuotientEquiv (F : Type*) [Field F] : (F[X] ⧸ zeroPrime F) ≃+* F :=
  RingHom.quotientKerEquivOfSurjective (constantCoeff_surjective F)

theorem zeroFiber_inertiaDeg_eq_one (F S : Type*) [Field F] [IsAlgClosed F]
    [CommRing S] [Algebra F[X] S] [Module.Finite F[X] S]
    (q : Ideal S) [q.IsPrime] [q.LiesOver (zeroPrime F)] :
    q.inertiaDeg F[X] = 1 := by
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
    zeroFiberLength F S = fiberDegree S (zeroPrime F) := by
  unfold zeroFiberLength fiberDegree
  apply Finset.sum_congr rfl
  intro q _
  rw [zeroFiber_inertiaDeg_eq_one F S q.1, mul_one,
    Ideal.ramificationIdx_eq (zeroPrime F) q.1]
  have hm : (zeroPrime F).map (algebraMap F[X] (Localization.AtPrime q.1)) =
      Ideal.span {algebraMap F[X] (Localization.AtPrime q.1) Polynomial.X} := by
    calc
      _ = (Ideal.span {Polynomial.X}).map
          (algebraMap F[X] (Localization.AtPrime q.1)) :=
        congrArg (Ideal.map (algebraMap F[X] (Localization.AtPrime q.1))) (zeroPrime_eq_span_X F)
      _ = _ := by rw [Ideal.map_span, Set.image_singleton]
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
    parameterZeroLength f hf = Module.finrank (IntermediateField.adjoin F {f}) E := by
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
    parameterZeroLength f hf = parameterZeroLength f⁻¹ (transcendental_inverse f hf) := by
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
            Ideal.span {algebraMap S (Localization.AtPrime q.asIdeal) a})) := by
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
          Ideal.span {algebraMap S (Localization.AtPrime q.asIdeal) a})).toNat : ℤ) := by
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

theorem zeroPrime_ne_bot (F : Type*) [Field F] : zeroPrime F ≠ ⊥ := by
  intro h
  have hx : Polynomial.X ∈ zeroPrime F := by
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
    algebraMap F[X] E Polynomial.X ≠ 0 := by
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
    zeroFiberIntegerOrderSum F S E = (zeroFiberLength F S : ℤ) := by
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
          ((map_ne_zero_iff _ (IsFractionRing.injective S E)).mpr hx)) := by
      congr 1
      ext
      exact IsScalarTower.algebraMap_apply F[X] S E Polynomial.X
    _ = _ := he
    _ = _ := by
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
    parameterZeroOrder f hf = (parameterZeroLength f hf : ℤ) := by
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
    parameterZeroOrder f hf = parameterZeroOrder f⁻¹ (transcendental_inverse f hf) := by
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
    algebraMap F[X] E p = Polynomial.aeval f p := by
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
          (Units.mk0 f hf.ne_zero) := by
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
    integerOrder v (Units.map (algebraMap A E) u) = 0 := by
  have hpos : 0 ≤ integerOrder v (Units.map (algebraMap A E) u) := by
    apply WithTop.coe_le_coe.mp
    simpa using hregular (u : A)
  have hneg : 0 ≤ integerOrder v (Units.map (algebraMap A E) u⁻¹) := by
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
      IsDiscreteValuationRing.addVal A a = n := by
  obtain ⟨n, u, rfl⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible ha hπ
  refine ⟨n, ?_, IsDiscreteValuationRing.addVal_def' u hπ n⟩
  have he : localFieldUnit (E := E) ((u : A) * π ^ n) ha =
      Units.map (algebraMap A E) u * localFieldUnit (E := E) π hπ.ne_zero ^ n := by
    ext
    simp [localFieldUnit, map_mul, map_pow]
  rw [he, integerOrder_mul, integerOrder_pow, integerOrder_unit_eq_zero v hregular]
  simp

theorem uniformizer_order_dvd
    (v : AddValuation E (WithTop ℤ))
    (hregular : ∀ a : A, 0 ≤ v (algebraMap A E a))
    {π : A} (hπ : Irreducible π) (z : Eˣ) :
    integerOrder v (localFieldUnit (E := E) π hπ.ne_zero) ∣ integerOrder v z := by
  obtain ⟨a, b, hb, hab⟩ := IsFractionRing.div_surjective A (z : E)
  have hb0 : b ≠ 0 := mem_nonZeroDivisors_iff_ne_zero.mp hb
  have ha0 : a ≠ 0 := by
    intro ha
    apply z.ne_zero
    rw [← hab, ha, map_zero, zero_div]
  have hz : z = localFieldUnit (E := E) a ha0 / localFieldUnit (E := E) b hb0 := by
    ext
    simpa only [Units.val_div_eq_div_val, localFieldUnit_val] using hab.symm
  obtain ⟨m, hm, _⟩ := exists_order_eq_uniformizer_multiple v hregular hπ a ha0
  obtain ⟨n, hn, _⟩ := exists_order_eq_uniformizer_multiple v hregular hπ b hb0
  rw [hz, integerOrder_div, hm, hn]
  exact ⟨(m : ℤ) - n, by ring⟩

theorem eq_fractionAddValuation
    (v : AddValuation E (WithTop ℤ))
    (hregular : ∀ a : A, 0 ≤ v (algebraMap A E a))
    (hcenter : ∀ a ∈ IsLocalRing.maximalIdeal A, a ≠ 0 → 0 < v (algebraMap A E a))
    (hnormalized : ∃ z : Eˣ, integerOrder v z = 1) :
    v = fractionAddValuation A E := by
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible A
  have hπmem : π ∈ IsLocalRing.maximalIdeal A := by
    rw [hπ.maximalIdeal_eq]
    exact Ideal.subset_span (Set.mem_singleton π)
  have hpos : 0 < integerOrder v (localFieldUnit (E := E) π hπ.ne_zero) := by
    apply WithTop.coe_lt_coe.mp
    simpa using hcenter π hπmem hπ.ne_zero
  have hone : integerOrder v (localFieldUnit (E := E) π hπ.ne_zero) = 1 := by
    obtain ⟨z, hz⟩ := hnormalized
    apply Int.eq_one_of_dvd_one hpos.le
    rw [← hz]
    exact uniformizer_order_dvd v hregular hπ z
  have hlocal (a : A) : v (algebraMap A E a) = localAddValuation A a := by
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
    ∃ z : Eˣ, integerOrder (fractionAddValuation A E) z = 1 := by
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
    {x : E} (hx : IsIntegral R x) : x ∈ v.valuationSubring := by
  let φ : R →+* v.valuationSubring :=
    { toFun := fun r => ⟨algebraMap R E r, hR r⟩
      map_zero' := by ext; simp
      map_one' := by ext; simp
      map_add' := by intros; ext; simp
      map_mul' := by intros; ext; simp }
  let : Algebra R v.valuationSubring := φ.toAlgebra
  let : IsScalarTower R v.valuationSubring E :=
    IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  exact (Valuation.valuationSubring.integers v).mem_of_integral hx.tower_top

theorem aeval_mem_valuationSubring
    {F E : Type*} [Field F] [Field E] [Algebra F E]
    (v : AddValuation E (WithTop ℤ)) (hF : ∀ c : F, 0 ≤ v (algebraMap F E c))
    (f : E) (hf : 0 ≤ v f) (p : F[X]) :
    Polynomial.aeval f p ∈ v.toValuation.valuationSubring := by
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
    (x : E) ∈ v.toValuation.valuationSubring := by
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
    x ∈ parameterValuationCenter f hf v hF hvf ↔ 0 < v (x : E) := by
  change parameterChartValuationHom f hf v hF hvf x ∈
    IsLocalRing.maximalIdeal v.toValuation.valuationSubring ↔ _
  exact v.toValuation.mem_maximalIdeal_iff

theorem parameterValuationCenter_liesOver
    {F E : Type*} [Field F] [Field E] [Algebra F E]
    (f : E) (hf : Transcendental F f)
    (v : AddValuation E (WithTop ℤ)) (hF : ∀ c : F, 0 ≤ v (algebraMap F E c))
    (hvf : 0 < v f) :
    letI := parameterPolynomialAlgebra f hf
    (parameterValuationCenter f hf v hF hvf.le).LiesOver (zeroPrime F) := by
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
    (g := parameterChartValuationHom f hf v hF hvf) (fun y => by
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
    IsLocalRing.maximalIdeal (Localization.AtPrime (parameterValuationCenter f hf v hF hvf)) := by
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
    (parameterCenterLocalHom f hf v hF hvf a : E) = algebraMap _ E a := by
  have hm : v.toValuation.valuationSubring.subtype.comp
      (parameterCenterLocalHom f hf v hF hvf) = algebraMap _ E := by
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
    0 ≤ v (algebraMap _ E a) := by
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
    (ha : a ∈ IsLocalRing.maximalIdeal _) : 0 < v (algebraMap _ E a) := by
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
          (algebraMap S (Localization.AtPrime q.asIdeal) a)) := by
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
    0 ≤ primeFieldValuation S E q (algebraMap S E a) := by
  rw [primeFieldValuation_algebraMap_localOrder]
  exact CurveLocalOrder.enatToIntegerOrder_monotone (show (0 : ℕ∞) ≤ _ from zero_le)

theorem enatToIntegerOrder_pos_iff (n : ℕ∞) :
    0 < CurveLocalOrder.enatToIntegerOrder n ↔ 0 < n := by
  rcases eq_or_ne n ⊤ with rfl | hn
  · simp
  obtain ⟨k, hk⟩ := ENat.ne_top_iff_exists.mp hn
  rw [← hk]
  simp

theorem primeFieldValuation_positive_iff
    (S E : Type*) [CommRing S] [IsDedekindDomain S]
    [Field E] [Algebra S E] [IsFractionRing S E]
    (q : IsDedekindDomain.HeightOneSpectrum S) (a : S) :
    0 < primeFieldValuation S E q (algebraMap S E a) ↔ a ∈ q.asIdeal := by
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
    {p q : NormalizedPlace F E} (h : p.valuation = q.valuation) : p = q := by
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
    v = parameterPlaceValuation f hf (parameterCenterPlace f hf v hF hvf) := by
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
    ∃ z : Eˣ, WeightedCurveDegree.integerOrder (primeFieldValuation S E q) z = 1 := by
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
    0 ≤ parameterPlaceValuation f hf q (algebraMap F E c) := by
  let := parameterAlgebra f hf
  let := parameterPolynomialAlgebra f hf
  let := parameter_scalarTower f hf
  let := parameter_finite f hf
  let S := parameterChart f hf
  let : Module.IsTorsionFree F[X] S :=
    Module.isTorsionFree_iff_algebraMap_injective.mpr
      (FunctionField.ringOfIntegers.algebraMap_injective F E)
  have hmap : algebraMap S E (algebraMap F[X] S (Polynomial.C c)) = algebraMap F E c := by
    rw [← IsScalarTower.algebraMap_apply F[X] S E,
      parameterPolynomialAlgebra_map f hf, Polynomial.aeval_C]
  change 0 ≤ primeFieldValuation S E (zeroFiberHeightOne F S q) (algebraMap F E c)
  rw [← hmap]
  exact primeFieldValuation_algebraMap_nonneg S E _ _

theorem parameterPlaceValuation_positive
    {F E : Type*} [Field F] [CharZero F] [Field E] [Algebra F E]
    (f : E) (hf : Transcendental F f)
    [FiniteDimensional (IntermediateField.adjoin F {f}) E]
    (q : parameterZeroPlaces f hf) : 0 < parameterPlaceValuation f hf q f := by
  let := parameterAlgebra f hf
  let := parameterPolynomialAlgebra f hf
  let := parameter_scalarTower f hf
  let := parameter_finite f hf
  let S := parameterChart f hf
  let : Module.IsTorsionFree F[X] S :=
    Module.isTorsionFree_iff_algebraMap_injective.mpr
      (FunctionField.ringOfIntegers.algebraMap_injective F E)
  have hmap : algebraMap S E (algebraMap F[X] S Polynomial.X) = f := by
    rw [← IsScalarTower.algebraMap_apply F[X] S E,
      parameterPolynomialAlgebra_map f hf, Polynomial.aeval_X]
  change 0 < primeFieldValuation S E (zeroFiberHeightOne F S q) f
  have hx : algebraMap F[X] S Polynomial.X ∈ q.1 := by
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
  normalized := by
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
      (parameterPlaceValuation_positive f hf q) = q := by
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
  left_inv p := by
    apply Subtype.ext
    apply NormalizedPlace.ext
    exact (valuation_eq_parameterPlaceValuation f hf p.1.valuation
      p.1.constants_nonneg p.2 p.1.normalized).symm
  right_inv q := parameterCenterPlace_parameterNormalizedPlace f hf q

theorem finite_positivePlaces
    {F E : Type*} [Field F] [CharZero F] [Field E] [Algebra F E]
    (f : E) (hf : Transcendental F f)
    [FiniteDimensional (IntermediateField.adjoin F {f}) E] :
    Set.Finite {p : NormalizedPlace F E | 0 < p.valuation f} := by
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
    (p : NormalizedPlace F E) (z : Eˣ) : placeOrder p z⁻¹ = -placeOrder p z := by
  exact integerOrder_inv p.valuation z

theorem valuation_pos_iff_order_pos {F E : Type*} [Field F] [Field E] [Algebra F E]
    (p : NormalizedPlace F E) (z : Eˣ) : 0 < p.valuation (z : E) ↔ 0 < placeOrder p z := by
  rw [← coe_integerOrder]
  exact WithTop.coe_lt_coe

theorem order_ne_zero_iff_positive_or_inverse
    {F E : Type*} [Field F] [Field E] [Algebra F E]
    (p : NormalizedPlace F E) (z : Eˣ) :
    placeOrder p z ≠ 0 ↔ 0 < p.valuation (z : E) ∨ 0 < p.valuation ((z : E)⁻¹) := by
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
    p ∈ positivePlaces f hf ↔ 0 < p.valuation f := by
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
    ∑ p ∈ positivePlaces f hf, placeOrder p (Units.mk0 f hf.ne_zero) = parameterZeroOrder f hf := by
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
    (Function.support (fun p : NormalizedPlace F E => placeOrder p (Units.mk0 f hf.ne_zero))).Finite := by
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
    (principalDivisor f hf).sum (fun _ n => n) = 0 := by
  classical
  let : FiniteDimensional (IntermediateField.adjoin F {f⁻¹}) E :=
    (adjoin_inverse_eq (F := F) f).symm ▸ inferInstance
  let z : Eˣ := Units.mk0 f hf.ne_zero
  let zi : Eˣ := Units.mk0 f⁻¹ (transcendental_inverse f hf).ne_zero
  have hiz : zi = z⁻¹ := by ext; simp [zi, z]
  have hsup : (principalDivisor f hf).support ⊆
      positivePlaces f hf ∪ positivePlaces f⁻¹ (transcendental_inverse f hf) := by
    intro p hp
    have hn : placeOrder p z ≠ 0 := by simpa [z] using Finsupp.mem_support_iff.mp hp
    simpa only [Finset.mem_union, mem_positivePlaces, z, Units.val_mk0] using
      (order_ne_zero_iff_positive_or_inverse p z).mp hn
  have hdisj : Disjoint (positivePlaces f hf)
      (positivePlaces f⁻¹ (transcendental_inverse f hf)) := by
    apply Finset.disjoint_left.mpr
    intro p hp hi
    have hp' : 0 < placeOrder p z :=
      (valuation_pos_iff_order_pos p z).mp ((mem_positivePlaces f hf p).mp hp)
    have hi' : 0 < placeOrder p zi :=
      (valuation_pos_iff_order_pos p zi).mp
        ((mem_positivePlaces f⁻¹ (transcendental_inverse f hf) p).mp hi)
    rw [hiz, placeOrder_inv] at hi'
    omega
  rw [Finsupp.sum_of_support_subset _ hsup _ (by intro _ _; rfl)]
  simp only [principalDivisor_apply]
  rw [Finset.sum_union hdisj, sum_positiveOrders_eq]
  have hi : (∑ p ∈ positivePlaces f⁻¹ (transcendental_inverse f hf), placeOrder p z) =
      -parameterZeroOrder f⁻¹ (transcendental_inverse f hf) := by
    calc
      _ = ∑ p ∈ positivePlaces f⁻¹ (transcendental_inverse f hf), -(placeOrder p zi) := by
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
    p.valuation (algebraMap F E c) = 0 := by
  let z : Eˣ := Units.mk0 (algebraMap F E c) ((map_ne_zero_iff _ (algebraMap F E).injective).mpr hc)
  have hpos : 0 ≤ integerOrder p.valuation z := by
    apply WithTop.coe_le_coe.mp
    rw [coe_integerOrder]
    exact p.constants_nonneg c
  have hinv : 0 ≤ integerOrder p.valuation z⁻¹ := by
    apply WithTop.coe_le_coe.mp
    rw [coe_integerOrder]
    simpa [z] using p.constants_nonneg c⁻¹
  rw [integerOrder_inv] at hinv
  have hz : integerOrder p.valuation z = 0 := by omega
  have he := coe_integerOrder p.valuation z
  rw [hz] at he
  exact he.symm

theorem placeOrder_constant_eq_zero
    {F E : Type*} [Field F] [Field E] [Algebra F E]
    (p : NormalizedPlace F E) (c : F) (hc : c ≠ 0) :
    placeOrder p (Units.mk0 (algebraMap F E c) ((map_ne_zero_iff _ (algebraMap F E).injective).mpr hc)) = 0 := by
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
    μ * d.weight v ≤ (n : ℚ) := by
  classical
  have hfinite : ∀ i ∈ d.support, (a i).order ≠ ⊤ := by
    intro i hi
    apply ne_top_of_le_ne_top (by simp : (n : ℕ∞) ≠ ⊤)
    exact (Finsupp.le_weight_of_ne_zero' (order ∘ a)
      (Finsupp.mem_support_iff.mp hi)).trans hbound
  have hsum :
      ((∑ i ∈ d.support, d i * (a i).order.toNat : ℕ) : ℕ∞) =
        d.weight (order ∘ a) := by
    simp only [Nat.cast_sum, Nat.cast_mul, Finsupp.weight_apply,
      Finsupp.sum, Function.comp_apply, nsmul_eq_mul]
    apply Finset.sum_congr rfl
    intro i hi
    rw [ENat.natCast_toNat (hfinite i hi)]
  have hnat : (∑ i ∈ d.support, d i * (a i).order.toNat : ℕ) ≤ n := by
    exact_mod_cast hsum.symm ▸ hbound
  calc
    μ * d.weight v = ∑ i ∈ d.support, (d i : ℚ) * (μ * v i) := by
      simp only [Finsupp.weight_apply, Finsupp.sum, nsmul_eq_mul, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i hi
      ring
    _ ≤ ∑ i ∈ d.support, (d i : ℚ) * ((a i).order.toNat : ℚ) := by
      apply Finset.sum_le_sum
      intro i hi
      exact mul_le_mul_of_nonneg_left
        (hcontact i _ (ENat.natCast_toNat (hfinite i hi)).symm) (by positivity)
    _ ≤ (n : ℚ) := by exact_mod_cast hnat

theorem rational_order_subst_of_jet_vanishing
    (v : σ → ℚ) (μ H : ℚ) (hμ : 0 ≤ μ)
    (f : MvPowerSeries σ R) (a : σ → MvPowerSeries τ S)
    (ha : HasSubst a)
    (hjet : ∀ d : σ →₀ ℕ, d.weight v < H → coeff d f = 0)
    (hcontact : ∀ i (k : ℕ), (a i).order = (k : ℕ∞) → μ * v i ≤ (k : ℚ)) :
    (⌈μ * H⌉₊ : ℕ∞) ≤ (f.subst a).order := by
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
  have hdne : coeff d f ≠ 0 := by
    intro he
    simp [he] at hbound
  have hbound' : d.weight (order ∘ a) ≤ (n : ℕ∞) := by
    simpa [hdne] using hbound
  have hH : H ≤ d.weight v := by
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
    (⌈μ * H⌉₊ : ℕ∞) ≤ PowerSeries.order (f.subst a) := by
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

def active (a : ι → PowerSeries ℂ) : Finset ι := by
  classical
  exact Finset.univ.filter (fun i => a i ≠ 0)

@[simp] theorem mem_active (a : ι → PowerSeries ℂ) (i : ι) :
    i ∈ active a ↔ a i ≠ 0 := by
  classical
  simp [active]

theorem active_nonempty (a : ι → PowerSeries ℂ) (hne : ∃ i, a i ≠ 0) :
    (active a).Nonempty := by
  obtain ⟨i,hi⟩ := hne
  exact ⟨i,(mem_active a i).mpr hi⟩

def contact (v : ι → ℚ) (a : ι → PowerSeries ℂ) (hne : ∃ i, a i ≠ 0) : ℚ :=
  (active a).inf' (active_nonempty a hne) (fun i => ((a i).order.toNat : ℚ) / v i)

theorem contact_le (v : ι → ℚ) (a : ι → PowerSeries ℂ) (hne : ∃ i, a i ≠ 0)
    (i : ι) (hi : a i ≠ 0) :
    contact v a hne ≤ ((a i).order.toNat : ℚ) / v i :=
  Finset.inf'_le _ ((mem_active a i).mpr hi)

theorem exists_attains (v : ι → ℚ) (a : ι → PowerSeries ℂ) (hne : ∃ i, a i ≠ 0) :
    ∃ i, a i ≠ 0 ∧ contact v a hne = ((a i).order.toNat : ℚ) / v i := by
  obtain ⟨i,hi,he⟩ := Finset.exists_mem_eq_inf' (active_nonempty a hne)
    (fun i => ((a i).order.toNat : ℚ) / v i)
  exact ⟨i,(mem_active a i).mp hi,he⟩

theorem contact_pos (v : ι → ℚ) (hv : ∀ i, 0 < v i)
    (a : ι → PowerSeries ℂ) (hne : ∃ i, a i ≠ 0)
    (hc : ∀ i, PowerSeries.constantCoeff (a i) = 0) : 0 < contact v a hne := by
  obtain ⟨i,hi,he⟩ := exists_attains v a hne
  rw [he]
  apply div_pos _ (hv i)
  have horder := PowerSeries.one_le_order_iff_constCoeff_eq_zero.mpr (hc i)
  rw [← PowerSeries.coe_toNat_order hi] at horder
  have hnat : 1 ≤ (a i).order.toNat := by exact_mod_cast horder
  exact_mod_cast (show 0 < (a i).order.toNat by omega)

theorem contact_bound (v : ι → ℚ) (hv : ∀ i, 0 < v i)
    (a : ι → PowerSeries ℂ) (hne : ∃ i, a i ≠ 0) (i : ι) (k : ℕ)
    (hk : (a i).order = (k : ℕ∞)) : contact v a hne * v i ≤ (k : ℚ) := by
  have hi : a i ≠ 0 := by
    intro hz
    simp [hz] at hk
  have hnat : (a i).order.toNat = k := by simpa using congrArg ENat.toNat hk
  exact hnat ▸ (le_div_iff₀ (hv i)).mp (contact_le v a hne i hi)

theorem le_contact (v : ι → ℚ) (hv : ∀ i, 0 < v i)
    (a : ι → PowerSeries ℂ) (hne : ∃ i, a i ≠ 0) (μ : ℚ)
    (hμ : ∀ i (k : ℕ), (a i).order = (k : ℕ∞) → μ * v i ≤ (k : ℚ)) :
    μ ≤ contact v a hne := by
  apply Finset.le_inf'
  intro i hi
  apply (le_div_iff₀ (hv i)).mpr
  exact hμ i _ (PowerSeries.coe_toNat_order ((mem_active a i).mp hi)).symm

theorem order_add_lower (B : ℚ) (f g : PowerSeries ℂ)
    (hf : ∀ k : ℕ, f.order = (k : ℕ∞) → B ≤ (k : ℚ))
    (hg : ∀ k : ℕ, g.order = (k : ℕ∞) → B ≤ (k : ℚ))
    (k : ℕ) (hk : (f + g).order = (k : ℕ∞)) : B ≤ (k : ℚ) := by
  have hmin : min f.order g.order ≤ (k : ℕ∞) :=
    (PowerSeries.min_order_le_order_add f g).trans hk.le
  rcases min_le_iff.mp hmin with h | h
  · have hn : f.order ≠ ⊤ := ne_top_of_le_ne_top (by simp) h
    have he := ENat.natCast_toNat hn
    have hb := hf f.order.toNat he.symm
    have hnat : f.order.toNat ≤ k := by
      exact_mod_cast he.symm ▸ h
    exact hb.trans (by exact_mod_cast hnat)
  · have hn : g.order ≠ ⊤ := ne_top_of_le_ne_top (by simp) h
    have he := ENat.natCast_toNat hn
    have hb := hg g.order.toNat he.symm
    have hnat : g.order.toNat ≤ k := by
      exact_mod_cast he.symm ▸ h
    exact hb.trans (by exact_mod_cast hnat)

theorem exists_attaining_add (v : ι → ℚ) (hv : ∀ i, 0 < v i)
    (a t : ι → PowerSeries ℂ) (hne : ∃ i, a i ≠ 0)
    (ht : ∀ i (k : ℕ), (t i).order = (k : ℕ∞) → contact v a hne * v i < (k : ℚ)) :
    ∃ i, a i + t i ≠ 0 ∧ (a i + t i).order = (a i).order ∧
      contact v a hne = ((a i + t i).order.toNat : ℚ) / v i := by
  obtain ⟨i,hi,he⟩ := exists_attains v a hne
  have heq : contact v a hne * v i = ((a i).order.toNat : ℚ) :=
    (eq_div_iff (ne_of_gt (hv i))).mp he
  have hord : (a i).order < (t i).order := by
    by_cases hzero : t i = 0
    · simpa [hzero] using PowerSeries.order_finite_iff_ne_zero.mpr hi
    · have ht' := ht i (t i).order.toNat (PowerSeries.coe_toNat_order hzero).symm
      rw [heq] at ht'
      have hnat : (a i).order.toNat < (t i).order.toNat := by exact_mod_cast ht'
      rw [← PowerSeries.coe_toNat_order hi, ← PowerSeries.coe_toNat_order hzero]
      exact_mod_cast hnat
  have hsum : (a i + t i).order = (a i).order := by
    rw [PowerSeries.order_add_of_order_ne _ _ hord.ne, inf_eq_left.mpr hord.le]
  have hne' : a i + t i ≠ 0 := by
    intro hz
    have hh := PowerSeries.order_eq_top.mpr hz
    rw [hsum] at hh
    exact hi (PowerSeries.order_eq_top.mp hh)
  exact ⟨i,hne',hsum,hsum ▸ he⟩

theorem add_not_all_zero (v : ι → ℚ) (hv : ∀ i, 0 < v i)
    (a t : ι → PowerSeries ℂ) (hne : ∃ i, a i ≠ 0)
    (ht : ∀ i (k : ℕ), (t i).order = (k : ℕ∞) → contact v a hne * v i < (k : ℚ)) :
    ∃ i, a i + t i ≠ 0 := by
  obtain ⟨i,hi,_⟩ := exists_attaining_add v hv a t hne ht
  exact ⟨i,hi⟩

theorem contact_add_high_tail (v : ι → ℚ) (hv : ∀ i, 0 < v i)
    (a t : ι → PowerSeries ℂ) (hne : ∃ i, a i ≠ 0)
    (ht : ∀ i (k : ℕ), (t i).order = (k : ℕ∞) → contact v a hne * v i < (k : ℚ)) :
    contact v (fun i => a i + t i) (add_not_all_zero v hv a t hne ht) = contact v a hne := by
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

theorem residue_sub_dvd (a : A) : π ∣ a - algebraMap C A (ρ a) := by
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
    remainder ρ π hker (a+b) = remainder ρ π hker a + remainder ρ π hker b := by
  apply mul_left_cancel₀ hπ
  rw [mul_add, mul_remainder, mul_remainder, mul_remainder, map_add, map_add]
  ring

include hπ in
@[simp] theorem remainder_smul (c : C) (a : A) :
    remainder ρ π hker (c • a) = c • remainder ρ π hker a := by
  apply mul_left_cancel₀ hπ
  rw [Algebra.smul_def, mul_remainder, map_mul, AlgHom.commutes, map_mul]
  rw [Algebra.smul_def, mul_left_comm, mul_remainder]
  simp only [Algebra.algebraMap_self, RingHom.id_apply]
  ring

include hπ in
@[simp] theorem remainder_algebraMap (c : C) :
    remainder ρ π hker (algebraMap C A c) = 0 := by
  apply mul_left_cancel₀ hπ
  rw [mul_zero, mul_remainder, AlgHom.commutes]
  simp

include hker in
omit [IsDomain A] in
theorem residue_uniformizer : ρ π = 0 := by
  change π ∈ RingHom.ker ρ.toRingHom
  rw [hker]
  exact Ideal.subset_span (by simp)

include hπ in
@[simp] theorem remainder_uniformizer_mul (a : A) :
    remainder ρ π hker (π*a) = a := by
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
      expansionCoeff ρ π hπ hker n (remainder ρ π hker a) := by
  simp only [expansionCoeff, pow_succ, Module.End.mul_apply]
  rfl

@[simp] theorem expansionCoeff_add (n : ℕ) (a b : A) :
    expansionCoeff ρ π hπ hker n (a+b) =
      expansionCoeff ρ π hπ hker n a + expansionCoeff ρ π hπ hker n b := by
  simp [expansionCoeff]

@[simp] theorem expansionCoeff_smul (n : ℕ) (c : C) (a : A) :
    expansionCoeff ρ π hπ hker n (c • a) = c * expansionCoeff ρ π hπ hker n a := by
  simp [expansionCoeff]

def expansion (a : A) : PowerSeries C := PowerSeries.mk (fun n => expansionCoeff ρ π hπ hker n a)

@[simp] theorem coeff_expansion (a : A) (n : ℕ) :
    PowerSeries.coeff n (expansion ρ π hπ hker a) = expansionCoeff ρ π hπ hker n a :=
  PowerSeries.coeff_mk _ _

@[simp] theorem expansion_add (a b : A) :
    expansion ρ π hπ hker (a+b) = expansion ρ π hπ hker a + expansion ρ π hπ hker b := by
  ext n
  simp only [map_add, coeff_expansion, expansionCoeff_add]

@[simp] theorem expansion_smul (c : C) (a : A) :
    expansion ρ π hπ hker (c • a) = c • expansion ρ π hπ hker a := by
  ext n
  simp only [map_smul, coeff_expansion, expansionCoeff_smul, smul_eq_mul]

@[simp] theorem expansion_algebraMap (c : C) :
    expansion ρ π hπ hker (algebraMap C A c) = PowerSeries.C c := by
  ext n
  cases n with
  | zero => simp
  | succ n =>
    rw [coeff_expansion, expansionCoeff_succ, remainder_algebraMap ρ π hπ hker]
    simp [expansionCoeff]

theorem expansion_rec (a : A) :
    expansion ρ π hπ hker a = PowerSeries.C (ρ a) +
      expansion ρ π hπ hker (remainder ρ π hker a) * PowerSeries.X := by
  ext n
  cases n with
  | zero => simp
  | succ n => simp only [map_add, coeff_expansion, PowerSeries.coeff_succ_C,
      PowerSeries.coeff_succ_mul_X, expansionCoeff_succ, zero_add]

include hπ in

theorem remainder_mul (a b : A) :
    remainder ρ π hker (a*b) = remainder ρ π hker a * b +
      algebraMap C A (ρ a) * remainder ρ π hker b := by
  apply mul_left_cancel₀ hπ
  rw [mul_add, ← mul_assoc, mul_remainder, mul_left_comm π,
    mul_remainder, mul_remainder, map_mul, map_mul]
  ring

theorem expansion_mul (a b : A) :
    expansion ρ π hπ hker (a*b) = expansion ρ π hπ hker a * expansion ρ π hπ hker b := by
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
          expansionCoeff ρ π hπ hker n (remainder ρ π hker (a*b)) := by
        rw [coeff_expansion, expansionCoeff_succ]
      _ = expansionCoeff ρ π hπ hker n (remainder ρ π hker a * b) +
          ρ a * expansionCoeff ρ π hπ hker n (remainder ρ π hker b) := by
        rw [remainder_mul ρ π hπ hker, ← Algebra.smul_def, expansionCoeff_add,
          expansionCoeff_smul]
      _ = PowerSeries.coeff n (expansion ρ π hπ hker (remainder ρ π hker a) *
          expansion ρ π hπ hker b) +
          ρ a * PowerSeries.coeff (n+1) (expansion ρ π hπ hker b) := by
        rw [← coeff_expansion, ih]
        rw [coeff_expansion, expansionCoeff_succ]
      _ = PowerSeries.coeff (n+1)
          ((expansion ρ π hπ hker (remainder ρ π hker a) * expansion ρ π hπ hker b) *
            PowerSeries.X + PowerSeries.C (ρ a) * expansion ρ π hπ hker b) := by
        simp only [map_add, PowerSeries.coeff_succ_mul_X, PowerSeries.coeff_C_mul]
      _ = PowerSeries.coeff (n+1) (expansion ρ π hπ hker a * expansion ρ π hπ hker b) := by
        conv_rhs => rw [expansion_rec ρ π hπ hker a]
        congr 1
        ring

def expansionHom : A →ₐ[C] PowerSeries C where
  toFun := expansion ρ π hπ hker
  map_zero' := by ext n; simp [expansionCoeff]
  map_one' := by simpa using expansion_algebraMap ρ π hπ hker (1 : C)
  map_add' := expansion_add ρ π hπ hker
  map_mul' := expansion_mul ρ π hπ hker
  commutes' := expansion_algebraMap ρ π hπ hker

@[simp] theorem constantCoeff_expansionHom (a : A) :
    PowerSeries.constantCoeff (expansionHom ρ π hπ hker a) = ρ a := by
  change PowerSeries.constantCoeff (expansion ρ π hπ hker a) = ρ a
  rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply, coeff_expansion, expansionCoeff_zero]

theorem expansionHom_uniformizer : expansionHom ρ π hπ hker π = PowerSeries.X := by
  change expansion ρ π hπ hker π = PowerSeries.X
  rw [expansion_rec, residue_uniformizer ρ π hker, map_zero, zero_add]
  have hr : remainder ρ π hker π = 1 := by
    simpa using remainder_uniformizer_mul ρ π hπ hker (1 : A)
  rw [hr]
  have he : expansion ρ π hπ hker (1 : A) = 1 := by
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
    PowerSeries.order (φ a) = IsDiscreteValuationRing.addVal A a := by
  by_cases ha : a = 0
  · subst a
    rw [map_zero, PowerSeries.order_zero, IsDiscreteValuationRing.addVal_zero]
  · obtain ⟨n, u, rfl⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible ha hπ
    rw [map_mul, map_pow, hφπ, PowerSeries.order_mul, PowerSeries.order_X_pow,
      PowerSeries.order_zero_of_isUnit (u.isUnit.map φ), zero_add,
      IsDiscreteValuationRing.addVal_def' u hπ]

theorem injective (φ : A →+* PowerSeries C) (π : A)
    (hπ : Irreducible π) (hφπ : φ π = PowerSeries.X) : Function.Injective φ := by
  intro a b hab
  have hz : φ (a - b) = 0 := by rw [map_sub, hab, sub_self]
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
    RingHom.ker (residueCoefficientMap C A).toRingHom = IsLocalRing.maximalIdeal A := by
  ext a
  change (residueCoefficientEquiv C A).symm (IsLocalRing.residue A a) = 0 ↔
    a ∈ IsLocalRing.maximalIdeal A
  rw [map_eq_zero_iff _ (AlgEquiv.injective _)]
  exact IsLocalRing.residue_eq_zero_iff a

def uniformizer : A := Classical.choose (IsDiscreteValuationRing.exists_irreducible A)

theorem uniformizer_irreducible : Irreducible (uniformizer A) :=
  Classical.choose_spec (IsDiscreteValuationRing.exists_irreducible A)

theorem residueCoefficientMap_ker_span :
    RingHom.ker (residueCoefficientMap C A).toRingHom = Ideal.span {uniformizer A} := by
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
    FormalLogJet.liftSeries m f = f.toMvPowerSeries (0 : Fin (m+1)) := by
  classical
  let e : Unit ↪ Fin (m+1) := ⟨fun _ => 0, fun a b _ => Subsingleton.elim a b⟩
  ext d
  rw [FormalLogJet.coeff_liftSeries]
  change (if d.tail = 0 then PowerSeries.coeff (d 0) f else 0) = coeff d (rename e f)
  by_cases ht : d.tail = 0
  · rw [ite_eq_left ht]
    have hd : d = Finsupp.single 0 (d 0) := by
      calc
        d = Finsupp.cons (d 0) d.tail := (Finsupp.cons_tail d).symm
        _ = Finsupp.single 0 (d 0) := by rw [ht, Finsupp.cons_zero_eq_single_zero]
    have he : Finsupp.embDomain e (Finsupp.single () (d 0)) = Finsupp.single 0 (d 0) := by
      rw [Finsupp.embDomain_single]
      rfl
    conv_rhs => rw [hd, ← he, coeff_embDomain_rename]
    rfl
  · rw [ite_eq_right ht]
    symm
    apply coeff_rename_eq_zero
    rintro ⟨x, hx⟩
    have hx' : x = Finsupp.single () (x ()) := by ext; simp
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
    (ht : ∀ i, PowerSeries.constantCoeff (tail i) = 0) : HasSubst (shiftVars tail) := by
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
    shiftMap tail ht (X 0) = X 0 := by
  rw [shiftMap, substAlgHom_X]
  rfl

@[simp] theorem shiftMap_X_succ {m : ℕ} (tail : Fin m → PowerSeries R)
    (ht : ∀ i, PowerSeries.constantCoeff (tail i) = 0) (i : Fin m) :
    shiftMap tail ht (X i.succ) = X i.succ + (tail i).toMvPowerSeries 0 := by
  rw [shiftMap, substAlgHom_X]
  rfl

@[simp] theorem shiftMap_toMvPowerSeries {m : ℕ} (tail : Fin m → PowerSeries R)
    (ht : ∀ i, PowerSeries.constantCoeff (tail i) = 0) (f : PowerSeries R) :
    shiftMap tail ht (f.toMvPowerSeries (0 : Fin (m+1))) = f.toMvPowerSeries 0 := by
  rw [shiftMap, substAlgHom_apply, PowerSeries.subst_toMvPowerSeries (shiftVars_hasSubst tail ht)]
  change PowerSeries.subst (X (0 : Fin (m+1))) f = f.toMvPowerSeries 0
  exact PowerSeries.toMvPowerSeries_eq_subst.symm

@[simp] theorem shiftMap_liftSeries {m : ℕ} (tail : Fin m → PowerSeries R)
    (ht : ∀ i, PowerSeries.constantCoeff (tail i) = 0) (f : PowerSeries R) :
    shiftMap tail ht (FormalLogJet.liftSeries m f) = FormalLogJet.liftSeries m f := by
  rw [liftSeries_eq_toMvPowerSeries, shiftMap_toMvPowerSeries]

@[simp] theorem shiftMap_apply {m : ℕ} (tail : Fin m → PowerSeries R)
    (ht : ∀ i, PowerSeries.constantCoeff (tail i) = 0) (f) :
    shiftMap tail ht f = subst (shiftVars tail) f := substAlgHom_apply _ _

theorem shiftMap_inverse {m : ℕ} (s t : Fin m → PowerSeries R)
    (hs : ∀ i, PowerSeries.constantCoeff (s i) = 0)
    (ht : ∀ i, PowerSeries.constantCoeff (t i) = 0)
    (hst : ∀ i, s i + t i = 0) (f : MvPowerSeries (Fin (m+1)) R) :
    shiftMap s hs (shiftMap t ht f) = f := by
  simp only [shiftMap_apply]
  rw [subst_comp_subst_apply (shiftVars_hasSubst t ht) (shiftVars_hasSubst s hs)]
  have hvars : (fun i => subst (shiftVars s) (shiftVars t i)) = X := by
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
    MvPowerSeries (Fin (m+1)) R ≃ₐ[R] MvPowerSeries (Fin (m+1)) R := by
  let hn : ∀ i, PowerSeries.constantCoeff (-tail i) = 0 := by simp [ht]
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
    ∏ i ∈ s, f i ∈ rationalWeightedIdeal v hv (∑ i ∈ s, c i) := by
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
    subst a f ∈ rationalWeightedIdeal v hv H := by
  classical
  intro d hd
  rw [coeff_subst ha]
  apply finsum_eq_zero_of_forall_eq_zero
  intro e
  by_cases he : coeff e f = 0
  · rw [he, zero_smul]
  have hHe : H ≤ Finsupp.weight w e := le_of_not_gt (fun h => he (hf e h))
  have hprod : e.prod (fun i n => a i ^ n) ∈
      rationalWeightedIdeal v hv (Finsupp.weight w e) := by
    rw [Finsupp.prod, Finsupp.weight_apply, Finsupp.sum]
    apply rationalWeightedIdeal_prod
    intro i hi
    have hp := Ideal.pow_mem_pow (hweight i) (e i)
    have hh := ideal_pow_le_rationalWeightedIdeal v hv
      (rationalWeightedIdeal v hv (w i)) (w i) le_rfl (e i) hp
    simpa only [nsmul_eq_mul] using hh
  rw [hprod d (hd.trans_le hHe), smul_zero]

theorem X_mem_rationalWeightedIdeal {σ : Type*} (v : σ → ℚ) (hv : ∀ i, 0 ≤ v i)
    (i : σ) : (X i : MvPowerSeries σ R) ∈ rationalWeightedIdeal v hv (v i) := by
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
    shiftMap tail ht f ∈ rationalWeightedIdeal v hv H := by
  rw [shiftMap_apply]
  apply subst_mem_rationalWeightedIdeal v v hv hv _ (shiftVars_hasSubst tail ht) _ H f hf
  intro i
  cases i using Fin.cases with
  | zero => exact X_mem_rationalWeightedIdeal v hv 0
  | succ i => exact Ideal.add_mem _ (X_mem_rationalWeightedIdeal v hv i.succ) (hweight i)

theorem rationalCoefficientPacket_eq_iff {σ : Type*} (v : σ → ℚ)
    (hv : ∀ i, 0 ≤ v i) (H : ℚ) (f g : MvPowerSeries σ R) :
    rationalCoefficientPacket v H f = rationalCoefficientPacket v H g ↔
      f - g ∈ rationalWeightedIdeal v hv H := by
  constructor
  · intro h d hd
    exact sub_eq_zero.mpr (congrFun h ⟨d,hd⟩)
  · intro h
    funext d
    exact sub_eq_zero.mp (h d.val d.property)

theorem rationalCoefficientPacket_surjective {σ : Type*} (v : σ → ℚ) (H : ℚ) :
    Function.Surjective (rationalCoefficientPacket (R := R) v H) := by
  classical
  intro p
  refine ⟨fun d => if hd : Finsupp.weight v d < H then p ⟨d,hd⟩ else 0, ?_⟩
  funext d
  exact dite_eq_left d.property

@[simp] theorem shiftEquiv_symm_apply {m : ℕ} (tail : Fin m → PowerSeries R)
    (ht : ∀ i, PowerSeries.constantCoeff (tail i) = 0) (f) :
    (shiftEquiv tail ht).symm f =
      shiftMap (fun i => -tail i) (by simp [ht]) f := rfl

theorem shiftEquiv_mem_iff {m : ℕ} (tail : Fin m → PowerSeries R)
    (ht : ∀ i, PowerSeries.constantCoeff (tail i) = 0)
    (v : Fin (m+1) → ℚ) (hv : ∀ i, 0 ≤ v i)
    (hweight : ∀ i, (tail i).toMvPowerSeries (0 : Fin (m+1)) ∈
      rationalWeightedIdeal v hv (v i.succ)) (H : ℚ) (f) :
    shiftEquiv tail ht f ∈ rationalWeightedIdeal v hv H ↔
      f ∈ rationalWeightedIdeal v hv H := by
  have hn : ∀ i, (-tail i).toMvPowerSeries (0 : Fin (m+1)) ∈
      rationalWeightedIdeal v hv (v i.succ) := by
    intro i
    rw [map_neg]
    intro d hd
    rw [map_neg, hweight i d hd, neg_zero]
  constructor
  · intro hf
    have h := shiftMap_mem_rationalWeightedIdeal (fun i => -tail i)
      (by simp [ht]) v hv hn H _ hf
    change (shiftEquiv tail ht).symm (shiftEquiv tail ht f) ∈ _ at h
    simpa only [AlgEquiv.symm_apply_apply] using h
  · exact shiftMap_mem_rationalWeightedIdeal tail ht v hv hweight H f

noncomputable def logTail (T : ℕ) : PowerSeries ℂ :=
  PowerSeries.log ℂ - (PowerSeries.trunc T (PowerSeries.log ℂ) : PowerSeries ℂ)

@[simp] theorem logTail_constantCoeff (T : ℕ) : PowerSeries.constantCoeff (logTail T) = 0 := by
  simp [logTail, Polynomial.constantCoeff_coe, PowerSeries.coeff_trunc,
    PowerSeries.coeff_log]

theorem coeff_logTail_eq_zero (T n : ℕ) (hn : n < T) :
    PowerSeries.coeff n (logTail T) = 0 := by
  simp [logTail, Polynomial.coeff_coe, PowerSeries.coeff_trunc, hn]

theorem logTail_mem_rationalWeightedIdeal {m : ℕ} (v : Fin (m+1) → ℚ)
    (hv : ∀ i, 0 ≤ v i) (T : ℕ) (H : ℚ) (hT : H ≤ (T : ℚ) * v 0) :
    (logTail T).toMvPowerSeries (0 : Fin (m+1)) ∈ rationalWeightedIdeal v hv H := by
  intro d hd
  rw [← liftSeries_eq_toMvPowerSeries, FormalLogJet.coeff_liftSeries]
  split_ifs with ht
  · have he : d = Finsupp.single 0 (d 0) := by
      calc
        d = Finsupp.cons (d 0) d.tail := (Finsupp.cons_tail d).symm
        _ = Finsupp.single 0 (d 0) := by rw [ht, Finsupp.cons_zero_eq_single_zero]
    have hdeg : (d 0 : ℚ) * v 0 < H := by
      calc
        (d 0 : ℚ) * v 0 = Finsupp.weight v (Finsupp.single 0 (d 0)) := by
          rw [Finsupp.weight_single, nsmul_eq_mul]
        _ = Finsupp.weight v d := congrArg _ he.symm
        _ < H := hd
    apply coeff_logTail_eq_zero
    by_contra hn
    have hcast : (T : ℚ) ≤ d 0 := by exact_mod_cast (Nat.le_of_not_gt hn)
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
      (truncatedFormalJet c T P) = FormalLogJet.formalJet c P := by
  have he : (shiftMap (fun i => logTail (T i)) (fun i => logTail_constantCoeff (T i))).comp
      (truncatedFormalJet c T) = FormalLogJet.formalJet c := by
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
    Function.Surjective (fun a j => rationalCoefficientPacket v H (e (f a j))) := by
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
      Function.Surjective (fun a j => rationalCoefficientPacket v H (f a j)) := by
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
      Function.Surjective (fun a j => rationalCoefficientPacket v H (truncatedFormalJet (c j) T (P a))) := by
  let tail := fun i => logTail (T i)
  let ht := fun i => logTail_constantCoeff (T i)
  let e := shiftEquiv tail ht
  have hw : ∀ i, (tail i).toMvPowerSeries (0 : Fin (m+1)) ∈
      rationalWeightedIdeal v hv (v i.succ) :=
    fun i => logTail_mem_rationalWeightedIdeal v hv (T i) (v i.succ) (hT i)
  have he : ∀ f ∈ rationalWeightedIdeal v hv H, e f ∈ rationalWeightedIdeal v hv H :=
    fun f hf => (shiftEquiv_mem_iff tail ht v hv hw H f).mpr hf
  have hi : ∀ f ∈ rationalWeightedIdeal v hv H, e.symm f ∈ rationalWeightedIdeal v hv H := by
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
    HasSubst (branchCoordinates c y x) := by
  apply hasSubst_of_constantCoeff_zero
  intro i
  have ht : MvPowerSeries.constantCoeff (y-1) = 0 := by
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
    subst a (liftSeries m f) = PowerSeries.subst (a 0) f := by
  rw [liftSeries_eq_toMvPowerSeries, PowerSeries.subst_toMvPowerSeries ha]

theorem formalJet_subst_branch {m : ℕ} (c : Fin m → ℂ) (y : PowerSeries ℂ)
    (x : Fin m → PowerSeries ℂ) (hy : PowerSeries.constantCoeff y = 1)
    (hx : ∀ i, PowerSeries.constantCoeff (x i) = c i)
    (p : PiExponentApprox.FramePolynomial m) :
    subst (branchCoordinates c y x) (formalJet c p) =
      MvPolynomial.aeval (Fin.cases y x) p := by
  let ha := branchCoordinates_hasSubst c y x hy hx
  have heq : (substAlgHom ha).comp (formalJet c) = MvPolynomial.aeval (Fin.cases y x) := by
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
      have hl : substAlgHom ha (formalLog m) = PowerSeries.subst (y-1) (PowerSeries.log ℂ) := by
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
        (PiExponentApprox.polynomialFrameWord m word p)) := by
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
        (PiExponentApprox.polynomialFrameWord m word p))).toNat : ℚ) := by
  have h := polynomialFrameWord_branch_order c y x hy hx v hv μ H hμ p hp hcontact word
  have hn := PowerSeries.order_eq_top.not.mpr hne
  have hh := ENat.toNat_le_toNat h hn
  exact Nat.ceil_le.mp (by simpa using hh)

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
      MvPolynomial.aeval (fun i => DVRBranch.expansion ℂ A (x i)) p := by
  have h : (DVRBranch.expansion ℂ A).comp (MvPolynomial.aeval x) =
      MvPolynomial.aeval (fun i => DVRBranch.expansion ℂ A (x i)) := by
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
    ∀ i, PowerSeries.constantCoeff (coordinates c y x i) = 0 := by
  intro i
  have ht : MvPowerSeries.constantCoeff (DVRBranch.expansion ℂ A y - 1) = 0 := by
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
    ∃ i, coordinates c y x i ≠ 0 := by
  classical
  by_contra hn
  push Not at hn
  have hy : y = 1 := by
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
        (MvPolynomial.aeval (Fin.cases y x) (polynomialFrameWord m word p))).toNat : ℚ) := by
  have heval (q : FramePolynomial m) :
      DVRBranch.expansion ℂ A (MvPolynomial.aeval (Fin.cases y x) q) =
      MvPolynomial.aeval (Fin.cases (DVRBranch.expansion ℂ A y)
        (fun i => DVRBranch.expansion ℂ A (x i))) q := by
    rw [expansion_aeval]
    apply congrArg (fun z => MvPolynomial.aeval z q)
    funext i
    cases i using Fin.cases <;> rfl
  have hne' : MvPolynomial.aeval (Fin.cases (DVRBranch.expansion ℂ A y)
      (fun i => DVRBranch.expansion ℂ A (x i))) (polynomialFrameWord m word p) ≠ 0 := by
    rw [← heval]
    exact (map_ne_zero_iff _ (DVRBranch.expansion_injective ℂ A)).mpr hne
  have hb := polynomialFrameWord_branch_order_toNat c (DVRBranch.expansion ℂ A y)
    (fun i => DVRBranch.expansion ℂ A (x i))
    (by simpa using hy) (fun i => by simpa using hx i)
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
        MvPolynomial.aeval (Fin.cases y x) (polynomialFrameWord m word p)})).toNat : ℚ) := by
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
    (s : Finset σ) (f : σ → K) : v (∏ i ∈ s, f i) = ∑ i ∈ s, v (f i) := by
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
      v (MvPolynomial.aeval x (MvPolynomial.monomial d c)) := by
  classical
  rw [MvPolynomial.aeval_monomial, v.map_mul, Finsupp.prod, valuation_prod]
  have heq : ((-Finsupp.weight w d * D : ℝ) : WithTop ℝ) =
      ∑ i ∈ d.support, d i • ((-w i * D : ℝ) : WithTop ℝ) := by
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
      ∑ i ∈ d.support, v (x i ^ d i) := by
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
    ((-N * D : ℝ) : WithTop ℝ) ≤ v (MvPolynomial.aeval x p) := by
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

def coordinateOrder (v : AddValuation K (WithTop ℤ)) (x : K) : ℤ := by
  classical
  exact if h : x = 0 then 0 else integerOrder v (Units.mk0 x h)

def coordinatePole (v : AddValuation K (WithTop ℤ)) (x : ι → K) (w : ι → ℚ) : ℚ :=
  weightedPole w (fun i => (coordinateOrder v (x i) : ℚ))

@[simp] theorem realValuation_of_ne_zero (v : AddValuation K (WithTop ℤ))
    (x : K) (hx : x ≠ 0) :
    realValuation v x = ((coordinateOrder v x : ℝ) : WithTop ℝ) := by
  rw [coordinateOrder, dite_eq_right hx, realValuation_apply]
  have h : v x = (integerOrder v (Units.mk0 x hx) : WithTop ℤ) :=
    (coe_integerOrder v (Units.mk0 x hx)).symm
  rw [h, WithTop.map_coe]

theorem coordinate_order_lower (v : AddValuation K (WithTop ℤ))
    (x : ι → K) (w : ι → ℚ) (hw : ∀ i, 0 < w i) (i : ι) :
    ((-(w i : ℝ) * (coordinatePole v x w : ℝ) : ℝ) : WithTop ℝ) ≤
      realValuation v (x i) := by
  by_cases hx : x i = 0
  · simp [hx]
  · rw [realValuation_of_ne_zero v (x i) hx]
    apply WithTop.coe_le_coe.mpr
    have h := (div_le_iff₀ (hw i)).mp
      (div_le_weightedPole w (fun j => (coordinateOrder v (x j) : ℚ)) i)
    have hq : -(w i) * coordinatePole v x w ≤ (coordinateOrder v (x i) : ℚ) := by
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
    B * (∑ p ∈ S, μ p) ≤ N * pole.sum (fun _ n => (n : ℝ)) := by
  classical
  let T := S ∪ z.support ∪ pole.support
  have hST : S ⊆ T := by intro p hp; simp [T, hp]
  have hzT : z.support ⊆ T := by intro p hp; simp [T, hp]
  have hpT : pole.support ⊆ T := by intro p hp; simp [T, hp]
  have hzsum : (∑ p ∈ T, (z p : ℝ)) = 0 := by
    have hh := z.sum_of_support_subset hzT (fun _ n => n) (by simp)
    have hi : (∑ p ∈ T, z p) = 0 := hh.symm.trans hz
    exact_mod_cast hi
  have hpsum : (∑ p ∈ T, (pole p : ℝ)) = pole.sum (fun _ n => (n : ℝ)) :=
    (pole.sum_of_support_subset hpT (fun _ n => (n : ℝ)) (by simp)).symm
  calc
    B * (∑ p ∈ S, μ p) = ∑ p ∈ S, B * μ p := Finset.mul_sum _ _ _
    _ ≤ ∑ p ∈ S, ((z p : ℝ) + N * (pole p : ℝ)) := by
      apply Finset.sum_le_sum
      intro p hp
      exact (hlocal p hp).trans (le_add_of_nonneg_right
        (mul_nonneg hN (by exact_mod_cast hpole_nonneg p)))
    _ ≤ ∑ p ∈ T, ((z p : ℝ) + N * (pole p : ℝ)) := by
      apply Finset.sum_le_sum_of_subset_of_nonneg hST
      intro p hp hnot
      have hh := hglobal p
      linarith
    _ = N * pole.sum (fun _ n => (n : ℝ)) := by
      rw [Finset.sum_add_distrib, ← Finset.mul_sum, hzsum, zero_add, hpsum]

theorem coordinatePole_eq_zero {E ι : Type*} [Field E] [Fintype ι]
    (v : AddValuation E (WithTop ℤ)) (x : ι → E) (w : ι → ℚ)
    (hx : ∀ i, coordinateOrder v (x i) = 0) : coordinatePole v x w = 0 := by
  unfold coordinatePole weightedPole
  simp only [hx, Int.cast_zero, neg_zero, zero_div]
  have he : (fun i : Option ι => i.elim 0 (fun _ => (0 : ℚ))) = fun _ => 0 := by
    funext i
    cases i <;> rfl
  rw [he]
  exact Finset.sup'_const _ _

theorem coordinatePole_finite_support {E ι P : Type*} [Field E] [Fintype ι]
    (v : P → AddValuation E (WithTop ℤ)) (x : ι → E) (w : ι → ℚ)
    (hfinite : ∀ i, Set.Finite {p | coordinateOrder (v p) (x i) ≠ 0}) :
    Set.Finite {p | coordinatePole (v p) x w ≠ 0} := by
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
    (f : E) (hf : IsAlgebraic ℂ f) : ∃ c : ℂ, algebraMap ℂ E c = f := by
  have hm : f ∈ algebraicClosure ℂ E := mem_algebraicClosure_iff.mpr hf
  rw [IntermediateField.eq_bot_of_isAlgClosed_of_isAlgebraic (algebraicClosure ℂ E)] at hm
  exact hm

theorem coordinateOrder_constant_eq_zero {E : Type*} [Field E] [Algebra ℂ E]
    (p : NormalizedPlace ℂ E) (c : ℂ) : coordinateOrder p.valuation (algebraMap ℂ E c) = 0 := by
  by_cases hc : c = 0
  · simp [hc, coordinateOrder]
  have hm : algebraMap ℂ E c ≠ 0 := (map_ne_zero_iff _ (algebraMap ℂ E).injective).mpr hc
  rw [coordinateOrder, dite_eq_right hm]
  exact CurveProductFormula.placeOrder_constant_eq_zero p c hc

def coordinateOrderDivisor {E : Type*} [Field E] [Algebra ℂ E]
    (hfinite : ∀ f : E, Transcendental ℂ f → FiniteDimensional (IntermediateField.adjoin ℂ {f}) E)
    (f : E) : NormalizedPlace ℂ E →₀ ℤ := by
  classical
  exact if ht : Transcendental ℂ f then
    letI := hfinite f ht
    CurveProductFormula.principalDivisor f ht
  else 0

@[simp] theorem coordinateOrderDivisor_apply {E : Type*} [Field E] [Algebra ℂ E]
    (hfinite : ∀ f : E, Transcendental ℂ f → FiniteDimensional (IntermediateField.adjoin ℂ {f}) E)
    (f : E) (p : NormalizedPlace ℂ E) :
    coordinateOrderDivisor hfinite f p = coordinateOrder p.valuation f := by
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
    (f : E) : (coordinateOrderDivisor hfinite f).sum (fun _ n => n) = 0 := by
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
    (coordinatePole_finite_support (fun p : NormalizedPlace ℂ E => p.valuation) x w (by
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
    (x : ι → E) (w : ι → ℚ) : 0 ≤ weightedDegree hfinite x w := by
  apply Finset.sum_nonneg
  intro p hp
  change (0 : ℝ) ≤ (coordinatePole p.valuation x w : ℚ)
  exact_mod_cast weightedPole_nonneg w (fun i => (coordinateOrder p.valuation (x i) : ℚ))

theorem constants_real_nonneg {E : Type*} [Field E] [Algebra ℂ E]
    (p : NormalizedPlace ℂ E) (c : ℂ) :
    0 ≤ realValuation p.valuation (algebraMap ℂ E c) := by
  have h := (show Monotone (WithTop.map (fun z : ℤ => (z : ℝ))) from
    (Int.cast_mono (R := ℝ)).withTop_map) (p.constants_nonneg c)
  have hz : WithTop.map (fun z : ℤ => (z : ℝ)) (0 : WithTop ℤ) = (0 : WithTop ℝ) := by
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
      (coordinateOrder p.valuation (MvPolynomial.aeval x f) : ℝ) := by
  have h := PolynomialPoleBound.polynomial_order_lower (realValuation p.valuation) x
    (fun i => (w i : ℝ)) (coordinatePole p.valuation x w : ℝ) N
    (by exact_mod_cast weightedPole_nonneg w (fun i => (coordinateOrder p.valuation (x i) : ℚ)))
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
    B * (∑ p ∈ S, μ p) ≤ N * weightedDegree hfinite x w := by
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
    MvPolynomial.aeval x f = 0 := by
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
    Transcendental ℂ (x - algebraMap ℂ E c) := by
  intro h
  apply hx
  simpa only [sub_add_cancel] using h.add (isAlgebraic_algebraMap c)

theorem exists_transcendental_coordinate (x : ι → E)
    (hx : IntermediateField.adjoin ℂ (Set.range x) = ⊤)
    (hE : ∃ z : E, Transcendental ℂ z) : ∃ i, Transcendental ℂ (x i) := by
  by_contra hn
  push Not at hn
  have hle : IntermediateField.adjoin ℂ (Set.range x) ≤ ⊥ := by
    apply IntermediateField.adjoin_le_iff.mpr
    rintro _ ⟨i, rfl⟩
    obtain ⟨c, hc⟩ := CurveContactSum.exists_constant_of_isAlgebraic (x i) (by
      simpa only [Transcendental, not_not] using hn i)
    exact IntermediateField.mem_bot.mpr ⟨c, hc⟩
  obtain ⟨z, hz⟩ := hE
  have hzbot : z ∈ (⊥ : IntermediateField ℂ E) := hle (by simp [hx])
  obtain ⟨c, hc⟩ := IntermediateField.mem_bot.mp hzbot
  exact hz (hc ▸ isAlgebraic_algebraMap c)

theorem finite_centered (x : ι → E) (a : ι → ℂ)
    (hx : ∃ i, Transcendental ℂ (x i))
    (hfinite : ∀ g : E, Transcendental ℂ g →
      FiniteDimensional (IntermediateField.adjoin ℂ {g}) E) :
    Set.Finite {p : NormalizedPlace ℂ E | Centered x a p} := by
  obtain ⟨i, hi⟩ := hx
  have ht := transcendental_sub_constant hi (a i)
  let := hfinite (x i - algebraMap ℂ E (a i)) ht
  exact (finite_positivePlaces (x i - algebraMap ℂ E (a i)) ht).subset
    (fun p hp => hp i)

theorem finite_centered_family [Finite J] (x : ι → E) (a : J → ι → ℂ)
    (hx : ∃ i, Transcendental ℂ (x i))
    (hfinite : ∀ g : E, Transcendental ℂ g →
      FiniteDimensional (IntermediateField.adjoin ℂ {g}) E) :
    Set.Finite {p : NormalizedPlace ℂ E | ∃ j, Centered x (a j) p} := by
  have he : {p : NormalizedPlace ℂ E | ∃ j, Centered x (a j) p} =
      ⋃ j, {p : NormalizedPlace ℂ E | Centered x (a j) p} := by ext p; simp
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
    (ha : Centered x a p) (i : ι) (c : ℂ) (hc : x i = algebraMap ℂ E c) : c = a i := by
  by_contra hne
  have h := ha i
  rw [hc, ← map_sub, CurveProductFormula.valuation_constant_eq_zero p _ (sub_ne_zero.mpr hne)] at h
  exact lt_irrefl _ h

theorem Centered.coordinate_nonneg {x : ι → E} {a : ι → ℂ} {p : NormalizedPlace ℂ E}
    (ha : Centered x a p) (i : ι) : 0 ≤ p.valuation (x i) := by
  have h := (le_min (ha i).le (p.constants_nonneg (a i))).trans
    (p.valuation.map_add (x i - algebraMap ℂ E (a i)) (algebraMap ℂ E (a i)))
  simpa only [sub_add_cancel] using h

theorem Centered.exists_nonzero_difference (x : ι → E) (a : ι → ℂ)
    (hx : ∃ i, Transcendental ℂ (x i)) :
    ∃ i, x i ≠ algebraMap ℂ E (a i) := by
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
  map_zero' := by ext; exact map_zero _
  map_one' := by ext; exact map_one _
  map_add' _ _ := by ext; exact map_add _ _ _
  map_mul' _ _ := by ext; exact map_mul _ _ _

instance constantsAlgebra (p : NormalizedPlace F E) : Algebra F (ring p) :=
  (constantsHom p).toAlgebra

instance scalarTower (p : NormalizedPlace F E) : IsScalarTower F (ring p) E :=
  IsScalarTower.of_algebraMap_eq (fun _ => rfl)

@[simp] theorem constants_algebraMap (p : NormalizedPlace F E) (c : F) :
    (algebraMap F (ring p) c : E) = algebraMap F E c := rfl

instance valuation_nontrivial (p : NormalizedPlace F E) :
    p.valuation.toValuation.IsNontrivial := by
  obtain ⟨z, hz⟩ := p.normalized
  apply (Valuation.isNontrivial_iff_exists_lt_one _).mpr
  refine ⟨z, z.ne_zero, ?_⟩
  change (0 : WithTop ℤ) < p.valuation (z : E)
  rw [← coe_integerOrder, hz]
  norm_num

instance discreteValuationRing (p : NormalizedPlace F E) :
    IsDiscreteValuationRing (ring p) := by
  let : IsCyclic (Multiplicative (OrderDual (WithTop ℤ)))ˣ :=
    inferInstanceAs (IsCyclic (WithZero (Multiplicative ℤ))ˣ)
  let : IsCyclic (MonoidWithZeroHom.valueGroup (.ofClass p.valuation.toValuation)) := by
    infer_instance
  exact Valuation.valuationSubring_isDiscreteValuationRing p.valuation.toValuation

theorem valuation_eq_fractionAddValuation (p : NormalizedPlace F E) :
    p.valuation = CurveLocalOrder.fractionAddValuation (ring p) E := by
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
    SupportBound ρ N (0 : MvPolynomial σ E) := by
  intro d hd
  simp at hd

theorem supportBound_C (ρ : σ → ℝ) (c : E) :
    SupportBound ρ 0 (MvPolynomial.C c) := by
  intro d hd
  have he : d = 0 := Finset.mem_singleton.mp (MvPolynomial.support_monomial_subset hd)
  subst d
  simp

theorem supportBound_X (ρ : σ → ℝ) (i : σ) :
    SupportBound ρ (ρ i) (MvPolynomial.X i : MvPolynomial σ E) := by
  classical
  intro d hd
  have he : d = Finsupp.single i 1 := by simpa only [MvPolynomial.support_X, Finset.mem_singleton] using hd
  subst d
  simp [Finsupp.weight_single]

theorem SupportBound.add {ρ : σ → ℝ} {N : ℝ} {p q : MvPolynomial σ E}
    (hp : SupportBound ρ N p) (hq : SupportBound ρ N q) : SupportBound ρ N (p + q) := by
  classical
  intro d hd
  rcases Finset.mem_union.mp (MvPolynomial.support_add hd) with h | h
  · exact hp d h
  · exact hq d h

theorem SupportBound.mul {ρ : σ → ℝ} {M N : ℝ} {p q : MvPolynomial σ E}
    (hp : SupportBound ρ M p) (hq : SupportBound ρ N q) : SupportBound ρ (M + N) (p * q) := by
  classical
  intro d hd
  obtain ⟨a, ha, b, hb, rfl⟩ := Finset.mem_add.mp (MvPolynomial.support_mul p q hd)
  simpa only [map_add] using add_le_add (hp a ha) (hq b hb)

theorem SupportBound.pow {ρ : σ → ℝ} {N : ℝ} {p : MvPolynomial σ E}
    (hp : SupportBound ρ N p) (m : ℕ) : SupportBound ρ ((m : ℝ) * N) (p ^ m) := by
  induction m with
  | zero => simpa only [pow_zero, Nat.cast_zero, zero_mul, MvPolynomial.C_1] using supportBound_C ρ (1 : E)
  | succ m ih =>
    simpa only [pow_succ, Nat.cast_add, Nat.cast_one, add_mul, one_mul] using ih.mul hp

theorem supportBound_prod {α : Type*} (s : Finset α) (ρ : σ → ℝ)
    (p : α → MvPolynomial σ E) (N : α → ℝ)
    (hp : ∀ i ∈ s, SupportBound ρ (N i) (p i)) :
    SupportBound ρ (∑ i ∈ s, N i) (∏ i ∈ s, p i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa only [Finset.sum_empty, Finset.prod_empty, MvPolynomial.C_1] using supportBound_C ρ (1 : E)
  | @insert i s hi ih =>
    simp only [Finset.sum_insert hi, Finset.prod_insert hi]
    exact (hp i (Finset.mem_insert_self _ _)).mul (ih (fun j hj => hp j (Finset.mem_insert_of_mem hj)))

theorem supportBound_sum {α : Type*} (s : Finset α) (ρ : σ → ℝ)
    (p : α → MvPolynomial σ E) (N : ℝ)
    (hp : ∀ i ∈ s, SupportBound ρ N (p i)) :
    SupportBound ρ N (∑ i ∈ s, p i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa only [Finset.sum_empty] using supportBound_zero ρ N
  | @insert i s hi ih =>
    rw [Finset.sum_insert hi]
    exact (hp i (Finset.mem_insert_self _ _)).add (ih (fun j hj => hp j (Finset.mem_insert_of_mem hj)))

theorem supportBound_aeval_monomial (ρ : ι → ℝ) (κ : σ → ℝ)
    (g : ι → MvPolynomial σ E) (hg : ∀ i, SupportBound κ (ρ i) (g i))
    (d : ι →₀ ℕ) (c : C) :
    SupportBound κ (Finsupp.weight ρ d) (MvPolynomial.aeval g (MvPolynomial.monomial d c)) := by
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
    SupportBound κ N (MvPolynomial.aeval g p) := by
  classical
  conv_rhs => rw [MvPolynomial.as_sum p, map_sum]
  exact supportBound_sum p.support κ _ N
    (fun d hd => (supportBound_aeval_monomial ρ κ g hg d (p.coeff d)).mono (hp d hd))

noncomputable def sliceMap (A : Finset ι) (b : ι → E) :
    MvPolynomial ι C →ₐ[C] MvPolynomial A E := by
  classical
  exact MvPolynomial.aeval (fun i => if h : i ∈ A then MvPolynomial.X ⟨i, h⟩ else MvPolynomial.C (b i))

@[simp] theorem sliceMap_X_mem (A : Finset ι) (b : ι → E) (i : ι) (hi : i ∈ A) :
    sliceMap (C := C) A b (MvPolynomial.X i) = MvPolynomial.X ⟨i, hi⟩ := by
  classical
  simp [sliceMap, hi]

@[simp] theorem sliceMap_X_notMem (A : Finset ι) (b : ι → E) (i : ι) (hi : i ∉ A) :
    sliceMap (C := C) A b (MvPolynomial.X i) = MvPolynomial.C (b i) := by
  classical
  simp [sliceMap, hi]

@[simp] theorem sliceMap_C (A : Finset ι) (b : ι → E) (c : C) :
    sliceMap A b (MvPolynomial.C c) = MvPolynomial.C (algebraMap C E c) := by
  classical
  simp [sliceMap]

theorem supportBound_sliceMap (A : Finset ι) (b : ι → E)
    (ρ : ι → ℝ) (hρ : ∀ i, 0 ≤ ρ i) (N : ℝ) (p : MvPolynomial ι C)
    (hp : ∀ d ∈ p.support, Finsupp.weight ρ d ≤ N) :
    SupportBound (fun i : A => ρ i) N (sliceMap A b p) := by
  classical
  let g : ι → MvPolynomial A E := fun i =>
    if h : i ∈ A then MvPolynomial.X ⟨i, h⟩ else MvPolynomial.C (b i)
  change SupportBound (fun i : A => ρ i) N (MvPolynomial.aeval g p)
  have hg : ∀ i, SupportBound (fun j : A => ρ j) (ρ i) (g i) := by
    intro i
    dsimp only [g]
    split_ifs with hi
    · exact supportBound_X (E := E) (fun j : A => ρ j) ⟨i, hi⟩
    · exact (supportBound_C (fun j : A => ρ j) (b i)).mono (hρ i)
  exact supportBound_aeval ρ (fun i : A => ρ i) g hg N p hp

theorem supportBound_renameEquiv (e : ι ≃ σ) (ρ : ι → ℝ) (N : ℝ)
    (p : MvPolynomial ι E) (hp : SupportBound ρ N p) :
    SupportBound (fun j => ρ (e.symm j)) N (MvPolynomial.rename e p) := by
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
      (∑ j ∈ d.support, (d j : ℝ) * ρ (A.equivFin.symm j)) ≤ N := by
  have h := supportBound_enumeratedSliceMap A b ρ hρ N p (by
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
    Tendsto (fun x : ℝ => (⌊a * x + b⌋₊ : ℝ) / x) atTop (𝓝 a) := by
  have hy : Tendsto (fun x : ℝ => a * x + b) atTop atTop :=
    tendsto_atTop_add_const_right atTop b (Tendsto.const_mul_atTop ha tendsto_id)
  have hratio : Tendsto (fun x : ℝ => (a * x + b) / x) atTop (𝓝 a) := by
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
    Tendsto (fun x : ℝ => f ⌊a * x + b⌋₊ / x ^ d) atTop (𝓝 (L * a ^ d)) := by
  have hfloor := tendsto_natFloor_affine_atTop ha b
  have h := (hf.comp hfloor).mul ((tendsto_natFloor_affine_div ha b).pow d)
  apply h.congr'
  filter_upwards [hfloor.eventually (eventually_ge_atTop 1)] with x hx
  have hn : (⌊a * x + b⌋₊ : ℝ) ≠ 0 := by
    exact_mod_cast (by omega : ⌊a * x + b⌋₊ ≠ 0)
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
    a ∈ unweightedSimplex d N ↔ ∑ i, a i ≤ N := by
  constructor
  · exact fun h => (Finset.mem_filter.mp h).2
  · intro h
    refine Finset.mem_filter.mpr ⟨Fintype.mem_piFinset.mpr ?_, h⟩
    intro i
    apply Finset.mem_range.mpr
    have := Finset.single_le_sum (fun j _ => Nat.zero_le (a j)) (Finset.mem_univ i)
    omega

theorem card_unweightedSimplex (d N : ℕ) :
    (unweightedSimplex d N).card = (N + d).choose d := by
  classical
  let target : Finset (Fin (d + 1) →₀ ℕ) := Finset.univ.finsuppAntidiag N
  have hc : target.card = (N + d).choose d := by
    rw [Finset.card_finsuppAntidiag_nat_eq_choose]
    simp only [Finset.card_univ, Fintype.card_fin]
    rw [show d + 1 + N - 1 = N + d by omega, Nat.choose_symm_add]
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
    have hs' : b 0 + ∑ i : Fin d, b i.succ = N := by
      simpa only [Fin.sum_univ_succ] using hs
    refine ⟨fun i => b i.succ, mem_unweightedSimplex.mpr (by omega), ?_⟩
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
      atTop (𝓝 (1 / (d.factorial : ℝ))) := by
  have h := (isEquivalent_choose d).div
    (IsEquivalent.refl : (fun N : ℕ => (N : ℝ) ^ d) ~[atTop]
      (fun N : ℕ => (N : ℝ) ^ d))
  apply h.symm.tendsto_nhds
  apply tendsto_const_nhds.congr'
  filter_upwards [eventually_ge_atTop 1] with N hN
  have hn : (N : ℝ) ≠ 0 := by exact_mod_cast (by omega : N ≠ 0)
  change 1 / (d.factorial : ℝ) = ((N : ℝ) ^ d / (d.factorial : ℝ)) / (N : ℝ) ^ d
  field_simp

theorem tendsto_choose_add_normalized (d c : ℕ) :
    Tendsto (fun N : ℕ => ((N + c).choose d : ℝ) / (N : ℝ) ^ d)
      atTop (𝓝 (1 / (d.factorial : ℝ))) := by
  have h₁ := (tendsto_choose_normalized d).comp (tendsto_add_atTop_nat c)
  have h₂ : Tendsto (fun N : ℕ => ((N + c : ℕ) : ℝ) / (N : ℝ))
      atTop (𝓝 1) := by
    simpa [Nat.cast_add, add_comm] using
      (tendsto_add_mul_div_add_mul_atTop_nhds (c : ℝ) 0 1 (d := 1) (by norm_num))
  have h := h₁.mul (h₂.pow d)
  simp only [one_pow, mul_one] at h
  apply h.congr'
  filter_upwards [eventually_ge_atTop 1] with N hN
  have hn : ((N + c : ℕ) : ℝ) ≠ 0 := by exact_mod_cast (by omega : N + c ≠ 0)
  simp only [Function.comp_apply]
  rw [div_pow]
  field_simp

theorem tendsto_card_unweightedSimplex (d : ℕ) :
    Tendsto (fun N : ℕ => ((unweightedSimplex d N).card : ℝ) / (N : ℝ) ^ d)
      atTop (𝓝 (1 / (d.factorial : ℝ))) := by
  simpa only [card_unweightedSimplex] using tendsto_choose_add_normalized d d

theorem tendsto_card_unweightedSimplex_add (d c : ℕ) :
    Tendsto (fun N : ℕ => ((unweightedSimplex d (N + c)).card : ℝ) / (N : ℝ) ^ d)
      atTop (𝓝 (1 / (d.factorial : ℝ))) := by
  simpa only [card_unweightedSimplex, Nat.add_assoc] using
    tendsto_choose_add_normalized d (c + d)

end PiExponent

end OAI
end Source0049

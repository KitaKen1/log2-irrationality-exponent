/- Generated rc4 checkpoint for LogTwo.
Modified from the reduced edition: new imports, separate module compilation,
and synchronous elaboration. Original source blocks and notices are retained.
See ../../../THIRD_PARTY_NOTICES.txt and ../../reduction.json.
-/
module
public import LogTwoCheckpoints.Part004
public import LogTwoCheckpoints.Part005
public import LogTwoCheckpoints.Part006
public import LogTwoCheckpoints.Part007
public import Mathlib.Algebra.Order.Antidiag.FinsuppEquiv
public import Mathlib.Analysis.Complex.Polynomial.Basic
public import Mathlib.LinearAlgebra.DirectSum.Finite
public import Mathlib.NumberTheory.BernoulliPolynomials
public import Mathlib.RingTheory.Ideal.KrullsHeightTheorem
public import Mathlib.RingTheory.IntegralClosure.GoingDown
public import Mathlib.RingTheory.KrullDimension.NonZeroDivisors
public import Mathlib.RingTheory.KrullDimension.Polynomial
public import Mathlib.RingTheory.MvPolynomial.Homogeneous
public import Mathlib.RingTheory.Polynomial.HilbertPoly
public import Mathlib.RingTheory.Regular.RegularSequence
public import Mathlib.Tactic
@[expose] public section
set_option Elab.async false

-- Source: OAI/NumberTheory/PiExponent/Polynomials/HomogeneousQuotientDimension.lean
section Source0200
-- Modified in this edition: unused plain lemmas removed; see reduction.json.
/-
Modification notice for the LogTwo project.
Derived from openai/math (Apache-2.0), revision adc7f1241b42e322a6451854ab7e4b4c146bf78a.
Original source: lean/OAI/NumberTheory/PiExponent/Polynomials/HomogeneousQuotientDimension.lean
Changes: Convert module/import declarations to the Lean 4.34 public module format.
See ../THIRD_PARTY_NOTICES.txt for provenance and the recorded changes.
-/

namespace OAI

noncomputable section
namespace PiExponentJets.W25

open MvPolynomial
open PiExponentJets.W64
open DirectSum

attribute [local instance] MvPolynomial.gradedAlgebra

variable {k σ : Type*} [Field k]

def quotientDegreeProjection (I : Ideal (MvPolynomial σ k))
    (hI : I.IsHomogeneous (MvPolynomial.homogeneousSubmodule σ k)) (n : ℕ) :
    (MvPolynomial σ k ⧸ I) →ₗ[k] (MvPolynomial σ k ⧸ I) :=
  (I.restrictScalars k).liftQ
    ((Ideal.Quotient.mkₐ k I).toLinearMap.comp
      (GradedAlgebra.proj (MvPolynomial.homogeneousSubmodule σ k) n)) (by
    intro p hp
    change Ideal.Quotient.mk I
      (GradedAlgebra.proj (MvPolynomial.homogeneousSubmodule σ k) n p) = 0
    apply Ideal.Quotient.eq_zero_iff_mem.mpr
    exact (Ideal.IsHomogeneous.mem_iff
      (MvPolynomial.homogeneousSubmodule σ k) hI).mp hp n)

@[simp] theorem quotientDegreeProjection_mk (I : Ideal (MvPolynomial σ k))
    (hI : I.IsHomogeneous (MvPolynomial.homogeneousSubmodule σ k)) (n : ℕ)
    (p : MvPolynomial σ k) :
    quotientDegreeProjection I hI n (Ideal.Quotient.mk I p) =
      Ideal.Quotient.mk I
        (GradedAlgebra.proj (MvPolynomial.homogeneousSubmodule σ k) n p) := rfl

theorem quotientDegreeProjection_of_mem (I : Ideal (MvPolynomial σ k))
    (hI : I.IsHomogeneous (MvPolynomial.homogeneousSubmodule σ k))
    (n m : ℕ) (x : MvPolynomial σ k ⧸ I) (hx : x ∈ quotientSection I m) :
    quotientDegreeProjection I hI n x = if n = m then x else 0 := by
  obtain ⟨p, hp, rfl⟩ := hx
  change quotientDegreeProjection I hI n (Ideal.Quotient.mk I p) = _
  rw [quotientDegreeProjection_mk, GradedAlgebra.proj_apply]
  by_cases hnm : n = m
  · subst n
    rw [DirectSum.decompose_of_mem_same (MvPolynomial.homogeneousSubmodule σ k) hp]
    simp
  · rw [DirectSum.decompose_of_mem_ne (MvPolynomial.homogeneousSubmodule σ k) hp
      (Ne.symm hnm)]
    simp [hnm]

theorem quotientSection_iSupIndep (I : Ideal (MvPolynomial σ k))
    (hI : I.IsHomogeneous (MvPolynomial.homogeneousSubmodule σ k)) :
    iSupIndep (quotientSection I) := by
  classical
  rw [iSupIndep_iff_finsetSum_eq_zero_imp_eq_zero]
  intro s v hv hsum i hi
  have hcalc : quotientDegreeProjection I hI i (∑ j ∈ s, v j) = v i := by
    rw [map_sum]
    calc
      ∑ j ∈ s, quotientDegreeProjection I hI i (v j) =
          ∑ j ∈ s, if i = j then v j else 0 := by
        apply Finset.sum_congr rfl
        intro j hj
        exact quotientDegreeProjection_of_mem I hI i j (v j) (hv j hj)
      _ = v i := by simp [hi]
  rw [hsum, map_zero] at hcalc
  exact hcalc.symm

theorem quotientSection_iSup_eq_top (I : Ideal (MvPolynomial σ k)) :
    (⨆ n, quotientSection I n) = ⊤ := by
  simp only [quotientSection, ← Submodule.map_iSup]
  rw [(DirectSum.Decomposition.isInternal
    (MvPolynomial.homogeneousSubmodule σ k)).submodule_iSup_eq_top]
  rw [Submodule.map_top]
  exact LinearMap.range_eq_top.mpr (Ideal.Quotient.mkₐ_surjective k I)

theorem quotientSection_isInternal (I : Ideal (MvPolynomial σ k))
    (hI : I.IsHomogeneous (MvPolynomial.homogeneousSubmodule σ k)) :
    DirectSum.IsInternal (quotientSection I) :=
  DirectSum.isInternal_submodule_of_iSupIndep_of_iSup_eq_top
    (quotientSection_iSupIndep I hI) (quotientSection_iSup_eq_top I)

def homogeneousQuotientDirectSumEquiv (I : Ideal (MvPolynomial σ k))
    (hI : I.IsHomogeneous (MvPolynomial.homogeneousSubmodule σ k)) :
    (⨁ n : ℕ, quotientSection I n) ≃ₗ[k] (MvPolynomial σ k ⧸ I) :=
  LinearEquiv.ofBijective (DirectSum.coeLinearMap (quotientSection I))
    (quotientSection_isInternal I hI)

theorem quotientSection_bounded_iSup_eq_top (I : Ideal (MvPolynomial σ k)) (B : ℕ)
    (hzero : ∀ n, B < n → quotientSection I n = ⊥) :
    (⨆ n : Fin (B+1), quotientSection I n.val) = ⊤ := by
  rw [← quotientSection_iSup_eq_top I]
  apply le_antisymm
  · exact iSup_le fun n => le_iSup (quotientSection I) n.val
  · apply iSup_le
    intro n
    by_cases hn : n < B+1
    · exact le_iSup (fun j : Fin (B+1) => quotientSection I j.val) ⟨n, hn⟩
    · rw [hzero n (Nat.lt_of_succ_le (Nat.le_of_not_lt hn))]
      exact bot_le

def boundedHomogeneousQuotientEquiv (I : Ideal (MvPolynomial σ k))
    (hI : I.IsHomogeneous (MvPolynomial.homogeneousSubmodule σ k)) (B : ℕ)
    (hzero : ∀ n, B < n → quotientSection I n = ⊥) :
    (⨁ n : Fin (B+1), quotientSection I n.val) ≃ₗ[k] (MvPolynomial σ k ⧸ I) :=
  LinearEquiv.ofBijective
    (DirectSum.coeLinearMap (fun n : Fin (B+1) => quotientSection I n.val))
    (DirectSum.isInternal_submodule_of_iSupIndep_of_iSup_eq_top
      ((quotientSection_iSupIndep I hI).comp Fin.val_injective)
      (quotientSection_bounded_iSup_eq_top I B hzero))

variable [Finite σ]

end PiExponentJets.W25

end

end OAI
end Source0200

-- Source: OAI/NumberTheory/PiExponent/LocalAlgebra/CumulativeHilbertSections.lean
section Source0201
/-
Modification notice for the LogTwo project.
Derived from openai/math (Apache-2.0), revision adc7f1241b42e322a6451854ab7e4b4c146bf78a.
Original source: lean/OAI/NumberTheory/PiExponent/LocalAlgebra/CumulativeHilbertSections.lean
Changes: Convert module/import declarations to the Lean 4.34 public module format.
See ../THIRD_PARTY_NOTICES.txt for provenance and the recorded changes.
-/

namespace OAI

noncomputable section
namespace PiExponentJets.W25

open MvPolynomial DirectSum
open PiExponentJets.W24 PiExponentJets.W64

attribute [local instance] MvPolynomial.gradedAlgebra

variable {k σ : Type*} [Field k]

theorem restrictTotalDegree_eq_iSup_homogeneous (n : ℕ) :
    restrictTotalDegree σ k n =
      ⨆ j : Fin (n + 1), homogeneousSubmodule σ k j.val := by
  classical
  apply le_antisymm
  · intro p hp
    have hpdegree : p.totalDegree ≤ n := (mem_restrictTotalDegree σ _ _).mp hp
    have hsum : (∑ j ∈ Finset.range (p.totalDegree + 1), homogeneousComponent j p) ∈
        ⨆ j : Fin (n + 1), homogeneousSubmodule σ k j.val := by
      apply Submodule.sum_mem
      intro j hj
      have hjdegree : j ≤ n :=
        (Nat.le_of_lt_succ (Finset.mem_range.mp hj)).trans hpdegree
      exact (le_iSup (fun a : Fin (n + 1) => homogeneousSubmodule σ k a.val)
        ⟨j, Nat.lt_succ_of_le hjdegree⟩) (homogeneousComponent_mem j p)
    simpa only [sum_homogeneousComponent] using hsum
  · apply iSup_le
    intro j p hp
    apply (mem_restrictTotalDegree σ _ _).mpr
    exact (show p.IsHomogeneous j.val from hp).totalDegree_le.trans
      (Nat.le_of_lt_succ j.isLt)

theorem quotientDegreeFiltration_eq_iSup_sections
    (I : Ideal (MvPolynomial σ k)) (n : ℕ) :
    quotientDegreeFiltration I n =
      ⨆ j : Fin (n + 1), quotientSection I j.val := by
  unfold quotientDegreeFiltration quotientSection
  rw [restrictTotalDegree_eq_iSup_homogeneous, Submodule.map_iSup]

theorem cumulativeSectionMap_injective (I : Ideal (MvPolynomial σ k))
    (hI : I.IsHomogeneous (homogeneousSubmodule σ k)) (n : ℕ) :
    Function.Injective
      (DirectSum.coeLinearMap (fun j : Fin (n + 1) => quotientSection I j.val)) :=
  ((quotientSection_iSupIndep I hI).comp Fin.val_injective).dfinsupp_lsum_injective

theorem cumulativeSectionMap_range (I : Ideal (MvPolynomial σ k)) (n : ℕ) :
    LinearMap.range
        (DirectSum.coeLinearMap (fun j : Fin (n + 1) => quotientSection I j.val)) =
      quotientDegreeFiltration I n := by
  rw [DirectSum.range_coeLinearMap, quotientDegreeFiltration_eq_iSup_sections]

def cumulativeHomogeneousQuotientEquiv (I : Ideal (MvPolynomial σ k))
    (hI : I.IsHomogeneous (homogeneousSubmodule σ k)) (n : ℕ) :
    (⨁ j : Fin (n + 1), quotientSection I j.val) ≃ₗ[k]
      quotientDegreeFiltration I n :=
  (LinearEquiv.ofInjective
    (DirectSum.coeLinearMap (fun j : Fin (n + 1) => quotientSection I j.val))
    (cumulativeSectionMap_injective I hI n)).trans
      (LinearEquiv.ofEq _ _ (cumulativeSectionMap_range I n))

@[simp] theorem cumulativeHomogeneousQuotientEquiv_apply
    (I : Ideal (MvPolynomial σ k))
    (hI : I.IsHomogeneous (homogeneousSubmodule σ k)) (n : ℕ)
    (x : ⨁ j : Fin (n + 1), quotientSection I j.val) :
    (cumulativeHomogeneousQuotientEquiv I hI n x : MvPolynomial σ k ⧸ I) =
      DirectSum.coeLinearMap (fun j : Fin (n + 1) => quotientSection I j.val) x := rfl

variable [Finite σ]

theorem quotientDegreeFiltration_finrank_eq_sum_fin
    (I : Ideal (MvPolynomial σ k))
    (hI : I.IsHomogeneous (homogeneousSubmodule σ k)) (n : ℕ) :
    Module.finrank k (quotientDegreeFiltration I n) =
      ∑ j : Fin (n + 1), Module.finrank k (quotientSection I j.val) := by
  rw [← (cumulativeHomogeneousQuotientEquiv I hI n).finrank_eq,
    Module.finrank_directSum]

theorem quotientDegreeFiltration_finrank_eq_sum
    (I : Ideal (MvPolynomial σ k))
    (hI : I.IsHomogeneous (homogeneousSubmodule σ k)) (n : ℕ) :
    Module.finrank k (quotientDegreeFiltration I n) =
      ∑ j ∈ Finset.range (n + 1), Module.finrank k (quotientSection I j) := by
  rw [quotientDegreeFiltration_finrank_eq_sum_fin I hI n]
  exact Fin.sum_univ_eq_sum_range
    (fun j : ℕ => Module.finrank k (quotientSection I j)) (n + 1)

end PiExponentJets.W25

end

end OAI
end Source0201

-- Source: OAI/NumberTheory/PiExponent/Polynomials/PolynomialCumulative.lean
section Source0202
/-
Modification notice for the LogTwo project.
Derived from openai/math (Apache-2.0), revision adc7f1241b42e322a6451854ab7e4b4c146bf78a.
Original source: lean/OAI/NumberTheory/PiExponent/Polynomials/PolynomialCumulative.lean
Changes: Convert module/import declarations to the Lean 4.34 public module format.
See ../THIRD_PARTY_NOTICES.txt for provenance and the recorded changes.
-/

namespace OAI

namespace PiExponentJets.W24

open Polynomial Finset

noncomputable def powerPrefixPolynomial (d : ℕ) : Polynomial ℚ :=
  C ((d + 1 : ℚ)⁻¹) * (Polynomial.bernoulli (d + 1) - C (_root_.bernoulli (d + 1)))

theorem powerPrefixPolynomial_eval (d n : ℕ) :
    (powerPrefixPolynomial d).eval (n : ℚ) = ∑ j ∈ range n, (j : ℚ) ^ d := by
  rw [powerPrefixPolynomial, eval_mul, eval_C, eval_sub, eval_C]
  rw [← Polynomial.sum_range_pow_eq_bernoulli_sub n d]
  have hd : (d + 1 : ℚ) ≠ 0 := by positivity
  exact inv_mul_cancel_left₀ hd _

theorem powerPrefixPolynomial_degree_le (d : ℕ) :
    (powerPrefixPolynomial d).natDegree ≤ d + 1 := by
  apply natDegree_le_iff_coeff_eq_zero.mpr
  intro j hj
  have hj0 : j ≠ 0 := by omega
  simp only [powerPrefixPolynomial, coeff_C_mul, coeff_sub,
    Polynomial.coeff_bernoulli, ite_eq_right (by omega : ¬j ≤ d + 1),
    coeff_C, ite_eq_right hj0, sub_zero, mul_zero]

theorem powerPrefixPolynomial_top_coefficient (d : ℕ) :
    (powerPrefixPolynomial d).coeff (d + 1) = (d + 1 : ℚ)⁻¹ := by
  simp [powerPrefixPolynomial, coeff_C_mul, Polynomial.coeff_bernoulli]

noncomputable def polynomialPrefix (p : Polynomial ℚ) : Polynomial ℚ :=
  ∑ i ∈ range (p.natDegree + 1), C (p.coeff i) * powerPrefixPolynomial i

theorem polynomialPrefix_eval (p : Polynomial ℚ) (n : ℕ) :
    (polynomialPrefix p).eval (n : ℚ) = ∑ j ∈ range n, p.eval (j : ℚ) := by
  simp only [polynomialPrefix, eval_finsetSum, eval_mul, eval_C,
    powerPrefixPolynomial_eval, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j _
  exact (Polynomial.eval_eq_sum_range (p := p) (j : ℚ)).symm

theorem polynomialPrefix_degree_le (p : Polynomial ℚ) :
    (polynomialPrefix p).natDegree ≤ p.natDegree + 1 := by
  apply Polynomial.natDegree_sum_le_of_forall_le
  intro i hi
  exact (natDegree_C_mul_le _ _).trans
    ((powerPrefixPolynomial_degree_le i).trans (by
      have hii := Finset.mem_range.mp hi
      omega))

theorem polynomialPrefix_top_coefficient (p : Polynomial ℚ) :
    (polynomialPrefix p).coeff (p.natDegree + 1) =
      p.leadingCoeff * (p.natDegree + 1 : ℚ)⁻¹ := by
  rw [polynomialPrefix, finsetSum_coeff]
  rw [Finset.sum_eq_single p.natDegree]
  · rw [coeff_C_mul, powerPrefixPolynomial_top_coefficient, coeff_natDegree]
  · intro i hi hne
    have hz : (powerPrefixPolynomial i).coeff (p.natDegree + 1) = 0 :=
      coeff_eq_zero_of_natDegree_lt ((powerPrefixPolynomial_degree_le i).trans_lt (by
        have hii := Finset.mem_range.mp hi
        omega))
    rw [coeff_C_mul, hz, mul_zero]
  · intro h
    exact (h (Finset.mem_range.mpr (Nat.lt_succ_self _))).elim

theorem polynomialPrefix_natDegree (p : Polynomial ℚ) (hp : p ≠ 0) :
    (polynomialPrefix p).natDegree = p.natDegree + 1 := by
  apply natDegree_eq_of_le_of_coeff_ne_zero (polynomialPrefix_degree_le p)
  rw [polynomialPrefix_top_coefficient]
  exact mul_ne_zero (leadingCoeff_ne_zero.mpr hp) (inv_ne_zero (by positivity))

theorem exists_eventual_cumulative_polynomial
    (values : ℕ → ℕ) (p : Polynomial ℚ) (hp0 : p ≠ 0) (N : ℕ)
    (hp : ∀ n : ℕ, N ≤ n → p.eval (n : ℚ) = (values n : ℚ)) :
    ∃ q : Polynomial ℚ, q.natDegree = p.natDegree + 1 ∧
      ∀ n : ℕ, N ≤ n → q.eval (n : ℚ) =
        ((∑ j ∈ range (n + 1), values j : ℕ) : ℚ) := by
  let c : ℚ := (∑ j ∈ range N, (values j : ℚ)) - (polynomialPrefix p).eval (N : ℚ)
  let q : Polynomial ℚ := (polynomialPrefix p).comp (X + C 1) + C c
  have hsum (m : ℕ) (hm : N ≤ m) :
      (polynomialPrefix p).eval (m : ℚ) + c = ∑ j ∈ range m, (values j : ℚ) := by
    induction m, hm using Nat.le_induction with
    | base => simp [c]
    | succ m hm ih =>
        rw [polynomialPrefix_eval, Finset.sum_range_succ,
          ← polynomialPrefix_eval, hp m hm, Finset.sum_range_succ]
        linarith
  refine ⟨q, ?_, ?_⟩
  · simp only [q, natDegree_add_C, natDegree_comp, natDegree_X, mul_one,
      polynomialPrefix_natDegree p hp0]
  · intro n hn
    simpa only [q, eval_add, eval_comp, eval_X, eval_C, Nat.cast_add, Nat.cast_one,
      Nat.cast_sum] using hsum (n + 1) (by omega)

end PiExponentJets.W24

end OAI
end Source0202

-- Source: OAI/NumberTheory/PiExponent/Polynomials/PolynomialGrowthRanks.lean
section Source0203
-- Modified in this edition: unused plain lemmas removed; see reduction.json.
/-
Modification notice for the LogTwo project.
Derived from openai/math (Apache-2.0), revision adc7f1241b42e322a6451854ab7e4b4c146bf78a.
Original source: lean/OAI/NumberTheory/PiExponent/Polynomials/PolynomialGrowthRanks.lean
Changes: Convert module/import declarations to the Lean 4.34 public module format.
See ../THIRD_PARTY_NOTICES.txt for provenance and the recorded changes.
-/

namespace OAI

open scoped BigOperators

namespace PiExponentJets.W32

def exponentBall (d n : ℕ) : Finset (Fin d →₀ ℕ) :=
  (Finset.range (n + 1)).biUnion fun m => (Finset.univ : Finset (Fin d)).finsuppAntidiag m

@[simp] theorem mem_exponentBall (d n : ℕ) (a : Fin d →₀ ℕ) :
    a ∈ exponentBall d n ↔ a.sum (fun _ e => e) ≤ n := by
  simp only [exponentBall, Finset.mem_biUnion, Finset.mem_range,
    Finset.mem_finsuppAntidiag', Finset.subset_univ, and_true]
  constructor
  · rintro ⟨m, hm, hsum⟩
    omega
  · intro h
    exact ⟨a.sum (fun _ e => e), by omega, rfl⟩

theorem card_exponentBall (d n : ℕ) : (exponentBall d n).card = (n + d).choose d := by
  classical
  have hdis : (↑(Finset.range (n + 1)) : Set ℕ).PairwiseDisjoint
      (fun m => (Finset.univ : Finset (Fin d)).finsuppAntidiag m) := by
    intro i hi j hj hij
    apply Finset.disjoint_left.mpr
    intro a hai haj
    have hi' := (Finset.mem_finsuppAntidiag'.mp hai).1
    have hj' := (Finset.mem_finsuppAntidiag'.mp haj).1
    exact hij (hi'.symm.trans hj')
  rw [exponentBall, Finset.card_biUnion hdis]
  simp_rw [Finset.card_finsuppAntidiag_nat_eq_multichoose, Finset.card_univ, Fintype.card_fin]
  exact Nat.sum_range_multichoose n d

theorem finrank_restrictTotalDegree (k : Type*) [Field k] (d n : ℕ) :
    Module.finrank k (MvPolynomial.restrictTotalDegree (Fin d) k n) = (n + d).choose d := by
  classical
  have hs : {a : Fin d →₀ ℕ | a.sum (fun _ e => e) ≤ n} =
      (↑(exponentBall d n) : Set (Fin d →₀ ℕ)) := by
    ext a
    simp only [Set.mem_ofPred_eq, Finset.mem_coe, mem_exponentBall]
  change Module.finrank k (MvPolynomial.restrictSupport k
    {a : Fin d →₀ ℕ | a.sum (fun _ e => e) ≤ n}) = _
  rw [hs, ← card_exponentBall]
  let b : Module.Basis (exponentBall d n) k
      (MvPolynomial.restrictSupport k
        (↑(exponentBall d n) : Set (Fin d →₀ ℕ))) :=
    MvPolynomial.basisRestrictSupport k
      (↑(exponentBall d n) : Set (Fin d →₀ ℕ))
  exact Module.finrank_eq_card_finset_basis b

noncomputable def polynomialGrowth (d : ℕ) : Polynomial ℚ :=
  Polynomial.preHilbertPoly ℚ d 0

@[simp] theorem polynomialGrowth_eval (d n : ℕ) :
    (polynomialGrowth d).eval (n : ℚ) = ((n + d).choose d : ℚ) := by
  simpa [polynomialGrowth] using
    Polynomial.preHilbertPoly_eq_choose_add_sub ℚ d (k := 0) (n := n) (Nat.zero_le (n + d))

theorem polynomialGrowth_eval_finrank (k : Type*) [Field k] (d n : ℕ) :
    (polynomialGrowth d).eval (n : ℚ) =
      (Module.finrank k (MvPolynomial.restrictTotalDegree (Fin d) k n) : ℚ) := by
  rw [polynomialGrowth_eval, finrank_restrictTotalDegree]

@[simp] theorem polynomialGrowth_natDegree (d : ℕ) :
    (polynomialGrowth d).natDegree = d :=
  Polynomial.natDegree_preHilbertPoly ℚ d 0

theorem polynomialGrowth_leadingCoeff (d : ℕ) :
    (polynomialGrowth d).leadingCoeff = (d.factorial : ℚ)⁻¹ :=
  Polynomial.leadingCoeff_preHilbertPoly ℚ d 0

theorem polynomialGrowth_leadingCoeff_pos (d : ℕ) :
    0 < (polynomialGrowth d).leadingCoeff := by
  rw [polynomialGrowth_leadingCoeff]
  positivity

noncomputable def scaledPolynomialGrowth (c d : ℕ) : Polynomial ℚ :=
  Polynomial.C (c : ℚ) * polynomialGrowth d

theorem scaledPolynomialGrowth_natDegree_le (c d : ℕ) :
    (scaledPolynomialGrowth c d).natDegree ≤ d := by
  exact (Polynomial.natDegree_C_mul_le _ _).trans_eq (polynomialGrowth_natDegree d)

theorem scaledPolynomialGrowth_eval_finrank (k : Type*) [Field k]
    (c d n : ℕ) :
    (scaledPolynomialGrowth c d).eval (n : ℚ) =
      (c : ℚ) * (Module.finrank k
        (MvPolynomial.restrictTotalDegree (Fin d) k n) : ℚ) := by
  rw [scaledPolynomialGrowth, Polynomial.eval_C_mul, polynomialGrowth_eval_finrank k]

end PiExponentJets.W32

end OAI
end Source0203

-- Source: OAI/NumberTheory/PiExponent/LocalAlgebra/PrimeHilbertComparison.lean
section Source0204
-- Modified in this edition: unused plain lemmas removed; see reduction.json.
/-
Modification notice for the LogTwo project.
Derived from openai/math (Apache-2.0), revision adc7f1241b42e322a6451854ab7e4b4c146bf78a.
Original source: lean/OAI/NumberTheory/PiExponent/LocalAlgebra/PrimeHilbertComparison.lean
Changes: Convert module/import declarations to the Lean 4.34 public module format.
See ../THIRD_PARTY_NOTICES.txt for provenance and the recorded changes.
-/

namespace OAI

namespace PiExponentJets.W24

open MvPolynomial Polynomial Finset
open PiExponentJets.W64

attribute [local instance] MvPolynomial.gradedAlgebra

variable {k σ : Type*} [Field k] [Fintype σ]

theorem normalization_binomial_lower_bound (s : ℕ)
    (I : Ideal (MvPolynomial σ k))
    (g : MvPolynomial (Fin s) k →ₐ[k] (MvPolynomial σ k ⧸ I))
    (hg : Function.Injective g) (F : Fin s → MvPolynomial σ k)
    (hF : ∀ i, Ideal.Quotient.mk I (F i) = g (MvPolynomial.X i))
    (D : ℕ) (hD : ∀ i, (F i).totalDegree ≤ D) (m : ℕ) :
    (m + s).choose s ≤ Module.finrank k (quotientDegreeFiltration I (D * m)) := by
  let L : restrictTotalDegree (Fin s) k m →ₗ[k]
      quotientDegreeFiltration I (D * m) :=
    { toFun := fun p => ⟨g p, by
        simpa only [Nat.mul_comm D m] using
          normalization_mem_quotientDegreeFiltration I g F hF D hD m p
            ((mem_restrictTotalDegree _ _ _).mp p.property)⟩
      map_add' := fun p q => Subtype.ext (g.map_add p q)
      map_smul' := fun c p => Subtype.ext (g.toLinearMap.map_smul c p) }
  rw [← W32.finrank_restrictTotalDegree k s m]
  exact LinearMap.finrank_le_finrank_of_injective (f := L)
    (fun p q h => Subtype.ext (hg (congrArg Subtype.val h)))

theorem normalization_binomial_lower_growth (s : ℕ)
    (I : Ideal (MvPolynomial σ k))
    (g : MvPolynomial (Fin s) k →ₐ[k] (MvPolynomial σ k ⧸ I))
    (hg : Function.Injective g) :
    ∃ D : ℕ, 0 < D ∧ ∀ m : ℕ,
      (m + s).choose s ≤ Module.finrank k (quotientDegreeFiltration I (D * m)) := by
  classical
  choose F hF using fun i : Fin s => Ideal.Quotient.mk_surjective (g (MvPolynomial.X i))
  let D := max (Finset.univ.sup fun i => (F i).totalDegree) 1
  have hD : ∀ i, (F i).totalDegree ≤ D := fun i =>
    (Finset.le_sup (f := fun j : Fin s => (F j).totalDegree)
      (Finset.mem_univ i)).trans (le_max_left _ _)
  exact ⟨D, lt_of_lt_of_le Nat.zero_lt_one (le_max_right _ _),
    normalization_binomial_lower_bound s I g hg F hF D hD⟩

theorem prime_quotientDegreeFiltration_finrank_pos
    (P : Ideal (MvPolynomial σ k)) [P.IsPrime]
    (hP : P.IsHomogeneous (homogeneousSubmodule σ k))
    (i : σ) (hi : MvPolynomial.X i ∉ P) (n : ℕ) :
    0 < Module.finrank k (quotientDegreeFiltration P n) := by
  rw [W25.quotientDegreeFiltration_finrank_eq_sum P hP n]
  exact (W27.prime_quotientSection_finrank_pos P i hi 0).trans_le
    (Finset.single_le_sum (s := Finset.range (n + 1)) (a := 0)
      (f := fun j => Module.finrank k (quotientSection P j))
      (fun j _ => Nat.zero_le _) (Finset.mem_range.mpr (Nat.zero_lt_succ n)))

theorem prime_hilbert_natDegree_add_one_eq_krullDim
    (P : Ideal (MvPolynomial σ k)) [P.IsPrime]
    (hP : P.IsHomogeneous (homogeneousSubmodule σ k))
    (i : σ) (hi : MvPolynomial.X i ∉ P)
    (p : Polynomial ℚ) (N : ℕ)
    (hp : ∀ n : ℕ, N ≤ n → p.eval (n : ℚ) =
      (Module.finrank k (quotientSection P n) : ℚ)) :
    (p.natDegree + 1 : WithBot ℕ∞) = ringKrullDim (MvPolynomial σ k ⧸ P) := by
  have hpl : 0 < p.leadingCoeff :=
    W27.polynomial_leadingCoeff_pos_of_eventually_pos p N (by
      intro n hn
      rw [hp n hn]
      exact_mod_cast W27.prime_quotientSection_finrank_pos P i hi n)
  have hp0 : p ≠ 0 := leadingCoeff_ne_zero.mp (ne_of_gt hpl)
  obtain ⟨q, hqd, hq⟩ := exists_eventual_cumulative_polynomial
    (fun n => Module.finrank k (quotientSection P n)) p hp0 N hp
  have hqv (n : ℕ) (hn : N ≤ n) :
      q.eval (n : ℚ) = (Module.finrank k (quotientDegreeFiltration P n) : ℚ) := by
    rw [hq n hn, W25.quotientDegreeFiltration_finrank_eq_sum P hP n]
  have hql : 0 < q.leadingCoeff :=
    W27.polynomial_leadingCoeff_pos_of_eventually_pos q N (by
      intro n hn
      rw [hqv n hn]
      exact_mod_cast prime_quotientDegreeFiltration_finrank_pos P hP i hi n)
  obtain ⟨s, g, hg, hfin, hdim⟩ :=
    exists_finite_normalization_with_dimension k (MvPolynomial σ k ⧸ P)
  obtain ⟨D, hD, hlo⟩ := normalization_binomial_lower_growth s P g hg
  obtain ⟨C, E, hC, hup⟩ := W29.finite_normalization_upper_growth P g hfin
  have hdeg : q.natDegree = s := natDegree_eq_of_polynomial_growth_bounds
      q (W32.polynomialGrowth s) (W32.scaledPolynomialGrowth C s) s
      hql (W32.polynomialGrowth_leadingCoeff_pos s)
      (W32.polynomialGrowth_natDegree s) (W32.scaledPolynomialGrowth_natDegree_le C s)
      (D : ℚ) 0 (C : ℚ) (E : ℚ) N (by
        intro n hn
        have hDn : N ≤ D * n := hn.trans (by nlinarith)
        rw [add_zero, ← Nat.cast_mul, hqv (D * n) hDn, W32.polynomialGrowth_eval]
        exact_mod_cast hlo n) (by
        intro n hn
        rw [hqv n hn, ← Nat.cast_mul, ← Nat.cast_add,
          W32.scaledPolynomialGrowth_eval_finrank k C s (C * n + E)]
        exact_mod_cast hup n)
  rw [hdim, ← hdeg, hqd]
  norm_cast

end PiExponentJets.W24

end OAI
end Source0204

-- Source: OAI/NumberTheory/PiExponent/LocalAlgebra/CompleteIntersectionComponentBound.lean
section Source0205
-- Modified in this edition: unused plain lemmas removed; see reduction.json.
/-
Modification notice for the LogTwo project.
Derived from openai/math (Apache-2.0), revision adc7f1241b42e322a6451854ab7e4b4c146bf78a.
Original source: lean/OAI/NumberTheory/PiExponent/LocalAlgebra/CompleteIntersectionComponentBound.lean
Changes: Convert module/import declarations to the Lean 4.34 public module format.
See ../THIRD_PARTY_NOTICES.txt for provenance and the recorded changes.
-/

namespace OAI

namespace PiExponentJets.W22

open PiExponentJets.W64
open scoped BigOperators
attribute [local instance] MvPolynomial.gradedAlgebra

variable {k σ : Type*} [Field k] [Fintype σ]

theorem actualHP_regular_sequence
    (rs : List (MvPolynomial σ k)) (degrees : Fin rs.length → ℕ)
    (hhom : ∀ i : Fin rs.length, rs[i].IsHomogeneous (degrees i))
    (hreg : RingTheory.Sequence.IsRegular (MvPolynomial σ k) rs)
    (hlen : rs.length < Fintype.card σ)
    (hI : (Ideal.ofList rs).IsHomogeneous (MvPolynomial.homogeneousSubmodule σ k)) :
    actualHP (Ideal.ofList rs) hI = regularSequenceHilbertPolynomial rs degrees := by
  apply actualHP_unique _ hI _
    (rationalDegreePolynomial (degreeAt degrees) rs.length).natDegree
  intro n hn
  exact regularSequenceHilbertPolynomial_eventually_exact
    (lt_of_le_of_lt (Nat.zero_le _) hlen) rs degrees hhom hreg hlen.le n hn

omit [Fintype σ] in
theorem regular_degreeAt_product_ne_zero
    (rs : List (MvPolynomial σ k)) (degrees : Fin rs.length → ℕ)
    (hhom : ∀ i : Fin rs.length, rs[i].IsHomogeneous (degrees i))
    (hreg : RingTheory.Sequence.IsRegular (MvPolynomial σ k) rs) :
    (∏ i ∈ Finset.range rs.length, degreeAt degrees i : ℕ) ≠ 0 := by
  classical
  apply Finset.prod_ne_zero_iff.mpr
  intro i hi
  have hi' := Finset.mem_range.mp hi
  simp only [degreeAt, dite_eq_left hi']
  exact Nat.ne_of_gt (PiExponentSiegel.W20.regular_homogeneous_degrees_pos
    rs degrees hhom hreg ⟨i, hi'⟩)

theorem actualHP_regular_sequence_natDegree
    (rs : List (MvPolynomial σ k)) (degrees : Fin rs.length → ℕ)
    (hhom : ∀ i : Fin rs.length, rs[i].IsHomogeneous (degrees i))
    (hreg : RingTheory.Sequence.IsRegular (MvPolynomial σ k) rs)
    (hlen : rs.length < Fintype.card σ)
    (hI : (Ideal.ofList rs).IsHomogeneous (MvPolynomial.homogeneousSubmodule σ k)) :
    (actualHP (Ideal.ofList rs) hI).natDegree = Fintype.card σ - rs.length - 1 := by
  rw [actualHP_regular_sequence rs degrees hhom hreg hlen hI]
  have hp : (rationalDegreePolynomial (degreeAt degrees) rs.length).eval 1 ≠ 0 := by
    rw [rationalDegreePolynomial_eval_one]
    exact_mod_cast regular_degreeAt_product_ne_zero rs degrees hhom hreg
  exact (hilbertPolynomial_degree_and_leading _ _ (Nat.sub_pos_of_lt hlen) hp).1

theorem actualMultiplicity_regular_sequence
    (rs : List (MvPolynomial σ k)) (degrees : Fin rs.length → ℕ)
    (hhom : ∀ i : Fin rs.length, rs[i].IsHomogeneous (degrees i))
    (hreg : RingTheory.Sequence.IsRegular (MvPolynomial σ k) rs)
    (hlen : rs.length < Fintype.card σ)
    (hI : (Ideal.ofList rs).IsHomogeneous (MvPolynomial.homogeneousSubmodule σ k)) :
    actualMultiplicity (Ideal.ofList rs) hI (actualHP (Ideal.ofList rs) hI).natDegree =
      (∏ i ∈ Finset.range rs.length, degreeAt degrees i : ℕ) := by
  rw [actualHP_regular_sequence_natDegree rs degrees hhom hreg hlen hI]
  unfold actualMultiplicity
  rw [actualHP_regular_sequence rs degrees hhom hreg hlen hI]
  exact regularSequenceHilbertPolynomial_multiplicity rs degrees hlen

end PiExponentJets.W22

end OAI
end Source0205

-- Source: OAI/NumberTheory/PiExponent/LocalAlgebra/PrimeHypersurfaceDimension.lean
section Source0206
-- Modified in this edition: unused plain lemmas removed; see reduction.json.
/-
Modification notice for the LogTwo project.
Derived from openai/math (Apache-2.0), revision adc7f1241b42e322a6451854ab7e4b4c146bf78a.
Original source: lean/OAI/NumberTheory/PiExponent/LocalAlgebra/PrimeHypersurfaceDimension.lean
Changes: Convert module/import declarations to the Lean 4.34 public module format.
See ../THIRD_PARTY_NOTICES.txt for provenance and the recorded changes.
-/

namespace OAI

namespace PiExponentJets.W24

open scoped nonZeroDivisors

section QuotientDimension

variable {R : Type*} [CommRing R]

theorem proper_prime_cut_dimension_succ_le
    (P Q : Ideal R) [P.IsPrime] (f : R)
    (hfP : f ∉ P) (hPQ : P ≤ Q) (hfQ : f ∈ Q) :
    ringKrullDim (R ⧸ Q) + 1 ≤ ringKrullDim (R ⧸ P) := by
  let g : (R ⧸ P) →+* (R ⧸ Q) := Ideal.Quotient.factor hPQ
  have hf0 : Ideal.Quotient.mk P f ≠ 0 := by
    exact fun h => hfP (Ideal.Quotient.eq_zero_iff_mem.mp h)
  have hreg : Ideal.Quotient.mk P f ∈ (R ⧸ P)⁰ :=
    mem_nonZeroDivisors_iff_ne_zero.mpr hf0
  apply ringKrullDim_succ_le_of_surjective g (Ideal.Quotient.factor_surjective hPQ) hreg
  exact Ideal.Quotient.eq_zero_iff_mem.mpr hfQ

theorem proper_prime_cut_dimension_le
    (P Q : Ideal R) [P.IsPrime] (f : R)
    (hfP : f ∉ P) (hPQ : P ≤ Q) (hfQ : f ∈ Q)
    (s : ℕ) (hdim : ringKrullDim (R ⧸ P) = (s : WithBot ℕ∞) + 2) :
    ringKrullDim (R ⧸ Q) ≤ (s : WithBot ℕ∞) + 1 := by
  apply ENat.WithBot.add_le_add_one_right_iff.mp
  have h := proper_prime_cut_dimension_succ_le P Q f hfP hPQ hfQ
  simpa only [hdim, add_assoc, one_add_one_eq_two] using h

end QuotientDimension

variable {R : Type*} [CommRing R] [IsNoetherianRing R]

theorem proper_prime_cut_relative_height_eq_one
    (P Q : Ideal R) [P.IsPrime] (f : R) (hfP : f ∉ P)
    (hQ : Q ∈ (P ⊔ Ideal.span {f}).minimalPrimes) :
    (Q.map (Ideal.Quotient.mk P)).height = 1 := by
  have : Q.IsPrime := hQ.1.1
  have hPQ : P ≤ Q := le_sup_left.trans hQ.1.2
  have hfQ : f ∈ Q :=
    (Ideal.span_singleton_le_iff_mem Q).mp (le_sup_right.trans hQ.1.2)
  have : (Q.map (Ideal.Quotient.mk P)).IsPrime :=
    Ideal.map_isPrime_of_surjective Ideal.Quotient.mk_surjective (by
      rwa [Ideal.mk_ker])
  have hne : Q.map (Ideal.Quotient.mk P) ≠ ⊥ := by
    intro h
    have hQP : Q ≤ P := by
      simpa only [Ideal.mk_ker] using
        (Ideal.map_eq_bot_iff_le_ker (Ideal.Quotient.mk P)).mp h
    exact hfP (hQP hfQ)
  have hlo : 1 ≤ (Q.map (Ideal.Quotient.mk P)).height := by
    have hlt : (⊥ : Ideal (R ⧸ P)) < Q.map (Ideal.Quotient.mk P) :=
      bot_lt_iff_ne_bot.mpr hne
    have h := Ideal.height_add_one_le_of_lt_of_isPrime hlt
    simpa only [Ideal.height_bot, zero_add] using h
  exact le_antisymm (Ideal.map_height_le_one_of_mem_minimalPrimes hQ) hlo

omit [IsNoetherianRing R] in
theorem minimal_proper_prime_cut_dimension_le
    (P Q : Ideal R) [P.IsPrime] (f : R) (hfP : f ∉ P)
    (hQ : Q ∈ (P ⊔ Ideal.span {f}).minimalPrimes)
    (s : ℕ) (hdim : ringKrullDim (R ⧸ P) = (s : WithBot ℕ∞) + 2) :
    ringKrullDim (R ⧸ Q) ≤ (s : WithBot ℕ∞) + 1 :=
  proper_prime_cut_dimension_le P Q f hfP (le_sup_left.trans hQ.1.2)
    ((Ideal.span_singleton_le_iff_mem Q).mp (le_sup_right.trans hQ.1.2)) s hdim

end PiExponentJets.W24

end OAI
end Source0206

-- Source: OAI/NumberTheory/PiExponent/LocalAlgebra/QuotientLocalizedLength.lean
section Source0207
-- Modified in this edition: unused plain lemmas removed; see reduction.json.
/-
Modification notice for the LogTwo project.
Derived from openai/math (Apache-2.0), revision adc7f1241b42e322a6451854ab7e4b4c146bf78a.
Original source: lean/OAI/NumberTheory/PiExponent/LocalAlgebra/QuotientLocalizedLength.lean
Changes: Convert module/import declarations to the Lean 4.34 public module format.
See ../THIRD_PARTY_NOTICES.txt for provenance and the recorded changes.
-/

namespace OAI

noncomputable section
namespace PiExponentSiegel.W23

theorem intrinsic_length_eq_of_ringEquiv {R S : Type*} [CommRing R] [CommRing S]
    (e : R ≃+* S) : Module.length R R = Module.length S S := by
  let : RingHomSurjective e.toRingHom := ⟨e.surjective⟩
  let f : R →ₛₗ[e.toRingHom] S :=
    { toFun := e
      map_add' := e.map_add'
      map_smul' := by
        intro r x
        exact e.map_mul' r x }
  exact PiExponentJets.W22.length_eq_of_semilinear_bijective
    e.toRingHom f e.bijective

theorem quotient_module_length_eq_intrinsic {R : Type*} [CommRing R] (I : Ideal R) :
    Module.length R (R ⧸ I) = Module.length (R ⧸ I) (R ⧸ I) := by
  have hq : Function.Surjective (algebraMap R (R ⧸ I)) := Ideal.Quotient.mk_surjective
  exact Module.length_eq_of_surjective (M := R ⧸ I) hq

variable {A : Type*} [CommRing A] (I P : Ideal A) [P.IsPrime] (hI : I ≤ P)

theorem quotient_localized_length_eq :
    Module.length (Localization.AtPrime P)
      (Localization.AtPrime P ⧸ parameterLocalizedIdeal I P) =
    Module.length (Localization.AtPrime (quotientParameterPrime I P hI))
      (Localization.AtPrime (quotientParameterPrime I P hI)) := by
  calc
    Module.length (Localization.AtPrime P)
        (Localization.AtPrime P ⧸ parameterLocalizedIdeal I P) =
      Module.length (Localization.AtPrime P ⧸ parameterLocalizedIdeal I P)
        (Localization.AtPrime P ⧸ parameterLocalizedIdeal I P) :=
      quotient_module_length_eq_intrinsic (parameterLocalizedIdeal I P)
    _ = Module.length (Localization.AtPrime (quotientParameterPrime I P hI))
        (Localization.AtPrime (quotientParameterPrime I P hI)) :=
      intrinsic_length_eq_of_ringEquiv (localizationQuotientParametersEquiv I P hI)

theorem quotient_localized_length_eq_explicit :
    Module.length (Localization.AtPrime P)
      (Localization.AtPrime P ⧸ I.map (algebraMap A (Localization.AtPrime P))) =
    Module.length (Localization.AtPrime (quotientParameterPrime I P hI))
      (Localization.AtPrime (quotientParameterPrime I P hI)) :=
  quotient_localized_length_eq I P hI

end PiExponentSiegel.W23

end

end OAI
end Source0207

-- Source: OAI/NumberTheory/PiExponent/LocalAlgebra/AffineClosedPointLocalization.lean
section Source0208
-- Modified in this edition: unused plain lemmas removed; see reduction.json.
/-
Modification notice for the LogTwo project.
Derived from openai/math (Apache-2.0), revision adc7f1241b42e322a6451854ab7e4b4c146bf78a.
Original source: lean/OAI/NumberTheory/PiExponent/LocalAlgebra/AffineClosedPointLocalization.lean
Changes: Convert module/import declarations to the Lean 4.34 public module format.
See ../THIRD_PARTY_NOTICES.txt for provenance and the recorded changes.
-/

namespace OAI

noncomputable section
namespace PiExponentSiegel.W23
open PiExponentSiegelAux.W09
open PiExponentJets.PolynomialLocalResidueResolution

variable (K α β : Type*) [Field K]

def affineCoefficientAlgHom :
    SplitPolynomial K α β →ₐ[K] FractionCoefficientPolynomial K α β :=
  (polynomialCoefficientLocalizationEquiv K α β).toAlgHom.comp
    (IsScalarTower.toAlgHom K (SplitPolynomial K α β)
      (PolynomialCoefficientLocalization K α β))

abbrev affineCoefficientMap :
    SplitPolynomial K α β →+* FractionCoefficientPolynomial K α β :=
  (affineCoefficientAlgHom K α β).toRingHom

@[reducible] def affineCoefficientAlgebra :
    Algebra (SplitPolynomial K α β) (FractionCoefficientPolynomial K α β) :=
  (affineCoefficientMap K α β).toAlgebra

attribute [local instance] affineCoefficientAlgebra

instance affineCoefficient_isLocalization :
    IsLocalization (coefficientDenominators K α β) (FractionCoefficientPolynomial K α β) := by
  exact (IsLocalization.isLocalization_iff_of_ringEquiv
    (coefficientDenominators K α β)
    (polynomialCoefficientLocalizationEquiv K α β).toRingEquiv).mp inferInstance

def affineMappedIdeal (P : Ideal (SplitPolynomial K α β)) :
    Ideal (FractionCoefficientPolynomial K α β) :=
  P.map (affineCoefficientMap K α β)

variable (Q : Ideal (SplitPolynomial K α β)) [Q.IsPrime]
variable (hB : IsTranscendenceBasis K (splitResidueBeta K α β Q))

theorem affineCoefficientMap_comap_closedPoint :
    (closedPolynomialIdeal K α β Q hB).comap (affineCoefficientMap K α β) = Q := by
  change ((coefficientClosedPoint K α β Q hB).map
      (polynomialCoefficientLocalizationEquiv K α β).toRingHom).comap
      ((polynomialCoefficientLocalizationEquiv K α β).toRingHom.comp
        (algebraMap (SplitPolynomial K α β) (PolynomialCoefficientLocalization K α β))) = Q
  rw [← Ideal.comap_comap, ← atPrimeImage_comap]
  exact coefficientClosedPoint_comap K α β Q hB

include hB in

theorem affineDenominators_disjoint (P : Ideal (SplitPolynomial K α β)) (hPQ : P ≤ Q) :
    Disjoint (coefficientDenominators K α β : Set (SplitPolynomial K α β)) (P : Set _) := by
  have hd : Disjoint (coefficientDenominators K α β : Set (SplitPolynomial K α β))
      (Q : Set _) := by
    rw [← affineCoefficientMap_comap_closedPoint K α β Q hB]
    exact (IsLocalization.disjoint_under_iff (coefficientDenominators K α β)
      (FractionCoefficientPolynomial K α β) (closedPolynomialIdeal K α β Q hB)).mpr
      (Ideal.IsMaximal.ne_top inferInstance)
  exact Set.disjoint_left.mpr fun x hx hxP => Set.disjoint_left.mp hd hx (hPQ hxP)

include hB in

theorem affineMappedIdeal_isPrime (P : Ideal (SplitPolynomial K α β)) [P.IsPrime]
    (hPQ : P ≤ Q) : (affineMappedIdeal K α β P).IsPrime := by
  exact IsLocalization.isPrime_of_isPrime_disjoint (coefficientDenominators K α β)
    (FractionCoefficientPolynomial K α β) P inferInstance
    (affineDenominators_disjoint K α β Q hB P hPQ)

theorem affineMappedIdeal_le_closedPoint (P : Ideal (SplitPolynomial K α β)) (hPQ : P ≤ Q) :
    affineMappedIdeal K α β P ≤ closedPolynomialIdeal K α β Q hB := by
  apply Ideal.map_le_iff_le_comap.mpr
  rw [affineCoefficientMap_comap_closedPoint]
  exact hPQ

include hB in

theorem affineMappedIdeal_comap (P : Ideal (SplitPolynomial K α β)) [P.IsPrime]
    (hPQ : P ≤ Q) :
    (affineMappedIdeal K α β P).comap (affineCoefficientMap K α β) = P :=
  IsLocalization.under_map_of_isPrime_disjoint (coefficientDenominators K α β)
    (FractionCoefficientPolynomial K α β) inferInstance
    (affineDenominators_disjoint K α β Q hB P hPQ)

theorem originalLocalCoefficientLocalEquiv_algebraMap (a : SplitPolynomial K α β) :
    originalLocalCoefficientLocalEquiv K α β Q hB
      (algebraMap (SplitPolynomial K α β) (Localization.AtPrime Q) a) =
      algebraMap (SplitPolynomial K α β) (CoefficientClosedLocal K α β Q hB) a := by
  let := closedLocal_isLocalizationAtOriginal K α β Q hB
  exact (IsLocalization.algEquiv Q.primeCompl (Localization.AtPrime Q)
    (CoefficientClosedLocal K α β Q hB)).commutes a

theorem closedPointLocalEquiv_algebraMap (a : SplitPolynomial K α β) :
    polynomialPrimeClosedPointEquiv K α β Q hB
      (algebraMap (SplitPolynomial K α β) (Localization.AtPrime Q) a) =
      algebraMap (FractionCoefficientPolynomial K α β)
        (Localization.AtPrime (closedPolynomialIdeal K α β Q hB))
        (affineCoefficientMap K α β a) := by
  change atPrimeEquivOfRingEquiv
    (polynomialCoefficientLocalizationEquiv K α β).toRingEquiv
    (coefficientClosedPoint K α β Q hB)
    (originalLocalCoefficientLocalEquiv K α β Q hB
      (algebraMap (SplitPolynomial K α β) (Localization.AtPrime Q) a)) = _
  exact (congrArg (atPrimeEquivOfRingEquiv
    (polynomialCoefficientLocalizationEquiv K α β).toRingEquiv
    (coefficientClosedPoint K α β Q hB))
    (originalLocalCoefficientLocalEquiv_algebraMap K α β Q hB a)).trans
    (atPrimeEquivOfRingEquiv_algebraMap
      (polynomialCoefficientLocalizationEquiv K α β).toRingEquiv
      (coefficientClosedPoint K α β Q hB)
      (algebraMap (SplitPolynomial K α β) (PolynomialCoefficientLocalization K α β) a))

theorem closedPointLocalEquiv_map_ideal (P : Ideal (SplitPolynomial K α β)) :
    (parameterLocalizedIdeal P Q).map
      (polynomialPrimeClosedPointEquiv K α β Q hB).toRingHom =
    parameterLocalizedIdeal (affineMappedIdeal K α β P)
      (closedPolynomialIdeal K α β Q hB) := by
  unfold parameterLocalizedIdeal affineMappedIdeal
  rw [Ideal.map_map, Ideal.map_map]
  congr 1
  apply RingHom.ext
  intro a
  exact closedPointLocalEquiv_algebraMap K α β Q hB a

def affineLocalQuotientEquiv (P : Ideal (SplitPolynomial K α β)) :
    (Localization.AtPrime Q ⧸ parameterLocalizedIdeal P Q) ≃+*
      (Localization.AtPrime (closedPolynomialIdeal K α β Q hB) ⧸
        parameterLocalizedIdeal (affineMappedIdeal K α β P)
          (closedPolynomialIdeal K α β Q hB)) :=
  Ideal.quotientEquiv _ _ (polynomialPrimeClosedPointEquiv K α β Q hB)
    (closedPointLocalEquiv_map_ideal K α β Q hB P).symm

def affineClosedQuotientLocalEquiv (P : Ideal (SplitPolynomial K α β)) (hPQ : P ≤ Q) :
    Localization.AtPrime (quotientParameterPrime P Q hPQ) ≃+*
      Localization.AtPrime
        (R := FractionCoefficientPolynomial K α β ⧸ affineMappedIdeal K α β P)
        (quotientParameterPrime (affineMappedIdeal K α β P)
        (closedPolynomialIdeal K α β Q hB)
        (affineMappedIdeal_le_closedPoint K α β Q hB P hPQ)) :=
  ((localizationQuotientParametersEquiv P Q hPQ).symm.trans
    (affineLocalQuotientEquiv K α β Q hB P)).trans
    (localizationQuotientParametersEquiv (affineMappedIdeal K α β P)
      (closedPolynomialIdeal K α β Q hB)
      (affineMappedIdeal_le_closedPoint K α β Q hB P hPQ))

def affineQuotientMap (P : Ideal (SplitPolynomial K α β)) :
    (SplitPolynomial K α β ⧸ P) →+*
      (FractionCoefficientPolynomial K α β ⧸ affineMappedIdeal K α β P) :=
  Ideal.quotientMap _ (affineCoefficientMap K α β) Ideal.le_comap_map

@[reducible] def affineQuotientAlgebra (P : Ideal (SplitPolynomial K α β)) :
    Algebra (SplitPolynomial K α β ⧸ P)
      (FractionCoefficientPolynomial K α β ⧸ affineMappedIdeal K α β P) :=
  RingHom.toAlgebra'
    (R := SplitPolynomial K α β ⧸ P)
    (S := FractionCoefficientPolynomial K α β ⧸ affineMappedIdeal K α β P)
    (affineQuotientMap K α β P) (fun x y =>
      (Ideal.Quotient.commSemiring (affineMappedIdeal K α β P)).mul_comm
        (affineQuotientMap K α β P x) y)

attribute [local instance] affineQuotientAlgebra

@[simp] theorem affineQuotientMap_mk (P : Ideal (SplitPolynomial K α β))
    (a : SplitPolynomial K α β) :
    affineQuotientMap K α β P (Ideal.Quotient.mk P a) =
      Ideal.Quotient.mk _ (affineCoefficientMap K α β a) := rfl

instance affineQuotient_scalarTower (P : Ideal (SplitPolynomial K α β)) :
    IsScalarTower K (SplitPolynomial K α β ⧸ P)
      (FractionCoefficientPolynomial K α β ⧸ affineMappedIdeal K α β P) := by
  apply IsScalarTower.of_algebraMap_eq
    (R := K) (S := SplitPolynomial K α β ⧸ P)
    (A := FractionCoefficientPolynomial K α β ⧸ affineMappedIdeal K α β P)
  intro k
  change Ideal.Quotient.mk _ (algebraMap K (FractionCoefficientPolynomial K α β) k) =
    affineQuotientMap K α β P (Ideal.Quotient.mk P (algebraMap K (SplitPolynomial K α β) k))
  rw [affineQuotientMap_mk]
  exact congrArg (Ideal.Quotient.mk (affineMappedIdeal K α β P))
    ((affineCoefficientAlgHom K α β).commutes k).symm

include hB in

theorem affineQuotientMap_injective (P : Ideal (SplitPolynomial K α β)) [P.IsPrime]
    (hPQ : P ≤ Q) : Function.Injective (affineQuotientMap K α β P) :=
  Ideal.quotientMap_injective' (affineMappedIdeal_comap K α β Q hB P hPQ).le

include hB in

theorem affineQuotient_faithfulSMul (P : Ideal (SplitPolynomial K α β)) [P.IsPrime]
    (hPQ : P ≤ Q) :
    FaithfulSMul (SplitPolynomial K α β ⧸ P)
      (FractionCoefficientPolynomial K α β ⧸ affineMappedIdeal K α β P) :=
  (faithfulSMul_iff_algebraMap_injective _ _).mpr
    (affineQuotientMap_injective K α β Q hB P hPQ)

include hB in

theorem affineQuotient_isDomain (P : Ideal (SplitPolynomial K α β)) [P.IsPrime]
    (hPQ : P ≤ Q) :
    IsDomain (FractionCoefficientPolynomial K α β ⧸ affineMappedIdeal K α β P) := by
  let := affineMappedIdeal_isPrime K α β Q hB P hPQ
  infer_instance

theorem affineQuotient_finiteType [Finite α] (P : Ideal (SplitPolynomial K α β)) :
    Algebra.FiniteType (SplitCoefficientField K β)
      (FractionCoefficientPolynomial K α β ⧸ affineMappedIdeal K α β P) :=
  Algebra.FiniteType.of_surjective
    (Ideal.Quotient.mkₐ (SplitCoefficientField K β) (affineMappedIdeal K α β P))
    Ideal.Quotient.mk_surjective

include hB in

theorem affineQuotient_isLocalization (P : Ideal (SplitPolynomial K α β)) [P.IsPrime]
    (hPQ : P ≤ Q) :
    IsLocalization ((coefficientDenominators K α β).map (Ideal.Quotient.mk P))
      (FractionCoefficientPolynomial K α β ⧸ affineMappedIdeal K α β P) := by
  apply (isLocalization_iff
    ((coefficientDenominators K α β).map (Ideal.Quotient.mk P))
    (FractionCoefficientPolynomial K α β ⧸ affineMappedIdeal K α β P)).mpr
  refine ⟨?_, ?_, ?_⟩
  · intro s
    obtain ⟨a, ha, he⟩ := s.property
    change IsUnit (affineQuotientMap K α β P (s : SplitPolynomial K α β ⧸ P))
    rw [← he, affineQuotientMap_mk]
    exact (IsLocalization.map_units (FractionCoefficientPolynomial K α β)
      (⟨a, ha⟩ : coefficientDenominators K α β)).map
        (Ideal.Quotient.mk (affineMappedIdeal K α β P))
  · intro z
    obtain ⟨t, rfl⟩ := Ideal.Quotient.mk_surjective z
    obtain ⟨⟨a, s⟩, hs⟩ := IsLocalization.surj (coefficientDenominators K α β) t
    refine ⟨⟨Ideal.Quotient.mk P a,
      ⟨Ideal.Quotient.mk P (s : SplitPolynomial K α β),
        Submonoid.mem_map_of_mem (Ideal.Quotient.mk P) s.property⟩⟩, ?_⟩
    change Ideal.Quotient.mk _ t *
      affineQuotientMap K α β P (Ideal.Quotient.mk P (s : SplitPolynomial K α β)) =
      affineQuotientMap K α β P (Ideal.Quotient.mk P a)
    rw [affineQuotientMap_mk, affineQuotientMap_mk, ← map_mul]
    exact congrArg (Ideal.Quotient.mk (affineMappedIdeal K α β P)) hs
  · intro x y hxy
    refine ⟨1, ?_⟩
    simpa only [Submonoid.coe_one, one_mul] using
      (affineQuotientMap_injective K α β Q hB P hPQ hxy)

end PiExponentSiegel.W23

end

end OAI
end Source0208

-- Source: OAI/NumberTheory/PiExponent/LocalAlgebra/AffineTranscendenceDimension.lean
section Source0209
/-
Modification notice for the LogTwo project.
Derived from openai/math (Apache-2.0), revision adc7f1241b42e322a6451854ab7e4b4c146bf78a.
Original source: lean/OAI/NumberTheory/PiExponent/LocalAlgebra/AffineTranscendenceDimension.lean
Changes: Convert module/import declarations to the Lean 4.34 public module format.
See ../THIRD_PARTY_NOTICES.txt for provenance and the recorded changes.
-/

namespace OAI

namespace PiExponentJets.W24

section Normalization

variable (k B : Type*) [Field k] [CommRing B] [IsDomain B] [Algebra k B]

theorem normalization_trdeg_toNat (s : ℕ)
    (g : MvPolynomial (Fin s) k →ₐ[k] B)
    (hg : Function.Injective g) (hi : g.IsIntegral) :
    (Algebra.trdeg k B).toNat = s := by
  let : Algebra (MvPolynomial (Fin s) k) B := g.toRingHom.toAlgebra
  have : IsScalarTower k (MvPolynomial (Fin s) k) B :=
    IsScalarTower.of_algebraMap_eq fun x => (g.commutes x).symm
  have : FaithfulSMul (MvPolynomial (Fin s) k) B :=
    (faithfulSMul_iff_algebraMap_injective _ _).mpr hg
  have : Algebra.IsIntegral (MvPolynomial (Fin s) k) B := ⟨hi⟩
  have : Algebra.IsAlgebraic (MvPolynomial (Fin s) k) B :=
    ⟨fun x => (Algebra.IsIntegral.isIntegral x).isAlgebraic⟩
  have ht := congrArg Cardinal.toNat
    (lift_trdeg_add_eq k (MvPolynomial (Fin s) k) B)
  simpa [trdeg_eq_zero] using ht.symm

theorem finiteType_domain_krullDim_eq_trdeg [Algebra.FiniteType k B] :
    ringKrullDim B = ((Algebra.trdeg k B).toNat : WithBot ℕ∞) := by
  obtain ⟨s, g, hg, hfin, hdim⟩ := exists_finite_normalization_with_dimension k B
  rw [hdim, normalization_trdeg_toNat k B s g hg hfin.to_isIntegral]

end Normalization

section AlgebraicTower

variable (k B C : Type*) [Field k] [CommRing B] [IsDomain B]
  [CommRing C] [IsDomain C] [Algebra k B] [Algebra k C] [Algebra B C]
  [IsScalarTower k B C] [FaithfulSMul B C]

theorem trdeg_toNat_eq_of_algebraic_tower [Algebra.IsAlgebraic B C] :
    (Algebra.trdeg k B).toNat = (Algebra.trdeg k C).toNat := by
  have ht := congrArg Cardinal.toNat (lift_trdeg_add_eq k B C)
  simpa only [trdeg_eq_zero, Cardinal.lift_zero, add_zero, Cardinal.toNat_lift] using ht

theorem localization_trdeg_toNat_eq (M : Submonoid B) [IsLocalization M C] :
    (Algebra.trdeg k B).toNat = (Algebra.trdeg k C).toNat := by
  have : Algebra.IsAlgebraic B C := IsLocalization.isAlgebraic C M
  exact trdeg_toNat_eq_of_algebraic_tower k B C

end AlgebraicTower

variable (k F B C : Type*) [Field k] [Field F] [CommRing B] [IsDomain B]
  [CommRing C] [IsDomain C] [Algebra k F] [Algebra k B] [Algebra k C]
  [Algebra B C] [Algebra F C] [IsScalarTower k B C] [IsScalarTower k F C]
  [FaithfulSMul B C] [Algebra.FiniteType k B] [Algebra.FiniteType F C]

theorem coefficient_localization_dimension
    (M : Submonoid B) [IsLocalization M C]
    (hF : Algebra.trdeg k F < Cardinal.aleph0) :
    ringKrullDim C + ((Algebra.trdeg k F).toNat : WithBot ℕ∞) = ringKrullDim B := by
  have hFC : Algebra.trdeg F C < Cardinal.aleph0 := trdeg_lt_aleph0_of_finiteType (R := F) (S := C)
  have ht := congrArg Cardinal.toNat (lift_trdeg_add_eq k F C)
  rw [Cardinal.toNat_lift_add_lift hF hFC, Cardinal.toNat_lift] at ht
  have hl := localization_trdeg_toNat_eq k B C M
  rw [finiteType_domain_krullDim_eq_trdeg F C,
    finiteType_domain_krullDim_eq_trdeg k B, hl, ← ht, Nat.cast_add]
  exact add_comm _ _

end PiExponentJets.W24

end OAI
end Source0209

-- Source: OAI/NumberTheory/PiExponent/LocalAlgebra/AffineResidueTranscendence.lean
section Source0210
/-
Modification notice for the LogTwo project.
Derived from openai/math (Apache-2.0), revision adc7f1241b42e322a6451854ab7e4b4c146bf78a.
Original source: lean/OAI/NumberTheory/PiExponent/LocalAlgebra/AffineResidueTranscendence.lean
Changes: Convert module/import declarations to the Lean 4.34 public module format.
See ../THIRD_PARTY_NOTICES.txt for provenance and the recorded changes.
-/

namespace OAI

noncomputable section
namespace PiExponentJets.W24
open scoped nonZeroDivisors

theorem trdeg_lt_aleph0_of_algebraic_tower
    (k B C : Type*) [Field k] [CommRing B] [IsDomain B]
    [CommRing C] [IsDomain C] [Algebra k B] [Algebra k C] [Algebra B C]
    [IsScalarTower k B C] [FaithfulSMul B C] [Algebra.IsAlgebraic B C]
    (hB : Algebra.trdeg k B < Cardinal.aleph0) :
    Algebra.trdeg k C < Cardinal.aleph0 := by
  have ht := lift_trdeg_add_eq k B C
  simp only [trdeg_eq_zero, Cardinal.lift_zero, add_zero] at ht
  have hlt := Cardinal.lift_lt_aleph0.mpr hB
  rw [ht] at hlt
  exact Cardinal.lift_lt_aleph0.mp hlt

theorem affine_prime_quotient_dimension_eq_residue_trdeg
    (k A : Type*) [Field k] [CommRing A] [Algebra k A]
    [Algebra.FiniteType k A] (Q : Ideal A) [Q.IsPrime] :
    ringKrullDim (A ⧸ Q) = ((Algebra.trdeg k Q.ResidueField).toNat : WithBot ℕ∞) := by
  have : FaithfulSMul (A ⧸ Q) Q.ResidueField :=
    (faithfulSMul_iff_algebraMap_injective _ _).mpr
      Q.injective_algebraMap_quotient_residueField
  rw [finiteType_domain_krullDim_eq_trdeg k (A ⧸ Q),
    localization_trdeg_toNat_eq k (A ⧸ Q) Q.ResidueField (nonZeroDivisors (A ⧸ Q))]

theorem affine_prime_quotient_dimension_eq_basis_card
    (k A β : Type*) [Field k] [CommRing A] [Algebra k A]
    [Algebra.FiniteType k A] (Q : Ideal A) [Q.IsPrime]
    (b : β → Q.ResidueField) (hb : IsTranscendenceBasis k b) :
    ringKrullDim (A ⧸ Q) = (Nat.card β : WithBot ℕ∞) := by
  have ht := congrArg Cardinal.toNat hb.lift_cardinalMk_eq_trdeg
  simp only [Cardinal.toNat_lift] at ht
  rw [affine_prime_quotient_dimension_eq_residue_trdeg k A Q, ← ht]
  rfl

theorem rational_coefficient_trdeg_toNat (k β : Type*) [Field k] :
    (Algebra.trdeg k (FractionRing (MvPolynomial β k))).toNat = Nat.card β := by
  rw [← localization_trdeg_toNat_eq k (MvPolynomial β k)
    (FractionRing (MvPolynomial β k)) (nonZeroDivisors (MvPolynomial β k))]
  simp only [MvPolynomial.trdeg_of_isDomain, Cardinal.toNat_lift, Nat.card]

theorem rational_coefficient_trdeg_lt_aleph0
    (k β : Type*) [Field k] [Finite β] :
    Algebra.trdeg k (FractionRing (MvPolynomial β k)) < Cardinal.aleph0 := by
  have : Algebra.IsAlgebraic (MvPolynomial β k) (FractionRing (MvPolynomial β k)) :=
    IsLocalization.isAlgebraic _ (nonZeroDivisors (MvPolynomial β k))
  apply trdeg_lt_aleph0_of_algebraic_tower k (MvPolynomial β k)
    (FractionRing (MvPolynomial β k))
  simp only [MvPolynomial.trdeg_of_isDomain, Cardinal.lift_lt_aleph0,
    Cardinal.mk_lt_aleph0]

theorem coefficient_trdeg_eq_prime_quotient_dimension
    (k A β : Type*) [Field k] [CommRing A] [Algebra k A]
    [Algebra.FiniteType k A] (Q : Ideal A) [Q.IsPrime]
    (b : β → Q.ResidueField) (hb : IsTranscendenceBasis k b) :
    ((Algebra.trdeg k (FractionRing (MvPolynomial β k))).toNat : WithBot ℕ∞) =
      ringKrullDim (A ⧸ Q) := by
  rw [rational_coefficient_trdeg_toNat k β,
    affine_prime_quotient_dimension_eq_basis_card k A β Q b hb]

end PiExponentJets.W24

end

end OAI
end Source0210

-- Source: OAI/NumberTheory/PiExponent/Polynomials/PolynomialMaximalHeight.lean
section Source0211
-- Modified in this edition: unused plain lemmas removed; see reduction.json.
/-
Modification notice for the LogTwo project.
Derived from openai/math (Apache-2.0), revision adc7f1241b42e322a6451854ab7e4b4c146bf78a.
Original source: lean/OAI/NumberTheory/PiExponent/Polynomials/PolynomialMaximalHeight.lean
Changes: Convert module/import declarations to the Lean 4.34 public module format.
See ../THIRD_PARTY_NOTICES.txt for provenance and the recorded changes.
-/

namespace OAI

noncomputable section
namespace PiExponentSiegelAux.W09

variable (K : Type*) [Field K]

theorem polynomialMaximal_height (n : ℕ)
    (m : Ideal (MvPolynomial (Fin n) K)) [m.IsMaximal] :
    m.height = (n : ℕ∞) := by
  induction n with
  | zero =>
      let e := MvPolynomial.isEmptyAlgEquiv K (Fin 0)
      let p : Ideal K := m.comap e.symm.toRingHom
      let : p.IsMaximal := Ideal.comap_isMaximal_of_equiv e.symm
      have hp : p = ⊥ := p.eq_bot_or_top.resolve_right (Ideal.IsMaximal.ne_top (inferInstance : p.IsMaximal))
      calc
        m.height = p.height := (e.symm.toRingEquiv.height_comap m).symm
        _ = (0 : ℕ∞) := by rw [hp, Ideal.height_bot]
  | succ n ih =>
      let e := MvPolynomial.finSuccEquiv K n
      let P : Ideal (Polynomial (MvPolynomial (Fin n) K)) :=
        m.comap e.symm.toRingHom
      let : P.IsMaximal := Ideal.comap_isMaximal_of_equiv e.symm
      let p : Ideal (MvPolynomial (Fin n) K) := P.comap Polynomial.C
      let : p.IsMaximal := Polynomial.isMaximal_comap_C_of_isJacobsonRing P
      let : P.LiesOver p := ⟨rfl⟩
      calc
        m.height = P.height := (e.symm.toRingEquiv.height_comap m).symm
        _ = p.height + 1 := Polynomial.height_eq_height_add_one p P
        _ = ((n + 1 : ℕ) : ℕ∞) := by rw [ih p]; simp

end PiExponentSiegelAux.W09

end

end OAI
end Source0211

-- Source: OAI/NumberTheory/PiExponent/LocalAlgebra/ClosedPointLocalDimension.lean
section Source0212
/-
Modification notice for the LogTwo project.
Derived from openai/math (Apache-2.0), revision adc7f1241b42e322a6451854ab7e4b4c146bf78a.
Original source: lean/OAI/NumberTheory/PiExponent/LocalAlgebra/ClosedPointLocalDimension.lean
Changes: Convert module/import declarations to the Lean 4.34 public module format.
See ../THIRD_PARTY_NOTICES.txt for provenance and the recorded changes.
-/

namespace OAI

namespace PiExponentJets.W29

section GoingDownHeight

variable {A B : Type*} [CommRing A] [CommRing B] [Algebra A B]
  [Algebra.HasGoingDown A B]

theorem under_height_le_of_goingDown (P : Ideal B) [P.IsPrime] :
    (P.under A).height ≤ P.height := by
  rw [PrimeSpectrum.height_eq_orderHeight (⟨P.under A, inferInstance⟩ : PrimeSpectrum A),
    PrimeSpectrum.height_eq_orderHeight (⟨P, inferInstance⟩ : PrimeSpectrum B)]
  apply Order.height_le
  intro l hl
  let : P.LiesOver l.last.asIdeal := ⟨congrArg PrimeSpectrum.asIdeal hl⟩
  obtain ⟨L, hlen, hlast, _⟩ := Ideal.exists_ltSeries_of_hasGoingDown l P
  have h : (L.length : ℕ∞) ≤ Order.height (⟨P, inferInstance⟩ : PrimeSpectrum B) :=
    Order.length_le_height (le_of_eq hlast)
  simpa only [hlen] using h

end GoingDownHeight

variable (k B : Type*) [Field k] [CommRing B] [IsDomain B]
  [Algebra k B] [Algebra.FiniteType k B]

include k

theorem affineDomain_maximal_height (m : Ideal B) [m.IsMaximal] :
    (m.height : WithBot ℕ∞) = ringKrullDim B := by
  obtain ⟨d, g, hg, hfin, hdim⟩ := W24.exists_finite_normalization_with_dimension k B
  let A := MvPolynomial (Fin d) k
  let : Algebra A B := g.toRingHom.toAlgebra
  have : Algebra.IsIntegral A B := ⟨hfin.to_isIntegral⟩
  have : FaithfulSMul A B := (faithfulSMul_iff_algebraMap_injective A B).mpr hg
  have : IsIntegrallyClosed A := inferInstance
  have : Algebra.HasGoingDown A B := inferInstance
  let p : Ideal A := m.under A
  have : p.IsMaximal := by
    dsimp [p]
    infer_instance
  have hp : p.height = (d : ℕ∞) :=
    PiExponentSiegelAux.W09.polynomialMaximal_height k d p
  have hlo : (d : ℕ∞) ≤ m.height := by
    rw [← hp]
    exact under_height_le_of_goingDown m
  apply le_antisymm
  · exact Ideal.height_le_ringKrullDim_of_ne_top
      (Ideal.IsMaximal.ne_top (inferInstance : m.IsMaximal))
  · rw [hdim]
    exact WithBot.coe_le_coe.mpr hlo

theorem closedPoint_local_dimension (m : Ideal B) [m.IsMaximal] :
    ringKrullDim (Localization.AtPrime m) = ringKrullDim B := by
  rw [IsLocalization.AtPrime.ringKrullDim_eq_height m (Localization.AtPrime m)]
  exact affineDomain_maximal_height k B m

end PiExponentJets.W29

end OAI
end Source0212

-- Source: OAI/NumberTheory/PiExponent/LocalAlgebra/AffinePrimeDimensionBridge.lean
section Source0213
/-
Modification notice for the LogTwo project.
Derived from openai/math (Apache-2.0), revision adc7f1241b42e322a6451854ab7e4b4c146bf78a.
Original source: lean/OAI/NumberTheory/PiExponent/LocalAlgebra/AffinePrimeDimensionBridge.lean
Changes: Convert module/import declarations to the Lean 4.34 public module format.
See ../THIRD_PARTY_NOTICES.txt for provenance and the recorded changes.
-/

namespace OAI

noncomputable section
namespace PiExponentJets.W24

theorem affine_prime_dimension_of_closedPoint_presentation
    (k B β C : Type*) [Field k] [CommRing B] [IsDomain B]
    [Algebra k B] [Algebra.FiniteType k B] [Finite β]
    [CommRing C] [IsDomain C] [Algebra k C] [Algebra B C]
    [Algebra (FractionRing (MvPolynomial β k)) C]
    [IsScalarTower k B C]
    [IsScalarTower k (FractionRing (MvPolynomial β k)) C]
    [FaithfulSMul B C]
    [Algebra.FiniteType (FractionRing (MvPolynomial β k)) C]
    (q : Ideal B) [q.IsPrime]
    (b : β → q.ResidueField) (hb : IsTranscendenceBasis k b)
    (M : Submonoid B) [IsLocalization M C]
    (m : Ideal C) [m.IsMaximal]
    (e : Localization.AtPrime q ≃+* Localization.AtPrime m) :
    (q.height : WithBot ℕ∞) + ringKrullDim (B ⧸ q) = ringKrullDim B := by
  have he : (q.height : WithBot ℕ∞) = ringKrullDim C := by
    rw [← IsLocalization.AtPrime.ringKrullDim_eq_height q (Localization.AtPrime q),
      e.ringKrullDim, W29.closedPoint_local_dimension (FractionRing (MvPolynomial β k)) C m]
  have hd := coefficient_localization_dimension k (FractionRing (MvPolynomial β k)) B C M
    (rational_coefficient_trdeg_lt_aleph0 k β)
  rw [coefficient_trdeg_eq_prime_quotient_dimension k B β q b hb] at hd
  exact he.symm ▸ hd

end PiExponentJets.W24

end

end OAI
end Source0213

-- Source: OAI/NumberTheory/PiExponent/LocalAlgebra/CoordinateBasisSplitting.lean
section Source0214
/-
Modification notice for the LogTwo project.
Derived from openai/math (Apache-2.0), revision adc7f1241b42e322a6451854ab7e4b4c146bf78a.
Original source: lean/OAI/NumberTheory/PiExponent/LocalAlgebra/CoordinateBasisSplitting.lean
Changes: Convert module/import declarations to the Lean 4.34 public module format.
See ../THIRD_PARTY_NOTICES.txt for provenance and the recorded changes.
-/

namespace OAI

noncomputable section
namespace PiExponentJets.PolynomialLocalResidueResolution

variable {n : ℕ} {T : Type*} (j : T → Fin n) (hj : Function.Injective j)

abbrev RemainingCoordinate := {i : Fin n // i ∉ Set.range j}

def coordinateIndexSplitting : RemainingCoordinate j ⊕ T ≃ Fin n := by
  classical
  exact (Equiv.sumCongr (Equiv.refl _) (Equiv.ofInjective j hj)).trans
    ((Equiv.sumComm _ _).trans (Equiv.sumCompl (fun i : Fin n => i ∈ Set.range j)))

@[simp] theorem coordinateIndexSplitting_inr (a : T) :
    coordinateIndexSplitting j hj (Sum.inr a) = j a := rfl

@[simp] theorem coordinateIndexSplitting_symm_selected (a : T) :
    (coordinateIndexSplitting j hj).symm (j a) = Sum.inr a := by
  rw [← coordinateIndexSplitting_inr j hj a, Equiv.symm_apply_apply]

def coordinateBasisRenaming (K : Type*) [Field K] : MvPolynomial (Fin n) K ≃ₐ[K]
    MvPolynomial (RemainingCoordinate j ⊕ T) K :=
  MvPolynomial.renameEquiv K (coordinateIndexSplitting j hj).symm

variable (K : Type*) [Field K] (Q : Ideal (MvPolynomial (Fin n) K)) [Q.IsPrime]
variable (t : Set Q.ResidueField) (j : t → Fin n) (hj : Function.Injective j)
variable (hcoord : ∀ a, residueCoordinate K n Q (j a) = (a : Q.ResidueField))
variable (ht : IsTranscendenceBasis K ((↑) : t → Q.ResidueField))

abbrev coordinateSplitPrime := Q.map (coordinateBasisRenaming j hj K).toRingHom

include hcoord ht in

theorem coordinateSplitPrime_basis :
    IsTranscendenceBasis K
      (splitResidueBeta K (RemainingCoordinate j) t (coordinateSplitPrime K Q t j hj)) := by
  have hb := primeResidueAlgEquiv_transcendenceBasis
    (coordinateBasisRenaming j hj K) Q ((↑) : t → Q.ResidueField) ht
  have he : splitResidueBeta K (RemainingCoordinate j) t (coordinateSplitPrime K Q t j hj) =
      fun a : t => primeResidueAlgEquiv (coordinateBasisRenaming j hj K) Q (a : Q.ResidueField) := by
    funext a
    rw [← hcoord a]
    change algebraMap (MvPolynomial (RemainingCoordinate j ⊕ t) K)
      (coordinateSplitPrime K Q t j hj).ResidueField (MvPolynomial.X (Sum.inr a)) =
      primeResidueAlgEquiv (coordinateBasisRenaming j hj K) Q
        (algebraMap (MvPolynomial (Fin n) K) Q.ResidueField (MvPolynomial.X (j a)))
    rw [primeResidueAlgEquiv_algebraMap]
    change algebraMap _ (coordinateSplitPrime K Q t j hj).ResidueField (MvPolynomial.X (Sum.inr a)) =
      algebraMap _ (coordinateSplitPrime K Q t j hj).ResidueField
        (MvPolynomial.rename (coordinateIndexSplitting j hj).symm (MvPolynomial.X (j a)))
    rw [MvPolynomial.rename_X, coordinateIndexSplitting_symm_selected]
  rw [he]
  exact hb

def coordinateBasisLocalEquiv : Localization.AtPrime Q ≃+*
    Localization.AtPrime (coordinateSplitPrime K Q t j hj) :=
  PiExponentSiegel.W23.atPrimeEquivOfRingEquiv (coordinateBasisRenaming j hj K).toRingEquiv Q

def coordinateBasisClosedPointEquiv : Localization.AtPrime Q ≃+*
    Localization.AtPrime
      (closedPolynomialIdeal K (RemainingCoordinate j) t (coordinateSplitPrime K Q t j hj)
        (coordinateSplitPrime_basis K Q t j hj hcoord ht)) :=
  (coordinateBasisLocalEquiv K Q t j hj).trans
    (polynomialPrimeClosedPointEquiv K (RemainingCoordinate j) t
      (coordinateSplitPrime K Q t j hj)
      (coordinateSplitPrime_basis K Q t j hj hcoord ht))

end PiExponentJets.PolynomialLocalResidueResolution

end

end OAI
end Source0214

-- Source: OAI/NumberTheory/PiExponent/LocalAlgebra/QuotientPrimeResidueBasis.lean
section Source0215
-- Modified in this edition: unused plain lemmas removed; see reduction.json.
/-
Modification notice for the LogTwo project.
Derived from openai/math (Apache-2.0), revision adc7f1241b42e322a6451854ab7e4b4c146bf78a.
Original source: lean/OAI/NumberTheory/PiExponent/LocalAlgebra/QuotientPrimeResidueBasis.lean
Changes: Convert module/import declarations to the Lean 4.34 public module format.
See ../THIRD_PARTY_NOTICES.txt for provenance and the recorded changes.
-/

namespace OAI

noncomputable section
namespace PiExponentJets.W24

section Surjective

variable {k A B : Type*} [CommRing k] [CommRing A] [CommRing B]
  [Algebra k A] [Algebra k B]

def surjective_prime_residueAlgEquiv
    (f : A →ₐ[k] B) (hf : Function.Surjective f)
    (P : Ideal A) [P.IsPrime] (Q : Ideal B) [Q.IsPrime]
    (hPQ : P = Q.comap f.toRingHom) : P.ResidueField ≃ₐ[k] Q.ResidueField :=
  AlgEquiv.ofBijective (Ideal.ResidueField.mapₐ P Q f hPQ)
    ((RingHom.surjectiveOnStalks_of_surjective hf).residueFieldMap_bijective P Q hPQ)

@[simp] theorem surjective_prime_residueAlgEquiv_algebraMap
    (f : A →ₐ[k] B) (hf : Function.Surjective f)
    (P : Ideal A) [P.IsPrime] (Q : Ideal B) [Q.IsPrime]
    (hPQ : P = Q.comap f.toRingHom) (a : A) :
    surjective_prime_residueAlgEquiv f hf P Q hPQ (algebraMap A P.ResidueField a) =
      algebraMap B Q.ResidueField (f a) :=
  Ideal.ResidueField.map_algebraMap P Q f.toRingHom hPQ a

end Surjective

variable {k A : Type*} [CommRing k] [CommRing A] [Algebra k A]

theorem quotient_prime_comap (P Q : Ideal A) (hPQ : P ≤ Q) :
    (Q.map (Ideal.Quotient.mk P)).comap (Ideal.Quotient.mk P) = Q := by
  rw [Ideal.comap_map_of_surjective _ Ideal.Quotient.mk_surjective]
  change Q ⊔ RingHom.ker (Ideal.Quotient.mk P) = Q
  rw [Ideal.mk_ker, sup_eq_left.mpr hPQ]

def quotientPrimeResidueAlgEquiv
    (P Q : Ideal A) [Q.IsPrime] (hPQ : P ≤ Q) :
    letI : (Q.map (Ideal.Quotient.mk P)).IsPrime :=
      Ideal.map_isPrime_of_surjective Ideal.Quotient.mk_surjective
        (by rw [Ideal.mk_ker]; exact hPQ)
    Q.ResidueField ≃ₐ[k] (Q.map (Ideal.Quotient.mk P)).ResidueField := by
  letI : (Q.map (Ideal.Quotient.mk P)).IsPrime :=
    Ideal.map_isPrime_of_surjective Ideal.Quotient.mk_surjective
      (by rw [Ideal.mk_ker]; exact hPQ)
  exact surjective_prime_residueAlgEquiv (Ideal.Quotient.mkₐ k P)
    Ideal.Quotient.mk_surjective Q (Q.map (Ideal.Quotient.mk P))
    (quotient_prime_comap P Q hPQ).symm

theorem quotientPrimeResidueAlgEquiv_basis
    (P Q : Ideal A) [Q.IsPrime] (hPQ : P ≤ Q)
    {ι : Type*} (b : ι → Q.ResidueField) (hb : IsTranscendenceBasis k b) :
    letI : (Q.map (Ideal.Quotient.mk P)).IsPrime :=
      Ideal.map_isPrime_of_surjective Ideal.Quotient.mk_surjective
        (by rw [Ideal.mk_ker]; exact hPQ)
    IsTranscendenceBasis k (fun i => quotientPrimeResidueAlgEquiv (k := k) P Q hPQ (b i)) := by
  exact (quotientPrimeResidueAlgEquiv (k := k) P Q hPQ).isTranscendenceBasis hb

end PiExponentJets.W24

end

end OAI
end Source0215

-- Source: OAI/NumberTheory/PiExponent/Polynomials/PolynomialPrimeDimension.lean
section Source0216
/-
Modification notice for the LogTwo project.
Derived from openai/math (Apache-2.0), revision adc7f1241b42e322a6451854ab7e4b4c146bf78a.
Original source: lean/OAI/NumberTheory/PiExponent/Polynomials/PolynomialPrimeDimension.lean
Changes: Convert module/import declarations to the Lean 4.34 public module format.
See ../THIRD_PARTY_NOTICES.txt for provenance and the recorded changes.
-/

namespace OAI

noncomputable section
namespace PiExponentJets.W24
open PiExponentSiegel.W23 PiExponentSiegelAux.W09
open PiExponentJets.PolynomialLocalResidueResolution

section Equivalence
variable {A B : Type*} [CommRing A] [CommRing B]

local instance imagePrime_isPrime (e : A ≃+* B) (Q : Ideal A) [Q.IsPrime] :
    (Q.map e.toRingHom).IsPrime := Ideal.map_isPrime_of_equiv e

theorem ringEquiv_localizedIdeal_map (e : A ≃+* B)
    (P Q : Ideal A) [Q.IsPrime] :
    (parameterLocalizedIdeal P Q).map (atPrimeEquivOfRingEquiv e Q).toRingHom =
      parameterLocalizedIdeal (P.map e.toRingHom) (Q.map e.toRingHom) := by
  unfold parameterLocalizedIdeal
  rw [Ideal.map_map, Ideal.map_map]
  congr 1
  apply RingHom.ext
  intro a
  exact atPrimeEquivOfRingEquiv_algebraMap e Q a

def ringEquiv_localQuotient (e : A ≃+* B) (P Q : Ideal A) [Q.IsPrime] :
    (Localization.AtPrime Q ⧸ parameterLocalizedIdeal P Q) ≃+*
      (Localization.AtPrime (Q.map e.toRingHom) ⧸
        parameterLocalizedIdeal (P.map e.toRingHom) (Q.map e.toRingHom)) :=
  Ideal.quotientEquiv _ _ (atPrimeEquivOfRingEquiv e Q)
    (ringEquiv_localizedIdeal_map e P Q).symm

end Equivalence

section Split
variable (k α β : Type*) [Field k] [Finite α] [Finite β]
variable (P Q : Ideal (SplitPolynomial k α β)) [P.IsPrime] [Q.IsPrime]

theorem split_polynomial_prime_pair_local_dimension
    (hPQ : P ≤ Q)
    (hB : IsTranscendenceBasis k (splitResidueBeta k α β Q)) :
    ringKrullDim (Localization.AtPrime Q ⧸ parameterLocalizedIdeal P Q) +
      ringKrullDim (SplitPolynomial k α β ⧸ Q) =
        ringKrullDim (SplitPolynomial k α β ⧸ P) := by
  let C := FractionCoefficientPolynomial k α β ⧸ affineMappedIdeal k α β P
  let q := quotientParameterPrime P Q hPQ
  let m := quotientParameterPrime (affineMappedIdeal k α β P)
    (closedPolynomialIdeal k α β Q hB)
    (affineMappedIdeal_le_closedPoint k α β Q hB P hPQ)
  let := affineCoefficientAlgebra k α β
  let := affineQuotientAlgebra k α β P
  let := affineQuotient_scalarTower k α β P
  let := affineQuotient_faithfulSMul k α β Q hB P hPQ
  let := affineQuotient_isDomain k α β Q hB P hPQ
  let := affineQuotient_finiteType k α β P
  let := affineQuotient_isLocalization k α β Q hB P hPQ
  let b : β → q.ResidueField :=
    fun i => quotientPrimeResidueAlgEquiv (k := k) P Q hPQ (splitResidueBeta k α β Q i)
  have hb : IsTranscendenceBasis k b :=
    quotientPrimeResidueAlgEquiv_basis P Q hPQ (splitResidueBeta k α β Q) hB
  have hd := affine_prime_dimension_of_closedPoint_presentation k
    (SplitPolynomial k α β ⧸ P) β C q b hb
    ((coefficientDenominators k α β).map (Ideal.Quotient.mk P)) m
    (affineClosedQuotientLocalEquiv k α β Q hB P hPQ)
  have hlocal := (localizationQuotientParametersEquiv P Q hPQ).ringKrullDim
  rw [IsLocalization.AtPrime.ringKrullDim_eq_height
    (quotientParameterPrime P Q hPQ) (Localization.AtPrime (quotientParameterPrime P Q hPQ))] at hlocal
  have hquot := @ringKrullDim_eq_of_ringEquiv
    ((SplitPolynomial k α β ⧸ P) ⧸ Q.map (Ideal.Quotient.mk P))
    (SplitPolynomial k α β ⧸ Q)
    (inferInstance : CommRing ((SplitPolynomial k α β ⧸ P) ⧸
      Q.map (Ideal.Quotient.mk P))).toCommSemiring
    (inferInstance : CommRing (SplitPolynomial k α β ⧸ Q)).toCommSemiring
    (DoubleQuot.quotQuotEquivQuotOfLE hPQ)
  change ringKrullDim ((SplitPolynomial k α β ⧸ P) ⧸ q) =
    ringKrullDim (SplitPolynomial k α β ⧸ Q) at hquot
  rw [← hlocal, hquot] at hd
  exact hd

end Split

section FinVariables
variable (k : Type*) [Field k] (n : ℕ)
variable (P Q : Ideal (MvPolynomial (Fin n) k)) [P.IsPrime] [Q.IsPrime]

theorem fin_polynomial_prime_pair_local_dimension (hPQ : P ≤ Q) :
    ringKrullDim (Localization.AtPrime Q ⧸ parameterLocalizedIdeal P Q) +
      ringKrullDim (MvPolynomial (Fin n) k ⧸ Q) =
        ringKrullDim (MvPolynomial (Fin n) k ⧸ P) := by
  classical
  obtain ⟨t, j, hfin, hj, hcoord, ht⟩ := exists_coordinate_basis_indices k n Q
  let : Finite t := hfin.to_subtype
  let e := coordinateBasisRenaming j hj k
  let P' := P.map e.toRingHom
  let Q' := Q.map e.toRingHom
  have : P'.IsPrime := Ideal.map_isPrime_of_equiv e
  have : Q'.IsPrime := Ideal.map_isPrime_of_equiv e
  have hpq : P' ≤ Q' := Ideal.map_mono hPQ
  have hb : IsTranscendenceBasis k (splitResidueBeta k (RemainingCoordinate j) t Q') :=
    coordinateSplitPrime_basis k Q t j hj hcoord ht
  have hd := split_polynomial_prime_pair_local_dimension k (RemainingCoordinate j) t P' Q' hpq hb
  have hl := (ringEquiv_localQuotient e.toRingEquiv P Q).ringKrullDim
  have hp := (Ideal.quotientEquiv P P' e.toRingEquiv rfl).ringKrullDim
  have hq := (Ideal.quotientEquiv Q Q' e.toRingEquiv rfl).ringKrullDim
  rw [← hl, ← hp, ← hq] at hd
  exact hd

end FinVariables

variable (k σ : Type*) [Field k] [Finite σ]
variable (P Q : Ideal (MvPolynomial σ k)) [P.IsPrime] [Q.IsPrime]

theorem polynomial_prime_pair_local_dimension (hPQ : P ≤ Q) :
    ringKrullDim (Localization.AtPrime Q ⧸ parameterLocalizedIdeal P Q) +
      ringKrullDim (MvPolynomial σ k ⧸ Q) = ringKrullDim (MvPolynomial σ k ⧸ P) := by
  classical
  let := Fintype.ofFinite σ
  let e : MvPolynomial σ k ≃ₐ[k] MvPolynomial (Fin (Fintype.card σ)) k :=
    MvPolynomial.renameEquiv k (Fintype.equivFin σ)
  let P' := P.map e.toRingHom
  let Q' := Q.map e.toRingHom
  have : P'.IsPrime := Ideal.map_isPrime_of_equiv e
  have : Q'.IsPrime := Ideal.map_isPrime_of_equiv e
  have hd := fin_polynomial_prime_pair_local_dimension k (Fintype.card σ) P' Q'
    (Ideal.map_mono hPQ)
  have hl := (ringEquiv_localQuotient e.toRingEquiv P Q).ringKrullDim
  have hp := (Ideal.quotientEquiv P P' e.toRingEquiv rfl).ringKrullDim
  have hq := (Ideal.quotientEquiv Q Q' e.toRingEquiv rfl).ringKrullDim
  rw [← hl, ← hp, ← hq] at hd
  exact hd

theorem polynomial_prime_pair_dimension (hPQ : P ≤ Q) :
    ((Q.map (Ideal.Quotient.mk P)).height : WithBot ℕ∞) +
      ringKrullDim (MvPolynomial σ k ⧸ Q) = ringKrullDim (MvPolynomial σ k ⧸ P) := by
  have hd := polynomial_prime_pair_local_dimension k σ P Q hPQ
  have hl := (localizationQuotientParametersEquiv P Q hPQ).ringKrullDim
  rw [IsLocalization.AtPrime.ringKrullDim_eq_height
    (quotientParameterPrime P Q hPQ) (Localization.AtPrime (quotientParameterPrime P Q hPQ))] at hl
  rw [hl] at hd
  exact hd

end PiExponentJets.W24

end

end OAI
end Source0216

-- Source: OAI/NumberTheory/PiExponent/LocalAlgebra/PrimeHypersurfaceEquidimension.lean
section Source0217
/-
Modification notice for the LogTwo project.
Derived from openai/math (Apache-2.0), revision adc7f1241b42e322a6451854ab7e4b4c146bf78a.
Original source: lean/OAI/NumberTheory/PiExponent/LocalAlgebra/PrimeHypersurfaceEquidimension.lean
Changes: Convert module/import declarations to the Lean 4.34 public module format.
See ../THIRD_PARTY_NOTICES.txt for provenance and the recorded changes.
-/

namespace OAI

namespace PiExponentJets.W24

variable (k σ : Type*) [Field k] [Finite σ]

theorem minimal_prime_hypersurface_dimension
    (P Q : Ideal (MvPolynomial σ k)) [P.IsPrime]
    (f : MvPolynomial σ k) (hfP : f ∉ P)
    (hQ : Q ∈ (P ⊔ Ideal.span {f}).minimalPrimes)
    (s : ℕ)
    (hdim : ringKrullDim (MvPolynomial σ k ⧸ P) = ((s + 2 : ℕ) : WithBot ℕ∞)) :
    ringKrullDim (MvPolynomial σ k ⧸ Q) = ((s + 1 : ℕ) : WithBot ℕ∞) := by
  let : Q.IsPrime := hQ.1.1
  have hd := polynomial_prime_pair_dimension k σ P Q (le_sup_left.trans hQ.1.2)
  rw [proper_prime_cut_relative_height_eq_one P Q f hfP hQ] at hd
  have he : ringKrullDim (MvPolynomial σ k ⧸ Q) + 1 =
      ((s + 1 : ℕ) : WithBot ℕ∞) + 1 := by
    calc
      ringKrullDim (MvPolynomial σ k ⧸ Q) + 1 =
          1 + ringKrullDim (MvPolynomial σ k ⧸ Q) := add_comm _ _
      _ = ringKrullDim (MvPolynomial σ k ⧸ P) := hd
      _ = ((s + 2 : ℕ) : WithBot ℕ∞) := hdim
      _ = ((s + 1 : ℕ) : WithBot ℕ∞) + 1 := by
        rw [show s + 2 = (s + 1) + 1 by omega, Nat.cast_add, Nat.cast_one]
  exact ENat.WithBot.add_one_cancel.mp he

end PiExponentJets.W24

end OAI
end Source0217

-- Source: OAI/NumberTheory/PiExponent/LocalAlgebra/HilbertDifferenceDegree.lean
section Source0218
/-
Modification notice for the LogTwo project.
Derived from openai/math (Apache-2.0), revision adc7f1241b42e322a6451854ab7e4b4c146bf78a.
Original source: lean/OAI/NumberTheory/PiExponent/LocalAlgebra/HilbertDifferenceDegree.lean
Changes: Convert module/import declarations to the Lean 4.34 public module format.
See ../THIRD_PARTY_NOTICES.txt for provenance and the recorded changes.
-/

namespace OAI

namespace PiExponentJets.W27
open Polynomial

theorem difference_taylor_coefficient (p : Polynomial ℚ) (s : ℕ)
    (hp : p.natDegree = s+1) (a : ℚ) :
    (p - Polynomial.taylor a p).coeff s = -a * (s+1 : ℚ) * p.leadingCoeff := by
  have hd : (Polynomial.hasseDeriv s p).natDegree ≤ 1 := by
    simpa [hp] using Polynomial.natDegree_hasseDeriv_le p s
  have hlin := Polynomial.eq_X_add_C_of_natDegree_le_one hd
  have h0 : (Polynomial.hasseDeriv s p).coeff 0 = p.coeff s := by
    simp [Polynomial.hasseDeriv_coeff]
  have h1 : (Polynomial.hasseDeriv s p).coeff 1 = (s+1 : ℚ) * p.leadingCoeff := by
    rw [Polynomial.hasseDeriv_coeff]
    simp only [Nat.add_comm 1 s, Nat.choose_succ_self_right, Nat.cast_add, Nat.cast_one]
    rw [← hp, Polynomial.coeff_natDegree]
  rw [Polynomial.coeff_sub, Polynomial.taylor_coeff, hlin]
  simp only [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_X]
  rw [h0, h1]
  ring

theorem difference_taylor_natDegree_le (p : Polynomial ℚ) (s : ℕ)
    (hp : p.natDegree = s+1) (a : ℚ) :
    (p - Polynomial.taylor a p).natDegree ≤ s := by
  apply Polynomial.natDegree_le_iff_coeff_eq_zero.mpr
  intro n hn
  rw [Polynomial.coeff_sub]
  by_cases he : n = s+1
  · subst n
    rw [← hp, Polynomial.coeff_natDegree, Polynomial.coeff_taylor_natDegree, sub_self]
  · have hlt : p.natDegree < n := by omega
    rw [Polynomial.coeff_eq_zero_of_natDegree_lt hlt,
      Polynomial.coeff_eq_zero_of_natDegree_lt (by simpa using hlt), sub_self]

theorem backward_difference_degree_and_leading
    (p : Polynomial ℚ) (s : ℕ) (hp : p.natDegree = s+1)
    (d : ℚ) (hd : d ≠ 0) :
    (p - Polynomial.taylor (-d) p).natDegree = s ∧
      (p - Polynomial.taylor (-d) p).leadingCoeff = d * (s+1 : ℚ) * p.leadingCoeff := by
  have hp0 : p ≠ 0 := by
    intro hz
    simp [hz] at hp
  have hs : (s+1 : ℚ) ≠ 0 := by positivity
  have hc : (p - Polynomial.taylor (-d) p).coeff s =
      d * (s+1 : ℚ) * p.leadingCoeff := by
    simpa using difference_taylor_coefficient p s hp (-d)
  have hcn : (p - Polynomial.taylor (-d) p).coeff s ≠ 0 := by
    rw [hc]
    exact mul_ne_zero (mul_ne_zero hd hs) (Polynomial.leadingCoeff_ne_zero.mpr hp0)
  have hdeg := Polynomial.natDegree_eq_of_le_of_coeff_ne_zero
    (difference_taylor_natDegree_le p s hp (-d)) hcn
  refine ⟨hdeg, ?_⟩
  simpa only [Polynomial.leadingCoeff, hdeg] using hc

theorem backward_difference_multiplicity
    (p : Polynomial ℚ) (s : ℕ) (hp : p.natDegree = s+1)
    (d : ℚ) (hd : d ≠ 0) :
    (p - Polynomial.taylor (-d) p).leadingCoeff *
        ((p - Polynomial.taylor (-d) p).natDegree.factorial : ℚ) =
      d * (p.leadingCoeff * (p.natDegree.factorial : ℚ)) := by
  obtain ⟨hdeg, hl⟩ := backward_difference_degree_and_leading p s hp d hd
  rw [hl, hdeg, hp, Nat.factorial_succ]
  push_cast
  ring

theorem backward_difference_eq_comp (p : Polynomial ℚ) (d : ℚ) :
    p - Polynomial.taylor (-d) p = p - p.comp (Polynomial.X - Polynomial.C d) := by
  simp only [Polynomial.taylor_apply, Polynomial.C_neg, sub_eq_add_neg]

end PiExponentJets.W27

end OAI
end Source0218

-- Source: OAI/NumberTheory/PiExponent/Geometry/ProperHypersurfaceHilbert.lean
section Source0219
/-
Modification notice for the LogTwo project.
Derived from openai/math (Apache-2.0), revision adc7f1241b42e322a6451854ab7e4b4c146bf78a.
Original source: lean/OAI/NumberTheory/PiExponent/Geometry/ProperHypersurfaceHilbert.lean
Changes: Convert module/import declarations to the Lean 4.34 public module format.
See ../THIRD_PARTY_NOTICES.txt for provenance and the recorded changes.
-/

namespace OAI

namespace PiExponentJets.W64

attribute [local instance] MvPolynomial.gradedAlgebra
variable {k σ : Type*} [Field k] [Finite σ]

omit [Finite σ] in
theorem prime_quotient_right_regular (P : Ideal (MvPolynomial σ k)) [P.IsPrime]
    (f : MvPolynomial σ k) (hfP : f ∉ P) :
    IsRightRegular (Ideal.Quotient.mk P f) := by
  have hf0 : Ideal.Quotient.mk P f ≠ 0 := by
    intro hz
    exact hfP (Ideal.Quotient.eq_zero_iff_mem.mp hz)
  intro x y hxy
  exact mul_right_cancel₀ hf0 hxy

theorem regular_hypersurface_polynomial_eventually
    (I : Ideal (MvPolynomial σ k))
    (hI : I.IsHomogeneous (MvPolynomial.homogeneousSubmodule σ k))
    {d : ℕ} (f : MvPolynomial σ k) (hf : f.IsHomogeneous d)
    (hreg : IsRightRegular (Ideal.Quotient.mk I f))
    (p : Polynomial ℚ) (N : ℕ)
    (hP : ∀ n : ℕ, N < n →
      (Module.finrank k (quotientSection I n) : ℚ) = p.eval (n : ℚ)) :
    ∀ n : ℕ, N+d < n →
      (Module.finrank k (quotientSection (Ideal.span {f} ⊔ I) n) : ℚ) =
        (p-shiftHilbertPolynomial p d).eval (n : ℚ) := by
  intro n hn
  have hdn : d ≤ n := by omega
  have hnP : N < n := by omega
  have hnshift : N < n-d := by omega
  have h := regular_hilbert_step I hI f hf hreg (n-d)
  rw [Nat.sub_add_cancel hdn] at h
  have hc : (Module.finrank k (quotientSection (Ideal.span {f} ⊔ I) n) : ℚ) +
      (Module.finrank k (quotientSection I (n-d)) : ℚ) =
      (Module.finrank k (quotientSection I n) : ℚ) := by
    exact_mod_cast h
  rw [hP n hnP, hP (n-d) hnshift] at hc
  rw [Polynomial.eval_sub, shiftHilbertPolynomial_eval p d n hdn]
  exact eq_sub_of_add_eq hc

theorem prime_hypersurface_actual_hilbert_degree
    (P : Ideal (MvPolynomial σ k)) [P.IsPrime]
    (hP : P.IsHomogeneous (MvPolynomial.homogeneousSubmodule σ k))
    {d : ℕ} (f : MvPolynomial σ k) (hf : f.IsHomogeneous d)
    (hfP : f ∉ P) (hd : 0 < d)
    (p : Polynomial ℚ) (N s : ℕ)
    (hp : ∀ n : ℕ, N < n →
      (Module.finrank k (quotientSection P n) : ℚ) = p.eval (n : ℚ))
    (hdegree : p.natDegree = s+1) :
    ∃ q : Polynomial ℚ,
      (∃ M : ℕ, ∀ n : ℕ, M < n →
        (Module.finrank k (quotientSection (Ideal.span {f} ⊔ P) n) : ℚ) = q.eval (n : ℚ)) ∧
      q.natDegree = s ∧
      q.leadingCoeff * (q.natDegree.factorial : ℚ) =
        (d : ℚ) * (p.leadingCoeff * (p.natDegree.factorial : ℚ)) := by
  have hdq : (d : ℚ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hd
  refine ⟨p-Polynomial.taylor (-(d : ℚ)) p, ⟨N+d, ?_⟩,
    (PiExponentJets.W27.backward_difference_degree_and_leading p s hdegree (d : ℚ) hdq).1,
    PiExponentJets.W27.backward_difference_multiplicity p s hdegree (d : ℚ) hdq⟩
  intro n hn
  rw [PiExponentJets.W27.backward_difference_eq_comp]
  exact regular_hypersurface_polynomial_eventually P hP f hf
    (prime_quotient_right_regular P f hfP) p N hp n hn

end PiExponentJets.W64

end OAI
end Source0219

-- Source: OAI/NumberTheory/PiExponent/LocalAlgebra/ComponentMultiplicitySum.lean
section Source0220
/-
Modification notice for the LogTwo project.
Derived from openai/math (Apache-2.0), revision adc7f1241b42e322a6451854ab7e4b4c146bf78a.
Original source: lean/OAI/NumberTheory/PiExponent/LocalAlgebra/ComponentMultiplicitySum.lean
Changes: Convert module/import declarations to the Lean 4.34 public module format.
See ../THIRD_PARTY_NOTICES.txt for provenance and the recorded changes.
-/

namespace OAI

namespace PiExponentJets.W22

open PiExponentJets.W64
open scoped BigOperators Classical
attribute [local instance] MvPolynomial.gradedAlgebra

theorem distinct_selected_factor_weight_le
    {τ β : Type*} [Fintype τ] (Q : τ → β) (hQinj : Function.Injective Q)
    (P : β) (W : τ → ℚ) (V : ℚ) (hV : 0 ≤ V)
    (hmatch : ∀ a, P = Q a → W a = V) :
    (∑ a, if P = Q a then W a else 0) ≤ V := by
  classical
  by_cases hex : ∃ a, P = Q a
  · obtain ⟨a, ha⟩ := hex
    have hsum : (∑ b, if P = Q b then W b else 0) = W a := by
      rw [Finset.sum_eq_single a]
      · simp only [ite_eq_left ha]
      · intro b _ hba
        have hb : P ≠ Q b := by
          intro hb
          exact hba (hQinj (hb.symm.trans ha))
        exact ite_eq_right hb
      · intro hnot
        exact False.elim (hnot (Finset.mem_univ a))
    rw [hsum, hmatch a ha]
  · have hzero : (∑ a, if P = Q a then W a else 0) = 0 := by
      apply Finset.sum_eq_zero
      intro a _
      exact ite_eq_right (fun ha => hex ⟨a, ha⟩)
    rw [hzero]
    exact hV

theorem grouped_count_weighted_sum_eq
    {τ β : Type*} [Fintype τ] (n : ℕ) (P : ℕ → β) (Q : τ → β) (W : τ → ℚ) :
    (∑ a, ((∑ i ∈ Finset.range n, if P i = Q a then 1 else 0 : ℕ) : ℚ) * W a) =
      ∑ i ∈ Finset.range n, ∑ a, if P i = Q a then W a else 0 := by
  classical
  simp only [Nat.cast_sum, Nat.cast_ite, Nat.cast_one, Nat.cast_zero,
    Finset.sum_mul, ite_mul, one_mul, zero_mul]
  exact Finset.sum_comm

variable {k σ τ : Type*} [Field k] [Fintype σ] [Fintype τ]

theorem component_multiplicity_sum_bound
    (I : Ideal (MvPolynomial σ k))
    (hI : I.IsHomogeneous (MvPolynomial.homogeneousSubmodule σ k))
    (Q : τ → Ideal (MvPolynomial σ k)) [∀ a, (Q a).IsPrime]
    (hQinj : Function.Injective Q)
    (hQhom : ∀ a, (Q a).IsHomogeneous (MvPolynomial.homogeneousSubmodule σ k))
    (hQ : ∀ a, Q a ∈ I.minimalPrimes)
    (v : τ → σ) (hv : ∀ a, MvPolynomial.X (v a) ∉ Q a)
    (hdegree : ∀ a, (actualHP (Q a) (hQhom a)).natDegree = (actualHP I hI).natDegree) :
    ∃ m : τ → ℕ,
      (∀ a, Module.length (Localization.AtPrime (Q a))
        (Localization.AtPrime (Q a) ⧸ I.map
          (algebraMap (MvPolynomial σ k) (Localization.AtPrime (Q a)))) = m a) ∧
      (∀ a, 1 ≤ actualMultiplicity (Q a) (hQhom a) (actualHP I hI).natDegree) ∧
      (∑ a, (m a : ℚ) * actualMultiplicity (Q a) (hQhom a)
        (actualHP I hI).natDegree) ≤ actualMultiplicity I hI (actualHP I hI).natDegree := by
  classical
  obtain ⟨n, J, f, degrees, hmono, hstart, hend, hdata⟩ :=
    exists_homogeneous_cyclic_filtration_nat I hI
  let D := (actualHP I hI).natDegree
  have hJ : ∀ i, (J i).IsHomogeneous (MvPolynomial.homogeneousSubmodule σ k) := by
    intro i
    by_cases hi : i < n
    · exact (hdata i hi).1
    · have heq : J i = ⊤ := by
        apply top_unique
        rw [← hend]
        exact (monotone_nat_of_le_succ hmono) (Nat.le_of_not_gt hi)
      rw [heq]
      exact Ideal.IsHomogeneous.top (MvPolynomial.homogeneousSubmodule σ k)
  have hIle : ∀ i, I ≤ J i := fun i =>
    hstart.symm.le.trans ((monotone_nat_of_le_succ hmono) (Nat.zero_le i))
  let P : Fin n → Ideal (MvPolynomial σ k) := fun i => (J i).colon {f i}
  have hP : ∀ i : Fin n, (P i).IsHomogeneous (MvPolynomial.homogeneousSubmodule σ k) :=
    fun i => homogeneous_colon_singleton (J i) (hJ i) (hdata i i.isLt).2.1
  have hIP : ∀ i : Fin n, I ≤ P i := fun i =>
    (hIle i).trans (ideal_le_colon_singleton (J i) (f i))
  have hPdeg : ∀ i : Fin n, (actualHP (P i) (hP i)).natDegree ≤ D :=
    fun i => actualHP_natDegree_antitone hI (hP i) (hIP i)
  let U : ℕ → ℚ := fun i => actualMultiplicity (J i) (hJ i) D
  let V : ℕ → ℚ := fun i =>
    if hi : i < n then actualMultiplicity (P ⟨i, hi⟩) (hP ⟨i, hi⟩) D else 0
  have hUstep : ∀ i < n, U i = U (i+1) + V i := by
    intro i hi
    simp only [U, V, dite_eq_left hi]
    exact actualMultiplicity_cyclic_step (J i) (J (i+1)) (hJ i) (hJ (i+1))
      (f i) (hdata i hi).2.1 (hdata i hi).2.2.2.2 (hP ⟨i, hi⟩) D (hPdeg ⟨i, hi⟩)
  have hUzero : U 0 = actualMultiplicity I hI D :=
    actualMultiplicity_congr (hJ 0) hI hstart D
  have hUend : U n = 0 := by
    have htop := Ideal.IsHomogeneous.top (MvPolynomial.homogeneousSubmodule σ k)
    exact (actualMultiplicity_congr (hJ n) htop hend D).trans (actualMultiplicity_top htop D)
  have hsum : actualMultiplicity I hI D = ∑ i ∈ Finset.range n, V i := by
    have ht := rational_filtration_telescope U V n hUstep
    rw [hUzero, hUend, add_zero] at ht
    exact ht
  let m : τ → ℕ := fun a =>
    ∑ i ∈ Finset.range n, if (J i).colon {f i} = Q a then 1 else 0
  have hm : ∀ a, Module.length (Localization.AtPrime (Q a))
      (Localization.AtPrime (Q a) ⧸ I.map
        (algebraMap (MvPolynomial σ k) (Localization.AtPrime (Q a)))) = m a := by
    intro a
    have hlength := localized_cyclic_filtration_length I (Q a) (hQ a)
      J hmono hstart n hend f
      (fun i hi => (hdata i hi).2.2.2.2) (fun i hi => (hdata i hi).2.2.2.1)
    rw [hlength]
    simp only [m, Nat.cast_sum, Nat.cast_ite, Nat.cast_one, Nat.cast_zero]
  have hpositive : ∀ a, 1 ≤ actualMultiplicity (Q a) (hQhom a) D := by
    intro a
    obtain ⟨N, hN⟩ := actualHP_eventually (Q a) (hQhom a)
    exact W27.prime_eventual_hilbert_coefficient_ge_one (Q a) (v a) (hv a)
      (actualHP (Q a) (hQhom a)) (N+1) D
      (fun t ht => (hN t (by omega)).symm) (hdegree a)
  refine ⟨m, hm, hpositive, ?_⟩
  change (∑ a, (m a : ℚ) * actualMultiplicity (Q a) (hQhom a) D) ≤
    actualMultiplicity I hI D
  rw [hsum]
  have hgroup := grouped_count_weighted_sum_eq n
    (fun i => (J i).colon {f i}) Q (fun a => actualMultiplicity (Q a) (hQhom a) D)
  change (∑ a, (m a : ℚ) * actualMultiplicity (Q a) (hQhom a) D) = _ at hgroup
  rw [hgroup]
  apply Finset.sum_le_sum
  intro i hi
  have hin : i < n := Finset.mem_range.mp hi
  have hnonneg : 0 ≤ V i := by
    simp only [V, dite_eq_left hin]
    exact actualMultiplicity_nonneg (P ⟨i, hin⟩) (hP ⟨i, hin⟩) D (hPdeg ⟨i, hin⟩)
  apply distinct_selected_factor_weight_le Q hQinj ((J i).colon {f i})
    (fun a => actualMultiplicity (Q a) (hQhom a) D) (V i) hnonneg
  intro a heq
  simp only [V, dite_eq_left hin]
  exact (actualMultiplicity_congr (hP ⟨i, hin⟩) (hQhom a) heq D).symm

end PiExponentJets.W22

end OAI
end Source0220

-- Source: OAI/NumberTheory/PiExponent/LocalAlgebra/PrimeCutBudget.lean
section Source0221
/-
Modification notice for the LogTwo project.
Derived from openai/math (Apache-2.0), revision adc7f1241b42e322a6451854ab7e4b4c146bf78a.
Original source: lean/OAI/NumberTheory/PiExponent/LocalAlgebra/PrimeCutBudget.lean
Changes: Convert module/import declarations to the Lean 4.34 public module format.
See ../THIRD_PARTY_NOTICES.txt for provenance and the recorded changes.
-/

namespace OAI

namespace PiExponentJets.W22

open PiExponentJets.W64
open scoped BigOperators Classical
attribute [local instance] MvPolynomial.gradedAlgebra

variable {k σ τ : Type*} [Field k] [Fintype σ] [Fintype τ]

noncomputable def actualLocalLength (I Q : Ideal (MvPolynomial σ k)) [Q.IsPrime] : ℕ :=
  (Module.length (Localization.AtPrime Q)
    (Localization.AtPrime Q ⧸ I.map
      (algebraMap (MvPolynomial σ k) (Localization.AtPrime Q)))).toNat

theorem actualLocalLength_spec
    (I Q : Ideal (MvPolynomial σ k)) [Q.IsPrime]
    (hI : I.IsHomogeneous (MvPolynomial.homogeneousSubmodule σ k))
    (hQ : Q ∈ I.minimalPrimes) :
    Module.length (Localization.AtPrime Q)
      (Localization.AtPrime Q ⧸ I.map
        (algebraMap (MvPolynomial σ k) (Localization.AtPrime Q))) = actualLocalLength I Q := by
  obtain ⟨n, J, f, d, hmono, hstart, hend, hdata, hlength⟩ :=
    exists_homogeneous_component_length_count I Q hI hQ
  let m : ℕ := ∑ i ∈ Finset.range n, if (J i).colon {f i} = Q then 1 else 0
  have hm : Module.length (Localization.AtPrime Q)
      (Localization.AtPrime Q ⧸ I.map
        (algebraMap (MvPolynomial σ k) (Localization.AtPrime Q))) = m := by
    rw [hlength]
    simp only [m, Nat.cast_sum, Nat.cast_ite, Nat.cast_one, Nat.cast_zero]
  simp only [actualLocalLength, hm, ENat.toNat_natCast]

omit [Fintype σ] in
theorem primeCut_isHomogeneous
    (P : Ideal (MvPolynomial σ k))
    (hP : P.IsHomogeneous (MvPolynomial.homogeneousSubmodule σ k))
    {d : ℕ} (f : MvPolynomial σ k) (hf : f.IsHomogeneous d) :
    (Ideal.span {f} ⊔ P).IsHomogeneous (MvPolynomial.homogeneousSubmodule σ k) := by
  have hsingle : (Ideal.span {f}).IsHomogeneous (MvPolynomial.homogeneousSubmodule σ k) := by
    apply Ideal.homogeneous_span (MvPolynomial.homogeneousSubmodule σ k)
    intro x hx
    have hxf : x = f := Set.mem_singleton_iff.mp hx
    subst x
    exact ⟨d, hf⟩
  exact hsingle.sup hP

theorem actualHP_prime_cut_degree_multiplicity
    (P : Ideal (MvPolynomial σ k)) [P.IsPrime]
    (hP : P.IsHomogeneous (MvPolynomial.homogeneousSubmodule σ k))
    {d : ℕ} (f : MvPolynomial σ k) (hf : f.IsHomogeneous d)
    (hfP : f ∉ P) (hd : 0 < d) (s : ℕ)
    (hdegree : (actualHP P hP).natDegree = s+1) :
    (actualHP (Ideal.span {f} ⊔ P) (primeCut_isHomogeneous P hP f hf)).natDegree = s ∧
      actualMultiplicity (Ideal.span {f} ⊔ P) (primeCut_isHomogeneous P hP f hf) s =
        (d : ℚ) * actualMultiplicity P hP (s+1) := by
  obtain ⟨N, hN⟩ := actualHP_eventually P hP
  obtain ⟨q, ⟨M, hM⟩, hqdegree, hqmult⟩ :=
    prime_hypersurface_actual_hilbert_degree P hP f hf hfP hd
      (actualHP P hP) N s hN hdegree
  have hq : actualHP (Ideal.span {f} ⊔ P) (primeCut_isHomogeneous P hP f hf) = q :=
    actualHP_unique _ _ q M hM
  refine ⟨by rw [hq]; exact hqdegree, ?_⟩
  unfold actualMultiplicity
  rw [hq]
  simpa only [Polynomial.leadingCoeff, hqdegree, hdegree] using hqmult

theorem prime_cut_component_budget
    (P : Ideal (MvPolynomial σ k)) [P.IsPrime]
    (hP : P.IsHomogeneous (MvPolynomial.homogeneousSubmodule σ k))
    {d : ℕ} (f : MvPolynomial σ k) (hf : f.IsHomogeneous d)
    (hfP : f ∉ P) (hd : 0 < d) (s : ℕ)
    (hdegree : (actualHP P hP).natDegree = s+1)
    (Q : τ → Ideal (MvPolynomial σ k)) [∀ a, (Q a).IsPrime]
    (hQinj : Function.Injective Q)
    (hQhom : ∀ a, (Q a).IsHomogeneous (MvPolynomial.homogeneousSubmodule σ k))
    (hQ : ∀ a, Q a ∈ (Ideal.span {f} ⊔ P).minimalPrimes)
    (v : τ → σ) (hv : ∀ a, MvPolynomial.X (v a) ∉ Q a)
    (hchildDegree : ∀ a, (actualHP (Q a) (hQhom a)).natDegree = s) :
    (∑ a, (actualLocalLength (Ideal.span {f} ⊔ P) (Q a) : ℚ) *
      actualMultiplicity (Q a) (hQhom a) s) ≤
      (d : ℚ) * actualMultiplicity P hP (s+1) := by
  have hI := primeCut_isHomogeneous P hP f hf
  obtain ⟨hIdegree, hImult⟩ := actualHP_prime_cut_degree_multiplicity
    P hP f hf hfP hd s hdegree
  obtain ⟨m, hm, hpositive, hbudget⟩ := component_multiplicity_sum_bound
    (Ideal.span {f} ⊔ P) hI Q hQinj hQhom hQ v hv
      (fun a => (hchildDegree a).trans hIdegree.symm)
  have hmactual : ∀ a, actualLocalLength (Ideal.span {f} ⊔ P) (Q a) = m a := by
    intro a
    unfold actualLocalLength
    rw [hm a, ENat.toNat_natCast]
  simpa only [hIdegree, hmactual, hImult] using hbudget

theorem actualHP_natDegree_of_prime_dimension
    (Q : Ideal (MvPolynomial σ k)) [Q.IsPrime]
    (hQ : Q.IsHomogeneous (MvPolynomial.homogeneousSubmodule σ k))
    (v : σ) (hv : MvPolynomial.X v ∉ Q) (s : ℕ)
    (hdim : ringKrullDim (MvPolynomial σ k ⧸ Q) = (s+1 : ℕ)) :
    (actualHP Q hQ).natDegree = s := by
  obtain ⟨N, hN⟩ := actualHP_eventually Q hQ
  have h := W24.prime_hilbert_natDegree_add_one_eq_krullDim Q hQ v hv
    (actualHP Q hQ) (N+1) (fun n hn => (hN n (by omega)).symm)
  have heq : (actualHP Q hQ).natDegree + 1 = s+1 := by exact_mod_cast h.trans hdim
  omega

end PiExponentJets.W22

end OAI
end Source0221

-- Source: OAI/NumberTheory/PiExponent/LocalAlgebra/RetainedIntersectionCycles.lean
section Source0222
-- Modified in this edition: unused plain lemmas removed; see reduction.json.
/-
Modification notice for the LogTwo project.
Derived from openai/math (Apache-2.0), revision adc7f1241b42e322a6451854ab7e4b4c146bf78a.
Original source: lean/OAI/NumberTheory/PiExponent/LocalAlgebra/RetainedIntersectionCycles.lean
Changes: Convert module/import declarations to the Lean 4.34 public module format.
See ../THIRD_PARTY_NOTICES.txt for provenance and the recorded changes.
-/

namespace OAI

namespace PiExponentJets.W22

open scoped BigOperators Classical
attribute [local instance] MvPolynomial.gradedAlgebra

universe u v w

def ProjectiveComponent (k : Type u) (σ : Type v) [Field k] :=
  {P : Ideal (MvPolynomial σ k) // P.IsPrime ∧
    P.IsHomogeneous (MvPolynomial.homogeneousSubmodule σ k) ∧
    ∃ i : σ, MvPolynomial.X i ∉ P}

namespace ProjectiveComponent

variable {k : Type u} {σ : Type v} [Field k]

instance (P : ProjectiveComponent k σ) : P.val.IsPrime := P.property.1

theorem homogeneous (P : ProjectiveComponent k σ) :
    P.val.IsHomogeneous (MvPolynomial.homogeneousSubmodule σ k) := P.property.2.1

noncomputable def coordinate (P : ProjectiveComponent k σ) : σ :=
  P.property.2.2.choose

theorem coordinate_not_mem (P : ProjectiveComponent k σ) :
    MvPolynomial.X P.coordinate ∉ P.val := P.property.2.2.choose_spec

variable [Fintype σ]

noncomputable def hilbertDegree (P : ProjectiveComponent k σ) : ℚ :=
  actualMultiplicity P.val P.homogeneous (actualHP P.val P.homogeneous).natDegree

theorem hilbertDegree_ge_one (P : ProjectiveComponent k σ) : 1 ≤ P.hilbertDegree := by
  obtain ⟨N, hN⟩ := actualHP_eventually P.val P.homogeneous
  exact W27.prime_eventual_hilbert_coefficient_ge_one P.val P.coordinate P.coordinate_not_mem
    (actualHP P.val P.homogeneous) (N+1) (actualHP P.val P.homogeneous).natDegree
    (fun n hn => (hN n (by omega)).symm) rfl

end ProjectiveComponent

structure RetainedPrimeCycle (k : Type u) (σ : Type v) [Field k] where
  Index : Type w
  finiteIndex : Fintype Index
  component : Index → ProjectiveComponent k σ
  coefficient : Index → ℕ

namespace RetainedPrimeCycle

variable {k : Type u} {σ : Type v} [Field k] [Fintype σ]

instance (C : RetainedPrimeCycle.{u,v,w} k σ) : Fintype C.Index := C.finiteIndex

noncomputable def degree (C : RetainedPrimeCycle.{u,v,w} k σ) : ℚ :=
  ∑ a, (C.coefficient a : ℚ) * (C.component a).hilbertDegree

noncomputable def coefficientAt (C : RetainedPrimeCycle.{u,v,w} k σ)
    (P : ProjectiveComponent k σ) : ℕ :=
  ∑ a, if C.component a = P then C.coefficient a else 0

theorem coefficientAt_le_degree (C : RetainedPrimeCycle.{u,v,w} k σ)
    (P : ProjectiveComponent k σ) : (C.coefficientAt P : ℚ) ≤ C.degree := by
  unfold coefficientAt degree
  rw [Nat.cast_sum]
  apply Finset.sum_le_sum
  intro a _
  by_cases h : C.component a = P
  · simp only [ite_eq_left h]
    have hc : (0 : ℚ) ≤ C.coefficient a := Nat.cast_nonneg _
    have hd := (C.component a).hilbertDegree_ge_one
    nlinarith
  · simp only [ite_eq_right h, Nat.cast_zero]
    exact mul_nonneg (Nat.cast_nonneg _) (le_trans (by norm_num)
      (C.component a).hilbertDegree_ge_one)

structure ProperCut (C : RetainedPrimeCycle.{u,v,w} k σ) where
  polynomial : MvPolynomial σ k
  polynomialDegree : ℕ
  positiveDegree : 0 < polynomialDegree
  homogeneous : polynomial.IsHomogeneous polynomialDegree
  avoidsParent : ∀ a, polynomial ∉ (C.component a).val
  dimensionIndex : ℕ
  parentDegree : ∀ a,
    (actualHP (C.component a).val (C.component a).homogeneous).natDegree = dimensionIndex+1
  Child : C.Index → Type w
  finiteChild : ∀ a, Fintype (Child a)
  child : ∀ a, Child a → ProjectiveComponent k σ
  distinctChild : ∀ a, Function.Injective (child a)
  minimalChild : ∀ a b,
    (child a b).val ∈ (Ideal.span {polynomial} ⊔ (C.component a).val).minimalPrimes
  childDegree : ∀ a b,
    (actualHP (child a b).val (child a b).homogeneous).natDegree = dimensionIndex

namespace ProperCut

variable {C : RetainedPrimeCycle.{u,v,w} k σ}

instance (F : ProperCut C) (a : C.Index) : Fintype (F.Child a) := F.finiteChild a

noncomputable def cutLength (F : ProperCut C) (a : C.Index) (b : F.Child a) : ℕ :=
  actualLocalLength (Ideal.span {F.polynomial} ⊔ (C.component a).val) (F.child a b).val

noncomputable def next (F : ProperCut C) : RetainedPrimeCycle.{u,v,w} k σ where
  Index := Σ a : C.Index, F.Child a
  finiteIndex := inferInstance
  component := fun x => F.child x.1 x.2
  coefficient := fun x => C.coefficient x.1 * F.cutLength x.1 x.2

@[simp] theorem next_component (F : ProperCut C) (a : C.Index) (b : F.Child a) :
    F.next.component ⟨a,b⟩ = F.child a b := rfl

@[simp] theorem next_coefficient (F : ProperCut C) (a : C.Index) (b : F.Child a) :
    F.next.coefficient ⟨a,b⟩ = C.coefficient a * F.cutLength a b := rfl

def CoversBelow (F : ProperCut C) (T : Ideal (MvPolynomial σ k)) : Prop :=
  ∀ a Q, Q ∈ (Ideal.span {F.polynomial} ⊔ (C.component a).val).minimalPrimes →
    Q ≤ T → ∃ b, (F.child a b).val = Q

theorem parent_budget (F : ProperCut C) (a : C.Index) :
    (∑ b, (F.cutLength a b : ℚ) * (F.child a b).hilbertDegree) ≤
      (F.polynomialDegree : ℚ) * (C.component a).hilbertDegree := by
  have hinj : Function.Injective (fun b : F.Child a => (F.child a b).val) := by
    intro b c h
    exact F.distinctChild a (Subtype.ext h)
  have h := prime_cut_component_budget (C.component a).val (C.component a).homogeneous
    F.polynomial F.homogeneous (F.avoidsParent a) F.positiveDegree F.dimensionIndex
    (F.parentDegree a) (fun b : F.Child a => (F.child a b).val) hinj
    (fun b => (F.child a b).homogeneous) (F.minimalChild a)
    (fun b => (F.child a b).coordinate) (fun b => (F.child a b).coordinate_not_mem)
    (F.childDegree a)
  simpa only [cutLength, ProjectiveComponent.hilbertDegree, F.childDegree, F.parentDegree] using h

theorem degree_next_le (F : ProperCut C) :
    F.next.degree ≤ (F.polynomialDegree : ℚ) * C.degree := by
  change (∑ x : Σ a : C.Index, F.Child a,
    ((C.coefficient x.1 * F.cutLength x.1 x.2 : ℕ) : ℚ) *
      (F.child x.1 x.2).hilbertDegree) ≤ _
  rw [Fintype.sum_sigma]
  calc
    _ ≤ ∑ a, (C.coefficient a : ℚ) *
        ((F.polynomialDegree : ℚ) * (C.component a).hilbertDegree) := by
      apply Finset.sum_le_sum
      intro a _
      simpa only [Nat.cast_mul, mul_assoc, Finset.mul_sum] using
        mul_le_mul_of_nonneg_left (F.parent_budget a) (Nat.cast_nonneg (C.coefficient a))
    _ = (F.polynomialDegree : ℚ) * C.degree := by
      rw [degree, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro a _
      ring

end ProperCut

inductive ProperCutHistory (C₀ : RetainedPrimeCycle.{u,v,w} k σ) :
    RetainedPrimeCycle.{u,v,w} k σ → ℕ → Prop
  | nil : ProperCutHistory C₀ C₀ 1
  | step {C : RetainedPrimeCycle.{u,v,w} k σ} {e : ℕ}
      (previous : ProperCutHistory C₀ C e) (F : ProperCut C) :
      ProperCutHistory C₀ F.next (e * F.polynomialDegree)

theorem ProperCutHistory.degree_bound
    {C₀ C : RetainedPrimeCycle.{u,v,w} k σ} {e : ℕ}
    (h : ProperCutHistory C₀ C e) : C.degree ≤ (e : ℚ) * C₀.degree := by
  induction h with
  | nil => simp
  | @step C e previous F ih =>
    calc
      F.next.degree ≤ (F.polynomialDegree : ℚ) * C.degree := F.degree_next_le
      _ ≤ (F.polynomialDegree : ℚ) * ((e : ℚ) * C₀.degree) :=
        mul_le_mul_of_nonneg_left ih (Nat.cast_nonneg F.polynomialDegree)
      _ = ((e * F.polynomialDegree : ℕ) : ℚ) * C₀.degree := by
        rw [Nat.cast_mul]
        ring

theorem ProperCutHistory.coefficient_bound
    {C₀ C : RetainedPrimeCycle.{u,v,w} k σ} {e : ℕ}
    (h : ProperCutHistory C₀ C e) (P : ProjectiveComponent k σ) :
    (C.coefficientAt P : ℚ) ≤ (e : ℚ) * C₀.degree :=
  (C.coefficientAt_le_degree P).trans h.degree_bound

end RetainedPrimeCycle
end PiExponentJets.W22

end OAI
end Source0222

-- Source: OAI/NumberTheory/PiExponent/LocalAlgebra/RetainedMinimalPrimeFamily.lean
section Source0223
-- Modified in this edition: unused plain lemmas removed; see reduction.json.
/-
Modification notice for the LogTwo project.
Derived from openai/math (Apache-2.0), revision adc7f1241b42e322a6451854ab7e4b4c146bf78a.
Original source: lean/OAI/NumberTheory/PiExponent/LocalAlgebra/RetainedMinimalPrimeFamily.lean
Changes: Convert module/import declarations to the Lean 4.34 public module format.
See ../THIRD_PARTY_NOTICES.txt for provenance and the recorded changes.
-/

namespace OAI

namespace PiExponentJets.W22

open scoped Classical
attribute [local instance] MvPolynomial.gradedAlgebra

universe u
variable {k σ : Type u} [Field k] [Fintype σ]

def RetainedMinimalPrime (I T : Ideal (MvPolynomial σ k)) :=
  {Q : Ideal (MvPolynomial σ k) // Q ∈ I.minimalPrimes ∧ Q ≤ T}

namespace RetainedMinimalPrime

variable {I T : Ideal (MvPolynomial σ k)}

noncomputable instance finiteFamily (I T : Ideal (MvPolynomial σ k)) :
    Fintype (RetainedMinimalPrime I T) := by
  have hfinite : {Q : Ideal (MvPolynomial σ k) | Q ∈ I.minimalPrimes ∧ Q ≤ T}.Finite :=
    (Ideal.finite_minimalPrimes_of_isNoetherianRing (MvPolynomial σ k) I).subset
      (fun _ h => h.1)
  exact hfinite.fintype

instance (Q : RetainedMinimalPrime I T) : Q.val.IsPrime := Q.property.1.1.1

noncomputable def toComponent
    (hI : I.IsHomogeneous (MvPolynomial.homogeneousSubmodule σ k))
    (v : σ) (hv : MvPolynomial.X v ∉ T) (Q : RetainedMinimalPrime I T) :
    ProjectiveComponent k σ :=
  ⟨Q.val, Q.property.1.1.1,
    PiExponentSiegel.W17.ConeLocalLength.minimalPrime_isHomogeneous I Q.val hI Q.property.1,
    v, fun h => hv (Q.property.2 h)⟩

omit [Fintype σ] in
@[simp] theorem toComponent_val
    (hI : I.IsHomogeneous (MvPolynomial.homogeneousSubmodule σ k))
    (v : σ) (hv : MvPolynomial.X v ∉ T) (Q : RetainedMinimalPrime I T) :
    (toComponent hI v hv Q).val = Q.val := rfl

omit [Fintype σ] in
theorem toComponent_injective
    (hI : I.IsHomogeneous (MvPolynomial.homogeneousSubmodule σ k))
    (v : σ) (hv : MvPolynomial.X v ∉ T) :
    Function.Injective (toComponent hI v hv : RetainedMinimalPrime I T → ProjectiveComponent k σ) := by
  intro Q R h
  exact Subtype.ext (congrArg (fun P : ProjectiveComponent k σ => P.val) h)

end RetainedMinimalPrime

namespace RetainedPrimeCycle

noncomputable def canonicalRetainedCut
    (C : RetainedPrimeCycle.{u,u,u} k σ)
    (f : MvPolynomial σ k) (d : ℕ) (hd : 0 < d) (hf : f.IsHomogeneous d)
    (havoid : ∀ a, f ∉ (C.component a).val)
    (s : ℕ) (hparent : ∀ a,
      (actualHP (C.component a).val (C.component a).homogeneous).natDegree = s+1)
    (T : Ideal (MvPolynomial σ k)) (v : σ) (hv : MvPolynomial.X v ∉ T)
    (hchildDim : ∀ a
      (Q : RetainedMinimalPrime (Ideal.span {f} ⊔ (C.component a).val) T),
      ringKrullDim (MvPolynomial σ k ⧸ Q.val) = (s+1 : ℕ)) : ProperCut C where
  polynomial := f
  polynomialDegree := d
  positiveDegree := hd
  homogeneous := hf
  avoidsParent := havoid
  dimensionIndex := s
  parentDegree := hparent
  Child := fun a => RetainedMinimalPrime (Ideal.span {f} ⊔ (C.component a).val) T
  finiteChild := fun _ => inferInstance
  child := fun a => RetainedMinimalPrime.toComponent
    (primeCut_isHomogeneous _ (C.component a).homogeneous f hf) v hv
  distinctChild := fun a => RetainedMinimalPrime.toComponent_injective
    (primeCut_isHomogeneous _ (C.component a).homogeneous f hf) v hv
  minimalChild := fun _ Q => Q.property.1
  childDegree := fun a Q => actualHP_natDegree_of_prime_dimension Q.val
    (RetainedMinimalPrime.toComponent
      (primeCut_isHomogeneous _ (C.component a).homogeneous f hf) v hv Q).homogeneous
    v (fun h => hv (Q.property.2 h)) s (hchildDim a Q)

end RetainedPrimeCycle
end PiExponentJets.W22

end OAI
end Source0223

-- Source: OAI/NumberTheory/PiExponent/LocalAlgebra/EquidimensionalRetainedCut.lean
section Source0224
-- Modified in this edition: unused plain lemmas removed; see reduction.json.
/-
Modification notice for the LogTwo project.
Derived from openai/math (Apache-2.0), revision adc7f1241b42e322a6451854ab7e4b4c146bf78a.
Original source: lean/OAI/NumberTheory/PiExponent/LocalAlgebra/EquidimensionalRetainedCut.lean
Changes: Convert module/import declarations to the Lean 4.34 public module format.
See ../THIRD_PARTY_NOTICES.txt for provenance and the recorded changes.
-/

namespace OAI

namespace PiExponentJets.W22.RetainedPrimeCycle

attribute [local instance] MvPolynomial.gradedAlgebra
universe u
variable {k σ : Type u} [Field k] [Fintype σ]

theorem retainedChild_dimension
    (C : RetainedPrimeCycle.{u,u,u} k σ) (f : MvPolynomial σ k)
    (havoid : ∀ a, f ∉ (C.component a).val) (s : ℕ)
    (hparent : ∀ a,
      (actualHP (C.component a).val (C.component a).homogeneous).natDegree = s+1)
    (T : Ideal (MvPolynomial σ k)) (a : C.Index)
    (Q : RetainedMinimalPrime (Ideal.span {f} ⊔ (C.component a).val) T) :
    ringKrullDim (MvPolynomial σ k ⧸ Q.val) = (s+1 : ℕ) := by
  obtain ⟨N, hN⟩ := actualHP_eventually (C.component a).val (C.component a).homogeneous
  have hPdim := W24.prime_hilbert_natDegree_add_one_eq_krullDim (C.component a).val
    (C.component a).homogeneous (C.component a).coordinate (C.component a).coordinate_not_mem
    (actualHP (C.component a).val (C.component a).homogeneous) (N+1)
    (fun n hn => (hN n (by omega)).symm)
  have hdim : ringKrullDim (MvPolynomial σ k ⧸ (C.component a).val) = (s+2 : ℕ) := by
    calc
      _ = ((actualHP (C.component a).val (C.component a).homogeneous).natDegree + 1 :
          WithBot ℕ∞) := hPdim.symm
      _ = ((s+2 : ℕ) : WithBot ℕ∞) := by
        rw [← Nat.cast_one, ← Nat.cast_add]
        exact congrArg (fun n : ℕ => (n : WithBot ℕ∞)) (by rw [hparent a])
  exact W24.minimal_prime_hypersurface_dimension k σ (C.component a).val Q.val f
    (havoid a) (by simpa only [sup_comm] using Q.property.1) s hdim

noncomputable def equidimensionalRetainedCut
    (C : RetainedPrimeCycle.{u,u,u} k σ)
    (f : MvPolynomial σ k) (d : ℕ) (hd : 0 < d) (hf : f.IsHomogeneous d)
    (havoid : ∀ a, f ∉ (C.component a).val)
    (s : ℕ) (hparent : ∀ a,
      (actualHP (C.component a).val (C.component a).homogeneous).natDegree = s+1)
    (T : Ideal (MvPolynomial σ k)) (v : σ) (hv : MvPolynomial.X v ∉ T) : ProperCut C :=
  canonicalRetainedCut C f d hd hf havoid s hparent T v hv
    (retainedChild_dimension C f havoid s hparent T)

end PiExponentJets.W22.RetainedPrimeCycle

end OAI
end Source0224

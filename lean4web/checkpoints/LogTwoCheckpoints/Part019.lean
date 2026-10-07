/- Generated rc4 checkpoint for LogTwo.
Modified from the reduced edition: new imports, separate module compilation,
and synchronous elaboration. Original source blocks and notices are retained.
See ../../../THIRD_PARTY_NOTICES.txt and ../../reduction.json.
-/
module
public import LogTwoCheckpoints.Part001
public import LogTwoCheckpoints.Part012
public import LogTwoCheckpoints.Part013
public import LogTwoCheckpoints.Part014
public import LogTwoCheckpoints.Part015
public import LogTwoCheckpoints.Part016
public import LogTwoCheckpoints.Part017
public import LogTwoCheckpoints.Part018
public import Batteries.Logic
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.EpiMono
public import Mathlib.Algebra.Homology.DerivedCategory.Ext.ExactSequences
public import Mathlib.Algebra.Homology.DerivedCategory.Ext.Linear
public import Mathlib.Algebra.Module.LocalizedModule.Away
public import Mathlib.AlgebraicGeometry.FunctionField
public import Mathlib.AlgebraicGeometry.IdealSheaf.Functorial
public import Mathlib.AlgebraicGeometry.Modules.Tilde
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Basic
public import Mathlib.Analysis.Complex.Polynomial.Basic
public import Mathlib.Data.Opposite
public import Mathlib.Data.SetLike.Basic
public import Mathlib.RingTheory.DiscreteValuationRing.Basic
public import Mathlib.RingTheory.Jacobson.Artinian
public import Mathlib.RingTheory.Localization.Away.AdjoinRoot
public import Mathlib.RingTheory.MvPolynomial.Ideal
public import Mathlib.RingTheory.Noetherian.Nilpotent
public import Mathlib.RingTheory.OrderOfVanishing.Basic
@[expose] public section
set_option Elab.async false

-- Source: OAI/NumberTheory/PiExponent/Cohomology/PencilCohomologyLaurent.lean
section Source0475
/-
Modification notice for the LogTwo project.
Derived from openai/math (Apache-2.0), revision adc7f1241b42e322a6451854ab7e4b4c146bf78a.
Original source: lean/OAI/NumberTheory/PiExponent/Cohomology/PencilCohomologyLaurent.lean
Changes: Convert module/import declarations to the Lean 4.34 public module format.
See ../THIRD_PARTY_NOTICES.txt for provenance and the recorded changes.
-/

namespace OAI

noncomputable section

namespace PiExponentSeshadri.LaurentTails
open LaurentPolynomial
open scoped LaurentPolynomial
variable {K M : Type*} [Field K] [AddCommGroup M]
  [Module K M] [Module K[T;T⁻¹] M] [IsScalarTower K K[T;T⁻¹] M]

omit [IsScalarTower K K[T;T⁻¹] M] in
lemma positive_tail (A : Submodule K M)
    (hA : ∀ x ∈ A, (T 1 : K[T;T⁻¹]) • x ∈ A) {x : M} (hx : x ∈ A) :
    ∀ n : ℕ, (T (n : ℤ) : K[T;T⁻¹]) • x ∈ A := by
  intro n
  induction n with
  | zero => simpa using hx
  | succ n ih =>
    simpa only [Nat.cast_add, Nat.cast_one, add_comm (n : ℤ) 1, T_add, mul_smul]
      using hA _ ih

omit [IsScalarTower K K[T;T⁻¹] M] in
lemma negative_tail (B : Submodule K M)
    (hB : ∀ x ∈ B, (T (-1) : K[T;T⁻¹]) • x ∈ B) {x : M} (hx : x ∈ B) :
    ∀ n : ℕ, (T (-(n : ℤ)) : K[T;T⁻¹]) • x ∈ B := by
  intro n
  induction n with
  | zero => simpa using hx
  | succ n ih =>
    have he : -((n + 1 : ℕ) : ℤ) = -1 + -(n : ℤ) := by omega
    simpa only [he, T_add, mul_smul] using hB _ ih

theorem quotient_finite [Module.Finite K[T;T⁻¹] M]
    (A B : Submodule K M)
    (hA : ∀ x ∈ A, (T 1 : K[T;T⁻¹]) • x ∈ A)
    (hB : ∀ x ∈ B, (T (-1) : K[T;T⁻¹]) • x ∈ B)
    (locA : ∀ x : M, ∃ n : ℕ, (T (n : ℤ) : K[T;T⁻¹]) • x ∈ A)
    (locB : ∀ x : M, ∃ n : ℕ, (T (-(n : ℤ)) : K[T;T⁻¹]) • x ∈ B) :
    Module.Finite K (M ⧸ (A ⊔ B)) := by
  classical
  obtain ⟨n,s,hs⟩ := Module.Finite.exists_fin (R := K[T;T⁻¹]) (M := M)
  choose a ha using fun i : Fin n => locA (s i)
  choose b hb using fun i : Fin n => locB (s i)
  let q := (A ⊔ B).mkQ
  let J := (i : Fin n) × ↥(Finset.Icc (-(b i : ℤ)) (a i : ℤ))
  let g : J → M ⧸ (A ⊔ B) := fun v => q ((T v.2.val : K[T;T⁻¹]) • s v.1)
  let W := Submodule.span K (Set.range g)
  have monomial (i : Fin n) (z : ℤ) : q ((T z : K[T;T⁻¹]) • s i) ∈ W := by
    by_cases hzA : (a i : ℤ) ≤ z
    · have he : z = ((z - a i).toNat : ℤ) + a i := by omega
      have hm : (T z : K[T;T⁻¹]) • s i ∈ A := by
        rw [he, T_add, mul_smul]
        exact positive_tail A hA (ha i) _
      have hq : q ((T z : K[T;T⁻¹]) • s i) = 0 :=
        (Submodule.Quotient.mk_eq_zero (A ⊔ B)).mpr ((show A ≤ A ⊔ B from le_sup_left) hm)
      rw [hq]; exact W.zero_mem
    · by_cases hzB : z ≤ -(b i : ℤ)
      · have he : z = -((-(b i : ℤ) - z).toNat : ℤ) + -(b i : ℤ) := by omega
        have hm : (T z : K[T;T⁻¹]) • s i ∈ B := by
          rw [he, T_add, mul_smul]
          exact negative_tail B hB (hb i) _
        have hq : q ((T z : K[T;T⁻¹]) • s i) = 0 :=
          (Submodule.Quotient.mk_eq_zero (A ⊔ B)).mpr ((show B ≤ A ⊔ B from le_sup_right) hm)
        rw [hq]; exact W.zero_mem
      · exact Submodule.subset_span ⟨⟨i,⟨z,Finset.mem_Icc.mpr (by omega)⟩⟩,rfl⟩
  have scalar_monomial (i : Fin n) (p : K[T;T⁻¹]) : q (p • s i) ∈ W := by
    induction p using LaurentPolynomial.induction_on' with
    | add p p' hp hp' => simpa only [add_smul, map_add] using W.add_mem hp hp'
    | C_mul_T z c =>
      rw [mul_smul, C_eq_algebraMap, algebraMap_smul, map_smul]
      exact W.smul_mem c (monomial i z)
  have spans : W = ⊤ := by
    apply top_unique
    intro x hx
    clear hx
    obtain ⟨m,rfl⟩ := (A ⊔ B).mkQ_surjective x
    have hm : m ∈ Submodule.span K[T;T⁻¹] (Set.range s) := hs ▸ Submodule.mem_top
    have hp : ∀ p : K[T;T⁻¹], q (p • m) ∈ W := by
      induction hm using Submodule.span_induction with
      | mem m hm => obtain ⟨i,rfl⟩ := hm; exact scalar_monomial i
      | zero => intro p; simp
      | add x y hx hy ihx ihy =>
        intro p
        simpa only [smul_add, map_add] using W.add_mem (ihx p) (ihy p)
      | smul a x hx ih => intro p; simpa only [smul_smul] using ih (p * a)
    change q m ∈ W
    simpa only [one_smul] using hp 1
  exact Module.Finite.of_fg_top (spans ▸ Submodule.fg_span (Set.finite_range g))

end PiExponentSeshadri.LaurentTails

namespace PiExponentSeshadri.LaurentCech
open LaurentPolynomial
open scoped LaurentPolynomial Polynomial
variable {K N P Q : Type*} [Field K]
  [AddCommGroup N] [AddCommGroup P] [AddCommGroup Q]
  [Module K N] [Module K P] [Module K Q]
  [Module K[X] N] [Module K[X] P] [Module K[X] Q]
  [IsScalarTower K K[X] N] [IsScalarTower K K[X] P] [IsScalarTower K K[X] Q]

omit [IsScalarTower K K[X] P] in
theorem cokernel_finite [Module.Finite K[X] N]
    (f : N →ₗ[K[X]] Q) [IsLocalizedModule.Away (Polynomial.X : K[X]) f]
    (g : P →ₗ[K] Q)
    (inverse_coordinate : ∀ y : P,
      (Polynomial.X : K[X]) • g ((Polynomial.X : K[X]) • y) = g y)
    (opposite_denominators : ∀ x : Q, ∃ n : ℕ, ∃ y : P,
      ((Polynomial.X : K[X])^n) • g y = x) :
    Module.Finite K (Q ⧸ ((f.restrictScalars K).range ⊔ g.range)) := by
  let : Module K[T;T⁻¹] Q := IsLocalizedModule.module
    (.powers (Polynomial.X : K[X])) f
  let : IsScalarTower K[X] K[T;T⁻¹] Q :=
    IsLocalizedModule.isScalarTower_module (.powers (Polynomial.X : K[X])) f
  let : IsScalarTower K K[T;T⁻¹] Q := .of_algebraMap_smul (fun c x => by
    rw [← C_eq_algebraMap, ← Polynomial.toLaurent_C,
      ← algebraMap_eq_toLaurent, algebraMap_smul]
    exact algebraMap_smul K[X] c x)
  let : Module.Finite K[T;T⁻¹] Q :=
    Module.Finite.of_isLocalizedModule (.powers (Polynomial.X : K[X])) f
  have pos (n : ℕ) (x : Q) : (T (n : ℤ) : K[T;T⁻¹]) • x =
      ((Polynomial.X : K[X])^n) • x := by
    rw [← Polynomial.toLaurent_X_pow, ← algebraMap_eq_toLaurent, algebraMap_smul]
  have pos1 (x : Q) : (T 1 : K[T;T⁻¹]) • x = (Polynomial.X : K[X]) • x := by
    simpa only [Nat.cast_one, pow_one] using pos 1 x
  have cancel (n : ℕ) (x : Q) : (T (-(n : ℤ)) : K[T;T⁻¹]) •
      ((T (n : ℤ) : K[T;T⁻¹]) • x) = x := by
    rw [← mul_smul, ← T_add, neg_add_cancel, T_zero, one_smul]
  apply LaurentTails.quotient_finite (A := (f.restrictScalars K).range) (B := g.range)
  · rintro _ ⟨y,rfl⟩
    refine ⟨(Polynomial.X : K[X]) • y, ?_⟩
    change f ((Polynomial.X : K[X]) • y) = (T 1 : K[T;T⁻¹]) • f y
    rw [map_smul, pos1]
  · rintro _ ⟨y,rfl⟩
    refine ⟨(Polynomial.X : K[X]) • y, ?_⟩
    have h := congrArg (fun z : Q => (T (-1) : K[T;T⁻¹]) • z)
      (inverse_coordinate y)
    rw [← pos1] at h
    have hc (z : Q) : (T (-1) : K[T;T⁻¹]) • ((T 1 : K[T;T⁻¹]) • z) = z := by
      simpa only [Nat.cast_one] using cancel 1 z
    rw [hc] at h
    exact h
  · intro x
    obtain ⟨n,y,hy⟩ := (inferInstance : IsLocalizedModule.Away (Polynomial.X : K[X]) f).surj _ _ x
    refine ⟨n, y, ?_⟩
    change f y = (T (n : ℤ) : K[T;T⁻¹]) • x
    rw [pos]
    exact hy.symm
  · intro x
    obtain ⟨n,y,hy⟩ := opposite_denominators x
    refine ⟨n,y,?_⟩
    rw [← hy, ← pos n, cancel n]
end PiExponentSeshadri.LaurentCech

namespace PiExponentSeshadri.LaurentLattices

section
open LaurentPolynomial Polynomial Module
open scoped LaurentPolynomial
variable {K : Type*} [Field K]

instance : IsPrincipalIdealRing K[T;T⁻¹] where
  principal I := by
    obtain ⟨a,ha⟩ := (IsPrincipalIdealRing.principal (I.under K[X])).principal
    refine ⟨⟨algebraMap K[X] K[T;T⁻¹] a, ?_⟩⟩
    rw [← IsLocalization.map_under (Submonoid.powers (Polynomial.X : K[X]))
      K[T;T⁻¹] I, ha, Ideal.map_span, Set.image_singleton]

def boundedBelow {ι M : Type*} [AddCommGroup M] [Module K[T;T⁻¹] M]
    [Module K M] [IsScalarTower K K[T;T⁻¹] M]
    (b : Basis ι K[T;T⁻¹] M) (l : ℤ) : Submodule K M :=
  ⨅ i, (AddMonoidAlgebra.supported K K (Set.Ici l)).comap
    (((Finsupp.lapply i).comp b.repr.toLinearMap).restrictScalars K)

def boundedAbove {ι M : Type*} [AddCommGroup M] [Module K[T;T⁻¹] M]
    [Module K M] [IsScalarTower K K[T;T⁻¹] M]
    (b : Basis ι K[T;T⁻¹] M) (u : ℤ) : Submodule K M :=
  ⨅ i, (AddMonoidAlgebra.supported K K (Set.Iic u)).comap
    (((Finsupp.lapply i).comp b.repr.toLinearMap).restrictScalars K)

variable {ι M : Type*} [AddCommGroup M] [Module K[T;T⁻¹] M]
  [Module K M] [IsScalarTower K K[T;T⁻¹] M]

lemma mem_boundedBelow (b : Basis ι K[T;T⁻¹] M) (l : ℤ) (x : M) :
    x ∈ boundedBelow b l ↔ ∀ i z, z < l → ((b.repr x) i).coeff z = 0 := by
  simp only [boundedBelow, Submodule.mem_iInf, Submodule.mem_comap,
    LinearMap.coe_restrictScalars, LinearMap.coe_comp, LinearEquiv.coe_coe,
    Function.comp_apply, Finsupp.lapply_apply, AddMonoidAlgebra.mem_supported',
    Set.mem_Ici, not_le]

lemma mem_boundedAbove (b : Basis ι K[T;T⁻¹] M) (u : ℤ) (x : M) :
    x ∈ boundedAbove b u ↔ ∀ i z, u < z → ((b.repr x) i).coeff z = 0 := by
  simp only [boundedAbove, Submodule.mem_iInf, Submodule.mem_comap,
    LinearMap.coe_restrictScalars, LinearMap.coe_comp, LinearEquiv.coe_coe,
    Function.comp_apply, Finsupp.lapply_apply, AddMonoidAlgebra.mem_supported',
    Set.mem_Iic, not_le]

lemma coeff_T_mul (p : K[T;T⁻¹]) (n z : ℤ) :
    (T n * p).coeff z = p.coeff (z-n) := by
  simp only [T, AddMonoidAlgebra.coeff_single_mul_apply, one_mul]
  congr 1
  omega

lemma below_shift (b : Basis ι K[T;T⁻¹] M) (l : ℤ) {x : M}
    (hx : x ∈ boundedBelow b l) (n : ℕ) :
    (T (n : ℤ) : K[T;T⁻¹]) • x ∈ boundedBelow b l := by
  rw [mem_boundedBelow] at hx ⊢
  intro i z hz
  rw [map_smul, Finsupp.smul_apply, smul_eq_mul, coeff_T_mul]
  exact hx i _ (by omega)

lemma above_shift (b : Basis ι K[T;T⁻¹] M) (u : ℤ) {x : M}
    (hx : x ∈ boundedAbove b u) (n : ℕ) :
    (T (-(n : ℤ)) : K[T;T⁻¹]) • x ∈ boundedAbove b u := by
  rw [mem_boundedAbove] at hx ⊢
  intro i z hz
  rw [map_smul, Finsupp.smul_apply, smul_eq_mul, coeff_T_mul]
  exact hx i _ (by omega)

theorem band_finite [Fintype ι] (b : Basis ι K[T;T⁻¹] M) (l u : ℤ) :
    Module.Finite K ↥(boundedBelow b l ⊓ boundedAbove b u) := by
  classical
  let W := boundedBelow b l ⊓ boundedAbove b u
  let J := ι × ↥(Finset.Icc l u)
  let φ : W →ₗ[K] (J → K) := LinearMap.pi (fun j =>
    (Finsupp.lapply j.2.val).comp ((AddMonoidAlgebra.coeffLinearEquiv K).toLinearMap.comp
      ((((Finsupp.lapply j.1).comp b.repr.toLinearMap).restrictScalars K).comp W.subtype)))
  apply Module.Finite.of_injective φ
  intro x y hxy
  apply Subtype.ext
  apply b.repr.injective
  ext i z
  by_cases hzL : z < l
  · rw [(mem_boundedBelow b l x.val).mp x.property.1 i z hzL,
      (mem_boundedBelow b l y.val).mp y.property.1 i z hzL]
  · by_cases hzU : u < z
    · rw [(mem_boundedAbove b u x.val).mp x.property.2 i z hzU,
        (mem_boundedAbove b u y.val).mp y.property.2 i z hzU]
    · exact congrFun hxy (i,⟨z,Finset.mem_Icc.mpr (by omega)⟩)

lemma finite_generators_bounded [Fintype ι] {κ : Type*} [Fintype κ]
    (b : Basis ι K[T;T⁻¹] M) (s : κ → M) :
    ∃ l u : ℤ, ∀ j, s j ∈ boundedBelow b l ∧ s j ∈ boundedAbove b u := by
  classical
  let S : Set ℤ := ⋃ i, ⋃ j, (↑((b.repr (s j)) i).coeff.support : Set ℤ)
  have hS : S.Finite := Set.finite_iUnion fun i => Set.finite_iUnion fun j =>
    Finset.finite_toSet _
  obtain ⟨l,hl⟩ := hS.bddBelow
  obtain ⟨u,hu⟩ := hS.bddAbove
  refine ⟨l,u,fun j => ⟨?_,?_⟩⟩
  · rw [mem_boundedBelow]
    intro i z hz
    by_contra hn
    have hm : z ∈ S := Set.mem_iUnion.mpr ⟨i,Set.mem_iUnion.mpr
      ⟨j,Finsupp.mem_support_iff.mpr hn⟩⟩
    exact (not_le.mpr hz) (hl hm)
  · rw [mem_boundedAbove]
    intro i z hz
    by_contra hn
    have hm : z ∈ S := Set.mem_iUnion.mpr ⟨i,Set.mem_iUnion.mpr
      ⟨j,Finsupp.mem_support_iff.mpr hn⟩⟩
    exact (not_le.mpr hz) (hu hm)

theorem intersection_finite [Module.Finite K[T;T⁻¹] M]
    [Module.IsTorsionFree K[T;T⁻¹] M]
    (A B : Submodule K M) {κ τ : Type*} [Fintype κ] [Fintype τ]
    (s : κ → M) (t : τ → M)
    (hA : A ≤ Submodule.span K (Set.range (fun j : κ × ℕ =>
      (T (j.2 : ℤ) : K[T;T⁻¹]) • s j.1)))
    (hB : B ≤ Submodule.span K (Set.range (fun j : τ × ℕ =>
      (T (-(j.2 : ℤ)) : K[T;T⁻¹]) • t j.1))) :
    Module.Finite K ↥(A ⊓ B) := by
  let b := Module.Free.chooseBasis K[T;T⁻¹] M
  obtain ⟨l,_,hs⟩ := finite_generators_bounded b s
  obtain ⟨_,u,ht⟩ := finite_generators_bounded b t
  have hbelow : A ≤ boundedBelow b l := hA.trans (Submodule.span_le.mpr (by
    rintro _ ⟨⟨j,n⟩,rfl⟩
    exact below_shift b l (hs j).1 n))
  have habove : B ≤ boundedAbove b u := hB.trans (Submodule.span_le.mpr (by
    rintro _ ⟨⟨j,n⟩,rfl⟩
    exact above_shift b u (ht j).2 n))
  let := band_finite b l u
  exact Module.Finite.of_injective (Submodule.inclusion (inf_le_inf hbelow habove))
    (Submodule.inclusion_injective _)

end

section
open LaurentPolynomial Polynomial Module
open scoped LaurentPolynomial
variable {K : Type*} [Field K]

instance laurent_finiteType : Algebra.FiniteType K K[T;T⁻¹] := by
  let : IsScalarTower K K[X] K[T;T⁻¹] := IsScalarTower.of_algebraMap_eq (fun c => by
    simp only [Polynomial.algebraMap_eq, algebraMap_eq_toLaurent, Polynomial.toLaurent_C,
      ← LaurentPolynomial.C_eq_algebraMap])
  let : Algebra.FinitePresentation K[X] K[T;T⁻¹] :=
    IsLocalization.Away.finitePresentation (Polynomial.X : K[X])
  let : Algebra.FiniteType K[X] K[T;T⁻¹] := inferInstance
  exact Algebra.FiniteType.trans (inferInstance : Algebra.FiniteType K K[X]) inferInstance

lemma quotient_finite (a : K[T;T⁻¹]) (ha : a ≠ 0) :
    Module.Finite K (K[T;T⁻¹] ⧸ Ideal.span {a}) := by
  have hlen := isFiniteLength_quotient_span_singleton K[T;T⁻¹]
    (mem_nonZeroDivisors_of_ne_zero ha)
  let := (isFiniteLength_iff_isNoetherian_isArtinian.mp hlen).2
  let : IsArtinianRing (K[T;T⁻¹] ⧸ Ideal.span {a}) :=
    isArtinian_of_tower K[T;T⁻¹] inferInstance
  exact Module.finite_of_isArtinianRing K _

theorem torsion_finite {M : Type*} [AddCommGroup M] [Module K[T;T⁻¹] M]
    [Module K M] [IsScalarTower K K[T;T⁻¹] M] [Module.Finite K[T;T⁻¹] M]
    (hM : Module.IsTorsion K[T;T⁻¹] M) : Module.Finite K M := by
  obtain ⟨a,ha,hn⟩ := Submodule.annihilator_top_inter_nonZeroDivisors hM
  have hkill : Module.IsTorsionBy K[T;T⁻¹] M a := fun x =>
    Submodule.mem_annihilator.mp ha x trivial
  let hset : Module.IsTorsionBySet K[T;T⁻¹] M (Ideal.span {a}) :=
    (Module.isTorsionBySet_span_singleton_iff a).mpr hkill
  let := hset.module
  let : IsScalarTower K[T;T⁻¹] (K[T;T⁻¹] ⧸ Ideal.span {a}) M := hset.isScalarTower
  let : IsScalarTower K (K[T;T⁻¹] ⧸ Ideal.span {a}) M := hset.isScalarTower
  let : Module.Finite (K[T;T⁻¹] ⧸ Ideal.span {a}) M :=
    Module.Finite.of_restrictScalars_finite K[T;T⁻¹] _ M
  let := quotient_finite a (nonZeroDivisors.ne_zero hn)
  exact Module.Finite.trans (K[T;T⁻¹] ⧸ Ideal.span {a}) M
end

section
open LaurentPolynomial Polynomial Module
open scoped LaurentPolynomial
variable {K : Type*} [Field K]
variable {M : Type*} [AddCommGroup M] [Module K[T;T⁻¹] M]
  [Module K M] [IsScalarTower K K[T;T⁻¹] M]

theorem intersection_finite_general [Module.Finite K[T;T⁻¹] M]
    (A B : Submodule K M) {κ τ : Type*} [Fintype κ] [Fintype τ]
    (s : κ → M) (t : τ → M)
    (hA : A ≤ Submodule.span K (Set.range (fun j : κ × ℕ =>
      (T (j.2 : ℤ) : K[T;T⁻¹]) • s j.1)))
    (hB : B ≤ Submodule.span K (Set.range (fun j : τ × ℕ =>
      (T (-(j.2 : ℤ)) : K[T;T⁻¹]) • t j.1))) :
    Module.Finite K ↥(A ⊓ B) := by
  let D := Submodule.torsion K[T;T⁻¹] M
  let q := D.mkQ.restrictScalars K
  let : Module.Finite K D := torsion_finite Submodule.torsion_isTorsion
  have ha : A.map q ≤ Submodule.span K (Set.range (fun j : κ × ℕ =>
      (T (j.2 : ℤ) : K[T;T⁻¹]) • q (s j.1))) := by
    apply (Submodule.map_mono hA).trans
    rw [Submodule.map_span]
    apply Submodule.span_mono
    rintro _ ⟨_, ⟨j,rfl⟩,rfl⟩
    exact ⟨j, (D.mkQ.map_smul _ _).symm⟩
  have hb : B.map q ≤ Submodule.span K (Set.range (fun j : τ × ℕ =>
      (T (-(j.2 : ℤ)) : K[T;T⁻¹]) • q (t j.1))) := by
    apply (Submodule.map_mono hB).trans
    rw [Submodule.map_span]
    apply Submodule.span_mono
    rintro _ ⟨_, ⟨j,rfl⟩,rfl⟩
    exact ⟨j, (D.mkQ.map_smul _ _).symm⟩
  let := intersection_finite (A.map q) (B.map q) (fun i => q (s i))
    (fun i => q (t i)) ha hb
  let f : ↥(A ⊓ B) →ₗ[K] ↥(A.map q ⊓ B.map q) :=
    (q.comp (A ⊓ B).subtype).codRestrict _ (fun x =>
      ⟨Submodule.mem_map.mpr ⟨x.val,x.property.1,rfl⟩,
        Submodule.mem_map.mpr ⟨x.val,x.property.2,rfl⟩⟩)
  let g : f.ker →ₗ[K] D :=
    (((A ⊓ B).subtype.comp f.ker.subtype).codRestrict (D.restrictScalars K)
      (fun x => by
        have h : q x.val.val = 0 := congrArg Subtype.val x.property
        exact (Submodule.Quotient.mk_eq_zero D).mp h))
  let : Module.Finite K f.ker := Module.Finite.of_injective g (by
    intro x y h
    apply Subtype.ext
    apply Subtype.ext
    exact congrArg (fun z : D => (z : M)) h)
  let : Module.Finite K (↥(A ⊓ B) ⧸ f.ker) :=
    Module.Finite.equiv f.quotKerEquivRange.symm
  exact Module.Finite.of_submodule_quotient f.ker
end

open LaurentPolynomial Polynomial Module
open scoped LaurentPolynomial
variable {K N Q : Type*} [Field K] [AddCommGroup N] [AddCommGroup Q]
  [Module K N] [Module K Q] [Module K[X] N] [IsScalarTower K K[X] N]
  [Module K[T;T⁻¹] Q] [IsScalarTower K K[T;T⁻¹] Q]

omit [IsScalarTower K K[T;T⁻¹] Q] in
lemma range_le_lattice {ι : Type*} [Fintype ι] (s : ι → N)
    (hs : Submodule.span K[X] (Set.range s) = ⊤) (g : N →ₗ[K] Q) (d : ℤ)
    (hpow : ∀ (n : ℕ) (x : N), g ((Polynomial.X : K[X])^n • x) =
      (T (d*n) : K[T;T⁻¹]) • g x) :
    g.range ≤ Submodule.span K (Set.range (fun j : ι × ℕ =>
      (T (d*j.2) : K[T;T⁻¹]) • g (s j.1))) := by
  classical
  rintro _ ⟨x,rfl⟩
  obtain ⟨f,hf⟩ := (Submodule.mem_span_range_iff_exists_fun K[X]).mp
    (show x ∈ Submodule.span K[X] (Set.range s) from hs ▸ trivial)
  rw [← hf, map_sum]
  apply Submodule.sum_mem
  intro i hi
  rw [← Polynomial.sum_C_mul_X_pow_eq (f i), Polynomial.sum, Finset.sum_smul, map_sum]
  apply Submodule.sum_mem
  intro n hn
  rw [mul_smul, ← Polynomial.algebraMap_eq, algebraMap_smul, map_smul, hpow]
  exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨(i,n),rfl⟩)

theorem range_intersection_finite [Module.Finite K[X] N]
    {P : Type*} [AddCommGroup P] [Module K P] [Module K[X] P]
    [IsScalarTower K K[X] P] [Module.Finite K[X] P]
    [Module.Finite K[T;T⁻¹] Q]
    (f : N →ₗ[K] Q) (g : P →ₗ[K] Q)
    (hf : ∀ x, f ((Polynomial.X : K[X]) • x) = (T 1 : K[T;T⁻¹]) • f x)
    (hg : ∀ x, g ((Polynomial.X : K[X]) • x) = (T (-1) : K[T;T⁻¹]) • g x) :
    Module.Finite K ↥(f.range ⊓ g.range) := by
  obtain ⟨n,s,hs⟩ := Module.Finite.exists_fin (R := K[X]) (M := N)
  obtain ⟨m,t,ht⟩ := Module.Finite.exists_fin (R := K[X]) (M := P)
  have hp (j : ℕ) (x : N) : f ((Polynomial.X : K[X])^j • x) =
      (T (1*(j : ℤ)) : K[T;T⁻¹]) • f x := by
    induction j with
    | zero => simp
    | succ j ih =>
      rw [pow_succ', mul_smul, hf, ih, ← mul_smul, ← T_add]
      congr 2
      omega
  have hn (j : ℕ) (x : P) : g ((Polynomial.X : K[X])^j • x) =
      (T ((-1)*(j : ℤ)) : K[T;T⁻¹]) • g x := by
    induction j with
    | zero => simp
    | succ j ih =>
      rw [pow_succ', mul_smul, hg, ih, ← mul_smul, ← T_add]
      congr 2
      omega
  apply intersection_finite_general f.range g.range (fun i => f (s i)) (fun i => g (t i))
  · simpa only [one_mul] using range_le_lattice s hs f 1 hp
  · simpa only [neg_one_mul] using range_le_lattice t ht g (-1) hn
end PiExponentSeshadri.LaurentLattices

namespace PiExponentSeshadri.LaurentCech
open LaurentPolynomial
open scoped LaurentPolynomial Polynomial
variable {K N P Q : Type*} [Field K]
  [AddCommGroup N] [AddCommGroup P] [AddCommGroup Q]
  [Module K N] [Module K P] [Module K Q]
  [Module K[X] N] [Module K[X] P] [Module K[X] Q]
  [IsScalarTower K K[X] N] [IsScalarTower K K[X] P] [IsScalarTower K K[X] Q]

theorem intersection_finite [Module.Finite K[X] N] [Module.Finite K[X] P]
    (f : N →ₗ[K[X]] Q) [IsLocalizedModule.Away (Polynomial.X : K[X]) f]
    (g : P →ₗ[K] Q)
    (inverse_coordinate : ∀ y : P,
      (Polynomial.X : K[X]) • g ((Polynomial.X : K[X]) • y) = g y) :
    Module.Finite K ↥((f.restrictScalars K).range ⊓ g.range) := by
  let : Module K[T;T⁻¹] Q := IsLocalizedModule.module
    (.powers (Polynomial.X : K[X])) f
  let : IsScalarTower K[X] K[T;T⁻¹] Q :=
    IsLocalizedModule.isScalarTower_module (.powers (Polynomial.X : K[X])) f
  let : IsScalarTower K K[T;T⁻¹] Q := .of_algebraMap_smul (fun c x => by
    rw [← C_eq_algebraMap, ← Polynomial.toLaurent_C,
      ← algebraMap_eq_toLaurent, algebraMap_smul]
    exact algebraMap_smul K[X] c x)
  let : Module.Finite K[T;T⁻¹] Q :=
    Module.Finite.of_isLocalizedModule (.powers (Polynomial.X : K[X])) f
  have pos (n : ℕ) (x : Q) : (T (n : ℤ) : K[T;T⁻¹]) • x =
      ((Polynomial.X : K[X])^n) • x := by
    rw [← Polynomial.toLaurent_X_pow, ← algebraMap_eq_toLaurent, algebraMap_smul]
  have pos1 (x : Q) : (T 1 : K[T;T⁻¹]) • x = (Polynomial.X : K[X]) • x := by
    simpa only [Nat.cast_one, pow_one] using pos 1 x
  have cancel (n : ℕ) (x : Q) : (T (-(n : ℤ)) : K[T;T⁻¹]) •
      ((T (n : ℤ) : K[T;T⁻¹]) • x) = x := by
    rw [← mul_smul, ← T_add, neg_add_cancel, T_zero, one_smul]
  apply LaurentLattices.range_intersection_finite (f.restrictScalars K) g
  · intro x
    change f ((Polynomial.X : K[X]) • x) = (T 1 : K[T;T⁻¹]) • f x
    rw [map_smul, pos1]
  · intro y
    have h := congrArg (fun z : Q => (T (-1) : K[T;T⁻¹]) • z)
      (inverse_coordinate y)
    rw [← pos1] at h
    have hc (z : Q) : (T (-1) : K[T;T⁻¹]) • ((T 1 : K[T;T⁻¹]) • z) = z := by
      simpa only [Nat.cast_one] using cancel 1 z
    rw [hc] at h
    exact h
end PiExponentSeshadri.LaurentCech

end

end OAI
end Source0475

-- Source: OAI/NumberTheory/PiExponent/Cohomology/PencilCohomologyCech.lean
section Source0476
/-
Modification notice for the LogTwo project.
Derived from openai/math (Apache-2.0), revision adc7f1241b42e322a6451854ab7e4b4c146bf78a.
Original source: lean/OAI/NumberTheory/PiExponent/Cohomology/PencilCohomologyCech.lean
Changes: Convert module/import declarations to the Lean 4.34 public module format.
Expose private helpers and adjust helper names where needed for module compatibility.
See ../THIRD_PARTY_NOTICES.txt for provenance and the recorded changes.
-/

namespace OAI

noncomputable section

namespace PiExponentSeshadri.ExtCokernel
open CategoryTheory CategoryTheory.Abelian
universe w v u t
variable {K : Type t} [CommRing K] {C : Type u} [Category.{v} C] [Abelian C]
  [Linear K C] [HasExt.{w} C] {S : ShortComplex C}

def quotientEquiv (hS : S.ShortExact) (M : C)
    (hvan : ∀ x : Ext S.X₂ M 1, x = 0) :
    ((S.X₁ ⟶ M) ⧸ (LinearMap.range
      (Linear.leftComp K M S.f))) ≃ₗ[K] Ext S.X₃ M 1 := by
  let d : (S.X₁ ⟶ M) →ₗ[K] Ext S.X₃ M 1 :=
    (hS.extClass.precompOfLinear K M (add_zero 1)).comp Ext.linearEquiv₀.symm.toLinearMap
  have hd : Function.Surjective d := by
    intro x
    obtain ⟨y,hy⟩ := Ext.contravariant_sequence_exact₃ hS M x (hvan _) (n₀ := 0) rfl
    refine ⟨Ext.linearEquiv₀ (R := K) y, ?_⟩
    change hS.extClass.comp (Ext.mk₀ (Ext.linearEquiv₀ (R := K) y)) (add_zero 1) = x
    rwa [Ext.mk₀_linearEquiv₀_apply]
  have hk : LinearMap.range (Linear.leftComp K M S.f) = d.ker := by
    ext f
    constructor
    · rintro ⟨g,rfl⟩
      change hS.extClass.comp (Ext.mk₀ (S.f ≫ g)) (add_zero 1) = 0
      rw [← Ext.mk₀_comp_mk₀]
      exact ShortComplex.ShortExact.extClass_comp_assoc hS _
    · intro hf
      change hS.extClass.comp (Ext.mk₀ f) (add_zero 1) = 0 at hf
      obtain ⟨y,hy⟩ := Ext.contravariant_sequence_exact₁ hS M (Ext.mk₀ f) rfl hf
      refine ⟨Ext.linearEquiv₀ (R := K) y, ?_⟩
      apply (Ext.linearEquiv₀ (R := K)).symm.injective
      change Ext.mk₀ (S.f ≫ Ext.linearEquiv₀ (R := K) y) = Ext.mk₀ f
      simpa only [← Ext.mk₀_comp_mk₀,
        Ext.mk₀_linearEquiv₀_apply] using hy
  exact (Submodule.quotEquivOfEq _ _ hk).trans (d.quotKerEquivOfSurjective hd)

end PiExponentSeshadri.ExtCokernel

namespace PiExponentSeshadri.Geometry
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace Abelian
open ModuleFlasque
variable {X : Scheme.{0}}
local instance : Linear Γ(X,⊤) (SheafOfModules X.ringCatSheaf) := sheafLinear X
local instance : HasExt.{1} (SheafOfModules X.ringCatSheaf) := schemeHasExt

abbrev pencilCechFreeOpen (U : X.Opens) : X.Modules :=
  freeOpen X.ringCatSheaf U

abbrev schemeShortComplex (U V : X.Opens) : ShortComplex X.Modules :=
  ModuleMayerVietoris.shortComplex X.ringCatSheaf U V

abbrev schemeFreeOpenEquiv (M : X.Modules) (U : X.Opens) :
    (pencilCechFreeOpen U ⟶ M) ≃ₗ[Γ(X,⊤)] OpenSections M U :=
  freeOpenLinearEquiv M U

def twoChartImage (M : X.Modules) (U V : X.Opens) :
    Submodule Γ(X,⊤) (OpenSections M (U ⊓ V)) :=
  (openRestriction M (show U ⊓ V ≤ U from inf_le_left)).range ⊔
  (openRestriction M (show U ⊓ V ≤ V from inf_le_right)).range

lemma twoChartImage_eq (M : X.Modules) (U V : X.Opens) :
    (LinearMap.range (Linear.leftComp (C := X.Modules) (X := pencilCechFreeOpen (U ⊓ V))
      (Y := pencilCechFreeOpen U ⊞ pencilCechFreeOpen V) Γ(X,⊤) M
      (schemeShortComplex U V).f)).map
      (schemeFreeOpenEquiv M (U ⊓ V)).toLinearMap = twoChartImage M U V := by
  simp only [schemeShortComplex, ModuleMayerVietoris.shortComplex]
  let P := twoChartImage M U V
  let l : pencilCechFreeOpen (U ⊓ V) ⟶ pencilCechFreeOpen U :=
    freeOpenMap X.ringCatSheaf (homOfLE (show U ⊓ V ≤ U from inf_le_left))
  let r : pencilCechFreeOpen (U ⊓ V) ⟶ pencilCechFreeOpen V :=
    freeOpenMap X.ringCatSheaf (homOfLE (show U ⊓ V ≤ V from inf_le_right))
  have hl (f : pencilCechFreeOpen U ⟶ M) :
      schemeFreeOpenEquiv M (U ⊓ V) (l ≫ f) =
        openRestriction M inf_le_left (schemeFreeOpenEquiv M U f) :=
    freeOpenLinearEquiv_naturality M inf_le_left f
  have hr (f : pencilCechFreeOpen V ⟶ M) :
      schemeFreeOpenEquiv M (U ⊓ V) (r ≫ f) =
        openRestriction M inf_le_right (schemeFreeOpenEquiv M V f) :=
    freeOpenLinearEquiv_naturality M inf_le_right f
  apply le_antisymm
  · rintro x ⟨f,⟨g,rfl⟩,rfl⟩
    have he : biprod.lift l (-r) ≫ g =
        l ≫ (biprod.inl ≫ g) - r ≫ (biprod.inr ≫ g) := by
      rw [biprod.lift_eq]
      simp only [Preadditive.add_comp, Category.assoc, Preadditive.neg_comp,
        sub_eq_add_neg]
    change schemeFreeOpenEquiv M (U ⊓ V)
      (biprod.lift l (-r) ≫ g) ∈ P
    rw [he, map_sub, hl, hr]
    exact P.sub_mem
      ((show (openRestriction M inf_le_left).range ≤ P from le_sup_left)
        ((openRestriction M inf_le_left).mem_range_self _))
      ((show (openRestriction M inf_le_right).range ≤ P from le_sup_right)
        ((openRestriction M inf_le_right).mem_range_self _))
  · apply sup_le
    · rintro x ⟨a,rfl⟩
      refine ⟨_, ⟨biprod.desc ((schemeFreeOpenEquiv M U).symm a) 0,rfl⟩, ?_⟩
      change schemeFreeOpenEquiv M (U ⊓ V)
        (biprod.lift l (-r) ≫ biprod.desc ((schemeFreeOpenEquiv M U).symm a) 0) = _
      rw [biprod.lift_desc, comp_zero, add_zero, hl, LinearEquiv.apply_symm_apply]
    · rintro x ⟨b,rfl⟩
      refine ⟨_, ⟨biprod.desc 0 (-((schemeFreeOpenEquiv M V).symm b)),rfl⟩, ?_⟩
      change schemeFreeOpenEquiv M (U ⊓ V)
        (biprod.lift l (-r) ≫ biprod.desc 0 (-((schemeFreeOpenEquiv M V).symm b))) = _
      rw [biprod.lift_desc, comp_zero, zero_add, Preadditive.neg_comp,
        Preadditive.comp_neg, neg_neg, hr, LinearEquiv.apply_symm_apply]

def twoAffineUnionExtOne [IsNoetherian X] (M : X.Modules) [M.IsQuasicoherent]
    (U V : X.Opens) (hU : IsAffineOpen U) (hV : IsAffineOpen V) :
    ((OpenSections M (U ⊓ V)) ⧸ twoChartImage M U V) ≃ₗ[Γ(X,⊤)]
      Ext.{1} (C := X.Modules) (pencilCechFreeOpen (U ⊔ V)) M 1 := by
  have hmid (y : Ext.{1} (C := X.Modules) (pencilCechFreeOpen U ⊞ pencilCechFreeOpen V) M 1) :
      y = 0 := by
    apply Ext.biprodAddEquiv.injective
    apply Prod.ext
    · simpa only [map_zero, Ext.biprodAddEquiv_apply_fst, Prod.fst_zero] using
        FiniteCoverCohomology.affine_open_ext_zero U hU M 0
          ((Ext.mk₀ biprod.inl).comp y (zero_add _))
    · simpa only [map_zero, Ext.biprodAddEquiv_apply_snd, Prod.snd_zero] using
        FiniteCoverCohomology.affine_open_ext_zero V hV M 0
          ((Ext.mk₀ biprod.inr).comp y (zero_add _))
  let e := Submodule.Quotient.equiv _ _ (schemeFreeOpenEquiv M (U ⊓ V))
    (twoChartImage_eq M U V)
  exact e.symm.trans (ExtCokernel.quotientEquiv
    (ModuleMayerVietoris.shortComplex_shortExact X.ringCatSheaf U V) M hmid)

def extSourceIso {E F : X.Modules} (e : E ≅ F) (M : X.Modules) (n : ℕ) :
    Ext.{1} (C := X.Modules) E M n ≃ₗ[Γ(X,⊤)] Ext.{1} (C := X.Modules) F M n where
  toFun := (Ext.mk₀ e.inv).precompOfLinear Γ(X,⊤) M (zero_add n)
  invFun := (Ext.mk₀ e.hom).precompOfLinear Γ(X,⊤) M (zero_add n)
  map_add' := map_add _
  map_smul' := map_smul _
  left_inv x := by
    change (Ext.mk₀ e.hom).comp ((Ext.mk₀ e.inv).comp x (zero_add n)) (zero_add n) = x
    rw [Ext.mk₀_comp_mk₀_assoc, e.hom_inv_id, Ext.mk₀_id_comp]
  right_inv x := by
    change (Ext.mk₀ e.inv).comp ((Ext.mk₀ e.hom).comp x (zero_add n)) (zero_add n) = x
    rw [Ext.mk₀_comp_mk₀_assoc, e.inv_hom_id, Ext.mk₀_id_comp]

def twoAffineCohomologyOne [IsNoetherian X] (M : X.Modules) [M.IsQuasicoherent]
    (U V : X.Opens) (hU : IsAffineOpen U) (hV : IsAffineOpen V) (hcover : U ⊔ V = ⊤) :
    ((OpenSections M (U ⊓ V)) ⧸ twoChartImage M U V) ≃ₗ[Γ(X,⊤)] cohomology M 1 := by
  let e := twoAffineUnionExtOne M U V hU hV
  rw [hcover] at e
  exact e.trans (extSourceIso (FreeOpenUnit.freeTopIso X.ringCatSheaf) M 1)

end PiExponentSeshadri.Geometry

namespace PiExponentSeshadri.Geometry.BaseSections

section
open AlgebraicGeometry CategoryTheory TopologicalSpace
open scoped Polynomial
variable {K : Type} [Field K] {U V W : Scheme.{0}} [IsAffine U] [IsAffine V]

theorem two_chart_cokernel_finite
    (kU : K →+* Γ(U,⊤)) (kV : K →+* Γ(V,⊤)) (kW : K →+* Γ(W,⊤))
    (a : W ⟶ U) (b : W ⟶ V) [IsOpenImmersion a] [IsOpenImmersion b]
    (hka : a.appTop.hom.comp kU = kW) (hkb : b.appTop.hom.comp kV = kW)
    (u : Γ(U,⊤)) (v : Γ(V,⊤))
    (ha : a.opensRange = U.basicOpen u) (hb : b.opensRange = V.basicOpen v)
    (huv : a.appTop u * b.appTop v = 1)
    (hu : (Polynomial.eval₂RingHom kU u).Finite)
    (L : LineBundle U) (P : LineBundle V) (N : W.Modules)
    (e : L.sheaf.restrict a ≅ N) (d : P.sheaf.restrict b ≅ N) :
    Module.Finite K (Sections kW N ⊤ ⧸
      ((chartMap kU kW a hka L.sheaf e).range ⊔
        (chartMap kV kW b hkb P.sheaf d).range)) := by
  let := polynomialModule kU u L.sheaf ⊤
  let := polynomialModule kV v P.sheaf ⊤
  let := polynomialModule kW (a.appTop u) N ⊤
  let := polynomialTower kU u L.sheaf ⊤
  let := polynomialTower kV v P.sheaf ⊤
  let := polynomialTower kW (a.appTop u) N ⊤
  let : Module.Finite K[X] (Sections kU L.sheaf ⊤) := polynomial_finite kU u L hu
  let F := chartPolynomialMap kU kW a hka L.sheaf e u
  let G := chartMap kV kW b hkb P.sheaf d
  let : IsLocalizedModule.Away (Polynomial.X : K[X]) F :=
    chartPolynomialMap_localize kU kW a hka L.sheaf e u ha
  have hInv (y : Sections kV P.sheaf ⊤) :
      (Polynomial.X : K[X]) • G ((Polynomial.X : K[X]) • y) = G y := by
    change (Polynomial.eval₂RingHom kW (a.appTop u)) Polynomial.X •
      G ((Polynomial.eval₂RingHom kV v) Polynomial.X • y) = G y
    simp only [Polynomial.coe_eval₂RingHom, Polynomial.eval₂_X]
    rw [chartMap_smul, ← mul_smul, huv, one_smul]
  have hDen (x : Sections kW N ⊤) : ∃ n : ℕ, ∃ y : Sections kV P.sheaf ⊤,
      (Polynomial.X : K[X])^n • G y = x := by
    let : Module Γ(V,⊤) (OpenSections N ⊤) :=
      Module.compHom (OpenSections N ⊤) b.appTop.hom
    let G' := chartModuleMap P.sheaf b d
    let : IsLocalizedModule.Away v G' := chartModuleMap_localize P.sheaf b d v hb
    obtain ⟨n,y,hy⟩ := (inferInstance : IsLocalizedModule.Away v G').surj _ _ x
    refine ⟨n,y,?_⟩
    change (Polynomial.eval₂RingHom kW (a.appTop u)) (Polynomial.X^n) • G y = x
    simp only [map_pow, Polynomial.coe_eval₂RingHom, Polynomial.eval₂_X]
    change b.appTop (v^n) • (x : OpenSections N ⊤) = G' y at hy
    change (a.appTop u)^n • (G' y : OpenSections N ⊤) = x
    erw [← hy, map_pow, ← mul_smul, ← mul_pow, huv, one_pow, one_smul]
  exact LaurentCech.cokernel_finite F G hInv hDen
end

section
open AlgebraicGeometry CategoryTheory TopologicalSpace
variable {K : Type} [Field K] {X : Scheme.{0}}

def twoBaseImage (k : K →+* Γ(X,⊤)) (M : X.Modules) (U V : X.Opens) :
    Submodule K (Sections k M (U ⊓ V)) :=
  (res k M (show U ⊓ V ≤ U from inf_le_left)).range ⊔
    (res k M (show U ⊓ V ≤ V from inf_le_right)).range

end

open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite
variable {K : Type} [Field K] {X : Scheme.{0}}

def twoBaseCohomologyOne [IsNoetherian X] (k : K →+* Γ(X,⊤))
    (M : X.Modules) [M.IsQuasicoherent] (U V : X.Opens)
    (hU : IsAffineOpen U) (hV : IsAffineOpen V) (hc : U ⊔ V = ⊤) :
    letI := Module.compHom (cohomology M 1) k
    (Sections k M (U ⊓ V) ⧸ twoBaseImage k M U V) ≃ₗ[K] cohomology M 1 := by
  letI : Algebra K Γ(X,⊤) := k.toAlgebra
  letI := Module.compHom (cohomology M 1) k
  letI : IsScalarTower K Γ(X,⊤) (cohomology M 1) :=
    .of_algebraMap_smul (fun _ _ => rfl)
  letI : Module K (OpenSections M (U ⊓ V)) := Module.compHom _ k
  letI : IsScalarTower K Γ(X,⊤) (OpenSections M (U ⊓ V)) :=
    .of_algebraMap_smul (fun _ _ => rfl)
  have he : twoBaseImage k M U V = (twoChartImage M U V).restrictScalars K := by
    apply Submodule.ext
    intro x
    change x ∈ twoBaseImage k M U V ↔
      (x : OpenSections M (U ⊓ V)) ∈ twoChartImage M U V
    simp only [twoBaseImage, twoChartImage]
    constructor
    · intro hx
      obtain ⟨y, hy, z, hz, h⟩ :=
        (Submodule.mem_sup (R := K) (M := Sections k M (U ⊓ V))).mp hx
      exact (Submodule.mem_sup (R := Γ(X,⊤)) (M := OpenSections M (U ⊓ V))).mpr
        ⟨y, hy, z, hz, h⟩
    · intro hx
      obtain ⟨y, hy, z, hz, h⟩ :=
        (Submodule.mem_sup (R := Γ(X,⊤)) (M := OpenSections M (U ⊓ V))).mp hx
      exact (Submodule.mem_sup (R := K) (M := Sections k M (U ⊓ V))).mpr
        ⟨y, hy, z, hz, h⟩
  let E := Submodule.Quotient.restrictScalarsEquiv K (twoChartImage M U V)
  let F := (twoAffineCohomologyOne M U V hU hV hc).restrictScalars K
  rw [he]
  exact E.trans F
end PiExponentSeshadri.Geometry.BaseSections

end

end OAI
end Source0476

-- Source: OAI/NumberTheory/PiExponent/Cohomology/PencilCohomologyFiniteCharts.lean
section Source0477
/-
Modification notice for the LogTwo project.
Derived from openai/math (Apache-2.0), revision adc7f1241b42e322a6451854ab7e4b4c146bf78a.
Original source: lean/OAI/NumberTheory/PiExponent/Cohomology/PencilCohomologyFiniteCharts.lean
Changes: Convert module/import declarations to the Lean 4.34 public module format.
See ../THIRD_PARTY_NOTICES.txt for provenance and the recorded changes.
-/

namespace OAI

noncomputable section

namespace PiExponentSeshadri.Projective

section
open AlgebraicGeometry CategoryTheory TopologicalSpace MvPolynomial HomogeneousLocalization
attribute [local instance] MvPolynomial.gradedAlgebra
variable {K σ : Type} [CommRing K]

theorem pencil_polynomial_irrelevant_le :
    (HomogeneousIdeal.irrelevant (homogeneousSubmodule σ K)).toIdeal ≤
      Ideal.span (Set.range (MvPolynomial.X (R := K) : σ → MvPolynomial σ K)) := by
  rw [HomogeneousIdeal.toIdeal_irrelevant_le]
  intro n hn p hp
  change p ∈ idealOfVars σ K
  rw [← pow_one (idealOfVars σ K), mem_pow_idealOfVars_iff]
  intro d hd
  change 1 ≤ d.sum fun _ v => v
  rw [Finsupp.sum, ← hp.degree_eq_sum_deg_support hd]
  exact hn

def projectiveCoordinateCover : (Proj (homogeneousSubmodule σ K)).AffineOpenCover :=
  Proj.affineOpenCoverOfIrrelevantLESpan _ (X (R := K))
    (m := fun _ => 1) (fun i => isHomogeneous_X K i) (fun _ => by decide)
    pencil_polynomial_irrelevant_le

open PiExponentSeshadri.Frames

lemma affine_evaluation_finite {R : Type} [CommRing R] {Y : Scheme}
    (f : R →+* Γ(Y,⊤)) [IsFinite (Y.toSpecΓ ≫ Spec.map (CommRingCat.ofHom f))] :
    f.Finite := by
  let g := Y.toSpecΓ ≫ Spec.map (CommRingCat.ofHom f)
  have hEq : (Scheme.ΓSpecIso (CommRingCat.of R)).inv ≫ g.appTop = CommRingCat.ofHom f := by
    simp only [g, Scheme.Hom.comp_appTop, Scheme.toSpecΓ_appTop,
      ← Scheme.ΓSpecIso_inv_naturality_assoc, Iso.inv_hom_id, Category.comp_id]
  have h := g.finite_appTop.comp (RingHom.Finite.of_surjective
    (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom
    (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (CommRingCat.of R)).inv).surjective)
  change ((Scheme.ΓSpecIso (CommRingCat.of R)).inv ≫ g.appTop).hom.Finite at h
  simpa only [hEq, CommRingCat.hom_ofHom] using h

lemma normalized_evalAway_polyToChart {R : Type} [CommRing R]
    (k : K →+* R) (a : σ → R) (i : σ) (hi : a i = 1) :
    (evalAway (𝒜 := homogeneousSubmodule σ K) (eval₂Hom k a) (MvPolynomial.X i)
      (by simpa only [eval₂Hom_X',hi] using (isUnit_one : IsUnit (1 : R)))).comp
      (polyToChart i) = eval₂Hom k (fun j : ChartVariables i => a j) := by
  let F := evalAway (𝒜 := homogeneousSubmodule σ K) (eval₂Hom k a) (MvPolynomial.X i)
    (by simpa only [eval₂Hom_X',hi] using (isUnit_one : IsUnit (1 : R)))
  apply MvPolynomial.ringHom_ext
  · intro r
    simp only [RingHom.comp_apply, polyToChart, eval₂Hom_C]
    change F (chartConstants i r) = k r
    exact evalAway_constants i k a hi r
  · intro j
    simp only [RingHom.comp_apply, polyToChart, eval₂Hom_X']
    change F (chartCoordinate i j.val) = a j.val
    have H := evalAway_mk_clear (𝒜 := homogeneousSubmodule σ K) (eval₂Hom k a) (isHomogeneous_X K i)
      (show IsUnit ((eval₂Hom k a) (MvPolynomial.X i)) by simpa only [eval₂Hom_X',hi] using
        (isUnit_one : IsUnit (1 : R))) 1 (X j.val) (by simpa using isHomogeneous_X K j.val)
    simpa only [chartCoordinate, eval₂Hom_X',hi,one_pow,mul_one] using H

theorem finite_sectionsMorphism_chart {X : Scheme} {M : X.Modules}
    (k : K →+* Γ(X,⊤)) (s : σ → (O X ⟶ M))
    (hs : (⨆ i, SectionOpens.isoOpen (s i)) = ⊤)
    [IsFinite (sectionsMorphism k s hs)] (i : σ) :
    IsAffine (SectionOpens.isoOpen (s i)).toScheme ∧
    (eval₂Hom ((SectionOpens.isoOpen (s i)).ι.appTop.hom.comp k)
      (fun j : ChartVariables i => coefficient (sectionFrame (s i))
        (restrictSection (SectionOpens.isoOpen (s i)).ι (s j)))).Finite := by
  let V := projectiveCoordinateCover (K := K) (σ := σ)
  let U := SectionOpens.isoOpen (s i)
  let k' := U.ι.appTop.hom.comp k
  let a : σ → Γ(U.toScheme,⊤) := fun j => coefficient (sectionFrame (s i))
    (restrictSection U.ι (s j))
  have hi : a i = 1 := sectionFrame_normalized (s i)
  let f := evalAway (𝒜 := homogeneousSubmodule σ K) (eval₂Hom k' a) (MvPolynomial.X i)
    (by simpa only [eval₂Hom_X',hi] using (isUnit_one : IsUnit (1 : Γ(U.toScheme,⊤))))
  let g : U.toScheme ⟶ Spec (CommRingCat.of (Away (homogeneousSubmodule σ K) (MvPolynomial.X i))) :=
    U.toScheme.toSpecΓ ≫ Spec.map (CommRingCat.ofHom f)
  have hV : IsOpenImmersion (V.f i) := by
    exact inferInstanceAs (IsOpenImmersion
      (Proj.awayι (PolyGrade K σ) (MvPolynomial.X i) (poly_X_mem i) (by decide)))
  have H : IsPullback g U.ι (V.f i) (sectionsMorphism k s hs) := by
    apply @IsOpenImmersion.isPullback _ _ _ _ g U.ι (V.f i)
      (sectionsMorphism k s hs) (inferInstanceAs (IsOpenImmersion U.ι)) hV
    · exact (sectionsMorphism_local k s hs i).trans (Category.assoc _ _ _).symm
    · change _ ⁻¹ᵁ (Proj.awayι (homogeneousSubmodule σ K) (MvPolynomial.X i) _ _).opensRange = _
      erw [Proj.opensRange_awayι, sectionsMorphism_preimage, Scheme.Opens.opensRange_ι]
  have hg : IsFinite g := by
    exact MorphismProperty.of_isPullback H.flip (inferInstance : IsFinite (sectionsMorphism k s hs))
  refine ⟨isAffine_of_isAffineHom g, ?_⟩
  have hf := (@affine_evaluation_finite _ _ U.toScheme f hg).comp (RingHom.Finite.of_surjective
    (polyToChart (R := K) i) (polynomialChartEquiv (R := K) i).symm.surjective)
  rwa [normalized_evalAway_polyToChart k' a i hi] at hf

instance boolChartUnique (i : Bool) : Unique (ChartVariables i) where
  default := ⟨!i, by cases i <;> decide⟩
  uniq j := by rcases j with ⟨j,hj⟩; cases i <;> cases j <;> simp_all

theorem finite_pencil_chart {X : Scheme} {M : X.Modules}
    (k : K →+* Γ(X,⊤)) (s : Bool → (O X ⟶ M))
    (hs : (⨆ i, SectionOpens.isoOpen (s i)) = ⊤)
    [IsFinite (sectionsMorphism k s hs)] (i : Bool) :
    IsAffine (SectionOpens.isoOpen (s i)).toScheme ∧
    (Polynomial.eval₂RingHom ((SectionOpens.isoOpen (s i)).ι.appTop.hom.comp k)
      (coefficient (sectionFrame (s i))
        (restrictSection (SectionOpens.isoOpen (s i)).ι (s (!i))))).Finite := by
  obtain ⟨hA,hf⟩ := finite_sectionsMorphism_chart k s hs i
  refine ⟨hA, ?_⟩
  have h := hf.comp (RingHom.Finite.of_surjective
    (MvPolynomial.uniqueAlgEquiv K (ChartVariables i)).symm.toRingHom
    (MvPolynomial.uniqueAlgEquiv K (ChartVariables i)).symm.surjective)
  have he : (eval₂Hom ((SectionOpens.isoOpen (s i)).ι.appTop.hom.comp k)
      (fun j : ChartVariables i => coefficient (sectionFrame (s i))
        (restrictSection (SectionOpens.isoOpen (s i)).ι (s j)))).comp
      (MvPolynomial.uniqueAlgEquiv K (ChartVariables i)).symm.toRingHom =
      Polynomial.eval₂RingHom ((SectionOpens.isoOpen (s i)).ι.appTop.hom.comp k)
      (coefficient (sectionFrame (s i))
        (restrictSection (SectionOpens.isoOpen (s i)).ι (s (!i)))) := by
    apply Polynomial.ringHom_ext
    · intro r
      simp [MvPolynomial.uniqueAlgEquiv]
    · have hd : (default : ChartVariables i).val = !i :=
        congrArg Subtype.val (Subsingleton.elim (default : ChartVariables i)
          ⟨!i, by cases i <;> decide⟩)
      simpa [MvPolynomial.uniqueAlgEquiv] using congrArg
        (fun j => coefficient (sectionFrame (s i))
          (restrictSection (SectionOpens.isoOpen (s i)).ι (s j))) hd
  rwa [he] at h
end

open AlgebraicGeometry CategoryTheory TopologicalSpace
open PiExponentSeshadri.Frames
variable {X : Scheme.{0}} {M : X.Modules}

lemma pencil_overlap_basic (s : Bool → (O X ⟶ M)) (i : Bool) :
    (SectionOpens.isoOpen (s i)).ι ⁻¹ᵁ SectionOpens.isoOpen (s (!i)) =
      (SectionOpens.isoOpen (s i)).toScheme.basicOpen
        (coefficient (sectionFrame (s i))
          (restrictSection (SectionOpens.isoOpen (s i)).ι (s (!i)))) :=
  preimage_isoOpen _ _ _

lemma pencil_overlap_reciprocal (s : Bool → (O X ⟶ M)) :
    let U := SectionOpens.isoOpen (s false)
    let V := SectionOpens.isoOpen (s true)
    let a := X.homOfLE (show U ⊓ V ≤ U from inf_le_left)
    let b := X.homOfLE (show U ⊓ V ≤ V from inf_le_right)
    a.appTop (coefficient (sectionFrame (s false)) (restrictSection U.ι (s true))) *
      b.appTop (coefficient (sectionFrame (s true)) (restrictSection V.ι (s false))) = 1 := by
  intro U V a b
  obtain ⟨c,hc⟩ := overlap_coefficients U.ι V.ι a b
    (by simp only [a,b, Scheme.homOfLE_ι])
    (sectionFrame (s false)) (sectionFrame (s true))
  have h0 := hc (s false)
  have h1 := hc (s true)
  have hv : b.appTop (coefficient (sectionFrame (s true))
      (restrictSection V.ι (s false))) = c := by
    simpa only [U, sectionFrame_normalized, map_one, mul_one] using h0
  rw [hv, mul_comm]
  simpa only [V, sectionFrame_normalized, map_one] using h1.symm

end PiExponentSeshadri.Projective

end

end OAI
end Source0477

-- Source: OAI/NumberTheory/PiExponent/Cohomology/PencilCohomologyPencil.lean
section Source0478
/-
Modification notice for the LogTwo project.
Derived from openai/math (Apache-2.0), revision adc7f1241b42e322a6451854ab7e4b4c146bf78a.
Original source: lean/OAI/NumberTheory/PiExponent/Cohomology/PencilCohomologyPencil.lean
Changes: Convert module/import declarations to the Lean 4.34 public module format.
See ../THIRD_PARTY_NOTICES.txt for provenance and the recorded changes.
-/

namespace OAI

namespace PiExponentSeshadri.Geometry.BaseSections
noncomputable section
open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite
variable {K : Type} [CommRing K] {X : Scheme.{0}}

lemma congr_apply (k : K →+* Γ(X,⊤)) (M : X.Modules) {U V : X.Opens}
    (h : U = V) (m : Sections k M U) :
    congr k M h m = M.presheaf.map (eqToHom h.symm).op m := by
  subst V
  change m = M.presheaf.map (𝟙 (op U)) m
  exact congrArg (fun f : M.presheaf.obj (op U) ⟶ M.presheaf.obj (op U) => f m)
    (M.presheaf.map_id (op U)).symm

def nestedRestriction (M : X.Modules) {U W : X.Opens} (h : W ≤ U) :
    (M.restrict U.ι).restrict (X.homOfLE h) ≅ M.restrict W.ι :=
  ((Scheme.Modules.restrictFunctorComp (X.homOfLE h) U.ι).app M).symm ≪≫
    (Scheme.Modules.restrictFunctorCongr (X.homOfLE_ι h)).app M

lemma nestedBase (k : K →+* Γ(X,⊤)) {U W : X.Opens} (h : W ≤ U) :
    (X.homOfLE h).appTop.hom.comp (U.ι.appTop.hom.comp k) = W.ι.appTop.hom.comp k := by
  rw [← RingHom.comp_assoc, ← CommRingCat.hom_comp, ← Scheme.Hom.comp_appTop,
    Scheme.homOfLE_ι]

lemma chartTop_nested (k : K →+* Γ(X,⊤)) (M : X.Modules)
    {U W : X.Opens} (h : W ≤ U)
    (m : Sections (U.ι.appTop.hom.comp k) (M.restrict U.ι) ⊤) :
    chartTop k M W (chartMap (U.ι.appTop.hom.comp k) (W.ι.appTop.hom.comp k)
      (X.homOfLE h) (nestedBase k h) (M.restrict U.ι) (nestedRestriction M h) m) =
        res k M h (chartTop k M U m) := by
  simp only [chartTop, LinearEquiv.trans_apply, restrictEquiv, congr_apply,
    chartMap, chartModuleMap, LinearMap.coe_comp,
    chartModuleEquiv, moduleIsoSections, openImmersionTop, restrictedOpenSections,
    nestedRestriction, Iso.trans_hom, Iso.symm_hom, Iso.app_hom]
  change M.presheaf.map _ (M.presheaf.map _ (M.presheaf.map _ (M.presheaf.map _ m))) =
    M.presheaf.map _ (M.presheaf.map _ m)
  have map_comp_apply {A B C : X.Opensᵒᵖ} (f : A ⟶ B) (g : B ⟶ C)
      (x : M.presheaf.obj A) :
      M.presheaf.map g (M.presheaf.map f x) = M.presheaf.map (f ≫ g) x := by
    exact (congrArg (fun h : M.presheaf.obj A ⟶ M.presheaf.obj C => h x)
      (M.presheaf.map_comp f g)).symm
  simp only [map_comp_apply]
  refine (map_comp_apply _ _ _).trans ?_
  symm
  exact map_comp_apply _ _ _

lemma chartMap_range_coherent (k : K →+* Γ(X,⊤)) (M : X.Modules)
    {U W : X.Opens} (h : W ≤ U) :
    (chartMap (U.ι.appTop.hom.comp k) (W.ι.appTop.hom.comp k) (X.homOfLE h)
      (nestedBase k h) (M.restrict U.ι) (nestedRestriction M h)).range.map
        (chartTop k M W).toLinearMap = (res k M h).range := by
  ext x
  constructor
  · rintro ⟨y,⟨z,rfl⟩,rfl⟩
    exact ⟨chartTop k M U z, (chartTop_nested k M h z).symm⟩
  · rintro ⟨z,rfl⟩
    refine ⟨_, ⟨(chartTop k M U).symm z,rfl⟩, ?_⟩
    exact (chartTop_nested k M h _).trans
      (congrArg (res k M h) ((chartTop k M U).apply_symm_apply z))

end
end PiExponentSeshadri.Geometry.BaseSections

end OAI
end Source0478

-- Source: OAI/NumberTheory/PiExponent/Cohomology/PencilCohomology.lean
section Source0479
/-
Modification notice for the LogTwo project.
Derived from openai/math (Apache-2.0), revision adc7f1241b42e322a6451854ab7e4b4c146bf78a.
Original source: lean/OAI/NumberTheory/PiExponent/Cohomology/PencilCohomology.lean
Changes: Convert module/import declarations to the Lean 4.34 public module format.
See ../THIRD_PARTY_NOTICES.txt for provenance and the recorded changes.
-/

namespace OAI

noncomputable section

namespace PiExponentSeshadri.Geometry.BaseSections

section
open AlgebraicGeometry CategoryTheory TopologicalSpace
open scoped Polynomial
variable {K : Type} [Field K] {U V W : Scheme.{0}} [IsAffine U] [IsAffine V]

theorem two_chart_intersection_finite
    (kU : K →+* Γ(U,⊤)) (kV : K →+* Γ(V,⊤)) (kW : K →+* Γ(W,⊤))
    (a : W ⟶ U) (b : W ⟶ V) [IsOpenImmersion a] [IsOpenImmersion b]
    (hka : a.appTop.hom.comp kU = kW) (hkb : b.appTop.hom.comp kV = kW)
    (u : Γ(U,⊤)) (v : Γ(V,⊤))
    (ha : a.opensRange = U.basicOpen u) (_hb : b.opensRange = V.basicOpen v)
    (huv : a.appTop u * b.appTop v = 1)
    (hu : (Polynomial.eval₂RingHom kU u).Finite)
    (hv : (Polynomial.eval₂RingHom kV v).Finite)
    (L : LineBundle U) (P : LineBundle V) (N : W.Modules)
    (e : L.sheaf.restrict a ≅ N) (d : P.sheaf.restrict b ≅ N) :
    Module.Finite K ↥((chartMap kU kW a hka L.sheaf e).range ⊓
        (chartMap kV kW b hkb P.sheaf d).range) := by
  let := polynomialModule kU u L.sheaf ⊤
  let := polynomialModule kV v P.sheaf ⊤
  let := polynomialModule kW (a.appTop u) N ⊤
  let := polynomialTower kU u L.sheaf ⊤
  let := polynomialTower kV v P.sheaf ⊤
  let := polynomialTower kW (a.appTop u) N ⊤
  let : Module.Finite K[X] (Sections kU L.sheaf ⊤) := polynomial_finite kU u L hu
  let : Module.Finite K[X] (Sections kV P.sheaf ⊤) := polynomial_finite kV v P hv
  let F := chartPolynomialMap kU kW a hka L.sheaf e u
  let G := chartMap kV kW b hkb P.sheaf d
  let : IsLocalizedModule.Away (Polynomial.X : K[X]) F :=
    chartPolynomialMap_localize kU kW a hka L.sheaf e u ha
  have hInv (y : Sections kV P.sheaf ⊤) :
      (Polynomial.X : K[X]) • G ((Polynomial.X : K[X]) • y) = G y := by
    change (Polynomial.eval₂RingHom kW (a.appTop u)) Polynomial.X •
      G ((Polynomial.eval₂RingHom kV v) Polynomial.X • y) = G y
    simp only [Polynomial.coe_eval₂RingHom, Polynomial.eval₂_X]
    rw [chartMap_smul, ← mul_smul, huv, one_smul]
  exact LaurentCech.intersection_finite F G hInv
end

open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite
open PiExponentSeshadri.Projective PiExponentSeshadri.Frames
variable {K : Type} [Field K] {X : Scheme.{0}}

def twoBaseIntersection (k : K →+* Γ(X,⊤)) (M : X.Modules) (U V : X.Opens) :
    Submodule K (Sections k M (U ⊓ V)) :=
  (res k M (show U ⊓ V ≤ U from inf_le_left)).range ⊓
    (res k M (show U ⊓ V ≤ V from inf_le_right)).range

theorem finite_pencil_intersection (k : K →+* Γ(X,⊤)) {M : X.Modules}
    (s : Bool → (O X ⟶ M)) (hs : (⨆ i, SectionOpens.isoOpen (s i)) = ⊤)
    [IsFinite (sectionsMorphism k s hs)] (L : LineBundle X) :
    let U := SectionOpens.isoOpen (s false)
    let V := SectionOpens.isoOpen (s true)
    Module.Finite K ↥(twoBaseIntersection k L.sheaf U V) := by
  intro U V
  let W := U ⊓ V
  let a := X.homOfLE (show W ≤ U from inf_le_left)
  let b := X.homOfLE (show W ≤ V from inf_le_right)
  let kU := U.ι.appTop.hom.comp k
  let kV := V.ι.appTop.hom.comp k
  let kW := W.ι.appTop.hom.comp k
  let u := coefficient (sectionFrame (s false)) (restrictSection U.ι (s true))
  let v := coefficient (sectionFrame (s true)) (restrictSection V.ι (s false))
  obtain ⟨hU,hu⟩ := finite_pencil_chart k s hs false
  obtain ⟨hV,hv⟩ := finite_pencil_chart k s hs true
  let : IsAffine U.toScheme := hU
  let : IsAffine V.toScheme := hV
  have ha : a.opensRange = U.toScheme.basicOpen u := by
    rw [Scheme.opensRange_homOfLE, Scheme.Hom.preimage_inf]
    simp only [Scheme.Opens.ι_preimage_self, top_inf_eq]
    exact pencil_overlap_basic s false
  have hb : b.opensRange = V.toScheme.basicOpen v := by
    rw [Scheme.opensRange_homOfLE, Scheme.Hom.preimage_inf]
    simp only [Scheme.Opens.ι_preimage_self, inf_top_eq]
    exact pencil_overlap_basic s true
  let e := nestedRestriction L.sheaf (show W ≤ U from inf_le_left)
  let d := nestedRestriction L.sheaf (show W ≤ V from inf_le_right)
  let F := chartMap kU kW a (nestedBase k inf_le_left) (L.restrict U.ι).sheaf e
  let G := chartMap kV kW b (nestedBase k inf_le_right) (L.restrict V.ι).sheaf d
  let : Module.Finite K ↥(F.range ⊓ G.range) :=
    two_chart_intersection_finite kU kV kW a b (nestedBase k inf_le_left)
      (nestedBase k inf_le_right) u v ha hb (pencil_overlap_reciprocal s) hu hv
      (L.restrict U.ι) (L.restrict V.ι) (L.sheaf.restrict W.ι) e d
  let E := chartTop k L.sheaf W
  have he : (F.range ⊓ G.range).map E.toLinearMap = twoBaseIntersection k L.sheaf U V := by
    rw [Submodule.map_inf E.toLinearMap E.injective]
    exact congrArg₂ (· ⊓ ·) (chartMap_range_coherent k L.sheaf inf_le_left)
      (chartMap_range_coherent k L.sheaf inf_le_right)
  let : Module.Finite K ↥((F.range ⊓ G.range).map E.toLinearMap) :=
    Module.Finite.equiv (E.submoduleMap (F.range ⊓ G.range))
  rw [← he]
  infer_instance
end PiExponentSeshadri.Geometry.BaseSections

namespace PiExponentSeshadri.Geometry
open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite Abelian
open PiExponentSeshadri.Projective PiExponentSeshadri.Frames BaseSections
variable {K : Type} [Field K] {X : Scheme.{0}}

lemma BaseSections.res_comp (k : K →+* Γ(X,⊤)) (M : X.Modules)
    {U V W : X.Opens} (h : U ≤ V) (g : V ≤ W) (m : Sections k M W) :
    res k M h (res k M g m) = res k M (h.trans g) m := by
  change M.presheaf.map (homOfLE h).op (M.presheaf.map (homOfLE g).op m) = _
  exact (congrArg (fun f : M.presheaf.obj (op W) ⟶ M.presheaf.obj (op U) => f m)
    (M.presheaf.map_comp (homOfLE g).op (homOfLE h).op)).symm

def BaseSections.globalIntersection [IsIntegral X] (k : K →+* Γ(X,⊤))
    (L : LineBundle X) (U V : X.Opens) :
    Sections k L.sheaf ⊤ →ₗ[K] ↥(twoBaseIntersection k L.sheaf U V) :=
  (res k L.sheaf (show U ⊓ V ≤ ⊤ from le_top)).codRestrict _ (by
    intro m
    exact ⟨⟨res k L.sheaf (show U ≤ ⊤ from le_top) m,
      res_comp k L.sheaf inf_le_left le_top m⟩,
      ⟨res k L.sheaf (show V ≤ ⊤ from le_top) m,
      res_comp k L.sheaf inf_le_right le_top m⟩⟩)

lemma BaseSections.globalIntersection_injective [IsIntegral X] (k : K →+* Γ(X,⊤))
    (L : LineBundle X) (U V : X.Opens) [Nonempty (U ⊓ V : X.Opens)] :
    Function.Injective (globalIntersection k L U V) := by
  intro a b h
  exact L.restriction_injective (homOfLE (show U ⊓ V ≤ ⊤ from le_top))
    (congrArg Subtype.val h)

def BaseSections.globalSectionsLinear (M : X.Modules) :
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

def BaseSections.cohomologyZero (k : K →+* Γ(X,⊤)) (M : X.Modules) :
    letI := Module.compHom (cohomology M 0) k
    cohomology M 0 ≃ₗ[K] Sections k M ⊤ := by
  letI := Module.compHom (cohomology M 0) k
  let e := (Ext.linearEquiv₀ (R := Γ(X,⊤)) (X := structureSheaf X) (Y := M)).trans
    (globalSectionsLinear M)
  refine { toFun := e
           invFun := e.symm
           left_inv := e.left_inv
           right_inv := e.right_inv
           map_add' := e.map_add
           map_smul' := ?_ }
  intro r m
  change e (k r • m) = restrictScalar X ⊤ (k r) • e m
  rw [e.map_smul]
  congr 1
  change k r = X.presheaf.map (𝟙 (op ⊤)) (k r)
  rw [X.presheaf.map_id]
  rfl

theorem finite_pencil_H0_finite [IsIntegral X]
    (k : K →+* Γ(X,⊤)) {M : X.Modules}
    (s : Bool → (O X ⟶ M)) (hs : (⨆ i, SectionOpens.isoOpen (s i)) = ⊤)
    [IsFinite (sectionsMorphism k s hs)] (hn : ¬ IsAffine X) (L : LineBundle X) :
    letI := Module.compHom (cohomology L.sheaf 0) k
    Module.Finite K (cohomology L.sheaf 0) := by
  let U := SectionOpens.isoOpen (s false)
  let V := SectionOpens.isoOpen (s true)
  obtain ⟨hU,_⟩ := finite_pencil_chart k s hs false
  obtain ⟨hV,_⟩ := finite_pencil_chart k s hs true
  have hc : U ⊔ V = ⊤ := by
    apply top_unique
    intro x hx
    have : x ∈ ⨆ i, SectionOpens.isoOpen (s i) := hs ▸ hx
    obtain ⟨i,hi⟩ := Opens.mem_iSup.mp this
    cases i with
    | false => exact Or.inl hi
    | true => exact Or.inr hi
  have hneU : (U : Set X).Nonempty := by
    by_contra h
    have he : U = ⊥ := by ext x; simp [Set.not_nonempty_iff_eq_empty.mp h]
    rw [he, bot_sup_eq] at hc
    have : IsAffine (⊤ : X.Opens).toScheme := hc ▸ hV
    exact hn (.of_isIso X.topIso.inv)
  have hneV : (V : Set X).Nonempty := by
    by_contra h
    have he : V = ⊥ := by ext x; simp [Set.not_nonempty_iff_eq_empty.mp h]
    rw [he, sup_bot_eq] at hc
    have : IsAffine (⊤ : X.Opens).toScheme := hc ▸ hU
    exact hn (.of_isIso X.topIso.inv)
  obtain ⟨x,hxU,hxV⟩ := nonempty_preirreducible_inter U.isOpen V.isOpen hneU hneV
  let : Nonempty (U ⊓ V : X.Opens) := ⟨⟨x,hxU,hxV⟩⟩
  let := finite_pencil_intersection k s hs L
  let : Module.Finite K (Sections k L.sheaf ⊤) := Module.Finite.of_injective
    (globalIntersection k L U V) (globalIntersection_injective k L U V)
  let := Module.compHom (cohomology L.sheaf 0) k
  exact Module.Finite.equiv (cohomologyZero k L.sheaf).symm

end PiExponentSeshadri.Geometry

namespace PiExponentSeshadri.Geometry.BaseSections
open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite
open PiExponentSeshadri.Projective PiExponentSeshadri.Frames
variable {K : Type} [Field K] {X : Scheme.{0}}

theorem finite_pencil_cokernel (k : K →+* Γ(X,⊤)) {M : X.Modules}
    (s : Bool → (O X ⟶ M)) (hs : (⨆ i, SectionOpens.isoOpen (s i)) = ⊤)
    [IsFinite (sectionsMorphism k s hs)] (L : LineBundle X) :
    let U := SectionOpens.isoOpen (s false)
    let V := SectionOpens.isoOpen (s true)
    Module.Finite K (Sections k L.sheaf (U ⊓ V) ⧸ twoBaseImage k L.sheaf U V) := by
  intro U V
  let W := U ⊓ V
  let a := X.homOfLE (show W ≤ U from inf_le_left)
  let b := X.homOfLE (show W ≤ V from inf_le_right)
  let kU := U.ι.appTop.hom.comp k
  let kV := V.ι.appTop.hom.comp k
  let kW := W.ι.appTop.hom.comp k
  let u := coefficient (sectionFrame (s false)) (restrictSection U.ι (s true))
  let v := coefficient (sectionFrame (s true)) (restrictSection V.ι (s false))
  obtain ⟨hU,hu⟩ := finite_pencil_chart k s hs false
  obtain ⟨hV,hv⟩ := finite_pencil_chart k s hs true
  let : IsAffine U.toScheme := hU
  let : IsAffine V.toScheme := hV
  have ha : a.opensRange = U.toScheme.basicOpen u := by
    rw [Scheme.opensRange_homOfLE, Scheme.Hom.preimage_inf]
    simp only [Scheme.Opens.ι_preimage_self, top_inf_eq]
    exact pencil_overlap_basic s false
  have hb : b.opensRange = V.toScheme.basicOpen v := by
    rw [Scheme.opensRange_homOfLE, Scheme.Hom.preimage_inf]
    simp only [Scheme.Opens.ι_preimage_self, inf_top_eq]
    exact pencil_overlap_basic s true
  let e := nestedRestriction L.sheaf (show W ≤ U from inf_le_left)
  let d := nestedRestriction L.sheaf (show W ≤ V from inf_le_right)
  let F := chartMap kU kW a (nestedBase k inf_le_left) (L.restrict U.ι).sheaf e
  let G := chartMap kV kW b (nestedBase k inf_le_right) (L.restrict V.ι).sheaf d
  let : Module.Finite K (Sections kW (L.sheaf.restrict W.ι) ⊤ ⧸ (F.range ⊔ G.range)) :=
    two_chart_cokernel_finite kU kV kW a b (nestedBase k inf_le_left)
      (nestedBase k inf_le_right) u v ha hb (pencil_overlap_reciprocal s) hu
      (L.restrict U.ι) (L.restrict V.ι) (L.sheaf.restrict W.ι) e d
  let E := chartTop k L.sheaf W
  have he : (F.range ⊔ G.range).map E.toLinearMap = twoBaseImage k L.sheaf U V := by
    rw [Submodule.map_sup]
    exact congrArg₂ (· ⊔ ·) (chartMap_range_coherent k L.sheaf inf_le_left)
      (chartMap_range_coherent k L.sheaf inf_le_right)
  let q := Submodule.Quotient.equiv (F.range ⊔ G.range)
    (twoBaseImage k L.sheaf U V) E he
  exact Module.Finite.of_surjective q.toLinearMap q.surjective
end PiExponentSeshadri.Geometry.BaseSections

namespace PiExponentSeshadri.Geometry
open AlgebraicGeometry CategoryTheory TopologicalSpace
open PiExponentSeshadri.Projective PiExponentSeshadri.Frames BaseSections
variable {K : Type} [Field K] {X : Scheme.{0}} [IsNoetherian X]

theorem finite_pencil_H1_finite (k : K →+* Γ(X,⊤)) {M : X.Modules}
    (s : Bool → (O X ⟶ M)) (hs : (⨆ i, SectionOpens.isoOpen (s i)) = ⊤)
    [IsFinite (sectionsMorphism k s hs)] (L : LineBundle X) :
    letI := Module.compHom (cohomology L.sheaf 1) k
    Module.Finite K (cohomology L.sheaf 1) := by
  let U := SectionOpens.isoOpen (s false)
  let V := SectionOpens.isoOpen (s true)
  obtain ⟨hU,_⟩ := finite_pencil_chart k s hs false
  obtain ⟨hV,_⟩ := finite_pencil_chart k s hs true
  have hc : U ⊔ V = ⊤ := by
    apply top_unique
    intro x hx
    have : x ∈ ⨆ i, SectionOpens.isoOpen (s i) := hs ▸ hx
    obtain ⟨i,hi⟩ := Opens.mem_iSup.mp this
    cases i with
    | false => exact Or.inl hi
    | true => exact Or.inr hi
  let := Module.compHom (cohomology L.sheaf 1) k
  let := finite_pencil_cokernel k s hs L
  let e := twoBaseCohomologyOne k L.sheaf U V hU hV hc
  exact Module.Finite.of_surjective e.toLinearMap e.surjective

end PiExponentSeshadri.Geometry

end

end OAI
end Source0479

-- Source: OAI/NumberTheory/PiExponent/Geometry/ProjectivePencilScalars.lean
section Source0480
/-
Modification notice for the LogTwo project.
Derived from openai/math (Apache-2.0), revision adc7f1241b42e322a6451854ab7e4b4c146bf78a.
Original source: lean/OAI/NumberTheory/PiExponent/Geometry/ProjectivePencilScalars.lean
Changes: Convert module/import declarations to the Lean 4.34 public module format.
See ../THIRD_PARTY_NOTICES.txt for provenance and the recorded changes.
-/

namespace OAI

namespace PiExponent.ProjectivePencilScalars
noncomputable section
open AlgebraicGeometry CategoryTheory

theorem projection_eq_structureMap (F : Type) [CommRing F] :
    polynomialProjectiveProjection F Bool = ProjectiveLine.structureMap F := by
  have hc : (polynomialGradeZeroEquiv F Bool).toRingHom =
      ProjectiveLine.constantsInDegreeZero F := by
    ext r
    rfl
  rw [polynomialProjectiveProjection, ProjectiveLine.structureMap, hc]

theorem scalars_comp_eq_structureScalars {F : Type} [CommRing F] {Y : Scheme.{0}}
    (f : Y ⟶ ProjectiveLine.projectiveLine F) :
    f.appTop.hom.comp (ProjectiveO1.scalars (R := F) (σ := Bool)) =
      (f ≫ ProjectiveLine.structureMap F).appTop.hom.comp
        (Scheme.ΓSpecIso (CommRingCat.of F)).inv.hom := by
  rw [ProjectiveO1.scalars, Scheme.Hom.comp_appTop, ← projection_eq_structureMap F]
  rfl

theorem scalars_comp_eq_baseScalars {Y : Scheme.{0}}
    (f : Y ⟶ ProjectiveLine.projectiveLine ℂ) :
    f.appTop.hom.comp (ProjectiveO1.scalars (R := ℂ) (σ := Bool)) =
      PiExponentSeshadri.Geometry.baseScalars (f ≫ ProjectiveLine.structureMap ℂ) :=
  scalars_comp_eq_structureScalars f

end
end PiExponent.ProjectivePencilScalars

end OAI
end Source0480

-- Source: OAI/NumberTheory/PiExponent/Geometry/ProjectiveFinitePencil.lean
section Source0481
/-
Modification notice for the LogTwo project.
Derived from openai/math (Apache-2.0), revision adc7f1241b42e322a6451854ab7e4b4c146bf78a.
Original source: lean/OAI/NumberTheory/PiExponent/Geometry/ProjectiveFinitePencil.lean
Changes: Convert module/import declarations to the Lean 4.34 public module format.
See ../THIRD_PARTY_NOTICES.txt for provenance and the recorded changes.
-/

namespace OAI

noncomputable section
namespace PiExponent.ProjectivePencil

section
open AlgebraicGeometry CategoryTheory TopologicalSpace
open PiExponentSeshadri.Frames PiExponentSeshadri.Geometry PiExponentSeshadri.Projective

variable {K σ : Type} [CommRing K] {X : Scheme.{0}}

def lineBundle (f : X ⟶ ProjectiveO1.projectiveSpace K σ) : LineBundle X :=
  (ProjectiveO1.lineBundle (R := K) (σ := σ)).pullback f

def coordinateSection (f : X ⟶ ProjectiveO1.projectiveSpace K σ) (i : σ) :
    O X ⟶ (lineBundle f).sheaf :=
  pullbackSection f (ProjectiveO1.coordinateSection (R := K) i)

def scalars (f : X ⟶ ProjectiveO1.projectiveSpace K σ) : K →+* Γ(X,⊤) :=
  f.appTop.hom.comp (ProjectiveO1.scalars (R := K) (σ := σ))

theorem sections_cover (f : X ⟶ ProjectiveO1.projectiveSpace K σ) :
    (⨆ i, PiExponentSeshadri.SectionOpens.isoOpen (coordinateSection f i)) = ⊤ :=
  pullback_sections_cover ProjectiveO1.coordinateSection ProjectiveO1.coordinateSection_cover f

theorem sectionsMorphism_eq (f : X ⟶ ProjectiveO1.projectiveSpace K σ) :
    sectionsMorphism (scalars f) (coordinateSection f) (sections_cover f) = f := by
  have h := sectionsMorphism_pullback
    (M := (ProjectiveO1.lineBundle (R := K) (σ := σ)).sheaf)
    (ProjectiveO1.scalars (R := K) (σ := σ))
    ProjectiveO1.coordinateSection ProjectiveO1.coordinateSection_cover f
  rw [ProjectiveO1.coordinate_sectionsMorphism_identity, Category.comp_id] at h
  exact h.symm

instance sectionsMorphism_isFinite (f : X ⟶ ProjectiveO1.projectiveSpace K σ)
    [IsFinite f] : IsFinite (sectionsMorphism (scalars f) (coordinateSection f) (sections_cover f)) := by
  rw [sectionsMorphism_eq]
  infer_instance

end

section
open AlgebraicGeometry CategoryTheory TopologicalSpace
open PiExponentSeshadri.Geometry
variable {K : Type} [Field K] {X : Scheme.{0}}

theorem H0_finite [IsIntegral X]
    (f : X ⟶ ProjectiveO1.projectiveSpace K Bool) [IsFinite f]
    (hn : ¬ IsAffine X) (L : LineBundle X) :
    letI := Module.compHom (cohomology L.sheaf 0) (scalars f)
    Module.Finite K (cohomology L.sheaf 0) :=
  finite_pencil_H0_finite (scalars f) (coordinateSection f) (sections_cover f) hn L

theorem H1_finite [IsNoetherian X]
    (f : X ⟶ ProjectiveO1.projectiveSpace K Bool) [IsFinite f] (L : LineBundle X) :
    letI := Module.compHom (cohomology L.sheaf 1) (scalars f)
    Module.Finite K (cohomology L.sheaf 1) :=
  finite_pencil_H1_finite (scalars f) (coordinateSection f) (sections_cover f) L

end
open AlgebraicGeometry CategoryTheory TopologicalSpace
open PiExponentSeshadri.Geometry
variable {X : Scheme.{0}}

theorem scalars_eq_baseScalars
    (f : X ⟶ ProjectiveLine.projectiveLine ℂ) :
    scalars f = baseScalars (f ≫ ProjectiveLine.structureMap ℂ) :=
  ProjectivePencilScalars.scalars_comp_eq_baseScalars f

theorem H0_finite_complex [IsIntegral X]
    (f : X ⟶ ProjectiveLine.projectiveLine ℂ) [IsFinite f]
    (hn : ¬ IsAffine X) (L : LineBundle X) :
    letI := Module.compHom (cohomology L.sheaf 0)
      (baseScalars (f ≫ ProjectiveLine.structureMap ℂ))
    Module.Finite ℂ (cohomology L.sheaf 0) := by
  rw [← scalars_eq_baseScalars f]
  exact H0_finite f hn L

theorem H1_finite_complex [IsNoetherian X]
    (f : X ⟶ ProjectiveLine.projectiveLine ℂ) [IsFinite f] (L : LineBundle X) :
    letI := Module.compHom (cohomology L.sheaf 1)
      (baseScalars (f ≫ ProjectiveLine.structureMap ℂ))
    Module.Finite ℂ (cohomology L.sheaf 1) := by
  rw [← scalars_eq_baseScalars f]
  exact H1_finite f L

end PiExponent.ProjectivePencil

end

end OAI
end Source0481

-- Source: OAI/NumberTheory/PiExponent/Ampleness/CurveNormalizationPolarization.lean
section Source0482
-- Modified in this edition: unused plain lemmas removed; see reduction.json.
/-
Modification notice for the LogTwo project.
Derived from openai/math (Apache-2.0), revision adc7f1241b42e322a6451854ab7e4b4c146bf78a.
Original source: lean/OAI/NumberTheory/PiExponent/Ampleness/CurveNormalizationPolarization.lean
Changes: Convert module/import declarations to the Lean 4.34 public module format.
See ../THIRD_PARTY_NOTICES.txt for provenance and the recorded changes.
-/

namespace OAI

noncomputable section
namespace PiExponent.CurveNormalizationModel
open AlgebraicGeometry CategoryTheory
open PiExponentSeshadri.Geometry
variable {E : Type} [Field E] [Algebra ℂ E]
variable (f : E) (hf : Transcendental ℂ f)
variable [FiniteDimensional (IntermediateField.adjoin ℂ {f}) E]

def parameterCurvePolarization : LineBundle (parameterCurve f hf) :=
  (ProjectiveO1.lineBundle (R := ℂ) (σ := Bool)).pullback (parameterCurveProjection f hf)

theorem parameterCurvePolarization_ample : (parameterCurvePolarization f hf).IsAmple := by
  let : CompactSpace (ProjectiveO1.projectiveSpace ℂ Bool) :=
    QuasiCompact.compactSpace_of_compactSpace (polynomialProjectiveProjection ℂ Bool)
  exact LineBundle.IsAmple.pullback_finite _ ProjectiveO1.lineBundle_ample
    (parameterCurveProjection f hf)

theorem parameterCurve_finiteLineCohomology :
    CurveDegree.FiniteLineCohomology (parameterCurveStructureMap f hf) := by
  intro L n hn
  have h0 := ProjectivePencil.H0_finite_complex (parameterCurveProjection f hf)
    (parameterCurve_not_isAffine f hf) L
  have h1 := ProjectivePencil.H1_finite_complex (parameterCurveProjection f hf) L
  rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hn with rfl | rfl
  · exact h0
  · exact h1

theorem parameterCurve_lineCohomologyTwoZero :
    CurveDegree.LineCohomologyTwoZero (parameterCurve f hf) := by
  intro L
  apply subsingleton_of_forall_eq 0
  intro x
  exact parameterCurve_lineBundle_ext_zero f hf L 2 (by omega) x

theorem parameterCurve_tensor_euler_add (L M : LineBundle (parameterCurve f hf)) :
    eulerCharacteristic (parameterCurveStructureMap f hf) 1 (L.tensor M).sheaf -
      eulerCharacteristic (parameterCurveStructureMap f hf) 1 M.sheaf =
    eulerCharacteristic (parameterCurveStructureMap f hf) 1 L.sheaf -
      eulerCharacteristic (parameterCurveStructureMap f hf) 1
        (structureSheaf (parameterCurve f hf)) :=
  CurveDegree.tensor_euler_add _ (parameterCurve_dimension_le_one f hf)
    (parameterCurvePolarization f hf) (parameterCurvePolarization_ample f hf)
    (parameterCurve_finiteLineCohomology f hf) (parameterCurve_lineCohomologyTwoZero f hf) L M

end PiExponent.CurveNormalizationModel

end

end OAI
end Source0482

-- Source: OAI/NumberTheory/PiExponent/Geometry/SectionZeroStalk.lean
section Source0483
/-
Modification notice for the LogTwo project.
Derived from openai/math (Apache-2.0), revision adc7f1241b42e322a6451854ab7e4b4c146bf78a.
Original source: lean/OAI/NumberTheory/PiExponent/Geometry/SectionZeroStalk.lean
Changes: Convert module/import declarations to the Lean 4.34 public module format.
See ../THIRD_PARTY_NOTICES.txt for provenance and the recorded changes.
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
      Ideal.span {((X.presheaf.germ U.1 _ hy)
        (U.1.topIso.hom (coefficient e (restrictSection U.1.ι s))))} := by
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
end Source0483

-- Source: OAI/NumberTheory/PiExponent/Geometry/CurveSectionDegree.lean
section Source0484
/-
Modification notice for the LogTwo project.
Derived from openai/math (Apache-2.0), revision adc7f1241b42e322a6451854ab7e4b4c146bf78a.
Original source: lean/OAI/NumberTheory/PiExponent/Geometry/CurveSectionDegree.lean
Changes: Convert module/import declarations to the Lean 4.34 public module format.
See ../THIRD_PARTY_NOTICES.txt for provenance and the recorded changes.
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
        I.ideal U = Ideal.span {(U.1.topIso.hom
          (endValue (e.inv ≫ (Scheme.Modules.restrictFunctor U.1.ι).map s ≫ d.hom)))} := by
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
end Source0484

-- Source: OAI/NumberTheory/PiExponent/Geometry/SectionOrderDivisor.lean
section Source0485
/-
Modification notice for the LogTwo project.
Derived from openai/math (Apache-2.0), revision adc7f1241b42e322a6451854ab7e4b4c146bf78a.
Original source: lean/OAI/NumberTheory/PiExponent/Geometry/SectionOrderDivisor.lean
Changes: Convert module/import declarations to the Lean 4.34 public module format.
See ../THIRD_PARTY_NOTICES.txt for provenance and the recorded changes.
-/

namespace OAI

noncomputable section
open CategoryTheory AlgebraicGeometry TopologicalSpace
open PiExponentSeshadri.Geometry PiExponentSeshadri.Frames
open PiExponent.CurveSectionDegree

namespace PiExponent.SectionOrderDivisor

variable {X : Scheme.{0}} [IsIntegral X]

abbrev CurvePoint (X : Scheme.{0}) [IsIntegral X] := {x : X // x ≠ genericPoint X}

omit [IsIntegral X] in
theorem mem_zero_support_iff_not_isUnit (L : LineBundle X) (s : GlobalSections X L.sheaf)
    (x : X) : x ∈ (SectionZeroIdeal.zeroIdeal L s).support ↔ ¬ IsUnit (coefficientGermAt L s x) := by
  let F := affineFrameAt L x
  rw [Scheme.IdealSheafData.mem_support_iff_of_mem (U := F.openSet) F.mem,
    SectionZeroIdeal.zeroIdeal_on_frame L s F.openSet F.frame,
    X.zeroLocus_span, X.zeroLocus_singleton]
  apply not_congr
  exact X.toRingedSpace.mem_basicOpen _ x F.mem

def orderAt (hDVR : ∀ x : X, x ≠ genericPoint X → IsDiscreteValuationRing (X.presheaf.stalk x))
    (L : LineBundle X) (s : GlobalSections X L.sheaf) (x : CurvePoint X) : ℕ :=
  letI := hDVR x.1 x.2
  (IsDiscreteValuationRing.addVal (X.presheaf.stalk x.1) (coefficientGermAt L s x.1)).toNat

theorem orderAt_eq_zero_of_not_mem
    (hDVR : ∀ x : X, x ≠ genericPoint X → IsDiscreteValuationRing (X.presheaf.stalk x))
    (L : LineBundle X) (s : GlobalSections X L.sheaf) (x : CurvePoint X)
    (hx : x.1 ∉ (SectionZeroIdeal.zeroIdeal L s).support) : orderAt hDVR L s x = 0 := by
  let := hDVR x.1 x.2
  have hu : IsUnit (coefficientGermAt L s x.1) :=
    not_not.mp ((mem_zero_support_iff_not_isUnit L s x.1).not.mp hx)
  unfold orderAt
  rw [IsDiscreteValuationRing.addVal_eq_zero_iff.mpr hu]
  rfl

def zeroPointEmbedding (L : LineBundle X) (s : GlobalSections X L.sheaf) (hs : s ≠ 0) :
    (SectionZeroIdeal.zeroIdeal L s).subscheme ↪ CurvePoint X where
  toFun y := ⟨(SectionZeroIdeal.zeroIdeal L s).subschemeι y, zeroPoint_ne_generic L s hs y⟩
  inj' _y _z h := (SectionZeroIdeal.zeroIdeal L s).subschemeι.isEmbedding.injective
    (congrArg (fun q : CurvePoint X => (q : X)) h)

theorem orderAt_finite_support
    (p : X ⟶ Spec (CommRingCat.of ℂ)) [IsProper p] (hd : topologicalKrullDim X ≤ 1)
    (hDVR : ∀ x : X, x ≠ genericPoint X → IsDiscreteValuationRing (X.presheaf.stalk x))
    (L : LineBundle X) (s : GlobalSections X L.sheaf) (hs : s ≠ 0) :
    (Function.support (orderAt hDVR L s)).Finite := by
  let : Finite (SectionZeroIdeal.zeroIdeal L s).subscheme :=
    finite_subscheme_of_curve p hd _ (SectionZeroIdeal.zeroIdeal_ne_bot L s hs)
  apply (Set.finite_range (zeroPointEmbedding L s hs)).subset
  intro x hx
  have hmem : x.1 ∈ (SectionZeroIdeal.zeroIdeal L s).support := by
    by_contra hn
    exact hx (orderAt_eq_zero_of_not_mem hDVR L s x hn)
  change x.1 ∈ ((SectionZeroIdeal.zeroIdeal L s).support : Set X) at hmem
  rw [← (SectionZeroIdeal.zeroIdeal L s).range_subschemeι] at hmem
  obtain ⟨y, hy⟩ := hmem
  exact ⟨y, Subtype.ext hy⟩

def divisor
    (p : X ⟶ Spec (CommRingCat.of ℂ)) [IsProper p] (hd : topologicalKrullDim X ≤ 1)
    (hDVR : ∀ x : X, x ≠ genericPoint X → IsDiscreteValuationRing (X.presheaf.stalk x))
    (L : LineBundle X) (s : GlobalSections X L.sheaf) (hs : s ≠ 0) : CurvePoint X →₀ ℕ :=
  Finsupp.ofSupportFinite (orderAt hDVR L s) (orderAt_finite_support p hd hDVR L s hs)

@[simp] theorem divisor_apply
    (p : X ⟶ Spec (CommRingCat.of ℂ)) [IsProper p] (hd : topologicalKrullDim X ≤ 1)
    (hDVR : ∀ x : X, x ≠ genericPoint X → IsDiscreteValuationRing (X.presheaf.stalk x))
    (L : LineBundle X) (s : GlobalSections X L.sheaf) (hs : s ≠ 0) (x : CurvePoint X) :
    divisor p hd hDVR L s hs x = orderAt hDVR L s x := rfl

theorem divisor_degree_eq_euler_difference
    (p : X ⟶ Spec (CommRingCat.of ℂ)) [IsProper p] (hd : topologicalKrullDim X ≤ 1)
    (hDVR : ∀ x : X, x ≠ genericPoint X → IsDiscreteValuationRing (X.presheaf.stalk x))
    (L : LineBundle X) (s : GlobalSections X L.sheaf) (hs : s ≠ 0)
    (hfiniteO : ∀ n ≤ 1, letI := Module.compHom (cohomology (structureSheaf X) n) (baseScalars p)
      FiniteDimensional ℂ (cohomology (structureSheaf X) n))
    (hfiniteL : ∀ n ≤ 1, letI := Module.compHom (cohomology L.sheaf n) (baseScalars p)
      FiniteDimensional ℂ (cohomology L.sheaf n))
    [Subsingleton (cohomology (structureSheaf X) 2)] :
    (divisor p hd hDVR L s hs).sum (fun _ n => (n : ℤ)) =
      eulerCharacteristic p 1 L.sheaf - eulerCharacteristic p 1 (structureSheaf X) := by
  classical
  let I := SectionZeroIdeal.zeroIdeal L s
  let : Finite I.subscheme := finite_subscheme_of_curve p hd I
    (SectionZeroIdeal.zeroIdeal_ne_bot L s hs)
  let : Fintype I.subscheme := Fintype.ofFinite _
  let D := divisor p hd hDVR L s hs
  let T := Finset.univ.map (zeroPointEmbedding L s hs)
  have hDT : D.support ⊆ T := by
    intro x hx
    have hn : orderAt hDVR L s x ≠ 0 := by simpa [D] using Finsupp.mem_support_iff.mp hx
    have hm : x.1 ∈ I.support := by
      by_contra hh
      exact hn (orderAt_eq_zero_of_not_mem hDVR L s x hh)
    change x.1 ∈ (I.support : Set X) at hm
    rw [← I.range_subschemeι] at hm
    obtain ⟨y, hy⟩ := hm
    exact Finset.mem_map.mpr ⟨y, Finset.mem_univ y, Subtype.ext hy⟩
  rw [euler_difference_eq_sum_zero_orders p hd L s hs hDVR hfiniteO hfiniteL]
  change D.sum (fun _ n => (n : ℤ)) = _
  rw [D.sum_of_support_subset hDT (fun _ n => (n : ℤ)) (by simp)]
  rw [Finset.sum_map]
  apply Finset.sum_congr rfl
  intro y _
  rfl

end PiExponent.SectionOrderDivisor

end

end OAI
end Source0485

-- Source: OAI/NumberTheory/PiExponent/Geometry/CurvePlaceSectionDivisor.lean
section Source0486
/-
Modification notice for the LogTwo project.
Derived from openai/math (Apache-2.0), revision adc7f1241b42e322a6451854ab7e4b4c146bf78a.
Original source: lean/OAI/NumberTheory/PiExponent/Geometry/CurvePlaceSectionDivisor.lean
Changes: Convert module/import declarations to the Lean 4.34 public module format.
See ../THIRD_PARTY_NOTICES.txt for provenance and the recorded changes.
-/

namespace OAI

noncomputable section
open AlgebraicGeometry CategoryTheory
open PiExponentSeshadri.Geometry
open PiExponent.CurveNormalizationModel PiExponent.CurveModelPlaces
open PiExponent.CurveValuationCenter

namespace PiExponent.CurvePlaceSectionDivisor

variable {E : Type} [Field E] [Algebra ℂ E]
variable (f : E) (hf : Transcendental ℂ f)
variable [FiniteDimensional (IntermediateField.adjoin ℂ {f}) E]

def divisor (L : LineBundle (parameterCurve f hf))
    (s : GlobalSections (parameterCurve f hf) L.sheaf) (hs : s ≠ 0) :
    NormalizedPlace ℂ E →₀ ℕ :=
  Finsupp.domCongr (placesEquivNongenericPoints f hf).symm
    (SectionOrderDivisor.divisor (parameterCurveStructureMap f hf)
      (parameterCurve_dimension_le_one f hf) (parameterCurve_stalkDVR f hf) L s hs)

@[simp] theorem divisor_apply (L : LineBundle (parameterCurve f hf))
    (s : GlobalSections (parameterCurve f hf) L.sheaf) (hs : s ≠ 0)
    (p : NormalizedPlace ℂ E) :
    divisor f hf L s hs p =
      SectionOrderDivisor.orderAt (parameterCurve_stalkDVR f hf) L s
        ⟨placePoint f hf p, placePoint_ne_genericPoint f hf p⟩ := by
  rw [divisor, Finsupp.domCongr_apply, Finsupp.equivMapDomain_apply]
  rfl

theorem degree_eq_euler_difference (L : LineBundle (parameterCurve f hf))
    (s : GlobalSections (parameterCurve f hf) L.sheaf) (hs : s ≠ 0)
    (hfiniteO : ∀ n ≤ 1,
      letI := Module.compHom (cohomology (structureSheaf (parameterCurve f hf)) n) (baseScalars (parameterCurveStructureMap f hf))
      FiniteDimensional ℂ (cohomology (structureSheaf (parameterCurve f hf)) n))
    (hfiniteL : ∀ n ≤ 1,
      letI := Module.compHom (cohomology L.sheaf n) (baseScalars (parameterCurveStructureMap f hf))
      FiniteDimensional ℂ (cohomology L.sheaf n)) :
    (divisor f hf L s hs).sum (fun _ n => (n : ℤ)) =
      eulerCharacteristic (parameterCurveStructureMap f hf) 1 L.sheaf -
      eulerCharacteristic (parameterCurveStructureMap f hf) 1
        (structureSheaf (parameterCurve f hf)) := by
  let : Subsingleton (cohomology (structureSheaf (parameterCurve f hf)) 2) := by
    apply subsingleton_of_forall_eq 0
    intro x
    exact parameterCurve_lineBundle_ext_zero f hf (L.pow 0) 2 (by omega) x
  rw [divisor, Finsupp.domCongr_apply, Finsupp.equivMapDomain_eq_mapDomain,
    Finsupp.sum_mapDomain_index (by simp) (by intros; simp)]
  exact SectionOrderDivisor.divisor_degree_eq_euler_difference
    (parameterCurveStructureMap f hf) (parameterCurve_dimension_le_one f hf)
    (parameterCurve_stalkDVR f hf) L s hs hfiniteO hfiniteL

theorem degree_eq_euler_difference_full (L : LineBundle (parameterCurve f hf))
    (s : GlobalSections (parameterCurve f hf) L.sheaf) (hs : s ≠ 0) :
    (divisor f hf L s hs).sum (fun _ n => (n : ℤ)) =
      eulerCharacteristic (parameterCurveStructureMap f hf) 1 L.sheaf -
      eulerCharacteristic (parameterCurveStructureMap f hf) 1
        (structureSheaf (parameterCurve f hf)) :=
  degree_eq_euler_difference f hf L s hs
    (parameterCurve_finiteLineCohomology f hf (L.pow 0))
    (parameterCurve_finiteLineCohomology f hf L)

end PiExponent.CurvePlaceSectionDivisor

end

end OAI
end Source0486

-- Source: OAI/NumberTheory/PiExponent/LocalAlgebra/LocalSectionOrder.lean
section Source0487
-- Modified in this edition: unused plain lemmas removed; see reduction.json.
/-
Modification notice for the LogTwo project.
Derived from openai/math (Apache-2.0), revision adc7f1241b42e322a6451854ab7e4b4c146bf78a.
Original source: lean/OAI/NumberTheory/PiExponent/LocalAlgebra/LocalSectionOrder.lean
Changes: Convert module/import declarations to the Lean 4.34 public module format.
See ../THIRD_PARTY_NOTICES.txt for provenance and the recorded changes.
-/

namespace OAI

noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open PiExponentSeshadri.Geometry PiExponentSeshadri.Frames
universe u

namespace PiExponent.LocalSectionOrder

def localCoefficient
    {A : Type u} [CommRing A] {M : (Spec (CommRingCat.of A)).Modules}
    (e : M ≅ O (Spec (CommRingCat.of A)))
    (s : O (Spec (CommRingCat.of A)) ⟶ M) : A :=
  (Scheme.ΓSpecIso (CommRingCat.of A)).hom (coefficient e s)

def localFrameChange
    {A : Type u} [CommRing A] {M : (Spec (CommRingCat.of A)).Modules}
    (e f : M ≅ O (Spec (CommRingCat.of A))) : Aˣ :=
  Units.map (Scheme.ΓSpecIso (CommRingCat.of A)).hom.hom (frameChange e f)

theorem localCoefficient_change
    {A : Type u} [CommRing A] {M : (Spec (CommRingCat.of A)).Modules}
    (e f : M ≅ O (Spec (CommRingCat.of A)))
    (s : O (Spec (CommRingCat.of A)) ⟶ M) :
    localCoefficient f s = (localFrameChange e f : A) * localCoefficient e s := by
  unfold localCoefficient
  rw [coefficient_change e f s, map_mul]
  rfl

def sectionOrder
    {A : Type u} [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
    {M : (Spec (CommRingCat.of A)).Modules}
    (e : M ≅ O (Spec (CommRingCat.of A)))
    (s : O (Spec (CommRingCat.of A)) ⟶ M) : ℕ∞ :=
  IsDiscreteValuationRing.addVal A (localCoefficient e s)

theorem sectionOrder_frame_independent
    {A : Type u} [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
    {M : (Spec (CommRingCat.of A)).Modules}
    (e f : M ≅ O (Spec (CommRingCat.of A)))
    (s : O (Spec (CommRingCat.of A)) ⟶ M) :
    sectionOrder e s = sectionOrder f s := by
  unfold sectionOrder
  rw [localCoefficient_change e f, AddValuation.map_mul,
    IsDiscreteValuationRing.addVal_eq_zero_of_unit, zero_add]

theorem localCoefficient_eq_zero_iff
    {A : Type u} [CommRing A] {M : (Spec (CommRingCat.of A)).Modules}
    (e : M ≅ O (Spec (CommRingCat.of A)))
    (s : O (Spec (CommRingCat.of A)) ⟶ M) : localCoefficient e s = 0 ↔ s = 0 := by
  constructor
  · intro h
    have hc : coefficient e s = 0 := by
      apply (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (CommRingCat.of A)).hom).1
      simpa only [localCoefficient, map_zero] using h
    have he : s ≫ e.hom = 0 := by
      ext U a
      change Γ(Spec (CommRingCat.of A), U) at a
      change (s ≫ e.hom).app U a = (0 : Γ(Spec (CommRingCat.of A), U))
      rw [end_apply, end_naturality]
      change a * (Spec (CommRingCat.of A)).presheaf.map _ (coefficient e s) = 0
      rw [hc, map_zero]
      exact mul_zero a
    apply (cancel_mono e.hom).mp
    simpa using he
  · intro h
    subst h
    unfold localCoefficient coefficient endValue
    rw [zero_comp]
    change (Scheme.ΓSpecIso (CommRingCat.of A)).hom (0 : Γ(Spec (CommRingCat.of A), ⊤)) = 0
    exact map_zero _

def zeroScheme
    {A : Type u} [CommRing A] {M : (Spec (CommRingCat.of A)).Modules}
    (e : M ≅ O (Spec (CommRingCat.of A)))
    (s : O (Spec (CommRingCat.of A)) ⟶ M) : Scheme :=
  Spec (CommRingCat.of (A ⧸ Ideal.span {localCoefficient e s}))

end PiExponent.LocalSectionOrder

end

end OAI
end Source0487

-- Source: OAI/NumberTheory/PiExponent/LocalAlgebra/LocalPullbackSectionOrder.lean
section Source0488
/-
Modification notice for the LogTwo project.
Derived from openai/math (Apache-2.0), revision adc7f1241b42e322a6451854ab7e4b4c146bf78a.
Original source: lean/OAI/NumberTheory/PiExponent/LocalAlgebra/LocalPullbackSectionOrder.lean
Changes: Convert module/import declarations to the Lean 4.34 public module format.
See ../THIRD_PARTY_NOTICES.txt for provenance and the recorded changes.
-/

namespace OAI

noncomputable section
open CategoryTheory AlgebraicGeometry TopologicalSpace
open PiExponentSeshadri.Geometry PiExponentSeshadri.Frames
open PiExponent.LocalSectionOrder PiExponent.CurveSectionDegree

namespace PiExponent.LocalPullbackSectionOrder

theorem topIso_germ_stalkMap {X : Scheme.{0}} (U : X.Opens) (y : U.toScheme) :
    U.topIso.hom ≫ X.presheaf.germ U (U.ι y) y.2 ≫ U.ι.stalkMap y =
      U.toScheme.presheaf.germ ⊤ y trivial := by
  have hmap : U.topIso.hom ≫ U.ι.app U =
      U.toScheme.presheaf.map (homOfLE (show U.ι ⁻¹ᵁ U ≤ ⊤ from le_top)).op := by
    rw [Scheme.Opens.ι_app, Scheme.Opens.topIso_hom]
    erw [← Functor.map_comp]
    rfl
  have hstalk := congrArg (fun k => U.topIso.hom ≫ k) (U.ι.germ_stalkMap U y y.2)
  have hres := congrArg (fun k => k ≫ U.toScheme.presheaf.germ (U.ι ⁻¹ᵁ U) y y.2) hmap
  exact hstalk.trans ((Category.assoc U.topIso.hom (U.ι.app U)
    (U.toScheme.presheaf.germ (U.ι ⁻¹ᵁ U) y y.2)).symm.trans
      (hres.trans (U.toScheme.presheaf.germ_res (homOfLE le_top) y y.2)))

theorem factor_coefficient_image {X : Scheme.{0}} {A : Type} [CommRing A] [IsLocalRing A]
    (U : X.Opens) (g : Spec (CommRingCat.of A) ⟶ U.toScheme)
    (c : Γ(U.toScheme, ⊤)) :
    (Scheme.ΓSpecIso (CommRingCat.of A)).hom (g.appTop c) =
      (Scheme.stalkClosedPointTo (g ≫ U.ι))
        (X.presheaf.germ U ((g ≫ U.ι) (IsLocalRing.closedPoint A))
          (g (IsLocalRing.closedPoint A)).2 (U.topIso.hom c)) := by
  have h := topIso_germ_stalkMap U (g (IsLocalRing.closedPoint A))
  have hg := Scheme.germ_stalkClosedPointTo g ⊤ trivial
  simp only [Scheme.stalkClosedPointTo_comp]
  change ((g.appTop ≫ (Scheme.ΓSpecIso (CommRingCat.of A)).hom) c) =
    ((U.topIso.hom ≫ X.presheaf.germ U _ _ ≫ U.ι.stalkMap _ ≫
      Scheme.stalkClosedPointTo g) c)
  erw [← Category.assoc U.topIso.hom
    (X.presheaf.germ U _ _ ≫ U.ι.stalkMap _) (Scheme.stalkClosedPointTo g), h]
  rw [hg]
  congr 1

theorem exists_frame_coefficient_germ {X : Scheme.{0}} {A : Type}
    [CommRing A] [IsLocalRing A] (f : Spec (CommRingCat.of A) ⟶ X)
    (L : LineBundle X) :
    ∃ e : (Scheme.Modules.pullback f).obj L.sheaf ≅ O (Spec (CommRingCat.of A)),
      ∀ s : GlobalSections X L.sheaf,
      localCoefficient e (pullbackSection f s) =
        (Scheme.stalkClosedPointTo f) (coefficientGermAt L s (f (IsLocalRing.closedPoint A))) := by
  let F := affineFrameAt L (f (IsLocalRing.closedPoint A))
  have hr : Set.range f ⊆ Set.range F.openSet.1.ι := by
    rw [Scheme.Opens.range_ι]
    rintro _ ⟨y, rfl⟩
    exact ((IsLocalRing.specializes_closedPoint y).map f.continuous).mem_open
      F.openSet.1.isOpen F.mem
  let g := IsOpenImmersion.lift F.openSet.1.ι f hr
  have hfac : g ≫ F.openSet.1.ι = f := IsOpenImmersion.lift_fac _ _ _
  obtain ⟨e, he⟩ := PullbackFrameCoefficient.exists_frame_of_factors_through_open
    F.openSet.1 g F.frame
  have haux (f' : Spec (CommRingCat.of A) ⟶ X) (hf' : g ≫ F.openSet.1.ι = f') :
      ∃ e' : (Scheme.Modules.pullback f').obj L.sheaf ≅ O (Spec (CommRingCat.of A)),
      ∀ s : GlobalSections X L.sheaf,
        localCoefficient e' (pullbackSection f' s) =
          (Scheme.stalkClosedPointTo f')
            ((X.presheaf.germ F.openSet.1 (f' (IsLocalRing.closedPoint A))
              (by rw [← hf']; exact (g (IsLocalRing.closedPoint A)).2))
              (F.openSet.1.topIso.hom (coefficient F.frame (restrictSection F.openSet.1.ι s)))) := by
    subst f'
    refine ⟨e, fun s => ?_⟩
    unfold localCoefficient
    exact (congrArg (Scheme.ΓSpecIso (CommRingCat.of A)).hom (he s)).trans
      (factor_coefficient_image F.openSet.1 g _)
  exact haux f hfac

theorem sectionOrder_eq_germ_order {X : Scheme.{0}} {A : Type}
    [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
    (f : Spec (CommRingCat.of A) ⟶ X)
    [IsDomain (X.presheaf.stalk (f (IsLocalRing.closedPoint A)))]
    [IsDiscreteValuationRing (X.presheaf.stalk (f (IsLocalRing.closedPoint A)))]
    [IsIso (Scheme.stalkClosedPointTo f)]
    (L : LineBundle X) (s : GlobalSections X L.sheaf)
    (e : (Scheme.Modules.pullback f).obj L.sheaf ≅ O (Spec (CommRingCat.of A))) :
    sectionOrder e (pullbackSection f s) =
      IsDiscreteValuationRing.addVal (X.presheaf.stalk (f (IsLocalRing.closedPoint A)))
        (coefficientGermAt L s (f (IsLocalRing.closedPoint A))) := by
  obtain ⟨e', he'⟩ := exists_frame_coefficient_germ f L
  rw [sectionOrder_frame_independent e e', sectionOrder, he']
  exact CurveModelLocalOrder.addVal_ringEquiv
    (asIso (Scheme.stalkClosedPointTo f)).commRingCatIsoToRingEquiv _

end PiExponent.LocalPullbackSectionOrder

end

end OAI
end Source0488

-- Source: OAI/NumberTheory/PiExponent/Geometry/CurvePlaceSectionOrder.lean
section Source0489
/-
Modification notice for the LogTwo project.
Derived from openai/math (Apache-2.0), revision adc7f1241b42e322a6451854ab7e4b4c146bf78a.
Original source: lean/OAI/NumberTheory/PiExponent/Geometry/CurvePlaceSectionOrder.lean
Changes: Convert module/import declarations to the Lean 4.34 public module format.
See ../THIRD_PARTY_NOTICES.txt for provenance and the recorded changes.
-/

namespace OAI

noncomputable section
open AlgebraicGeometry CategoryTheory
open PiExponentSeshadri.Geometry PiExponentSeshadri.Frames
open PiExponent.CurveNormalizationModel PiExponent.CurveModelPlaces
open PiExponent.CurveValuationCenter PiExponent.CurvePlaceCenter
open PiExponent.LocalSectionOrder

namespace PiExponent.CurvePlaceSectionOrder

variable {E : Type} [Field E] [Algebra ℂ E]
variable (f : E) (hf : Transcendental ℂ f)
variable [FiniteDimensional (IntermediateField.adjoin ℂ {f}) E]

theorem divisor_eq_local_order (L : LineBundle (parameterCurve f hf))
    (s : GlobalSections (parameterCurve f hf) L.sheaf) (hs : s ≠ 0)
    (p : NormalizedPlace ℂ E)
    (e : (Scheme.Modules.pullback (centerMorphism f hf p)).obj L.sheaf ≅
      O (Spec (CommRingCat.of (PlaceValuationRing.ring p)))) :
    CurvePlaceSectionDivisor.divisor f hf L s hs p =
      (sectionOrder e (pullbackSection (centerMorphism f hf p) s)).toNat := by
  let : IsDiscreteValuationRing ((parameterCurve f hf).presheaf.stalk
      ((centerMorphism f hf p) (IsLocalRing.closedPoint (PlaceValuationRing.ring p)))) := by
    rw [centerMorphism_closedPoint]
    exact parameterCurve_stalkDVR f hf _ (placePoint_ne_genericPoint f hf p)
  have h := LocalPullbackSectionOrder.sectionOrder_eq_germ_order
    (centerMorphism f hf p) L s e
  have hp : (centerMorphism f hf p) (IsLocalRing.closedPoint (PlaceValuationRing.ring p)) ≠
      genericPoint (parameterCurve f hf) := by
    rw [centerMorphism_closedPoint]
    exact placePoint_ne_genericPoint f hf p
  have h' : (sectionOrder e (pullbackSection (centerMorphism f hf p) s)).toNat =
      SectionOrderDivisor.orderAt (parameterCurve_stalkDVR f hf) L s
        ⟨(centerMorphism f hf p) (IsLocalRing.closedPoint (PlaceValuationRing.ring p)), hp⟩ :=
    congrArg ENat.toNat h
  have heq : (⟨(centerMorphism f hf p) (IsLocalRing.closedPoint (PlaceValuationRing.ring p)), hp⟩ :
      SectionOrderDivisor.CurvePoint (parameterCurve f hf)) =
        ⟨placePoint f hf p, placePoint_ne_genericPoint f hf p⟩ := by
    apply Subtype.ext
    exact centerMorphism_closedPoint f hf p
  rw [heq] at h'
  exact (CurvePlaceSectionDivisor.divisor_apply f hf L s hs p).trans h'.symm

end PiExponent.CurvePlaceSectionOrder

end

end OAI
end Source0489

-- Source: OAI/NumberTheory/PiExponent/LocalAlgebra/InvertibleIdealLocal.lean
section Source0490
/-
Modification notice for the LogTwo project.
Derived from openai/math (Apache-2.0), revision adc7f1241b42e322a6451854ab7e4b4c146bf78a.
Original source: lean/OAI/NumberTheory/PiExponent/LocalAlgebra/InvertibleIdealLocal.lean
Changes: Convert module/import declarations to the Lean 4.34 public module format.
See ../THIRD_PARTY_NOTICES.txt for provenance and the recorded changes.
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
end Source0490

-- Source: OAI/NumberTheory/PiExponent/LocalAlgebra/TensorIdealInclusion.lean
section Source0491
-- Modified in this edition: unused plain lemmas removed; see reduction.json.
/-
Modification notice for the LogTwo project.
Derived from openai/math (Apache-2.0), revision adc7f1241b42e322a6451854ab7e4b4c146bf78a.
Original source: lean/OAI/NumberTheory/PiExponent/LocalAlgebra/TensorIdealInclusion.lean
Changes: Convert module/import declarations to the Lean 4.34 public module format.
See ../THIRD_PARTY_NOTICES.txt for provenance and the recorded changes.
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
end Source0491

-- Source: OAI/NumberTheory/PiExponent/LocalAlgebra/IdealTensorPowers.lean
section Source0492
/-
Modification notice for the LogTwo project.
Derived from openai/math (Apache-2.0), revision adc7f1241b42e322a6451854ab7e4b4c146bf78a.
Original source: lean/OAI/NumberTheory/PiExponent/LocalAlgebra/IdealTensorPowers.lean
Changes: Convert module/import declarations to the Lean 4.34 public module format.
See ../THIRD_PARTY_NOTICES.txt for provenance and the recorded changes.
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
    Ideal.span {(affineMapCoefficient U (idealPowerFrame J U.1 e n)
      (Scheme.Modules.restrictUnitIso U.1.ι) (idealPowerInclusion J ι n))} =
      (Ideal.span {affineMapCoefficient U e (Scheme.Modules.restrictUnitIso U.1.ι) ι})^n := by
  induction n with
  | zero =>
    simp only [idealPowerFrame, idealPowerInclusion]
    exact (congrArg (fun r : Γ(X,U.1) => Ideal.span {r})
      (affineMapCoefficient_id U (Scheme.Modules.restrictUnitIso U.1.ι))).trans (by simp)
  | succ n ih =>
    change Ideal.span {(affineMapCoefficient U (tensorFrame J (J.pow n) U.1 e (idealPowerFrame J U.1 e n))
      (Scheme.Modules.restrictUnitIso U.1.ι) (tensorInclusion J (J.pow n) ι ≫ idealPowerInclusion J ι n))} = _
    erw [affineMapCoefficient_comp U _ (idealPowerFrame J U.1 e n),
      ← Ideal.span_singleton_mul_span_singleton,ih]
    rw [show Ideal.span {(affineMapCoefficient U (tensorFrame J (J.pow n) U.1 e (idealPowerFrame J U.1 e n))
      (idealPowerFrame J U.1 e n) (tensorInclusion J (J.pow n) ι))} =
      Ideal.span {affineMapCoefficient U e (Scheme.Modules.restrictUnitIso U.1.ι) ι} from
        tensor_inclusion_ideal J (J.pow n) ι U e (idealPowerFrame J U.1 e n)]
    rw [pow_succ']

end
end PiExponentSeshadri.Geometry

end OAI
end Source0492

-- Source: OAI/NumberTheory/PiExponent/LocalAlgebra/GlobalInvertibleIdeal.lean
section Source0493
/-
Modification notice for the LogTwo project.
Derived from openai/math (Apache-2.0), revision adc7f1241b42e322a6451854ab7e4b4c146bf78a.
Original source: lean/OAI/NumberTheory/PiExponent/LocalAlgebra/GlobalInvertibleIdeal.lean
Changes: Convert module/import declarations to the Lean 4.34 public module format.
See ../THIRD_PARTY_NOTICES.txt for provenance and the recorded changes.
-/

namespace OAI

namespace PiExponentSeshadri.InvertibleLocal
noncomputable section

section
open CategoryTheory AlgebraicGeometry Opposite
open PiExponentSeshadri.Geometry
variable {X Y Z : Scheme} {I : X.IdealSheafData} {f : Y ⟶ X}

lemma restricted_image_on_chart (J : LineBundle Y) (ι : J.sheaf ⟶ structureSheaf Y)
    (h : PresentsPullbackIdeal I f J ι)
    (j : Z ⟶ Y) [IsOpenImmersion j] (U : Z.affineOpens) (V : X.affineOpens)
    (hUV : j ''ᵁ U.1 ≤ f ⁻¹ᵁ V.1) :
    ((restrictedInclusion J ι j).val.app (op U.1)).hom.range =
      ((I.comap f).comap j).ideal U := by
  rw [(I.comap f).ideal_comap_of_isOpenImmersion j U]
  have he := (h.2 ⟨j ''ᵁ U.1, U.2.image_of_isOpenImmersion j⟩ V hUV).trans
    (IdealPullback.comap_ideal I f _ V hUV).symm
  ext r
  change (∃ s, (restrictedInclusion J ι j).val.app (op U.1) s = r) ↔ _
  erw [Ideal.mem_comap, ← he]
  change (∃ s, _) ↔ ∃ s, ι.val.app (op (j ''ᵁ U.1)) s = (j.appIso U.1).inv r
  constructor
  · rintro ⟨s, hs⟩
    refine ⟨s, ?_⟩
    change (j.appIso U.1).hom (ι.val.app (op (j ''ᵁ U.1)) s) = r at hs
    rw [← hs]
    exact (congrArg (fun k : Γ(Y, j ''ᵁ U.1) ⟶ Γ(Y, j ''ᵁ U.1) =>
      k (ι.val.app (op (j ''ᵁ U.1)) s)) (j.appIso U.1).hom_inv_id).symm
  · rintro ⟨s, hs⟩
    refine ⟨s, ?_⟩
    change (j.appIso U.1).hom (ι.val.app (op (j ''ᵁ U.1)) s) = r
    rw [hs]
    exact congrArg (fun k : Γ(Z, U.1) ⟶ Γ(Z, U.1) => k r) (j.appIso U.1).inv_hom_id

private theorem globalInvertible_mono_iso_inv_comp {C : Type*} [Category C] {A B D : C}
    (e : A ≅ B) (g : A ⟶ D) [Mono g] : Mono (e.inv ≫ g) := inferInstance

lemma local_equation_on_chart (J : LineBundle Y) (ι : J.sheaf ⟶ structureSheaf Y)
    (h : PresentsPullbackIdeal I f J ι)
    (U : Y.affineOpens) (V : X.affineOpens) (hUV : U.1 ≤ f ⁻¹ᵁ V.1)
    (e : J.sheaf.restrict U.1.ι ≅ structureSheaf U.1.toScheme) :
    ∃ r : Γ(U.1.toScheme, ⊤), IsRegular r ∧
      ((I.comap f).comap U.1.ι).ideal ⟨⊤, isAffineOpen_top _⟩ = Ideal.span {r} := by
  let : Mono ι := h.1
  let g : UnitEndomorphism.unit U.1.toScheme ⟶ UnitEndomorphism.unit U.1.toScheme :=
    e.inv ≫ restrictedInclusion J ι U.1.ι
  let : Mono (restrictedInclusion J ι U.1.ι) := restrictedInclusion_mono J ι U.1.ι
  have : Mono g := globalInvertible_mono_iso_inv_comp e (restrictedInclusion J ι U.1.ι)
  refine ⟨UnitEndomorphism.equation g ⊤, UnitEndomorphism.equation_regular g ⊤, ?_⟩
  rw [← UnitEndomorphism.image_principal g ⊤,
    ← restricted_image_on_chart J ι h U.1.ι ⟨⊤, isAffineOpen_top _⟩ V
      (by simpa only [Scheme.Opens.ι_image_top] using hUV)]
  ext r
  change (∃ s, (restrictedInclusion J ι U.1.ι).val.app (op ⊤) s = r) ↔
    ∃ s, (restrictedInclusion J ι U.1.ι).val.app (op ⊤) (e.inv.val.app (op ⊤) s) = r
  constructor
  · rintro ⟨s, hs⟩
    refine ⟨e.hom.val.app (op ⊤) s, ?_⟩
    have ht : e.inv.val.app (op ⊤) (e.hom.val.app (op ⊤) s) = s := by
      exact congrArg (fun k : J.sheaf.restrict U.1.ι ⟶ J.sheaf.restrict U.1.ι =>
        k.val.app (op ⊤) s) e.hom_inv_id
    rw [ht]; exact hs
  · rintro ⟨s, hs⟩
    exact ⟨e.inv.val.app (op ⊤) s, hs⟩

lemma local_equations (hf : InvertiblePullbackIdeal I f) (y : Y) :
    ∃ U : Y.affineOpens, y ∈ U.1 ∧ ∃ r : Γ(U.1.toScheme, ⊤), IsRegular r ∧
      ((I.comap f).comap U.1.ι).ideal ⟨⊤, isAffineOpen_top _⟩ = Ideal.span {r} := by
  obtain ⟨J, ι, h⟩ := hf
  obtain ⟨W, hyW, ⟨e⟩⟩ := J.locallyRankOne y
  obtain ⟨V, hV, hyV, _⟩ := exists_isAffineOpen_mem_and_subset
    (show f y ∈ (⊤ : X.Opens) from trivial)
  obtain ⟨U, hU, hyU, hUV⟩ := exists_isAffineOpen_mem_and_subset
    (show y ∈ W ⊓ f ⁻¹ᵁ V from ⟨hyW, hyV⟩)
  refine ⟨⟨U, hU⟩, hyU, ?_⟩
  exact local_equation_on_chart J ι h ⟨U, hU⟩ ⟨V, hV⟩
    (hUV.trans inf_le_right) (frameOfLE J.sheaf (hUV.trans inf_le_left) e)

lemma invertible_iff_local_equations :
    InvertiblePullbackIdeal I f ↔
    ∀ y : Y, ∃ U : Y.affineOpens, y ∈ U.1 ∧
      ∃ r : Γ(U.1.toScheme, ⊤), IsRegular r ∧
      ((I.comap f).comap U.1.ι).ideal ⟨⊤, isAffineOpen_top _⟩ = Ideal.span {r} :=
  ⟨local_equations, invertible_of_local_equations⟩

lemma invertible_congr {X' : Scheme} {I' : X'.IdealSheafData} {f' : Y ⟶ X'}
    (he : I.comap f = I'.comap f') :
    InvertiblePullbackIdeal I f ↔ InvertiblePullbackIdeal I' f' := by
  rw [invertible_iff_local_equations, invertible_iff_local_equations, he]

end

open CategoryTheory AlgebraicGeometry
open PiExponentSeshadri.Geometry
variable {X Y Z : Scheme}

lemma presents_restrict_general (I : X.IdealSheafData) (f : Y ⟶ X)
    (J : LineBundle Y) (ι : J.sheaf ⟶ structureSheaf Y)
    (hf : PresentsPullbackIdeal I f J ι) (j : Z ⟶ Y) [IsOpenImmersion j] :
    PresentsPullbackIdeal I (j ≫ f) (restrictLineBundle J j) (restrictedInclusion J ι j) := by
  let : Mono ι := hf.1
  refine ⟨restrictedInclusion_mono J ι j, ?_⟩
  intro U V e
  change ((restrictedInclusion J ι j).val.app (Opposite.op U.1)).hom.range = _
  rw [restricted_image_on_chart J ι hf j U V ?_, ← Scheme.IdealSheafData.comap_comp]
  · exact IdealPullback.comap_ideal I (j ≫ f) U V e
  · rintro _ ⟨z, hz, rfl⟩
    exact e hz

lemma invertible_restrict_general (I : X.IdealSheafData) (f : Y ⟶ X)
    (hf : InvertiblePullbackIdeal I f) (j : Z ⟶ Y) [IsOpenImmersion j] :
    InvertiblePullbackIdeal I (j ≫ f) := by
  obtain ⟨J, ι, h⟩ := hf
  exact ⟨restrictLineBundle J j, restrictedInclusion J ι j,
    presents_restrict_general I f J ι h j⟩

lemma invertible_of_cover (I : X.IdealSheafData) (f : Y ⟶ X) (C : Y.OpenCover)
    (hf : ∀ i, InvertiblePullbackIdeal I (C.f i ≫ f)) :
    InvertiblePullbackIdeal I f := by
  let J : LineBundle Y := {
    sheaf := IdealModule.closedModule (I.comap f)
    locallyRankOne y := by
      let i := C.idx y
      obtain ⟨z, hz⟩ := C.covers y
      obtain ⟨U, hzU, r, hr, hIr⟩ := local_equations (hf i) z
      let j := U.1.ι ≫ C.f i
      have he : ((I.comap f).comap j).ideal ⟨⊤, isAffineOpen_top U.1.toScheme⟩ =
          Ideal.span {r} := by
        simpa only [j, Scheme.IdealSheafData.comap_comp] using hIr
      obtain ⟨e⟩ := IdealModule.frame_restriction (I.comap f) j r he hr.1
      refine ⟨j.opensRange, ?_, ⟨IdealModule.frameOnRange _ j e⟩⟩
      exact ⟨⟨z, hzU⟩, hz⟩ }
  have : Mono (IdealModule.closedInclusion (I.comap f)) :=
    inferInstanceAs (Mono (IdealModule.inclusion (I.comap f).subschemeι))
  refine ⟨J, IdealModule.closedInclusion (I.comap f), this, ?_⟩
  intro U V e
  change ((IdealModule.closedInclusion (I.comap f)).val.app (Opposite.op U.1)).hom.range = _
  rw [IdealModule.closed_image]
  exact IdealPullback.comap_ideal I f U V e

end
end PiExponentSeshadri.InvertibleLocal

end OAI
end Source0493

-- Source: OAI/NumberTheory/PiExponent/Approximation/CoherentCokernels.lean
section Source0494
/-
Modification notice for the LogTwo project.
Derived from openai/math (Apache-2.0), revision adc7f1241b42e322a6451854ab7e4b4c146bf78a.
Original source: lean/OAI/NumberTheory/PiExponent/Approximation/CoherentCokernels.lean
Changes: Convert module/import declarations to the Lean 4.34 public module format.
See ../THIRD_PARTY_NOTICES.txt for provenance and the recorded changes.
-/

namespace OAI

namespace PiExponent.CoherentCokernels
noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite
open PiExponent.FiniteGlobalPresentation PiExponent.CoherentAffineFinite
universe u

private def presentationOfIso (X : Scheme.{u})
    {M N : SheafOfModules.{u} X.ringCatSheaf} (e : M ≅ N)
    (P : M.Presentation) : N.Presentation := by
  let : IsIso e.hom := e.isIso_hom
  exact P.ofIsIso e.hom

def specCokernelIso {R : CommRingCat.{u}} {M N : (Spec R).Modules}
    [M.IsQuasicoherent] [N.IsQuasicoherent] (f : M ⟶ N) :
    let g := (tilde.functor R).preimage
      ((asIso M.fromTildeΓ).hom ≫ f ≫ (asIso N.fromTildeΓ).inv)
    (tilde.functor R).obj (cokernel g) ≅ cokernel f := by
  intro g
  let hm := Scheme.Modules.isIso_fromTildeΓ_of_isQuasicoherent M
  let hn := Scheme.Modules.isIso_fromTildeΓ_of_isQuasicoherent N
  let em := @asIso _ _ _ _ M.fromTildeΓ hm
  let en := @asIso _ _ _ _ N.fromTildeΓ hn
  exact PreservesCokernel.iso (tilde.functor R) g ≪≫
    cokernel.mapIso ((tilde.functor R).map g) f em en (by
        change (tilde.functor R).map ((tilde.functor R).preimage _) ≫ _ = _
        erw [Functor.map_preimage]
        exact (Category.assoc em.hom (f ≫ en.inv) en.hom).trans
          (congrArg (fun q => em.hom ≫ q)
            ((Category.assoc f en.inv en.hom).trans
              ((congrArg (fun q => f ≫ q) en.inv_hom_id).trans (Category.comp_id f)))))

theorem spec_cokernel_exists_finitePresentation {R : CommRingCat.{u}} [IsNoetherianRing R]
    {M N : (Spec R).Modules} [M.IsQuasicoherent] [N.IsQuasicoherent]
    [Module.Finite R ((modulesSpecToSheaf.obj N).obj.obj (op ⊤))] (f : M ⟶ N) :
    ∃ P : (cokernel f).Presentation, P.IsFinite := by
  let g := (tilde.functor R).preimage
    ((asIso M.fromTildeΓ).hom ≫ f ≫ (asIso N.fromTildeΓ).inv)
  have : Module.Finite R (moduleSpecΓFunctor.obj N) := inferInstanceAs
    (Module.Finite R ((modulesSpecToSheaf.obj N).obj.obj (op ⊤)))
  have : Module.Finite R (cokernel (C := ModuleCat R) g) :=
    Module.Finite.of_surjective (cokernel.π g).hom
      ((ModuleCat.epi_iff_surjective _).mp inferInstance)
  obtain ⟨P,hP⟩ := tilde_exists_finitePresentation (cokernel g)
  exact ⟨presentationOfIso (Spec R) (specCokernelIso f) P,
    ⟨⟨hP.isFiniteType_generators.finite⟩, ⟨hP.isFiniteType_relations.finite⟩⟩⟩

theorem affine_cokernel_exists_finitePresentation {X : Scheme.{u}}
    [IsAffine X] [IsLocallyNoetherian X] {M N : X.Modules}
    [M.IsQuasicoherent] [N.IsQuasicoherent] (f : M ⟶ N)
    (hN : LocallyFinitelyGenerated N) :
    ∃ P : (cokernel f).Presentation, P.IsFinite := by
  let a := X.isoSpec.inv
  let F := Scheme.Modules.restrictFunctor a
  have : IsNoetherianRing Γ(X,⊤) :=
    IsLocallyNoetherian.component_noetherian ⟨⊤, isAffineOpen_top X⟩
  have : Module.Finite Γ(X,⊤) ((modulesSpecToSheaf.obj (N.restrict a)).obj.obj (op ⊤)) :=
    spec_sections_finite_of_localGenerators (N.restrict a) (hN.restrict a)
  obtain ⟨P,hP⟩ := spec_cokernel_exists_finitePresentation (F.map f)
  let e := PreservesCokernel.iso F f
  let P' := presentationOfIso (Spec Γ(X,⊤)) e.symm P
  let b := X.isoSpec.hom
  let G : SheafOfModules (Spec Γ(X,⊤)).ringCatSheaf ⥤ SheafOfModules X.ringCatSheaf :=
    Scheme.Modules.restrictFunctor b
  let : PreservesColimitsOfSize.{u,u} G :=
    (Scheme.Modules.restrictAdjunction b).leftAdjoint_preservesColimits
  let Q := P'.map G (Scheme.Modules.restrictUnitIso b).symm
  let e₁ := (Scheme.Modules.restrictFunctorComp b a).app (cokernel f)
  have e₂ : (cokernel f).restrict (𝟙 X) ≅ ((cokernel f).restrict a).restrict b := by
    change (cokernel f).restrict (b ≫ a) ≅ ((cokernel f).restrict a).restrict b at e₁
    simpa only [b, a, Iso.hom_inv_id] using e₁
  let e₃ := e₂.symm ≪≫ Scheme.Modules.restrictFunctorId.app (cokernel f)
  exact ⟨presentationOfIso X e₃ Q,
    ⟨⟨hP.isFiniteType_generators.finite⟩, ⟨hP.isFiniteType_relations.finite⟩⟩⟩

theorem cokernel_isFinitePresentation {X : Scheme.{u}} [IsLocallyNoetherian X]
    {M N : X.Modules} [M.IsQuasicoherent] [N.IsFinitePresentation] (f : M ⟶ N) :
    (cokernel f).IsFinitePresentation := by
  apply isFinitePresentation_of_affine_presentations
  intro U
  have : IsAffine U.1.toScheme := U.2
  let F := Scheme.Modules.restrictFunctor U.1.ι
  let : N.IsQuasicoherent :=
    (SheafOfModules.IsFinitePresentation.exists_quasicoherentData N).choose.isQuasicoherent
  obtain ⟨P,hP⟩ := affine_cokernel_exists_finitePresentation (F.map f)
    ((locallyFinitelyGenerated_of_finitePresentation N).restrict U.1.ι)
  let e := PreservesCokernel.iso F f
  exact ⟨presentationOfIso U.1.toScheme e.symm P,
    ⟨⟨hP.isFiniteType_generators.finite⟩, ⟨hP.isFiniteType_relations.finite⟩⟩⟩
end
end PiExponent.CoherentCokernels

end OAI
end Source0494

-- Source: OAI/NumberTheory/PiExponent/Approximation/FullSupportNilpotence.lean
section Source0495
-- Modified in this edition: unused plain lemmas removed; see reduction.json.
/-
Modification notice for the LogTwo project.
Derived from openai/math (Apache-2.0), revision adc7f1241b42e322a6451854ab7e4b4c146bf78a.
Original source: lean/OAI/NumberTheory/PiExponent/Approximation/FullSupportNilpotence.lean
Changes: Convert module/import declarations to the Lean 4.34 public module format.
See ../THIRD_PARTY_NOTICES.txt for provenance and the recorded changes.
-/

namespace OAI

namespace PiExponentSeshadri.Geometry
noncomputable section
open AlgebraicGeometry CategoryTheory TopologicalSpace
variable {X : Scheme}

lemma idealSheaf_le_nilradical_of_fullSupport (I : X.IdealSheafData)
    (hI : I.support = ⊤) : I ≤ X.nilradical := by
  have h : (⊤ : Closeds X) ≤ I.support := by rw [hI]
  simpa only [Scheme.IdealSheafData.vanishingIdeal_top] using
    Scheme.IdealSheafData.le_support_iff_le_vanishingIdeal.mp h

lemma affineIdeal_isNilpotent_of_fullSupport [IsLocallyNoetherian X]
    (I : X.IdealSheafData) (hI : I.support = ⊤) (U : X.affineOpens) :
    IsNilpotent (I.ideal U) := by
  let := IsLocallyNoetherian.component_noetherian U
  apply (Ideal.FG.isNilpotent_iff_le_nilradical (IsNoetherian.noetherian _)).mpr
  exact idealSheaf_le_nilradical_of_fullSupport I hI U

theorem exists_pos_pow_eq_bot_of_fullSupport [IsNoetherian X]
    (I : X.IdealSheafData) (hI : I.support = ⊤) :
    ∃ n : ℕ, 0 < n ∧ I ^ n = ⊥ := by
  classical
  have hlocal : ∀ U : X.affineOpens, ∃ n : ℕ, I.ideal U ^ n = ⊥ :=
    fun U => affineIdeal_isNilpotent_of_fullSupport I hI U
  choose n hn using hlocal
  obtain ⟨S, hS⟩ := isCompact_univ.elim_finite_subcover
    (fun U : X.affineOpens => (U.1 : Set X)) (fun U => U.1.isOpen)
    (by
      intro x _
      have hx : x ∈ (⨆ U : X.affineOpens, U.1) := by
        rw [iSup_affineOpens_eq_top X]
        trivial
      obtain ⟨U, hU⟩ := Opens.mem_iSup.mp hx
      exact Set.mem_iUnion.mpr ⟨U, hU⟩)
  refine ⟨S.sup n + 1, Nat.succ_pos _, ?_⟩
  apply Scheme.IdealSheafData.ext_of_iSup_eq_top (fun U : S => U.val)
  · apply top_unique
    intro x _
    obtain ⟨U, hU⟩ := Set.mem_iUnion.mp (hS (show x ∈ Set.univ from trivial))
    obtain ⟨hUS, hxU⟩ := Set.mem_iUnion.mp hU
    exact Opens.mem_iSup.mpr ⟨⟨U, hUS⟩, hxU⟩
  · intro U
    change I.ideal U.val ^ (S.sup n + 1) = ⊥
    apply le_bot_iff.mp
    calc
      I.ideal U.val ^ (S.sup n + 1) ≤ I.ideal U.val ^ n U.val :=
        Ideal.pow_le_pow_right ((Finset.le_sup U.property).trans (Nat.le_succ _))
      _ = ⊥ := hn U.val

end
end PiExponentSeshadri.Geometry

end OAI
end Source0495

-- Source: OAI/NumberTheory/PiExponent/LocalAlgebra/IdealPowerFiltration.lean
section Source0496
/-
Modification notice for the LogTwo project.
Derived from openai/math (Apache-2.0), revision adc7f1241b42e322a6451854ab7e4b4c146bf78a.
Original source: lean/OAI/NumberTheory/PiExponent/LocalAlgebra/IdealPowerFiltration.lean
Changes: Convert module/import declarations to the Lean 4.34 public module format.
See ../THIRD_PARTY_NOTICES.txt for provenance and the recorded changes.
-/

namespace OAI

namespace PiExponentSeshadri.IdealModule
noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite
variable {X : Scheme.{0}}

instance closedInclusion_mono (I : X.IdealSheafData) : Mono (closedInclusion I) :=
  inferInstanceAs (Mono (inclusion I.subschemeι))

lemma closedInclusion_structureMap_eq_zero {I J : X.IdealSheafData} (h : I ≤ J) :
    closedInclusion I ≫ structureMap J.subschemeι = 0 := by
  ext U x
  change J.subschemeι.app U ((closedInclusion I).app U x) = 0
  have hi : I.subschemeι.app U ((closedInclusion I).app U x) = 0 :=
    congrArg (fun f => f.app U x) (kernel.condition (structureMap I.subschemeι))
  rw [Scheme.Hom.congr_app (Scheme.IdealSheafData.inclusion_subschemeι h).symm U,
    Scheme.Hom.comp_app]
  change J.subscheme.presheaf.map _
    ((Scheme.IdealSheafData.inclusion h).app _
      (I.subschemeι.app U ((closedInclusion I).app U x))) = 0
  rw [hi, map_zero, map_zero]

def closedMap {I J : X.IdealSheafData} (h : I ≤ J) : closedModule I ⟶ closedModule J :=
  kernel.lift (structureMap J.subschemeι) (closedInclusion I)
    (closedInclusion_structureMap_eq_zero h)

@[reassoc (attr := simp)] lemma closedMap_inclusion {I J : X.IdealSheafData} (h : I ≤ J) :
    closedMap h ≫ closedInclusion J = closedInclusion I := kernel.lift_ι _ _ _

instance closedMap_mono {I J : X.IdealSheafData} (h : I ≤ J) : Mono (closedMap h) := by
  have : Mono (closedMap h ≫ closedInclusion J) := by rw [closedMap_inclusion]; infer_instance
  exact mono_of_mono (closedMap h) (closedInclusion J)

@[simp] lemma closedMap_refl (I : X.IdealSheafData) : closedMap (le_refl I) = 𝟙 _ := by
  apply (cancel_mono (closedInclusion I)).mp
  simp

@[reassoc (attr := simp)] lemma closedMap_comp {I J K : X.IdealSheafData}
    (hIJ : I ≤ J) (hJK : J ≤ K) : closedMap hIJ ≫ closedMap hJK = closedMap (hIJ.trans hJK) := by
  apply (cancel_mono (closedInclusion K)).mp
  simp

def powerMap (I : X.IdealSheafData) (n : ℕ) : closedModule (I^(n+1)) ⟶ closedModule (I^n) :=
  closedMap (fun _U => Ideal.pow_le_pow_right (Nat.le_succ n))

instance powerMap_mono (I : X.IdealSheafData) (n : ℕ) : Mono (powerMap I n) :=
  closedMap_mono _

def powerLayer (I : X.IdealSheafData) (n : ℕ) : X.Modules := cokernel (powerMap I n)

def powerSequence (I : X.IdealSheafData) (n : ℕ) : ShortComplex X.Modules :=
  ShortComplex.mk (powerMap I n) (cokernel.π (powerMap I n)) (cokernel.condition _)

theorem powerSequence_shortExact (I : X.IdealSheafData) (n : ℕ) :
    (powerSequence I n).ShortExact := by
  change (ShortComplex.mk (powerMap I n) (cokernel.π (powerMap I n)) _).ShortExact
  exact { exact := ShortComplex.exact_of_g_is_cokernel _ (cokernelIsCokernel (powerMap I n)) }

theorem closedModule_bot_isZero : IsZero (closedModule (⊥ : X.IdealSheafData)) := by
  have hmono : Mono (structureMap (Scheme.IdealSheafData.subschemeι (⊥ : X.IdealSheafData))) := by
    let F := Scheme.Modules.toPresheafOfModules X
    apply F.mono_of_mono_map
    apply PresheafOfModules.mono_of_injective
    intro U
    exact (ConcreteCategory.bijective_of_isIso
      ((⊥ : X.IdealSheafData).subschemeι.app U.unop)).injective
  exact isZero_kernel_of_mono _

theorem closedModule_isFinitePresentation [IsLocallyNoetherian X] (I : X.IdealSheafData) :
    (closedModule I).IsFinitePresentation := by
  have : (unit X).IsFinitePresentation :=
    PiExponent.GeometrySupport.LineBundleCoherent.structureSheaf_isFinitePresentation
  have : (unit I.subscheme).IsFinitePresentation :=
    PiExponent.GeometrySupport.LineBundleCoherent.structureSheaf_isFinitePresentation
  let : ((Scheme.Modules.pushforward I.subschemeι).obj (unit I.subscheme)).IsQuasicoherent :=
    (SheafOfModules.IsFinitePresentation.exists_quasicoherentData
      ((Scheme.Modules.pushforward I.subschemeι).obj (unit I.subscheme))).choose.isQuasicoherent
  exact PiExponent.FiniteGlobalPresentation.kernel_isFinitePresentation (structureMap I.subschemeι)

theorem powerLayer_isFinitePresentation [IsLocallyNoetherian X]
    (I : X.IdealSheafData) (n : ℕ) : (powerLayer I n).IsFinitePresentation := by
  have := closedModule_isFinitePresentation (I^n)
  have := closedModule_isFinitePresentation (I^(n+1))
  let : (closedModule (I^(n+1))).IsQuasicoherent :=
    (SheafOfModules.IsFinitePresentation.exists_quasicoherentData
      (closedModule (I^(n+1)))).choose.isQuasicoherent
  exact PiExponent.CoherentCokernels.cokernel_isFinitePresentation (powerMap I n)

theorem powerModule_eventually_isZero [IsNoetherian X] (I : X.IdealSheafData)
    (hI : I.support = ⊤) : ∃ n : ℕ, 0 < n ∧ IsZero (closedModule (I^n)) := by
  obtain ⟨n, hn, he⟩ := Geometry.exists_pos_pow_eq_bot_of_fullSupport I hI
  exact ⟨n,hn,he ▸ closedModule_bot_isZero⟩

end
end PiExponentSeshadri.IdealModule

end OAI
end Source0496

-- Source: OAI/NumberTheory/PiExponent/LocalAlgebra/IdealPowerAnnihilator.lean
section Source0497
/-
Modification notice for the LogTwo project.
Derived from openai/math (Apache-2.0), revision adc7f1241b42e322a6451854ab7e4b4c146bf78a.
Original source: lean/OAI/NumberTheory/PiExponent/LocalAlgebra/IdealPowerAnnihilator.lean
Changes: Convert module/import declarations to the Lean 4.34 public module format.
See ../THIRD_PARTY_NOTICES.txt for provenance and the recorded changes.
-/

namespace OAI

namespace PiExponentSeshadri.IdealModule
noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite
open PiExponentSeshadri.Geometry
variable {X : Scheme.{0}}

theorem hom_ext_affine {M N : X.Modules} {f g : M ⟶ N}
    (h : ∀ U : X.affineOpens, f.app U.1 = g.app U.1) : f = g := by
  let F := SheafOfModules.toSheaf X.ringCatSheaf
  apply F.map_injective
  apply Sheaf.hom_ext
  apply TopCat.Sheaf.hom_ext _ _ (show Opens.IsBasis
    (Set.range (fun U : X.affineOpens => U.1)) by simpa using X.isBasis_affineOpens)
  intro U
  ext x
  exact ConcreteCategory.congr_hom (h U) x

lemma restriction_mem_ideal (I : X.IdealSheafData) (r : Γ(X,⊤))
    (hr : I.subschemeι.appTop r = 0) (U : X.affineOpens) :
    restrictScalar X U.1 r ∈ I.ideal U := by
  rw [← I.ker_subschemeι_app U, RingHom.mem_ker]
  unfold restrictScalar
  have h := congrArg (fun f => f r) (I.subschemeι.naturality
    (homOfLE (show U.1 ≤ ⊤ from le_top)).op)
  change I.subschemeι.app U.1 (X.presheaf.map (homOfLE le_top).op r) = _ at h
  rw [CommRingCat.comp_apply] at h
  exact h.trans ((congrArg _ hr).trans (map_zero _))

lemma smul_closedInclusion_structureMap_eq_zero (I : X.IdealSheafData) (n : ℕ)
    (r : Γ(X,⊤)) (hr : I.subschemeι.appTop r = 0) :
    (r • closedInclusion (I^n)) ≫ structureMap (I^(n+1)).subschemeι = 0 := by
  apply hom_ext_affine
  intro U
  ext x
  change (I^(n+1)).subschemeι.app U.1
    (restrictScalar X U.1 r * (show Γ(X,U.1) from (closedInclusion (I^n)).app U.1 x)) = 0
  apply RingHom.mem_ker.mp
  rw [(I^(n+1)).ker_subschemeι_app U]
  change restrictScalar X U.1 r * (show Γ(X,U.1) from (closedInclusion (I^n)).app U.1 x) ∈
    I.ideal U ^ (n+1)
  rw [pow_succ']
  apply Ideal.mul_mem_mul (restriction_mem_ideal I r hr U)
  change (closedInclusion (I^n)).app U.1 x ∈ (I^n).ideal U
  rw [← closed_image (I^n) U]
  exact ⟨x,rfl⟩

def multiplyToNextPower (I : X.IdealSheafData) (n : ℕ)
    (r : Γ(X,⊤)) (hr : I.subschemeι.appTop r = 0) :
    closedModule (I^n) ⟶ closedModule (I^(n+1)) :=
  kernel.lift (structureMap (I^(n+1)).subschemeι) (r • closedInclusion (I^n))
    (smul_closedInclusion_structureMap_eq_zero I n r hr)

@[reassoc (attr := simp)] lemma multiplyToNextPower_inclusion (I : X.IdealSheafData) (n : ℕ)
    (r : Γ(X,⊤)) (hr : I.subschemeι.appTop r = 0) :
    multiplyToNextPower I n r hr ≫ closedInclusion (I^(n+1)) = r • closedInclusion (I^n) :=
  kernel.lift_ι _ _ _

lemma multiplyToNextPower_powerMap (I : X.IdealSheafData) (n : ℕ)
    (r : Γ(X,⊤)) (hr : I.subschemeι.appTop r = 0) :
    multiplyToNextPower I n r hr ≫ powerMap I n = r • 𝟙 (closedModule (I^n)) := by
  apply (cancel_mono (closedInclusion (I^n))).mp
  rw [Category.assoc, show powerMap I n ≫ closedInclusion (I^n) =
    closedInclusion (I^(n+1)) from closedMap_inclusion _]
  rw [multiplyToNextPower_inclusion]
  ext U x
  change restrictScalar X U r * (show Γ(X,U) from (closedInclusion (I^n)).app U x) =
    (closedInclusion (I^n)).app U (restrictScalar X U r • x)
  exact ((closedInclusion (I^n)).app_smul _ x).symm

theorem powerLayer_smul_id_eq_zero (I : X.IdealSheafData) (n : ℕ)
    (r : Γ(X,⊤)) (hr : I.subschemeι.appTop r = 0) :
    r • 𝟙 (powerLayer I n) = 0 := by
  apply (cancel_epi (cokernel.π (powerMap I n))).mp
  have h : (r • 𝟙 (closedModule (I^n))) ≫ cokernel.π (powerMap I n) = 0 := by
    rw [← multiplyToNextPower_powerMap I n r hr, Category.assoc, cokernel.condition,
      Limits.comp_zero]
  calc
    _ = (r • 𝟙 (closedModule (I^n))) ≫ cokernel.π (powerMap I n) := by
      ext U x
      exact ((cokernel.π (powerMap I n)).app_smul _ x).symm
    _ = 0 := h
    _ = _ := Limits.comp_zero.symm
end
end PiExponentSeshadri.IdealModule

end OAI
end Source0497

-- Source: OAI/NumberTheory/PiExponent/LocalAlgebra/PresentedIdealIso.lean
section Source0498
/-
Modification notice for the LogTwo project.
Derived from openai/math (Apache-2.0), revision adc7f1241b42e322a6451854ab7e4b4c146bf78a.
Original source: lean/OAI/NumberTheory/PiExponent/LocalAlgebra/PresentedIdealIso.lean
Changes: Convert module/import declarations to the Lean 4.34 public module format.
See ../THIRD_PARTY_NOTICES.txt for provenance and the recorded changes.
-/

namespace OAI

noncomputable section
namespace PiExponent.PresentedIdealIso
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite
open PiExponentSeshadri.Geometry PiExponentSeshadri.IdealModule
open PiExponent.SectionImageIdeal
variable {X Y : Scheme.{0}}

theorem imageIdealSheaf_eq_comap
    (I : X.IdealSheafData) (f : Y ⟶ X)
    (J : LineBundle Y) (ι : J.sheaf ⟶ structureSheaf Y)
    [J.sheaf.IsQuasicoherent] (hJ : PresentsPullbackIdeal I f J ι) :
    imageIdealSheaf ι = I.comap f := by
  classical
  have hlocal (y : Y) : ∃ U : Y.affineOpens, y ∈ U.1 ∧
      ∃ V : X.affineOpens, U.1 ≤ f ⁻¹ᵁ V.1 := by
    obtain ⟨V, hV, hyV, -⟩ := exists_isAffineOpen_mem_and_subset
      (show f y ∈ (⊤ : X.Opens) from trivial)
    obtain ⟨U, hU, hyU, hUV⟩ := exists_isAffineOpen_mem_and_subset
      (show y ∈ f ⁻¹ᵁ V from hyV)
    exact ⟨⟨U, hU⟩, hyU, ⟨V, hV⟩, hUV⟩
  choose U hy V hUV using hlocal
  apply Scheme.IdealSheafData.ext_of_iSup_eq_top U
  · apply top_unique
    intro y _
    exact Opens.mem_iSup.mpr ⟨y, hy y⟩
  · intro y
    exact (hJ.2 (U y) (V y) (hUV y)).trans
      (PiExponentSeshadri.IdealPullback.comap_ideal I f (U y) (V y) (hUV y)).symm

theorem presented_range_eq
    (I : X.IdealSheafData) (f : Y ⟶ X)
    (J : LineBundle Y) (ι : J.sheaf ⟶ structureSheaf Y)
    (hJ : PresentsPullbackIdeal I f J ι) (U : Y.affineOpens) :
    (ι.val.app (op U.1)).hom.range = (I.comap f).ideal U := by
  let := GeometrySupport.LineBundleCoherent.lineBundle_isFinitePresentation J
  let : J.sheaf.IsQuasicoherent :=
    (SheafOfModules.IsFinitePresentation.exists_quasicoherentData J.sheaf).choose.isQuasicoherent
  exact congrArg (fun K : Y.IdealSheafData => K.ideal U)
    (imageIdealSheaf_eq_comap I f J ι hJ)

theorem inclusion_structureMap_zero
    (I : X.IdealSheafData) (f : Y ⟶ X)
    (J : LineBundle Y) (ι : J.sheaf ⟶ structureSheaf Y)
    (hJ : PresentsPullbackIdeal I f J ι) :
    ι ≫ structureMap (I.comap f).subschemeι = 0 := by
  apply hom_ext_affine
  intro U
  ext x
  change (I.comap f).subschemeι.app U.1 (ι.app U.1 x) = 0
  apply RingHom.mem_ker.mp
  rw [(I.comap f).ker_subschemeι_app U, ← presented_range_eq I f J ι hJ U]
  exact ⟨x, rfl⟩

def toIdealModule
    (I : X.IdealSheafData) (f : Y ⟶ X)
    (J : LineBundle Y) (ι : J.sheaf ⟶ structureSheaf Y)
    (hJ : PresentsPullbackIdeal I f J ι) : J.sheaf ⟶ closedModule (I.comap f) :=
  kernel.lift (structureMap (I.comap f).subschemeι) ι
    (inclusion_structureMap_zero I f J ι hJ)

@[reassoc (attr := simp)] theorem toIdealModule_inclusion
    (I : X.IdealSheafData) (f : Y ⟶ X)
    (J : LineBundle Y) (ι : J.sheaf ⟶ structureSheaf Y)
    (hJ : PresentsPullbackIdeal I f J ι) :
    toIdealModule I f J ι hJ ≫ closedInclusion (I.comap f) = ι :=
  kernel.lift_ι _ _ _

instance toIdealModule_isIso
    (I : X.IdealSheafData) (f : Y ⟶ X)
    (J : LineBundle Y) (ι : J.sheaf ⟶ structureSheaf Y)
    (hJ : PresentsPullbackIdeal I f J ι) : IsIso (toIdealModule I f J ι hJ) := by
  have : Mono ι := hJ.1
  let K := I.comap f
  let t := toIdealModule I f J ι hJ
  let κ := closedInclusion K
  apply isIso_of_affine_app
  intro U
  have hιinj : Function.Injective (ι.val.app (op U.1)) := by
    have : Mono ι.val := inferInstanceAs (Mono ((Scheme.Modules.toPresheafOfModules Y).map ι))
    exact PresheafOfModules.injective_of_mono ι.val (op U.1)
  have hκinj : Function.Injective (κ.val.app (op U.1)) := by
    have : Mono κ.val := inferInstanceAs (Mono ((Scheme.Modules.toPresheafOfModules Y).map κ))
    exact PresheafOfModules.injective_of_mono κ.val (op U.1)
  have hfac (m : Γ(J.sheaf, U.1)) : κ.app U.1 (t.app U.1 m) = ι.app U.1 m :=
    congrArg (fun a : J.sheaf ⟶ structureSheaf Y => a.app U.1 m)
      (toIdealModule_inclusion I f J ι hJ)
  apply (ConcreteCategory.isIso_iff_bijective _).mpr
  constructor
  · intro a b hab
    apply hιinj
    exact (hfac a).symm.trans ((congrArg (κ.app U.1) hab).trans (hfac b))
  · intro z
    have hz : κ.app U.1 z ∈ K.ideal U := by
      rw [← closed_image K U]
      exact ⟨z, rfl⟩
    rw [← presented_range_eq I f J ι hJ U] at hz
    obtain ⟨m, hm⟩ := hz
    refine ⟨m, hκinj ?_⟩
    exact (hfac m).trans hm

def iso
    (I : X.IdealSheafData) (f : Y ⟶ X)
    (J₁ J₂ : LineBundle Y)
    (ι₁ : J₁.sheaf ⟶ structureSheaf Y) (ι₂ : J₂.sheaf ⟶ structureSheaf Y)
    (h₁ : PresentsPullbackIdeal I f J₁ ι₁)
    (h₂ : PresentsPullbackIdeal I f J₂ ι₂) : J₁.sheaf ≅ J₂.sheaf :=
  asIso (toIdealModule I f J₁ ι₁ h₁) ≪≫ (asIso (toIdealModule I f J₂ ι₂ h₂)).symm

@[reassoc (attr := simp)] theorem iso_hom_inclusion
    (I : X.IdealSheafData) (f : Y ⟶ X)
    (J₁ J₂ : LineBundle Y)
    (ι₁ : J₁.sheaf ⟶ structureSheaf Y) (ι₂ : J₂.sheaf ⟶ structureSheaf Y)
    (h₁ : PresentsPullbackIdeal I f J₁ ι₁)
    (h₂ : PresentsPullbackIdeal I f J₂ ι₂) :
    (iso I f J₁ J₂ ι₁ ι₂ h₁ h₂).hom ≫ ι₂ = ι₁ := by
  have h₂inv : (asIso (toIdealModule I f J₂ ι₂ h₂)).inv ≫ ι₂ =
      closedInclusion (I.comap f) := by
    have hh := congrArg
      (fun a : J₂.sheaf ⟶ structureSheaf Y =>
        (asIso (toIdealModule I f J₂ ι₂ h₂)).inv ≫ a)
      (toIdealModule_inclusion I f J₂ ι₂ h₂)
    exact hh.symm.trans (Iso.inv_hom_id_assoc _ _)
  change toIdealModule I f J₁ ι₁ h₁ ≫
    (asIso (toIdealModule I f J₂ ι₂ h₂)).inv ≫ ι₂ = ι₁
  rw [h₂inv]
  exact toIdealModule_inclusion I f J₁ ι₁ h₁

end PiExponent.PresentedIdealIso

end

end OAI
end Source0498

-- Source: LogTwo/Geometry/SectionIdealBridge.lean
section Source0499
/-
Modification notice for the LogTwo project.
Adapted from openai/math (Apache-2.0), revision adc7f1241b42e322a6451854ab7e4b4c146bf78a.
Changes: Extract generic zero-ideal, section-divisor and inverse-line-bundle degree arguments.
See ../THIRD_PARTY_NOTICES.txt for provenance and the recorded changes.
-/

/-! Generic zero-ideal, section-divisor and Euler-degree bridges adapted from
openai/math Ampleness/ExceptionalCurveDegree.lean (Apache-2.0).
Only scheme-generic statements are extracted; no fixed-Y contact theorem.
See THIRD_PARTY_NOTICES.txt. -/
namespace LogTwo.Geometry.SectionIdealBridge
noncomputable section
open OAI AlgebraicGeometry CategoryTheory TopologicalSpace Opposite
open OAI.PiExponent PiExponentSeshadri.Geometry PiExponentSeshadri.Frames
open PiExponent.SectionZeroIdeal PiExponent.SectionImageIdeal
variable {X Y : Scheme.{0}}

def inverseSection (J : LineBundle Y) (ι : J.sheaf ⟶ O Y) :
    GlobalSections Y J.inverse.sheaf :=
  (lineTensorInverseIso J).inv ≫ tensorInclusion J J.inverse ι

theorem inverseSection_zeroIdeal (J : LineBundle Y) (ι : J.sheaf ⟶ O Y)
    [J.sheaf.IsQuasicoherent] :
    zeroIdeal J.inverse (inverseSection J ι) = imageIdealSheaf ι := by
  classical
  have hc (y : Y) := common_affine_frames J J.inverse y
  choose U hy e f using hc
  let e' y := (e y).some
  let f' y := (f y).some
  apply Scheme.IdealSheafData.ext_of_iSup_eq_top U
  · apply top_unique
    intro y _
    exact Opens.mem_iSup.mpr ⟨y, hy y⟩
  · intro y
    let V := U y
    let a := Scheme.Modules.restrictUnitIso V.1.ι
    let b := tensorFrame J J.inverse V.1 (e' y) (f' y)
    rw [zeroIdeal_on_frame J.inverse (inverseSection J ι) V (f' y),
      imageIdealSheaf_on_frame ι V (e' y)]
    change Ideal.span {(affineMapCoefficient V a (f' y)
      ((lineTensorInverseIso J).inv ≫ tensorInclusion J J.inverse ι))} = _
    erw [affineMapCoefficient_comp V a b (f' y),
      ← Ideal.span_singleton_mul_span_singleton]
    have hu : IsUnit (affineMapCoefficient V a b (lineTensorInverseIso J).inv) := by
      apply IsUnit.map V.1.topIso.hom.hom
      exact (end_isIso_iff _).mp
        (a.symm ≪≫ ((Scheme.Modules.restrictFunctor V.1.ι).mapIso
          (lineTensorInverseIso J)).symm ≪≫ b).isIso_hom
    rw [Ideal.span_singleton_eq_top.mpr hu, Ideal.top_mul]
    exact tensor_inclusion_ideal J J.inverse ι V (e' y) (f' y)

theorem inverseSection_zeroIdeal_eq_comap
    (I : X.IdealSheafData) (π : Y ⟶ X)
    (J : LineBundle Y) (ι : J.sheaf ⟶ O Y)
    (hJ : PresentsPullbackIdeal I π J ι) :
    zeroIdeal J.inverse (inverseSection J ι) = I.comap π := by
  let := GeometrySupport.LineBundleCoherent.lineBundle_isFinitePresentation J
  rw [inverseSection_zeroIdeal, PresentedIdealIso.imageIdealSheaf_eq_comap I π J ι hJ]

theorem zeroIdeal_pullback (L : LineBundle X) (s : GlobalSections X L.sheaf)
    (f : Y ⟶ X) :
    zeroIdeal (L.pullback f) (pullbackSection f s) = (zeroIdeal L s).comap f := by
  classical
  have hlocal (y : Y) : ∃ V : Y.affineOpens, y ∈ V.1 ∧
      (zeroIdeal (L.pullback f) (pullbackSection f s)).ideal V =
        ((zeroIdeal L s).comap f).ideal V := by
    obtain ⟨U, hU, ⟨e⟩⟩ := PiExponentSeshadri.InvertibleLocal.affine_frame L (f y)
    obtain ⟨V, hV, hyV, hVU⟩ := exists_isAffineOpen_mem_and_subset
      (show y ∈ f ⁻¹ᵁ U.1 from hU)
    let g := f.resLE U.1 V hVU
    obtain ⟨eF, he⟩ := exists_restricted_pullback_frame_all_of_factor f U.1 V g
      (Scheme.Hom.resLE_comp_ι f hVU).symm e
    refine ⟨⟨V, hV⟩, hyV, ?_⟩
    rw [zeroIdeal_on_frame (L.pullback f) (pullbackSection f s) ⟨V, hV⟩ eF,
      PiExponentSeshadri.IdealPullback.comap_ideal (zeroIdeal L s) f ⟨V, hV⟩ U hVU,
      zeroIdeal_on_frame L s U e, Ideal.map_span, Set.image_singleton]
    erw [he s]
    congr 2
    change V.topIso.hom ((f.resLE U.1 V hVU).appTop _) = _
    have ht : (f.resLE U.1 V hVU).appTop = U.1.topIso.hom ≫
        f.appLE U.1 V hVU ≫ V.topIso.inv := by
      simpa only [Scheme.Hom.appTop, Scheme.Hom.appLE_eq_app] using!
        (Scheme.Hom.resLE_app_top f hVU)
    rw [ht]
    simp only [CommRingCat.comp_apply, Iso.inv_hom_id_apply]
  choose V hy hV using hlocal
  apply Scheme.IdealSheafData.ext_of_iSup_eq_top V
  · apply top_unique
    intro y _
    exact Opens.mem_iSup.mpr ⟨y, hy y⟩
  · exact hV

theorem zeroIdeal_zero (L : LineBundle X) : zeroIdeal L 0 = ⊥ := by
  classical
  choose U hx e using fun x : X => PiExponentSeshadri.InvertibleLocal.affine_frame L x
  apply Scheme.IdealSheafData.ext_of_iSup_eq_top U
  · apply top_unique
    intro x _
    exact Opens.mem_iSup.mpr ⟨x, hx x⟩
  · intro x
    rw [zeroIdeal_on_frame L 0 (U x) (e x).some]
    erw [restrictSection_zero, coefficient_zero, map_zero, Ideal.span_singleton_zero]
    rfl

theorem pullback_inverseSection_zeroIdeal
    (I : X.IdealSheafData) (π : Y ⟶ X)
    (J : LineBundle Y) (ι : J.sheaf ⟶ O Y)
    (hJ : PresentsPullbackIdeal I π J ι)
    {Z : Scheme.{0}} (g : Z ⟶ Y) :
    zeroIdeal (J.inverse.pullback g) (pullbackSection g (inverseSection J ι)) =
      I.comap (g ≫ π) := by
  rw [zeroIdeal_pullback, inverseSection_zeroIdeal_eq_comap I π J ι hJ,
    Scheme.IdealSheafData.comap_comp]

theorem pullback_inverseSection_ne_zero
    (I : X.IdealSheafData) (π : Y ⟶ X)
    (J : LineBundle Y) (ι : J.sheaf ⟶ O Y)
    (hJ : PresentsPullbackIdeal I π J ι)
    {Z : Scheme.{0}} (g : Z ⟶ Y) (hg : I.comap (g ≫ π) ≠ ⊥) :
    pullbackSection g (inverseSection J ι) ≠ 0 := by
  intro hs
  have h := pullback_inverseSection_zeroIdeal I π J ι hJ g
  rw [hs] at h
  exact hg (h.symm.trans (zeroIdeal_zero _))

theorem zeroIdeal_spec_top {A : Type} [CommRing A]
    (L : LineBundle (Spec (CommRingCat.of A)))
    (s : GlobalSections _ L.sheaf) (e : L.sheaf ≅ O (Spec (CommRingCat.of A))) :
    ((zeroIdeal L s).ideal ⟨⊤, isAffineOpen_top _⟩).map
      (Scheme.ΓSpecIso (CommRingCat.of A)).hom.hom =
        Ideal.span {LocalSectionOrder.localCoefficient e s} := by
  change (imageIdeal (L.dualSection s) ⊤).map _ = _
  rw [imageIdeal_top_of_frame (L.dualSection s)
    (InverseFrames.pairingFrame (lineTensorInverseIso L) e)]
  change (Ideal.span {endValue ((InverseFrames.pairingFrame (lineTensorInverseIso L) e).inv ≫
    InverseFrames.dualMap (lineTensorInverseIso L) s)}).map _ = _
  erw [InverseFrames.dualMap_coefficient]
  rw [Ideal.map_span, Set.image_singleton]
  rfl

def localIdeal {A : Type} [CommRing A] (I : X.IdealSheafData)
    (q : Spec (CommRingCat.of A) ⟶ X) : Ideal A :=
  ((I.comap q).ideal ⟨⊤, isAffineOpen_top _⟩).map
    (Scheme.ΓSpecIso (CommRingCat.of A)).hom.hom

section Curve
open CurveNormalizationModel CurveValuationCenter CurvePlaceCenter
open LocalSectionOrder
variable {E : Type} [Field E] [Algebra ℂ E]
variable (f : E) (hf : Transcendental ℂ f)
variable [FiniteDimensional (IntermediateField.adjoin ℂ {f}) E]

theorem divisor_eq_localIdeal_length
    (L : LineBundle (parameterCurve f hf))
    (s : GlobalSections _ L.sheaf) (hs : s ≠ 0) (p : NormalizedPlace ℂ E) :
    CurvePlaceSectionDivisor.divisor f hf L s hs p =
      (Module.length (PlaceValuationRing.ring p)
        ((PlaceValuationRing.ring p) ⧸ localIdeal (zeroIdeal L s) (centerMorphism f hf p))).toNat := by
  let q := centerMorphism f hf p
  obtain ⟨e, he⟩ := LocalPullbackSectionOrder.exists_frame_coefficient_germ q L
  have hn : localCoefficient e (pullbackSection q s) ≠ 0 := by
    rw [he s]
    apply (map_ne_zero_iff _
      (ConcreteCategory.bijective_of_isIso (Scheme.stalkClosedPointTo q)).injective).mpr
    exact SectionZeroStalk.sectionGerm_ne_zero L s hs
      (CurveSectionDegree.affineFrameAt L (q (IsLocalRing.closedPoint _))).openSet
      (CurveSectionDegree.affineFrameAt L (q (IsLocalRing.closedPoint _))).frame _
      (CurveSectionDegree.affineFrameAt L (q (IsLocalRing.closedPoint _))).mem
  have hi : localIdeal (zeroIdeal L s) q =
      Ideal.span {localCoefficient e (pullbackSection q s)} := by
    unfold localIdeal
    rw [← zeroIdeal_pullback L s q]
    exact zeroIdeal_spec_top (L.pullback q) (pullbackSection q s) e
  rw [CurvePlaceSectionOrder.divisor_eq_local_order f hf L s hs p e, hi,
    CurveLocalOrder.length_quotient_span_eq_addVal hn]
  rfl

variable (I : X.IdealSheafData) (π : Y ⟶ X)
variable (J : LineBundle Y) (ι : J.sheaf ⟶ O Y)
variable (hJ : PresentsPullbackIdeal I π J ι)
variable (g : parameterCurve f hf ⟶ Y) (hg : I.comap (g ≫ π) ≠ ⊥)

def idealDivisor : NormalizedPlace ℂ E →₀ ℕ :=
  CurvePlaceSectionDivisor.divisor f hf (J.inverse.pullback g)
    (pullbackSection g (inverseSection J ι))
    (pullback_inverseSection_ne_zero I π J ι hJ g hg)

theorem idealDivisor_apply (p : NormalizedPlace ℂ E) :
    idealDivisor f hf I π J ι hJ g hg p =
      (Module.length (PlaceValuationRing.ring p)
        ((PlaceValuationRing.ring p) ⧸
          localIdeal I (centerMorphism f hf p ≫ g ≫ π))).toNat := by
  erw [idealDivisor, divisor_eq_localIdeal_length]
  have hi : localIdeal
      (zeroIdeal (J.inverse.pullback g) (pullbackSection g (inverseSection J ι)))
        (centerMorphism f hf p) = localIdeal I (centerMorphism f hf p ≫ g ≫ π) := by
    simp only [localIdeal, pullback_inverseSection_zeroIdeal I π J ι hJ g,
      Scheme.IdealSheafData.comap_comp]
  rw [hi]

theorem degree_eq_neg_idealDivisor_sum :
    eulerCharacteristic (parameterCurveStructureMap f hf) 1 (J.pullback g).sheaf -
      eulerCharacteristic (parameterCurveStructureMap f hf) 1
        (structureSheaf (parameterCurve f hf)) =
      -(idealDivisor f hf I π J ι hJ g hg).sum (fun _ n => (n : ℤ)) := by
  have hd := CurvePlaceSectionDivisor.degree_eq_euler_difference_full f hf
    (J.inverse.pullback g) (pullbackSection g (inverseSection J ι))
    (pullback_inverseSection_ne_zero I π J ι hJ g hg)
  have ht := parameterCurve_tensor_euler_add f hf (J.pullback g) (J.inverse.pullback g)
  let e : ((J.pullback g).tensor (J.inverse.pullback g)).sheaf ≅
      structureSheaf (parameterCurve f hf) :=
    (PiExponentSeshadri.PullbackTensor.iso g J J.inverse).symm ≪≫
      (Scheme.Modules.pullback g).mapIso (lineTensorInverseIso J) ≪≫ pullbackUnitIso g
  have he := eulerCharacteristic_iso (parameterCurveStructureMap f hf) e 1
  change _ = -(CurvePlaceSectionDivisor.divisor f hf (J.inverse.pullback g)
    (pullbackSection g (inverseSection J ι)) _).sum (fun _ n => (n : ℤ))
  omega

end Curve
end
end LogTwo.Geometry.SectionIdealBridge
end Source0499

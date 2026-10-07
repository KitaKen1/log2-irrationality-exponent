/- Generated rc4 checkpoint for LogTwo.
Modified from the reduced edition: new imports, separate module compilation,
and synchronous elaboration. Original source blocks and notices are retained.
See ../../../THIRD_PARTY_NOTICES.txt and ../../reduction.json.
-/
module
public import Batteries.Logic
public import Lean.Elab.Tactic.Omega
public import Mathlib.Algebra.Category.ModuleCat.Ext.HasExt
public import Mathlib.Algebra.Group.ForwardDiff
public import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
public import Mathlib.Algebra.Module.Submodule.Union
public import Mathlib.Analysis.Complex.Polynomial.Basic
public import Mathlib.Analysis.Polynomial.Basic
public import Mathlib.Data.Sym.Card
public import Mathlib.RingTheory.Flat.Localization
public import Mathlib.RingTheory.Ideal.AssociatedPrime.Localization
public import Mathlib.RingTheory.KrullDimension.Regular
public import Mathlib.RingTheory.LocalRing.Quotient
public import Mathlib.RingTheory.MvPolynomial.Homogeneous
public import Mathlib.RingTheory.OrderOfVanishing.Noetherian
public import Mathlib.RingTheory.PowerSeries.WellKnown
public import Mathlib.Tactic
@[expose] public section
set_option Elab.async false

-- Source: OAI/NumberTheory/PiExponent/LocalAlgebra/RegularDegreePositivity.lean
section Source0150
-- Modified in this edition: unused plain lemmas removed; see reduction.json.
/-
Modification notice for the LogTwo project.
Derived from openai/math (Apache-2.0), revision adc7f1241b42e322a6451854ab7e4b4c146bf78a.
Original source: lean/OAI/NumberTheory/PiExponent/LocalAlgebra/RegularDegreePositivity.lean
Changes: Convert module/import declarations to the Lean 4.34 public module format.
See ../THIRD_PARTY_NOTICES.txt for provenance and the recorded changes.
-/

namespace OAI

namespace PiExponentSiegel.W20

open scoped BigOperators

section Ring

variable {R : Type*} [CommRing R]

theorem regular_sequence_ideal_ne_top (rs : List R)
    (hreg : RingTheory.Sequence.IsRegular R rs) : Ideal.ofList rs ≠ ⊤ := by
  intro htop
  apply hreg.top_ne_smul
  have hmul : (Ideal.ofList rs • (⊤ : Submodule R R)) = Ideal.ofList rs :=
    (Ideal.ofList rs).mul_top
  rw [hmul, htop]

theorem regular_sequence_term_not_isUnit (rs : List R)
    (hreg : RingTheory.Sequence.IsRegular R rs) (i : Fin rs.length) :
    ¬ IsUnit rs[i] := by
  intro hunit
  apply regular_sequence_ideal_ne_top rs hreg
  exact (Ideal.ofList rs).eq_top_of_isUnit_mem
    (Ideal.subset_span (List.getElem_mem i.isLt)) hunit

theorem regular_sequence_term_ne_zero (rs : List R)
    (hreg : RingTheory.Sequence.IsRegular R rs) (i : Fin rs.length) : rs[i] ≠ 0 := by
  let I : Ideal R := Ideal.ofList (rs.take i.val)
  have hle : I ≤ Ideal.ofList rs :=
    Ideal.span_mono (List.take_subset i.val rs)
  have hproper : I ≠ ⊤ := ne_top_of_le_ne_top
    (regular_sequence_ideal_ne_top rs hreg) hle
  let : Nontrivial (R ⧸ I) := Ideal.Quotient.nontrivial_iff.mpr hproper
  have hsmul := hreg.toIsWeaklyRegular.regular_mod_prev i.val i.isLt
  have hmul : (Ideal.ofList (rs.take i.val) • (⊤ : Submodule R R)) = I := I.mul_top
  rw [hmul] at hsmul
  intro hz
  have hz' : rs[i.val] = 0 := by simpa only [Fin.getElem_fin] using hz
  have hsmulzero : IsSMulRegular (R ⧸ I) (0 : R) := hz' ▸ hsmul
  exact IsSMulRegular.not_zero hsmulzero

end Ring

variable {k σ : Type*} [Field k]

theorem regular_homogeneous_degrees_pos
    (rs : List (MvPolynomial σ k)) (degrees : Fin rs.length → ℕ)
    (hhom : ∀ i : Fin rs.length, rs[i].IsHomogeneous (degrees i))
    (hreg : RingTheory.Sequence.IsRegular (MvPolynomial σ k) rs) :
    ∀ i, 0 < degrees i := by
  intro i
  by_contra hpos
  have hzero : degrees i = 0 := Nat.eq_zero_of_not_pos hpos
  have hhomzero : rs[i].IsHomogeneous 0 := by simpa only [hzero] using hhom i
  have hdegzero : (rs[i]).totalDegree = 0 :=
    (MvPolynomial.totalDegree_zero_iff_isHomogeneous (σ := σ)).mpr hhomzero
  have hconstant : rs[i] = MvPolynomial.C ((rs[i]).coeff 0) :=
    MvPolynomial.totalDegree_eq_zero_iff_eq_C.mp hdegzero
  have hcoeff : (rs[i]).coeff 0 ≠ 0 := by
    intro hz
    apply regular_sequence_term_ne_zero rs hreg i
    rw [hconstant, hz, map_zero]
  apply regular_sequence_term_not_isUnit rs hreg i
  rw [hconstant]
  exact (isUnit_iff_ne_zero.mpr hcoeff).map MvPolynomial.C

end PiExponentSiegel.W20

end OAI
end Source0150

-- Source: OAI/NumberTheory/PiExponent/Ampleness/LocalHomogeneousDegrees.lean
section Source0151
/-
Modification notice for the LogTwo project.
Derived from openai/math (Apache-2.0), revision adc7f1241b42e322a6451854ab7e4b4c146bf78a.
Original source: lean/OAI/NumberTheory/PiExponent/Ampleness/LocalHomogeneousDegrees.lean
Changes: Convert module/import declarations to the Lean 4.34 public module format.
See ../THIRD_PARTY_NOTICES.txt for provenance and the recorded changes.
-/

namespace OAI

namespace PiExponentJets.W22

variable {k σ : Type*} [Field k]

theorem homogeneous_degrees_pos_of_local_regular
    (T : Ideal (MvPolynomial σ k)) [T.IsPrime]
    (gs : List (MvPolynomial σ k)) (degrees : Fin gs.length → ℕ)
    (hhom : ∀ i : Fin gs.length, gs[i].IsHomogeneous (degrees i))
    (hreg : RingTheory.Sequence.IsRegular (Localization.AtPrime T)
      (gs.map (algebraMap (MvPolynomial σ k) (Localization.AtPrime T)))) :
    ∀ i, 0 < degrees i := by
  intro i
  let μ := algebraMap (MvPolynomial σ k) (Localization.AtPrime T)
  let imap : Fin (gs.map μ).length := ⟨i.val, by simpa only [List.length_map] using i.isLt⟩
  have hn : μ gs[i] ≠ 0 := by
    simpa only [List.getElem_map, Fin.getElem_fin] using
      PiExponentSiegel.W20.regular_sequence_term_ne_zero (gs.map μ) hreg imap
  have hu : ¬ IsUnit (μ gs[i]) := by
    simpa only [List.getElem_map, Fin.getElem_fin] using
      PiExponentSiegel.W20.regular_sequence_term_not_isUnit (gs.map μ) hreg imap
  by_contra hpos
  have hd : degrees i = 0 := Nat.eq_zero_of_not_pos hpos
  have hh : gs[i].IsHomogeneous 0 := by simpa only [hd] using hhom i
  have hg : gs[i] = MvPolynomial.C ((gs[i]).coeff 0) :=
    MvPolynomial.totalDegree_eq_zero_iff_eq_C.mp
      ((MvPolynomial.totalDegree_zero_iff_isHomogeneous (σ := σ)).mpr hh)
  have hc : (gs[i]).coeff 0 ≠ 0 := by
    intro hc
    apply hn
    rw [hg, hc, map_zero, map_zero]
  apply hu
  rw [hg]
  exact ((isUnit_iff_ne_zero.mpr hc).map MvPolynomial.C).map μ

end PiExponentJets.W22

end OAI
end Source0151

-- Source: OAI/NumberTheory/PiExponent/LocalAlgebra/GenericCombination.lean
section Source0152
-- Modified in this edition: unused plain lemmas removed; see reduction.json.
/-
Modification notice for the LogTwo project.
Derived from openai/math (Apache-2.0), revision adc7f1241b42e322a6451854ab7e4b4c146bf78a.
Original source: lean/OAI/NumberTheory/PiExponent/LocalAlgebra/GenericCombination.lean
Changes: Convert module/import declarations to the Lean 4.34 public module format.
See ../THIRD_PARTY_NOTICES.txt for provenance and the recorded changes.
-/

namespace OAI

namespace PiExponentSiegel.W20

variable {K M I J : Type*} [Field K] [Infinite K]
  [AddCommGroup M] [Module K M] [Finite I]

theorem exists_linearCombination_avoiding_submodules
    (g : J → M) (P : I → Submodule K M)
    (h : ∀ i, ¬ Submodule.span K (Set.range g) ≤ P i) :
    ∃ c : J →₀ K, ∀ i, Finsupp.linearCombination K g c ∉ P i := by
  let bad : I → Submodule K (J →₀ K) :=
    fun i => (P i).comap (Finsupp.linearCombination K g)
  have hbad : ∀ i, bad i ≠ ⊤ := by
    intro i hi
    apply h i
    apply Submodule.span_le.mpr
    rintro _ ⟨j, rfl⟩
    have hc : Finsupp.single j (1 : K) ∈ bad i := by
      rw [hi]
      trivial
    change Finsupp.linearCombination K g (Finsupp.single j 1) ∈ P i at hc
    simpa using hc
  obtain ⟨c, hc⟩ := Submodule.exists_forall_notMem_of_forall_ne_top bad hbad
  exact ⟨c, hc⟩

variable {R : Type*} [CommRing R] [Algebra K R]

theorem exists_linearCombination_avoiding_ideals
    (g : J → R) (P : I → Ideal R)
    (h : ∀ i, ¬ Ideal.span (Set.range g) ≤ P i) :
    ∃ c : J →₀ K, ∀ i, Finsupp.linearCombination K g c ∉ P i := by
  apply exists_linearCombination_avoiding_submodules g
    (fun i => (P i).restrictScalars K)
  intro i hi
  apply h i
  apply Ideal.span_le.mpr
  intro x hx
  exact hi (Submodule.subset_span hx)

theorem exists_linearCombination_avoiding_primes_below_radical
    (g : J → R) (m : Ideal R)
    (hgen : (Ideal.span (Set.range g)).radical = m)
    (P : I → Ideal R) (hprime : ∀ i, (P i).IsPrime)
    (hbelow : ∀ i, P i < m) :
    ∃ c : J →₀ K, ∀ i, Finsupp.linearCombination K g c ∉ P i := by
  apply exists_linearCombination_avoiding_ideals g P
  intro i hle
  have hmle : m ≤ P i := by
    rw [← hgen]
    exact (hprime i).radical_le_iff.mpr hle
  exact (not_le_of_gt (hbelow i)) hmle

end PiExponentSiegel.W20

end OAI
end Source0152

-- Source: OAI/NumberTheory/PiExponent/LocalAlgebra/IsolatedIntersectionSteps.lean
section Source0153
-- Modified in this edition: unused plain lemmas removed; see reduction.json.
/-
Modification notice for the LogTwo project.
Derived from openai/math (Apache-2.0), revision adc7f1241b42e322a6451854ab7e4b4c146bf78a.
Original source: lean/OAI/NumberTheory/PiExponent/LocalAlgebra/IsolatedIntersectionSteps.lean
Changes: Convert module/import declarations to the Lean 4.34 public module format.
See ../THIRD_PARTY_NOTICES.txt for provenance and the recorded changes.
-/

namespace OAI

namespace PiExponentSiegel.W17.IsolatedIntersection

variable {R : Type*} [CommRing R]

theorem local_regular_avoids_retained_minimalPrime
    (I T : Ideal R) [T.IsPrime] {Q : Ideal R} {f : R}
    (hQ : Q ∈ I.minimalPrimes) (hQT : Q ≤ T)
    (hreg : IsSMulRegular
      (Localization.AtPrime T ⧸ I.map (algebraMap R (Localization.AtPrime T)))
      (algebraMap R (Localization.AtPrime T) f)) : f ∉ Q := by
  let L := Localization.AtPrime T
  let a : R →+* L := algebraMap R L
  have hd : Disjoint (T.primeCompl : Set R) (Q : Set R) := by
    apply Set.disjoint_left.mpr
    intro x hx hxQ
    exact (show x ∉ T from hx) (hQT hxQ)
  have hc : (Q.map a).comap a = Q :=
    IsLocalization.under_map_of_isPrime_disjoint T.primeCompl L hQ.1.1 hd
  have hm : Q.map a ∈ (I.map a).minimalPrimes := by
    rw [IsLocalization.minimalPrimes_map T.primeCompl L]
    change (Q.map a).comap a ∈ I.minimalPrimes
    rw [hc]
    exact hQ
  have hnot : a f ∉ Q.map a := hreg.notMem_of_mem_minimalPrimes
    (by simpa only [Ideal.annihilator_quotient] using hm)
  exact fun hf => hnot (Ideal.mem_map_of_mem a hf)

variable {K ι τ : Type*} [Field K] [Infinite K] [Algebra K R] [Finite ι]

end PiExponentSiegel.W17.IsolatedIntersection

end OAI
end Source0153

-- Source: OAI/NumberTheory/PiExponent/LocalAlgebra/CyclicPrimeFactor.lean
section Source0154
/-
Modification notice for the LogTwo project.
Derived from openai/math (Apache-2.0), revision adc7f1241b42e322a6451854ab7e4b4c146bf78a.
Original source: lean/OAI/NumberTheory/PiExponent/LocalAlgebra/CyclicPrimeFactor.lean
Changes: Convert module/import declarations to the Lean 4.34 public module format.
See ../THIRD_PARTY_NOTICES.txt for provenance and the recorded changes.
-/

namespace OAI

namespace PiExponentJets.W22

variable {R : Type*} [CommRing R]

noncomputable def cyclicFactorEquiv (I : Ideal R) (f : R) :
    (R ⧸ I.colon {f}) ≃ₗ[R]
      (↥(I ⊔ Ideal.span {f}) ⧸ I.submoduleOf (I ⊔ Ideal.span {f})) := by
  let J : Ideal R := I ⊔ Ideal.span {f}
  have hfJ : f ∈ J := (show Ideal.span {f} ≤ J from le_sup_right)
    (Ideal.subset_span (by simp))
  let F : R →ₗ[R] J ⧸ I.submoduleOf J :=
    (I.submoduleOf J).mkQ.comp (LinearMap.toSpanSingleton R J ⟨f, hfJ⟩)
  have hker : LinearMap.ker F = I.colon {f} := by
    ext a
    change ((Submodule.Quotient.mk (a • (⟨f, hfJ⟩ : J)) : J ⧸ I.submoduleOf J) = 0) ↔
      a ∈ I.colon {f}
    rw [Submodule.Quotient.mk_eq_zero]
    change a * f ∈ I ↔ a ∈ I.colon {f}
    simp only [Submodule.mem_colon_singleton, smul_eq_mul]
  have hsurj : Function.Surjective F := by
    intro y
    obtain ⟨x, rfl⟩ := (I.submoduleOf J).mkQ_surjective y
    have hx : (x : R) ∈ Ideal.span {f} ⊔ I := by
      simpa only [J, sup_comm] using x.property
    obtain ⟨a, b, hb, hab⟩ := Ideal.mem_span_singleton_sup.mp hx
    refine ⟨a, ?_⟩
    change (Submodule.Quotient.mk (a • (⟨f, hfJ⟩ : J)) : J ⧸ I.submoduleOf J) =
      Submodule.Quotient.mk x
    rw [Submodule.Quotient.eq]
    change a * f - (x : R) ∈ I
    rw [← hab]
    simpa only [sub_add_eq_sub_sub, sub_self, zero_sub] using I.neg_mem hb
  exact (Submodule.quotEquivOfEq _ _ hker.symm).trans (F.quotKerEquivOfSurjective hsurj)

end PiExponentJets.W22

end OAI
end Source0154

-- Source: OAI/NumberTheory/PiExponent/LocalAlgebra/SubquotientLength.lean
section Source0155
/-
Modification notice for the LogTwo project.
Derived from openai/math (Apache-2.0), revision adc7f1241b42e322a6451854ab7e4b4c146bf78a.
Original source: lean/OAI/NumberTheory/PiExponent/LocalAlgebra/SubquotientLength.lean
Changes: Convert module/import declarations to the Lean 4.34 public module format.
See ../THIRD_PARTY_NOTICES.txt for provenance and the recorded changes.
-/

namespace OAI

namespace PiExponentJets.W22

open scoped BigOperators

variable {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]

noncomputable def subquotientEquivImage (A B : Submodule R M) :
    (B ⧸ A.submoduleOf B) ≃ₗ[R] B.map A.mkQ := by
  let F : B →ₗ[R] M ⧸ A := A.mkQ.comp B.subtype
  have hker : LinearMap.ker F = A.submoduleOf B := by
    simp only [F, LinearMap.ker_comp, Submodule.ker_mkQ, Submodule.submoduleOf]
  have hrange : LinearMap.range F = B.map A.mkQ := by
    simp only [F, LinearMap.range_comp, Submodule.range_subtype]
  exact (Submodule.quotEquivOfEq _ _ hker.symm).trans
    (F.quotKerEquivRange.trans (LinearEquiv.ofEq _ _ hrange))

theorem quotient_length_step (A B : Submodule R M) (hAB : A ≤ B) :
    Module.length R (M ⧸ A) =
      Module.length R (B ⧸ A.submoduleOf B) + Module.length R (M ⧸ B) := by
  let T : Submodule R (M ⧸ A) := B.map A.mkQ
  have h := Module.length_eq_add_of_exact T.subtype T.mkQ
    (Submodule.subtype_injective _) (Submodule.mkQ_surjective _)
    (LinearMap.exact_subtype_mkQ _)
  change Module.length R (M ⧸ A) = Module.length R (B.map A.mkQ) +
    Module.length R ((M ⧸ A) ⧸ B.map A.mkQ) at h
  rw [← (subquotientEquivImage A B).length_eq,
    (Submodule.quotientQuotientEquivQuotient A B hAB).length_eq] at h
  exact h

theorem quotient_length_eq_sum_and_last
    (N : ℕ → Submodule R M) (hmono : ∀ i, N i ≤ N (i + 1)) (n : ℕ) :
    Module.length R (M ⧸ N 0) =
      (∑ i ∈ Finset.range n,
        Module.length R (N (i + 1) ⧸ (N i).submoduleOf (N (i + 1)))) +
      Module.length R (M ⧸ N n) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [ih, quotient_length_step (N n) (N (n + 1)) (hmono n),
      Finset.sum_range_succ, add_assoc]

theorem quotient_length_eq_sum_of_last_top
    (N : ℕ → Submodule R M) (hmono : ∀ i, N i ≤ N (i + 1))
    (n : ℕ) (htop : N n = ⊤) :
    Module.length R (M ⧸ N 0) =
      ∑ i ∈ Finset.range n,
        Module.length R (N (i + 1) ⧸ (N i).submoduleOf (N (i + 1))) := by
  have heq := congrArg (fun A : Submodule R M => Module.length R (M ⧸ A)) htop
  have hz : Module.length R (M ⧸ N n) = 0 := heq.trans Module.length_eq_zero
  simpa only [hz, add_zero] using quotient_length_eq_sum_and_last N hmono n

end PiExponentJets.W22

end OAI
end Source0155

-- Source: OAI/NumberTheory/PiExponent/LocalAlgebra/LocalIntersectionLength.lean
section Source0156
/-
Modification notice for the LogTwo project.
Derived from openai/math (Apache-2.0), revision adc7f1241b42e322a6451854ab7e4b4c146bf78a.
Original source: lean/OAI/NumberTheory/PiExponent/LocalAlgebra/LocalIntersectionLength.lean
Changes: Convert module/import declarations to the Lean 4.34 public module format.
See ../THIRD_PARTY_NOTICES.txt for provenance and the recorded changes.
-/

namespace OAI

namespace PiExponentJets.W28.LocalIntersection

variable {A M : Type*} [CommRing A] [AddCommGroup M] [Module A M]

theorem finite_length_kernel_eq_cokernel
    (u : M →ₗ[A] M) (hfin : IsFiniteLength A M) :
    Module.length A (LinearMap.ker u) =
      Module.length A (M ⧸ LinearMap.range u) := by
  have hk := Module.length_eq_add_of_exact (LinearMap.ker u).subtype
    (LinearMap.ker u).mkQ (Submodule.subtype_injective _)
    (Submodule.mkQ_surjective _) (LinearMap.exact_subtype_mkQ _)
  rw [u.quotKerEquivRange.length_eq] at hk
  have hr := Module.length_eq_add_of_exact (LinearMap.range u).subtype
    (LinearMap.range u).mkQ (Submodule.subtype_injective _)
    (Submodule.mkQ_surjective _) (LinearMap.exact_subtype_mkQ _)
  have hfiniteRange : Module.length A (LinearMap.range u) ≠ ⊤ :=
    Module.length_ne_top_iff.mpr
      (hfin.of_injective (Submodule.subtype_injective (LinearMap.range u)))
  apply ENat.add_left_injective_of_ne_top hfiniteRange
  calc
    Module.length A (LinearMap.ker u) + Module.length A (LinearMap.range u) =
        Module.length A M := hk.symm
    _ = Module.length A (M ⧸ LinearMap.range u) +
        Module.length A (LinearMap.range u) := hr.trans (add_comm _ _)

def quotientMul (I : Ideal A) (x : A) : (A ⧸ I) →ₗ[A] (A ⧸ I) :=
  x • LinearMap.id

@[simp] theorem quotientMul_apply (I : Ideal A) (x : A) (y : A ⧸ I) :
    quotientMul I x y = x • y := rfl

@[simp] theorem quotientMul_mk (I : Ideal A) (x a : A) :
    quotientMul I x (I.mkQ a) = I.mkQ (a * x) := by
  change x • I.mkQ a = I.mkQ (a * x)
  calc
    x • I.mkQ a = I.mkQ (x • a) := (I.mkQ.map_smul x a).symm
    _ = I.mkQ (a * x) := by rw [smul_eq_mul, mul_comm]

theorem quotientMul_kernel (I : Ideal A) (x : A) :
    LinearMap.ker (quotientMul I x) = Submodule.map I.mkQ (I.colon {x}) := by
  ext y
  constructor
  · intro hy
    obtain ⟨a, rfl⟩ := I.mkQ_surjective y
    have ha : a * x ∈ I := by
      have hz : quotientMul I x (I.mkQ a) = 0 := hy
      rw [quotientMul_mk, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero] at hz
      exact hz
    refine ⟨a, ?_, rfl⟩
    change a ∈ I.colon {x}
    simpa only [Submodule.mem_colon_singleton, smul_eq_mul] using ha
  · rintro ⟨a, ha, rfl⟩
    change a ∈ I.colon {x} at ha
    change quotientMul I x (I.mkQ a) = 0
    rw [quotientMul_mk, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
    simpa only [Submodule.mem_colon_singleton, smul_eq_mul] using ha

noncomputable def colonQuotientEquivKernel (I : Ideal A) (x : A) :
    ((I.colon {x}) ⧸ I.submoduleOf (I.colon {x})) ≃ₗ[A]
      LinearMap.ker (quotientMul I x) :=
  (W22.subquotientEquivImage I (I.colon {x})).trans
    (LinearEquiv.ofEq _ _ (quotientMul_kernel I x).symm)

theorem quotientMul_range (I : Ideal A) (x : A) :
    LinearMap.range (quotientMul I x) = Submodule.map I.mkQ (Ideal.span {x}) := by
  have hcomp : (quotientMul I x).comp I.mkQ =
      I.mkQ.comp (LinearMap.toSpanSingleton A A x) := by
    apply LinearMap.ext
    intro a
    change quotientMul I x (I.mkQ a) = I.mkQ (a * x)
    exact quotientMul_mk I x a
  have hr := congrArg LinearMap.range hcomp
  simpa only [LinearMap.range_comp, Submodule.range_mkQ, Submodule.map_top,
    LinearMap.range_toSpanSingleton] using hr

noncomputable def cokernelEquivCut (I : Ideal A) (x : A) :
    ((A ⧸ I) ⧸ LinearMap.range (quotientMul I x)) ≃ₗ[A]
      A ⧸ (I ⊔ Ideal.span {x}) :=
  (Submodule.quotEquivOfEq _ _ (quotientMul_range I x)).trans
    (Submodule.quotientQuotientEquivQuotientSup I (Ideal.span {x}))

theorem kernel_length_eq_colon (I : Ideal A) (x : A) :
    Module.length A (LinearMap.ker (quotientMul I x)) =
      Module.length A ((I.colon {x}) ⧸ I.submoduleOf (I.colon {x})) :=
  (colonQuotientEquivKernel I x).length_eq.symm

theorem cokernel_length_eq_cut (I : Ideal A) (x : A) :
    Module.length A ((A ⧸ I) ⧸ LinearMap.range (quotientMul I x)) =
      Module.length A (A ⧸ (I ⊔ Ideal.span {x})) :=
  (cokernelEquivCut I x).length_eq

theorem finite_length_cut_eq_colon (I : Ideal A) (x : A)
    (hfin : IsFiniteLength A (A ⧸ I)) :
    Module.length A (A ⧸ (I ⊔ Ideal.span {x})) =
      Module.length A ((I.colon {x}) ⧸ I.submoduleOf (I.colon {x})) := by
  rw [← cokernel_length_eq_cut, ← kernel_length_eq_colon]
  exact (finite_length_kernel_eq_cokernel (quotientMul I x) hfin).symm

theorem regular_colon_length_zero (I : Ideal A) (x : A)
    (hregular : Function.Injective (quotientMul I x)) :
    Module.length A ((I.colon {x}) ⧸ I.submoduleOf (I.colon {x})) = 0 := by
  rw [← kernel_length_eq_colon, LinearMap.ker_eq_bot.mpr hregular]
  exact Module.length_bot

end PiExponentJets.W28.LocalIntersection

end OAI
end Source0156

-- Source: OAI/NumberTheory/PiExponent/LocalAlgebra/FiniteFreeExtTransfer.lean
section Source0157
/-
Modification notice for the LogTwo project.
Derived from openai/math (Apache-2.0), revision adc7f1241b42e322a6451854ab7e4b4c146bf78a.
Original source: lean/OAI/NumberTheory/PiExponent/LocalAlgebra/FiniteFreeExtTransfer.lean
Changes: Convert module/import declarations to the Lean 4.34 public module format.
See ../THIRD_PARTY_NOTICES.txt for provenance and the recorded changes.
-/

namespace OAI

noncomputable section
universe w v u

namespace PiExponentSiegelAux.W31
open Module
open CategoryTheory CategoryTheory.Abelian
open scoped BigOperators

section General
variable {C : Type u} [Category.{v} C] [Abelian C] [HasExt.{w} C]

theorem ext_subsingleton_of_finite_identity_factorization
    {ι : Type*} [Fintype ι] (X F G : C) (n : ℕ)
    (p : ι → (F ⟶ G)) (j : ι → (G ⟶ F))
    (htotal : (∑ i, p i ≫ j i) = 𝟙 F)
    (h : Subsingleton (Ext X G n)) : Subsingleton (Ext X F n) := by
  apply subsingleton_of_forall_eq 0
  intro e
  have he : (∑ i, (e.comp (Ext.mk₀ (p i)) (add_zero n)).comp
      (Ext.mk₀ (j i)) (add_zero n)) = e := by
    simp only [Ext.comp_assoc_of_second_deg_zero, Ext.mk₀_comp_mk₀,
      ← Ext.comp_sum, ← Ext.mk₀_sum, htotal, Ext.comp_mk₀_id]
  calc
    e = _ := he.symm
    _ = 0 := by
      apply Finset.sum_eq_zero
      intro i hi
      rw [h.elim (e.comp (Ext.mk₀ (p i)) (add_zero n)) 0, Ext.zero_comp]

end General

variable {R : Type u} [CommRing R]
variable {F : Type u} [AddCommGroup F] [Module R F]

theorem ext_subsingleton_of_finite_basis {ι : Type*} [Fintype ι]
    (b : Basis ι R F) (X : ModuleCat.{u} R) (n : ℕ)
    (h : Subsingleton (Ext X (ModuleCat.of R R) n)) :
    Subsingleton (Ext X (ModuleCat.of R F) n) := by
  apply ext_subsingleton_of_finite_identity_factorization X (ModuleCat.of R F)
    (ModuleCat.of R R) n
    (fun i => ModuleCat.ofHom (b.coord i))
    (fun i => ModuleCat.ofHom (LinearMap.toSpanSingleton R F (b i))) ?_ h
  apply ModuleCat.hom_ext
  ext x
  simpa only [ModuleCat.hom_sum, ModuleCat.hom_comp, ModuleCat.hom_ofHom,
    ModuleCat.hom_id, LinearMap.sum_apply, LinearMap.comp_apply,
    LinearMap.toSpanSingleton_apply, Basis.coord_apply, LinearMap.id_apply] using
    b.sum_repr x

theorem ext_subsingleton_of_finite_free [Module.Free R F] [Module.Finite R F]
    (X : ModuleCat.{u} R) (n : ℕ)
    (h : Subsingleton (Ext X (ModuleCat.of R R) n)) :
    Subsingleton (Ext X (ModuleCat.of R F) n) :=
  ext_subsingleton_of_finite_basis (Module.Free.chooseBasis R F) X n h

end PiExponentSiegelAux.W31

end

end OAI
end Source0157

-- Source: OAI/NumberTheory/PiExponent/LocalAlgebra/FreeResolutionAssociatedHeight.lean
section Source0158
-- Modified in this edition: unused plain lemmas removed; see reduction.json.
/-
Modification notice for the LogTwo project.
Derived from openai/math (Apache-2.0), revision adc7f1241b42e322a6451854ab7e4b4c146bf78a.
Original source: lean/OAI/NumberTheory/PiExponent/LocalAlgebra/FreeResolutionAssociatedHeight.lean
Changes: Convert module/import declarations to the Lean 4.34 public module format.
See ../THIRD_PARTY_NOTICES.txt for provenance and the recorded changes.
-/

namespace OAI

noncomputable section

universe w v u

namespace PiExponentJets.W18
open CategoryTheory CategoryTheory.Abelian

section ExactDimensionShifting
variable {C : Type u} [Category.{v} C] [Abelian C] [HasExt.{w} C]

theorem ext_subsingleton_of_shortExact
    (X : C) (S : ShortComplex C) (hS : S.ShortExact) (n : ℕ)
    (hmid : Subsingleton (Ext X S.X₂ n))
    (hleft : Subsingleton (Ext X S.X₁ (n + 1))) :
    Subsingleton (Ext X S.X₃ n) := by
  let := hmid
  let := hleft
  apply subsingleton_of_forall_eq 0
  intro e
  obtain ⟨a, ha⟩ := Ext.covariant_sequence_exact₃ X hS e rfl
    (Subsingleton.elim _ 0)
  rw [Subsingleton.elim a 0, Ext.zero_comp] at ha
  exact ha.symm

end ExactDimensionShifting

variable {R : Type u} [CommRing R] [IsNoetherianRing R]
variable {M : Type u} [AddCommGroup M] [Module R M]

theorem associatedPrime_nonzero_quotient_hom (P : Ideal R)
    (hP : IsAssociatedPrime P M) :
    ∃ f : R ⧸ P →ₗ[R] M, f ≠ 0 := by
  obtain ⟨hprime, f, hf⟩ :=
    (isAssociatedPrime_iff_exists_injective_linearMap P M).mp hP
  let := hprime
  refine ⟨f, ?_⟩
  intro hz
  have h10 : (1 : R ⧸ P) = 0 := hf (by simp [hz])
  exact one_ne_zero h10

theorem associatedPrime_nonzero_ext_zero (P : Ideal R)
    (hP : IsAssociatedPrime P M) :
    ∃ e : Ext (ModuleCat.of R (R ⧸ P)) (ModuleCat.of R M) 0, e ≠ 0 := by
  obtain ⟨f, hf⟩ := associatedPrime_nonzero_quotient_hom P hP
  refine ⟨Ext.mk₀ (ModuleCat.ofHom f), ?_⟩
  intro he
  have hh := (Ext.mk₀_eq_zero_iff (ModuleCat.ofHom f)).mp he
  exact hf (congrArg (fun g : ModuleCat.of R (R ⧸ P) ⟶ ModuleCat.of R M => g.hom) hh)

theorem not_isAssociatedPrime_of_ext_zero (P : Ideal R)
    (h : Subsingleton (Ext (ModuleCat.of R (R ⧸ P)) (ModuleCat.of R M) 0)) :
    ¬ IsAssociatedPrime P M := by
  intro hP
  obtain ⟨e, he⟩ := associatedPrime_nonzero_ext_zero P hP
  exact he (h.elim e 0)

end PiExponentJets.W18

end

end OAI
end Source0158

-- Source: OAI/NumberTheory/PiExponent/Polynomials/PolynomialLocalUnmixedness.lean
section Source0159
-- Modified in this edition: unused plain lemmas removed; see reduction.json.
/-
Modification notice for the LogTwo project.
Derived from openai/math (Apache-2.0), revision adc7f1241b42e322a6451854ab7e4b4c146bf78a.
Original source: lean/OAI/NumberTheory/PiExponent/Polynomials/PolynomialLocalUnmixedness.lean
Changes: Convert module/import declarations to the Lean 4.34 public module format.
See ../THIRD_PARTY_NOTICES.txt for provenance and the recorded changes.
-/

namespace OAI

noncomputable section
namespace PiExponentJets.PolynomialLocalUnmixedness

section RegularPair
variable {S : Type*} [CommRing S]

def pairRelation (f g : S) : (S × S) →ₗ[S] S where
  toFun z := f * z.1 + g * z.2
  map_add' x y := by dsimp; ring
  map_smul' r x := by simp only [Prod.smul_fst, Prod.smul_snd, RingHom.id_apply, smul_eq_mul]; ring

def pairBoundary (f g : S) : S →ₗ[S] S × S where
  toFun t := (-g * t, f * t)
  map_add' x y := by ext <;> dsimp <;> ring
  map_smul' r x := by ext <;> simp only [Prod.smul_fst, Prod.smul_snd, RingHom.id_apply, smul_eq_mul] <;> ring

theorem pair_relation_range (f g : S) :
    LinearMap.range (pairRelation f g) = Ideal.ofList [f, g] := by
  apply le_antisymm
  · rintro _ ⟨⟨a, b⟩, rfl⟩
    have hf : f ∈ Ideal.ofList [f, g] := Ideal.subset_span (by simp)
    have hg : g ∈ Ideal.ofList [f, g] := Ideal.subset_span (by simp)
    change f * a + g * b ∈ Ideal.ofList [f, g]
    exact Ideal.add_mem _ (by simpa [mul_comm] using (Ideal.ofList [f, g]).smul_mem a hf)
      (by simpa [mul_comm] using (Ideal.ofList [f, g]).smul_mem b hg)
  · apply Ideal.span_le.mpr
    intro r hr
    have hr : r = f ∨ r = g := by simpa using hr
    rcases hr with rfl | rfl
    · exact ⟨(1, 0), by simp [pairRelation]⟩
    · exact ⟨(0, 1), by simp [pairRelation]⟩

def pairToIdeal (f g : S) : (S × S) →ₗ[S] Ideal.ofList [f, g] :=
  (pairRelation f g).codRestrict (Ideal.ofList [f, g]) (fun z => by
    rw [← pair_relation_range]
    exact LinearMap.mem_range_self _ _)

end RegularPair

variable (k : Type*) [Field k] (n : ℕ)
variable (Q : Ideal (MvPolynomial (Fin n) k)) [Q.IsPrime]

abbrev PolynomialLocal := Localization.AtPrime Q

def PolynomialLocalPairUnmixednessTarget : Prop :=
  ∀ f g : PolynomialLocal k n Q,
    RingTheory.Sequence.IsRegular (PolynomialLocal k n Q) [f, g] →
    ∀ P : Ideal (PolynomialLocal k n Q),
      IsAssociatedPrime P (PolynomialLocal k n Q ⧸ Ideal.ofList [f, g]) →
        P.height = 2

end PiExponentJets.PolynomialLocalUnmixedness

end

end OAI
end Source0159

-- Source: OAI/NumberTheory/PiExponent/LocalAlgebra/PairResolutionShortComplex.lean
section Source0160
-- Modified in this edition: unused plain lemmas removed; see reduction.json.
/-
Modification notice for the LogTwo project.
Derived from openai/math (Apache-2.0), revision adc7f1241b42e322a6451854ab7e4b4c146bf78a.
Original source: lean/OAI/NumberTheory/PiExponent/LocalAlgebra/PairResolutionShortComplex.lean
Changes: Convert module/import declarations to the Lean 4.34 public module format.
See ../THIRD_PARTY_NOTICES.txt for provenance and the recorded changes.
-/

namespace OAI

noncomputable section
namespace PiExponentJets.PolynomialLocalUnmixedness
open CategoryTheory

variable {S : Type*} [CommRing S]

def pairQuotientShortComplex (f g : S) : ShortComplex (ModuleCat S) :=
  ShortComplex.moduleCatMk (Ideal.ofList [f, g]).subtype (Ideal.ofList [f, g]).mkQ
    (by
      apply LinearMap.ext
      intro x
      exact (Submodule.Quotient.mk_eq_zero (Ideal.ofList [f, g])).mpr x.property)

def pairSyzygyShortComplex (f g : S) : ShortComplex (ModuleCat S) :=
  ShortComplex.moduleCatMk (pairBoundary f g) (pairToIdeal f g) (by
    apply LinearMap.ext
    intro t
    apply Subtype.ext
    change f * (-g * t) + g * (f * t) = 0
    ring)

end PiExponentJets.PolynomialLocalUnmixedness

end

end OAI
end Source0160

-- Source: OAI/NumberTheory/PiExponent/LocalAlgebra/RegularPairExtObstruction.lean
section Source0161
-- Modified in this edition: unused plain lemmas removed; see reduction.json.
/-
Modification notice for the LogTwo project.
Derived from openai/math (Apache-2.0), revision adc7f1241b42e322a6451854ab7e4b4c146bf78a.
Original source: lean/OAI/NumberTheory/PiExponent/LocalAlgebra/RegularPairExtObstruction.lean
Changes: Convert module/import declarations to the Lean 4.34 public module format.
See ../THIRD_PARTY_NOTICES.txt for provenance and the recorded changes.
-/

namespace OAI

noncomputable section
universe u
namespace PiExponentJets.W18
open CategoryTheory CategoryTheory.Abelian
open PiExponentJets.PolynomialLocalUnmixedness

variable {S : Type u} [CommRing S]

end PiExponentJets.W18

end

end OAI
end Source0161

-- Source: OAI/NumberTheory/PiExponent/Polynomials/PolynomialAssociatedLocalization.lean
section Source0162
-- Modified in this edition: unused plain lemmas removed; see reduction.json.
/-
Modification notice for the LogTwo project.
Derived from openai/math (Apache-2.0), revision adc7f1241b42e322a6451854ab7e4b4c146bf78a.
Original source: lean/OAI/NumberTheory/PiExponent/Polynomials/PolynomialAssociatedLocalization.lean
Changes: Convert module/import declarations to the Lean 4.34 public module format.
See ../THIRD_PARTY_NOTICES.txt for provenance and the recorded changes.
-/

namespace OAI

noncomputable section
universe u
open IsLocalRing RingTheory.Sequence
namespace PiExponentSiegel.W58

section Flat
variable {R S : Type*} [CommRing R] [CommRing S] [Algebra R S]

theorem weaklyRegular_map_of_flat [Module.Flat R S] (rs : List R)
    (h : IsWeaklyRegular R rs) :
    IsWeaklyRegular S (rs.map (algebraMap R S)) := by
  apply (isWeaklyRegular_map_algebraMap_iff S S rs).mpr
  exact ((TensorProduct.rid R S).isWeaklyRegular_congr rs).mp
    (h.isWeaklyRegular_lTensor (M₂ := S))

end Flat

section LocalQuotient
variable {R : Type*} [CommRing R]
variable (L : Type*) [CommRing L] [Algebra R L]
variable (P : Ideal R) [P.IsPrime] [IsLocalization.AtPrime L P] [IsLocalRing L]

omit [IsLocalRing L] in
theorem localized_ideal_eq_map (I : Ideal R) :
    I.localized' L P.primeCompl (Algebra.linearMap R L) =
      I.map (algebraMap R L) := by
  rw [Submodule.localized'_eq_span]
  rfl

def localizedIdealQuotientEquiv (I : Ideal R) :
    (L ⧸ I.localized' L P.primeCompl (Algebra.linearMap R L)) ≃ₗ[L]
      L ⧸ I.map (algebraMap R L) :=
  Submodule.quotEquivOfEq _ _ (localized_ideal_eq_map L P I)

omit [P.IsPrime] in
theorem ideal_le_of_quotient_associatedPrime (I : Ideal R)
    (hP : IsAssociatedPrime P (R ⧸ I)) : I ≤ P := by
  simpa only [Submodule.annihilator_top, Ideal.annihilator_quotient] using
    hP.annihilator_le

end LocalQuotient

variable {R : Type u} [CommRing R]
variable (L : Type u) [CommRing L] [Algebra R L] [IsNoetherianRing L]
variable (P : Ideal R) [P.IsPrime] [IsLocalization.AtPrime L P]
variable [IsLocalRing L]

end PiExponentSiegel.W58

end

end OAI
end Source0162

-- Source: OAI/NumberTheory/PiExponent/LocalAlgebra/RegularPrefixLocalization.lean
section Source0163
/-
Modification notice for the LogTwo project.
Derived from openai/math (Apache-2.0), revision adc7f1241b42e322a6451854ab7e4b4c146bf78a.
Original source: lean/OAI/NumberTheory/PiExponent/LocalAlgebra/RegularPrefixLocalization.lean
Changes: Convert module/import declarations to the Lean 4.34 public module format.
See ../THIRD_PARTY_NOTICES.txt for provenance and the recorded changes.
-/

namespace OAI

noncomputable section
namespace PiExponentJets.W16

open RingTheory.Sequence

variable {A : Type*} [CommRing A]

theorem weaklyRegular_atPrime_mono
    (T Q : Ideal A) [T.IsPrime] [Q.IsPrime] (hQT : Q ≤ T)
    (gs : List A)
    (hreg : IsWeaklyRegular (Localization.AtPrime T)
      (gs.map (algebraMap A (Localization.AtPrime T)))) :
    IsWeaklyRegular (Localization.AtPrime Q)
      (gs.map (algebraMap A (Localization.AtPrime Q))) := by
  have hc : T.primeCompl ≤ Q.primeCompl := by
    intro a ha
    exact fun h => ha (hQT h)
  let : Algebra (Localization.AtPrime T) (Localization.AtPrime Q) :=
    IsLocalization.localizationAlgebraOfSubmonoidLe
      (Localization.AtPrime T) (Localization.AtPrime Q) T.primeCompl Q.primeCompl hc
  let : IsScalarTower A (Localization.AtPrime T) (Localization.AtPrime Q) :=
    IsLocalization.localization_isScalarTower_of_submonoid_le
      (Localization.AtPrime T) (Localization.AtPrime Q) T.primeCompl Q.primeCompl hc
  let : IsLocalization
      (Q.primeCompl.map (algebraMap A (Localization.AtPrime T)))
      (Localization.AtPrime Q) :=
    IsLocalization.isLocalization_of_submonoid_le
      (Localization.AtPrime T) (Localization.AtPrime Q) T.primeCompl Q.primeCompl hc
  let : Module.Flat (Localization.AtPrime T) (Localization.AtPrime Q) :=
    IsLocalization.flat (Localization.AtPrime Q)
      (Q.primeCompl.map (algebraMap A (Localization.AtPrime T)))
  have hh := PiExponentSiegel.W58.weaklyRegular_map_of_flat
    (S := Localization.AtPrime Q)
    (gs.map (algebraMap A (Localization.AtPrime T))) hreg
  have hmaps :
      (gs.map (algebraMap A (Localization.AtPrime T))).map
        (algebraMap (Localization.AtPrime T) (Localization.AtPrime Q)) =
      gs.map (algebraMap A (Localization.AtPrime Q)) := by
    simp only [List.map_map]
    congr 1
    funext a
    exact (IsScalarTower.algebraMap_apply A
      (Localization.AtPrime T) (Localization.AtPrime Q) a).symm
  rw [hmaps] at hh
  exact hh

theorem regularPrefix_quotientMul_injective
    (T Q : Ideal A) [T.IsPrime] [Q.IsPrime] (hQT : Q ≤ T)
    (gs : List A)
    (hreg : IsRegular (Localization.AtPrime T)
      (gs.map (algebraMap A (Localization.AtPrime T))))
    (j : ℕ) (hj : j < gs.length) :
    Function.Injective
      (W28.LocalIntersection.quotientMul
        ((Ideal.ofList (gs.take j)).map (algebraMap A (Localization.AtPrime Q)))
        (algebraMap A (Localization.AtPrime Q) gs[j])) := by
  have hw := weaklyRegular_atPrime_mono T Q hQT gs hreg.toIsWeaklyRegular
  have hm := hw.regular_mod_prev j (by simpa only [List.length_map] using hj)
  have he :
      (Ideal.ofList ((gs.map (algebraMap A (Localization.AtPrime Q))).take j) •
        (⊤ : Submodule (Localization.AtPrime Q) (Localization.AtPrime Q))) =
      (Ideal.ofList (gs.take j)).map (algebraMap A (Localization.AtPrime Q)) := by
    change Ideal.ofList ((gs.map (algebraMap A (Localization.AtPrime Q))).take j) *
      (⊤ : Ideal (Localization.AtPrime Q)) = _
    rw [Ideal.mul_top, Ideal.map_ofList, List.map_take]
  have hm' : IsSMulRegular
      (Localization.AtPrime Q ⧸
        (Ideal.ofList ((gs.map (algebraMap A (Localization.AtPrime Q))).take j) •
          (⊤ : Submodule (Localization.AtPrime Q) (Localization.AtPrime Q))))
      (algebraMap A (Localization.AtPrime Q) gs[j]) := by
    simpa only [List.getElem_map] using hm
  change IsSMulRegular
    (Localization.AtPrime Q ⧸
      (Ideal.ofList (gs.take j)).map (algebraMap A (Localization.AtPrime Q)))
    (algebraMap A (Localization.AtPrime Q) gs[j])
  exact ((Submodule.quotEquivOfEq _ _ he).isSMulRegular_congr
    (algebraMap A (Localization.AtPrime Q) gs[j])).mp hm'

end PiExponentJets.W16

end

end OAI
end Source0163

-- Source: OAI/NumberTheory/PiExponent/LocalAlgebra/LocalPrefixCutDimension.lean
section Source0164
/-
Modification notice for the LogTwo project.
Derived from openai/math (Apache-2.0), revision adc7f1241b42e322a6451854ab7e4b4c146bf78a.
Original source: lean/OAI/NumberTheory/PiExponent/LocalAlgebra/LocalPrefixCutDimension.lean
Changes: Convert module/import declarations to the Lean 4.34 public module format.
See ../THIRD_PARTY_NOTICES.txt for provenance and the recorded changes.
-/

namespace OAI

namespace PiExponentJets.W29

open Ideal

section LocalQuotient

variable {S : Type*} [CommRing S] [IsNoetherianRing S] [IsLocalRing S]

theorem local_quotient_cut_dimension_one (I : Ideal S) (x : S)
    (hmin : IsLocalRing.maximalIdeal S ∈ (I ⊔ Ideal.span {x}).minimalPrimes)
    (hinj : Function.Injective (W28.LocalIntersection.quotientMul I x)) :
    ringKrullDim (S ⧸ I) = 1 := by
  have hImax : I ≤ IsLocalRing.maximalIdeal S := le_sup_left.trans hmin.1.2
  have hIne : I ≠ ⊤ := ne_of_lt
    (lt_of_le_of_lt hImax (IsLocalRing.maximalIdeal.isMaximal S).lt_top)
  let : Nontrivial (S ⧸ I) := Ideal.Quotient.nontrivial_iff.mpr hIne
  let : IsLocalRing (S ⧸ I) :=
    IsLocalRing.of_surjective' (Ideal.Quotient.mk I) Ideal.Quotient.mk_surjective
  have hmap : (IsLocalRing.maximalIdeal S).map (Ideal.Quotient.mk I) =
      IsLocalRing.maximalIdeal (S ⧸ I) :=
    IsLocalRing.map_maximalIdeal_of_surjective (Ideal.Quotient.mk I)
      Ideal.Quotient.mk_surjective
  have hu : ringKrullDim (S ⧸ I) ≤ 1 := by
    have hheight := Ideal.map_height_le_one_of_mem_minimalPrimes hmin
    rw [hmap] at hheight
    rw [← IsLocalRing.maximalIdeal_height_eq_ringKrullDim]
    exact WithBot.coe_le_coe.mpr hheight
  let xb : S ⧸ I := Ideal.Quotient.mk I x
  have hx : x ∈ IsLocalRing.maximalIdeal S :=
    hmin.1.2 (Ideal.mem_sup_right (Ideal.subset_span (by simp)))
  have hxb : xb ∈ IsLocalRing.maximalIdeal (S ⧸ I) := by
    rw [← hmap]
    exact Ideal.mem_map_of_mem (Ideal.Quotient.mk I) hx
  have hreg : IsSMulRegular (S ⧸ I) xb := by
    intro y z hyz
    change xb * y = xb * z at hyz
    apply hinj
    change x • y = x • z
    simpa only [Algebra.smul_def, Ideal.Quotient.algebraMap_eq] using hyz
  have hspan : (Ideal.span {xb} : Ideal (S ⧸ I)) ≤
      IsLocalRing.maximalIdeal (S ⧸ I) := (Ideal.span_singleton_le_iff_mem _).mpr hxb
  have hspanne : (Ideal.span {xb} : Ideal (S ⧸ I)) ≠ ⊤ := ne_of_lt
    (lt_of_le_of_lt hspan (IsLocalRing.maximalIdeal.isMaximal (S ⧸ I)).lt_top)
  let : Nontrivial ((S ⧸ I) ⧸ Ideal.span {xb}) :=
    Ideal.Quotient.nontrivial_iff.mpr hspanne
  have hdrop := ringKrullDim_quotient_span_singleton_succ_eq_ringKrullDim hreg hxb
  have hl : 1 ≤ ringKrullDim (S ⧸ I) := by
    rw [← hdrop]
    simpa only [zero_add, add_zero, add_comm] using add_le_add_right
      (ringKrullDim_nonneg_of_nontrivial (R := (S ⧸ I) ⧸ Ideal.span {xb}))
      (1 : WithBot ℕ∞)
  exact le_antisymm hu hl

end LocalQuotient

variable {A : Type*} [CommRing A] [IsNoetherianRing A]

theorem regularPrefix_local_cut_dimension_one
    (T Q : Ideal A) [T.IsPrime] [Q.IsPrime] (hQT : Q ≤ T)
    (gs : List A)
    (hreg : RingTheory.Sequence.IsRegular (Localization.AtPrime T)
      (gs.map (algebraMap A (Localization.AtPrime T))))
    (j : ℕ) (hj : j < gs.length)
    (hQ : Q ∈ (Ideal.ofList (gs.take j) ⊔ Ideal.span {gs[j]}).minimalPrimes) :
    ringKrullDim (Localization.AtPrime Q ⧸
      (Ideal.ofList (gs.take j)).map (algebraMap A (Localization.AtPrime Q))) = 1 := by
  let μ := algebraMap A (Localization.AtPrime Q)
  have hmin : IsLocalRing.maximalIdeal (Localization.AtPrime Q) ∈
      (((Ideal.ofList (gs.take j)).map μ) ⊔ Ideal.span {μ gs[j]}).minimalPrimes := by
    have hloc : IsLocalRing.maximalIdeal (Localization.AtPrime Q) ∈
        ((Ideal.ofList (gs.take j) ⊔ Ideal.span {gs[j]}).map μ).minimalPrimes := by
      rw [IsLocalization.minimalPrimes_map Q.primeCompl (Localization.AtPrime Q)]
      simpa only [Set.mem_preimage, Localization.AtPrime.under_maximalIdeal] using hQ
    simpa only [Ideal.map_sup, Ideal.map_span, Set.image_singleton] using hloc
  exact local_quotient_cut_dimension_one _ _ hmin
    (W16.regularPrefix_quotientMul_injective T Q hQT gs hreg j hj)

end PiExponentJets.W29

end OAI
end Source0164

-- Source: OAI/NumberTheory/PiExponent/Polynomials/HomogeneousSections.lean
section Source0165
-- Modified in this edition: unused plain lemmas removed; see reduction.json.
/-
Modification notice for the LogTwo project.
Derived from openai/math (Apache-2.0), revision adc7f1241b42e322a6451854ab7e4b4c146bf78a.
Original source: lean/OAI/NumberTheory/PiExponent/Polynomials/HomogeneousSections.lean
Changes: Convert module/import declarations to the Lean 4.34 public module format.
See ../THIRD_PARTY_NOTICES.txt for provenance and the recorded changes.
-/

namespace OAI

namespace PiExponentJets.W64

variable {k σ : Type*} [Field k] [Finite σ]

private theorem finite_exponents_of_degree (n : ℕ) :
    {d : σ →₀ ℕ | d.degree = n}.Finite :=
  (Finsupp.finite_of_degree_le n).subset (fun _ h => le_of_eq h)

noncomputable instance homogeneousSection_finite (n : ℕ) :
    Module.Finite k (MvPolynomial.homogeneousSubmodule σ k n) := by
  rw [MvPolynomial.homogeneousSubmodule_eq_finsupp_supported]
  let : Fintype {d : σ →₀ ℕ | d.degree = n} :=
    (finite_exponents_of_degree n).fintype
  exact Module.Finite.equiv
    (AddMonoidAlgebra.supportedEquivFinsupp (R := k) (S := k)
      {d : σ →₀ ℕ | d.degree = n}).symm

theorem homogeneousSection_finrank (n : ℕ) :
    Module.finrank k (MvPolynomial.homogeneousSubmodule σ k n) =
      Nat.card {d : σ →₀ ℕ | d.degree = n} := by
  rw [MvPolynomial.homogeneousSubmodule_eq_finsupp_supported]
  let : Fintype {d : σ →₀ ℕ | d.degree = n} :=
    (finite_exponents_of_degree n).fintype
  calc
    _ = Module.finrank k ({d : σ →₀ ℕ | d.degree = n} →₀ k) :=
      (AddMonoidAlgebra.supportedEquivFinsupp (R := k) (S := k)
        {d : σ →₀ ℕ | d.degree = n}).finrank_eq
    _ = Nat.card {d : σ →₀ ℕ | d.degree = n} := by
      simp only [Module.finrank_finsupp_self, Nat.card_eq_fintype_card]

noncomputable def homogeneousMultiply {d : ℕ} (f : MvPolynomial σ k)
    (hf : f.IsHomogeneous d) (n : ℕ) :
    MvPolynomial.homogeneousSubmodule σ k n →ₗ[k]
      MvPolynomial.homogeneousSubmodule σ k (n + d) where
  toFun x := ⟨x.1 * f, x.2.mul hf⟩
  map_add' x y := by apply Subtype.ext; exact add_mul _ _ _
  map_smul' c x := by apply Subtype.ext; exact smul_mul_assoc _ _ _

omit [Finite σ] in
theorem homogeneousMultiply_injective {d : ℕ} (f : MvPolynomial σ k)
    (hf : f.IsHomogeneous d) (hf0 : f ≠ 0) (n : ℕ) :
    Function.Injective (homogeneousMultiply f hf n) := by
  intro x y h
  apply Subtype.ext
  exact mul_right_cancel₀ hf0 (congrArg Subtype.val h)

end PiExponentJets.W64

end OAI
end Source0165

-- Source: OAI/NumberTheory/PiExponent/LocalAlgebra/QuotientSections.lean
section Source0166
/-
Modification notice for the LogTwo project.
Derived from openai/math (Apache-2.0), revision adc7f1241b42e322a6451854ab7e4b4c146bf78a.
Original source: lean/OAI/NumberTheory/PiExponent/LocalAlgebra/QuotientSections.lean
Changes: Convert module/import declarations to the Lean 4.34 public module format.
See ../THIRD_PARTY_NOTICES.txt for provenance and the recorded changes.
-/

namespace OAI

namespace PiExponentJets.W64

variable {k σ : Type*} [Field k] [Finite σ]

noncomputable def quotientSection (I : Ideal (MvPolynomial σ k)) (n : ℕ) :
    Submodule k (MvPolynomial σ k ⧸ I) :=
  (MvPolynomial.homogeneousSubmodule σ k n).map (Ideal.Quotient.mkₐ k I).toLinearMap

noncomputable instance quotientSection_finite (I : Ideal (MvPolynomial σ k)) (n : ℕ) :
    Module.Finite k (quotientSection I n) := by
  unfold quotientSection
  infer_instance

noncomputable def quotientSectionMultiply (I : Ideal (MvPolynomial σ k))
    {d : ℕ} (f : MvPolynomial σ k) (hf : f.IsHomogeneous d) (n : ℕ) :
    quotientSection I n →ₗ[k] quotientSection I (n + d) where
  toFun x := ⟨x.1 * Ideal.Quotient.mk I f, by
    obtain ⟨p, hp, hpx⟩ := Submodule.mem_map.mp x.2
    apply Submodule.mem_map.mpr
    refine ⟨p * f, hp.mul hf, ?_⟩
    change Ideal.Quotient.mk I (p * f) = x.1 * Ideal.Quotient.mk I f
    rw [map_mul]
    exact congrArg (fun y => y * Ideal.Quotient.mk I f) hpx⟩
  map_add' x y := by apply Subtype.ext; exact add_mul _ _ _
  map_smul' c x := by apply Subtype.ext; exact smul_mul_assoc _ _ _

omit [Finite σ] in
theorem quotientSectionMultiply_injective (I : Ideal (MvPolynomial σ k))
    {d : ℕ} (f : MvPolynomial σ k) (hf : f.IsHomogeneous d)
    (hreg : IsRightRegular (Ideal.Quotient.mk I f)) (n : ℕ) :
    Function.Injective (quotientSectionMultiply I f hf n) := by
  intro x y h
  apply Subtype.ext
  exact hreg (congrArg Subtype.val h)

theorem quotientSectionCokernel_finrank_add (I : Ideal (MvPolynomial σ k))
    {d : ℕ} (f : MvPolynomial σ k) (hf : f.IsHomogeneous d)
    (hreg : IsRightRegular (Ideal.Quotient.mk I f)) (n : ℕ) :
    Module.finrank k
        (quotientSection I (n + d) ⧸
          LinearMap.range (quotientSectionMultiply I f hf n)) +
      Module.finrank k (quotientSection I n) =
      Module.finrank k (quotientSection I (n + d)) := by
  have hi := quotientSectionMultiply_injective I f hf hreg n
  simpa only [LinearMap.finrank_range_of_inj hi] using
    (LinearMap.range (quotientSectionMultiply I f hf n)).finrank_quotient_add_finrank

end PiExponentJets.W64

end OAI
end Source0166

-- Source: OAI/NumberTheory/PiExponent/LocalAlgebra/PrimeHilbertDegree.lean
section Source0167
/-
Modification notice for the LogTwo project.
Derived from openai/math (Apache-2.0), revision adc7f1241b42e322a6451854ab7e4b4c146bf78a.
Original source: lean/OAI/NumberTheory/PiExponent/LocalAlgebra/PrimeHilbertDegree.lean
Changes: Convert module/import declarations to the Lean 4.34 public module format.
See ../THIRD_PARTY_NOTICES.txt for provenance and the recorded changes.
-/

namespace OAI

namespace PiExponentJets.W27

open scoped BigOperators
open Filter Polynomial
open PiExponentJets.W64

variable {k σ : Type*} [Field k] [Fintype σ]

theorem prime_quotientSection_finrank_pos
    (P : Ideal (MvPolynomial σ k)) [hP : P.IsPrime]
    (i : σ) (hi : MvPolynomial.X i ∉ P) (n : ℕ) :
    0 < Module.finrank k (quotientSection P n) := by
  let : Module.IsTorsionFree k (quotientSection P n) :=
    DivisionSemiring.to_moduleIsTorsionFree
  apply Module.finrank_pos_iff_exists_ne_zero.mpr
  let x : quotientSection P n :=
    ⟨Ideal.Quotient.mk P (MvPolynomial.X i ^ n),
      Submodule.mem_map.mpr ⟨MvPolynomial.X i ^ n,
        MvPolynomial.isHomogeneous_X_pow i n, rfl⟩⟩
  refine ⟨x, ?_⟩
  intro hx
  have hx' : Ideal.Quotient.mk P (MvPolynomial.X i ^ n) = 0 :=
    congrArg Subtype.val hx
  exact hi (hP.mem_of_pow_mem n (Ideal.Quotient.eq_zero_iff_mem.mp hx'))

theorem polynomial_leadingCoeff_nonneg_of_eventually_nonneg
    (p : Polynomial ℚ) (N : ℕ)
    (hp : ∀ n : ℕ, N ≤ n → 0 ≤ p.eval (n : ℚ)) :
    0 ≤ p.leadingCoeff := by
  by_cases hd : p.natDegree = 0
  · have he : p = Polynomial.C p.leadingCoeff := by
      simpa [Polynomial.leadingCoeff, hd] using Polynomial.eq_C_of_natDegree_eq_zero hd
    have hconst := hp N le_rfl
    rw [he, Polynomial.eval_C] at hconst
    exact hconst
  · by_contra hneg
    have hneg' : p.leadingCoeff < 0 := lt_of_not_ge hneg
    have hdeg : 0 < p.degree := Polynomial.natDegree_pos_iff_degree_pos.mp (Nat.pos_of_ne_zero hd)
    have ht : Tendsto (fun n : ℕ => p.eval (n : ℚ)) atTop atBot :=
      (p.tendsto_atBot_of_leadingCoeff_nonpos hdeg hneg'.le).comp
        tendsto_natCast_atTop_atTop
    obtain ⟨n, hnN, hn⟩ := ((eventually_ge_atTop N).and
      (ht.eventually_lt_atBot 0)).exists
    exact (not_lt_of_ge (hp n hnN)) hn

theorem polynomial_leadingCoeff_pos_of_eventually_pos
    (p : Polynomial ℚ) (N : ℕ)
    (hp : ∀ n : ℕ, N ≤ n → 0 < p.eval (n : ℚ)) :
    0 < p.leadingCoeff := by
  have hn := polynomial_leadingCoeff_nonneg_of_eventually_nonneg p N
    (fun n hn => (hp n hn).le)
  have hp0 : p ≠ 0 := by
    intro h
    simpa [h] using hp N le_rfl
  exact lt_of_le_of_ne hn (Polynomial.leadingCoeff_ne_zero.mpr hp0).symm

theorem factorial_leadingCoeff_is_integer
    (p : Polynomial ℚ) (values : ℕ → ℕ) (N : ℕ)
    (hp : ∀ n : ℕ, N ≤ n → p.eval (n : ℚ) = (values n : ℚ)) :
    ∃ z : ℤ, (z : ℚ) = p.leadingCoeff * (p.natDegree.factorial : ℚ) := by
  let d := p.natDegree
  let z : ℤ := ∑ j ∈ Finset.range (d + 1),
    ((-1 : ℤ) ^ (d-j) * (d.choose j : ℤ)) * (values (N+j) : ℤ)
  refine ⟨z, ?_⟩
  have hd := congrFun p.fwdDiff_iter_degree_eq_factorial (N : ℚ)
  rw [fwdDiff_iter_eq_sum_shift] at hd
  have he (j : ℕ) : p.eval ((N : ℚ) + j • (1 : ℚ)) = (values (N+j) : ℚ) := by
    simpa using hp (N+j) (Nat.le_add_right N j)
  simp only [he] at hd
  simpa [z, d, Int.cast_sum, Int.cast_mul, Int.cast_pow, zsmul_eq_mul,
    Pi.smul_apply, smul_eq_mul] using hd

theorem eventual_hilbert_degree_ge_one
    (p : Polynomial ℚ) (values : ℕ → ℕ) (N : ℕ)
    (hp : ∀ n : ℕ, N ≤ n → p.eval (n : ℚ) = (values n : ℚ))
    (hv : ∀ n : ℕ, N ≤ n → 0 < values n) :
    1 ≤ p.leadingCoeff * (p.natDegree.factorial : ℚ) := by
  have hl := polynomial_leadingCoeff_pos_of_eventually_pos p N (by
    intro n hn
    rw [hp n hn]
    exact_mod_cast hv n hn)
  have hpos : 0 < p.leadingCoeff * (p.natDegree.factorial : ℚ) :=
    mul_pos hl (by exact_mod_cast Nat.factorial_pos p.natDegree)
  obtain ⟨z, hz⟩ := factorial_leadingCoeff_is_integer p values N hp
  have hzpos : 0 < z := by exact_mod_cast (hz.symm ▸ hpos)
  have hzge : (1 : ℤ) ≤ z := by omega
  rw [← hz]
  exact_mod_cast hzge

theorem prime_eventual_hilbert_degree_ge_one
    (P : Ideal (MvPolynomial σ k)) [P.IsPrime]
    (i : σ) (hi : MvPolynomial.X i ∉ P)
    (p : Polynomial ℚ) (N : ℕ)
    (hp : ∀ n : ℕ, N ≤ n → p.eval (n : ℚ) =
      (Module.finrank k (quotientSection P n) : ℚ)) :
    1 ≤ p.leadingCoeff * (p.natDegree.factorial : ℚ) :=
  eventual_hilbert_degree_ge_one p _ N hp
    (fun n _ => prime_quotientSection_finrank_pos P i hi n)

theorem prime_eventual_hilbert_coefficient_ge_one
    (P : Ideal (MvPolynomial σ k)) [P.IsPrime]
    (i : σ) (hi : MvPolynomial.X i ∉ P)
    (p : Polynomial ℚ) (N d : ℕ)
    (hp : ∀ n : ℕ, N ≤ n → p.eval (n : ℚ) =
      (Module.finrank k (quotientSection P n) : ℚ))
    (hd : p.natDegree = d) :
    1 ≤ p.coeff d * (d.factorial : ℚ) := by
  simpa [Polynomial.leadingCoeff, hd] using
    prime_eventual_hilbert_degree_ge_one P i hi p N hp

end PiExponentJets.W27

end OAI
end Source0167

-- Source: OAI/NumberTheory/PiExponent/LocalAlgebra/HilbertGrowthComparison.lean
section Source0168
/-
Modification notice for the LogTwo project.
Derived from openai/math (Apache-2.0), revision adc7f1241b42e322a6451854ab7e4b4c146bf78a.
Original source: lean/OAI/NumberTheory/PiExponent/LocalAlgebra/HilbertGrowthComparison.lean
Changes: Convert module/import declarations to the Lean 4.34 public module format.
See ../THIRD_PARTY_NOTICES.txt for provenance and the recorded changes.
-/

namespace OAI

namespace PiExponentJets.W24

open Polynomial

theorem natDegree_le_of_eventual_polynomial_le (p q : Polynomial ℚ)
    (hp : 0 < p.leadingCoeff) (N : ℕ)
    (hle : ∀ n : ℕ, N ≤ n → p.eval (n : ℚ) ≤ q.eval (n : ℚ)) :
    p.natDegree ≤ q.natDegree := by
  by_contra hn
  have hdeg : q.degree < p.degree := degree_lt_degree (Nat.lt_of_not_ge hn)
  have hnonneg := W27.polynomial_leadingCoeff_nonneg_of_eventually_nonneg
    (q - p) N (fun n hn => by simpa only [eval_sub] using sub_nonneg.mpr (hle n hn))
  rw [leadingCoeff_sub_of_degree_lt' hdeg] at hnonneg
  exact (not_le_of_gt hp) (neg_nonneg.mp hnonneg)

theorem natDegree_affine_comp_le (p : Polynomial ℚ) (a b : ℚ) :
    (p.comp (C a * X + C b)).natDegree ≤ p.natDegree := by
  have ha : (C a * X + C b : Polynomial ℚ).natDegree ≤ 1 := by
    rw [natDegree_add_C]
    simpa only [natDegree_X] using natDegree_C_mul_le a (X : Polynomial ℚ)
  exact (natDegree_comp_le).trans ((Nat.mul_le_mul_left _ ha).trans_eq (Nat.mul_one _))

theorem natDegree_eq_of_polynomial_growth_bounds
    (q lower upper : Polynomial ℚ) (d : ℕ)
    (hql : 0 < q.leadingCoeff) (hll : 0 < lower.leadingCoeff)
    (hld : lower.natDegree = d) (hud : upper.natDegree ≤ d)
    (a b c e : ℚ) (N : ℕ)
    (hlo : ∀ n : ℕ, N ≤ n → lower.eval (n : ℚ) ≤ q.eval (a * n + b))
    (hup : ∀ n : ℕ, N ≤ n → q.eval (n : ℚ) ≤ upper.eval (c * n + e)) :
    q.natDegree = d := by
  have hlow : lower.natDegree ≤ (q.comp (C a * X + C b)).natDegree :=
    natDegree_le_of_eventual_polynomial_le lower _ hll N (by
      simpa only [eval_comp, eval_add, eval_mul, eval_C, eval_X] using hlo)
  have hupp : q.natDegree ≤ (upper.comp (C c * X + C e)).natDegree :=
    natDegree_le_of_eventual_polynomial_le q _ hql N (by
      simpa only [eval_comp, eval_add, eval_mul, eval_C, eval_X] using hup)
  exact le_antisymm
    (hupp.trans ((natDegree_affine_comp_le upper c e).trans hud))
    (hld ▸ hlow.trans (natDegree_affine_comp_le q a b))

end PiExponentJets.W24

end OAI
end Source0168

-- Source: OAI/NumberTheory/PiExponent/Polynomials/HomogeneousIdealStep.lean
section Source0169
/-
Modification notice for the LogTwo project.
Derived from openai/math (Apache-2.0), revision adc7f1241b42e322a6451854ab7e4b4c146bf78a.
Original source: lean/OAI/NumberTheory/PiExponent/Polynomials/HomogeneousIdealStep.lean
Changes: Convert module/import declarations to the Lean 4.34 public module format.
See ../THIRD_PARTY_NOTICES.txt for provenance and the recorded changes.
-/

namespace OAI

namespace PiExponentJets.W64

attribute [local instance] MvPolynomial.gradedAlgebra

variable {k σ : Type*} [Field k]

theorem homogeneous_mem_step_decomposition
    (I : Ideal (MvPolynomial σ k))
    (hI : I.IsHomogeneous (MvPolynomial.homogeneousSubmodule σ k))
    {d n : ℕ} (f p : MvPolynomial σ k)
    (hf : f.IsHomogeneous d) (hp : p.IsHomogeneous (n + d))
    (hmem : p ∈ Ideal.span {f} ⊔ I) :
    ∃ a : MvPolynomial σ k, a.IsHomogeneous n ∧ p - a * f ∈ I := by
  obtain ⟨a, b, hb, hab⟩ := Ideal.mem_span_singleton_sup.mp hmem
  let aₙ := DirectSum.decompose (MvPolynomial.homogeneousSubmodule σ k) a n
  refine ⟨aₙ.1, aₙ.2, ?_⟩
  have hproj := congrArg
    (GradedRing.proj (MvPolynomial.homogeneousSubmodule σ k) (n + d)) hab
  rw [map_add, GradedRing.proj_apply, GradedRing.proj_apply,
    GradedRing.proj_apply,
    DirectSum.coe_decompose_mul_add_of_right_mem
      (MvPolynomial.homogeneousSubmodule σ k) hf,
    DirectSum.decompose_of_mem_same (MvPolynomial.homogeneousSubmodule σ k) hp] at hproj
  have hb' := (Ideal.IsHomogeneous.mem_iff
    (MvPolynomial.homogeneousSubmodule σ k) hI).mp hb (n + d)
  have heq : p - aₙ.1 * f =
      (DirectSum.decompose (MvPolynomial.homogeneousSubmodule σ k) b (n + d) :
        MvPolynomial σ k) := by
    apply sub_eq_iff_eq_add.mpr
    simpa only [aₙ, add_comm] using hproj.symm
  rw [heq]
  exact hb'

theorem homogeneous_mem_step_of_degree_lt
    (I : Ideal (MvPolynomial σ k))
    (hI : I.IsHomogeneous (MvPolynomial.homogeneousSubmodule σ k))
    {d n : ℕ} (f p : MvPolynomial σ k)
    (hf : f.IsHomogeneous d) (hp : p.IsHomogeneous n) (hnd : n < d)
    (hmem : p ∈ Ideal.span {f} ⊔ I) : p ∈ I := by
  obtain ⟨a, b, hb, hab⟩ := Ideal.mem_span_singleton_sup.mp hmem
  have hproj := congrArg
    (GradedRing.proj (MvPolynomial.homogeneousSubmodule σ k) n) hab
  rw [map_add, GradedRing.proj_apply, GradedRing.proj_apply,
    GradedRing.proj_apply,
    DirectSum.coe_decompose_mul_of_right_mem_of_not_le
      (MvPolynomial.homogeneousSubmodule σ k) hf (Nat.not_le_of_lt hnd),
    zero_add,
    DirectSum.decompose_of_mem_same (MvPolynomial.homogeneousSubmodule σ k) hp] at hproj
  rw [← hproj]
  exact (Ideal.IsHomogeneous.mem_iff
    (MvPolynomial.homogeneousSubmodule σ k) hI).mp hb n

end PiExponentJets.W64

end OAI
end Source0169

-- Source: OAI/NumberTheory/PiExponent/LocalAlgebra/RegularHilbertStep.lean
section Source0170
/-
Modification notice for the LogTwo project.
Derived from openai/math (Apache-2.0), revision adc7f1241b42e322a6451854ab7e4b4c146bf78a.
Original source: lean/OAI/NumberTheory/PiExponent/LocalAlgebra/RegularHilbertStep.lean
Changes: Convert module/import declarations to the Lean 4.34 public module format.
See ../THIRD_PARTY_NOTICES.txt for provenance and the recorded changes.
-/

namespace OAI

namespace PiExponentJets.W64

attribute [local instance] MvPolynomial.gradedAlgebra

variable {k σ : Type*} [Field k]

noncomputable def quotientSectionFactor (I J : Ideal (MvPolynomial σ k))
    (hIJ : I ≤ J) (n : ℕ) : quotientSection I n →ₗ[k] quotientSection J n where
  toFun x := ⟨Ideal.Quotient.factorₐ k hIJ x.1, by
    obtain ⟨p, hp, hpx⟩ := Submodule.mem_map.mp x.2
    change Ideal.Quotient.mk I p = x.1 at hpx
    apply Submodule.mem_map.mpr
    refine ⟨p, hp, ?_⟩
    exact congrArg (Ideal.Quotient.factorₐ k hIJ) hpx⟩
  map_add' x y := by apply Subtype.ext; exact map_add _ _ _
  map_smul' c x := by apply Subtype.ext; exact map_smul _ _ _

theorem quotientSectionFactor_surjective (I J : Ideal (MvPolynomial σ k))
    (hIJ : I ≤ J) (n : ℕ) :
    Function.Surjective (quotientSectionFactor I J hIJ n) := by
  intro y
  obtain ⟨p, hp, hpy⟩ := Submodule.mem_map.mp y.2
  refine ⟨⟨Ideal.Quotient.mk I p, Submodule.mem_map.mpr ⟨p, hp, rfl⟩⟩, ?_⟩
  apply Subtype.ext
  exact hpy

theorem quotientSectionFactor_ker_eq (I : Ideal (MvPolynomial σ k))
    (hI : I.IsHomogeneous (MvPolynomial.homogeneousSubmodule σ k))
    {d : ℕ} (f : MvPolynomial σ k) (hf : f.IsHomogeneous d) (n : ℕ) :
    LinearMap.ker (quotientSectionFactor I (Ideal.span {f} ⊔ I) le_sup_right (n+d)) =
      LinearMap.range (quotientSectionMultiply I f hf n) := by
  ext x
  constructor
  · intro hx
    obtain ⟨p, hp, hpx⟩ := Submodule.mem_map.mp x.2
    change Ideal.Quotient.mk I p = x.1 at hpx
    have hz : Ideal.Quotient.mk (Ideal.span {f} ⊔ I) p = 0 := by
      have hxv := congrArg Subtype.val (LinearMap.mem_ker.mp hx)
      change (Ideal.Quotient.factorₐ k le_sup_right) x.1 = 0 at hxv
      change (Ideal.Quotient.factorₐ k le_sup_right) (Ideal.Quotient.mk I p) = 0
      rw [hpx]
      exact hxv
    have hmem := Ideal.Quotient.eq_zero_iff_mem.mp hz
    obtain ⟨a, ha, hpa⟩ := homogeneous_mem_step_decomposition I hI f p hf hp hmem
    apply LinearMap.mem_range.mpr
    refine ⟨⟨Ideal.Quotient.mk I a, Submodule.mem_map.mpr ⟨a, ha, rfl⟩⟩, ?_⟩
    apply Subtype.ext
    change Ideal.Quotient.mk I a * Ideal.Quotient.mk I f = x.1
    rw [← map_mul]
    have he : Ideal.Quotient.mk I (p - a * f) = 0 :=
      Ideal.Quotient.eq_zero_iff_mem.mpr hpa
    rw [map_sub, sub_eq_zero] at he
    exact he.symm.trans hpx
  · intro hx
    obtain ⟨y, rfl⟩ := LinearMap.mem_range.mp hx
    apply LinearMap.mem_ker.mpr
    apply Subtype.ext
    change (Ideal.Quotient.factorₐ k le_sup_right)
      (y.1 * Ideal.Quotient.mk I f) = 0
    rw [map_mul]
    change (Ideal.Quotient.factorₐ k le_sup_right) y.1 *
      Ideal.Quotient.mk (Ideal.span {f} ⊔ I) f = 0
    have hf0 : Ideal.Quotient.mk (Ideal.span {f} ⊔ I) f = 0 := by
      apply Ideal.Quotient.eq_zero_iff_mem.mpr
      have hinc : Ideal.span {f} ≤ Ideal.span {f} ⊔ I := le_sup_left
      exact hinc (Ideal.subset_span (Set.mem_singleton f))
    rw [hf0, mul_zero]

theorem regular_hilbert_step [Finite σ] (I : Ideal (MvPolynomial σ k))
    (hI : I.IsHomogeneous (MvPolynomial.homogeneousSubmodule σ k))
    {d : ℕ} (f : MvPolynomial σ k) (hf : f.IsHomogeneous d)
    (hreg : IsRightRegular (Ideal.Quotient.mk I f)) (n : ℕ) :
    Module.finrank k (quotientSection (Ideal.span {f} ⊔ I) (n+d)) +
      Module.finrank k (quotientSection I n) =
      Module.finrank k (quotientSection I (n+d)) := by
  have hd := quotientSectionCokernel_finrank_add I f hf hreg n
  rw [← quotientSectionFactor_ker_eq I hI f hf n] at hd
  let e := (quotientSectionFactor I (Ideal.span {f} ⊔ I) le_sup_right (n+d)).quotKerEquivOfSurjective
      (quotientSectionFactor_surjective I (Ideal.span {f} ⊔ I) le_sup_right (n+d))
  rw [e.finrank_eq] at hd
  exact hd

theorem hilbert_step_of_degree_lt (I : Ideal (MvPolynomial σ k))
    (hI : I.IsHomogeneous (MvPolynomial.homogeneousSubmodule σ k))
    {d n : ℕ} (f : MvPolynomial σ k) (hf : f.IsHomogeneous d) (hnd : n < d) :
    Module.finrank k (quotientSection (Ideal.span {f} ⊔ I) n) =
      Module.finrank k (quotientSection I n) := by
  let φ := quotientSectionFactor I (Ideal.span {f} ⊔ I) le_sup_right n
  have hinj : Function.Injective φ := by
    apply LinearMap.ker_eq_bot.mp
    apply le_antisymm ?_ bot_le
    intro x hx
    change x = 0
    obtain ⟨p, hp, hpx⟩ := Submodule.mem_map.mp x.2
    change Ideal.Quotient.mk I p = x.1 at hpx
    have hz : Ideal.Quotient.mk (Ideal.span {f} ⊔ I) p = 0 := by
      have hxv := congrArg Subtype.val (LinearMap.mem_ker.mp hx)
      change (Ideal.Quotient.factorₐ k le_sup_right) x.1 = 0 at hxv
      change (Ideal.Quotient.factorₐ k le_sup_right) (Ideal.Quotient.mk I p) = 0
      rw [hpx]
      exact hxv
    have hpI := homogeneous_mem_step_of_degree_lt I hI f p hf hp hnd
      (Ideal.Quotient.eq_zero_iff_mem.mp hz)
    apply Subtype.ext
    change x.1 = 0
    rw [← hpx]
    exact Ideal.Quotient.eq_zero_iff_mem.mpr hpI
  exact (LinearEquiv.ofBijective φ
    ⟨hinj, quotientSectionFactor_surjective I (Ideal.span {f} ⊔ I) le_sup_right n⟩).finrank_eq.symm

end PiExponentJets.W64

end OAI
end Source0170

-- Source: OAI/NumberTheory/PiExponent/LocalAlgebra/RegularPrefixes.lean
section Source0171
-- Modified in this edition: unused plain lemmas removed; see reduction.json.
/-
Modification notice for the LogTwo project.
Derived from openai/math (Apache-2.0), revision adc7f1241b42e322a6451854ab7e4b4c146bf78a.
Original source: lean/OAI/NumberTheory/PiExponent/LocalAlgebra/RegularPrefixes.lean
Changes: Convert module/import declarations to the Lean 4.34 public module format.
See ../THIRD_PARTY_NOTICES.txt for provenance and the recorded changes.
-/

namespace OAI

namespace PiExponentSiegel.W20

section Ring

variable {R : Type*} [CommRing R]

theorem prefixIdeal_succ (rs : List R) (i : Fin rs.length) :
    Ideal.ofList (rs.take (i.val + 1)) =
      Ideal.span {rs[i]} ⊔ Ideal.ofList (rs.take i.val) := by
  rw [List.take_succ_eq_append_getElem i.isLt, Ideal.ofList_append,
    Ideal.ofList_singleton, sup_comm]
  simp only [Fin.getElem_fin]

theorem regular_next_mod_prefix (rs : List R)
    (hreg : RingTheory.Sequence.IsRegular R rs) (i : Fin rs.length) :
    IsRightRegular (Ideal.Quotient.mk (Ideal.ofList (rs.take i.val)) rs[i]) := by
  have hsmul := hreg.toIsWeaklyRegular.regular_mod_prev i.val i.isLt
  have htop : (Ideal.ofList (rs.take i.val) • (⊤ : Submodule R R)) =
      Ideal.ofList (rs.take i.val) := by
    exact (Ideal.ofList (rs.take i.val)).mul_top
  rw [htop] at hsmul
  intro x y hxy
  apply hsmul
  simpa only [Algebra.smul_def, Ideal.Quotient.algebraMap_eq, mul_comm,
    Fin.getElem_fin] using hxy

end Ring

attribute [local instance] MvPolynomial.gradedAlgebra

variable {k σ : Type*} [Field k] [Finite σ]

omit [Finite σ] in
theorem prefixIdeal_homogeneous
    (rs : List (MvPolynomial σ k)) (degrees : Fin rs.length → ℕ)
    (hhom : ∀ i : Fin rs.length, rs[i].IsHomogeneous (degrees i)) (n : ℕ) :
    (Ideal.ofList (rs.take n)).IsHomogeneous
      (MvPolynomial.homogeneousSubmodule σ k) := by
  apply Ideal.homogeneous_span (MvPolynomial.homogeneousSubmodule σ k)
  intro f hf
  obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.mp (List.mem_of_mem_take hf)
  exact ⟨degrees ⟨i, hi⟩, hhom ⟨i, hi⟩⟩

end PiExponentSiegel.W20

end OAI
end Source0171

-- Source: OAI/NumberTheory/PiExponent/Analysis/HilbertSeries.lean
section Source0172
/-
Modification notice for the LogTwo project.
Derived from openai/math (Apache-2.0), revision adc7f1241b42e322a6451854ab7e4b4c146bf78a.
Original source: lean/OAI/NumberTheory/PiExponent/Analysis/HilbertSeries.lean
Changes: Convert module/import declarations to the Lean 4.34 public module format.
See ../THIRD_PARTY_NOTICES.txt for provenance and the recorded changes.
-/

namespace OAI

namespace PiExponentJets.W64

attribute [local instance] MvPolynomial.gradedAlgebra

variable {k σ : Type*} [Field k] [Finite σ]

noncomputable def sectionHilbertSeries (I : Ideal (MvPolynomial σ k)) : PowerSeries ℤ :=
  PowerSeries.mk (fun n => (Module.finrank k (quotientSection I n) : ℤ))

omit [Finite σ] in
@[simp] theorem coeff_sectionHilbertSeries (I : Ideal (MvPolynomial σ k)) (n : ℕ) :
    PowerSeries.coeff n (sectionHilbertSeries I) =
      (Module.finrank k (quotientSection I n) : ℤ) :=
  PowerSeries.coeff_mk _ _

theorem sectionHilbertSeries_regular_step (I : Ideal (MvPolynomial σ k))
    (hI : I.IsHomogeneous (MvPolynomial.homogeneousSubmodule σ k))
    {d : ℕ} (f : MvPolynomial σ k) (hf : f.IsHomogeneous d)
    (hreg : IsRightRegular (Ideal.Quotient.mk I f)) :
    sectionHilbertSeries (Ideal.span {f} ⊔ I) =
      (1 - PowerSeries.X ^ d) * sectionHilbertSeries I := by
  ext n
  rw [sub_mul, one_mul, map_sub, PowerSeries.coeff_X_pow_mul']
  simp only [coeff_sectionHilbertSeries]
  by_cases hdn : d ≤ n
  · rw [ite_eq_left hdn]
    have h := regular_hilbert_step I hI f hf hreg (n-d)
    rw [Nat.sub_add_cancel hdn] at h
    apply eq_sub_of_add_eq
    exact_mod_cast h
  · rw [ite_eq_right hdn, sub_zero]
    exact congrArg (fun m : ℕ => (m : ℤ))
      (hilbert_step_of_degree_lt I hI f hf (Nat.lt_of_not_ge hdn))

end PiExponentJets.W64

end OAI
end Source0172

-- Source: OAI/NumberTheory/PiExponent/Polynomials/HilbertPolynomialBase.lean
section Source0173
/-
Modification notice for the LogTwo project.
Derived from openai/math (Apache-2.0), revision adc7f1241b42e322a6451854ab7e4b4c146bf78a.
Original source: lean/OAI/NumberTheory/PiExponent/Polynomials/HilbertPolynomialBase.lean
Changes: Convert module/import declarations to the Lean 4.34 public module format.
See ../THIRD_PARTY_NOTICES.txt for provenance and the recorded changes.
-/

namespace OAI

namespace PiExponentJets.W64

variable {σ : Type*}

noncomputable def exponentDegreeEquivSym (n : ℕ) :
    {d : σ →₀ ℕ | d.degree = n} ≃ Sym σ n := by
  classical
  exact
    { toFun := fun d => ⟨d.1.toMultiset, by
        rw [Finsupp.card_toMultiset]
        exact d.2⟩
      invFun := fun m => ⟨Multiset.toFinsupp m.1, by
        have hc := Finsupp.card_toMultiset (Multiset.toFinsupp m.1)
        rw [Multiset.toFinsupp_toMultiset] at hc
        change (Multiset.toFinsupp m.1).degree = n
        exact hc.symm.trans m.2⟩
      left_inv := fun d => Subtype.ext (Multiset.toFinsupp.apply_symm_apply d.1)
      right_inv := fun m => Subtype.ext (Multiset.toFinsupp.symm_apply_apply m.1) }

theorem card_exponents_degree [Fintype σ] (n : ℕ) :
    Nat.card {d : σ →₀ ℕ | d.degree = n} = (Fintype.card σ).multichoose n := by
  classical
  rw [Nat.card_congr (exponentDegreeEquivSym n), Nat.card_eq_fintype_card]
  exact Sym.card_sym_eq_multichoose σ n

variable {k : Type*} [Field k] [Finite σ]

omit [Finite σ] in
theorem quotientSection_bot_finrank (n : ℕ) :
    Module.finrank k (quotientSection (⊥ : Ideal (MvPolynomial σ k)) n) =
      Module.finrank k (MvPolynomial.homogeneousSubmodule σ k n) := by
  let e := LinearEquiv.ofBijective
    (Ideal.Quotient.mkₐ k (⊥ : Ideal (MvPolynomial σ k))).toLinearMap
    ((Ideal.Quotient.mk_bijective_iff_eq_bot (⊥ : Ideal (MvPolynomial σ k))).mpr rfl)
  exact e.finrank_map_eq (MvPolynomial.homogeneousSubmodule σ k n)

theorem quotientSection_bot_finrank_multichoose [Fintype σ] (n : ℕ) :
    Module.finrank k (quotientSection (⊥ : Ideal (MvPolynomial σ k)) n) =
      (Fintype.card σ).multichoose n := by
  rw [quotientSection_bot_finrank, homogeneousSection_finrank, card_exponents_degree]

theorem sectionHilbertSeries_bot [Fintype σ] (hσ : 0 < Fintype.card σ) :
    sectionHilbertSeries (⊥ : Ideal (MvPolynomial σ k)) =
      (PowerSeries.invOneSubPow ℤ (Fintype.card σ)).val := by
  rw [PowerSeries.invOneSubPow_val_eq_mk_sub_one_add_choose_of_pos ℤ (Fintype.card σ) hσ]
  ext n
  rw [coeff_sectionHilbertSeries, PowerSeries.coeff_mk,
    quotientSection_bot_finrank_multichoose, Nat.multichoose_eq]
  congr 1
  have hs : Fintype.card σ + n - 1 = (Fintype.card σ - 1) + n := by omega
  rw [hs]
  exact Nat.choose_symm_add.symm

end PiExponentJets.W64

end OAI
end Source0173

-- Source: OAI/NumberTheory/PiExponent/Analysis/RegularSequenceSeries.lean
section Source0174
-- Modified in this edition: unused plain lemmas removed; see reduction.json.
/-
Modification notice for the LogTwo project.
Derived from openai/math (Apache-2.0), revision adc7f1241b42e322a6451854ab7e4b4c146bf78a.
Original source: lean/OAI/NumberTheory/PiExponent/Analysis/RegularSequenceSeries.lean
Changes: Convert module/import declarations to the Lean 4.34 public module format.
See ../THIRD_PARTY_NOTICES.txt for provenance and the recorded changes.
-/

namespace OAI

namespace PiExponentJets.W64

open scoped BigOperators
attribute [local instance] MvPolynomial.gradedAlgebra

variable {k σ : Type*} [Field k] [Finite σ]

noncomputable def degreeAt {m : ℕ} (degrees : Fin m → ℕ) (i : ℕ) : ℕ :=
  if hi : i < m then degrees ⟨i, hi⟩ else 0

theorem regular_prefix_series
    (rs : List (MvPolynomial σ k)) (degrees : Fin rs.length → ℕ)
    (hhom : ∀ i : Fin rs.length, rs[i].IsHomogeneous (degrees i))
    (hreg : RingTheory.Sequence.IsRegular (MvPolynomial σ k) rs)
    (n : ℕ) (hn : n ≤ rs.length) :
    sectionHilbertSeries (Ideal.ofList (rs.take n)) =
      (∏ i ∈ Finset.range n, (1 - PowerSeries.X ^ degreeAt degrees i)) *
        sectionHilbertSeries (⊥ : Ideal (MvPolynomial σ k)) := by
  induction n with
  | zero => simp
  | succ n ih =>
    have hlt : n < rs.length := hn
    have hn' : n ≤ rs.length := Nat.le_of_lt hlt
    rw [PiExponentSiegel.W20.prefixIdeal_succ rs ⟨n, hlt⟩]
    simp only [Fin.getElem_fin]
    have hh : (rs[n]'hlt).IsHomogeneous (degrees ⟨n, hlt⟩) := by
      simpa only [Fin.getElem_fin] using hhom ⟨n, hlt⟩
    have hr : IsRightRegular (Ideal.Quotient.mk (Ideal.ofList (rs.take n)) (rs[n]'hlt)) := by
      simpa only [Fin.getElem_fin] using
        PiExponentSiegel.W20.regular_next_mod_prefix rs hreg ⟨n, hlt⟩
    rw [sectionHilbertSeries_regular_step _
      (PiExponentSiegel.W20.prefixIdeal_homogeneous rs degrees hhom n)
      (rs[n]'hlt) hh hr]
    rw [ih hn', Finset.prod_range_succ]
    simp only [degreeAt, dite_eq_left hlt]
    ac_rfl

theorem degree_factors_mul_invOneSubPow (D : ℕ → ℕ) (m : ℕ) :
    (∏ i ∈ Finset.range m, (1 - (PowerSeries.X : PowerSeries ℤ) ^ D i)) *
      (PowerSeries.invOneSubPow ℤ m).val =
      ∏ i ∈ Finset.range m, ∑ j ∈ Finset.range (D i),
        (PowerSeries.X : PowerSeries ℤ) ^ j := by
  have hfactor :
      (∏ i ∈ Finset.range m, (1 - (PowerSeries.X : PowerSeries ℤ) ^ D i)) =
        (∏ i ∈ Finset.range m, ∑ j ∈ Finset.range (D i),
          (PowerSeries.X : PowerSeries ℤ) ^ j) * (1 - PowerSeries.X) ^ m := by
    simp_rw [← geom_sum_mul_neg]
    rw [Finset.prod_mul_distrib]
    simp
  rw [hfactor, mul_assoc, ← PowerSeries.invOneSubPow_inv_eq_one_sub_pow]
  rw [(PowerSeries.invOneSubPow ℤ m).inv_val, mul_one]

end PiExponentJets.W64

end OAI
end Source0174

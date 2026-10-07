module
public import Mathlib
@[expose] public section

section Source0000
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

theorem homogeneousCokernel_finrank_add {d : ℕ} (f : MvPolynomial σ k)
    (hf : f.IsHomogeneous d) (hf0 : f ≠ 0) (n : ℕ) :
    Module.finrank k
        (MvPolynomial.homogeneousSubmodule σ k (n + d) ⧸
          LinearMap.range (homogeneousMultiply f hf n)) +
      Module.finrank k (MvPolynomial.homogeneousSubmodule σ k n) =
      Module.finrank k (MvPolynomial.homogeneousSubmodule σ k (n + d)) := by
  have hi := homogeneousMultiply_injective f hf hf0 n
  simpa only [LinearMap.finrank_range_of_inj hi] using
    (LinearMap.range (homogeneousMultiply f hf n)).finrank_quotient_add_finrank

end PiExponentJets.W64

end OAI
end Source0000

section Source0001
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
end Source0001

section Source0002
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
end Source0002

section Source0003
namespace OAI

namespace PiExponentJets.W22

open scoped BigOperators

variable {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]

theorem length_filtration_step (A B : Submodule R M) (hAB : A ≤ B) :
    Module.length R B = Module.length R A + Module.length R (B ⧸ A.submoduleOf B) := by
  have h := Module.length_eq_add_of_exact (A.submoduleOf B).subtype
    (A.submoduleOf B).mkQ (Submodule.subtype_injective _)
    (Submodule.mkQ_surjective _) (LinearMap.exact_subtype_mkQ _)
  rw [(Submodule.submoduleOfEquivOfLe hAB).length_eq] at h
  exact h

theorem length_eq_sum_filtration
    (N : ℕ → Submodule R M) (hmono : ∀ i, N i ≤ N (i + 1))
    (hzero : N 0 = ⊥) (n : ℕ) :
    Module.length R (N n) =
      ∑ i ∈ Finset.range n, Module.length R (N (i + 1) ⧸ (N i).submoduleOf (N (i + 1))) := by
  induction n with
  | zero =>
    simp only [Finset.range_zero, Finset.sum_empty]
    have hlen := congrArg (fun A : Submodule R M => Module.length R A) hzero
    exact hlen.trans Module.length_eq_zero
  | succ n ih =>
    rw [length_filtration_step (N n) (N (n + 1)) (hmono n), ih,
      Finset.sum_range_succ]

theorem module_length_eq_sum_filtration
    (N : ℕ → Submodule R M) (hmono : ∀ i, N i ≤ N (i + 1))
    (hzero : N 0 = ⊥) (n : ℕ) (htop : N n = ⊤) :
    Module.length R M =
      ∑ i ∈ Finset.range n, Module.length R (N (i + 1) ⧸ (N i).submoduleOf (N (i + 1))) := by
  have hlen := congrArg (fun A : Submodule R M => Module.length R A) htop
  have hlen' : Module.length R (N n) = Module.length R M :=
    hlen.trans Module.length_top
  exact hlen'.symm.trans (length_eq_sum_filtration N hmono hzero n)

end PiExponentJets.W22

end OAI
end Source0003

section Source0004
namespace OAI

namespace PiExponentJets.W22

open scoped Classical BigOperators

variable {R : Type*} [CommRing R]

theorem map_ideal_eq_top_of_not_le
    (P Q : Ideal R) [Q.IsPrime] (hPQ : ¬ P ≤ Q) :
    P.map (algebraMap R (Localization.AtPrime Q)) = ⊤ := by
  obtain ⟨x, hxP, hxQ⟩ := IsConcreteLe.not_le_iff_exists.mp hPQ
  have hu : IsUnit (algebraMap R (Localization.AtPrime Q) x) :=
    (IsLocalization.AtPrime.isUnit_to_map_iff (Localization.AtPrime Q) Q x).mpr hxQ
  exact Ideal.eq_top_of_isUnit_mem _ (Ideal.mem_map_of_mem _ hxP) hu

theorem localized_prime_factor_length_zero
    (P Q : Ideal R) [Q.IsPrime] (hPQ : ¬ P ≤ Q) :
    Module.length (Localization.AtPrime Q)
      (Localization.AtPrime Q ⧸ P.map (algebraMap R (Localization.AtPrime Q))) = 0 := by
  rw [map_ideal_eq_top_of_not_le P Q hPQ]
  exact Module.length_eq_zero

theorem localized_prime_factor_length_one
    (Q : Ideal R) [Q.IsPrime] :
    Module.length (Localization.AtPrime Q)
      (Localization.AtPrime Q ⧸ Q.map (algebraMap R (Localization.AtPrime Q))) = 1 := by
  rw [Localization.AtPrime.map_eq_maximalIdeal]
  let : IsSimpleModule (Localization.AtPrime Q)
      (Localization.AtPrime Q ⧸ IsLocalRing.maximalIdeal (Localization.AtPrime Q)) :=
    isSimpleModule_iff_isCoatom.mpr (Ideal.isMaximal_def.mp inferInstance)
  exact Module.length_eq_one _ _

theorem prime_not_le_of_ne_minimal
    (I P Q : Ideal R) [P.IsPrime]
    (hQ : Q ∈ I.minimalPrimes) (hIP : I ≤ P) (hne : P ≠ Q) : ¬ P ≤ Q := by
  intro hPQ
  exact hne (le_antisymm hPQ (hQ.2 ⟨inferInstance, hIP⟩ hPQ))

theorem localized_prime_factor_length
    (I P Q : Ideal R) [P.IsPrime] [Q.IsPrime]
    (hQ : Q ∈ I.minimalPrimes) (hIP : I ≤ P) :
    Module.length (Localization.AtPrime Q)
      (Localization.AtPrime Q ⧸ P.map (algebraMap R (Localization.AtPrime Q))) =
      if P = Q then 1 else 0 := by
  classical
  by_cases hPQ : P = Q
  · subst P
    simpa only [ite_true] using localized_prime_factor_length_one Q
  · rw [ite_eq_right hPQ]
    exact localized_prime_factor_length_zero P Q
      (prime_not_le_of_ne_minimal I P Q hQ hIP hPQ)

theorem local_component_length_eq_prime_factor_count
    (I Q : Ideal R) [Q.IsPrime] (hQ : Q ∈ I.minimalPrimes)
    (N : ℕ → Submodule (Localization.AtPrime Q)
      (Localization.AtPrime Q ⧸ I.map (algebraMap R (Localization.AtPrime Q))))
    (hmono : ∀ i, N i ≤ N (i + 1)) (hzero : N 0 = ⊥)
    (n : ℕ) (htop : N n = ⊤)
    (P : ℕ → Ideal R) [∀ i, (P i).IsPrime]
    (hIP : ∀ i < n, I ≤ P i)
    (e : ∀ i < n,
      (N (i + 1) ⧸ (N i).submoduleOf (N (i + 1))) ≃ₗ[Localization.AtPrime Q]
        (Localization.AtPrime Q ⧸ (P i).map (algebraMap R (Localization.AtPrime Q)))) :
    Module.length (Localization.AtPrime Q)
      (Localization.AtPrime Q ⧸ I.map (algebraMap R (Localization.AtPrime Q))) =
      ∑ i ∈ Finset.range n, if P i = Q then 1 else 0 := by
  rw [module_length_eq_sum_filtration N hmono hzero n htop]
  apply Finset.sum_congr rfl
  intro i hi
  rw [(e i (Finset.mem_range.mp hi)).length_eq]
  exact localized_prime_factor_length I (P i) Q hQ (hIP i (Finset.mem_range.mp hi))

end PiExponentJets.W22

end OAI
end Source0004

section Source0005
namespace OAI

namespace PiExponentJets.W24

section OrderLifting

variable {α β : Type*} [PartialOrder α] [PartialOrder β]

theorem exists_chain_lift_last (f : α → β) (hs : Function.Surjective f)
    (hu : ∀ a b, f a < b → ∃ a', a < a' ∧ f a' = b)
    (p : LTSeries β) :
    ∃ q : LTSeries α, q.length = p.length ∧ f q.last = p.last := by
  induction p using RelSeries.inductionOn' with
  | singleton b =>
      obtain ⟨a, ha⟩ := hs b
      exact ⟨RelSeries.singleton _ a, rfl, ha⟩
  | snoc p b hb ih =>
      obtain ⟨q, hlen, hlast⟩ := ih
      obtain ⟨a, ha, hab⟩ := hu q.last b (hlast.symm ▸ hb)
      refine ⟨q.snoc a ha, ?_, ?_⟩
      · simp only [RelSeries.snoc_length, hlen]
      · simpa only [RelSeries.last_snoc] using hab

theorem krullDim_le_of_goingUp (f : α → β) (hs : Function.Surjective f)
    (hu : ∀ a b, f a < b → ∃ a', a < a' ∧ f a' = b) :
    Order.krullDim β ≤ Order.krullDim α := by
  unfold Order.krullDim
  refine iSup_le fun p => ?_
  obtain ⟨q, hlen, _⟩ := exists_chain_lift_last f hs hu p
  exact hlen ▸ le_iSup (fun q : LTSeries α => (q.length : WithBot ℕ∞)) q

end OrderLifting

section IntegralDimension

variable {A B : Type*} [CommRing A] [CommRing B]

theorem ringKrullDim_eq_of_integral_injective (f : A →+* B)
    (hf : Function.Injective f) (hi : f.IsIntegral) :
    ringKrullDim B = ringKrullDim A := by
  let : Algebra A B := f.toAlgebra
  have : Algebra.IsIntegral A B := ⟨hi⟩
  let c : PrimeSpectrum B → PrimeSpectrum A :=
    fun p => ⟨p.asIdeal.comap f, inferInstance⟩
  have hc : StrictMono c := by
    intro p q hpq
    obtain ⟨hpq', x, hxq, hxp⟩ := IsConcreteLe.lt_iff_le_and_exists.mp (show p.asIdeal < q.asIdeal from hpq)
    exact Ideal.under_lt_under_of_integral_mem_sdiff hpq' ⟨hxq, hxp⟩
      (Algebra.IsIntegral.isIntegral x)
  have hs : Function.Surjective c := by
    intro p
    obtain ⟨q, _, hq, hqp⟩ := Ideal.exists_ideal_over_prime_of_isIntegral
      p.asIdeal (⊥ : Ideal B) (by
        change RingHom.ker f ≤ p.asIdeal
        rw [(RingHom.injective_iff_ker_eq_bot f).mp hf]
        exact bot_le)
    exact ⟨⟨q, hq⟩, PrimeSpectrum.ext hqp⟩
  have hu : ∀ a b, c a < b → ∃ a', a < a' ∧ c a' = b := by
    intro a b hab
    obtain ⟨q, haq, hq, hqb⟩ :=
      Ideal.exists_ideal_over_prime_of_isIntegral_of_isPrime b.asIdeal a.asIdeal hab.le
    refine ⟨⟨q, hq⟩, lt_of_le_of_ne haq ?_, PrimeSpectrum.ext hqb⟩
    intro heq
    have he : c a = b := by
      rw [heq]
      exact PrimeSpectrum.ext hqb
    exact hab.ne he
  exact le_antisymm (Order.krullDim_le_of_strictMono c hc)
    (krullDim_le_of_goingUp c hs hu)

end IntegralDimension

variable (k R : Type*) [Field k] [CommRing R] [Nontrivial R] [Algebra k R]
  [Algebra.FiniteType k R]

theorem exists_finite_normalization_with_dimension :
    ∃ s : ℕ, ∃ g : MvPolynomial (Fin s) k →ₐ[k] R,
      Function.Injective g ∧ g.Finite ∧ ringKrullDim R = (s : WithBot ℕ∞) := by
  obtain ⟨s, g, hg, hfin⟩ := exists_finite_inj_algHom_of_fg k R
  refine ⟨s, g, hg, hfin, ?_⟩
  have hd := ringKrullDim_eq_of_integral_injective g.toRingHom hg hfin.to_isIntegral
  simpa only [MvPolynomial.ringKrullDim_of_isNoetherianRing,
    ringKrullDim_eq_zero_of_field, ENat.card_eq_coe_natCard, Nat.card_fin, zero_add, WithBot.coe_natCast] using hd

end PiExponentJets.W24

end OAI
end Source0005

section Source0006
namespace OAI

noncomputable section
universe w v u

namespace PiExponentSiegelAux.W31
open Module
open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian
open HomologicalComplex

section General
variable {C : Type u} [Category.{v} C] [Abelian C]

def projectiveResolutionOfExact (P : ChainComplex C ℕ) (M : C)
    (ε : P.X 0 ⟶ M) (hε : P.d 1 0 ≫ ε = 0)
    (hzero : (ShortComplex.mk (P.d 1 0) ε hε).Exact)
    (hepi : Epi ε) (hexact : ∀ n : ℕ, P.ExactAt (n + 1))
    (hproj : ∀ n : ℕ, CategoryTheory.Projective (P.X n)) :
    CategoryTheory.ProjectiveResolution M where
  complex := P
  projective := hproj
  π := (ChainComplex.toSingle₀Equiv P M).symm ⟨ε, hε⟩
  quasiIso := ⟨fun n => by
    cases n with
    | zero =>
      rw [ChainComplex.quasiIsoAt₀_iff,
        ShortComplex.quasiIso_iff_of_zeros' _ (by simp) (by simp)
          (by simp)]
      simpa [ChainComplex.toSingle₀Equiv] using! And.intro hzero hepi
    | succ n =>
      rw [quasiIsoAt_iff_exactAt' (hL := ChainComplex.exactAt_succ_single_obj ..)]
      exact hexact n⟩

theorem projectiveResolutionOfExact_complex (P : ChainComplex C ℕ) (M : C)
    (ε : P.X 0 ⟶ M) (hε : P.d 1 0 ≫ ε = 0)
    (hzero : (ShortComplex.mk (P.d 1 0) ε hε).Exact)
    (hepi : Epi ε) (hexact : ∀ n : ℕ, P.ExactAt (n + 1))
    (hproj : ∀ n : ℕ, CategoryTheory.Projective (P.X n)) :
    (projectiveResolutionOfExact P M ε hε hzero hepi hexact hproj).complex = P := rfl

variable [HasExt.{w} C]

def resolutionExtAddEquiv (M Y : C) (P : ProjectiveResolution M) (n : ℕ) :
    Ext M Y n ≃+
      CochainComplex.HomComplex.CohomologyClass P.cochainComplex
        ((CochainComplex.singleFunctor C 0).obj Y) n :=
  P.extAddEquivCohomologyClass

theorem ext_subsingleton_iff_cocycles_are_boundaries
    (M Y : C) (P : ProjectiveResolution M) (n : ℕ) :
    Subsingleton (Ext M Y (n + 1)) ↔
      ∀ (f : P.complex.X (n + 1) ⟶ Y),
        P.complex.d (n + 2) (n + 1) ≫ f = 0 →
        ∃ g : P.complex.X n ⟶ Y, P.complex.d (n + 1) n ≫ g = f := by
  constructor
  · intro h f hf
    exact (P.extMk_eq_zero_iff f (n + 2) rfl hf n rfl).mp
      (h.elim _ 0)
  · intro h
    apply subsingleton_of_forall_eq 0
    intro e
    obtain ⟨f, hf, rfl⟩ := P.extMk_surjective e (n + 2) rfl
    exact (P.extMk_eq_zero_iff f (n + 2) rfl hf n rfl).mpr (h f hf)

theorem ext_subsingleton_of_isZero_resolution_term
    (M Y : C) (P : ProjectiveResolution M) (n : ℕ)
    (hterm : IsZero (P.complex.X n)) : Subsingleton (Ext M Y n) := by
  apply subsingleton_of_forall_eq 0
  intro e
  obtain ⟨f, hf, rfl⟩ := P.extMk_surjective e (n + 1) rfl
  have hfzero : f = 0 := hterm.eq_of_src f 0
  subst f
  exact P.extMk_zero (n + 1) rfl

end General

variable {R : Type u} [CommRing R]

theorem module_exactAt_succ_of_range_eq_ker (P : ChainComplex (ModuleCat.{u} R) ℕ)
    (n : ℕ)
    (h : LinearMap.range (P.d (n + 2) (n + 1)).hom =
      LinearMap.ker (P.d (n + 1) n).hom) : P.ExactAt (n + 1) := by
  rw [HomologicalComplex.exactAt_iff' _ (n + 2) (n + 1) n (by simp) (by simp)]
  rw [ShortComplex.moduleCat_exact_iff_range_eq_ker]
  exact h

def finiteFreeResolutionOfExact (P : ChainComplex (ModuleCat.{u} R) ℕ)
    (M : ModuleCat.{u} R) (ε : P.X 0 ⟶ M) (hε : P.d 1 0 ≫ ε = 0)
    (hzero : LinearMap.range (P.d 1 0).hom = LinearMap.ker ε.hom)
    (hepi : Function.Surjective ε.hom)
    (hexact : ∀ n : ℕ, LinearMap.range (P.d (n + 2) (n + 1)).hom =
      LinearMap.ker (P.d (n + 1) n).hom)
    (rank : ℕ → ℕ) (basis : ∀ n : ℕ, Basis (Fin (rank n)) R (P.X n)) :
    ProjectiveResolution M :=
  projectiveResolutionOfExact P M ε hε
    ((ShortComplex.moduleCat_exact_iff_range_eq_ker _).mpr hzero)
    ((ModuleCat.epi_iff_surjective ε).mpr hepi)
    (fun n => module_exactAt_succ_of_range_eq_ker P n (hexact n))
    (fun n => ModuleCat.projective_of_free (basis n))

def moduleFreeResolutionOfExact (P : ChainComplex (ModuleCat.{u} R) ℕ)
    (M : ModuleCat.{u} R) (ε : P.X 0 ⟶ M) (hε : P.d 1 0 ≫ ε = 0)
    (hzero : LinearMap.range (P.d 1 0).hom = LinearMap.ker ε.hom)
    (hepi : Function.Surjective ε.hom)
    (hexact : ∀ n : ℕ, LinearMap.range (P.d (n + 2) (n + 1)).hom =
      LinearMap.ker (P.d (n + 1) n).hom)
    (hfree : ∀ n : ℕ, Module.Free R (P.X n)) : ProjectiveResolution M :=
  projectiveResolutionOfExact P M ε hε
    ((ShortComplex.moduleCat_exact_iff_range_eq_ker _).mpr hzero)
    ((ModuleCat.epi_iff_surjective ε).mpr hepi)
    (fun n => module_exactAt_succ_of_range_eq_ker P n (hexact n))
    (fun n => by
      let := hfree n
      exact ModuleCat.projective_of_free (Module.Free.chooseBasis R (P.X n)))

end PiExponentSiegelAux.W31

end

end OAI
end Source0006

#print axioms OAI.PiExponentJets.W27.prime_quotientSection_finrank_pos
#print axioms OAI.PiExponentSiegelAux.W31.projectiveResolutionOfExact

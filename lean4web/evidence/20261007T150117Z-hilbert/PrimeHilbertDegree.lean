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
  letI : Module.IsTorsionFree k (quotientSection P n) :=
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

#print axioms OAI.PiExponentJets.W27.prime_quotientSection_finrank_pos

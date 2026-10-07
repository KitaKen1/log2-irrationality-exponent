/- Generated rc4 checkpoint for LogTwo.
Modified from the reduced edition: new imports, separate module compilation,
and synchronous elaboration. Original source blocks and notices are retained.
See ../../../THIRD_PARTY_NOTICES.txt and ../../reduction.json.
-/
module
public import LogTwoCheckpoints.Part001
public import LogTwoCheckpoints.Part003
public import LogTwoCheckpoints.Part004
public import Mathlib.Analysis.Complex.Polynomial.Basic
public import Mathlib.Data.FunLike.Basic
public import Mathlib.FieldTheory.SeparablyGenerated
public import Mathlib.RingTheory.GradedAlgebra.Radical
public import Mathlib.RingTheory.Ideal.KrullsHeightTheorem
public import Mathlib.RingTheory.KrullDimension.Polynomial
public import Mathlib.RingTheory.LocalRing.Length
public import Mathlib.RingTheory.LocalRing.ResidueField.Instances
public import Mathlib.RingTheory.Regular.Flat
public import Mathlib.RingTheory.Unramified.LocalRing
public import Mathlib.Tactic
@[expose] public section
set_option Elab.async false

-- Source: OAI/NumberTheory/PiExponent/LocalAlgebra/WeightedBezout.lean
section Source0125
-- Modified in this edition: unused plain lemmas removed; see reduction.json.
/-
Modification notice for the LogTwo project.
Derived from openai/math (Apache-2.0), revision adc7f1241b42e322a6451854ab7e4b4c146bf78a.
Original source: lean/OAI/NumberTheory/PiExponent/LocalAlgebra/WeightedBezout.lean
Changes: Convert module/import declarations to the Lean 4.34 public module format.
See ../THIRD_PARTY_NOTICES.txt for provenance and the recorded changes.
-/

namespace OAI

namespace PiExponent.WeightedBezout

open scoped BigOperators

variable {k σ τ : Type*} [Field k]

noncomputable def translatedPowerSubstitution (w : σ → ℕ) (a : σ → k) :
    MvPolynomial σ k →ₐ[k] MvPolynomial σ k :=
  MvPolynomial.aeval (fun i => MvPolynomial.C (a i) + MvPolynomial.X i ^ w i)

@[simp] theorem translatedPowerSubstitution_X (w : σ → ℕ) (a : σ → k) (i : σ) :
    translatedPowerSubstitution w a (MvPolynomial.X i) =
      MvPolynomial.C (a i) + MvPolynomial.X i ^ w i := by
  simp [translatedPowerSubstitution]

@[simp] theorem translatedPowerSubstitution_C (w : σ → ℕ) (a : σ → k) (c : k) :
    translatedPowerSubstitution w a (MvPolynomial.C c) = MvPolynomial.C c := by
  simp [translatedPowerSubstitution]

theorem totalDegree_aeval_monomial_le (w : σ → ℕ) (g : σ → MvPolynomial τ k)
    (hg : ∀ i, (g i).totalDegree ≤ w i) (d : σ →₀ ℕ) (c : k) :
    (MvPolynomial.aeval g (MvPolynomial.monomial d c)).totalDegree ≤
      Finsupp.weight w d := by
  classical
  rw [MvPolynomial.aeval_monomial]
  calc
    _ ≤ (MvPolynomial.C c).totalDegree +
        (d.prod fun i e => g i ^ e).totalDegree := MvPolynomial.totalDegree_mul _ _
    _ ≤ ∑ i ∈ d.support, d i * w i := by
      simp only [MvPolynomial.totalDegree_C, zero_add, Finsupp.prod]
      apply (MvPolynomial.totalDegree_finsetProd _ _).trans
      exact Finset.sum_le_sum (fun i hi => (MvPolynomial.totalDegree_pow (g i) (d i)).trans
        (Nat.mul_le_mul_left (d i) (hg i)))
    _ = _ := by simp [Finsupp.weight, Finsupp.linearCombination_apply, Finsupp.sum, smul_eq_mul]

theorem totalDegree_aeval_le_weighted (w : σ → ℕ) (g : σ → MvPolynomial τ k)
    (hg : ∀ i, (g i).totalDegree ≤ w i) (p : MvPolynomial σ k) :
    (MvPolynomial.aeval g p).totalDegree ≤ p.weightedTotalDegree w := by
  classical
  conv_lhs => rw [MvPolynomial.as_sum p, map_sum]
  apply (MvPolynomial.totalDegree_finsetSum _ _).trans
  apply Finset.sup_le
  intro d hd
  exact (totalDegree_aeval_monomial_le w g hg d (p.coeff d)).trans
    (MvPolynomial.le_weightedTotalDegree w hd)

theorem translatedPowerSubstitution_totalDegree (w : σ → ℕ) (a : σ → k)
    (p : MvPolynomial σ k) :
    (translatedPowerSubstitution w a p).totalDegree ≤ p.weightedTotalDegree w := by
  apply totalDegree_aeval_le_weighted
  intro i
  exact (MvPolynomial.totalDegree_add _ _).trans (by simp)

noncomputable def translation (a : σ → k) : MvPolynomial σ k →ₐ[k] MvPolynomial σ k :=
  MvPolynomial.aeval (fun i => MvPolynomial.C (a i) + MvPolynomial.X i)

theorem translatedPowerSubstitution_factor (w : σ → ℕ) (a : σ → k) :
    translatedPowerSubstitution w a =
      (MvPolynomial.aeval (fun i => MvPolynomial.X i ^ w i)).comp (translation a) := by
  ext i
  simp [translatedPowerSubstitution, translation]

noncomputable def translationEquiv (a : σ → k) : MvPolynomial σ k ≃ₐ[k] MvPolynomial σ k :=
  AlgEquiv.ofAlgHom (translation a) (translation (-a))
    (by ext i; simp [translation])
    (by ext i; simp [translation])

noncomputable def pointIdeal (a : σ → k) : Ideal (MvPolynomial σ k) :=
  RingHom.ker (MvPolynomial.aeval a).toRingHom

instance pointIdeal_isMaximal (a : σ → k) : (pointIdeal a).IsMaximal := by
  apply RingHom.ker_isMaximal_of_surjective
  intro c
  exact ⟨MvPolynomial.C c, by simp⟩

@[simp] theorem mem_pointIdeal (a : σ → k) (p : MvPolynomial σ k) :
    p ∈ pointIdeal a ↔ MvPolynomial.aeval a p = 0 := Iff.rfl

theorem pointIdeal_eq_span (a : σ → k) :
    pointIdeal a = Ideal.span (Set.range (fun i =>
      MvPolynomial.X i - MvPolynomial.C (a i))) := by
  let J : Ideal (MvPolynomial σ k) := Ideal.span (Set.range (fun i =>
    MvPolynomial.X i - MvPolynomial.C (a i)))
  have hJ : J ≤ pointIdeal a := by
    apply Ideal.span_le.mpr
    rintro p ⟨i, rfl⟩
    simp
  apply le_antisymm _ hJ
  have heval : Ideal.Quotient.mk J =
      ((Ideal.Quotient.mk J).comp MvPolynomial.C).comp (MvPolynomial.aeval a).toRingHom := by
    apply MvPolynomial.ringHom_ext
    · intro c
      simp
    · intro i
      simp only [RingHom.comp_apply, AlgHom.toRingHom_eq_coe, RingHom.coe_coe,
        MvPolynomial.aeval_X]
      apply sub_eq_zero.mp
      rw [← map_sub, Ideal.Quotient.eq_zero_iff_mem]
      exact Ideal.subset_span ⟨i, rfl⟩
  intro p hp
  apply Ideal.Quotient.eq_zero_iff_mem.mp
  rw [heval]
  simp only [RingHom.comp_apply]
  change (Ideal.Quotient.mk J) (MvPolynomial.C (MvPolynomial.aeval a p)) = 0
  rw [(mem_pointIdeal a p).mp hp, map_zero, map_zero]

theorem translatedPowerSubstitution_eval_origin (w : σ → ℕ) (a : σ → k)
    (hw : ∀ i, 0 < w i) :
    (MvPolynomial.aeval (0 : σ → k)).comp (translatedPowerSubstitution w a) =
      MvPolynomial.aeval a := by
  ext i
  simp [translatedPowerSubstitution, zero_pow (hw i).ne']

theorem translatedPowerSubstitution_comap_origin (w : σ → ℕ) (a : σ → k)
    (hw : ∀ i, 0 < w i) :
    (pointIdeal (0 : σ → k)).comap (translatedPowerSubstitution w a).toRingHom =
      pointIdeal a := by
  ext p
  change MvPolynomial.aeval (0 : σ → k) (translatedPowerSubstitution w a p) = 0 ↔ _
  have h := congrArg (fun f : MvPolynomial σ k →ₐ[k] k => f p)
    (translatedPowerSubstitution_eval_origin w a hw)
  change MvPolynomial.aeval (0 : σ → k) (translatedPowerSubstitution w a p) =
    MvPolynomial.aeval a p at h
  rw [h]
  rfl

theorem prime_over_pointIdeal_eq_origin (w : σ → ℕ) (a : σ → k)
    (Q : Ideal (MvPolynomial σ k)) [Q.IsPrime]
    (hQ : pointIdeal a ≤ Q.comap (translatedPowerSubstitution w a).toRingHom) :
    Q = pointIdeal (0 : σ → k) := by
  have hle : pointIdeal (0 : σ → k) ≤ Q := by
    rw [pointIdeal_eq_span]
    apply Ideal.span_le.mpr
    rintro p ⟨i, rfl⟩
    have hi : MvPolynomial.X i - MvPolynomial.C (a i) ∈ pointIdeal a := by simp
    have hp := hQ hi
    change translatedPowerSubstitution w a (MvPolynomial.X i - MvPolynomial.C (a i)) ∈ Q at hp
    have hpow : MvPolynomial.X i ^ w i ∈ Q := by
      simpa only [map_sub, translatedPowerSubstitution_X, translatedPowerSubstitution_C,
        add_sub_cancel_left] using hp
    change MvPolynomial.X i - MvPolynomial.C (0 : k) ∈ Q
    rw [MvPolynomial.C_0, sub_zero]
    exact (inferInstance : Q.IsPrime).mem_of_pow_mem (w i) hpow
  exact ((inferInstance : (pointIdeal (0 : σ → k)).IsMaximal).eq_of_le
    (inferInstance : Q.IsPrime).ne_top hle).symm

theorem translatedPowerSubstitution_totalDegree_real (w : σ → ℕ) (a : σ → k)
    (ρ : σ → ℝ) (M N : ℝ) (hM : 0 ≤ M) (hMN : 0 ≤ M * N)
    (hw : ∀ i, (w i : ℝ) = M * ρ i) (p : MvPolynomial σ k)
    (hp : ∀ d ∈ p.support, (∑ i ∈ d.support, (d i : ℝ) * ρ i) ≤ N) :
    ((translatedPowerSubstitution w a p).totalDegree : ℝ) ≤ M * N := by
  have hb : p.weightedTotalDegree w ≤ ⌊M * N⌋₊ := by
    apply Finset.sup_le
    intro d hd
    apply (Nat.le_floor_iff hMN).mpr
    calc
      (Finsupp.weight w d : ℝ) = M * ∑ i ∈ d.support, (d i : ℝ) * ρ i := by
        rw [Finsupp.weight_apply]
        simp only [Finsupp.sum, smul_eq_mul, Nat.cast_sum, Nat.cast_mul]
        simp_rw [hw]
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro i hi
        ring
      _ ≤ M * N := mul_le_mul_of_nonneg_left (hp d hd) hM
  have hd := (translatedPowerSubstitution_totalDegree w a p).trans hb
  exact (Nat.cast_le.mpr hd).trans (Nat.floor_le hMN)

theorem origin_minimalPrimes_map (w : σ → ℕ) (a : σ → k)
    (hw : ∀ i, 0 < w i) (I : Ideal (MvPolynomial σ k))
    (hI : pointIdeal a ∈ I.minimalPrimes) :
    pointIdeal (0 : σ → k) ∈
      (I.map (translatedPowerSubstitution w a).toRingHom).minimalPrimes := by
  let φ := (translatedPowerSubstitution w a).toRingHom
  have hc : (pointIdeal (0 : σ → k)).comap φ = pointIdeal a :=
    translatedPowerSubstitution_comap_origin w a hw
  refine ⟨⟨inferInstance, ?_⟩, ?_⟩
  · apply Ideal.map_le_iff_le_comap.mpr
    rw [hc]
    exact hI.1.2
  · intro Q hQ hQle
    let : Q.IsPrime := hQ.1
    have hIQ : I ≤ Q.comap φ := Ideal.map_le_iff_le_comap.mp hQ.2
    have hQP : Q.comap φ ≤ pointIdeal a := by
      rw [← hc]
      exact Ideal.comap_mono hQle
    have hPQ : pointIdeal a ≤ Q.comap φ := hI.2 ⟨inferInstance, hIQ⟩ hQP
    have heq := prime_over_pointIdeal_eq_origin w a Q hPQ
    exact heq.symm.le

end PiExponent.WeightedBezout

end OAI
end Source0125

-- Source: OAI/NumberTheory/PiExponent/LocalAlgebra/SeparablePointLength.lean
section Source0126
/-
Modification notice for the LogTwo project.
Derived from openai/math (Apache-2.0), revision adc7f1241b42e322a6451854ab7e4b4c146bf78a.
Original source: lean/OAI/NumberTheory/PiExponent/LocalAlgebra/SeparablePointLength.lean
Changes: Convert module/import declarations to the Lean 4.34 public module format.
See ../THIRD_PARTY_NOTICES.txt for provenance and the recorded changes.
-/

namespace OAI

namespace PiExponent.SeparablePointLength

open IsLocalRing TensorProduct

variable {K E ι : Type*} [Field K] [Field E] [Algebra K E]

attribute [local instance] MvPolynomial.algebraMvPolynomial

noncomputable def coefficientBaseChangeEquiv :
    (MvPolynomial ι K) ⊗[K] E ≃ₐ[MvPolynomial ι K] MvPolynomial ι E :=
  Algebra.IsPushout.equiv K (MvPolynomial ι K) E (MvPolynomial ι E)

theorem coefficientExtension_flat :
    Module.Flat (MvPolynomial ι K) (MvPolynomial ι E) :=
  Module.Flat.of_linearEquiv (coefficientBaseChangeEquiv (K := K) (E := E) (ι := ι)).symm.toLinearEquiv

theorem coefficientExtension_finite [Module.Finite K E] :
    Module.Finite (MvPolynomial ι K) (MvPolynomial ι E) :=
  Module.Finite.equiv (coefficientBaseChangeEquiv (K := K) (E := E) (ι := ι)).toLinearEquiv

theorem coefficientExtension_unramified [Algebra.IsSeparable K E] :
    Algebra.FormallyUnramified (MvPolynomial ι K) (MvPolynomial ι E) := by
  let : Algebra.FormallyUnramified K E := Algebra.FormallyUnramified.of_isSeparable K E
  exact Algebra.FormallyUnramified.of_equiv (coefficientBaseChangeEquiv (K := K) (E := E) (ι := ι))

theorem length_quotient_map_of_unramified
    {A B : Type*} [CommRing A] [CommRing B] [Algebra A B]
    [IsLocalRing A] [IsLocalRing B] [IsLocalHom (algebraMap A B)]
    [Module.Flat A B] [Algebra.EssFiniteType A B] [Algebra.FormallyUnramified A B]
    (I : Ideal A) :
    Module.length B (B ⧸ I.map (algebraMap A B)) = Module.length A (A ⧸ I) := by
  rw [(Algebra.TensorProduct.quotIdealMapEquivTensorQuot B I).toLinearEquiv.length_eq,
    IsLocalRing.length_baseChange, Algebra.FormallyUnramified.map_maximalIdeal]
  let : IsSimpleModule B (B ⧸ maximalIdeal B) :=
    isSimpleModule_iff_isCoatom.mpr (Ideal.isMaximal_def.mp inferInstance)
  rw [Module.length_eq_one B (B ⧸ maximalIdeal B), mul_one]

noncomputable def contractedPoint (b : ι → E) : Ideal (MvPolynomial ι K) :=
  (WeightedBezout.pointIdeal b).comap (algebraMap (MvPolynomial ι K) (MvPolynomial ι E))

instance contractedPoint_isPrime (b : ι → E) : (contractedPoint (K := K) b).IsPrime := by
  unfold contractedPoint
  infer_instance

instance point_liesOver (b : ι → E) :
    (WeightedBezout.pointIdeal b).LiesOver (contractedPoint (K := K) b) := ⟨rfl⟩

theorem contractedPoint_eq_ker (b : ι → E) :
    contractedPoint (K := K) b = RingHom.ker (MvPolynomial.aeval b).toRingHom := by
  ext p
  change MvPolynomial.aeval b (MvPolynomial.map (algebraMap K E) p) = 0 ↔
    MvPolynomial.aeval b p = 0
  simp [MvPolynomial.aeval_def]

noncomputable def pointLocalMap (b : ι → E) :
    Localization.AtPrime (contractedPoint (K := K) b) →+*
      Localization.AtPrime (WeightedBezout.pointIdeal b) :=
  Localization.localRingHom (contractedPoint (K := K) b) (WeightedBezout.pointIdeal b)
    (algebraMap (MvPolynomial ι K) (MvPolynomial ι E)) rfl

@[instance_reducible] noncomputable def pointLocalAlgebra (b : ι → E) :
    Algebra (Localization.AtPrime (contractedPoint (K := K) b))
      (Localization.AtPrime (WeightedBezout.pointIdeal b)) :=
  Localization.AtPrime.algebraOfLiesOver (contractedPoint (K := K) b) (WeightedBezout.pointIdeal b)

theorem pointLocal_flat (b : ι → E) :
    letI := pointLocalAlgebra (K := K) b
    Module.Flat (Localization.AtPrime (contractedPoint (K := K) b))
      (Localization.AtPrime (WeightedBezout.pointIdeal b)) := by
  let := pointLocalAlgebra (K := K) b
  let : Module.Flat (MvPolynomial ι K) (MvPolynomial ι E) := coefficientExtension_flat
  infer_instance

theorem pointLocal_unramified [Algebra.IsSeparable K E] (b : ι → E) :
    letI := pointLocalAlgebra (K := K) b
    Algebra.FormallyUnramified (Localization.AtPrime (contractedPoint (K := K) b))
      (Localization.AtPrime (WeightedBezout.pointIdeal b)) := by
  let := pointLocalAlgebra (K := K) b
  let : Algebra.FormallyUnramified (MvPolynomial ι K) (MvPolynomial ι E) :=
    coefficientExtension_unramified
  exact Algebra.FormallyUnramified.of_restrictScalars (MvPolynomial ι K) _ _

theorem pointLocal_essFiniteType [Module.Finite K E] (b : ι → E) :
    letI := pointLocalAlgebra (K := K) b
    Algebra.EssFiniteType (Localization.AtPrime (contractedPoint (K := K) b))
      (Localization.AtPrime (WeightedBezout.pointIdeal b)) := by
  let := pointLocalAlgebra (K := K) b
  let : Module.Finite (MvPolynomial ι K) (MvPolynomial ι E) := coefficientExtension_finite
  exact Algebra.EssFiniteType.of_comp (MvPolynomial ι K) _ _

@[simp] theorem pointLocalMap_algebraMap (b : ι → E) (p : MvPolynomial ι K) :
    pointLocalMap (K := K) b (algebraMap _ (Localization.AtPrime (contractedPoint (K := K) b)) p) =
      algebraMap _ (Localization.AtPrime (WeightedBezout.pointIdeal b))
        (MvPolynomial.map (algebraMap K E) p) :=
  Localization.localRingHom_to_map _ _ _ rfl p

instance pointLocalMap_isLocalHom (b : ι → E) :
    IsLocalHom (pointLocalMap (K := K) b) :=
  Localization.isLocalHom_localRingHom _ _ _ rfl

theorem pointLocalMap_ideal_map (b : ι → E) (I : Ideal (MvPolynomial ι K)) :
    (I.map (algebraMap _ (Localization.AtPrime (contractedPoint (K := K) b)))).map
        (pointLocalMap (K := K) b) =
      (I.map (MvPolynomial.map (algebraMap K E))).map
        (algebraMap _ (Localization.AtPrime (WeightedBezout.pointIdeal b))) := by
  rw [Ideal.map_map, Ideal.map_map]
  congr 1
  apply RingHom.ext
  intro p
  exact pointLocalMap_algebraMap b p

theorem pointLocal_quotient_length [Module.Finite K E] [Algebra.IsSeparable K E]
    (b : ι → E) (I : Ideal (MvPolynomial ι K)) :
    Module.length (Localization.AtPrime (WeightedBezout.pointIdeal b))
      (Localization.AtPrime (WeightedBezout.pointIdeal b) ⧸
        (I.map (MvPolynomial.map (algebraMap K E))).map
          (algebraMap _ (Localization.AtPrime (WeightedBezout.pointIdeal b)))) =
    Module.length (Localization.AtPrime (contractedPoint (K := K) b))
      (Localization.AtPrime (contractedPoint (K := K) b) ⧸
        I.map (algebraMap _ (Localization.AtPrime (contractedPoint (K := K) b)))) := by
  let A := Localization.AtPrime (contractedPoint (K := K) b)
  let B := Localization.AtPrime (WeightedBezout.pointIdeal b)
  let := pointLocalAlgebra (K := K) b
  let : IsLocalHom (algebraMap A B) := pointLocalMap_isLocalHom b
  let : Module.Flat A B := pointLocal_flat b
  let : Algebra.EssFiniteType A B := pointLocal_essFiniteType b
  let : Algebra.FormallyUnramified A B := pointLocal_unramified b
  have h := length_quotient_map_of_unramified (B := B) (I.map (algebraMap _ A))
  change Module.length B (B ⧸ (I.map (algebraMap _ A)).map (pointLocalMap (K := K) b)) = _ at h
  rw [pointLocalMap_ideal_map] at h
  exact h

theorem point_mem_minimalPrimes_map [Module.Finite K E]
    (b : ι → E) (I : Ideal (MvPolynomial ι K))
    (hminimal : contractedPoint (K := K) b ∈ I.minimalPrimes) :
    WeightedBezout.pointIdeal b ∈
      (I.map (MvPolynomial.map (algebraMap K E))).minimalPrimes := by
  let : Module.Finite (MvPolynomial ι K) (MvPolynomial ι E) := coefficientExtension_finite
  change WeightedBezout.pointIdeal b ∈
    (I.map (algebraMap (MvPolynomial ι K) (MvPolynomial ι E))).minimalPrimes
  refine ⟨⟨inferInstance, Ideal.map_le_iff_le_comap.mpr hminimal.1.2⟩, ?_⟩
  intro Q hQ hQP
  let : Q.IsPrime := hQ.1
  have hunder : Q.under (MvPolynomial ι K) ≤ contractedPoint (K := K) b :=
    Ideal.comap_mono hQP
  have hcont : contractedPoint (K := K) b ≤ Q.under (MvPolynomial ι K) :=
    hminimal.2 ⟨inferInstance, Ideal.map_le_iff_le_comap.mp hQ.2⟩ hunder
  exact (Ideal.IsIntegral.mem_minimalPrimes_map_under
    (R := MvPolynomial ι K) (WeightedBezout.pointIdeal b)).2
      ⟨hQ.1, Ideal.map_le_iff_le_comap.mpr hcont⟩ hQP

end PiExponent.SeparablePointLength

end OAI
end Source0126

-- Source: OAI/NumberTheory/PiExponent/Polynomials/PolynomialLocalResidueResolution.lean
section Source0127
-- Modified in this edition: unused plain lemmas removed; see reduction.json.
/-
Modification notice for the LogTwo project.
Derived from openai/math (Apache-2.0), revision adc7f1241b42e322a6451854ab7e4b4c146bf78a.
Original source: lean/OAI/NumberTheory/PiExponent/Polynomials/PolynomialLocalResidueResolution.lean
Changes: Convert module/import declarations to the Lean 4.34 public module format.
See ../THIRD_PARTY_NOTICES.txt for provenance and the recorded changes.
-/

namespace OAI

noncomputable section
namespace PiExponentJets.PolynomialLocalResidueResolution

section LocalCoefficientField
variable {K R ι : Type*} [Field K] [CommRing R] [IsLocalRing R] [Algebra K R]

def residueAlgHom : R →ₐ[K] IsLocalRing.ResidueField R :=
  { IsLocalRing.residue R with commutes' := fun _ => rfl }

theorem isUnit_aeval_of_residue_independent (x : ι → R)
    (hx : AlgebraicIndependent K (fun i => IsLocalRing.residue R (x i)))
    (f : MvPolynomial ι K) (hf : f ≠ 0) : IsUnit (MvPolynomial.aeval x f) := by
  apply (IsLocalRing.residue_ne_zero_iff_isUnit (MvPolynomial.aeval x f)).mp
  intro hz
  apply hf
  apply hx.eq_zero_of_aeval_eq_zero
  have he := MvPolynomial.comp_aeval_apply (f := x) (residueAlgHom (K := K) (R := R)) f
  exact he.symm.trans hz

def rationalCoefficientMap (x : ι → R)
    (hx : AlgebraicIndependent K (fun i => IsLocalRing.residue R (x i))) :
    FractionRing (MvPolynomial ι K) →+* R :=
  IsLocalization.lift (M := nonZeroDivisors (MvPolynomial ι K))
    (S := FractionRing (MvPolynomial ι K)) (g := (MvPolynomial.aeval x).toRingHom)
    (fun f => isUnit_aeval_of_residue_independent x hx f (nonZeroDivisors.coe_ne_zero f))

@[simp] theorem rationalCoefficientMap_polynomial (x : ι → R)
    (hx : AlgebraicIndependent K (fun i => IsLocalRing.residue R (x i)))
    (f : MvPolynomial ι K) :
    rationalCoefficientMap x hx
      (algebraMap (MvPolynomial ι K) (FractionRing (MvPolynomial ι K)) f) =
        MvPolynomial.aeval x f :=
  IsLocalization.lift_eq _ _

end LocalCoefficientField

variable (K : Type*) [Field K] (n : ℕ)
variable (Q : Ideal (MvPolynomial (Fin n) K)) [Q.IsPrime]

abbrev LocalPolynomialRing := Localization.AtPrime Q
abbrev LocalPolynomialResidue := Q.ResidueField

def residueCoordinate (i : Fin n) : LocalPolynomialResidue K n Q :=
  algebraMap (MvPolynomial (Fin n) K) (LocalPolynomialResidue K n Q) (MvPolynomial.X i)

end PiExponentJets.PolynomialLocalResidueResolution

end

end OAI
end Source0127

-- Source: OAI/NumberTheory/PiExponent/LocalAlgebra/CoordinateTranscendenceLocalization.lean
section Source0128
/-
Modification notice for the LogTwo project.
Derived from openai/math (Apache-2.0), revision adc7f1241b42e322a6451854ab7e4b4c146bf78a.
Original source: lean/OAI/NumberTheory/PiExponent/LocalAlgebra/CoordinateTranscendenceLocalization.lean
Changes: Convert module/import declarations to the Lean 4.34 public module format.
See ../THIRD_PARTY_NOTICES.txt for provenance and the recorded changes.
-/

namespace OAI

noncomputable section
namespace PiExponentJets.PolynomialLocalResidueResolution

variable (K : Type*) [Field K] (n : ℕ)
variable (Q : Ideal (MvPolynomial (Fin n) K)) [Q.IsPrime]

lemma residueCoordinate_aeval (f : MvPolynomial (Fin n) K) :
    MvPolynomial.aeval (residueCoordinate K n Q) f =
      algebraMap (MvPolynomial (Fin n) K) (LocalPolynomialResidue K n Q) f := by
  have he : MvPolynomial.aeval (residueCoordinate K n Q) =
      IsScalarTower.toAlgHom K (MvPolynomial (Fin n) K) (LocalPolynomialResidue K n Q) := by
    ext i
    simp only [MvPolynomial.aeval_X]
    rfl
  exact AlgHom.congr_fun he f

theorem residueCoordinate_adjoin_top :
    IntermediateField.adjoin K (Set.range (residueCoordinate K n Q)) = ⊤ := by
  apply top_unique
  intro z _
  obtain ⟨a, b, hb, hz⟩ :=
    IsFractionRing.div_surjective (MvPolynomial (Fin n) K ⧸ Q) z
  obtain ⟨f, rfl⟩ := Ideal.Quotient.mk_surjective a
  obtain ⟨g, rfl⟩ := Ideal.Quotient.mk_surjective b
  apply (IntermediateField.mem_adjoin_range_iff K (residueCoordinate K n Q) z).mpr
  refine ⟨f, g, ?_⟩
  simpa only [residueCoordinate_aeval,
    Ideal.algebraMap_quotient_residueField_mk] using hz.symm

theorem exists_coordinate_residue_basis :
    ∃ t : Set (LocalPolynomialResidue K n Q),
      t.Finite ∧ t ⊆ Set.range (residueCoordinate K n Q) ∧
      IsTranscendenceBasis K ((↑) : t → LocalPolynomialResidue K n Q) := by
  have htop := residueCoordinate_adjoin_top K n Q
  let : Algebra.IsAlgebraic
      (Algebra.adjoin K (Set.range (residueCoordinate K n Q)))
      (LocalPolynomialResidue K n Q) := by
    rw [← IntermediateField.isAlgebraic_adjoin_iff_top, htop, Algebra.isAlgebraic_iff_isIntegral]
    exact Algebra.isIntegral_of_surjective IntermediateField.topEquiv.surjective
  obtain ⟨t, ht, htb⟩ :=
    exists_isTranscendenceBasis_subset (R := K) (Set.range (residueCoordinate K n Q))
  exact ⟨t, (Set.finite_range _).subset ht, ht, htb⟩

theorem exists_coordinate_basis_indices :
    ∃ (t : Set (LocalPolynomialResidue K n Q)) (j : t → Fin n),
      t.Finite ∧ Function.Injective j ∧
      (∀ a, residueCoordinate K n Q (j a) = (a : LocalPolynomialResidue K n Q)) ∧
      IsTranscendenceBasis K ((↑) : t → LocalPolynomialResidue K n Q) := by
  classical
  obtain ⟨t, hfin, ht, htb⟩ := exists_coordinate_residue_basis K n Q
  choose j hj using fun a : t => ht a.property
  refine ⟨t, j, hfin, ?_, hj, htb⟩
  intro a b hab
  apply Subtype.ext
  exact (hj a).symm.trans ((congrArg (residueCoordinate K n Q) hab).trans (hj b))

end PiExponentJets.PolynomialLocalResidueResolution

end

end OAI
end Source0128

-- Source: OAI/NumberTheory/PiExponent/Polynomials/CoefficientLocalizationMaximal.lean
section Source0129
/-
Modification notice for the LogTwo project.
Derived from openai/math (Apache-2.0), revision adc7f1241b42e322a6451854ab7e4b4c146bf78a.
Original source: lean/OAI/NumberTheory/PiExponent/Polynomials/CoefficientLocalizationMaximal.lean
Changes: Convert module/import declarations to the Lean 4.34 public module format.
See ../THIRD_PARTY_NOTICES.txt for provenance and the recorded changes.
-/

namespace OAI

noncomputable section
namespace PiExponentJets.PolynomialLocalResidueResolution

section MaximalKernel
variable {F A L : Type*} [Field F] [CommRing A] [Field L]
variable [Algebra F A] [Algebra F L] [Algebra.IsAlgebraic F L]

theorem algebraic_field_kernel_isMaximal (f : A →ₐ[F] L) :
    (RingHom.ker f.toRingHom).IsMaximal := by
  apply Ideal.Quotient.maximal_of_isField
  exact MulEquiv.isField (Subalgebra.isField_of_algebraic f.range)
    (Ideal.quotientKerEquivRange f).toRingEquiv.toMulEquiv

end MaximalKernel

variable {R A L : Type*} [CommRing R] [CommRing A] [CommRing L]
variable (M : Submonoid R) [Algebra R A] [IsLocalization M A]

include M in

theorem extended_kernel_eq (f : R →+* L) (g : A →+* L)
    (h : g.comp (algebraMap R A) = f) :
    (RingHom.ker f).map (algebraMap R A) = RingHom.ker g := by
  have hk : (RingHom.ker g).comap (algebraMap R A) = RingHom.ker f := by
    ext x
    change g (algebraMap R A x) = 0 ↔ f x = 0
    have he := RingHom.congr_fun h x
    change g (algebraMap R A x) = f x at he
    rw [he]
  rw [← hk]
  exact IsLocalization.map_under M A (RingHom.ker g)

end PiExponentJets.PolynomialLocalResidueResolution

end

end OAI
end Source0129

-- Source: OAI/NumberTheory/PiExponent/Polynomials/PolynomialCoefficientLocalization.lean
section Source0130
-- Modified in this edition: unused plain lemmas removed; see reduction.json.
/-
Modification notice for the LogTwo project.
Derived from openai/math (Apache-2.0), revision adc7f1241b42e322a6451854ab7e4b4c146bf78a.
Original source: lean/OAI/NumberTheory/PiExponent/Polynomials/PolynomialCoefficientLocalization.lean
Changes: Convert module/import declarations to the Lean 4.34 public module format.
See ../THIRD_PARTY_NOTICES.txt for provenance and the recorded changes.
-/

namespace OAI

noncomputable section
namespace PiExponentSiegelAux.W09

variable (K : Type*) [Field K] (α β : Type*)

abbrev SplitPolynomial := MvPolynomial (α ⊕ β) K
abbrev CoefficientPolynomial := MvPolynomial β K
abbrev CoefficientFractionField := FractionRing (CoefficientPolynomial K β)
abbrev FractionCoefficientPolynomial := MvPolynomial α (CoefficientFractionField K β)

def coefficientDenominators : Submonoid (SplitPolynomial K α β) :=
  (nonZeroDivisors (CoefficientPolynomial K β)).map
    (MvPolynomial.rename (Sum.inr : β → α ⊕ β)).toRingHom

abbrev PolynomialCoefficientLocalization := Localization (coefficientDenominators K α β)

@[simp] theorem mem_coefficientDenominators (p : SplitPolynomial K α β) :
    p ∈ coefficientDenominators K α β ↔
      ∃ f : CoefficientPolynomial K β, f ≠ 0 ∧ MvPolynomial.rename Sum.inr f = p := by
  simp [coefficientDenominators, Submonoid.mem_map, mem_nonZeroDivisors_iff_ne_zero]

@[simp] theorem sumAlgEquiv_coefficientRename (f : CoefficientPolynomial K β) :
    MvPolynomial.sumAlgEquiv K α β (MvPolynomial.rename Sum.inr f) = MvPolynomial.C f := by
  exact congrArg (fun g : CoefficientPolynomial K β →ₐ[K]
      MvPolynomial α (CoefficientPolynomial K β) => g f)
    (MvPolynomial.sumAlgEquiv_comp_rename_inr K α β)

theorem sumAlgEquiv_coefficientDenominators :
    (coefficientDenominators K α β).map (MvPolynomial.sumAlgEquiv K α β) =
      (nonZeroDivisors (CoefficientPolynomial K β)).map (MvPolynomial.C (σ := α)) := by
  ext y
  constructor
  · rintro ⟨x, ⟨f, hf, rfl⟩, rfl⟩
    exact ⟨f, hf, (sumAlgEquiv_coefficientRename K α β f).symm⟩
  · rintro ⟨f, hf, rfl⟩
    exact ⟨MvPolynomial.rename Sum.inr f, ⟨f, hf, rfl⟩,
      sumAlgEquiv_coefficientRename K α β f⟩

attribute [local instance] MvPolynomial.algebraMvPolynomial

local instance coefficientPolynomial_scalarTower :
    IsScalarTower K (MvPolynomial α (CoefficientPolynomial K β))
      (FractionCoefficientPolynomial K α β) :=
  IsScalarTower.of_algebraMap_eq (fun c => by
    change MvPolynomial.C (algebraMap K (CoefficientFractionField K β) c) =
      MvPolynomial.map
        (algebraMap (CoefficientPolynomial K β) (CoefficientFractionField K β))
        (MvPolynomial.C (MvPolynomial.C c))
    rw [MvPolynomial.map_C]
    exact congrArg (MvPolynomial.C (σ := α))
      (IsScalarTower.algebraMap_apply K (CoefficientPolynomial K β)
        (CoefficientFractionField K β) c))

def polynomialCoefficientLocalizationEquiv :
    PolynomialCoefficientLocalization K α β ≃ₐ[K] FractionCoefficientPolynomial K α β :=
  IsLocalization.algEquivOfAlgEquiv
    (PolynomialCoefficientLocalization K α β) (FractionCoefficientPolynomial K α β)
    (MvPolynomial.sumAlgEquiv K α β) (sumAlgEquiv_coefficientDenominators K α β)

@[simp] theorem polynomialCoefficientLocalizationEquiv_algebraMap
    (p : SplitPolynomial K α β) :
    polynomialCoefficientLocalizationEquiv K α β
      (algebraMap (SplitPolynomial K α β) (PolynomialCoefficientLocalization K α β) p) =
      MvPolynomial.map
        (algebraMap (CoefficientPolynomial K β) (CoefficientFractionField K β))
        (MvPolynomial.sumAlgEquiv K α β p) :=
  IsLocalization.algEquivOfAlgEquiv_eq (sumAlgEquiv_coefficientDenominators K α β) p

@[simp] theorem polynomialCoefficientLocalizationEquiv_X_inl (i : α) :
    polynomialCoefficientLocalizationEquiv K α β
      (algebraMap (SplitPolynomial K α β) (PolynomialCoefficientLocalization K α β)
        (MvPolynomial.X (Sum.inl i))) = MvPolynomial.X i := by
  rw [polynomialCoefficientLocalizationEquiv_algebraMap]
  rw [MvPolynomial.sumAlgEquiv_X_inl, MvPolynomial.map_X]

@[simp] theorem polynomialCoefficientLocalizationEquiv_X_inr (j : β) :
    polynomialCoefficientLocalizationEquiv K α β
      (algebraMap (SplitPolynomial K α β) (PolynomialCoefficientLocalization K α β)
        (MvPolynomial.X (Sum.inr j))) =
      MvPolynomial.C (algebraMap (CoefficientPolynomial K β) (CoefficientFractionField K β)
        (MvPolynomial.X j)) := by
  rw [polynomialCoefficientLocalizationEquiv_algebraMap]
  rw [MvPolynomial.sumAlgEquiv_X_inr, MvPolynomial.map_C]

@[simp] theorem polynomialCoefficientLocalizationEquiv_coefficient
    (f : CoefficientPolynomial K β) :
    polynomialCoefficientLocalizationEquiv K α β
      (algebraMap (SplitPolynomial K α β) (PolynomialCoefficientLocalization K α β)
        (MvPolynomial.rename Sum.inr f)) =
      MvPolynomial.C (algebraMap (CoefficientPolynomial K β) (CoefficientFractionField K β) f) := by
  rw [polynomialCoefficientLocalizationEquiv_algebraMap,
    sumAlgEquiv_coefficientRename, MvPolynomial.map_C]

end PiExponentSiegelAux.W09

end

end OAI
end Source0130

-- Source: OAI/NumberTheory/PiExponent/Polynomials/RationalResidueCoefficientField.lean
section Source0131
-- Modified in this edition: unused plain lemmas removed; see reduction.json.
/-
Modification notice for the LogTwo project.
Derived from openai/math (Apache-2.0), revision adc7f1241b42e322a6451854ab7e4b4c146bf78a.
Original source: lean/OAI/NumberTheory/PiExponent/Polynomials/RationalResidueCoefficientField.lean
Changes: Convert module/import declarations to the Lean 4.34 public module format.
See ../THIRD_PARTY_NOTICES.txt for provenance and the recorded changes.
-/

namespace OAI

noncomputable section
namespace PiExponentJets.PolynomialLocalResidueResolution
open scoped IntermediateField.algebraAdjoinAdjoin

variable {K R ι : Type*} [Field K] [CommRing R] [IsLocalRing R] [Algebra K R]
variable (x : ι → R)
variable (hx : AlgebraicIndependent K (fun i => IsLocalRing.residue R (x i)))

def rationalResidueEquiv : FractionRing (MvPolynomial ι K) ≃ₐ[K]
    IntermediateField.adjoin K (Set.range (fun i => IsLocalRing.residue R (x i))) :=
  IsFractionRing.algEquivOfAlgEquiv hx.aevalEquiv

@[simp] theorem rationalResidueEquiv_polynomial (f : MvPolynomial ι K) :
    ((rationalResidueEquiv x hx
      (algebraMap (MvPolynomial ι K) (FractionRing (MvPolynomial ι K)) f)) :
        IsLocalRing.ResidueField R) =
      MvPolynomial.aeval (fun i => IsLocalRing.residue R (x i)) f := by
  rw [rationalResidueEquiv, IsFractionRing.algEquivOfAlgEquiv_algebraMap]
  rfl

def residueCoefficientSection :
    IntermediateField.adjoin K (Set.range (fun i => IsLocalRing.residue R (x i))) →+* R :=
  (rationalCoefficientMap x hx).comp (rationalResidueEquiv x hx).symm.toRingHom

end PiExponentJets.PolynomialLocalResidueResolution

end

end OAI
end Source0131

-- Source: OAI/NumberTheory/PiExponent/LocalAlgebra/SplitCoordinateClosedPoint.lean
section Source0132
/-
Modification notice for the LogTwo project.
Derived from openai/math (Apache-2.0), revision adc7f1241b42e322a6451854ab7e4b4c146bf78a.
Original source: lean/OAI/NumberTheory/PiExponent/LocalAlgebra/SplitCoordinateClosedPoint.lean
Changes: Convert module/import declarations to the Lean 4.34 public module format.
See ../THIRD_PARTY_NOTICES.txt for provenance and the recorded changes.
-/

namespace OAI

noncomputable section
namespace PiExponentJets.PolynomialLocalResidueResolution
open scoped IntermediateField

variable (K α β : Type*) [Field K]
variable (Q : Ideal (MvPolynomial (α ⊕ β) K)) [Q.IsPrime]

abbrev SplitLocalRing := Localization.AtPrime Q
abbrev SplitResidue := Q.ResidueField
abbrev SplitCoefficientField := FractionRing (MvPolynomial β K)

def splitLocalBeta (j : β) : SplitLocalRing K α β Q :=
  algebraMap (MvPolynomial (α ⊕ β) K) (SplitLocalRing K α β Q) (MvPolynomial.X (Sum.inr j))

def splitResidueBeta (j : β) : SplitResidue K α β Q :=
  IsLocalRing.residue (SplitLocalRing K α β Q) (splitLocalBeta K α β Q j)

variable (hB : IsTranscendenceBasis K (splitResidueBeta K α β Q))

@[reducible] def splitCoefficientResidueAlgebra :
    Algebra (SplitCoefficientField K β) (SplitResidue K α β Q) :=
  (((IntermediateField.adjoin K (Set.range (splitResidueBeta K α β Q))).val.toRingHom).comp
    (rationalResidueEquiv (splitLocalBeta K α β Q) hB.1).toRingHom).toAlgebra

theorem splitResidue_algebraic :
    letI := splitCoefficientResidueAlgebra K α β Q hB
    Algebra.IsAlgebraic (SplitCoefficientField K β) (SplitResidue K α β Q) := by
  let := splitCoefficientResidueAlgebra K α β Q hB
  have h := hB.isAlgebraic_field
  exact (Algebra.isAlgebraic_ringHom_iff_of_comp_eq
    (rationalResidueEquiv (splitLocalBeta K α β Q) hB.1)
    (RingEquiv.refl (SplitResidue K α β Q)) (by rfl)).mp h

def closedPointEvaluation :
    letI := splitCoefficientResidueAlgebra K α β Q hB
    MvPolynomial α (SplitCoefficientField K β) →ₐ[SplitCoefficientField K β]
      SplitResidue K α β Q :=
  letI := splitCoefficientResidueAlgebra K α β Q hB
  MvPolynomial.aeval (fun i =>
    algebraMap (MvPolynomial (α ⊕ β) K) (SplitResidue K α β Q) (MvPolynomial.X (Sum.inl i)))

abbrev closedPointEvaluationRingHom :
    MvPolynomial α (SplitCoefficientField K β) →+* SplitResidue K α β Q :=
  letI := splitCoefficientResidueAlgebra K α β Q hB
  (closedPointEvaluation K α β Q hB).toRingHom

theorem closedPointEvaluation_kernel_maximal :
    (RingHom.ker (closedPointEvaluationRingHom K α β Q hB)).IsMaximal := by
  let := splitCoefficientResidueAlgebra K α β Q hB
  let := splitResidue_algebraic K α β Q hB
  exact algebraic_field_kernel_isMaximal (closedPointEvaluation K α β Q hB)

theorem closedPointEvaluation_coefficient (f : MvPolynomial β K) :
    closedPointEvaluation K α β Q hB
      (MvPolynomial.C (algebraMap (MvPolynomial β K) (SplitCoefficientField K β) f)) =
      MvPolynomial.aeval (splitResidueBeta K α β Q) f := by
  let := splitCoefficientResidueAlgebra K α β Q hB
  rw [closedPointEvaluation, MvPolynomial.aeval_C]
  change ((rationalResidueEquiv (splitLocalBeta K α β Q) hB.1
    (algebraMap (MvPolynomial β K) (SplitCoefficientField K β) f)) :
      SplitResidue K α β Q) = _
  exact rationalResidueEquiv_polynomial (splitLocalBeta K α β Q) hB.1 f

end PiExponentJets.PolynomialLocalResidueResolution

end

end OAI
end Source0132

-- Source: OAI/NumberTheory/PiExponent/LocalAlgebra/SplitClosedPointCompatibility.lean
section Source0133
/-
Modification notice for the LogTwo project.
Derived from openai/math (Apache-2.0), revision adc7f1241b42e322a6451854ab7e4b4c146bf78a.
Original source: lean/OAI/NumberTheory/PiExponent/LocalAlgebra/SplitClosedPointCompatibility.lean
Changes: Convert module/import declarations to the Lean 4.34 public module format.
See ../THIRD_PARTY_NOTICES.txt for provenance and the recorded changes.
-/

namespace OAI

noncomputable section
namespace PiExponentJets.PolynomialLocalResidueResolution

variable (K α β : Type*) [Field K]
variable (Q : Ideal (MvPolynomial (α ⊕ β) K)) [Q.IsPrime]
variable (hB : IsTranscendenceBasis K (splitResidueBeta K α β Q))

theorem closedPointEvaluation_original :
    ((closedPointEvaluationRingHom K α β Q hB).comp
      (PiExponentSiegelAux.W09.polynomialCoefficientLocalizationEquiv K α β).toRingHom).comp
      (algebraMap (MvPolynomial (α ⊕ β) K)
        (PiExponentSiegelAux.W09.PolynomialCoefficientLocalization K α β)) =
      algebraMap (MvPolynomial (α ⊕ β) K) (SplitResidue K α β Q) := by
  apply MvPolynomial.ringHom_ext
  · intro a
    change closedPointEvaluation K α β Q hB
      (PiExponentSiegelAux.W09.polynomialCoefficientLocalizationEquiv K α β
        (algebraMap (MvPolynomial (α ⊕ β) K)
          (PiExponentSiegelAux.W09.PolynomialCoefficientLocalization K α β)
          (MvPolynomial.C a))) = _
    have h := closedPointEvaluation_coefficient K α β Q hB (MvPolynomial.C a)
    rw [← PiExponentSiegelAux.W09.polynomialCoefficientLocalizationEquiv_coefficient] at h
    simpa only [RingHom.comp_apply, MvPolynomial.rename_C, MvPolynomial.aeval_C,
      IsScalarTower.algebraMap_apply K (MvPolynomial (α ⊕ β) K) (SplitResidue K α β Q),
      MvPolynomial.algebraMap_eq] using h
  · intro i
    cases i with
    | inl i =>
      let := splitCoefficientResidueAlgebra K α β Q hB
      change closedPointEvaluation K α β Q hB
        (PiExponentSiegelAux.W09.polynomialCoefficientLocalizationEquiv K α β
          (algebraMap (MvPolynomial (α ⊕ β) K)
            (PiExponentSiegelAux.W09.PolynomialCoefficientLocalization K α β)
            (MvPolynomial.X (Sum.inl i)))) = _
      rw [PiExponentSiegelAux.W09.polynomialCoefficientLocalizationEquiv_X_inl,
        closedPointEvaluation, MvPolynomial.aeval_X]
    | inr j =>
      let := splitCoefficientResidueAlgebra K α β Q hB
      change closedPointEvaluation K α β Q hB
        (PiExponentSiegelAux.W09.polynomialCoefficientLocalizationEquiv K α β
          (algebraMap (MvPolynomial (α ⊕ β) K)
            (PiExponentSiegelAux.W09.PolynomialCoefficientLocalization K α β)
            (MvPolynomial.X (Sum.inr j)))) = _
      rw [PiExponentSiegelAux.W09.polynomialCoefficientLocalizationEquiv_X_inr,
        closedPointEvaluation_coefficient, MvPolynomial.aeval_X]
      rfl

include hB in

theorem coefficientLocalization_extendedPrime_maximal :
    (Q.map (algebraMap (MvPolynomial (α ⊕ β) K)
      (PiExponentSiegelAux.W09.PolynomialCoefficientLocalization K α β))).IsMaximal := by
  have hker := extended_kernel_eq
    (PiExponentSiegelAux.W09.coefficientDenominators K α β)
    (algebraMap (MvPolynomial (α ⊕ β) K) (SplitResidue K α β Q))
    ((closedPointEvaluationRingHom K α β Q hB).comp
      (PiExponentSiegelAux.W09.polynomialCoefficientLocalizationEquiv K α β).toRingHom)
    (closedPointEvaluation_original K α β Q hB)
  rw [Ideal.ker_algebraMap_residueField] at hker
  rw [hker]
  change ((RingHom.ker (closedPointEvaluationRingHom K α β Q hB)).comap
    (PiExponentSiegelAux.W09.polynomialCoefficientLocalizationEquiv K α β).toRingHom).IsMaximal
  let := closedPointEvaluation_kernel_maximal K α β Q hB
  exact Ideal.comap_isMaximal_of_surjective _
    (PiExponentSiegelAux.W09.polynomialCoefficientLocalizationEquiv K α β).surjective

theorem coefficientClosedPoint_comap :
    (RingHom.ker ((closedPointEvaluationRingHom K α β Q hB).comp
      (PiExponentSiegelAux.W09.polynomialCoefficientLocalizationEquiv K α β).toRingHom)).comap
      (algebraMap (MvPolynomial (α ⊕ β) K)
        (PiExponentSiegelAux.W09.PolynomialCoefficientLocalization K α β)) = Q := by
  ext f
  change closedPointEvaluation K α β Q hB
    (PiExponentSiegelAux.W09.polynomialCoefficientLocalizationEquiv K α β
      (algebraMap _ (PiExponentSiegelAux.W09.PolynomialCoefficientLocalization K α β) f)) = 0 ↔ f ∈ Q
  have h := RingHom.congr_fun (closedPointEvaluation_original K α β Q hB) f
  change closedPointEvaluation K α β Q hB
    (PiExponentSiegelAux.W09.polynomialCoefficientLocalizationEquiv K α β
      (algebraMap _ (PiExponentSiegelAux.W09.PolynomialCoefficientLocalization K α β) f)) =
        algebraMap (MvPolynomial (α ⊕ β) K) (SplitResidue K α β Q) f at h
  rw [h]
  exact Ideal.algebraMap_residueField_eq_zero

end PiExponentJets.PolynomialLocalResidueResolution

end

end OAI
end Source0133

-- Source: OAI/NumberTheory/PiExponent/Polynomials/PolynomialPrimeClosedPointEquiv.lean
section Source0134
/-
Modification notice for the LogTwo project.
Derived from openai/math (Apache-2.0), revision adc7f1241b42e322a6451854ab7e4b4c146bf78a.
Original source: lean/OAI/NumberTheory/PiExponent/Polynomials/PolynomialPrimeClosedPointEquiv.lean
Changes: Convert module/import declarations to the Lean 4.34 public module format.
See ../THIRD_PARTY_NOTICES.txt for provenance and the recorded changes.
-/

namespace OAI

noncomputable section
namespace PiExponentJets.PolynomialLocalResidueResolution

variable (K α β : Type*) [Field K]
variable (Q : Ideal (MvPolynomial (α ⊕ β) K)) [Q.IsPrime]
variable (hB : IsTranscendenceBasis K (splitResidueBeta K α β Q))

def coefficientClosedPoint :
    Ideal (PiExponentSiegelAux.W09.PolynomialCoefficientLocalization K α β) :=
  RingHom.ker ((closedPointEvaluationRingHom K α β Q hB).comp
    (PiExponentSiegelAux.W09.polynomialCoefficientLocalizationEquiv K α β).toRingHom)

instance coefficientClosedPoint_isMaximal :
    (coefficientClosedPoint K α β Q hB).IsMaximal := by
  change ((RingHom.ker (closedPointEvaluationRingHom K α β Q hB)).comap
    (PiExponentSiegelAux.W09.polynomialCoefficientLocalizationEquiv K α β).toRingHom).IsMaximal
  let := closedPointEvaluation_kernel_maximal K α β Q hB
  exact Ideal.comap_isMaximal_of_surjective _
    (PiExponentSiegelAux.W09.polynomialCoefficientLocalizationEquiv K α β).surjective

abbrev CoefficientClosedLocal := Localization.AtPrime (coefficientClosedPoint K α β Q hB)

theorem closedLocal_isLocalizationAtOriginal :
    IsLocalization.AtPrime (CoefficientClosedLocal K α β Q hB) Q := by
  have h : IsLocalization.AtPrime (CoefficientClosedLocal K α β Q hB)
      ((coefficientClosedPoint K α β Q hB).comap
        (algebraMap (MvPolynomial (α ⊕ β) K)
          (PiExponentSiegelAux.W09.PolynomialCoefficientLocalization K α β))) := by
    infer_instance
  have hQ : (coefficientClosedPoint K α β Q hB).comap
      (algebraMap (MvPolynomial (α ⊕ β) K)
        (PiExponentSiegelAux.W09.PolynomialCoefficientLocalization K α β)) = Q :=
    coefficientClosedPoint_comap K α β Q hB
  have transport (J : Ideal (MvPolynomial (α ⊕ β) K)) [J.IsPrime]
      (he : J = Q) :
      IsLocalization.AtPrime (CoefficientClosedLocal K α β Q hB) J →
        IsLocalization.AtPrime (CoefficientClosedLocal K α β Q hB) Q := by
    subst J
    exact id
  exact transport _ hQ h

def originalLocalCoefficientLocalEquiv :
    Localization.AtPrime Q ≃+* CoefficientClosedLocal K α β Q hB := by
  letI := closedLocal_isLocalizationAtOriginal K α β Q hB
  exact (IsLocalization.algEquiv Q.primeCompl
    (Localization.AtPrime Q) (CoefficientClosedLocal K α β Q hB)).toRingEquiv

def closedPolynomialIdeal : Ideal (MvPolynomial α (SplitCoefficientField K β)) :=
  (coefficientClosedPoint K α β Q hB).map
    (PiExponentSiegelAux.W09.polynomialCoefficientLocalizationEquiv K α β).toRingHom

instance closedPolynomialIdeal_isMaximal :
    (closedPolynomialIdeal K α β Q hB).IsMaximal := by
  exact (inferInstance : (coefficientClosedPoint K α β Q hB).IsMaximal).map_bijective
    (PiExponentSiegelAux.W09.polynomialCoefficientLocalizationEquiv K α β).toRingHom
    (PiExponentSiegelAux.W09.polynomialCoefficientLocalizationEquiv K α β).bijective

def polynomialPrimeClosedPointEquiv :
    Localization.AtPrime Q ≃+*
      Localization.AtPrime (closedPolynomialIdeal K α β Q hB) :=
  (originalLocalCoefficientLocalEquiv K α β Q hB).trans
    (PiExponentSiegel.W23.atPrimeEquivOfRingEquiv
      (PiExponentSiegelAux.W09.polynomialCoefficientLocalizationEquiv K α β).toRingEquiv
      (coefficientClosedPoint K α β Q hB))

def polynomialPrimeClosedPointResidueEquiv :
    Q.ResidueField ≃+* (closedPolynomialIdeal K α β Q hB).ResidueField :=
  IsLocalRing.ResidueField.mapEquiv (polynomialPrimeClosedPointEquiv K α β Q hB)

end PiExponentJets.PolynomialLocalResidueResolution

end

end OAI
end Source0134

-- Source: OAI/NumberTheory/PiExponent/LocalAlgebra/CoordinateSliceLength.lean
section Source0135
/-
Modification notice for the LogTwo project.
Derived from openai/math (Apache-2.0), revision adc7f1241b42e322a6451854ab7e4b4c146bf78a.
Original source: lean/OAI/NumberTheory/PiExponent/LocalAlgebra/CoordinateSliceLength.lean
Changes: Convert module/import declarations to the Lean 4.34 public module format.
See ../THIRD_PARTY_NOTICES.txt for provenance and the recorded changes.
-/

namespace OAI

noncomputable section

namespace PiExponent.CoordinateSliceLength

open PiExponentJets.PolynomialLocalResidueResolution

abbrev localizedLength {R : Type*} [CommRing R] (P : Ideal R) [P.IsPrime] (I : Ideal R) : ℕ∞ :=
  Module.length (Localization.AtPrime P)
    (Localization.AtPrime P ⧸ I.map (algebraMap R (Localization.AtPrime P)))

theorem localizedLength_congr {R : Type*} [CommRing R]
    (P Q : Ideal R) [P.IsPrime] [Q.IsPrime] (h : P = Q) (I : Ideal R) :
    localizedLength P I = localizedLength Q I := by
  subst Q
  rfl

variable (K α β : Type*) [Field K]
variable (Q : Ideal (MvPolynomial (α ⊕ β) K)) [Q.IsPrime]
variable (hB : IsTranscendenceBasis K (splitResidueBeta K α β Q))

def rationalizePolynomial :
    MvPolynomial (α ⊕ β) K →+* MvPolynomial α (SplitCoefficientField K β) :=
  (PiExponentSiegelAux.W09.polynomialCoefficientLocalizationEquiv K α β).toRingHom.comp
    (algebraMap (MvPolynomial (α ⊕ β) K)
      (PiExponentSiegelAux.W09.PolynomialCoefficientLocalization K α β))

@[simp] theorem rationalizePolynomial_X_inl (i : α) :
    rationalizePolynomial K α β (MvPolynomial.X (Sum.inl i)) = MvPolynomial.X i :=
  PiExponentSiegelAux.W09.polynomialCoefficientLocalizationEquiv_X_inl K α β i

@[simp] theorem rationalizePolynomial_X_inr (i : β) :
    rationalizePolynomial K α β (MvPolynomial.X (Sum.inr i)) =
      MvPolynomial.C (algebraMap (MvPolynomial β K) (SplitCoefficientField K β)
        (MvPolynomial.X i)) :=
  PiExponentSiegelAux.W09.polynomialCoefficientLocalizationEquiv_X_inr K α β i

theorem closedPolynomialIdeal_eq_ker :
    closedPolynomialIdeal K α β Q hB =
      RingHom.ker (closedPointEvaluationRingHom K α β Q hB) := by
  unfold closedPolynomialIdeal coefficientClosedPoint
  change ((RingHom.ker (closedPointEvaluationRingHom K α β Q hB)).comap
    (PiExponentSiegelAux.W09.polynomialCoefficientLocalizationEquiv K α β).toRingHom).map
      (PiExponentSiegelAux.W09.polynomialCoefficientLocalizationEquiv K α β).toRingHom = _
  exact Ideal.map_comap_of_surjective _
    (PiExponentSiegelAux.W09.polynomialCoefficientLocalizationEquiv K α β).surjective _

theorem map_prime_eq_closedPolynomialIdeal :
    Q.map (rationalizePolynomial K α β) = closedPolynomialIdeal K α β Q hB := by
  have h := extended_kernel_eq
    (PiExponentSiegelAux.W09.coefficientDenominators K α β)
    (algebraMap (MvPolynomial (α ⊕ β) K) (SplitResidue K α β Q))
    ((closedPointEvaluationRingHom K α β Q hB).comp
      (PiExponentSiegelAux.W09.polynomialCoefficientLocalizationEquiv K α β).toRingHom)
    (closedPointEvaluation_original K α β Q hB)
  rw [Ideal.ker_algebraMap_residueField] at h
  unfold closedPolynomialIdeal coefficientClosedPoint
  rw [← h, Ideal.map_map]
  rfl

theorem closedPolynomialIdeal_comap :
    (closedPolynomialIdeal K α β Q hB).comap (rationalizePolynomial K α β) = Q := by
  rw [closedPolynomialIdeal_eq_ker]
  change RingHom.ker ((closedPointEvaluationRingHom K α β Q hB).comp
    (rationalizePolynomial K α β)) = Q
  rw [show (closedPointEvaluationRingHom K α β Q hB).comp
      (rationalizePolynomial K α β) =
      algebraMap (MvPolynomial (α ⊕ β) K) (SplitResidue K α β Q) from
    closedPointEvaluation_original K α β Q hB]
  exact Ideal.ker_algebraMap_residueField Q

theorem closedPolynomialIdeal_mem_minimalPrimes
    (I : Ideal (MvPolynomial (α ⊕ β) K)) (hQ : Q ∈ I.minimalPrimes) :
    closedPolynomialIdeal K α β Q hB ∈
      (I.map (rationalizePolynomial K α β)).minimalPrimes := by
  refine ⟨⟨inferInstance, ?_⟩, ?_⟩
  · rw [← map_prime_eq_closedPolynomialIdeal]
    exact Ideal.map_mono hQ.1.2
  · intro J hJ hJP
    let : J.IsPrime := hJ.1
    have hcont : Q ≤ J.comap (rationalizePolynomial K α β) := by
      apply hQ.2 ⟨inferInstance, Ideal.map_le_iff_le_comap.mp hJ.2⟩
      rw [← closedPolynomialIdeal_comap K α β Q hB]
      exact Ideal.comap_mono hJP
    rw [← map_prime_eq_closedPolynomialIdeal]
    exact Ideal.map_le_iff_le_comap.mpr hcont

theorem polynomialPrimeClosedPointEquiv_algebraMap
    (p : MvPolynomial (α ⊕ β) K) :
    polynomialPrimeClosedPointEquiv K α β Q hB
      (algebraMap _ (Localization.AtPrime Q) p) =
    algebraMap (MvPolynomial α (SplitCoefficientField K β)) (Localization.AtPrime (closedPolynomialIdeal K α β Q hB))
      (rationalizePolynomial K α β p) := by
  let := closedLocal_isLocalizationAtOriginal K α β Q hB
  change PiExponentSiegel.W23.atPrimeEquivOfRingEquiv _ _
    ((IsLocalization.algEquiv Q.primeCompl (Localization.AtPrime Q)
      (CoefficientClosedLocal K α β Q hB))
      (algebraMap _ (Localization.AtPrime Q) p)) = _
  rw [AlgEquiv.commutes]
  rw [IsScalarTower.algebraMap_apply (MvPolynomial (α ⊕ β) K)
    (PiExponentSiegelAux.W09.PolynomialCoefficientLocalization K α β)
    (CoefficientClosedLocal K α β Q hB)]
  exact PiExponentSiegel.W23.atPrimeEquivOfRingEquiv_algebraMap _ _ _

theorem polynomialPrimeClosedPointEquiv_map_ideal (I : Ideal (MvPolynomial (α ⊕ β) K)) :
    (I.map (algebraMap _ (Localization.AtPrime Q))).map
      (polynomialPrimeClosedPointEquiv K α β Q hB).toRingHom =
    (I.map (rationalizePolynomial K α β)).map
      (algebraMap (MvPolynomial α (SplitCoefficientField K β)) (Localization.AtPrime (closedPolynomialIdeal K α β Q hB))) := by
  rw [Ideal.map_map, Ideal.map_map]
  congr 1
  apply RingHom.ext
  intro p
  exact polynomialPrimeClosedPointEquiv_algebraMap K α β Q hB p

include hB in

theorem length_eq_rationalized (I : Ideal (MvPolynomial (α ⊕ β) K)) :
    localizedLength Q I =
      localizedLength (closedPolynomialIdeal K α β Q hB)
        (I.map (rationalizePolynomial K α β)) :=
  LocalLengthTransport.localLength_eq_of_localizedIdeal_map Q
    (closedPolynomialIdeal K α β Q hB) (polynomialPrimeClosedPointEquiv K α β Q hB)
    I (I.map (rationalizePolynomial K α β))
    (polynomialPrimeClosedPointEquiv_map_ideal K α β Q hB I)

theorem splitCoefficientResidue_isScalarTower :
    letI := splitCoefficientResidueAlgebra K α β Q hB
    IsScalarTower K (SplitCoefficientField K β) (SplitResidue K α β Q) := by
  let := splitCoefficientResidueAlgebra K α β Q hB
  apply IsScalarTower.of_algebraMap_eq
  intro a
  change algebraMap K (SplitResidue K α β Q) a =
    ((rationalResidueEquiv (splitLocalBeta K α β Q) hB.1
      (algebraMap K (SplitCoefficientField K β) a)) : SplitResidue K α β Q)
  rw [AlgEquiv.commutes]
  rfl

theorem splitResidue_finite [Finite α] [Finite β] :
    letI := splitCoefficientResidueAlgebra K α β Q hB
    Module.Finite (SplitCoefficientField K β) (SplitResidue K α β Q) := by
  let := splitCoefficientResidueAlgebra K α β Q hB
  let := splitCoefficientResidue_isScalarTower K α β Q hB
  let : Algebra.EssFiniteType K (SplitResidue K α β Q) :=
    Algebra.EssFiniteType.comp K (MvPolynomial (α ⊕ β) K) (SplitResidue K α β Q)
  let := Algebra.EssFiniteType.of_comp K (SplitCoefficientField K β)
    (SplitResidue K α β Q)
  let := splitResidue_algebraic K α β Q hB
  exact Algebra.finite_of_essFiniteType_of_isAlgebraic

def slicePoint (i : α) : SplitResidue K α β Q :=
  algebraMap (MvPolynomial (α ⊕ β) K) (SplitResidue K α β Q)
    (MvPolynomial.X (Sum.inl i))

def residueSlice :
    MvPolynomial (α ⊕ β) K →+* MvPolynomial α (SplitResidue K α β Q) :=
  (MvPolynomial.aeval (fun i : α ⊕ β => match i with
    | Sum.inl i => MvPolynomial.X i
    | Sum.inr j => MvPolynomial.C (splitResidueBeta K α β Q j))).toRingHom

theorem map_rationalize_eq_residueSlice :
    letI := splitCoefficientResidueAlgebra K α β Q hB
    (MvPolynomial.map (algebraMap (SplitCoefficientField K β) (SplitResidue K α β Q))).comp
      (rationalizePolynomial K α β) = residueSlice K α β Q := by
  let := splitCoefficientResidueAlgebra K α β Q hB
  let := splitCoefficientResidue_isScalarTower K α β Q hB
  apply MvPolynomial.ringHom_ext
  · intro a
    change MvPolynomial.map _ (rationalizePolynomial K α β (MvPolynomial.C a)) = _
    have hr : rationalizePolynomial K α β (MvPolynomial.C a) =
        MvPolynomial.C (algebraMap K (SplitCoefficientField K β) a) := by
      change PiExponentSiegelAux.W09.polynomialCoefficientLocalizationEquiv K α β
        (algebraMap K (PiExponentSiegelAux.W09.PolynomialCoefficientLocalization K α β) a) = _
      exact (PiExponentSiegelAux.W09.polynomialCoefficientLocalizationEquiv K α β).commutes a
    rw [hr, MvPolynomial.map_C]
    change MvPolynomial.C _ = MvPolynomial.aeval _ (MvPolynomial.C a)
    rw [MvPolynomial.aeval_C]
    exact congrArg MvPolynomial.C
      (IsScalarTower.algebraMap_apply K (SplitCoefficientField K β) (SplitResidue K α β Q) a).symm
  · intro i
    cases i with
    | inl i => simp [residueSlice]
    | inr i =>
      have hc := closedPointEvaluation_coefficient K α β Q hB (MvPolynomial.X i)
      simp only [closedPointEvaluation, MvPolynomial.aeval_C, MvPolynomial.aeval_X] at hc
      simpa [residueSlice] using congrArg (MvPolynomial.C (σ := α)) hc

theorem closedPolynomialIdeal_eq_contractedPoint :
    letI := splitCoefficientResidueAlgebra K α β Q hB
    closedPolynomialIdeal K α β Q hB =
      SeparablePointLength.contractedPoint (K := SplitCoefficientField K β)
        (slicePoint K α β Q) := by
  let := splitCoefficientResidueAlgebra K α β Q hB
  rw [closedPolynomialIdeal_eq_ker, SeparablePointLength.contractedPoint_eq_ker]
  rfl

include hB in

theorem length_eq_residueSlice [Finite α] [Finite β] [CharZero K]
    (I : Ideal (MvPolynomial (α ⊕ β) K)) :
    Module.length (Localization.AtPrime Q)
      (Localization.AtPrime Q ⧸ I.map (algebraMap _ (Localization.AtPrime Q))) =
    Module.length (Localization.AtPrime (WeightedBezout.pointIdeal (slicePoint K α β Q)))
      (Localization.AtPrime (WeightedBezout.pointIdeal (slicePoint K α β Q)) ⧸
        (I.map (residueSlice K α β Q)).map (algebraMap _
          (Localization.AtPrime (WeightedBezout.pointIdeal (slicePoint K α β Q))))) := by
  let := splitCoefficientResidueAlgebra K α β Q hB
  let := splitResidue_finite K α β Q hB
  have hc := closedPolynomialIdeal_eq_contractedPoint K α β Q hB
  have h := length_eq_rationalized K α β Q hB I
  have hcongr := localizedLength_congr
    (closedPolynomialIdeal K α β Q hB)
    (SeparablePointLength.contractedPoint (K := SplitCoefficientField K β) (slicePoint K α β Q))
    hc (I.map (rationalizePolynomial K α β))
  have he := SeparablePointLength.pointLocal_quotient_length
    (K := SplitCoefficientField K β) (slicePoint K α β Q)
    (I.map (rationalizePolynomial K α β))
  have hi : (I.map (rationalizePolynomial K α β)).map
      (MvPolynomial.map (algebraMap (SplitCoefficientField K β) (SplitResidue K α β Q))) =
      I.map (residueSlice K α β Q) := by
    rw [Ideal.map_map, map_rationalize_eq_residueSlice K α β Q hB]
  rw [hi] at he
  exact h.trans (hcongr.trans he.symm)

include hB in

theorem slicePoint_mem_minimalPrimes [Finite α] [Finite β]
    (I : Ideal (MvPolynomial (α ⊕ β) K)) (hQ : Q ∈ I.minimalPrimes) :
    WeightedBezout.pointIdeal (slicePoint K α β Q) ∈
      (I.map (residueSlice K α β Q)).minimalPrimes := by
  let := splitCoefficientResidueAlgebra K α β Q hB
  let := splitResidue_finite K α β Q hB
  have h := closedPolynomialIdeal_mem_minimalPrimes K α β Q hB I hQ
  rw [closedPolynomialIdeal_eq_contractedPoint K α β Q hB] at h
  have he := SeparablePointLength.point_mem_minimalPrimes_map
    (K := SplitCoefficientField K β) (slicePoint K α β Q)
    (I.map (rationalizePolynomial K α β)) h
  rw [Ideal.map_map, map_rationalize_eq_residueSlice K α β Q hB] at he
  exact he

end PiExponent.CoordinateSliceLength

end

end OAI
end Source0135

-- Source: OAI/NumberTheory/PiExponent/LocalAlgebra/CoordinateTranscendenceBasis.lean
section Source0136
-- Modified in this edition: unused plain lemmas removed; see reduction.json.
/-
Modification notice for the LogTwo project.
Derived from openai/math (Apache-2.0), revision adc7f1241b42e322a6451854ab7e4b4c146bf78a.
Original source: lean/OAI/NumberTheory/PiExponent/LocalAlgebra/CoordinateTranscendenceBasis.lean
Changes: Convert module/import declarations to the Lean 4.34 public module format.
See ../THIRD_PARTY_NOTICES.txt for provenance and the recorded changes.
-/

namespace OAI

noncomputable section
namespace PiExponent
open MvPolynomial
open NormalBasisRigidity

section Linear
variable {K ι : Type*} [Field K] [Fintype ι]

theorem normalBasis_complement_surjective (T : Submodule K (ι → K))
    (A : Finset ι)
    (hA : IsNormalBasis (K := K) (fun i => T.mkQ (Pi.basisFun K ι i)) A) :
    Function.Surjective (fun t : T => fun i : {i // i ∉ A} => t.val i.val) := by
  classical
  have hli : LinearIndependent K (fun i : A => T.mkQ (Pi.basisFun K ι i)) := hA.1
  let b : Module.Basis A K ((ι → K) ⧸ T) := Module.Basis.mk hli (by
    have hr : Set.range (fun i : A => T.mkQ (Pi.basisFun K ι i)) =
        (fun i => T.mkQ (Pi.basisFun K ι i)) '' (A : Set ι) := by ext; simp
    change ⊤ ≤ Submodule.span K (Set.range (fun i : A => T.mkQ (Pi.basisFun K ι i)))
    rw [hr, hA.2])
  intro g
  let u : ι → K := fun i => if hi : i ∈ A then 0 else g ⟨i, hi⟩
  let w : ι → K := ∑ i : A, b.repr (T.mkQ u) i • Pi.basisFun K ι i.val
  have hw : T.mkQ w = T.mkQ u := by
    change T.mkQ (∑ i : A, _) = _
    simp only [map_sum, map_smul]
    simpa only [b, Module.Basis.mk_apply] using b.sum_repr (T.mkQ u)
  have ht : u - w ∈ T := by
    rw [← Submodule.Quotient.mk_eq_zero]
    change T.mkQ (u - w) = 0
    rw [map_sub, hw, sub_self]
  refine ⟨⟨u - w, ht⟩, ?_⟩
  funext i
  have hw0 : w i.val = 0 := by
    dsimp [w]
    simp only [Finset.sum_apply, Pi.smul_apply]
    apply Finset.sum_eq_zero
    intro a _
    have hn : a.val ≠ i.val := fun he => i.property (he ▸ a.property)
    simp [Pi.basisFun_apply, Ne.symm hn]
  change u i.val - w i.val = g i
  simp [u, i.property, hw0]

theorem normalBasis_complement_injective (T : Submodule K (ι → K))
    (A : Finset ι)
    (hA : IsNormalBasis (K := K) (fun i => T.mkQ (Pi.basisFun K ι i)) A) :
    Function.Injective (fun t : T => fun i : {i // i ∉ A} => t.val i.val) := by
  classical
  suffices hz : ∀ t : T, (∀ i, i ∉ A → t.val i = 0) → t = 0 by
    intro t u h
    have hd : t - u = 0 := hz (t - u) (by
      intro i hi
      exact sub_eq_zero.mpr (congrFun h ⟨i,hi⟩))
    exact sub_eq_zero.mp hd
  intro t ht
  have he : (∑ a : A, t.val a.val • Pi.basisFun K ι a.val) = t.val := by
    ext i
    simp only [Finset.sum_apply, Pi.smul_apply, Pi.basisFun_apply]
    by_cases hi : i ∈ A
    · rw [Finset.sum_eq_single (⟨i, hi⟩ : A)]
      · simp
      · intro a _ hn
        have hn' : a.val ≠ i := fun h => hn (Subtype.ext h)
        simp [Ne.symm hn']
      · simp
    · simp [ht i hi, show ∀ a : A, a.val ≠ i from fun a h => hi (h ▸ a.property)]
  have hs : (∑ a : A, t.val a.val • T.mkQ (Pi.basisFun K ι a.val)) = 0 := by
    calc
      _ = T.mkQ (∑ a : A, t.val a.val • Pi.basisFun K ι a.val) := by simp only [map_sum, map_smul]
      _ = 0 := by rw [he]; exact (Submodule.Quotient.mk_eq_zero T).mpr t.property
  have hall := (Fintype.linearIndependent_iff.mp hA.1) _ hs
  apply Subtype.ext
  ext i
  by_cases hi : i ∈ A
  · exact hall ⟨i,hi⟩
  · exact ht i hi

end Linear

section PolynomialChain
variable {C E ι κ : Type*} [Field C] [Field E] [Algebra C E] [Fintype ι] [Fintype κ]

theorem polynomialGradient_mul (φ : MvPolynomial ι C →ₐ[C] E) (t : ι → E)
    (p q : MvPolynomial ι C) :
    (∑ i, φ (pderiv i (p*q)) * t i) =
      φ p * (∑ i, φ (pderiv i q) * t i) +
      φ q * (∑ i, φ (pderiv i p) * t i) := by
  simp only [pderiv_mul, map_add, map_mul, add_mul, Finset.sum_add_distrib]
  simp only [Finset.mul_sum]
  conv_lhs => rw [add_comm]
  congr 1 <;> apply Finset.sum_congr rfl <;> intro i _ <;> ring

theorem polynomialGradient_rename (φ : MvPolynomial ι C →ₐ[C] E) (t : ι → E)
    (f : κ → ι) (p : MvPolynomial κ C) :
    (∑ i, φ (pderiv i (rename f p)) * t i) =
      ∑ j, φ (rename f (pderiv j p)) * t (f j) := by
  classical
  induction p using MvPolynomial.induction_on with
  | C c => simp
  | add p q hp hq => simp [hp,hq, add_mul, Finset.sum_add_distrib]
  | mul_X p j hp =>
    rw [map_mul, polynomialGradient_mul, hp]
    have hgrad : (∑ i, φ (pderiv i (rename f (X j))) * t i) = t (f j) := by
      simp [Pi.single_apply]
    rw [hgrad]
    let ψ : MvPolynomial κ C →ₐ[C] E := φ.comp (rename f)
    have hR := polynomialGradient_mul ψ (t ∘ f) p (X j)
    change _ = ∑ i, ψ (pderiv i (p * X j)) * (t ∘ f) i
    rw [hR]
    simp [ψ, Pi.single_apply]

end PolynomialChain

section KernelCriterion
variable {C E ι : Type*} [Field C] [CharZero C] [Field E] [Algebra C E] [Fintype ι]

omit [CharZero C] in
theorem pderiv_totalDegree_lt_of_pos (p : MvPolynomial ι C) (hp : 0 < p.totalDegree)
    (i : ι) : (pderiv i p).totalDegree < p.totalDegree := by
  classical
  apply lt_of_le_of_lt (show (pderiv i p).totalDegree ≤ p.totalDegree - 1 from ?_)
    (Nat.sub_lt hp (by omega))
  apply Finset.sup_le
  intro m hm
  have hcoeff : p.coeff (m + Finsupp.single i 1) ≠ 0 := by
    have hh := (mem_support_iff.mp hm)
    rw [coeff_pderiv] at hh
    exact (mul_ne_zero_iff.mp hh).1
  have hb := le_totalDegree (mem_support_iff.mpr hcoeff)
  have hsum : (m + Finsupp.single i 1).sum (fun _ e => e) =
      m.sum (fun _ e => e) + 1 := by
    simp [Finsupp.sum_fintype, Finset.sum_add_distrib]
  rw [hsum] at hb
  omega

theorem eq_C_of_pderiv_eq_zero (p : MvPolynomial ι C)
    (hp : ∀ i, pderiv i p = 0) : p = MvPolynomial.C (p.coeff 0) := by
  classical
  ext m
  by_cases hm : m = 0
  · subst m; simp
  · rw [coeff_C, ite_eq_right (Ne.symm hm)]
    have hex : ∃ i, m i ≠ 0 := by
      by_contra! h
      apply hm
      ext i
      exact h i
    obtain ⟨i, hi'⟩ := hex
    have hc := congrArg (fun p : MvPolynomial ι C => p.coeff (m - Finsupp.single i 1)) (hp i)
    rw [coeff_pderiv, Finsupp.sub_add_single_one_cancel hi'] at hc
    have hpos : 0 < ((m - Finsupp.single i 1 : ι →₀ ℕ) i) + 1 := by omega
    have hn : ((((m - Finsupp.single i 1 : ι →₀ ℕ) i) : C) + 1) ≠ 0 := by
      exact_mod_cast (Nat.ne_of_gt hpos)
    rw [AddMonoidAlgebra.coeff_zero, Finsupp.zero_apply] at hc
    exact (mul_eq_zero.mp hc).resolve_right hn

theorem algebraicIndependent_of_pderiv_kernel (x : ι → E)
    (hker : ∀ p : MvPolynomial ι C, aeval x p = 0 →
      ∀ i, aeval x (pderiv i p) = 0) : AlgebraicIndependent C x := by
  apply algebraicIndependent_iff.mpr
  intro p
  induction hp : p.totalDegree using Nat.strong_induction_on generalizing p with
  | h n ih =>
    intro hz
    by_cases hn : n = 0
    · have he := totalDegree_eq_zero_iff_eq_C.mp (hp.trans hn)
      rw [he, aeval_C] at hz
      have hconstant : p.coeff 0 = 0 := (algebraMap C E).injective (by simpa using hz)
      rw [he, hconstant, map_zero]
    · have hpartials : ∀ i, pderiv i p = 0 := by
        intro i
        exact ih _ (hp ▸ pderiv_totalDegree_lt_of_pos p (by omega) i)
          _ rfl (hker p hz i)
      have he := eq_C_of_pderiv_eq_zero p hpartials
      rw [he, aeval_C] at hz
      have hconstant : p.coeff 0 = 0 := (algebraMap C E).injective (by simpa using hz)
      rw [he, hconstant, map_zero]

theorem normalBasis_complement_algebraicIndependent
    (φ : MvPolynomial ι C →ₐ[C] E) (Q : Ideal (MvPolynomial ι C))
    (hker : ∀ p, φ p = 0 → p ∈ Q)
    (A : Finset ι)
    (hA : IsNormalBasis (K := E)
      (fun i => (polynomialTangent φ Q).mkQ (Pi.basisFun E ι i)) A) :
    AlgebraicIndependent C (fun i : {i // i ∉ A} => φ (X i.val)) := by
  classical
  let x : {i // i ∉ A} → E := fun i => φ (X i.val)
  have hφ (p : MvPolynomial {i // i ∉ A} C) : φ (rename Subtype.val p) = aeval x p := by
    have he : φ.comp (rename Subtype.val) = aeval x := by ext i; simp [x]
    exact AlgHom.congr_fun he p
  apply algebraicIndependent_of_pderiv_kernel
  intro p hp j
  obtain ⟨t,ht⟩ := normalBasis_complement_surjective (polynomialTangent φ Q) A hA
    (Pi.single j 1)
  have hmem : rename Subtype.val p ∈ Q := hker _ ((hφ p).trans hp)
  have heq : (∑ i, φ (pderiv i (rename Subtype.val p)) * t.val i) = 0 := by
    exact congrFun t.property ⟨rename Subtype.val p,hmem⟩
  rw [polynomialGradient_rename] at heq
  have hv : ∀ i : {i // i ∉ A}, t.val i.val = (Pi.single j (1 : E) : {i // i ∉ A} → E) i := by
    intro i
    exact congrFun ht i
  simpa [hv, hφ, Pi.single_apply, x] using heq

end KernelCriterion

section Algebraicity
open KaehlerDifferential
variable {C E ι : Type*} [Field C] [CharZero C] [Field E] [Algebra C E] [Fintype ι]

omit [CharZero C] [Fintype ι] in
theorem derivation_eq_zero_of_field_generators
    (x : ι → E) (hgen : IntermediateField.adjoin C (Set.range x) = ⊤)
    (d : Derivation C E E) (hd : ∀ i, d (x i) = 0) : d = 0 := by
  have hp : ∀ a ∈ Algebra.adjoin C (Set.range x), d a = 0 := by
    exact Derivation.eqOn_adjoin (D1 := d) (D2 := 0) (by rintro _ ⟨i,rfl⟩; exact hd i)
  apply Derivation.ext
  intro z
  have hz : z ∈ IntermediateField.adjoin C (Set.range x) := by rw [hgen]; trivial
  obtain ⟨a,ha,b,hb,rfl⟩ := IntermediateField.mem_adjoin_iff_div.mp hz
  change d (a / b) = 0
  rw [d.leibniz_div, hp a ha, hp b hb, smul_zero, smul_zero, sub_self, smul_zero]

theorem normalBasis_complement_isAlgebraic
    [Algebra.EssFiniteType C E]
    (φ : MvPolynomial ι C →ₐ[C] E) (Q : Ideal (MvPolynomial ι C))
    (hQ : ∀ p ∈ Q, φ p = 0)
    (hgen : IntermediateField.adjoin C (Set.range (fun i => φ (X i))) = ⊤)
    (A : Finset ι)
    (hA : IsNormalBasis (K := E)
      (fun i => (polynomialTangent (φ) Q).mkQ
        (Pi.basisFun (E) ι i)) A) :
    Algebra.IsAlgebraic
      (IntermediateField.adjoin C
        (Set.range (fun i : {i // i ∉ A} => φ (X i.val))))
      (E) := by
  classical
  let K := IntermediateField.adjoin C
    (Set.range (fun i : {i // i ∉ A} => φ (X i.val)))
  have hdzero (d : Derivation K E E) : d = 0 := by
    let dC := d.restrictScalars C
    let t : polynomialTangent (φ) Q :=
      ⟨(fun i => dC (φ (X i))),
        derivation_mem_polynomialTangent _ _ hQ dC⟩
    have ht : t = 0 := normalBasis_complement_injective _ A hA (by
      funext i
      change d (φ (X i.val)) = 0
      let k : K := ⟨φ (X i.val),
        IntermediateField.subset_adjoin C _ (Set.mem_range_self i)⟩
      exact d.map_algebraMap k)
    have hc : ∀ i, dC (φ (X i)) = 0 := by
      intro i
      exact congrFun (congrArg Subtype.val ht) i
    have hh := derivation_eq_zero_of_field_generators (fun i => φ (X i)) hgen dC hc
    ext z
    exact DFunLike.congr_fun hh z
  let : Algebra.EssFiniteType K E := Algebra.EssFiniteType.of_comp C K E
  constructor
  intro z
  have hz : D K E z = 0 := by
    apply (Module.forall_dual_apply_eq_zero_iff E _).mp
    intro l
    let d : Derivation K E E := l.compDer (D K E)
    exact DFunLike.congr_fun (hdzero d) z
  exact isAlgebraic_of_logarithmic_differential (C := K) (0 : E) z (by rw [map_zero, hz, smul_zero])

end Algebraicity

section TranscendenceBasis
open scoped IntermediateField.algebraAdjoinAdjoin
variable {C E ι : Type*} [Field C] [CharZero C] [Field E] [Algebra C E] [Fintype ι]

theorem normalBasis_complement_isTranscendenceBasis
    [Algebra.EssFiniteType C E]
    (φ : MvPolynomial ι C →ₐ[C] E) (Q : Ideal (MvPolynomial ι C))
    (hQ : ∀ p, φ p = 0 ↔ p ∈ Q)
    (hgen : IntermediateField.adjoin C (Set.range (fun i => φ (X i))) = ⊤)
    (A : Finset ι)
    (hA : IsNormalBasis (K := E)
      (fun i => (polynomialTangent φ Q).mkQ (Pi.basisFun E ι i)) A) :
    IsTranscendenceBasis C (fun i : {i // i ∉ A} => φ (X i.val)) := by
  have hind := normalBasis_complement_algebraicIndependent φ Q
    (fun p => (hQ p).mp) A hA
  apply hind.isTranscendenceBasis_iff_isAlgebraic.mpr
  let K := IntermediateField.adjoin C
    (Set.range (fun i : {i // i ∉ A} => φ (X i.val)))
  let : Algebra.IsAlgebraic K E := normalBasis_complement_isAlgebraic φ Q
    (fun p => (hQ p).mpr) hgen A hA
  exact Algebra.IsAlgebraic.trans _ K E

end TranscendenceBasis

variable {C ι : Type*} [Field C] [Fintype ι]

omit [Fintype ι] in

theorem polynomialResidueMap_field_generation
    (Q : Ideal (MvPolynomial ι C)) [Q.IsPrime] :
    IntermediateField.adjoin C (Set.range (fun i => polynomialResidueMap Q (X i))) = ⊤ := by
  apply top_unique
  intro z _
  obtain ⟨a,b,hb,hz⟩ := IsFractionRing.div_surjective (MvPolynomial ι C ⧸ Q) z
  obtain ⟨a,rfl⟩ := Ideal.Quotient.mk_surjective a
  obtain ⟨b,rfl⟩ := Ideal.Quotient.mk_surjective b
  have he : aeval (fun i => polynomialResidueMap Q (X i)) = polynomialResidueMap Q := by
    ext i
    simp
  apply (IntermediateField.mem_adjoin_range_iff C _ z).mpr
  refine ⟨a,b,?_⟩
  rw [he]
  exact hz.symm

omit [Fintype ι] in

theorem idealResidueMap_field_generation
    (Q : Ideal (MvPolynomial ι C)) [Q.IsPrime] :
    IntermediateField.adjoin C
      (Set.range (fun i => algebraMap (MvPolynomial ι C) Q.ResidueField (X i))) = ⊤ := by
  apply top_unique
  intro z _
  obtain ⟨a,b,hb,hz⟩ := IsFractionRing.div_surjective (MvPolynomial ι C ⧸ Q) z
  obtain ⟨a,rfl⟩ := Ideal.Quotient.mk_surjective a
  obtain ⟨b,rfl⟩ := Ideal.Quotient.mk_surjective b
  have he : aeval (fun i => algebraMap (MvPolynomial ι C) Q.ResidueField (X i)) =
      IsScalarTower.toAlgHom C (MvPolynomial ι C) Q.ResidueField := by
    ext i
    simp
  apply (IntermediateField.mem_adjoin_range_iff C _ z).mpr
  refine ⟨a,b,?_⟩
  rw [he]
  simpa only [IsScalarTower.coe_toAlgHom', Ideal.algebraMap_quotient_residueField_mk] using hz.symm

theorem idealResidueNormalBasis_complement_isTranscendenceBasis
    [CharZero C] (Q : Ideal (MvPolynomial ι C)) [Q.IsPrime] (A : Finset ι)
    (hA : IsNormalBasis (K := Q.ResidueField)
      (fun i => (polynomialTangent
        (IsScalarTower.toAlgHom C (MvPolynomial ι C) Q.ResidueField) Q).mkQ
          (Pi.basisFun Q.ResidueField ι i)) A) :
    IsTranscendenceBasis C
      (fun i : {i // i ∉ A} => algebraMap (MvPolynomial ι C) Q.ResidueField (X i.val)) := by
  let : Algebra.EssFiniteType C Q.ResidueField :=
    .comp C (MvPolynomial ι C) Q.ResidueField
  exact normalBasis_complement_isTranscendenceBasis
    (IsScalarTower.toAlgHom C (MvPolynomial ι C) Q.ResidueField) Q
    (fun _ => Ideal.algebraMap_residueField_eq_zero)
    (idealResidueMap_field_generation Q) A hA

end PiExponent

end

end OAI
end Source0136

-- Source: OAI/NumberTheory/PiExponent/LocalAlgebra/PointLengthEquiv.lean
section Source0137
/-
Modification notice for the LogTwo project.
Derived from openai/math (Apache-2.0), revision adc7f1241b42e322a6451854ab7e4b4c146bf78a.
Original source: lean/OAI/NumberTheory/PiExponent/LocalAlgebra/PointLengthEquiv.lean
Changes: Convert module/import declarations to the Lean 4.34 public module format.
See ../THIRD_PARTY_NOTICES.txt for provenance and the recorded changes.
-/

namespace OAI

namespace PiExponent.PointLengthEquiv

open PiExponent.WeightedBezout

variable {E F ι : Type*} [Field E] [Field F]

theorem evaluation_map (e : E ≃+* F) (b : ι → E) (p : MvPolynomial ι E) :
    MvPolynomial.aeval (fun i => e (b i)) (MvPolynomial.map e.toRingHom p) =
      e (MvPolynomial.aeval b p) := by
  simpa [MvPolynomial.aeval_def] using
    ((MvPolynomial.eval_map e.toRingHom (fun i => e (b i)) p).trans
      (MvPolynomial.eval₂_comp e.toRingHom b p).symm)

theorem pointIdeal_comap (e : E ≃+* F) (b : ι → E) :
    pointIdeal b = (pointIdeal (fun i => e (b i))).comap
      (MvPolynomial.mapEquiv ι e).toRingHom := by
  ext p
  change MvPolynomial.aeval b p = 0 ↔
    MvPolynomial.aeval (fun i => e (b i)) (MvPolynomial.map e.toRingHom p) = 0
  rw [evaluation_map]
  exact e.map_eq_zero_iff.symm

theorem pointIdeal_map (e : E ≃+* F) (b : ι → E) :
    (pointIdeal b).map (MvPolynomial.mapEquiv ι e).toRingHom =
      pointIdeal (fun i => e (b i)) := by
  rw [pointIdeal_comap e b]
  exact Ideal.map_comap_of_surjective (MvPolynomial.mapEquiv ι e).toRingHom
    (MvPolynomial.mapEquiv ι e).surjective _

theorem pointLocal_quotient_length (e : E ≃+* F) (b : ι → E)
    (I : Ideal (MvPolynomial ι E)) :
    Module.length (Localization.AtPrime (pointIdeal b))
      (Localization.AtPrime (pointIdeal b) ⧸
        I.map (algebraMap _ (Localization.AtPrime (pointIdeal b)))) =
    Module.length (Localization.AtPrime (pointIdeal (fun i => e (b i))))
      (Localization.AtPrime (pointIdeal (fun i => e (b i))) ⧸
        (I.map (MvPolynomial.map e.toRingHom)).map
          (algebraMap _ (Localization.AtPrime (pointIdeal (fun i => e (b i)))))) := by
  exact PiExponentJets.W22.localized_quotient_length_eq_of_ringEquiv
    (MvPolynomial.mapEquiv ι e) (pointIdeal b) (pointIdeal (fun i => e (b i)))
    (pointIdeal_comap e b) I

theorem point_mem_minimalPrimes_map (e : E ≃+* F) (b : ι → E)
    (I : Ideal (MvPolynomial ι E)) (hI : pointIdeal b ∈ I.minimalPrimes) :
    pointIdeal (fun i => e (b i)) ∈ (I.map (MvPolynomial.map e.toRingHom)).minimalPrimes := by
  let φ := MvPolynomial.mapEquiv ι e
  change pointIdeal (fun i => e (b i)) ∈ (I.map φ.toRingHom).minimalPrimes
  have hker : RingHom.ker φ.toRingHom = ⊥ := by
    ext p
    change φ p = 0 ↔ p = 0
    exact φ.map_eq_zero_iff
  rw [Ideal.minimalPrimes_map_of_surjective (f := φ.toRingHom) φ.surjective, hker, sup_bot_eq]
  exact ⟨pointIdeal b, hI, pointIdeal_map e b⟩

end PiExponent.PointLengthEquiv

end OAI
end Source0137

-- Source: OAI/NumberTheory/PiExponent/Approximation/CoordinateSliceComparison.lean
section Source0138
/-
Modification notice for the LogTwo project.
Derived from openai/math (Apache-2.0), revision adc7f1241b42e322a6451854ab7e4b4c146bf78a.
Original source: lean/OAI/NumberTheory/PiExponent/Approximation/CoordinateSliceComparison.lean
Changes: Convert module/import declarations to the Lean 4.34 public module format.
See ../THIRD_PARTY_NOTICES.txt for provenance and the recorded changes.
-/

namespace OAI

noncomputable section
namespace PiExponent.CoordinateSliceComparison

open PiExponentJets.PolynomialLocalResidueResolution
open CoordinateFiniteSlice

variable {K ι : Type*} [Field K] [Fintype ι]

abbrev primeLength {R : Type*} [CommRing R] (Q : Ideal R) [Q.IsPrime] (I : Ideal R) : ℕ∞ :=
  Module.length (Localization.AtPrime Q)
    (Localization.AtPrime Q ⧸ I.map (algebraMap R (Localization.AtPrime Q)))

omit [Fintype ι] in
theorem splitBasis (Q : Ideal (MvPolynomial ι K)) [Q.IsPrime] (A : Finset ι)
    (hB : IsTranscendenceBasis K (fun i : {i // i ∉ A} => residueCoordinates Q i.val)) :
    IsTranscendenceBasis K
      (splitResidueBeta K (Fin A.card) {i // i ∉ A} (splitPrime Q A)) :=
  complementary_transcendenceBasis Q A hB

omit [Fintype ι] in
theorem map_residueSlice_eq_enumeratedSliceMap
    (Q : Ideal (MvPolynomial ι K)) [Q.IsPrime] (A : Finset ι) :
    (MvPolynomial.map (residueEquiv Q A).symm.toRingHom).comp
      ((CoordinateSliceLength.residueSlice K (Fin A.card) {i // i ∉ A} (splitPrime Q A)).comp
        (coordinateRenaming (K := K) A).toRingHom) =
      (WeightedSliceDegree.enumeratedSliceMap (C := K) A (residueCoordinates Q)).toRingHom := by
  apply MvPolynomial.ringHom_ext
  · intro c
    simp [CoordinateSliceLength.residueSlice, coordinateRenaming,
      WeightedSliceDegree.enumeratedSliceMap, WeightedSliceDegree.sliceMap,
      MvPolynomial.algebraMap_eq, AlgEquiv.commutes]
  · intro i
    obtain ⟨j, rfl⟩ := (coordinateEquiv A).surjective i
    cases j with
    | inl j =>
      simp [RingHom.comp_apply, CoordinateSliceLength.residueSlice]
    | inr j =>
      change MvPolynomial.map (residueEquiv Q A).symm.toRingHom
        (CoordinateSliceLength.residueSlice K (Fin A.card) {i // i ∉ A} (splitPrime Q A)
          (coordinateRenaming (K := K) A (MvPolynomial.X j.val))) =
        WeightedSliceDegree.enumeratedSliceMap (C := K) A (residueCoordinates Q) (MvPolynomial.X j.val)
      rw [coordinateRenaming_X_inr]
      rw [show CoordinateSliceLength.residueSlice K (Fin A.card) {i // i ∉ A} (splitPrime Q A)
          (MvPolynomial.X (Sum.inr j)) =
          MvPolynomial.C (splitResidueBeta K (Fin A.card) {i // i ∉ A} (splitPrime Q A) j) by
        simp [CoordinateSliceLength.residueSlice]]
      rw [MvPolynomial.map_C, enumeratedSliceMap_X_inr]
      exact congrArg MvPolynomial.C (residueEquiv_symm_coordinate_inr Q A j)

omit [Fintype ι] in
theorem map_splitPoint_eq (Q : Ideal (MvPolynomial ι K)) [Q.IsPrime] (A : Finset ι) :
    (fun i => (residueEquiv Q A).symm.toRingEquiv
      (CoordinateSliceLength.slicePoint K (Fin A.card) {i // i ∉ A} (splitPrime Q A) i)) =
      slicePoint Q A := by
  funext i
  exact residueEquiv_symm_coordinate_inl Q A i

omit [Fintype ι] in
theorem map_slice_ideal (Q I : Ideal (MvPolynomial ι K)) [Q.IsPrime] (A : Finset ι) :
    ((I.map (coordinateRenaming (K := K) A).toRingHom).map
      (CoordinateSliceLength.residueSlice K (Fin A.card) {i // i ∉ A} (splitPrime Q A))).map
      (MvPolynomial.map (residueEquiv Q A).symm.toRingHom) =
    I.map (WeightedSliceDegree.enumeratedSliceMap (C := K) A (residueCoordinates Q)).toRingHom := by
  rw [Ideal.map_map, Ideal.map_map]
  congr 1
  exact map_residueSlice_eq_enumeratedSliceMap Q A

theorem length_eq_enumeratedSlice [CharZero K]
    (Q I : Ideal (MvPolynomial ι K)) [Q.IsPrime] (A : Finset ι)
    (hB : IsTranscendenceBasis K (fun i : {i // i ∉ A} => residueCoordinates Q i.val)) :
    primeLength Q I = primeLength (WeightedBezout.pointIdeal (slicePoint Q A))
      (I.map (WeightedSliceDegree.enumeratedSliceMap (C := K) A (residueCoordinates Q)).toRingHom) := by
  have h₁ := PiExponentJets.W22.localized_quotient_length_eq_of_ringEquiv
    (coordinateRenaming (K := K) A).toRingEquiv Q (splitPrime Q A)
    (PiExponentSiegel.W23.atPrimeImage_comap (coordinateRenaming (K := K) A).toRingEquiv Q) I
  have h₂ := CoordinateSliceLength.length_eq_residueSlice K (Fin A.card) {i // i ∉ A}
    (splitPrime Q A) (splitBasis Q A hB) (I.map (coordinateRenaming (K := K) A).toRingHom)
  have h₃ := PointLengthEquiv.pointLocal_quotient_length (residueEquiv Q A).symm.toRingEquiv
    (CoordinateSliceLength.slicePoint K (Fin A.card) {i // i ∉ A} (splitPrime Q A))
    ((I.map (coordinateRenaming (K := K) A).toRingHom).map
      (CoordinateSliceLength.residueSlice K (Fin A.card) {i // i ∉ A} (splitPrime Q A)))
  rw [map_slice_ideal, map_splitPoint_eq] at h₃
  exact h₁.trans (h₂.trans h₃)

theorem slicePoint_mem_minimalPrimes
    (Q I : Ideal (MvPolynomial ι K)) [Q.IsPrime] (A : Finset ι)
    (hB : IsTranscendenceBasis K (fun i : {i // i ∉ A} => residueCoordinates Q i.val))
    (hQ : Q ∈ I.minimalPrimes) :
    WeightedBezout.pointIdeal (slicePoint Q A) ∈
      (I.map (WeightedSliceDegree.enumeratedSliceMap (C := K) A (residueCoordinates Q)).toRingHom).minimalPrimes := by
  have h₁ := splitPrime_mem_minimalPrimes Q I A hQ
  have h₂ := CoordinateSliceLength.slicePoint_mem_minimalPrimes K (Fin A.card) {i // i ∉ A}
    (splitPrime Q A) (splitBasis Q A hB) (I.map (coordinateRenaming (K := K) A).toRingHom) h₁
  have h₃ := PointLengthEquiv.point_mem_minimalPrimes_map (residueEquiv Q A).symm.toRingEquiv
    (CoordinateSliceLength.slicePoint K (Fin A.card) {i // i ∉ A} (splitPrime Q A))
    ((I.map (coordinateRenaming (K := K) A).toRingHom).map
      (CoordinateSliceLength.residueSlice K (Fin A.card) {i // i ∉ A} (splitPrime Q A))) h₂
  rw [map_slice_ideal, map_splitPoint_eq] at h₃
  exact h₃

theorem length_eq_enumeratedSlice_of_normalBasis [CharZero K]
    (Q I : Ideal (MvPolynomial ι K)) [Q.IsPrime] (A : Finset ι)
    (hA : NormalBasisRigidity.IsNormalBasis (K := Q.ResidueField)
      (fun i => (polynomialTangent
        (IsScalarTower.toAlgHom K (MvPolynomial ι K) Q.ResidueField) Q).mkQ
        (Pi.basisFun Q.ResidueField ι i)) A) :
    primeLength Q I = primeLength (WeightedBezout.pointIdeal (slicePoint Q A))
      (I.map (WeightedSliceDegree.enumeratedSliceMap (C := K) A (residueCoordinates Q)).toRingHom) :=
  length_eq_enumeratedSlice Q I A
    (idealResidueNormalBasis_complement_isTranscendenceBasis Q A hA)

theorem slicePoint_mem_minimalPrimes_of_normalBasis [CharZero K]
    (Q I : Ideal (MvPolynomial ι K)) [Q.IsPrime] (A : Finset ι)
    (hA : NormalBasisRigidity.IsNormalBasis (K := Q.ResidueField)
      (fun i => (polynomialTangent
        (IsScalarTower.toAlgHom K (MvPolynomial ι K) Q.ResidueField) Q).mkQ
        (Pi.basisFun Q.ResidueField ι i)) A)
    (hQ : Q ∈ I.minimalPrimes) :
    WeightedBezout.pointIdeal (slicePoint Q A) ∈
      (I.map (WeightedSliceDegree.enumeratedSliceMap (C := K) A (residueCoordinates Q)).toRingHom).minimalPrimes :=
  slicePoint_mem_minimalPrimes Q I A
    (idealResidueNormalBasis_complement_isTranscendenceBasis Q A hA) hQ

omit [Fintype ι] in
theorem map_span_sliceFamily
    (Q : Ideal (MvPolynomial ι K)) [Q.IsPrime] (A : Finset ι)
    {J : Type*} (f : J → MvPolynomial ι K) :
    (Ideal.span (Set.range f)).map
      (WeightedSliceDegree.enumeratedSliceMap (C := K) A (residueCoordinates Q)).toRingHom =
    Ideal.span (Set.range (fun j =>
      WeightedSliceDegree.enumeratedSliceMap (C := K) A (residueCoordinates Q) (f j))) := by
  rw [Ideal.map_span, ← Set.range_comp]
  rfl

theorem length_eq_sliceFamily_of_normalBasis [CharZero K]
    (Q : Ideal (MvPolynomial ι K)) [Q.IsPrime] (A : Finset ι)
    (hA : NormalBasisRigidity.IsNormalBasis (K := Q.ResidueField)
      (fun i => (polynomialTangent
        (IsScalarTower.toAlgHom K (MvPolynomial ι K) Q.ResidueField) Q).mkQ
        (Pi.basisFun Q.ResidueField ι i)) A)
    {J : Type*} (f : J → MvPolynomial ι K) :
    primeLength Q (Ideal.span (Set.range f)) =
      primeLength (WeightedBezout.pointIdeal (slicePoint Q A))
        (Ideal.span (Set.range (fun j =>
          WeightedSliceDegree.enumeratedSliceMap (C := K) A (residueCoordinates Q) (f j)))) := by
  have h := length_eq_enumeratedSlice_of_normalBasis Q (Ideal.span (Set.range f)) A hA
  rw [map_span_sliceFamily] at h
  exact h

theorem sliceFamily_mem_minimalPrimes_of_normalBasis [CharZero K]
    (Q : Ideal (MvPolynomial ι K)) [Q.IsPrime] (A : Finset ι)
    (hA : NormalBasisRigidity.IsNormalBasis (K := Q.ResidueField)
      (fun i => (polynomialTangent
        (IsScalarTower.toAlgHom K (MvPolynomial ι K) Q.ResidueField) Q).mkQ
        (Pi.basisFun Q.ResidueField ι i)) A)
    {J : Type*} (f : J → MvPolynomial ι K)
    (hQ : Q ∈ (Ideal.span (Set.range f)).minimalPrimes) :
    WeightedBezout.pointIdeal (slicePoint Q A) ∈
      (Ideal.span (Set.range (fun j =>
        WeightedSliceDegree.enumeratedSliceMap (C := K) A (residueCoordinates Q) (f j)))).minimalPrimes := by
  have h := slicePoint_mem_minimalPrimes_of_normalBasis Q (Ideal.span (Set.range f)) A hA hQ
  rw [map_span_sliceFamily] at h
  exact h

end PiExponent.CoordinateSliceComparison

end

end OAI
end Source0138

-- Source: OAI/NumberTheory/PiExponent/LocalAlgebra/FlatLocalLength.lean
section Source0139
-- Modified in this edition: unused plain lemmas removed; see reduction.json.
/-
Modification notice for the LogTwo project.
Derived from openai/math (Apache-2.0), revision adc7f1241b42e322a6451854ab7e4b4c146bf78a.
Original source: lean/OAI/NumberTheory/PiExponent/LocalAlgebra/FlatLocalLength.lean
Changes: Convert module/import declarations to the Lean 4.34 public module format.
See ../THIRD_PARTY_NOTICES.txt for provenance and the recorded changes.
-/

namespace OAI

noncomputable section
namespace PiExponentJets.W25

open TensorProduct

variable {A B : Type*} [CommRing A] [CommRing B] [Algebra A B]
  [IsLocalRing A] [IsLocalRing B]

theorem simple_baseChange_of_map_maximalIdeal
    (hmax : (IsLocalRing.maximalIdeal A).map (algebraMap A B) =
      IsLocalRing.maximalIdeal B)
    {M : Type*} [AddCommGroup M] [Module A M] [IsSimpleModule A M] :
    IsSimpleModule B (B ⊗[A] M) := by
  obtain ⟨J, hJ, ⟨e⟩⟩ :=
    (isSimpleModule_iff_quot_maximal (R := A) (M := M)).mp inferInstance
  have hJmax : J = IsLocalRing.maximalIdeal A := IsLocalRing.eq_maximalIdeal hJ
  subst J
  have : IsSimpleModule B (B ⧸ IsLocalRing.maximalIdeal B) :=
    isSimpleModule_iff_isCoatom.mpr
      (Ideal.isMaximal_def.mp (inferInstance : (IsLocalRing.maximalIdeal B).IsMaximal))
  let eB : (B ⊗[A] M) ≃ₗ[B] (B ⧸ IsLocalRing.maximalIdeal B) :=
    (e.baseChange A B M (A ⧸ IsLocalRing.maximalIdeal A)).trans
      ((Algebra.TensorProduct.quotIdealMapEquivTensorQuot B
        (IsLocalRing.maximalIdeal A)).toLinearEquiv.symm.trans
        (Submodule.quotEquivOfEq _ _ hmax))
  exact IsSimpleModule.congr eB

theorem length_baseChange_of_flat_local [Module.Flat A B]
    (hmax : (IsLocalRing.maximalIdeal A).map (algebraMap A B) =
      IsLocalRing.maximalIdeal B)
    {M : Type*} [AddCommGroup M] [Module A M] (hM : IsFiniteLength A M) :
    Module.length B (B ⊗[A] M) = Module.length A M := by
  induction hM with
  | of_subsingleton =>
    simp only [Module.length_eq_zero]
  | @of_simple_quotient M _ _ N hsimple hN ih =>
    have : IsSimpleModule B (B ⊗[A] (M ⧸ N)) :=
      simple_baseChange_of_map_maximalIdeal hmax
    have hexact : Function.Exact N.subtype N.mkQ := by
      rw [LinearMap.exact_iff, Submodule.range_subtype, Submodule.ker_mkQ]
    have hinj : Function.Injective (N.subtype.baseChange B) :=
      Module.Flat.lTensor_preserves_injective_linearMap N.subtype
        (Submodule.subtype_injective N)
    have hsurj : Function.Surjective (N.mkQ.baseChange B) :=
      LinearMap.lTensor_surjective B (Submodule.mkQ_surjective N)
    have hbaseexact : Function.Exact (N.subtype.baseChange B) (N.mkQ.baseChange B) :=
      Module.Flat.lTensor_exact B hexact
    have hA := Module.length_eq_add_of_exact N.subtype N.mkQ
      (Submodule.subtype_injective N) (Submodule.mkQ_surjective N) hexact
    have hB := Module.length_eq_add_of_exact (N.subtype.baseChange B)
      (N.mkQ.baseChange B) hinj hsurj hbaseexact
    calc
      Module.length B (B ⊗[A] M) =
          Module.length B (B ⊗[A] N) + Module.length B (B ⊗[A] (M ⧸ N)) := hB
      _ = Module.length A N + Module.length A (M ⧸ N) := by
        rw [ih, Module.length_eq_one B (B ⊗[A] (M ⧸ N)),
          Module.length_eq_one A (M ⧸ N)]
      _ = Module.length A M := hA.symm

theorem length_quotient_map_of_flat_local [Module.Flat A B]
    (hmax : (IsLocalRing.maximalIdeal A).map (algebraMap A B) =
      IsLocalRing.maximalIdeal B)
    (I : Ideal A) (hI : IsFiniteLength A (A ⧸ I)) :
    Module.length B (B ⧸ I.map (algebraMap A B)) = Module.length A (A ⧸ I) := by
  calc
    Module.length B (B ⧸ I.map (algebraMap A B)) =
        Module.length B (B ⊗[A] (A ⧸ I)) :=
      (Algebra.TensorProduct.quotIdealMapEquivTensorQuot B I).toLinearEquiv.length_eq
    _ = Module.length A (A ⧸ I) := length_baseChange_of_flat_local hmax hI

end PiExponentJets.W25

end

end OAI
end Source0139

-- Source: OAI/NumberTheory/PiExponent/LocalAlgebra/ConeLocalLength.lean
section Source0140
-- Modified in this edition: unused plain lemmas removed; see reduction.json.
/-
Modification notice for the LogTwo project.
Derived from openai/math (Apache-2.0), revision adc7f1241b42e322a6451854ab7e4b4c146bf78a.
Original source: lean/OAI/NumberTheory/PiExponent/LocalAlgebra/ConeLocalLength.lean
Changes: Convert module/import declarations to the Lean 4.34 public module format.
See ../THIRD_PARTY_NOTICES.txt for provenance and the recorded changes.
-/

namespace OAI

noncomputable section

namespace PiExponentSiegel.W17.ConeLocalLength

attribute [local instance] Localization.AtPrime.algebraOfLiesOver

section ExtendedPrime

variable {A B : Type*} [CommRing A] [CommRing B] [Algebra A B]
    (P : Ideal A) [P.IsPrime] (Q : Ideal B) [Q.IsPrime] [Q.LiesOver P]

theorem localized_maximalIdeal_map_eq (hQ : Q = P.map (algebraMap A B)) :
    (IsLocalRing.maximalIdeal (Localization.AtPrime P)).map
      (algebraMap (Localization.AtPrime P) (Localization.AtPrime Q)) =
    IsLocalRing.maximalIdeal (Localization.AtPrime Q) := by
  rw [← IsLocalization.AtPrime.map_eq_maximalIdeal P (Localization.AtPrime P),
    Ideal.map_map, ← IsScalarTower.algebraMap_eq A (Localization.AtPrime P)
      (Localization.AtPrime Q),
    IsScalarTower.algebraMap_eq A B (Localization.AtPrime Q), ← Ideal.map_map, ← hQ]
  exact IsLocalization.AtPrime.map_eq_maximalIdeal Q (Localization.AtPrime Q)

end ExtendedPrime

section PolynomialExtension

variable (A : Type*) [CommRing A] (P : Ideal A) [P.IsPrime]

abbrev polynomialPrime : Ideal (Polynomial A) := P.map Polynomial.C

omit [P.IsPrime] in
theorem polynomialPrime_comap :
    (polynomialPrime A P).comap (algebraMap A (Polynomial A)) = P := by
  ext a
  change Polynomial.C a ∈ P.map Polynomial.C ↔ a ∈ P
  rw [Ideal.mem_map_C_iff]
  constructor
  · intro h
    simpa using h 0
  · intro ha n
    by_cases hn : n = 0
    · subst n
      simpa using ha
    · simp [Polynomial.coeff_C, hn]

instance polynomialPrime_liesOver : (polynomialPrime A P).LiesOver P :=
  (Ideal.liesOver_iff _ _).mpr (polynomialPrime_comap A P).symm

end PolynomialExtension

section LaurentExtension

variable (A : Type*) [CommRing A] (P : Ideal A) [P.IsPrime]

abbrev laurentPrime : Ideal (LaurentPolynomial A) := P.map LaurentPolynomial.C

instance laurent_polynomial_tower : IsScalarTower A (Polynomial A) (LaurentPolynomial A) :=
  IsScalarTower.of_algebraMap_eq (fun a => by
    simp [LaurentPolynomial.algebraMap_eq_toLaurent, Polynomial.algebraMap_eq,
      ← LaurentPolynomial.C_eq_algebraMap])

theorem polynomialPrime_disjoint_powers_X :
    Disjoint (Submonoid.powers (Polynomial.X : Polynomial A) : Set (Polynomial A))
      (polynomialPrime A P : Set (Polynomial A)) := by
  apply Set.disjoint_left.mpr
  rintro f ⟨n, rfl⟩ hf
  have hc := (Ideal.mem_map_C_iff.mp hf) n
  exact P.one_notMem (by simpa using hc)

omit [P.IsPrime] in
theorem laurentPrime_eq_map_polynomialPrime :
    laurentPrime A P = (polynomialPrime A P).map
      (algebraMap (Polynomial A) (LaurentPolynomial A)) := by
  have hc : (algebraMap (Polynomial A) (LaurentPolynomial A)).comp
      (Polynomial.C : A →+* Polynomial A) = LaurentPolynomial.C := by
    apply RingHom.ext
    intro a
    exact Polynomial.toLaurent_C a
  change P.map LaurentPolynomial.C =
    (P.map Polynomial.C).map (algebraMap (Polynomial A) (LaurentPolynomial A))
  rw [Ideal.map_map, hc]

instance laurentPrime_isPrime : (laurentPrime A P).IsPrime := by
  rw [laurentPrime_eq_map_polynomialPrime]
  exact IsLocalization.isPrime_of_isPrime_disjoint
    (Submonoid.powers (Polynomial.X : Polynomial A)) (LaurentPolynomial A)
    (polynomialPrime A P) inferInstance (polynomialPrime_disjoint_powers_X A P)

theorem laurentPrime_comap :
    (laurentPrime A P).comap (algebraMap A (LaurentPolynomial A)) = P := by
  rw [IsScalarTower.algebraMap_eq A (Polynomial A) (LaurentPolynomial A),
    ← Ideal.comap_comap, laurentPrime_eq_map_polynomialPrime,
    show Ideal.comap (algebraMap (Polynomial A) (LaurentPolynomial A))
        ((polynomialPrime A P).map (algebraMap (Polynomial A) (LaurentPolynomial A))) =
        polynomialPrime A P from
      IsLocalization.under_map_of_isPrime_disjoint
        (Submonoid.powers (Polynomial.X : Polynomial A)) (LaurentPolynomial A)
        (show (polynomialPrime A P).IsPrime from inferInstance)
        (polynomialPrime_disjoint_powers_X A P)]
  exact polynomialPrime_comap A P

instance laurentPrime_liesOver : (laurentPrime A P).LiesOver P :=
  (Ideal.liesOver_iff _ _).mpr (laurentPrime_comap A P).symm

instance laurent_flat : Module.Flat A (LaurentPolynomial A) := by
  let : Module.Flat (Polynomial A) (LaurentPolynomial A) :=
    IsLocalization.flat (LaurentPolynomial A) (Submonoid.powers (Polynomial.X : Polynomial A))
  exact Module.Flat.trans A (Polynomial A) (LaurentPolynomial A)

theorem laurentLocal_maximalIdeal_map_eq :
    (IsLocalRing.maximalIdeal (Localization.AtPrime P)).map
      (algebraMap (Localization.AtPrime P)
        (Localization.AtPrime (laurentPrime A P))) =
    IsLocalRing.maximalIdeal (Localization.AtPrime (laurentPrime A P)) :=
  localized_maximalIdeal_map_eq P (laurentPrime A P) rfl

theorem laurentLocal_quotient_length
    (I : Ideal (Localization.AtPrime P))
    (hI : IsFiniteLength (Localization.AtPrime P) (Localization.AtPrime P ⧸ I)) :
    Module.length (Localization.AtPrime (laurentPrime A P))
      (Localization.AtPrime (laurentPrime A P) ⧸ I.map
        (algebraMap (Localization.AtPrime P)
          (Localization.AtPrime (laurentPrime A P)))) =
    Module.length (Localization.AtPrime P) (Localization.AtPrime P ⧸ I) :=
  PiExponentJets.W25.length_quotient_map_of_flat_local
    (laurentLocal_maximalIdeal_map_eq A P) I hI

end LaurentExtension

variable (k σ : Type*) [CommRing k]

abbrev AffineRing := MvPolynomial σ k
abbrev ConeRing := MvPolynomial (Option σ) k
abbrev ConeAway := Localization.Away (MvPolynomial.X none : ConeRing k σ)
abbrev LaurentChart := LaurentPolynomial (AffineRing k σ)

def coneHomogenizingUnit : (ConeAway k σ)ˣ :=
  (IsLocalization.Away.algebraMap_isUnit
    (S := ConeAway k σ) (MvPolynomial.X none : ConeRing k σ)).unit

@[simp] theorem coneHomogenizingUnit_val :
    (coneHomogenizingUnit k σ : ConeAway k σ) =
      algebraMap (ConeRing k σ) (ConeAway k σ) (MvPolynomial.X none) :=
  IsUnit.unit_spec _

@[simp] theorem coneHomogenizingUnit_inv_mul :
    (↑(coneHomogenizingUnit k σ)⁻¹ : ConeAway k σ) *
      algebraMap (ConeRing k σ) (ConeAway k σ) (MvPolynomial.X none) = 1 := by
  rw [← coneHomogenizingUnit_val]
  exact Units.inv_mul (coneHomogenizingUnit k σ)

def affineToConeAway : AffineRing k σ →+* ConeAway k σ :=
  MvPolynomial.eval₂Hom
    ((algebraMap (ConeRing k σ) (ConeAway k σ)).comp MvPolynomial.C)
    (fun i => algebraMap (ConeRing k σ) (ConeAway k σ) (MvPolynomial.X (some i)) *
      ↑(coneHomogenizingUnit k σ)⁻¹)

@[simp] theorem affineToConeAway_C (a : k) :
    affineToConeAway k σ (MvPolynomial.C a) =
      algebraMap (ConeRing k σ) (ConeAway k σ) (MvPolynomial.C a) := by
  simp [affineToConeAway]

@[simp] theorem affineToConeAway_X (i : σ) :
    affineToConeAway k σ (MvPolynomial.X i) =
      algebraMap (ConeRing k σ) (ConeAway k σ) (MvPolynomial.X (some i)) *
        ↑(coneHomogenizingUnit k σ)⁻¹ := by
  simp [affineToConeAway]

def coneToLaurent : ConeRing k σ →+* LaurentChart k σ :=
  MvPolynomial.eval₂Hom (LaurentPolynomial.C.comp MvPolynomial.C)
    (fun i => i.elim (LaurentPolynomial.T 1)
      (fun j => LaurentPolynomial.C (MvPolynomial.X j) * LaurentPolynomial.T 1))

@[simp] theorem coneToLaurent_C (a : k) :
    coneToLaurent k σ (MvPolynomial.C a) =
      LaurentPolynomial.C (MvPolynomial.C a) := by simp [coneToLaurent]

@[simp] theorem coneToLaurent_X_none :
    coneToLaurent k σ (MvPolynomial.X none) = LaurentPolynomial.T 1 := by
  simp [coneToLaurent]

@[simp] theorem coneToLaurent_X_some (i : σ) :
    coneToLaurent k σ (MvPolynomial.X (some i)) =
      LaurentPolynomial.C (MvPolynomial.X i) * LaurentPolynomial.T 1 := by
  simp [coneToLaurent]

def coneAwayToLaurent : ConeAway k σ →+* LaurentChart k σ :=
  IsLocalization.Away.lift (MvPolynomial.X none : ConeRing k σ)
    (g := coneToLaurent k σ) (by simpa using LaurentPolynomial.isUnit_T (R := AffineRing k σ) 1)

@[simp] theorem coneAwayToLaurent_algebraMap (p : ConeRing k σ) :
    coneAwayToLaurent k σ (algebraMap (ConeRing k σ) (ConeAway k σ) p) =
      coneToLaurent k σ p := by simp [coneAwayToLaurent]

def laurentToConeAway : LaurentChart k σ →+* ConeAway k σ :=
  LaurentPolynomial.eval₂ (affineToConeAway k σ) (coneHomogenizingUnit k σ)

@[simp] theorem laurentToConeAway_C (p : AffineRing k σ) :
    laurentToConeAway k σ (LaurentPolynomial.C p) = affineToConeAway k σ p := by
  simp [laurentToConeAway]

@[simp] theorem laurentToConeAway_T :
    laurentToConeAway k σ (LaurentPolynomial.T 1) = coneHomogenizingUnit k σ := by
  simp [laurentToConeAway]

theorem laurentToConeAway_comp_coneToLaurent :
    (laurentToConeAway k σ).comp (coneToLaurent k σ) =
      algebraMap (ConeRing k σ) (ConeAway k σ) := by
  apply MvPolynomial.ringHom_ext
  · intro a
    simp
  · intro i
    cases i with
    | none => simp
    | some i => simp [mul_assoc]

theorem laurentToConeAway_comp_coneAwayToLaurent :
    (laurentToConeAway k σ).comp (coneAwayToLaurent k σ) = RingHom.id _ := by
  apply IsLocalization.ringHom_ext
    (Submonoid.powers (MvPolynomial.X none : ConeRing k σ))
  apply RingHom.ext
  intro p
  change laurentToConeAway k σ
    (coneAwayToLaurent k σ (algebraMap _ _ p)) = algebraMap _ _ p
  rw [coneAwayToLaurent_algebraMap]
  exact RingHom.congr_fun (laurentToConeAway_comp_coneToLaurent k σ) p

theorem coneAwayToLaurent_comp_affineToConeAway :
    (coneAwayToLaurent k σ).comp (affineToConeAway k σ) = LaurentPolynomial.C := by
  apply MvPolynomial.ringHom_ext
  · intro a
    simp
  · intro i
    change coneAwayToLaurent k σ (affineToConeAway k σ (MvPolynomial.X i)) =
      LaurentPolynomial.C (MvPolynomial.X i)
    apply (LaurentPolynomial.isUnit_T (R := AffineRing k σ) 1).mul_left_inj.mp
    have hu : coneAwayToLaurent k σ (coneHomogenizingUnit k σ) =
        LaurentPolynomial.T 1 := by simp
    calc
      coneAwayToLaurent k σ (affineToConeAway k σ (MvPolynomial.X i)) *
          LaurentPolynomial.T 1 =
          coneAwayToLaurent k σ
            (affineToConeAway k σ (MvPolynomial.X i) * coneHomogenizingUnit k σ) := by
        rw [map_mul, hu]
      _ = LaurentPolynomial.C (MvPolynomial.X i) * LaurentPolynomial.T 1 := by
        simp [mul_assoc]

theorem coneAwayToLaurent_comp_laurentToConeAway :
    (coneAwayToLaurent k σ).comp (laurentToConeAway k σ) = RingHom.id _ := by
  apply IsLocalization.ringHom_ext
    (Submonoid.powers (Polynomial.X : Polynomial (AffineRing k σ)))
  apply Polynomial.ringHom_ext
  · intro a
    change coneAwayToLaurent k σ
      (laurentToConeAway k σ (algebraMap _ _ (Polynomial.C a))) =
        algebraMap _ _ (Polynomial.C a)
    simp only [LaurentPolynomial.algebraMap_eq_toLaurent, Polynomial.toLaurent_C,
      laurentToConeAway_C]
    exact RingHom.congr_fun (coneAwayToLaurent_comp_affineToConeAway k σ) a
  · change coneAwayToLaurent k σ
      (laurentToConeAway k σ (algebraMap _ _ Polynomial.X)) =
        algebraMap _ _ Polynomial.X
    simp [LaurentPolynomial.algebraMap_eq_toLaurent]

def coneLaurentEquiv : ConeAway k σ ≃+* LaurentChart k σ :=
  RingEquiv.ofRingHom (coneAwayToLaurent k σ) (laurentToConeAway k σ)
    (coneAwayToLaurent_comp_laurentToConeAway k σ)
    (laurentToConeAway_comp_coneAwayToLaurent k σ)

end PiExponentSiegel.W17.ConeLocalLength

end

end OAI
end Source0140

-- Source: OAI/NumberTheory/PiExponent/LocalAlgebra/ConePrimeLocalization.lean
section Source0141
-- Modified in this edition: unused plain lemmas removed; see reduction.json.
/-
Modification notice for the LogTwo project.
Derived from openai/math (Apache-2.0), revision adc7f1241b42e322a6451854ab7e4b4c146bf78a.
Original source: lean/OAI/NumberTheory/PiExponent/LocalAlgebra/ConePrimeLocalization.lean
Changes: Convert module/import declarations to the Lean 4.34 public module format.
See ../THIRD_PARTY_NOTICES.txt for provenance and the recorded changes.
-/

namespace OAI

noncomputable section

namespace PiExponentSiegel.W17.ConeLocalLength

attribute [local instance] Localization.AtPrime.algebraOfLiesOver

variable (k σ : Type*) [CommRing k]
variable (P : Ideal (AffineRing k σ)) [P.IsPrime]

def awayChartPrime : Ideal (ConeAway k σ) :=
  (laurentPrime (AffineRing k σ) P).comap (coneLaurentEquiv k σ).toRingHom

instance awayChartPrime_isPrime : (awayChartPrime k σ P).IsPrime := by
  unfold awayChartPrime
  infer_instance

def conePrime : Ideal (ConeRing k σ) :=
  (awayChartPrime k σ P).comap (algebraMap (ConeRing k σ) (ConeAway k σ))

instance conePrime_isPrime : (conePrime k σ P).IsPrime := by
  unfold conePrime
  infer_instance

theorem homogenizing_coordinate_not_mem_conePrime :
    (MvPolynomial.X none : ConeRing k σ) ∉ conePrime k σ P := by
  intro h
  change algebraMap (ConeRing k σ) (ConeAway k σ) (MvPolynomial.X none) ∈
    awayChartPrime k σ P at h
  exact (show (awayChartPrime k σ P).IsPrime from inferInstance).ne_top
    ((awayChartPrime k σ P).eq_top_of_isUnit_mem h
      (IsLocalization.Away.algebraMap_isUnit (S := ConeAway k σ)
        (MvPolynomial.X none : ConeRing k σ)))

def conePrimeLocalizationEquiv :
    Localization.AtPrime (conePrime k σ P) ≃+*
      Localization.AtPrime (laurentPrime (AffineRing k σ) P) :=
  (IsLocalization.localizationLocalizationAtPrimeIsoLocalization
    (Submonoid.powers (MvPolynomial.X none : ConeRing k σ))
    (awayChartPrime k σ P)).toRingEquiv.trans
      (PiExponentJets.W22.primeLocalizationEquiv (coneLaurentEquiv k σ)
        (awayChartPrime k σ P) (laurentPrime (AffineRing k σ) P) rfl)

def affineLocalToConeLocal : Localization.AtPrime P →+*
    Localization.AtPrime (conePrime k σ P) :=
  (conePrimeLocalizationEquiv k σ P).symm.toRingHom.comp
    (algebraMap (Localization.AtPrime P)
      (Localization.AtPrime (laurentPrime (AffineRing k σ) P)))

@[instance_reducible] def affineLocalConeAlgebra :
    Algebra (Localization.AtPrime P) (Localization.AtPrime (conePrime k σ P)) :=
  (affineLocalToConeLocal k σ P).toAlgebra

theorem affineLocalToConeLocal_map_maximalIdeal :
    (IsLocalRing.maximalIdeal (Localization.AtPrime P)).map
      (affineLocalToConeLocal k σ P) =
    IsLocalRing.maximalIdeal (Localization.AtPrime (conePrime k σ P)) := by
  rw [affineLocalToConeLocal, ← Ideal.map_map,
    laurentLocal_maximalIdeal_map_eq (AffineRing k σ) P]
  exact IsLocalRing.map_maximalIdeal_of_surjective
    (conePrimeLocalizationEquiv k σ P).symm.toRingHom
    (conePrimeLocalizationEquiv k σ P).symm.surjective

theorem affineLocalToConeLocal_flat :
    letI := affineLocalConeAlgebra k σ P
    Module.Flat (Localization.AtPrime P) (Localization.AtPrime (conePrime k σ P)) := by
  let := affineLocalConeAlgebra k σ P
  let e : Localization.AtPrime (conePrime k σ P) ≃ₐ[Localization.AtPrime P]
      Localization.AtPrime (laurentPrime (AffineRing k σ) P) :=
    { conePrimeLocalizationEquiv k σ P with
      commutes' := by
        intro a
        change conePrimeLocalizationEquiv k σ P
          ((conePrimeLocalizationEquiv k σ P).symm (algebraMap _ _ a)) = _
        exact (conePrimeLocalizationEquiv k σ P).apply_symm_apply _ }
  exact Module.Flat.of_linearEquiv e.toLinearEquiv

end PiExponentSiegel.W17.ConeLocalLength

end

end OAI
end Source0141

-- Source: OAI/NumberTheory/PiExponent/Polynomials/Homogenization.lean
section Source0142
-- Modified in this edition: unused plain lemmas removed; see reduction.json.
/-
Modification notice for the LogTwo project.
Derived from openai/math (Apache-2.0), revision adc7f1241b42e322a6451854ab7e4b4c146bf78a.
Original source: lean/OAI/NumberTheory/PiExponent/Polynomials/Homogenization.lean
Changes: Convert module/import declarations to the Lean 4.34 public module format.
See ../THIRD_PARTY_NOTICES.txt for provenance and the recorded changes.
-/

namespace OAI

namespace PiExponentJets.W22

open scoped BigOperators
open MvPolynomial

variable {k σ : Type*} [CommRing k]

noncomputable def dehomogenize : MvPolynomial (Option σ) k →+* MvPolynomial σ k :=
  MvPolynomial.eval₂Hom MvPolynomial.C (fun o : Option σ => o.elim 1 MvPolynomial.X)

@[simp] theorem dehomogenize_X_none :
    dehomogenize (MvPolynomial.X none : MvPolynomial (Option σ) k) = 1 := by
  simp [dehomogenize]

@[simp] theorem dehomogenize_rename (p : MvPolynomial σ k) :
    dehomogenize (MvPolynomial.rename some p) = p := by
  change MvPolynomial.eval₂Hom MvPolynomial.C
    (fun o : Option σ => o.elim 1 MvPolynomial.X) (MvPolynomial.rename some p) = p
  rw [MvPolynomial.eval₂Hom_rename]
  change MvPolynomial.eval₂ MvPolynomial.C MvPolynomial.X p = p
  exact MvPolynomial.eval₂_eta p

noncomputable def homogenize (p : MvPolynomial σ k) : MvPolynomial (Option σ) k :=
  ∑ i ∈ Finset.range (p.totalDegree + 1),
    MvPolynomial.rename some (MvPolynomial.homogeneousComponent i p) *
      MvPolynomial.X none ^ (p.totalDegree - i)

@[simp] theorem dehomogenize_homogenize (p : MvPolynomial σ k) :
    dehomogenize (homogenize p) = p := by
  simp only [homogenize, map_sum, map_mul, map_pow, dehomogenize_rename,
    dehomogenize_X_none, one_pow, mul_one]
  exact MvPolynomial.sum_homogeneousComponent p

theorem homogenize_isHomogeneous (p : MvPolynomial σ k) :
    (homogenize p).IsHomogeneous p.totalDegree := by
  apply MvPolynomial.IsHomogeneous.sum
  intro i hi
  have hi' : i ≤ p.totalDegree := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
  have hcomponent :=
    (MvPolynomial.homogeneousComponent_isHomogeneous i p).rename_isHomogeneous
      (f := (some : σ → Option σ))
  simpa only [Nat.add_sub_of_le hi'] using
    hcomponent.mul (MvPolynomial.isHomogeneous_X_pow (none : Option σ) (p.totalDegree - i))

end PiExponentJets.W22

end OAI
end Source0142

-- Source: OAI/NumberTheory/PiExponent/Polynomials/ConeHomogeneousEquations.lean
section Source0143
-- Modified in this edition: unused plain lemmas removed; see reduction.json.
/-
Modification notice for the LogTwo project.
Derived from openai/math (Apache-2.0), revision adc7f1241b42e322a6451854ab7e4b4c146bf78a.
Original source: lean/OAI/NumberTheory/PiExponent/Polynomials/ConeHomogeneousEquations.lean
Changes: Convert module/import declarations to the Lean 4.34 public module format.
See ../THIRD_PARTY_NOTICES.txt for provenance and the recorded changes.
-/

namespace OAI

noncomputable section
open scoped BigOperators

namespace PiExponentSiegel.W17.ConeLocalLength

section Scaling

variable {k B σ : Type*} [CommRing k] [CommRing B]

theorem eval₂_scale_of_isHomogeneous (F : MvPolynomial σ k) (d : ℕ)
    (hF : F.IsHomogeneous d) (c : k →+* B) (x : σ → B) (t : B) :
    MvPolynomial.eval₂ c (fun i => x i * t) F =
      MvPolynomial.eval₂ c x F * t ^ d := by
  classical
  simp only [MvPolynomial.eval₂_eq, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro m hm
  simp only [mul_pow, Finset.prod_mul_distrib]
  rw [Finset.prod_pow_eq_pow_sum, ← hF.degree_eq_sum_deg_support hm, mul_assoc]

end Scaling

variable (k σ : Type*) [CommRing k]

private theorem coneToLaurent_scaled_eval (F : ConeRing k σ) :
    coneToLaurent k σ F =
      MvPolynomial.eval₂ (LaurentPolynomial.C.comp MvPolynomial.C)
        (fun i : Option σ =>
          LaurentPolynomial.C (i.elim 1 MvPolynomial.X) *
            (LaurentPolynomial.T 1 : LaurentChart k σ)) F := by
  have hv : (fun i : Option σ => i.elim (LaurentPolynomial.T 1 : LaurentChart k σ)
      (fun j => LaurentPolynomial.C (MvPolynomial.X j) * LaurentPolynomial.T 1)) =
      (fun i : Option σ => LaurentPolynomial.C (i.elim 1 MvPolynomial.X) *
        (LaurentPolynomial.T 1 : LaurentChart k σ)) := by
    funext i
    cases i <;> simp only [Option.elim_none, Option.elim_some, map_one, one_mul]
  change MvPolynomial.eval₂ (LaurentPolynomial.C.comp MvPolynomial.C)
    (fun i : Option σ => i.elim (LaurentPolynomial.T 1)
      (fun j => LaurentPolynomial.C (MvPolynomial.X j) * LaurentPolynomial.T 1)) F = _
  rw [hv]

private theorem laurent_eval_dehomogenize (F : ConeRing k σ) :
    MvPolynomial.eval₂ (LaurentPolynomial.C.comp MvPolynomial.C)
      (fun i : Option σ => LaurentPolynomial.C (i.elim 1 MvPolynomial.X)) F =
      (LaurentPolynomial.C (PiExponentJets.W22.dehomogenize F) : LaurentChart k σ) :=
  (MvPolynomial.map_eval₂Hom MvPolynomial.C
    (fun i : Option σ => i.elim 1 MvPolynomial.X) LaurentPolynomial.C F).symm

theorem coneToLaurent_homogeneous (F : ConeRing k σ) (d : ℕ)
    (hF : F.IsHomogeneous d) :
    coneToLaurent k σ F =
      LaurentPolynomial.C (PiExponentJets.W22.dehomogenize F) *
        (LaurentPolynomial.T 1 : LaurentChart k σ) ^ d := by
  rw [coneToLaurent_scaled_eval]
  rw [eval₂_scale_of_isHomogeneous F d hF, laurent_eval_dehomogenize]

theorem coneToLaurent_homogenize (f : AffineRing k σ) :
    coneToLaurent k σ (PiExponentJets.W22.homogenize f) =
      LaurentPolynomial.C f * (LaurentPolynomial.T 1 : LaurentChart k σ) ^ f.totalDegree := by
  simpa using coneToLaurent_homogeneous k σ (PiExponentJets.W22.homogenize f)
    f.totalDegree (PiExponentJets.W22.homogenize_isHomogeneous f)

theorem map_homogenized_span_eq_laurent_span {ι : Type*} (f : ι → AffineRing k σ) :
    (Ideal.span (Set.range (fun i => PiExponentJets.W22.homogenize (f i)))).map
      (coneToLaurent k σ) =
    (Ideal.span (Set.range f)).map (LaurentPolynomial.C : AffineRing k σ →+* LaurentChart k σ) := by
  apply le_antisymm
  · apply Ideal.map_le_iff_le_comap.mpr
    apply Ideal.span_le.mpr
    rintro _ ⟨i, rfl⟩
    change coneToLaurent k σ (PiExponentJets.W22.homogenize (f i)) ∈
      (Ideal.span (Set.range f)).map
        (LaurentPolynomial.C : AffineRing k σ →+* LaurentChart k σ)
    rw [coneToLaurent_homogenize]
    exact Ideal.mul_mem_right _ _ (Ideal.mem_map_of_mem _
      (Ideal.subset_span (Set.mem_range_self i)))
  · apply Ideal.map_le_iff_le_comap.mpr
    apply Ideal.span_le.mpr
    rintro _ ⟨i, rfl⟩
    change (LaurentPolynomial.C (f i) : LaurentChart k σ) ∈
      (Ideal.span (Set.range (fun j => PiExponentJets.W22.homogenize (f j)))).map
        (coneToLaurent k σ)
    apply (Ideal.mul_unit_mem_iff_mem _
      ((LaurentPolynomial.isUnit_T (R := AffineRing k σ) 1).pow (f i).totalDegree)).mp
    rw [← coneToLaurent_homogenize]
    exact Ideal.mem_map_of_mem _ (Ideal.subset_span (Set.mem_range_self i))

variable (P : Ideal (AffineRing k σ)) [P.IsPrime]

end PiExponentSiegel.W17.ConeLocalLength

end

end OAI
end Source0143

-- Source: OAI/NumberTheory/PiExponent/Geometry/ConePrimeProperties.lean
section Source0144
-- Modified in this edition: unused plain lemmas removed; see reduction.json.
/-
Modification notice for the LogTwo project.
Derived from openai/math (Apache-2.0), revision adc7f1241b42e322a6451854ab7e4b4c146bf78a.
Original source: lean/OAI/NumberTheory/PiExponent/Geometry/ConePrimeProperties.lean
Changes: Convert module/import declarations to the Lean 4.34 public module format.
See ../THIRD_PARTY_NOTICES.txt for provenance and the recorded changes.
-/

namespace OAI

noncomputable section

namespace PiExponentSiegel.W17.ConeLocalLength

attribute [local instance] MvPolynomial.gradedAlgebra

section General

variable {A B : Type*} [CommRing A] [CommRing B]

theorem mapped_minimalPrime_of_prime_extension
    (f : A →+* B) {I P : Ideal A} (hP : P ∈ I.minimalPrimes)
    (hprime : (P.map f).IsPrime) (hcontract : (P.map f).comap f = P) :
    P.map f ∈ (I.map f).minimalPrimes := by
  refine ⟨⟨hprime, Ideal.map_mono hP.1.2⟩, ?_⟩
  intro Q hQ hQP
  apply Ideal.map_le_iff_le_comap.mpr
  apply hP.2 ⟨hQ.1.comap f, Ideal.map_le_iff_le_comap.mp hQ.2⟩
  exact (Ideal.comap_mono hQP).trans hcontract.le

theorem minimalPrime_isHomogeneous {k σ : Type*} [CommRing k]
    (I Q : Ideal (MvPolynomial σ k))
    (hI : I.IsHomogeneous (MvPolynomial.homogeneousSubmodule σ k))
    (hQ : Q ∈ I.minimalPrimes) :
    Q.IsHomogeneous (MvPolynomial.homogeneousSubmodule σ k) := by
  let := MvPolynomial.gradedAlgebra (σ := σ) (R := k)
  let C := Q.homogeneousCore (MvPolynomial.homogeneousSubmodule σ k)
  have hIC : I ≤ C.toIdeal := by
    rw [← hI.toIdeal_homogeneousCore_eq_self]
    exact Ideal.homogeneousCore_mono _ hQ.1.2
  have hCQ : C.toIdeal ≤ Q := Ideal.toIdeal_homogeneousCore_le _ _
  have hQC : Q ≤ C.toIdeal := hQ.2 ⟨hQ.1.1.homogeneousCore, hIC⟩ hCQ
  have heq : C.toIdeal = Q := le_antisymm hCQ hQC
  exact heq ▸ C.isHomogeneous

end General

variable (k σ : Type*) [CommRing k]
variable (P : Ideal (AffineRing k σ)) [P.IsPrime]

theorem conePrime_minimal_over_homogenized {ι : Type*} (f : ι → AffineRing k σ)
    (hP : P ∈ (Ideal.span (Set.range f)).minimalPrimes) :
    conePrime k σ P ∈
      (Ideal.span (Set.range (fun i => PiExponentJets.W22.homogenize (f i)))).minimalPrimes := by
  let H := Ideal.span (Set.range (fun i => PiExponentJets.W22.homogenize (f i)))
  have hLP : laurentPrime (AffineRing k σ) P ∈ (H.map (coneToLaurent k σ)).minimalPrimes := by
    rw [map_homogenized_span_eq_laurent_span k σ f]
    exact mapped_minimalPrime_of_prime_extension LaurentPolynomial.C hP inferInstance
      (laurentPrime_comap (AffineRing k σ) P)
  have hcomp : coneToLaurent k σ = (coneLaurentEquiv k σ).toRingHom.comp
      (algebraMap (ConeRing k σ) (ConeAway k σ)) := by
    apply RingHom.ext
    intro F
    exact (coneAwayToLaurent_algebraMap k σ F).symm
  have hI : (H.map (coneToLaurent k σ)).comap (coneLaurentEquiv k σ).toRingHom =
      H.map (algebraMap (ConeRing k σ) (ConeAway k σ)) := by
    rw [hcomp, ← Ideal.map_map]
    simp only [RingEquiv.toRingHom_eq_coe]
    rw [Ideal.map_comap_of_equiv]
    apply Ideal.ext
    intro z
    change (coneLaurentEquiv k σ).symm ((coneLaurentEquiv k σ) z) ∈
      H.map (algebraMap (ConeRing k σ) (ConeAway k σ)) ↔ z ∈
      H.map (algebraMap (ConeRing k σ) (ConeAway k σ))
    rw [RingEquiv.symm_apply_apply]
  have hchart := Ideal.minimalPrimes_comap_of_surjective
    (coneLaurentEquiv k σ).surjective hLP
  change awayChartPrime k σ P ∈
    ((H.map (coneToLaurent k σ)).comap (coneLaurentEquiv k σ).toRingHom).minimalPrimes at hchart
  rw [hI, IsLocalization.minimalPrimes_map
    (Submonoid.powers (MvPolynomial.X none : ConeRing k σ)) (ConeAway k σ)] at hchart
  exact hchart

variable [IsNoetherianRing (AffineRing k σ)]

end PiExponentSiegel.W17.ConeLocalLength

end

end OAI
end Source0144

-- Source: OAI/NumberTheory/PiExponent/LocalAlgebra/ConeEquationLength.lean
section Source0145
/-
Modification notice for the LogTwo project.
Derived from openai/math (Apache-2.0), revision adc7f1241b42e322a6451854ab7e4b4c146bf78a.
Original source: lean/OAI/NumberTheory/PiExponent/LocalAlgebra/ConeEquationLength.lean
Changes: Convert module/import declarations to the Lean 4.34 public module format.
See ../THIRD_PARTY_NOTICES.txt for provenance and the recorded changes.
-/

namespace OAI

noncomputable section

attribute [local instance] Localization.AtPrime.algebraOfLiesOver

namespace PiExponentSiegel.W17.ConeLocalLength

variable (k σ : Type*) [CommRing k]
variable (P : Ideal (AffineRing k σ)) [P.IsPrime]

theorem conePrimeLocalizationEquiv_algebraMap (F : ConeRing k σ) :
    conePrimeLocalizationEquiv k σ P
      (algebraMap (ConeRing k σ) (Localization.AtPrime (conePrime k σ P)) F) =
    algebraMap (LaurentChart k σ)
      (Localization.AtPrime (laurentPrime (AffineRing k σ) P)) (coneToLaurent k σ F) := by
  let a := IsLocalization.localizationLocalizationAtPrimeIsoLocalization
    (Submonoid.powers (MvPolynomial.X none : ConeRing k σ)) (awayChartPrime k σ P)
  let b := PiExponentJets.W22.primeLocalizationEquiv (coneLaurentEquiv k σ)
    (awayChartPrime k σ P) (laurentPrime (AffineRing k σ) P) rfl
  change b (a (algebraMap (ConeRing k σ) _ F)) = _
  rw [a.commutes F]
  change b (algebraMap (ConeAway k σ) _ (algebraMap (ConeRing k σ) (ConeAway k σ) F)) = _
  rw [show b (algebraMap (ConeAway k σ) _
      (algebraMap (ConeRing k σ) (ConeAway k σ) F)) =
      algebraMap (LaurentChart k σ) _ ((coneLaurentEquiv k σ)
        (algebraMap (ConeRing k σ) (ConeAway k σ) F)) from
    IsLocalization.ringEquivOfRingEquiv_eq
      (PiExponentJets.W22.primeCompl_map_eq_of_comap (coneLaurentEquiv k σ)
        (awayChartPrime k σ P) (laurentPrime (AffineRing k σ) P) rfl) _]
  exact congrArg (algebraMap (LaurentChart k σ)
    (Localization.AtPrime (laurentPrime (AffineRing k σ) P)))
    (coneAwayToLaurent_algebraMap k σ F)

theorem conePrimeLocalizationEquiv_map_ideal (J : Ideal (ConeRing k σ)) :
    (J.map (algebraMap (ConeRing k σ)
      (Localization.AtPrime (conePrime k σ P)))).map
        (conePrimeLocalizationEquiv k σ P).toRingHom =
    (J.map (coneToLaurent k σ)).map (algebraMap (LaurentChart k σ)
      (Localization.AtPrime (laurentPrime (AffineRing k σ) P))) := by
  rw [Ideal.map_map, Ideal.map_map]
  congr 1
  apply RingHom.ext
  intro F
  exact conePrimeLocalizationEquiv_algebraMap k σ P F

theorem affine_ideal_map_to_laurent_local (J : Ideal (AffineRing k σ)) :
    (J.map (algebraMap (AffineRing k σ) (Localization.AtPrime P))).map
      (algebraMap (Localization.AtPrime P)
        (Localization.AtPrime (laurentPrime (AffineRing k σ) P))) =
    (J.map (LaurentPolynomial.C : AffineRing k σ →+* LaurentChart k σ)).map
      (algebraMap (LaurentChart k σ)
        (Localization.AtPrime (laurentPrime (AffineRing k σ) P))) := by
  rw [Ideal.map_map, Ideal.map_map]
  congr 1
  apply RingHom.ext
  intro x
  rw [RingHom.comp_apply, RingHom.comp_apply, ← IsScalarTower.algebraMap_apply]
  rw [LaurentPolynomial.C_eq_algebraMap, ← IsScalarTower.algebraMap_apply]

theorem homogenized_cone_local_length_eq {ι : Type*} (f : ι → AffineRing k σ)
    (hfinite : IsFiniteLength (Localization.AtPrime P)
      (Localization.AtPrime P ⧸ (Ideal.span (Set.range f)).map
        (algebraMap (AffineRing k σ) (Localization.AtPrime P)))) :
    Module.length (Localization.AtPrime (conePrime k σ P))
      (Localization.AtPrime (conePrime k σ P) ⧸
        (Ideal.span (Set.range (fun i => PiExponentJets.W22.homogenize (f i)))).map
          (algebraMap (ConeRing k σ) (Localization.AtPrime (conePrime k σ P)))) =
    Module.length (Localization.AtPrime P)
      (Localization.AtPrime P ⧸ (Ideal.span (Set.range f)).map
        (algebraMap (AffineRing k σ) (Localization.AtPrime P))) := by
  let J := Ideal.span (Set.range f)
  let H := Ideal.span (Set.range (fun i => PiExponentJets.W22.homogenize (f i)))
  have hid := conePrimeLocalizationEquiv_map_ideal k σ P H
  rw [map_homogenized_span_eq_laurent_span k σ f] at hid
  have hlength := PiExponentJets.W22.quotient_length_eq_of_ringEquiv
    (conePrimeLocalizationEquiv k σ P)
    (H.map (algebraMap (ConeRing k σ) (Localization.AtPrime (conePrime k σ P))))
    ((J.map (LaurentPolynomial.C : AffineRing k σ →+* LaurentChart k σ)).map
      (algebraMap (LaurentChart k σ)
        (Localization.AtPrime (laurentPrime (AffineRing k σ) P)))) hid.symm
  apply hlength.trans
  have h := laurentLocal_quotient_length (AffineRing k σ) P
    (J.map (algebraMap (AffineRing k σ) (Localization.AtPrime P))) hfinite
  rw [affine_ideal_map_to_laurent_local k σ P J] at h
  exact h

end PiExponentSiegel.W17.ConeLocalLength

end

end OAI
end Source0145

-- Source: OAI/NumberTheory/PiExponent/LocalAlgebra/ConeRegularSequence.lean
section Source0146
/-
Modification notice for the LogTwo project.
Derived from openai/math (Apache-2.0), revision adc7f1241b42e322a6451854ab7e4b4c146bf78a.
Original source: lean/OAI/NumberTheory/PiExponent/LocalAlgebra/ConeRegularSequence.lean
Changes: Convert module/import declarations to the Lean 4.34 public module format.
See ../THIRD_PARTY_NOTICES.txt for provenance and the recorded changes.
-/

namespace OAI

noncomputable section

attribute [local instance] Localization.AtPrime.algebraOfLiesOver

namespace PiExponentSiegel.W17.ConeLocalLength

open RingTheory.Sequence

section Units

variable {R τ M : Type*} [CommRing R] [AddCommGroup M] [Module R M]

theorem ofList_map_mul_units (xs : List τ) (a u : τ → R) (hu : ∀ x, IsUnit (u x)) :
    Ideal.ofList (xs.map (fun x => a x * u x)) = Ideal.ofList (xs.map a) := by
  apply le_antisymm
  · apply Ideal.span_le.mpr
    intro r hr
    obtain ⟨x, hx, rfl⟩ := List.mem_map.mp hr
    exact Ideal.mul_mem_right _ _ (Ideal.subset_span (List.mem_map.mpr ⟨x, hx, rfl⟩))
  · apply Ideal.span_le.mpr
    intro r hr
    obtain ⟨x, hx, rfl⟩ := List.mem_map.mp hr
    apply (Ideal.mul_unit_mem_iff_mem _ (hu x)).mp
    exact Ideal.subset_span (List.mem_map.mpr ⟨x, hx, rfl⟩)

theorem isRegular_map_mul_units (xs : List τ) (a u : τ → R) (hu : ∀ x, IsUnit (u x))
    (hreg : IsRegular M (xs.map a)) :
    IsRegular M (xs.map (fun x => a x * u x)) := by
  refine ⟨⟨?_⟩, ?_⟩
  · intro i hi
    have hi' : i < xs.length := by simpa only [List.length_map] using hi
    have ha := hreg.regular_mod_prev i (by simpa only [List.length_map] using hi')
    simp only [List.getElem_map] at ha ⊢
    have hI : Ideal.ofList ((xs.map (fun x => a x * u x)).take i) =
        Ideal.ofList ((xs.map a).take i) := by
      simp only [← List.map_take]
      exact ofList_map_mul_units (xs.take i) a u hu
    have hN : (Ideal.ofList ((xs.map (fun x => a x * u x)).take i) •
        (⊤ : Submodule R M)) = Ideal.ofList ((xs.map a).take i) • ⊤ :=
      congrArg (fun J : Ideal R => J • (⊤ : Submodule R M)) hI
    exact Eq.mp (congrArg (fun N : Submodule R M =>
      IsSMulRegular (M ⧸ N) (a xs[i] * u xs[i])) hN.symm)
      (ha.mul ((hu xs[i]).isSMulRegular _))
  · rw [ofList_map_mul_units xs a u hu]
    exact hreg.top_ne_smul

end Units

variable (k σ : Type*) [CommRing k]
variable (P : Ideal (AffineRing k σ)) [P.IsPrime]

def coneLocalCoordinate : Localization.AtPrime (conePrime k σ P) :=
  algebraMap (ConeRing k σ) (Localization.AtPrime (conePrime k σ P)) (MvPolynomial.X none)

theorem coneLocalCoordinate_isUnit : IsUnit (coneLocalCoordinate k σ P) :=
  IsLocalization.map_units (Localization.AtPrime (conePrime k σ P))
    (⟨MvPolynomial.X none, homogenizing_coordinate_not_mem_conePrime k σ P⟩ :
      (conePrime k σ P).primeCompl)

theorem homogenized_local_eq_affine_mul_coordinate (f : AffineRing k σ) :
    algebraMap (ConeRing k σ) (Localization.AtPrime (conePrime k σ P))
      (PiExponentJets.W22.homogenize f) =
    affineLocalToConeLocal k σ P (algebraMap (AffineRing k σ) (Localization.AtPrime P) f) *
      coneLocalCoordinate k σ P ^ f.totalDegree := by
  let e := conePrimeLocalizationEquiv k σ P
  have ha : e (affineLocalToConeLocal k σ P
      (algebraMap (AffineRing k σ) (Localization.AtPrime P) f)) =
      algebraMap (LaurentChart k σ)
        (Localization.AtPrime (laurentPrime (AffineRing k σ) P)) (LaurentPolynomial.C f) := by
    change e (e.symm (algebraMap (Localization.AtPrime P)
      (Localization.AtPrime (laurentPrime (AffineRing k σ) P))
        (algebraMap (AffineRing k σ) (Localization.AtPrime P) f))) = _
    rw [e.apply_symm_apply]
    exact (IsScalarTower.algebraMap_apply (AffineRing k σ) (Localization.AtPrime P)
      (Localization.AtPrime (laurentPrime (AffineRing k σ) P)) f).symm.trans
        (IsScalarTower.algebraMap_apply (AffineRing k σ) (LaurentChart k σ)
          (Localization.AtPrime (laurentPrime (AffineRing k σ) P)) f)
  apply e.injective
  rw [e.map_mul, e.map_pow, ha]
  change conePrimeLocalizationEquiv k σ P
    (algebraMap (ConeRing k σ) (Localization.AtPrime (conePrime k σ P))
      (PiExponentJets.W22.homogenize f)) =
    algebraMap (LaurentChart k σ)
      (Localization.AtPrime (laurentPrime (AffineRing k σ) P)) (LaurentPolynomial.C f) *
    conePrimeLocalizationEquiv k σ P
      (algebraMap (ConeRing k σ) (Localization.AtPrime (conePrime k σ P))
        (MvPolynomial.X none)) ^ f.totalDegree
  rw [conePrimeLocalizationEquiv_algebraMap, conePrimeLocalizationEquiv_algebraMap,
    coneToLaurent_homogenize, coneToLaurent_X_none, map_mul, map_pow]

theorem affineLocalToConeLocal_faithfullyFlat :
    letI := affineLocalConeAlgebra k σ P
    Module.FaithfullyFlat (Localization.AtPrime P)
      (Localization.AtPrime (conePrime k σ P)) := by
  let := affineLocalConeAlgebra k σ P
  let := affineLocalToConeLocal_flat k σ P
  let : IsLocalHom (algebraMap (Localization.AtPrime P)
      (Localization.AtPrime (conePrime k σ P))) :=
    ((IsLocalRing.local_hom_TFAE _).out 1 3).mpr
      (affineLocalToConeLocal_map_maximalIdeal k σ P).le
  exact Module.FaithfullyFlat.of_flat_of_isLocalHom

theorem homogenized_list_regular_at_cone (fs : List (AffineRing k σ))
    (hreg : IsRegular (Localization.AtPrime P)
      (fs.map (algebraMap (AffineRing k σ) (Localization.AtPrime P)))) :
    IsRegular (Localization.AtPrime (conePrime k σ P))
      ((fs.map PiExponentJets.W22.homogenize).map
        (algebraMap (ConeRing k σ) (Localization.AtPrime (conePrime k σ P)))) := by
  let := affineLocalConeAlgebra k σ P
  let := affineLocalToConeLocal_faithfullyFlat k σ P
  have hbase : IsRegular (Localization.AtPrime (conePrime k σ P))
      (fs.map (fun f => affineLocalToConeLocal k σ P
        (algebraMap (AffineRing k σ) (Localization.AtPrime P) f))) := by
    have hb := hreg.of_faithfullyFlat (S := Localization.AtPrime (conePrime k σ P))
    change IsRegular (Localization.AtPrime (conePrime k σ P))
      ((fs.map (algebraMap (AffineRing k σ) (Localization.AtPrime P))).map
        (affineLocalToConeLocal k σ P)) at hb
    simpa only [List.map_map, Function.comp_def] using hb
  have hscaled := isRegular_map_mul_units fs
    (fun f => affineLocalToConeLocal k σ P
      (algebraMap (AffineRing k σ) (Localization.AtPrime P) f))
    (fun f => coneLocalCoordinate k σ P ^ f.totalDegree)
    (fun f => (coneLocalCoordinate_isUnit k σ P).pow f.totalDegree) hbase
  simpa only [List.map_map, Function.comp_def,
    homogenized_local_eq_affine_mul_coordinate] using hscaled

end PiExponentSiegel.W17.ConeLocalLength

end

end OAI
end Source0146

-- Source: OAI/NumberTheory/PiExponent/LocalAlgebra/LocalLength.lean
section Source0147
-- Modified in this edition: unused plain lemmas removed; see reduction.json.
/-
Modification notice for the LogTwo project.
Derived from openai/math (Apache-2.0), revision adc7f1241b42e322a6451854ab7e4b4c146bf78a.
Original source: lean/OAI/NumberTheory/PiExponent/LocalAlgebra/LocalLength.lean
Changes: Convert module/import declarations to the Lean 4.34 public module format.
See ../THIRD_PARTY_NOTICES.txt for provenance and the recorded changes.
-/

namespace OAI

namespace PiExponentJets.W22

variable {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]

theorem quotient_length_antitone {P Q : Submodule R M} (hPQ : P ≤ Q) :
    Module.length R (M ⧸ Q) ≤ Module.length R (M ⧸ P) :=
  Module.length_le_of_surjective (Submodule.factor hPQ)
    (Submodule.factor_surjective hPQ)

theorem ideal_quotient_length_le {a J : Ideal R} (haJ : a ≤ J) :
    Module.length R (R ⧸ J) ≤ Module.length R (R ⧸ a) :=
  quotient_length_antitone haJ

theorem ideal_quotient_length_le_of_bound {a J : Ideal R} (haJ : a ≤ J)
    {B : ℕ∞} (hbound : Module.length R (R ⧸ a) ≤ B) :
    Module.length R (R ⧸ J) ≤ B :=
  (ideal_quotient_length_le haJ).trans hbound

end PiExponentJets.W22

end OAI
end Source0147

-- Source: OAI/NumberTheory/PiExponent/LocalAlgebra/LocalizedComponent.lean
section Source0148
/-
Modification notice for the LogTwo project.
Derived from openai/math (Apache-2.0), revision adc7f1241b42e322a6451854ab7e4b4c146bf78a.
Original source: lean/OAI/NumberTheory/PiExponent/LocalAlgebra/LocalizedComponent.lean
Changes: Convert module/import declarations to the Lean 4.34 public module format.
See ../THIRD_PARTY_NOTICES.txt for provenance and the recorded changes.
-/

namespace OAI

namespace PiExponentJets.W22

variable {R : Type*} [CommRing R]

theorem radical_mem_minimalPrimes (I : Ideal R) [I.radical.IsPrime] :
    I.radical ∈ I.minimalPrimes := by
  rw [← Ideal.radical_minimalPrimes, Ideal.minimalPrimes_eq_subsingleton_self]
  exact Set.mem_singleton _

theorem mem_minimalPrimes_of_localized_radical
    (I P : Ideal R) [P.IsPrime]
    (hrad : (I.map (algebraMap R (Localization.AtPrime P))).radical =
      IsLocalRing.maximalIdeal (Localization.AtPrime P)) :
    P ∈ I.minimalPrimes := by
  have hp : (I.map (algebraMap R (Localization.AtPrime P))).radical.IsPrime := by
    rw [hrad]
    infer_instance
  let := hp
  have hm := radical_mem_minimalPrimes (I.map (algebraMap R (Localization.AtPrime P)))
  rw [hrad, IsLocalization.minimalPrimes_map P.primeCompl (Localization.AtPrime P)] at hm
  change (IsLocalRing.maximalIdeal (Localization.AtPrime P)).comap
    (algebraMap R (Localization.AtPrime P)) ∈ I.minimalPrimes at hm
  simpa only [Localization.AtPrime.under_maximalIdeal] using hm

end PiExponentJets.W22

end OAI
end Source0148

-- Source: OAI/NumberTheory/PiExponent/LocalAlgebra/LocalizedRadical.lean
section Source0149
/-
Modification notice for the LogTwo project.
Derived from openai/math (Apache-2.0), revision adc7f1241b42e322a6451854ab7e4b4c146bf78a.
Original source: lean/OAI/NumberTheory/PiExponent/LocalAlgebra/LocalizedRadical.lean
Changes: Convert module/import declarations to the Lean 4.34 public module format.
See ../THIRD_PARTY_NOTICES.txt for provenance and the recorded changes.
-/

namespace OAI

namespace PiExponentJets.W22

variable {R : Type*} [CommRing R]

theorem localized_radical_eq_maximal_of_mem_minimalPrimes
    (I P : Ideal R) [P.IsPrime] (hP : P ∈ I.minimalPrimes) :
    (I.map (algebraMap R (Localization.AtPrime P))).radical =
      IsLocalRing.maximalIdeal (Localization.AtPrime P) := by
  have hreverse : P.map (algebraMap R (Localization.AtPrime P)) ≤
      (I.map (algebraMap R (Localization.AtPrime P))).radical := by
    rw [Ideal.radical_eq_sInf, le_sInf_iff]
    rintro q ⟨hqI, hq⟩
    obtain ⟨hqprime, hqP⟩ :=
      ((IsLocalization.AtPrime.orderIsoOfPrime (Localization.AtPrime P) P) ⟨q, hq⟩).2
    rw [Ideal.map_le_iff_le_comap] at hqI ⊢
    exact hP.2 ⟨hqprime, hqI⟩ hqP
  have hmprime : (IsLocalRing.maximalIdeal (Localization.AtPrime P)).IsPrime := inferInstance
  apply le_antisymm
  · apply hmprime.radical_le_iff.mpr
    rw [← Localization.AtPrime.map_eq_maximalIdeal]
    exact Ideal.map_mono hP.1.2
  · simpa only [Localization.AtPrime.map_eq_maximalIdeal] using hreverse

end PiExponentJets.W22

end OAI
end Source0149

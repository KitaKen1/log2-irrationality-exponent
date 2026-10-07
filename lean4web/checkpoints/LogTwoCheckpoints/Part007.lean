/- Generated rc4 checkpoint for LogTwo.
Modified from the reduced edition: new imports, separate module compilation,
and synchronous elaboration. Original source blocks and notices are retained.
See ../../../THIRD_PARTY_NOTICES.txt and ../../reduction.json.
-/
module
public import LogTwoCheckpoints.Part006
public import Lean.Elab.Tactic.Omega
public import Mathlib.Analysis.Complex.Polynomial.Basic
public import Mathlib.Data.SetLike.Basic
public import Mathlib.RingTheory.GradedAlgebra.Radical
public import Mathlib.RingTheory.Ideal.AssociatedPrime.Finiteness
public import Mathlib.RingTheory.KrullDimension.Field
public import Mathlib.RingTheory.KrullDimension.Polynomial
public import Mathlib.RingTheory.Length
public import Mathlib.RingTheory.MvPolynomial.Homogeneous
public import Mathlib.RingTheory.NoetherNormalization
public import Mathlib.RingTheory.Polynomial.HilbertPoly
public import Mathlib.RingTheory.Regular.RegularSequence
@[expose] public section
set_option Elab.async false

-- Source: OAI/NumberTheory/PiExponent/LocalAlgebra/CompleteIntersectionHilbert.lean
section Source0175
-- Modified in this edition: unused plain lemmas removed; see reduction.json.
/-
Modification notice for the LogTwo project.
Derived from openai/math (Apache-2.0), revision adc7f1241b42e322a6451854ab7e4b4c146bf78a.
Original source: lean/OAI/NumberTheory/PiExponent/LocalAlgebra/CompleteIntersectionHilbert.lean
Changes: Convert module/import declarations to the Lean 4.34 public module format.
See ../THIRD_PARTY_NOTICES.txt for provenance and the recorded changes.
-/

namespace OAI

namespace PiExponentJets.W64

open scoped BigOperators
attribute [local instance] MvPolynomial.gradedAlgebra

noncomputable def degreePolynomial (D : ℕ → ℕ) (m : ℕ) : Polynomial ℤ :=
  ∏ i ∈ Finset.range m, ∑ j ∈ Finset.range (D i), (Polynomial.X : Polynomial ℤ) ^ j

theorem degreePolynomial_eval_one (D : ℕ → ℕ) (m : ℕ) :
    (degreePolynomial D m).eval 1 = ∏ i ∈ Finset.range m, (D i : ℤ) := by
  simp [degreePolynomial, Polynomial.eval_prod, Polynomial.eval_finsetSum]

variable {k σ : Type*} [Field k] [Fintype σ]

end PiExponentJets.W64

end OAI
end Source0175

-- Source: OAI/NumberTheory/PiExponent/LocalAlgebra/PositiveDimensionalHilbert.lean
section Source0176
-- Modified in this edition: unused plain lemmas removed; see reduction.json.
/-
Modification notice for the LogTwo project.
Derived from openai/math (Apache-2.0), revision adc7f1241b42e322a6451854ab7e4b4c146bf78a.
Original source: lean/OAI/NumberTheory/PiExponent/LocalAlgebra/PositiveDimensionalHilbert.lean
Changes: Convert module/import declarations to the Lean 4.34 public module format.
See ../THIRD_PARTY_NOTICES.txt for provenance and the recorded changes.
-/

namespace OAI

namespace PiExponentJets.W64

open scoped BigOperators
attribute [local instance] MvPolynomial.gradedAlgebra

variable {k σ : Type*} [Field k] [Fintype σ]

theorem regular_sequence_series_general
    (hσ : 0 < Fintype.card σ)
    (rs : List (MvPolynomial σ k)) (degrees : Fin rs.length → ℕ)
    (hhom : ∀ i : Fin rs.length, rs[i].IsHomogeneous (degrees i))
    (hreg : RingTheory.Sequence.IsRegular (MvPolynomial σ k) rs) :
    sectionHilbertSeries (Ideal.ofList rs) =
      (∏ i ∈ Finset.range rs.length, (1 - PowerSeries.X ^ degreeAt degrees i)) *
        (PowerSeries.invOneSubPow ℤ (Fintype.card σ)).val := by
  have h := regular_prefix_series rs degrees hhom hreg rs.length le_rfl
  simp only [List.take_length] at h
  rwa [sectionHilbertSeries_bot hσ] at h

theorem degreePolynomial_coe (D : ℕ → ℕ) (m : ℕ) :
    ((degreePolynomial D m) : PowerSeries ℤ) =
      ∏ i ∈ Finset.range m, ∑ j ∈ Finset.range (D i),
        (PowerSeries.X : PowerSeries ℤ) ^ j := by
  change (Polynomial.coeToPowerSeries.ringHom : Polynomial ℤ →+* PowerSeries ℤ)
    (∏ i ∈ Finset.range m, ∑ j ∈ Finset.range (D i),
      (Polynomial.X : Polynomial ℤ) ^ j) = _
  rw [map_prod]
  apply Finset.prod_congr rfl
  intro i hi
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro j hj
  rw [map_pow]
  simp only [Polynomial.coeToPowerSeries.ringHom_apply, Polynomial.coe_X]

theorem regular_sequence_series_residual
    (hσ : 0 < Fintype.card σ)
    (rs : List (MvPolynomial σ k)) (degrees : Fin rs.length → ℕ)
    (hhom : ∀ i : Fin rs.length, rs[i].IsHomogeneous (degrees i))
    (hreg : RingTheory.Sequence.IsRegular (MvPolynomial σ k) rs)
    (hlen : rs.length ≤ Fintype.card σ) :
    sectionHilbertSeries (Ideal.ofList rs) =
      ((degreePolynomial (degreeAt degrees) rs.length) : PowerSeries ℤ) *
        (PowerSeries.invOneSubPow ℤ (Fintype.card σ - rs.length)).val := by
  rw [regular_sequence_series_general hσ rs degrees hhom hreg]
  have hn : Fintype.card σ = rs.length + (Fintype.card σ - rs.length) :=
    (Nat.add_sub_of_le hlen).symm
  have hi := congrArg (PowerSeries.invOneSubPow ℤ) hn
  rw [PowerSeries.invOneSubPow_add] at hi
  rw [hi, Units.val_mul, ← mul_assoc,
    degree_factors_mul_invOneSubPow, ← degreePolynomial_coe]

noncomputable def rationalSectionHilbertSeries (I : Ideal (MvPolynomial σ k)) :
    PowerSeries ℚ := PowerSeries.map (Int.castRingHom ℚ) (sectionHilbertSeries I)

omit [Fintype σ] in
@[simp] theorem coeff_rationalSectionHilbertSeries
    (I : Ideal (MvPolynomial σ k)) (n : ℕ) :
    PowerSeries.coeff n (rationalSectionHilbertSeries I) =
      (Module.finrank k (quotientSection I n) : ℚ) := by
  simp [rationalSectionHilbertSeries, PowerSeries.coeff_map]

noncomputable def rationalDegreePolynomial (D : ℕ → ℕ) (m : ℕ) : Polynomial ℚ :=
  (degreePolynomial D m).map (Int.castRingHom ℚ)

theorem rationalDegreePolynomial_eval_one (D : ℕ → ℕ) (m : ℕ) :
    (rationalDegreePolynomial D m).eval 1 =
      (∏ i ∈ Finset.range m, D i : ℕ) := by
  rw [rationalDegreePolynomial, Polynomial.eval_one_map, degreePolynomial_eval_one]
  simp

theorem map_int_invOneSubPow (r : ℕ) :
    PowerSeries.map (Int.castRingHom ℚ) (PowerSeries.invOneSubPow ℤ r).val =
      (PowerSeries.invOneSubPow ℚ r).val := by
  cases r with
  | zero => simp [PowerSeries.invOneSubPow_zero]
  | succ r =>
    rw [PowerSeries.invOneSubPow_val_succ_eq_mk_add_choose,
      PowerSeries.invOneSubPow_val_succ_eq_mk_add_choose]
    ext n
    simp [PowerSeries.coeff_map]

theorem rational_regular_sequence_series_residual
    (hσ : 0 < Fintype.card σ)
    (rs : List (MvPolynomial σ k)) (degrees : Fin rs.length → ℕ)
    (hhom : ∀ i : Fin rs.length, rs[i].IsHomogeneous (degrees i))
    (hreg : RingTheory.Sequence.IsRegular (MvPolynomial σ k) rs)
    (hlen : rs.length ≤ Fintype.card σ) :
    rationalSectionHilbertSeries (Ideal.ofList rs) =
      ((rationalDegreePolynomial (degreeAt degrees) rs.length) : PowerSeries ℚ) *
        (PowerSeries.invOneSubPow ℚ (Fintype.card σ - rs.length)).val := by
  rw [rationalSectionHilbertSeries,
    regular_sequence_series_residual hσ rs degrees hhom hreg hlen,
    map_mul, map_int_invOneSubPow]
  rw [← Polynomial.polynomial_map_coe]
  rfl

noncomputable def regularSequenceHilbertPolynomial
    (rs : List (MvPolynomial σ k)) (degrees : Fin rs.length → ℕ) : Polynomial ℚ :=
  Polynomial.hilbertPoly (rationalDegreePolynomial (degreeAt degrees) rs.length)
    (Fintype.card σ - rs.length)

theorem regularSequenceHilbertPolynomial_eventually_exact
    (hσ : 0 < Fintype.card σ)
    (rs : List (MvPolynomial σ k)) (degrees : Fin rs.length → ℕ)
    (hhom : ∀ i : Fin rs.length, rs[i].IsHomogeneous (degrees i))
    (hreg : RingTheory.Sequence.IsRegular (MvPolynomial σ k) rs)
    (hlen : rs.length ≤ Fintype.card σ) (n : ℕ)
    (hn : (rationalDegreePolynomial (degreeAt degrees) rs.length).natDegree < n) :
    (Module.finrank k (quotientSection (Ideal.ofList rs) n) : ℚ) =
      (regularSequenceHilbertPolynomial rs degrees).eval (n : ℚ) := by
  rw [← coeff_rationalSectionHilbertSeries,
    rational_regular_sequence_series_residual hσ rs degrees hhom hreg hlen]
  exact Polynomial.coeff_mul_invOneSubPow_eq_hilbertPoly_eval _ hn

theorem hilbertPolynomial_top_coefficient (p : Polynomial ℚ) (r : ℕ) (hr : 0 < r) :
    (Polynomial.hilbertPoly p r).coeff (r-1) =
      p.eval 1 * ((r-1).factorial : ℚ)⁻¹ := by
  obtain ⟨s, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hr)
  simp only [Nat.succ_sub_one, Polynomial.hilbertPoly_succ,
    Polynomial.finsetSum_coeff, Polynomial.coeff_smul, smul_eq_mul,
    Polynomial.coeff_preHilbertPoly_self]
  rw [← Finset.sum_mul]
  congr 1
  simp [Polynomial.eval_eq_sum, Polynomial.sum]

theorem hilbertPolynomial_natDegree_le (p : Polynomial ℚ) (r : ℕ) (hr : 0 < r) :
    (Polynomial.hilbertPoly p r).natDegree ≤ r-1 := by
  obtain ⟨s, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hr)
  simp only [Nat.succ_sub_one, Polynomial.hilbertPoly_succ]
  apply Polynomial.natDegree_sum_le_of_forall_le
  intro i _
  exact (Polynomial.natDegree_smul_le _ _).trans
    (Polynomial.natDegree_preHilbertPoly ℚ s i).le

theorem hilbertPolynomial_degree_and_leading
    (p : Polynomial ℚ) (r : ℕ) (hr : 0 < r) (hp : p.eval 1 ≠ 0) :
    (Polynomial.hilbertPoly p r).natDegree = r-1 ∧
      (Polynomial.hilbertPoly p r).leadingCoeff = p.eval 1 * ((r-1).factorial : ℚ)⁻¹ := by
  have hf : (((r-1).factorial : ℕ) : ℚ) ≠ 0 := by
    exact_mod_cast Nat.factorial_ne_zero (r-1)
  have hc : (Polynomial.hilbertPoly p r).coeff (r-1) ≠ 0 := by
    rw [hilbertPolynomial_top_coefficient p r hr]
    exact mul_ne_zero hp (inv_ne_zero hf)
  have hd := Polynomial.natDegree_eq_of_le_of_coeff_ne_zero
    (hilbertPolynomial_natDegree_le p r hr) hc
  refine ⟨hd, ?_⟩
  rw [Polynomial.leadingCoeff, hd, hilbertPolynomial_top_coefficient p r hr]

noncomputable def hilbertMultiplicity (p : Polynomial ℚ) (ringDimension : ℕ) : ℚ :=
  p.coeff (ringDimension-1) * ((ringDimension-1).factorial : ℚ)

theorem regularSequenceHilbertPolynomial_multiplicity
    (rs : List (MvPolynomial σ k)) (degrees : Fin rs.length → ℕ)
    (hlen : rs.length < Fintype.card σ) :
    hilbertMultiplicity (regularSequenceHilbertPolynomial rs degrees)
        (Fintype.card σ - rs.length) =
      (∏ i ∈ Finset.range rs.length, degreeAt degrees i : ℕ) := by
  have hr : 0 < Fintype.card σ - rs.length := Nat.sub_pos_of_lt hlen
  have hf : (((Fintype.card σ - rs.length - 1).factorial : ℕ) : ℚ) ≠ 0 := by
    exact_mod_cast Nat.factorial_ne_zero (Fintype.card σ - rs.length - 1)
  rw [hilbertMultiplicity, regularSequenceHilbertPolynomial,
    hilbertPolynomial_top_coefficient _ _ hr, mul_assoc, inv_mul_cancel₀ hf,
    mul_one, rationalDegreePolynomial_eval_one]

end PiExponentJets.W64

end OAI
end Source0176

-- Source: OAI/NumberTheory/PiExponent/LocalAlgebra/ColonHilbertStep.lean
section Source0177
/-
Modification notice for the LogTwo project.
Derived from openai/math (Apache-2.0), revision adc7f1241b42e322a6451854ab7e4b4c146bf78a.
Original source: lean/OAI/NumberTheory/PiExponent/LocalAlgebra/ColonHilbertStep.lean
Changes: Convert module/import declarations to the Lean 4.34 public module format.
See ../THIRD_PARTY_NOTICES.txt for provenance and the recorded changes.
-/

namespace OAI

namespace PiExponentJets.W64

attribute [local instance] MvPolynomial.gradedAlgebra
variable {k σ : Type*} [Field k] [Finite σ]

omit [Finite σ] in
theorem ideal_le_colon_singleton (I : Ideal (MvPolynomial σ k))
    (f : MvPolynomial σ k) : I ≤ I.colon {f} := by
  intro p hp
  apply Submodule.mem_colon_singleton.mpr
  simpa only [smul_eq_mul] using I.mul_mem_right f hp

omit [Finite σ] in
theorem quotientSectionFactor_colon_ker (I : Ideal (MvPolynomial σ k))
    {d : ℕ} (f : MvPolynomial σ k) (hf : f.IsHomogeneous d) (n : ℕ) :
    LinearMap.ker (quotientSectionFactor I (I.colon {f})
      (ideal_le_colon_singleton I f) n) =
      LinearMap.ker (quotientSectionMultiply I f hf n) := by
  ext x
  obtain ⟨p, hp, hpx⟩ := Submodule.mem_map.mp x.2
  change Ideal.Quotient.mk I p = x.1 at hpx
  simp only [LinearMap.mem_ker, Subtype.ext_iff]
  change (Ideal.Quotient.factorₐ k (ideal_le_colon_singleton I f)) x.1 = 0 ↔
    x.1 * Ideal.Quotient.mk I f = 0
  rw [← hpx]
  change Ideal.Quotient.mk (I.colon {f}) p = 0 ↔
    Ideal.Quotient.mk I (p * f) = 0
  rw [Ideal.Quotient.eq_zero_iff_mem, Ideal.Quotient.eq_zero_iff_mem,
    Submodule.mem_colon_singleton, smul_eq_mul]

theorem quotientSectionMultiply_range_finrank_colon
    (I : Ideal (MvPolynomial σ k)) {d : ℕ}
    (f : MvPolynomial σ k) (hf : f.IsHomogeneous d) (n : ℕ) :
    Module.finrank k (LinearMap.range (quotientSectionMultiply I f hf n)) =
      Module.finrank k (quotientSection (I.colon {f}) n) := by
  let φ := quotientSectionFactor I (I.colon {f}) (ideal_le_colon_singleton I f) n
  have hd := (LinearMap.ker φ).finrank_quotient_add_finrank
  let e := φ.quotKerEquivOfSurjective
    (quotientSectionFactor_surjective I (I.colon {f}) (ideal_le_colon_singleton I f) n)
  rw [e.finrank_eq] at hd
  change Module.finrank k (quotientSection (I.colon {f}) n) +
    Module.finrank k (LinearMap.ker (quotientSectionFactor I (I.colon {f})
      (ideal_le_colon_singleton I f) n)) = _ at hd
  rw [quotientSectionFactor_colon_ker I f hf n] at hd
  have hm := (quotientSectionMultiply I f hf n).finrank_range_add_finrank_ker
  omega

theorem colon_hilbert_step (I : Ideal (MvPolynomial σ k))
    (hI : I.IsHomogeneous (MvPolynomial.homogeneousSubmodule σ k))
    {d : ℕ} (f : MvPolynomial σ k) (hf : f.IsHomogeneous d) (n : ℕ) :
    Module.finrank k (quotientSection (Ideal.span {f} ⊔ I) (n+d)) +
      Module.finrank k (quotientSection (I.colon {f}) n) =
      Module.finrank k (quotientSection I (n+d)) := by
  have hd := (LinearMap.range (quotientSectionMultiply I f hf n)).finrank_quotient_add_finrank
  rw [quotientSectionMultiply_range_finrank_colon I f hf n,
    ← quotientSectionFactor_ker_eq I hI f hf n] at hd
  let e := (quotientSectionFactor I (Ideal.span {f} ⊔ I) le_sup_right (n+d)).quotKerEquivOfSurjective
    (quotientSectionFactor_surjective I (Ideal.span {f} ⊔ I) le_sup_right (n+d))
  rw [e.finrank_eq] at hd
  exact hd

theorem sectionHilbertSeries_colon_step (I : Ideal (MvPolynomial σ k))
    (hI : I.IsHomogeneous (MvPolynomial.homogeneousSubmodule σ k))
    {d : ℕ} (f : MvPolynomial σ k) (hf : f.IsHomogeneous d) :
    sectionHilbertSeries I = sectionHilbertSeries (Ideal.span {f} ⊔ I) +
      PowerSeries.X ^ d * sectionHilbertSeries (I.colon {f}) := by
  ext n
  rw [map_add, PowerSeries.coeff_X_pow_mul']
  simp only [coeff_sectionHilbertSeries]
  by_cases hdn : d ≤ n
  · rw [ite_eq_left hdn]
    have h := colon_hilbert_step I hI f hf (n-d)
    rw [Nat.sub_add_cancel hdn] at h
    exact_mod_cast h.symm
  · rw [ite_eq_right hdn, add_zero]
    exact congrArg (fun m : ℕ => (m : ℤ))
      (hilbert_step_of_degree_lt I hI f hf (Nat.lt_of_not_ge hdn)).symm

end PiExponentJets.W64

end OAI
end Source0177

-- Source: OAI/NumberTheory/PiExponent/Polynomials/HomogeneousPrimeFactor.lean
section Source0178
/-
Modification notice for the LogTwo project.
Derived from openai/math (Apache-2.0), revision adc7f1241b42e322a6451854ab7e4b4c146bf78a.
Original source: lean/OAI/NumberTheory/PiExponent/Polynomials/HomogeneousPrimeFactor.lean
Changes: Convert module/import declarations to the Lean 4.34 public module format.
See ../THIRD_PARTY_NOTICES.txt for provenance and the recorded changes.
-/

namespace OAI

namespace PiExponentJets.W22

attribute [local instance] MvPolynomial.gradedAlgebra

variable {k σ : Type*} [Field k] [Finite σ]

omit [Finite σ] in
theorem homogeneous_colon_singleton
    (I : Ideal (MvPolynomial σ k))
    (hI : I.IsHomogeneous (MvPolynomial.homogeneousSubmodule σ k))
    {d : ℕ} {f : MvPolynomial σ k} (hf : f.IsHomogeneous d) :
    (I.colon {f}).IsHomogeneous (MvPolynomial.homogeneousSubmodule σ k) := by
  intro n a ha
  apply Submodule.mem_colon_singleton.mpr
  have haf : a * f ∈ I := by simpa only [smul_eq_mul] using
    (Submodule.mem_colon_singleton.mp ha)
  have h := hI (n + d) haf
  rw [DirectSum.coe_decompose_mul_add_of_right_mem
    (MvPolynomial.homogeneousSubmodule σ k) hf] at h
  exact h

theorem exists_homogeneous_prime_colon
    (I : Ideal (MvPolynomial σ k))
    (hI : I.IsHomogeneous (MvPolynomial.homogeneousSubmodule σ k))
    (hproper : I ≠ ⊤) :
    ∃ (d : ℕ) (f : MvPolynomial σ k), f.IsHomogeneous d ∧ f ∉ I ∧
      (I.colon {f}).IsPrime := by
  classical
  let candidates : Ideal (MvPolynomial σ k) → Prop := fun P =>
    ∃ d f, f.IsHomogeneous d ∧ f ∉ I ∧ P = I.colon {f}
  have hnonempty : ∃ P, candidates P := by
    refine ⟨I.colon {(1 : MvPolynomial σ k)}, 0, 1, ?_, ?_, rfl⟩
    · exact MvPolynomial.isHomogeneous_one σ k
    · exact fun h => hproper (Ideal.eq_top_of_isUnit_mem I h isUnit_one)
  obtain ⟨P, hP, hmax⟩ := exists_maximal_of_wellFoundedGT candidates hnonempty
  obtain ⟨d, f, hf, hfI, rfl⟩ := hP
  refine ⟨d, f, hf, hfI, ?_⟩
  apply (homogeneous_colon_singleton I hI hf).isPrime_of_homogeneous_mem_or_mem
  · intro htop
    have h : (1 : MvPolynomial σ k) ∈ I.colon {f} := by
      rw [htop]
      trivial
    exact hfI (by simpa only [Submodule.mem_colon_singleton, one_smul] using h)
  · intro a b ha hb hab
    by_cases hbI : b ∈ I.colon {f}
    · exact Or.inr hbI
    · left
      obtain ⟨e, he⟩ := hb
      have hb' : b.IsHomogeneous e := he
      have hbf : (b * f).IsHomogeneous (e + d) := hb'.mul hf
      have hbfI : b * f ∉ I := by
        simpa only [Submodule.mem_colon_singleton, smul_eq_mul] using hbI
      have hle : I.colon {f} ≤ I.colon {b * f} := by
        intro r hr
        apply Submodule.mem_colon_singleton.mpr
        have hrf : r * f ∈ I := by
          simpa only [smul_eq_mul] using (Submodule.mem_colon_singleton.mp hr)
        simpa only [smul_eq_mul, mul_left_comm r b f] using I.mul_mem_left b hrf
      have hback : I.colon {b * f} ≤ I.colon {f} :=
        hmax ⟨e + d, b * f, hbf, hbfI, rfl⟩ hle
      apply hback
      apply Submodule.mem_colon_singleton.mpr
      simpa only [smul_eq_mul, mul_assoc] using (Submodule.mem_colon_singleton.mp hab)

end PiExponentJets.W22

end OAI
end Source0178

-- Source: OAI/NumberTheory/PiExponent/Analysis/ColonSeriesTelescope.lean
section Source0179
/-
Modification notice for the LogTwo project.
Derived from openai/math (Apache-2.0), revision adc7f1241b42e322a6451854ab7e4b4c146bf78a.
Original source: lean/OAI/NumberTheory/PiExponent/Analysis/ColonSeriesTelescope.lean
Changes: Convert module/import declarations to the Lean 4.34 public module format.
See ../THIRD_PARTY_NOTICES.txt for provenance and the recorded changes.
-/

namespace OAI

namespace PiExponentJets.W64

open scoped BigOperators
attribute [local instance] MvPolynomial.gradedAlgebra
variable {k σ : Type*} [Field k]

noncomputable def iteratedColon (I : Ideal (MvPolynomial σ k)) (f : MvPolynomial σ k) :
    ℕ → Ideal (MvPolynomial σ k)
  | 0 => I
  | n+1 => (iteratedColon I f n).colon {f}

@[simp] theorem iteratedColon_zero (I : Ideal (MvPolynomial σ k)) (f : MvPolynomial σ k) :
    iteratedColon I f 0 = I := rfl

@[simp] theorem iteratedColon_succ (I : Ideal (MvPolynomial σ k)) (f : MvPolynomial σ k)
    (n : ℕ) : iteratedColon I f (n+1) = (iteratedColon I f n).colon {f} := rfl

theorem iteratedColon_homogeneous (I : Ideal (MvPolynomial σ k))
    (hI : I.IsHomogeneous (MvPolynomial.homogeneousSubmodule σ k))
    {d : ℕ} (f : MvPolynomial σ k) (hf : f.IsHomogeneous d) (n : ℕ) :
    (iteratedColon I f n).IsHomogeneous (MvPolynomial.homogeneousSubmodule σ k) := by
  induction n with
  | zero => exact hI
  | succ n ih => exact PiExponentJets.W22.homogeneous_colon_singleton _ ih hf

variable [Finite σ]

theorem iteratedColon_series_telescope (I : Ideal (MvPolynomial σ k))
    (hI : I.IsHomogeneous (MvPolynomial.homogeneousSubmodule σ k))
    (f : MvPolynomial σ k) (hf : f.IsHomogeneous 1) (m : ℕ) :
    sectionHilbertSeries I =
      (∑ j ∈ Finset.range m, PowerSeries.X ^ j *
        sectionHilbertSeries (Ideal.span {f} ⊔ iteratedColon I f j)) +
      PowerSeries.X ^ m * sectionHilbertSeries (iteratedColon I f m) := by
  induction m with
  | zero => simp
  | succ m ih =>
    have hs := sectionHilbertSeries_colon_step (iteratedColon I f m)
      (iteratedColon_homogeneous I hI f hf m) f hf
    simp only [pow_one, ← iteratedColon_succ] at hs
    rw [ih, hs, Finset.sum_range_succ, pow_succ]
    ring

theorem stableColon_series (I : Ideal (MvPolynomial σ k))
    (hI : I.IsHomogeneous (MvPolynomial.homogeneousSubmodule σ k))
    (f : MvPolynomial σ k) (hf : f.IsHomogeneous 1)
    (hstable : I.colon {f} = I) :
    sectionHilbertSeries I = sectionHilbertSeries (Ideal.span {f} ⊔ I) *
      (PowerSeries.invOneSubPow ℤ 1).val := by
  have hs := sectionHilbertSeries_colon_step I hI f hf
  rw [hstable, pow_one] at hs
  have he : (1 - PowerSeries.X) * sectionHilbertSeries I =
      sectionHilbertSeries (Ideal.span {f} ⊔ I) := by
    linear_combination hs
  have hunit : (1 - (PowerSeries.X : PowerSeries ℤ)) *
      (PowerSeries.invOneSubPow ℤ 1).val = 1 := by
    rw [← pow_one (1 - (PowerSeries.X : PowerSeries ℤ)),
      ← PowerSeries.invOneSubPow_inv_eq_one_sub_pow]
    exact (PowerSeries.invOneSubPow ℤ 1).inv_val
  calc
    sectionHilbertSeries I = ((1-PowerSeries.X) * sectionHilbertSeries I) *
        (PowerSeries.invOneSubPow ℤ 1).val := by
          rw [mul_right_comm, hunit, one_mul]
    _ = _ := by rw [he]

theorem stabilized_iteratedColon_series (I : Ideal (MvPolynomial σ k))
    (hI : I.IsHomogeneous (MvPolynomial.homogeneousSubmodule σ k))
    (f : MvPolynomial σ k) (hf : f.IsHomogeneous 1) (m : ℕ)
    (hstable : iteratedColon I f (m+1) = iteratedColon I f m) :
    sectionHilbertSeries I =
      (∑ j ∈ Finset.range m, PowerSeries.X ^ j *
        sectionHilbertSeries (Ideal.span {f} ⊔ iteratedColon I f j)) +
      PowerSeries.X ^ m *
        (sectionHilbertSeries (Ideal.span {f} ⊔ iteratedColon I f m) *
          (PowerSeries.invOneSubPow ℤ 1).val) := by
  rw [iteratedColon_series_telescope I hI f hf m,
    stableColon_series (iteratedColon I f m)
      (iteratedColon_homogeneous I hI f hf m) f hf hstable]

end PiExponentJets.W64

end OAI
end Source0179

-- Source: OAI/NumberTheory/PiExponent/LocalAlgebra/HilbertDenominatorReduction.lean
section Source0180
/-
Modification notice for the LogTwo project.
Derived from openai/math (Apache-2.0), revision adc7f1241b42e322a6451854ab7e4b4c146bf78a.
Original source: lean/OAI/NumberTheory/PiExponent/LocalAlgebra/HilbertDenominatorReduction.lean
Changes: Convert module/import declarations to the Lean 4.34 public module format.
See ../THIRD_PARTY_NOTICES.txt for provenance and the recorded changes.
-/

namespace OAI

namespace PiExponentJets.W64

open scoped BigOperators
attribute [local instance] MvPolynomial.gradedAlgebra
variable {k σ : Type*} [Field k] [Finite σ]

noncomputable def colonHilbertNumerator (P : ℕ → Polynomial ℤ) (m : ℕ) : Polynomial ℤ :=
  (∑ j ∈ Finset.range m, Polynomial.X ^ j * P j) * (1 - Polynomial.X) +
    Polynomial.X ^ m * P m

theorem stabilized_colon_polynomial_numerator
    (I : Ideal (MvPolynomial σ k))
    (hI : I.IsHomogeneous (MvPolynomial.homogeneousSubmodule σ k))
    (f : MvPolynomial σ k) (hf : f.IsHomogeneous 1) (m r : ℕ)
    (hstable : iteratedColon I f (m+1) = iteratedColon I f m)
    (P : ℕ → Polynomial ℤ)
    (hP : ∀ j : ℕ, sectionHilbertSeries (Ideal.span {f} ⊔ iteratedColon I f j) =
      (P j : PowerSeries ℤ) * (PowerSeries.invOneSubPow ℤ r).val) :
    sectionHilbertSeries I = (colonHilbertNumerator P m : PowerSeries ℤ) *
      (PowerSeries.invOneSubPow ℤ (r+1)).val := by
  have hu : (PowerSeries.invOneSubPow ℤ r).val =
      (1-PowerSeries.X) * (PowerSeries.invOneSubPow ℤ (r+1)).val := by
    symm
    simpa only [pow_one, Nat.add_comm] using
      PowerSeries.one_sub_pow_mul_invOneSubPow_val_add_eq_invOneSubPow_val ℤ r 1
  have hv : (PowerSeries.invOneSubPow ℤ r).val * (PowerSeries.invOneSubPow ℤ 1).val =
      (PowerSeries.invOneSubPow ℤ (r+1)).val := by
    rw [← Units.val_mul, ← PowerSeries.invOneSubPow_add]
  rw [stabilized_iteratedColon_series I hI f hf m hstable]
  simp_rw [hP]
  have hsum : (∑ j ∈ Finset.range m,
      PowerSeries.X ^ j * ((P j : PowerSeries ℤ) * (PowerSeries.invOneSubPow ℤ r).val)) =
      (∑ j ∈ Finset.range m, PowerSeries.X ^ j * (P j : PowerSeries ℤ)) *
        (PowerSeries.invOneSubPow ℤ r).val := by
    simp only [Finset.sum_mul, mul_assoc]
  rw [hsum, mul_assoc (P m : PowerSeries ℤ), hv, hu]
  have hcoe : (colonHilbertNumerator P m : PowerSeries ℤ) =
      (∑ j ∈ Finset.range m, PowerSeries.X ^ j * (P j : PowerSeries ℤ)) *
        (1-PowerSeries.X) + PowerSeries.X ^ m * (P m : PowerSeries ℤ) := by
    change Polynomial.coeToPowerSeries.ringHom
      ((∑ j ∈ Finset.range m, Polynomial.X ^ j * P j) * (1-Polynomial.X) +
        Polynomial.X ^ m * P m) = _
    rw [map_add, map_mul, map_sum]
    simp only [map_mul, map_sub, map_pow, map_one]
    simp only [Polynomial.coeToPowerSeries.ringHom_apply, Polynomial.coe_X]
  rw [hcoe]
  ring

end PiExponentJets.W64

end OAI
end Source0180

-- Source: OAI/NumberTheory/PiExponent/LocalAlgebra/HilbertZeroVariables.lean
section Source0181
/-
Modification notice for the LogTwo project.
Derived from openai/math (Apache-2.0), revision adc7f1241b42e322a6451854ab7e4b4c146bf78a.
Original source: lean/OAI/NumberTheory/PiExponent/LocalAlgebra/HilbertZeroVariables.lean
Changes: Convert module/import declarations to the Lean 4.34 public module format.
See ../THIRD_PARTY_NOTICES.txt for provenance and the recorded changes.
-/

namespace OAI

namespace PiExponentJets.W64

variable {k σ : Type*} [Field k] [Fintype σ]

theorem quotientSection_finrank_zero_of_no_variables
    (hσ : Fintype.card σ = 0) (I : Ideal (MvPolynomial σ k)) (n : ℕ) :
    Module.finrank k (quotientSection I (n+1)) = 0 := by
  have h := Submodule.finrank_map_le (Ideal.Quotient.mkₐ k I).toLinearMap
    (MvPolynomial.homogeneousSubmodule σ k (n+1))
  rw [homogeneousSection_finrank, card_exponents_degree, hσ,
    Nat.multichoose_zero_succ] at h
  exact Nat.eq_zero_of_le_zero h

theorem sectionHilbertSeries_no_variables
    (hσ : Fintype.card σ = 0) (I : Ideal (MvPolynomial σ k)) :
    sectionHilbertSeries I = PowerSeries.C (Module.finrank k (quotientSection I 0) : ℤ) := by
  ext n
  cases n with
  | zero => simp
  | succ n =>
    rw [coeff_sectionHilbertSeries, quotientSection_finrank_zero_of_no_variables hσ I n]
    simp only [PowerSeries.coeff_C, Nat.succ_ne_zero, ite_false, Nat.cast_zero]

theorem exists_hilbert_numerator_no_variables
    (hσ : Fintype.card σ = 0) (I : Ideal (MvPolynomial σ k)) :
    ∃ P : Polynomial ℤ, sectionHilbertSeries I =
      (P : PowerSeries ℤ) * (PowerSeries.invOneSubPow ℤ (Fintype.card σ)).val := by
  refine ⟨Polynomial.C (Module.finrank k (quotientSection I 0) : ℤ), ?_⟩
  simpa only [hσ, PowerSeries.invOneSubPow_zero, Units.val_one, mul_one,
    Polynomial.coe_C] using sectionHilbertSeries_no_variables hσ I

end PiExponentJets.W64

end OAI
end Source0181

-- Source: OAI/NumberTheory/PiExponent/LocalAlgebra/StabilizedColonPowers.lean
section Source0182
-- Modified in this edition: unused plain lemmas removed; see reduction.json.
/-
Modification notice for the LogTwo project.
Derived from openai/math (Apache-2.0), revision adc7f1241b42e322a6451854ab7e4b4c146bf78a.
Original source: lean/OAI/NumberTheory/PiExponent/LocalAlgebra/StabilizedColonPowers.lean
Changes: Convert module/import declarations to the Lean 4.34 public module format.
See ../THIRD_PARTY_NOTICES.txt for provenance and the recorded changes.
-/

namespace OAI

namespace PiExponentJets.W06

section ColonPowers
variable {R : Type*} [CommRing R]

@[simp] theorem colon_pow_zero (I : Ideal R) (x : R) :
    I.colon {x ^ (0 : ℕ)} = I := by
  ext a
  simp [Submodule.mem_colon_singleton, smul_eq_mul]

theorem colon_pow_succ (I : Ideal R) (x : R) (j : ℕ) :
    I.colon {x ^ (j + 1)} = (I.colon {x ^ j}).colon {x} := by
  ext a
  simp only [Submodule.mem_colon_singleton, smul_eq_mul, pow_succ,
    mul_assoc, mul_comm, mul_left_comm]

theorem colon_powers_monotone (I : Ideal R) (x : R) :
    Monotone (fun j : ℕ => I.colon {x ^ j}) := by
  apply monotone_nat_of_le_succ
  intro j
  rw [colon_pow_succ]
  exact Ideal.le_colon

theorem exists_colon_powers_eventually_constant [IsNoetherianRing R]
    (I : Ideal R) (x : R) :
    ∃ m : ℕ, ∀ j : ℕ, m ≤ j → I.colon {x ^ j} = I.colon {x ^ m} := by
  let chain : ℕ →o Submodule R R :=
    ⟨fun j => I.colon {x ^ j}, colon_powers_monotone I x⟩
  obtain ⟨m, hm⟩ := monotone_stabilizes_iff_noetherian.mpr
    (inferInstance : IsNoetherian R R) chain
  exact ⟨m, fun j hj => (hm j hj).symm⟩

theorem exists_colon_pow_stable [IsNoetherianRing R] (I : Ideal R) (x : R) :
    ∃ m : ℕ, I.colon {x ^ (m + 1)} = I.colon {x ^ m} := by
  obtain ⟨m, hm⟩ := exists_colon_powers_eventually_constant I x
  exact ⟨m, hm (m + 1) (Nat.le_succ m)⟩

end ColonPowers

attribute [local instance] MvPolynomial.gradedAlgebra
variable {k σ : Type*} [Field k]

end PiExponentJets.W06

end OAI
end Source0182

-- Source: OAI/NumberTheory/PiExponent/Polynomials/CoordinateQuotientGrading.lean
section Source0183
/-
Modification notice for the LogTwo project.
Derived from openai/math (Apache-2.0), revision adc7f1241b42e322a6451854ab7e4b4c146bf78a.
Original source: lean/OAI/NumberTheory/PiExponent/Polynomials/CoordinateQuotientGrading.lean
Changes: Convert module/import declarations to the Lean 4.34 public module format.
See ../THIRD_PARTY_NOTICES.txt for provenance and the recorded changes.
-/

namespace OAI

attribute [local instance] MvPolynomial.gradedAlgebra

namespace PiExponentSiegel.W08

section

open MvPolynomial

variable {k σ τ : Type*} [Field k]

noncomputable def coordinateEval : MvPolynomial (Option σ) k →ₐ[k] MvPolynomial σ k :=
  MvPolynomial.aeval (fun o => Option.elim o 0 MvPolynomial.X)

noncomputable def coordinateInclude : MvPolynomial σ k →ₐ[k] MvPolynomial (Option σ) k :=
  MvPolynomial.rename Option.some

@[simp] theorem coordinateEval_X_none :
    coordinateEval (k := k) (σ := σ) (X none) = 0 := by simp [coordinateEval]

@[simp] theorem coordinateEval_X_some (i : σ) :
    coordinateEval (k := k) (X (some i)) = X i := by simp [coordinateEval]

@[simp] theorem coordinateEval_include (p : MvPolynomial σ k) :
    coordinateEval (coordinateInclude p) = p := by
  have h : (coordinateEval (k := k) (σ := σ)).comp coordinateInclude = AlgHom.id k _ := by
    ext i
    simp [coordinateInclude]
  exact AlgHom.congr_fun h p

theorem coordinateEval_surjective :
    Function.Surjective (coordinateEval (k := k) (σ := σ)) :=
  fun p => ⟨coordinateInclude p, coordinateEval_include p⟩

theorem coordinateEval_homogeneous {p : MvPolynomial (Option σ) k} {n : ℕ}
    (hp : p.IsHomogeneous n) : (coordinateEval p).IsHomogeneous n := by
  simpa only [coordinateEval, one_mul] using hp.aeval
    (fun o => Option.elim o 0 (MvPolynomial.X : σ → MvPolynomial σ k))
    (show ∀ o : Option σ, (Option.elim o 0 (MvPolynomial.X : σ → MvPolynomial σ k)).IsHomogeneous 1
      from fun o => by cases o with
        | none => exact (homogeneousSubmodule σ k 1).zero_mem
        | some i => exact isHomogeneous_X k i)

theorem coordinateInclude_homogeneous {p : MvPolynomial σ k} {n : ℕ}
    (hp : p.IsHomogeneous n) : (coordinateInclude p).IsHomogeneous n :=
  hp.rename_isHomogeneous

noncomputable def coordinateImageIdeal (J : Ideal (MvPolynomial (Option σ) k)) :
    Ideal (MvPolynomial σ k) := J.map coordinateEval.toRingHom

theorem homogeneous_ideal_map_of_degree_preserving
    (f : MvPolynomial σ k →ₐ[k] MvPolynomial τ k)
    (hf : ∀ n (p : MvPolynomial σ k), p.IsHomogeneous n → (f p).IsHomogeneous n)
    (J : Ideal (MvPolynomial σ k))
    (hJ : J.IsHomogeneous (MvPolynomial.homogeneousSubmodule σ k)) :
    (J.map f.toRingHom).IsHomogeneous (MvPolynomial.homogeneousSubmodule τ k) := by
  obtain ⟨S, hS⟩ := (Ideal.IsHomogeneous.iff_exists (MvPolynomial.homogeneousSubmodule σ k) J).mp hJ
  rw [hS, Ideal.map_span]
  apply Ideal.homogeneous_span
  rintro q ⟨p, ⟨z, hz, rfl⟩, rfl⟩
  obtain ⟨n, hn⟩ := z.property
  exact ⟨n, hf n z hn⟩

theorem coordinateImageIdeal_homogeneous (J : Ideal (MvPolynomial (Option σ) k))
    (hJ : J.IsHomogeneous (MvPolynomial.homogeneousSubmodule (Option σ) k)) :
    (coordinateImageIdeal J).IsHomogeneous (MvPolynomial.homogeneousSubmodule σ k) :=
  homogeneous_ideal_map_of_degree_preserving coordinateEval
    (fun _ _ hp => coordinateEval_homogeneous hp) J hJ

theorem coordinateInclude_eval_mod (J : Ideal (MvPolynomial (Option σ) k))
    (hX : X none ∈ J) (p : MvPolynomial (Option σ) k) :
    Ideal.Quotient.mk J (coordinateInclude (coordinateEval p)) = Ideal.Quotient.mk J p := by
  have h : ((Ideal.Quotient.mkₐ k J).comp coordinateInclude).comp coordinateEval =
      Ideal.Quotient.mkₐ k J := by
    ext i
    cases i with
    | none => simpa [coordinateInclude] using (Ideal.Quotient.eq_zero_iff_mem.mpr hX).symm
    | some i => simp [coordinateInclude]
  exact AlgHom.congr_fun h p

noncomputable def coordinateQuotientMap (J : Ideal (MvPolynomial (Option σ) k)) :
    (MvPolynomial (Option σ) k ⧸ J) →ₐ[k]
      (MvPolynomial σ k ⧸ coordinateImageIdeal J) :=
  Ideal.quotientMapₐ (coordinateImageIdeal J) coordinateEval Ideal.le_comap_map

theorem coordinateInclude_image_mem (J : Ideal (MvPolynomial (Option σ) k))
    (hX : X none ∈ J) {p : MvPolynomial σ k} (hp : p ∈ coordinateImageIdeal J) :
    coordinateInclude p ∈ J := by
  obtain ⟨q, hq, rfl⟩ :=
    (Ideal.mem_map_iff_of_surjective coordinateEval.toRingHom coordinateEval_surjective).mp hp
  apply Ideal.Quotient.eq_zero_iff_mem.mp
  change Ideal.Quotient.mk J (coordinateInclude (coordinateEval q)) = 0
  rw [coordinateInclude_eval_mod J hX]
  exact Ideal.Quotient.eq_zero_iff_mem.mpr hq

noncomputable def coordinateQuotientInverse (J : Ideal (MvPolynomial (Option σ) k))
    (hX : X none ∈ J) :
    (MvPolynomial σ k ⧸ coordinateImageIdeal J) →ₐ[k]
      (MvPolynomial (Option σ) k ⧸ J) :=
  Ideal.quotientMapₐ J coordinateInclude (fun _ hp => coordinateInclude_image_mem J hX hp)

noncomputable def coordinateQuotientEquiv (J : Ideal (MvPolynomial (Option σ) k))
    (hX : X none ∈ J) :
    (MvPolynomial (Option σ) k ⧸ J) ≃ₐ[k]
      (MvPolynomial σ k ⧸ coordinateImageIdeal J) :=
  { coordinateQuotientMap J with
    invFun := coordinateQuotientInverse J hX
    left_inv := by
      intro x
      obtain ⟨p, rfl⟩ := Ideal.Quotient.mk_surjective x
      exact coordinateInclude_eval_mod J hX p
    right_inv := by
      intro x
      obtain ⟨p, rfl⟩ := Ideal.Quotient.mk_surjective x
      change Ideal.Quotient.mk _ (coordinateEval (coordinateInclude p)) = _
      rw [coordinateEval_include] }

@[simp] theorem coordinateQuotientEquiv_mk (J : Ideal (MvPolynomial (Option σ) k))
    (hX : X none ∈ J) (p : MvPolynomial (Option σ) k) :
    coordinateQuotientEquiv J hX (Ideal.Quotient.mk J p) =
      Ideal.Quotient.mk (coordinateImageIdeal J) (coordinateEval p) := rfl

theorem coordinateQuotientEquiv_section_map (J : Ideal (MvPolynomial (Option σ) k))
    (hX : X none ∈ J) (n : ℕ) :
    (PiExponentJets.W64.quotientSection J n).map
      (coordinateQuotientEquiv J hX).toLinearEquiv.toLinearMap =
      PiExponentJets.W64.quotientSection (coordinateImageIdeal J) n := by
  apply le_antisymm
  · intro x hx
    obtain ⟨y, hy, rfl⟩ := Submodule.mem_map.mp hx
    obtain ⟨p, hp, rfl⟩ := Submodule.mem_map.mp hy
    exact Submodule.mem_map.mpr ⟨coordinateEval p, coordinateEval_homogeneous hp, rfl⟩
  · intro x hx
    obtain ⟨p, hp, rfl⟩ := Submodule.mem_map.mp hx
    apply Submodule.mem_map.mpr
    refine ⟨Ideal.Quotient.mk J (coordinateInclude p), ?_, ?_⟩
    · exact Submodule.mem_map.mpr ⟨coordinateInclude p, coordinateInclude_homogeneous hp, rfl⟩
    · change Ideal.Quotient.mk _ (coordinateEval (coordinateInclude p)) = _
      rw [coordinateEval_include]
      rfl

noncomputable def coordinateQuotientSectionEquiv (J : Ideal (MvPolynomial (Option σ) k))
    (hX : X none ∈ J) (n : ℕ) :
    PiExponentJets.W64.quotientSection J n ≃ₗ[k]
      PiExponentJets.W64.quotientSection (coordinateImageIdeal J) n :=
  (coordinateQuotientEquiv J hX).toLinearEquiv.ofSubmodules _ _
    (coordinateQuotientEquiv_section_map J hX n)

theorem coordinateQuotientSection_finrank (J : Ideal (MvPolynomial (Option σ) k))
    (hX : X none ∈ J) (n : ℕ) :
    Module.finrank k (PiExponentJets.W64.quotientSection J n) =
      Module.finrank k (PiExponentJets.W64.quotientSection (coordinateImageIdeal J) n) :=
  (coordinateQuotientSectionEquiv J hX n).finrank_eq

end

variable {k σ τ : Type*} [Field k]

noncomputable def renameQuotientEquiv (e : σ ≃ τ) (J : Ideal (MvPolynomial σ k)) :
    (MvPolynomial σ k ⧸ J) ≃ₐ[k]
      (MvPolynomial τ k ⧸ J.map (MvPolynomial.rename e).toRingHom) :=
  Ideal.quotientEquivAlg J _ (MvPolynomial.renameEquiv k e) rfl

theorem renameQuotientEquiv_section_map (e : σ ≃ τ)
    (J : Ideal (MvPolynomial σ k)) (n : ℕ) :
    (PiExponentJets.W64.quotientSection J n).map
      (renameQuotientEquiv e J).toLinearEquiv.toLinearMap =
      PiExponentJets.W64.quotientSection (J.map (MvPolynomial.rename e).toRingHom) n := by
  apply le_antisymm
  · intro x hx
    obtain ⟨y, hy, rfl⟩ := Submodule.mem_map.mp hx
    obtain ⟨p, hp, rfl⟩ := Submodule.mem_map.mp hy
    exact Submodule.mem_map.mpr ⟨MvPolynomial.rename e p, hp.rename_isHomogeneous, rfl⟩
  · intro x hx
    obtain ⟨p, hp, rfl⟩ := Submodule.mem_map.mp hx
    apply Submodule.mem_map.mpr
    refine ⟨Ideal.Quotient.mk J (MvPolynomial.rename e.symm p), ?_, ?_⟩
    · exact Submodule.mem_map.mpr ⟨MvPolynomial.rename e.symm p, hp.rename_isHomogeneous, rfl⟩
    · change Ideal.Quotient.mk _ (MvPolynomial.rename e (MvPolynomial.rename e.symm p)) = _
      exact congrArg (Ideal.Quotient.mk _) ((MvPolynomial.renameEquiv k e).apply_symm_apply p)

noncomputable def renameQuotientSectionEquiv (e : σ ≃ τ)
    (J : Ideal (MvPolynomial σ k)) (n : ℕ) :
    PiExponentJets.W64.quotientSection J n ≃ₗ[k]
      PiExponentJets.W64.quotientSection (J.map (MvPolynomial.rename e).toRingHom) n :=
  (renameQuotientEquiv e J).toLinearEquiv.ofSubmodules _ _
    (renameQuotientEquiv_section_map e J n)

theorem renameQuotientSection_finrank (e : σ ≃ τ)
    (J : Ideal (MvPolynomial σ k)) (n : ℕ) :
    Module.finrank k (PiExponentJets.W64.quotientSection J n) =
      Module.finrank k
        (PiExponentJets.W64.quotientSection (J.map (MvPolynomial.rename e).toRingHom) n) :=
  (renameQuotientSectionEquiv e J n).finrank_eq

theorem renameImageIdeal_homogeneous (e : σ ≃ τ) (J : Ideal (MvPolynomial σ k))
    (hJ : J.IsHomogeneous (MvPolynomial.homogeneousSubmodule σ k)) :
    (J.map (MvPolynomial.rename e).toRingHom).IsHomogeneous
      (MvPolynomial.homogeneousSubmodule τ k) :=
  homogeneous_ideal_map_of_degree_preserving (MvPolynomial.rename e)
    (fun _ _ hp => hp.rename_isHomogeneous) J hJ

end PiExponentSiegel.W08

end OAI
end Source0183

-- Source: OAI/NumberTheory/PiExponent/Polynomials/HomogeneousHilbertExistence.lean
section Source0184
/-
Modification notice for the LogTwo project.
Derived from openai/math (Apache-2.0), revision adc7f1241b42e322a6451854ab7e4b4c146bf78a.
Original source: lean/OAI/NumberTheory/PiExponent/Polynomials/HomogeneousHilbertExistence.lean
Changes: Convert module/import declarations to the Lean 4.34 public module format.
See ../THIRD_PARTY_NOTICES.txt for provenance and the recorded changes.
-/

namespace OAI

namespace PiExponentJets.W64

universe u v
attribute [local instance] MvPolynomial.gradedAlgebra
variable {k : Type v} [Field k]

theorem iteratedColon_eq_colon_power {σ : Type u} [Finite σ]
    (I : Ideal (MvPolynomial σ k)) (f : MvPolynomial σ k) (n : ℕ) :
    iteratedColon I f n = I.colon {f^n} := by
  induction n with
  | zero => simp only [iteratedColon_zero, PiExponentJets.W06.colon_pow_zero]
  | succ n ih => rw [iteratedColon_succ, ih, PiExponentJets.W06.colon_pow_succ]

theorem sectionHilbertSeries_rename {σ τ : Type u} [Finite σ] [Finite τ]
    (e : σ ≃ τ) (I : Ideal (MvPolynomial σ k)) :
    sectionHilbertSeries I =
      sectionHilbertSeries (I.map (MvPolynomial.rename e).toRingHom) := by
  ext n
  simp only [coeff_sectionHilbertSeries,
    PiExponentSiegel.W08.renameQuotientSection_finrank e I n]

theorem sectionHilbertSeries_coordinate {σ : Type u} [Finite σ]
    (I : Ideal (MvPolynomial (Option σ) k)) (hX : MvPolynomial.X none ∈ I) :
    sectionHilbertSeries I =
      sectionHilbertSeries (PiExponentSiegel.W08.coordinateImageIdeal I) := by
  ext n
  simp only [coeff_sectionHilbertSeries,
    PiExponentSiegel.W08.coordinateQuotientSection_finrank I hX n]

theorem exists_homogeneous_hilbert_numerator
    (σ : Type u) [Fintype σ] (I : Ideal (MvPolynomial σ k))
    (hI : I.IsHomogeneous (MvPolynomial.homogeneousSubmodule σ k)) :
    ∃ P : Polynomial ℤ, sectionHilbertSeries I =
      (P : PowerSeries ℤ) * (PowerSeries.invOneSubPow ℤ (Fintype.card σ)).val := by
  classical
  refine Fintype.induction_empty_option
    (P := fun τ _ => ∀ J : Ideal (MvPolynomial τ k),
      J.IsHomogeneous (MvPolynomial.homogeneousSubmodule τ k) →
      ∃ P : Polynomial ℤ, sectionHilbertSeries J =
        (P : PowerSeries ℤ) * (PowerSeries.invOneSubPow ℤ (Fintype.card τ)).val)
    ?_ ?_ ?_ σ I hI
  · intro α β _ e ih J hJ
    let : Fintype α := Fintype.ofEquiv β e.symm
    obtain ⟨P, hP⟩ := ih (J.map (MvPolynomial.rename e.symm).toRingHom)
      (PiExponentSiegel.W08.renameImageIdeal_homogeneous e.symm J hJ)
    refine ⟨P, ?_⟩
    rw [sectionHilbertSeries_rename e.symm J]
    simpa only [Fintype.card_congr e] using hP
  · intro J _
    exact exists_hilbert_numerator_no_variables (by simp) J
  · intro α _ ih J hJ
    let f : MvPolynomial (Option α) k := MvPolynomial.X none
    have hf : f.IsHomogeneous 1 := MvPolynomial.isHomogeneous_X k none
    obtain ⟨m, hm⟩ := PiExponentJets.W06.exists_colon_pow_stable J f
    have hstable : iteratedColon J f (m+1) = iteratedColon J f m := by
      simpa only [iteratedColon_eq_colon_power] using hm
    let Jlower : ℕ → Ideal (MvPolynomial (Option α) k) :=
      fun j => Ideal.span {f} ⊔ iteratedColon J f j
    have hlower : ∀ j, (Jlower j).IsHomogeneous
        (MvPolynomial.homogeneousSubmodule (Option α) k) := by
      intro j
      apply Ideal.IsHomogeneous.sup
      · apply Ideal.homogeneous_span (MvPolynomial.homogeneousSubmodule (Option α) k)
        intro g hg
        obtain rfl := Set.mem_singleton_iff.mp hg
        exact ⟨1, hf⟩
      · exact iteratedColon_homogeneous J hJ f hf j
    have hX : ∀ j, MvPolynomial.X none ∈ Jlower j := by
      intro j
      have hinc : Ideal.span {f} ≤ Jlower j := le_sup_left
      exact hinc (Ideal.subset_span (Set.mem_singleton f))
    choose P hP using fun j => ih (PiExponentSiegel.W08.coordinateImageIdeal (Jlower j))
      (PiExponentSiegel.W08.coordinateImageIdeal_homogeneous (Jlower j) (hlower j))
    have hseries : ∀ j, sectionHilbertSeries (Ideal.span {f} ⊔ iteratedColon J f j) =
        (P j : PowerSeries ℤ) * (PowerSeries.invOneSubPow ℤ (Fintype.card α)).val := by
      intro j
      rw [show Ideal.span {f} ⊔ iteratedColon J f j = Jlower j from rfl,
        sectionHilbertSeries_coordinate (Jlower j) (hX j)]
      exact hP j
    refine ⟨colonHilbertNumerator P m, ?_⟩
    simpa only [Fintype.card_option] using
      stabilized_colon_polynomial_numerator J hJ f hf m (Fintype.card α) hstable P hseries

end PiExponentJets.W64

end OAI
end Source0184

-- Source: OAI/NumberTheory/PiExponent/Polynomials/HomogeneousHilbertPolynomial.lean
section Source0185
-- Modified in this edition: unused plain lemmas removed; see reduction.json.
/-
Modification notice for the LogTwo project.
Derived from openai/math (Apache-2.0), revision adc7f1241b42e322a6451854ab7e4b4c146bf78a.
Original source: lean/OAI/NumberTheory/PiExponent/Polynomials/HomogeneousHilbertPolynomial.lean
Changes: Convert module/import declarations to the Lean 4.34 public module format.
See ../THIRD_PARTY_NOTICES.txt for provenance and the recorded changes.
-/

namespace OAI

namespace PiExponentJets.W64

universe u v
attribute [local instance] MvPolynomial.gradedAlgebra
variable {k : Type v} [Field k]

theorem rational_hilbert_numerator {σ : Type u} [Fintype σ]
    (I : Ideal (MvPolynomial σ k)) (P : Polynomial ℤ)
    (hP : sectionHilbertSeries I =
      (P : PowerSeries ℤ) * (PowerSeries.invOneSubPow ℤ (Fintype.card σ)).val) :
    rationalSectionHilbertSeries I =
      ((P.map (Int.castRingHom ℚ)) : PowerSeries ℚ) *
        (PowerSeries.invOneSubPow ℚ (Fintype.card σ)).val := by
  rw [rationalSectionHilbertSeries, hP, map_mul, map_int_invOneSubPow,
    ← Polynomial.polynomial_map_coe]

theorem exists_homogeneous_hilbert_polynomial
    (σ : Type u) [Fintype σ] (I : Ideal (MvPolynomial σ k))
    (hI : I.IsHomogeneous (MvPolynomial.homogeneousSubmodule σ k)) :
    ∃ p : Polynomial ℚ, ∃ N : ℕ, ∀ n : ℕ, N < n →
      (Module.finrank k (quotientSection I n) : ℚ) = p.eval (n : ℚ) := by
  obtain ⟨P, hP⟩ := exists_homogeneous_hilbert_numerator σ I hI
  refine ⟨Polynomial.hilbertPoly (P.map (Int.castRingHom ℚ)) (Fintype.card σ),
    (P.map (Int.castRingHom ℚ)).natDegree, ?_⟩
  intro n hn
  rw [← coeff_rationalSectionHilbertSeries, rational_hilbert_numerator I P hP]
  exact Polynomial.coeff_mul_invOneSubPow_eq_hilbertPoly_eval _ hn

end PiExponentJets.W64

end OAI
end Source0185

-- Source: OAI/NumberTheory/PiExponent/LocalAlgebra/PrimeDegreeExistence.lean
section Source0186
-- Modified in this edition: unused plain lemmas removed; see reduction.json.
/-
Modification notice for the LogTwo project.
Derived from openai/math (Apache-2.0), revision adc7f1241b42e322a6451854ab7e4b4c146bf78a.
Original source: lean/OAI/NumberTheory/PiExponent/LocalAlgebra/PrimeDegreeExistence.lean
Changes: Convert module/import declarations to the Lean 4.34 public module format.
See ../THIRD_PARTY_NOTICES.txt for provenance and the recorded changes.
-/

namespace OAI

namespace PiExponentJets.W27
open PiExponentJets.W64
attribute [local instance] MvPolynomial.gradedAlgebra

variable {k σ : Type*} [Field k] [Fintype σ]

omit [Fintype σ] in
theorem quotient_eventual_hilbert_coefficient_nonneg
    (I : Ideal (MvPolynomial σ k)) (p : Polynomial ℚ) (N d : ℕ)
    (hp : ∀ n : ℕ, N ≤ n → p.eval (n : ℚ) =
      (Module.finrank k (quotientSection I n) : ℚ))
    (hd : p.natDegree ≤ d) : 0 ≤ p.coeff d * (d.factorial : ℚ) := by
  have hl : 0 ≤ p.leadingCoeff :=
    polynomial_leadingCoeff_nonneg_of_eventually_nonneg p N (by
      intro n hn
      rw [hp n hn]
      positivity)
  rcases eq_or_lt_of_le hd with heq | hlt
  · rw [← heq, ← Polynomial.leadingCoeff]
    exact mul_nonneg hl (by positivity)
  · rw [Polynomial.coeff_eq_zero_of_natDegree_lt hlt, zero_mul]

end PiExponentJets.W27

end OAI
end Source0186

-- Source: OAI/NumberTheory/PiExponent/Polynomials/ColonHilbertPolynomial.lean
section Source0187
-- Modified in this edition: unused plain lemmas removed; see reduction.json.
/-
Modification notice for the LogTwo project.
Derived from openai/math (Apache-2.0), revision adc7f1241b42e322a6451854ab7e4b4c146bf78a.
Original source: lean/OAI/NumberTheory/PiExponent/Polynomials/ColonHilbertPolynomial.lean
Changes: Convert module/import declarations to the Lean 4.34 public module format.
See ../THIRD_PARTY_NOTICES.txt for provenance and the recorded changes.
-/

namespace OAI

namespace PiExponentJets.W64

attribute [local instance] MvPolynomial.gradedAlgebra
variable {k σ : Type*} [Field k] [Finite σ]

noncomputable def shiftHilbertPolynomial (p : Polynomial ℚ) (d : ℕ) : Polynomial ℚ :=
  p.comp (Polynomial.X - Polynomial.C (d : ℚ))

@[simp] theorem shiftHilbertPolynomial_eval (p : Polynomial ℚ) (d n : ℕ)
    (hdn : d ≤ n) :
    (shiftHilbertPolynomial p d).eval (n : ℚ) = p.eval ((n-d : ℕ) : ℚ) := by
  simp [shiftHilbertPolynomial, Polynomial.eval_comp, Nat.cast_sub hdn]

@[simp] theorem shiftHilbertPolynomial_natDegree (p : Polynomial ℚ) (d : ℕ) :
    (shiftHilbertPolynomial p d).natDegree = p.natDegree := by
  rw [shiftHilbertPolynomial, Polynomial.natDegree_comp,
    Polynomial.natDegree_X_sub_C, mul_one]

@[simp] theorem shiftHilbertPolynomial_leadingCoeff (p : Polynomial ℚ) (d : ℕ) :
    (shiftHilbertPolynomial p d).leadingCoeff = p.leadingCoeff := by
  rw [shiftHilbertPolynomial, Polynomial.leadingCoeff_comp]
  · rw [Polynomial.leadingCoeff_X_sub_C, one_pow, mul_one]
  · rw [Polynomial.natDegree_X_sub_C]
    exact one_ne_zero

theorem shiftHilbertPolynomial_top_coeff (p : Polynomial ℚ) (d t : ℕ)
    (hp : p.natDegree ≤ t) :
    (shiftHilbertPolynomial p d).coeff t = p.coeff t := by
  by_cases he : p.natDegree = t
  · rw [← he]
    calc
      (shiftHilbertPolynomial p d).coeff p.natDegree =
          (shiftHilbertPolynomial p d).coeff (shiftHilbertPolynomial p d).natDegree := by
            rw [shiftHilbertPolynomial_natDegree]
      _ = (shiftHilbertPolynomial p d).leadingCoeff := Polynomial.coeff_natDegree
      _ = p.leadingCoeff := shiftHilbertPolynomial_leadingCoeff p d
      _ = p.coeff p.natDegree := Polynomial.coeff_natDegree.symm
  · have ht : p.natDegree < t := lt_of_le_of_ne hp he
    rw [Polynomial.coeff_eq_zero_of_natDegree_lt
      (by simpa using ht : (shiftHilbertPolynomial p d).natDegree < t),
      Polynomial.coeff_eq_zero_of_natDegree_lt ht]

theorem colon_hilbert_polynomial_eventually
    (I : Ideal (MvPolynomial σ k))
    (hI : I.IsHomogeneous (MvPolynomial.homogeneousSubmodule σ k))
    {d : ℕ} (f : MvPolynomial σ k) (hf : f.IsHomogeneous d)
    (pJ pP : Polynomial ℚ) (NJ NP : ℕ)
    (hJ : ∀ n : ℕ, NJ < n →
      (Module.finrank k (quotientSection (Ideal.span {f} ⊔ I) n) : ℚ) = pJ.eval (n : ℚ))
    (hP : ∀ n : ℕ, NP < n →
      (Module.finrank k (quotientSection (I.colon {f}) n) : ℚ) = pP.eval (n : ℚ)) :
    ∀ n : ℕ, NJ + NP + d < n →
      (Module.finrank k (quotientSection I n) : ℚ) =
        (pJ + shiftHilbertPolynomial pP d).eval (n : ℚ) := by
  intro n hn
  have hdn : d ≤ n := by omega
  have hnJ : NJ < n := by omega
  have hnP : NP < n-d := by omega
  have h := colon_hilbert_step I hI f hf (n-d)
  rw [Nat.sub_add_cancel hdn] at h
  have hc : (Module.finrank k (quotientSection I n) : ℚ) =
      (Module.finrank k (quotientSection (Ideal.span {f} ⊔ I) n) : ℚ) +
      (Module.finrank k (quotientSection (I.colon {f}) (n-d)) : ℚ) := by
    exact_mod_cast h.symm
  rw [hc, hJ n hnJ, hP (n-d) hnP,
    Polynomial.eval_add, shiftHilbertPolynomial_eval pP d n hdn]

end PiExponentJets.W64

end OAI
end Source0187

-- Source: OAI/NumberTheory/PiExponent/Polynomials/HilbertPolynomial.lean
section Source0188
/-
Modification notice for the LogTwo project.
Derived from openai/math (Apache-2.0), revision adc7f1241b42e322a6451854ab7e4b4c146bf78a.
Original source: lean/OAI/NumberTheory/PiExponent/Polynomials/HilbertPolynomial.lean
Changes: Convert module/import declarations to the Lean 4.34 public module format.
See ../THIRD_PARTY_NOTICES.txt for provenance and the recorded changes.
-/

namespace OAI

namespace PiExponentJets.W22

open PiExponentJets.W64
attribute [local instance] MvPolynomial.gradedAlgebra

variable {k σ : Type*} [Field k] [Fintype σ]

theorem polynomial_eq_of_nat_tail (p q : Polynomial ℚ) (N : ℕ)
    (h : ∀ n : ℕ, N < n → p.eval (n : ℚ) = q.eval (n : ℚ)) : p = q := by
  have hinj : Function.Injective (fun n : ℕ => ((N + 1 + n : ℕ) : ℚ)) := by
    intro a b hab
    change ((N + 1 + a : ℕ) : ℚ) = ((N + 1 + b : ℕ) : ℚ) at hab
    have hab' : N + 1 + a = N + 1 + b := by exact_mod_cast hab
    omega
  apply Polynomial.eq_of_infinite_eval_eq
  apply (Set.infinite_range_of_injective hinj).mono
  rintro x ⟨n, rfl⟩
  exact h _ (by omega)

noncomputable def actualHP (I : Ideal (MvPolynomial σ k))
    (hI : I.IsHomogeneous (MvPolynomial.homogeneousSubmodule σ k)) : Polynomial ℚ :=
  (exists_homogeneous_hilbert_polynomial σ I hI).choose

theorem actualHP_eventually (I : Ideal (MvPolynomial σ k))
    (hI : I.IsHomogeneous (MvPolynomial.homogeneousSubmodule σ k)) :
    ∃ N : ℕ, ∀ n : ℕ, N < n →
      (Module.finrank k (quotientSection I n) : ℚ) = (actualHP I hI).eval (n : ℚ) :=
  (exists_homogeneous_hilbert_polynomial σ I hI).choose_spec

theorem actualHP_unique (I : Ideal (MvPolynomial σ k))
    (hI : I.IsHomogeneous (MvPolynomial.homogeneousSubmodule σ k))
    (p : Polynomial ℚ) (N : ℕ)
    (hp : ∀ n : ℕ, N < n →
      (Module.finrank k (quotientSection I n) : ℚ) = p.eval (n : ℚ)) :
    actualHP I hI = p := by
  obtain ⟨M, hM⟩ := actualHP_eventually I hI
  apply polynomial_eq_of_nat_tail _ _ (M + N)
  intro n hn
  exact (hM n (by omega)).symm.trans (hp n (by omega))

theorem actualHP_congr {I J : Ideal (MvPolynomial σ k)}
    (hI : I.IsHomogeneous (MvPolynomial.homogeneousSubmodule σ k))
    (hJ : J.IsHomogeneous (MvPolynomial.homogeneousSubmodule σ k)) (h : I = J) :
    actualHP I hI = actualHP J hJ := by
  subst J
  rfl

theorem actualHP_top
    (h : (⊤ : Ideal (MvPolynomial σ k)).IsHomogeneous
      (MvPolynomial.homogeneousSubmodule σ k)) : actualHP ⊤ h = 0 := by
  apply actualHP_unique _ h 0 0
  intro n _
  have hz : Module.finrank k (quotientSection (⊤ : Ideal (MvPolynomial σ k)) n) = 0 :=
    Module.finrank_eq_zero_of_subsingleton k _
  simp only [hz, Nat.cast_zero, Polynomial.eval_zero]

theorem actualHP_leadingCoeff_nonneg (I : Ideal (MvPolynomial σ k))
    (hI : I.IsHomogeneous (MvPolynomial.homogeneousSubmodule σ k)) :
    0 ≤ (actualHP I hI).leadingCoeff := by
  obtain ⟨N, hN⟩ := actualHP_eventually I hI
  apply W27.polynomial_leadingCoeff_nonneg_of_eventually_nonneg _ (N + 1)
  intro n hn
  rw [← hN n (by omega)]
  positivity

theorem actualHP_natDegree_antitone {I J : Ideal (MvPolynomial σ k)}
    (hI : I.IsHomogeneous (MvPolynomial.homogeneousSubmodule σ k))
    (hJ : J.IsHomogeneous (MvPolynomial.homogeneousSubmodule σ k)) (hIJ : I ≤ J) :
    (actualHP J hJ).natDegree ≤ (actualHP I hI).natDegree := by
  by_cases hz : actualHP J hJ = 0
  · simp only [hz, Polynomial.natDegree_zero, Nat.zero_le]
  have hpos : 0 < (actualHP J hJ).leadingCoeff :=
    lt_of_le_of_ne (actualHP_leadingCoeff_nonneg J hJ)
      (Ne.symm (Polynomial.leadingCoeff_ne_zero.mpr hz))
  obtain ⟨NI, hNI⟩ := actualHP_eventually I hI
  obtain ⟨NJ, hNJ⟩ := actualHP_eventually J hJ
  apply W24.natDegree_le_of_eventual_polynomial_le _ _ hpos (NI + NJ + 1)
  intro n hn
  rw [← hNI n (by omega), ← hNJ n (by omega)]
  have hdim := (quotientSectionFactor I J hIJ n).finrank_range_le
  rw [LinearMap.range_eq_top.mpr (quotientSectionFactor_surjective I J hIJ n),
    finrank_top] at hdim
  exact_mod_cast hdim

theorem actualHP_colon_step (I : Ideal (MvPolynomial σ k))
    (hI : I.IsHomogeneous (MvPolynomial.homogeneousSubmodule σ k))
    {d : ℕ} (f : MvPolynomial σ k) (hf : f.IsHomogeneous d)
    (hJ : (Ideal.span {f} ⊔ I).IsHomogeneous (MvPolynomial.homogeneousSubmodule σ k))
    (hP : (I.colon {f}).IsHomogeneous (MvPolynomial.homogeneousSubmodule σ k)) :
    actualHP I hI = actualHP (Ideal.span {f} ⊔ I) hJ +
      shiftHilbertPolynomial (actualHP (I.colon {f}) hP) d := by
  obtain ⟨NJ, hNJ⟩ := actualHP_eventually (Ideal.span {f} ⊔ I) hJ
  obtain ⟨NP, hNP⟩ := actualHP_eventually (I.colon {f}) hP
  apply actualHP_unique I hI _ (NJ + NP + d)
  exact colon_hilbert_polynomial_eventually I hI f hf _ _ NJ NP hNJ hNP

end PiExponentJets.W22

end OAI
end Source0188

-- Source: OAI/NumberTheory/PiExponent/LocalAlgebra/HilbertMultiplicityFiltration.lean
section Source0189
/-
Modification notice for the LogTwo project.
Derived from openai/math (Apache-2.0), revision adc7f1241b42e322a6451854ab7e4b4c146bf78a.
Original source: lean/OAI/NumberTheory/PiExponent/LocalAlgebra/HilbertMultiplicityFiltration.lean
Changes: Convert module/import declarations to the Lean 4.34 public module format.
See ../THIRD_PARTY_NOTICES.txt for provenance and the recorded changes.
-/

namespace OAI

namespace PiExponentJets.W22

open PiExponentJets.W64
open scoped BigOperators
attribute [local instance] MvPolynomial.gradedAlgebra

variable {k σ : Type*} [Field k] [Fintype σ]

noncomputable def actualMultiplicity (I : Ideal (MvPolynomial σ k))
    (hI : I.IsHomogeneous (MvPolynomial.homogeneousSubmodule σ k)) (d : ℕ) : ℚ :=
  (actualHP I hI).coeff d * (d.factorial : ℚ)

theorem actualMultiplicity_congr {I J : Ideal (MvPolynomial σ k)}
    (hI : I.IsHomogeneous (MvPolynomial.homogeneousSubmodule σ k))
    (hJ : J.IsHomogeneous (MvPolynomial.homogeneousSubmodule σ k)) (h : I = J) (d : ℕ) :
    actualMultiplicity I hI d = actualMultiplicity J hJ d := by
  unfold actualMultiplicity
  rw [actualHP_congr hI hJ h]

theorem actualMultiplicity_nonneg (I : Ideal (MvPolynomial σ k))
    (hI : I.IsHomogeneous (MvPolynomial.homogeneousSubmodule σ k)) (d : ℕ)
    (hd : (actualHP I hI).natDegree ≤ d) : 0 ≤ actualMultiplicity I hI d := by
  obtain ⟨N, hN⟩ := actualHP_eventually I hI
  exact W27.quotient_eventual_hilbert_coefficient_nonneg I (actualHP I hI) (N+1) d
    (fun n hn => (hN n (by omega)).symm) hd

theorem actualMultiplicity_top
    (h : (⊤ : Ideal (MvPolynomial σ k)).IsHomogeneous
      (MvPolynomial.homogeneousSubmodule σ k)) (d : ℕ) :
    actualMultiplicity ⊤ h d = 0 := by
  simp only [actualMultiplicity, actualHP_top h, Polynomial.coeff_zero, zero_mul]

theorem actualMultiplicity_cyclic_step
    (I J : Ideal (MvPolynomial σ k))
    (hI : I.IsHomogeneous (MvPolynomial.homogeneousSubmodule σ k))
    (hJ : J.IsHomogeneous (MvPolynomial.homogeneousSubmodule σ k))
    {s : ℕ} (f : MvPolynomial σ k) (hf : f.IsHomogeneous s)
    (hstep : J = I ⊔ Ideal.span {f})
    (hP : (I.colon {f}).IsHomogeneous (MvPolynomial.homogeneousSubmodule σ k))
    (d : ℕ) (hd : (actualHP (I.colon {f}) hP).natDegree ≤ d) :
    actualMultiplicity I hI d =
      actualMultiplicity J hJ d + actualMultiplicity (I.colon {f}) hP d := by
  have hJs : (Ideal.span {f} ⊔ I).IsHomogeneous
      (MvPolynomial.homogeneousSubmodule σ k) := by
    simpa only [hstep, sup_comm] using hJ
  have heq : Ideal.span {f} ⊔ I = J := (sup_comm _ _).trans hstep.symm
  unfold actualMultiplicity
  rw [actualHP_colon_step I hI f hf hJs hP, Polynomial.coeff_add,
    shiftHilbertPolynomial_top_coeff _ _ d hd, add_mul,
    actualHP_congr hJs hJ heq]

theorem rational_filtration_telescope (U V : ℕ → ℚ) :
    ∀ n : ℕ, (∀ i < n, U i = U (i+1) + V i) →
      U 0 = (∑ i ∈ Finset.range n, V i) + U n := by
  intro n
  induction n with
  | zero => intro _; simp
  | succ n ih =>
    intro hs
    have hprev := ih (fun i hi => hs i (Nat.lt_succ_of_lt hi))
    rw [hprev, hs n (Nat.lt_succ_self n), Finset.sum_range_succ]
    ring

end PiExponentJets.W22

end OAI
end Source0189

-- Source: OAI/NumberTheory/PiExponent/LocalAlgebra/FiltrationLength.lean
section Source0190
-- Modified in this edition: unused plain lemmas removed; see reduction.json.
/-
Modification notice for the LogTwo project.
Derived from openai/math (Apache-2.0), revision adc7f1241b42e322a6451854ab7e4b4c146bf78a.
Original source: lean/OAI/NumberTheory/PiExponent/LocalAlgebra/FiltrationLength.lean
Changes: Convert module/import declarations to the Lean 4.34 public module format.
See ../THIRD_PARTY_NOTICES.txt for provenance and the recorded changes.
-/

namespace OAI

namespace PiExponentJets.W22

open scoped BigOperators

variable {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]

end PiExponentJets.W22

end OAI
end Source0190

-- Source: OAI/NumberTheory/PiExponent/LocalAlgebra/LocalComponentDegree.lean
section Source0191
-- Modified in this edition: unused plain lemmas removed; see reduction.json.
/-
Modification notice for the LogTwo project.
Derived from openai/math (Apache-2.0), revision adc7f1241b42e322a6451854ab7e4b4c146bf78a.
Original source: lean/OAI/NumberTheory/PiExponent/LocalAlgebra/LocalComponentDegree.lean
Changes: Convert module/import declarations to the Lean 4.34 public module format.
See ../THIRD_PARTY_NOTICES.txt for provenance and the recorded changes.
-/

namespace OAI

namespace PiExponentJets.W22

open scoped Classical BigOperators

variable {R : Type*} [CommRing R]

theorem map_ideal_eq_top_of_not_le
    (P Q : Ideal R) [Q.IsPrime] (hPQ : ¬ P ≤ Q) :
    P.map (algebraMap R (Localization.AtPrime Q)) = ⊤ := by
  obtain ⟨x, hxP, hxQ⟩ := IsConcreteLE.not_le_iff_exists.mp hPQ
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

end PiExponentJets.W22

end OAI
end Source0191

-- Source: OAI/NumberTheory/PiExponent/LocalAlgebra/LocalizedCyclicFactor.lean
section Source0192
/-
Modification notice for the LogTwo project.
Derived from openai/math (Apache-2.0), revision adc7f1241b42e322a6451854ab7e4b4c146bf78a.
Original source: lean/OAI/NumberTheory/PiExponent/LocalAlgebra/LocalizedCyclicFactor.lean
Changes: Convert module/import declarations to the Lean 4.34 public module format.
See ../THIRD_PARTY_NOTICES.txt for provenance and the recorded changes.
-/

namespace OAI

namespace PiExponentJets.W22

variable {R : Type*} [CommRing R]

theorem map_colon_singleton_localization
    (S : Submonoid R) (L : Type*) [CommRing L] [Algebra R L] [IsLocalization S L]
    (I : Ideal R) (f : R) :
    (I.colon {f}).map (algebraMap R L) =
      (I.map (algebraMap R L)).colon {algebraMap R L f} := by
  apply (IsLocalization.orderEmbedding S L).injective
  ext a
  change algebraMap R L a ∈ (I.colon {f}).map (algebraMap R L) ↔
    algebraMap R L a ∈ (I.map (algebraMap R L)).colon {algebraMap R L f}
  simp only [Submodule.mem_colon_singleton, smul_eq_mul, ← map_mul,
    IsLocalization.algebraMap_mem_map_algebraMap_iff S L, mul_assoc]

noncomputable def localizedCyclicFactorEquiv
    (S : Submonoid R) (L : Type*) [CommRing L] [Algebra R L] [IsLocalization S L]
    (I : Ideal R) (f : R) :
    (L ⧸ (I.colon {f}).map (algebraMap R L)) ≃ₗ[L]
      (((I ⊔ Ideal.span {f}).map (algebraMap R L)) ⧸
        (I.map (algebraMap R L)).submoduleOf
          ((I ⊔ Ideal.span {f}).map (algebraMap R L))) := by
  rw [map_colon_singleton_localization S L, Ideal.map_sup,
    Ideal.map_span, Set.image_singleton]
  exact cyclicFactorEquiv (I.map (algebraMap R L)) (algebraMap R L f)

noncomputable def primeLocalizedCyclicFactorEquiv
    (Q : Ideal R) [Q.IsPrime] (I : Ideal R) (f : R) :
    (Localization.AtPrime Q ⧸ (I.colon {f}).map
      (algebraMap R (Localization.AtPrime Q))) ≃ₗ[Localization.AtPrime Q]
      (((I ⊔ Ideal.span {f}).map (algebraMap R (Localization.AtPrime Q))) ⧸
        (I.map (algebraMap R (Localization.AtPrime Q))).submoduleOf
          ((I ⊔ Ideal.span {f}).map (algebraMap R (Localization.AtPrime Q)))) :=
  localizedCyclicFactorEquiv Q.primeCompl (Localization.AtPrime Q) I f

end PiExponentJets.W22

end OAI
end Source0192

-- Source: OAI/NumberTheory/PiExponent/LocalAlgebra/LocalizedFiltrationLength.lean
section Source0193
/-
Modification notice for the LogTwo project.
Derived from openai/math (Apache-2.0), revision adc7f1241b42e322a6451854ab7e4b4c146bf78a.
Original source: lean/OAI/NumberTheory/PiExponent/LocalAlgebra/LocalizedFiltrationLength.lean
Changes: Convert module/import declarations to the Lean 4.34 public module format.
See ../THIRD_PARTY_NOTICES.txt for provenance and the recorded changes.
-/

namespace OAI

namespace PiExponentJets.W22

open scoped BigOperators Classical

variable {R : Type*} [CommRing R]

theorem localized_cyclic_filtration_length
    (I Q : Ideal R) [Q.IsPrime] (hQ : Q ∈ I.minimalPrimes)
    (J : ℕ → Ideal R) (hmono : ∀ i, J i ≤ J (i + 1))
    (hstart : J 0 = I) (n : ℕ) (hend : J n = ⊤)
    (f : ℕ → R)
    (hstep : ∀ i < n, J (i + 1) = J i ⊔ Ideal.span {f i})
    (hprime : ∀ i < n, ((J i).colon {f i}).IsPrime) :
    Module.length (Localization.AtPrime Q)
      (Localization.AtPrime Q ⧸ I.map (algebraMap R (Localization.AtPrime Q))) =
      ∑ i ∈ Finset.range n, if (J i).colon {f i} = Q then 1 else 0 := by
  let L := Localization.AtPrime Q
  let N : ℕ → Ideal L := fun i => (J i).map (algebraMap R L)
  have hNmono : ∀ i, N i ≤ N (i + 1) := fun i => Ideal.map_mono (hmono i)
  have hNtop : N n = ⊤ := by simp only [N, hend, Ideal.map_top]
  have hstartlen := congrArg
    (fun A : Ideal R => Module.length L (L ⧸ A.map (algebraMap R L))) hstart
  have hlen := quotient_length_eq_sum_of_last_top N hNmono n hNtop
  have hbase : I ≤ J 0 := hstart.symm.le
  have hIle : ∀ i, I ≤ J i := fun i =>
    hbase.trans ((monotone_nat_of_le_succ hmono) (Nat.zero_le i))
  calc
    _ = Module.length L (L ⧸ N 0) := hstartlen.symm
    _ = ∑ i ∈ Finset.range n,
        Module.length L (N (i + 1) ⧸ (N i).submoduleOf (N (i + 1))) := hlen
    _ = _ := by
      apply Finset.sum_congr rfl
      intro i hi
      have hin : i < n := Finset.mem_range.mp hi
      let := hprime i hin
      have hIP : I ≤ (J i).colon {f i} := by
        intro a ha
        apply Submodule.mem_colon_singleton.mpr
        exact (J i).mul_mem_right (f i) (hIle i ha)
      have heq : Module.length L (N (i + 1) ⧸ (N i).submoduleOf (N (i + 1))) =
          Module.length L (L ⧸ ((J i).colon {f i}).map (algebraMap R L)) := by
        have htransport := congrArg
          (fun K : Ideal R => Module.length L
            (↥(K.map (algebraMap R L)) ⧸
              ((J i).map (algebraMap R L)).submoduleOf (K.map (algebraMap R L))))
          (hstep i hin)
        exact htransport.trans
          (primeLocalizedCyclicFactorEquiv Q (J i) (f i)).symm.length_eq
      rw [heq]
      exact localized_prime_factor_length I ((J i).colon {f i}) Q hQ hIP

end PiExponentJets.W22

end OAI
end Source0193

-- Source: OAI/NumberTheory/PiExponent/Polynomials/HomogeneousPrimeFiltration.lean
section Source0194
-- Modified in this edition: unused plain lemmas removed; see reduction.json.
/-
Modification notice for the LogTwo project.
Derived from openai/math (Apache-2.0), revision adc7f1241b42e322a6451854ab7e4b4c146bf78a.
Original source: lean/OAI/NumberTheory/PiExponent/Polynomials/HomogeneousPrimeFiltration.lean
Changes: Convert module/import declarations to the Lean 4.34 public module format.
See ../THIRD_PARTY_NOTICES.txt for provenance and the recorded changes.
-/

namespace OAI

namespace PiExponentJets.W22

attribute [local instance] MvPolynomial.gradedAlgebra

variable {k σ : Type*} [Field k]

def HomogeneousPrimeStep (I J : Ideal (MvPolynomial σ k)) : Prop :=
  I.IsHomogeneous (MvPolynomial.homogeneousSubmodule σ k) ∧
    ∃ (d : ℕ) (f : MvPolynomial σ k), f.IsHomogeneous d ∧ f ∉ I ∧
      (I.colon {f}).IsPrime ∧ J = I ⊔ Ideal.span {f}

theorem HomogeneousPrimeStep.homogeneous {I J : Ideal (MvPolynomial σ k)}
    (h : HomogeneousPrimeStep I J) :
    J.IsHomogeneous (MvPolynomial.homogeneousSubmodule σ k) := by
  obtain ⟨hI, d, f, hf, _, _, rfl⟩ := h
  apply hI.sup
  apply Ideal.homogeneous_span (MvPolynomial.homogeneousSubmodule σ k)
  intro x hx
  obtain rfl := Set.mem_singleton_iff.mp hx
  exact ⟨d, hf⟩

theorem HomogeneousPrimeStep.lt {I J : Ideal (MvPolynomial σ k)}
    (h : HomogeneousPrimeStep I J) : I < J := by
  obtain ⟨_, d, f, _, hfI, _, rfl⟩ := h
  refine lt_of_le_of_ne le_sup_left ?_
  intro heq
  have hm : f ∈ I ⊔ Ideal.span {f} :=
    (show Ideal.span {f} ≤ I ⊔ Ideal.span {f} from le_sup_right)
      (Ideal.subset_span (by simp))
  exact hfI (by simpa only [← heq] using hm)

variable [Finite σ]

theorem exists_homogeneous_prime_filtration
    (I : Ideal (MvPolynomial σ k))
    (hI : I.IsHomogeneous (MvPolynomial.homogeneousSubmodule σ k)) :
    ∃ s : RelSeries {(A, B) | HomogeneousPrimeStep (k := k) (σ := σ) A B},
      s.head = I ∧ s.last = ⊤ := by
  let r : Set (Ideal (MvPolynomial σ k) × Ideal (MvPolynomial σ k)) :=
    {(A, B) | HomogeneousPrimeStep A B}
  have ht : (⊤ : Ideal (MvPolynomial σ k)).IsHomogeneous
      (MvPolynomial.homogeneousSubmodule σ k) ∧
      ∃ s : RelSeries r, s.head = I ∧ s.last = ⊤ := by
    refine WellFoundedGT.induction_top
      ⟨I, hI, RelSeries.singleton r I, rfl, rfl⟩ ?_
    rintro J hJtop ⟨hJ, s, hshead, hslast⟩
    obtain ⟨d, f, hf, hfJ, hp⟩ := exists_homogeneous_prime_colon J hJ hJtop
    have hstep : HomogeneousPrimeStep J (J ⊔ Ideal.span {f}) :=
      ⟨hJ, d, f, hf, hfJ, hp, rfl⟩
    refine ⟨J ⊔ Ideal.span {f}, hstep.lt, hstep.homogeneous,
      s.snoc (J ⊔ Ideal.span {f}) (by
        change HomogeneousPrimeStep s.last (J ⊔ Ideal.span {f})
        simpa only [hslast] using hstep), ?_, by simp only [RelSeries.last_snoc]⟩
    simpa using hshead
  exact ht.2

end PiExponentJets.W22

end OAI
end Source0194

-- Source: OAI/NumberTheory/PiExponent/Polynomials/HomogeneousComponentLength.lean
section Source0195
/-
Modification notice for the LogTwo project.
Derived from openai/math (Apache-2.0), revision adc7f1241b42e322a6451854ab7e4b4c146bf78a.
Original source: lean/OAI/NumberTheory/PiExponent/Polynomials/HomogeneousComponentLength.lean
Changes: Convert module/import declarations to the Lean 4.34 public module format.
See ../THIRD_PARTY_NOTICES.txt for provenance and the recorded changes.
-/

namespace OAI

namespace PiExponentJets.W22

open scoped BigOperators Classical
attribute [local instance] MvPolynomial.gradedAlgebra

variable {k σ : Type*} [Field k] [Finite σ]

theorem exists_homogeneous_cyclic_filtration_nat
    (I : Ideal (MvPolynomial σ k))
    (hI : I.IsHomogeneous (MvPolynomial.homogeneousSubmodule σ k)) :
    ∃ (n : ℕ) (J : ℕ → Ideal (MvPolynomial σ k))
      (f : ℕ → MvPolynomial σ k) (d : ℕ → ℕ),
      (∀ i, J i ≤ J (i + 1)) ∧ J 0 = I ∧ J n = ⊤ ∧
      ∀ i < n, (J i).IsHomogeneous (MvPolynomial.homogeneousSubmodule σ k) ∧
        (f i).IsHomogeneous (d i) ∧ f i ∉ J i ∧
        ((J i).colon {f i}).IsPrime ∧ J (i + 1) = J i ⊔ Ideal.span {f i} := by
  classical
  obtain ⟨s, hshead, hslast⟩ := exists_homogeneous_prime_filtration I hI
  have hsmono : Monotone s :=
    (Fin.strictMono_iff_lt_succ.mpr fun i => (s.step i).lt).monotone
  let J : ℕ → Ideal (MvPolynomial σ k) := fun i =>
    s ⟨min i s.length, Nat.lt_succ_of_le (min_le_right _ _)⟩
  have hd : ∀ i : Fin s.length, ∃ (d : ℕ) (f : MvPolynomial σ k),
      f.IsHomogeneous d ∧ f ∉ s i.castSucc ∧
        ((s i.castSucc).colon {f}).IsPrime ∧
        s i.succ = s i.castSucc ⊔ Ideal.span {f} := fun i => (s.step i).2
  let degrees : Fin s.length → ℕ := fun i => (hd i).choose
  let generators : Fin s.length → MvPolynomial σ k := fun i => (hd i).choose_spec.choose
  let f : ℕ → MvPolynomial σ k := fun i =>
    if hi : i < s.length then generators ⟨i, hi⟩ else 0
  let d : ℕ → ℕ := fun i => if hi : i < s.length then degrees ⟨i, hi⟩ else 0
  refine ⟨s.length, J, f, d, ?_, ?_, ?_, ?_⟩
  · intro i
    apply hsmono
    exact min_le_min_right s.length (Nat.le_succ i)
  · change s.head = I
    exact hshead
  · simpa only [J, min_self, RelSeries.last, Fin.last] using hslast
  · intro i hi
    have hfi := (hd ⟨i, hi⟩).choose_spec.choose_spec
    have hleft : J i = s (Fin.castSucc ⟨i, hi⟩) := by
      apply congrArg s
      apply Fin.ext
      exact min_eq_left (Nat.le_of_lt hi)
    have hright : J (i + 1) = s (Fin.succ ⟨i, hi⟩) := by
      apply congrArg s
      apply Fin.ext
      exact min_eq_left (Nat.succ_le_of_lt hi)
    simpa only [f, d, dite_eq_left hi, degrees, generators, hleft, hright] using
      And.intro (s.step ⟨i, hi⟩).1 hfi

theorem exists_homogeneous_component_length_count
    (I Q : Ideal (MvPolynomial σ k)) [Q.IsPrime]
    (hI : I.IsHomogeneous (MvPolynomial.homogeneousSubmodule σ k))
    (hQ : Q ∈ I.minimalPrimes) :
    ∃ (n : ℕ) (J : ℕ → Ideal (MvPolynomial σ k))
      (f : ℕ → MvPolynomial σ k) (d : ℕ → ℕ),
      (∀ i, J i ≤ J (i + 1)) ∧ J 0 = I ∧ J n = ⊤ ∧
      (∀ i < n, (J i).IsHomogeneous (MvPolynomial.homogeneousSubmodule σ k) ∧
        (f i).IsHomogeneous (d i) ∧ f i ∉ J i ∧
        ((J i).colon {f i}).IsPrime ∧ J (i + 1) = J i ⊔ Ideal.span {f i}) ∧
      Module.length (Localization.AtPrime Q)
        (Localization.AtPrime Q ⧸ I.map
          (algebraMap (MvPolynomial σ k) (Localization.AtPrime Q))) =
        ∑ i ∈ Finset.range n, if (J i).colon {f i} = Q then 1 else 0 := by
  obtain ⟨n, J, f, d, hmono, hstart, hend, hstep⟩ :=
    exists_homogeneous_cyclic_filtration_nat I hI
  refine ⟨n, J, f, d, hmono, hstart, hend, hstep, ?_⟩
  exact localized_cyclic_filtration_length I Q hQ J hmono hstart n hend f
    (fun i hi => (hstep i hi).2.2.2.2) (fun i hi => (hstep i hi).2.2.2.1)

end PiExponentJets.W22

end OAI
end Source0195

-- Source: OAI/NumberTheory/PiExponent/LocalAlgebra/ComponentMultiplicityBound.lean
section Source0196
-- Modified in this edition: unused plain lemmas removed; see reduction.json.
/-
Modification notice for the LogTwo project.
Derived from openai/math (Apache-2.0), revision adc7f1241b42e322a6451854ab7e4b4c146bf78a.
Original source: lean/OAI/NumberTheory/PiExponent/LocalAlgebra/ComponentMultiplicityBound.lean
Changes: Convert module/import declarations to the Lean 4.34 public module format.
See ../THIRD_PARTY_NOTICES.txt for provenance and the recorded changes.
-/

namespace OAI

namespace PiExponentJets.W22

open PiExponentJets.W64
open scoped BigOperators Classical
attribute [local instance] MvPolynomial.gradedAlgebra

variable {k σ : Type*} [Field k] [Fintype σ]

end PiExponentJets.W22

end OAI
end Source0196

-- Source: OAI/NumberTheory/PiExponent/LocalAlgebra/PrimeHilbertDimension.lean
section Source0197
/-
Modification notice for the LogTwo project.
Derived from openai/math (Apache-2.0), revision adc7f1241b42e322a6451854ab7e4b4c146bf78a.
Original source: lean/OAI/NumberTheory/PiExponent/LocalAlgebra/PrimeHilbertDimension.lean
Changes: Convert module/import declarations to the Lean 4.34 public module format.
See ../THIRD_PARTY_NOTICES.txt for provenance and the recorded changes.
-/

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
    obtain ⟨hpq', x, hxq, hxp⟩ := IsConcreteLE.lt_iff_le_and_exists.mp (show p.asIdeal < q.asIdeal from hpq)
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
end Source0197

-- Source: OAI/NumberTheory/PiExponent/Geometry/NormalizationGrowth.lean
section Source0198
-- Modified in this edition: unused plain lemmas removed; see reduction.json.
/-
Modification notice for the LogTwo project.
Derived from openai/math (Apache-2.0), revision adc7f1241b42e322a6451854ab7e4b4c146bf78a.
Original source: lean/OAI/NumberTheory/PiExponent/Geometry/NormalizationGrowth.lean
Changes: Convert module/import declarations to the Lean 4.34 public module format.
See ../THIRD_PARTY_NOTICES.txt for provenance and the recorded changes.
-/

namespace OAI

namespace PiExponentJets.W24

open MvPolynomial

section Substitution

variable {k σ τ : Type*} [CommSemiring k]

theorem totalDegree_aeval_le (F : τ → MvPolynomial σ k) (D : ℕ)
    (hF : ∀ i, (F i).totalDegree ≤ D) (p : MvPolynomial τ k) :
    (aeval F p).totalDegree ≤ p.totalDegree * D := by
  classical
  have hm (d : τ →₀ ℕ) (c : k) :
      (aeval F (monomial d c)).totalDegree ≤ (d.sum fun _ e => e) * D := by
    rw [aeval_monomial, Finsupp.prod]
    calc
      (algebraMap k (MvPolynomial σ k) c *
          ∏ i ∈ d.support, F i ^ d i).totalDegree
          ≤ (∏ i ∈ d.support, F i ^ d i).totalDegree := by
            simpa only [MvPolynomial.algebraMap_eq, totalDegree_C, zero_add] using
              totalDegree_mul (C c) (∏ i ∈ d.support, F i ^ d i)
      _ ≤ ∑ i ∈ d.support, (F i ^ d i).totalDegree := totalDegree_finsetProd _ _
      _ ≤ ∑ i ∈ d.support, d i * D :=
        Finset.sum_le_sum fun i _ =>
          (totalDegree_pow (F i) (d i)).trans (Nat.mul_le_mul_left _ (hF i))
      _ = (d.sum fun _ e => e) * D := by rw [Finsupp.sum, Finset.sum_mul]
  have he : aeval F p = ∑ d ∈ p.support, aeval F (monomial d (p.coeff d)) := by
    conv_lhs => rw [p.as_sum, map_sum]
  rw [he]
  exact totalDegree_finsetSum_le fun d hd =>
    (hm d (p.coeff d)).trans (Nat.mul_le_mul_right D (le_totalDegree hd))

end Substitution

variable {k σ : Type*} [Field k] [Finite σ]

noncomputable def quotientDegreeFiltration (I : Ideal (MvPolynomial σ k)) (n : ℕ) :
    Submodule k (MvPolynomial σ k ⧸ I) :=
  (restrictTotalDegree σ k n).map (Ideal.Quotient.mkₐ k I).toLinearMap

noncomputable instance quotientDegreeFiltration_finite (I : Ideal (MvPolynomial σ k))
    (n : ℕ) : Module.Finite k (quotientDegreeFiltration I n) := by
  unfold quotientDegreeFiltration
  infer_instance

omit [Finite σ] in
theorem normalization_mem_quotientDegreeFiltration {τ : Type*}
    (I : Ideal (MvPolynomial σ k))
    (g : MvPolynomial τ k →ₐ[k] (MvPolynomial σ k ⧸ I))
    (F : τ → MvPolynomial σ k)
    (hF : ∀ i, Ideal.Quotient.mk I (F i) = g (X i))
    (D : ℕ) (hD : ∀ i, (F i).totalDegree ≤ D)
    (n : ℕ) (p : MvPolynomial τ k) (hp : p.totalDegree ≤ n) :
    g p ∈ quotientDegreeFiltration I (n * D) := by
  have he : (Ideal.Quotient.mkₐ k I).comp (aeval F) = g := by
    ext i
    simp only [AlgHom.comp_apply, aeval_X]
    exact hF i
  refine Submodule.mem_map.mpr ⟨aeval F p,
    (mem_restrictTotalDegree σ _ _).mpr
      ((totalDegree_aeval_le F D hD p).trans (Nat.mul_le_mul_right D hp)), ?_⟩
  exact AlgHom.congr_fun he p

end PiExponentJets.W24

end OAI
end Source0198

-- Source: OAI/NumberTheory/PiExponent/Geometry/FiniteNormalizationGrowth.lean
section Source0199
/-
Modification notice for the LogTwo project.
Derived from openai/math (Apache-2.0), revision adc7f1241b42e322a6451854ab7e4b4c146bf78a.
Original source: lean/OAI/NumberTheory/PiExponent/Geometry/FiniteNormalizationGrowth.lean
Changes: Convert module/import declarations to the Lean 4.34 public module format.
See ../THIRD_PARTY_NOTICES.txt for provenance and the recorded changes.
-/

namespace OAI

namespace PiExponentJets.W29

open MvPolynomial Submodule
open scoped BigOperators

section CoefficientPieces

variable {k R τ : Type*} [Field k] [CommRing R] [Algebra k R]
  [Fintype τ] {m : ℕ}

noncomputable def boundedCoefficientMap (g : MvPolynomial τ k →ₐ[k] R)
    (e : Fin m → R) (n : ℕ) :
    (Fin m → restrictTotalDegree τ k n) →ₗ[k] R where
  toFun p := ∑ j, g (p j) * e j
  map_add' p q := by simp [map_add, add_mul, Finset.sum_add_distrib]
  map_smul' c p := by simp [map_smul, Finset.smul_sum]

noncomputable def generatorPiece (g : MvPolynomial τ k →ₐ[k] R)
    (e : Fin m → R) (n : ℕ) : Submodule k R :=
  LinearMap.range (boundedCoefficientMap g e n)

omit [Fintype τ] in
lemma mem_generatorPiece (g : MvPolynomial τ k →ₐ[k] R) (e : Fin m → R)
    (n : ℕ) (r : R) : r ∈ generatorPiece g e n ↔
      ∃ p : Fin m → MvPolynomial τ k,
        (∀ j, (p j).totalDegree ≤ n) ∧ (∑ j, g (p j) * e j) = r := by
  constructor
  · rintro ⟨p, rfl⟩
    exact ⟨fun j => p j, fun j => (mem_restrictTotalDegree τ _ _).mp (p j).property, rfl⟩
  · rintro ⟨p, hp, hpr⟩
    exact ⟨fun j => ⟨p j, (mem_restrictTotalDegree τ _ _).mpr (hp j)⟩, hpr⟩

omit [Fintype τ] in
lemma generatorPiece_mono (g : MvPolynomial τ k →ₐ[k] R) (e : Fin m → R) :
    Monotone (generatorPiece g e) := by
  intro a b hab r hr
  obtain ⟨p, hp, hpr⟩ := (mem_generatorPiece g e a r).mp hr
  exact (mem_generatorPiece g e b r).mpr ⟨p, fun j => (hp j).trans hab, hpr⟩

noncomputable instance generatorPiece_finite (g : MvPolynomial τ k →ₐ[k] R)
    (e : Fin m → R) (n : ℕ) : Module.Finite k (generatorPiece g e n) := by
  unfold generatorPiece
  infer_instance

lemma finrank_generatorPiece_le (g : MvPolynomial τ k →ₐ[k] R)
    (e : Fin m → R) (n : ℕ) :
    Module.finrank k (generatorPiece g e n) ≤
      m * Module.finrank k (restrictTotalDegree τ k n) := by
  calc
    Module.finrank k (generatorPiece g e n) ≤
        Module.finrank k (Fin m → restrictTotalDegree τ k n) :=
      LinearMap.finrank_range_le (boundedCoefficientMap g e n)
    _ = m * Module.finrank k (restrictTotalDegree τ k n) := by
      rw [Module.finrank_pi_fintype]
      simp

omit [Fintype τ] in
lemma mul_mem_generatorPiece (g : MvPolynomial τ k →ₐ[k] R) (e : Fin m → R)
    (x : R) (A : Fin m → Fin m → MvPolynomial τ k) (D : ℕ)
    (hA : ∀ j, x * e j = ∑ l, g (A j l) * e l)
    (hD : ∀ j l, (A j l).totalDegree ≤ D)
    {n : ℕ} {r : R} (hr : r ∈ generatorPiece g e n) :
    x * r ∈ generatorPiece g e (n + D) := by
  classical
  obtain ⟨p, hp, rfl⟩ := (mem_generatorPiece g e n r).mp hr
  apply (mem_generatorPiece g e (n + D) _).mpr
  refine ⟨fun l => ∑ j, p j * A j l, ?_, ?_⟩
  · intro l
    exact totalDegree_finsetSum_le fun j _ =>
      (totalDegree_mul (p j) (A j l)).trans (Nat.add_le_add (hp j) (hD j l))
  · simp only [map_sum, map_mul, Finset.sum_mul]
    rw [Finset.sum_comm]
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j _
    calc
      (∑ l, g (p j) * g (A j l) * e l) =
          g (p j) * (∑ l, g (A j l) * e l) := by
            simp only [Finset.mul_sum, mul_assoc]
      _ = x * (g (p j) * e j) := by rw [← hA j]; ring

end CoefficientPieces

section FiniteMatrices

variable {k R σ τ : Type*} [Field k] [CommRing R] [Algebra k R]
  [Fintype σ]

theorem finite_multiplication_matrices (g : MvPolynomial τ k →ₐ[k] R)
    (hfin : g.Finite) (x : σ → R) :
    ∃ (m D E : ℕ) (e : Fin m → R)
      (A : σ → Fin m → Fin m → MvPolynomial τ k),
      (∀ i j, x i * e j = ∑ l, g (A i j l) * e l) ∧
      (∀ i j l, (A i j l).totalDegree ≤ D) ∧
      (1 : R) ∈ generatorPiece g e E := by
  classical
  let : Algebra (MvPolynomial τ k) R := g.toRingHom.toAlgebra
  let : Module.Finite (MvPolynomial τ k) R := hfin
  obtain ⟨m, e, he⟩ := Module.Finite.exists_fin (R := MvPolynomial τ k) (M := R)
  have hex (r : R) : ∃ p : Fin m → MvPolynomial τ k, ∑ j, g (p j) * e j = r := by
    have hr : r ∈ Submodule.span (MvPolynomial τ k) (Set.range e) := by rw [he]; trivial
    obtain ⟨p, hp⟩ := (Submodule.mem_span_range_iff_exists_fun _).mp hr
    refine ⟨p, ?_⟩
    change (∑ j, g (p j) * e j) = r at hp
    exact hp
  choose A hA using fun i j => hex (x i * e j)
  obtain ⟨p, hp⟩ := hex 1
  let D := Finset.univ.sup fun i => Finset.univ.sup fun j =>
    Finset.univ.sup fun l => (A i j l).totalDegree
  let E := Finset.univ.sup fun j => (p j).totalDegree
  refine ⟨m, D, E, e, A, fun i j => (hA i j).symm, ?_, ?_⟩
  · intro i j l
    calc
      (A i j l).totalDegree
          ≤ Finset.univ.sup (fun l => (A i j l).totalDegree) :=
            Finset.le_sup (f := fun l => (A i j l).totalDegree) (Finset.mem_univ l)
      _ ≤ Finset.univ.sup (fun j => Finset.univ.sup (fun l => (A i j l).totalDegree)) :=
            Finset.le_sup (f := fun j => Finset.univ.sup
              (fun l => (A i j l).totalDegree)) (Finset.mem_univ j)
      _ ≤ D := Finset.le_sup (f := fun i => Finset.univ.sup
          (fun j => Finset.univ.sup (fun l => (A i j l).totalDegree)))
          (Finset.mem_univ i)
  · exact (mem_generatorPiece g e E 1).mpr
      ⟨p, fun j => Finset.le_sup (f := fun j => (p j).totalDegree)
        (Finset.mem_univ j), hp⟩

end FiniteMatrices

section Propagation

variable {k R σ τ : Type*} [Field k] [CommRing R] [Algebra k R]
  {m D E : ℕ}

lemma variable_pow_mem_generatorPiece (g : MvPolynomial τ k →ₐ[k] R)
    (e : Fin m → R) (f : MvPolynomial σ k →ₐ[k] R)
    (A : σ → Fin m → Fin m → MvPolynomial τ k)
    (hA : ∀ i j, f (X i) * e j = ∑ l, g (A i j l) * e l)
    (hD : ∀ i j l, (A i j l).totalDegree ≤ D)
    {n : ℕ} {r : R} (hr : r ∈ generatorPiece g e n) (i : σ) (a : ℕ) :
    r * f (X i) ^ a ∈ generatorPiece g e (n + a * D) := by
  induction a with
  | zero => simpa using hr
  | succ a ih =>
    have h := mul_mem_generatorPiece g e (f (X i)) (A i) D (hA i) (hD i) ih
    have hdeg : n + (a + 1) * D = n + a * D + D := by ring
    rw [hdeg]
    simpa only [pow_succ, mul_assoc, mul_comm, mul_left_comm] using h

lemma monomial_mem_generatorPiece (g : MvPolynomial τ k →ₐ[k] R)
    (e : Fin m → R) (f : MvPolynomial σ k →ₐ[k] R)
    (A : σ → Fin m → Fin m → MvPolynomial τ k)
    (hA : ∀ i j, f (X i) * e j = ∑ l, g (A i j l) * e l)
    (hD : ∀ i j l, (A i j l).totalDegree ≤ D)
    (h1 : (1 : R) ∈ generatorPiece g e E) (a : σ →₀ ℕ) (c : k) :
    f (monomial a c) ∈ generatorPiece g e (E + (a.sum fun _ e => e) * D) := by
  classical
  induction a using Finsupp.induction with
  | zero =>
    have h := (generatorPiece g e E).smul_mem c h1
    simpa only [Finsupp.sum_zero_index, zero_mul, add_zero, ← C_apply,
      ← MvPolynomial.algebraMap_eq, AlgHom.commutes, Algebra.smul_def, mul_one] using h
  | single_add i a b hbi ha ih =>
    have h := variable_pow_mem_generatorPiece g e f A hA hD ih i a
    have hsum : (Finsupp.single i a + b).sum (fun _ e => e) =
        a + b.sum (fun _ e => e) := by
      rw [Finsupp.sum_add_index' (fun _ => rfl) (fun _ _ _ => rfl),
        Finsupp.sum_single_index (by rfl)]
    have hdeg : E + ((Finsupp.single i a + b).sum fun _ e => e) * D =
        E + (b.sum fun _ e => e) * D + a * D := by
      rw [hsum]
      ring
    rw [hdeg, monomial_single_add, map_mul, map_pow]
    simpa only [mul_comm] using h

lemma polynomial_mem_generatorPiece (g : MvPolynomial τ k →ₐ[k] R)
    (e : Fin m → R) (f : MvPolynomial σ k →ₐ[k] R)
    (A : σ → Fin m → Fin m → MvPolynomial τ k)
    (hA : ∀ i j, f (X i) * e j = ∑ l, g (A i j l) * e l)
    (hD : ∀ i j l, (A i j l).totalDegree ≤ D)
    (h1 : (1 : R) ∈ generatorPiece g e E) (p : MvPolynomial σ k) :
    f p ∈ generatorPiece g e (E + p.totalDegree * D) := by
  classical
  have he : f p = ∑ a ∈ p.support, f (monomial a (p.coeff a)) := by
    conv_lhs => rw [p.as_sum, map_sum]
  rw [he]
  apply Submodule.sum_mem
  intro a ha
  exact generatorPiece_mono g e
    (Nat.add_le_add_left (Nat.mul_le_mul_right D (le_totalDegree ha)) E)
    (monomial_mem_generatorPiece g e f A hA hD h1 a (p.coeff a))

end Propagation

variable {k σ τ : Type*} [Field k] [Fintype σ] [Fintype τ]

theorem finite_normalization_upper_growth
    (I : Ideal (MvPolynomial σ k))
    (g : MvPolynomial τ k →ₐ[k] (MvPolynomial σ k ⧸ I)) (hfin : g.Finite) :
    ∃ C E : ℕ, 0 < C ∧ ∀ n : ℕ,
      Module.finrank k (W24.quotientDegreeFiltration I n) ≤
        C * Module.finrank k (restrictTotalDegree τ k (C * n + E)) := by
  classical
  let f := Ideal.Quotient.mkₐ k I
  obtain ⟨m, D, E, e, A, hA, hD, h1⟩ :=
    finite_multiplication_matrices g hfin (fun i : σ => f (X i))
  let C := max (max m D) 1
  have hmC : m ≤ C := (le_max_left m D).trans (le_max_left _ _)
  have hDC : D ≤ C := (le_max_right m D).trans (le_max_left _ _)
  refine ⟨C, E, lt_of_lt_of_le Nat.zero_lt_one (le_max_right _ _), fun n => ?_⟩
  have hle : W24.quotientDegreeFiltration I n ≤ generatorPiece g e (C * n + E) := by
    rintro r ⟨p, hp, rfl⟩
    have hpdeg := (mem_restrictTotalDegree σ n p).mp hp
    apply generatorPiece_mono g e
      (show E + p.totalDegree * D ≤ C * n + E by
        have hmul := Nat.mul_le_mul hpdeg hDC
        simpa only [Nat.mul_comm, Nat.add_comm] using Nat.add_le_add_left hmul E)
    exact polynomial_mem_generatorPiece g e f A hA hD h1 p
  calc
    Module.finrank k (W24.quotientDegreeFiltration I n)
        ≤ Module.finrank k (generatorPiece g e (C * n + E)) :=
          Submodule.finrank_mono hle
    _ ≤ m * Module.finrank k (restrictTotalDegree τ k (C * n + E)) :=
      finrank_generatorPiece_le g e _
    _ ≤ C * Module.finrank k (restrictTotalDegree τ k (C * n + E)) :=
      Nat.mul_le_mul_right _ hmC

end PiExponentJets.W29

end OAI
end Source0199

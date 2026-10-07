/-
Modification notice for the LogTwo project.
Derived from openai/math (Apache-2.0), revision adc7f1241b42e322a6451854ab7e4b4c146bf78a.
Original source: lean/OAI/NumberTheory/PiExponent/LocalAlgebra/HilbertMultiplicityFiltration.lean
Changes: Convert module/import declarations to the Lean 4.34 public module format.
See ../../../../../THIRD_PARTY_NOTICES.txt for provenance and the recorded changes.
-/

module

public import OAI.NumberTheory.PiExponent.Polynomials.HilbertPolynomial

@[expose] public section

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

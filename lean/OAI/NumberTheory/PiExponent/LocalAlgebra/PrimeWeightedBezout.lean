/-
Modification notice for the LogTwo project.
Derived from openai/math (Apache-2.0), revision adc7f1241b42e322a6451854ab7e4b4c146bf78a.
Original source: lean/OAI/NumberTheory/PiExponent/LocalAlgebra/PrimeWeightedBezout.lean
Changes: Convert module/import declarations to the Lean 4.34 public module format.
See ../../../../../THIRD_PARTY_NOTICES.txt for provenance and the recorded changes.
-/

module

public import OAI.NumberTheory.PiExponent.Approximation.CoordinateSliceComparison
public import OAI.NumberTheory.PiExponent.Jets.PrimeNormalCotangent
public import OAI.NumberTheory.PiExponent.LocalAlgebra.WeightedBezoutBound

@[expose] public section

namespace OAI

noncomputable section
namespace PiExponent.PrimeWeightedBezout

open scoped BigOperators
open CoordinateFiniteSlice CoordinateSliceComparison NormalBasisRigidity WeightedSliceDegree

theorem weighted_prime_length_bound {n : ℕ}
    (Q : Ideal (MvPolynomial (Fin n) ℂ)) [Q.IsPrime]
    (A : Finset (Fin n))
    (hA : IsNormalBasis (K := Q.ResidueField)
      (fun i => (polynomialTangent (primeResidueMap Q) Q).mkQ
        (Pi.basisFun Q.ResidueField _ i)) A)
    {J : Type*} (f : J → MvPolynomial (Fin n) ℂ)
    (hQ : Q ∈ (Ideal.span (Set.range f)).minimalPrimes)
    (rho : Fin n → ℚ) (hrho : ∀ i, 0 < rho i)
    (N : ℝ) (hN : 0 ≤ N)
    (hdegree : ∀ j, ∀ d ∈ (f j).support,
      (∑ i ∈ d.support, (d i : ℝ) * (rho i : ℝ)) ≤ N) :
    ∃ L : ℕ, primeLength Q (Ideal.span (Set.range f)) = L ∧
      (L : ℝ) ≤ N ^ A.card / ∏ i ∈ A, (rho i : ℝ) := by
  let : Infinite Q.ResidueField := Infinite.of_injective
    (algebraMap ℂ Q.ResidueField) (algebraMap ℂ Q.ResidueField).injective
  have hminimal := sliceFamily_mem_minimalPrimes_of_normalBasis Q A hA f hQ
  have hlength := length_eq_sliceFamily_of_normalBasis Q A hA f
  have hrhoR (i : Fin n) : (0 : ℝ) < rho i := by exact_mod_cast hrho i
  have hsliceDegree : ∀ j, ∀ d ∈
      (enumeratedSliceMap A (residueCoordinates Q) (f j)).support,
      (∑ i ∈ d.support, (d i : ℝ) * (rho (A.equivFin.symm i) : ℝ)) ≤ N := by
    intro j
    exact supportBound_enumeratedSliceMap_sum A (residueCoordinates Q)
      (fun i => (rho i : ℝ)) (fun i => (hrhoR i).le) N (f j) (hdegree j)
  obtain ⟨L, hL, hupper⟩ := WeightedBezout.rational_pointLength_bound
    Q.ResidueField (fun j => enumeratedSliceMap A (residueCoordinates Q) (f j))
    (slicePoint Q A) (fun i => rho (A.equivFin.symm i)) (fun i => hrho _) N hN
    hsliceDegree hminimal
  refine ⟨L, hlength.trans hL, ?_⟩
  have hp : (∏ i : Fin A.card, (rho (A.equivFin.symm i) : ℝ)) =
      ∏ i ∈ A, (rho i : ℝ) := by
    calc
      _ = ∏ i : A, (rho i : ℝ) :=
        Fintype.prod_equiv A.equivFin.symm _ _ (fun _ => rfl)
      _ = _ := Finset.prod_coe_sort A (fun i => (rho i : ℝ))
  simpa only [hp] using hupper

end PiExponent.PrimeWeightedBezout
end

end OAI

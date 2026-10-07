/-
Modification notice for the LogTwo project.
Derived from openai/math (Apache-2.0), revision adc7f1241b42e322a6451854ab7e4b4c146bf78a.
Original source: lean/OAI/NumberTheory/PiExponent/Jets/PrimeTaylorCotangent.lean
Changes: Convert module/import declarations to the Lean 4.34 public module format.
See ../../../../../THIRD_PARTY_NOTICES.txt for provenance and the recorded changes.
-/

module

public import OAI.NumberTheory.PiExponent.Jets.RectangularCotangent
public import OAI.NumberTheory.PiExponent.LocalAlgebra.PrimeNormalKernel

@[expose] public section

namespace OAI

noncomputable section

namespace PiExponent

open PiExponentApprox.TransverseMultiplicity MvPowerSeries

variable {C ι σ : Type*} [Field C] [CharZero C] [Fintype ι]
variable [Fintype σ] [DecidableEq σ]
variable (Q : Ideal (MvPolynomial ι C)) [Q.IsPrime]

omit [Fintype ι] [Fintype σ] in
theorem primeRectangular_maps_maximal
    (tau : Localization.AtPrime Q →+* MvPowerSeries σ Q.ResidueField)
    (hzero : ∀ x, constantCoeff (tau x) = algebraMap (Localization.AtPrime Q) Q.ResidueField x)
    (n : σ → ℕ) (hn : ∀ i, 2 ≤ n i) :
    IsLocalRing.maximalIdeal (Localization.AtPrime Q) ≤
      (rectangularAugmentationIdeal (K := Q.ResidueField) n hn).comap
        (rectangularTaylorAlgHom n tau) := by
  apply rectangularTaylorAlgHom_maps_residueIdeal n (rectangularPositive n hn)
    tau (algebraMap (Localization.AtPrime Q) Q.ResidueField) hzero
  exact le_of_eq (IsLocalRing.ker_residue (R := Localization.AtPrime Q)).symm

theorem prime_rectangular_mapCotangent_surjective
    (tau : Localization.AtPrime Q →+* MvPowerSeries σ Q.ResidueField)
    (hzero : ∀ x, constantCoeff (tau x) = algebraMap (Localization.AtPrime Q) Q.ResidueField x)
    (v : σ → ι → Q.ResidueField)
    (hv : LinearIndependent Q.ResidueField
      (fun j => (polynomialTangent (primeResidueMap Q) Q).mkQ (v j)))
    (hfirst : ∀ j x, coeff (Finsupp.single j 1) (tau x) = primeLocalDirectional Q (v j) x)
    (n : σ → ℕ) (hn : ∀ i, 2 ≤ n i) :
    Function.Surjective
      (Ideal.mapCotangent (IsLocalRing.maximalIdeal (Localization.AtPrime Q))
        (rectangularAugmentationIdeal (K := Q.ResidueField) n hn)
        (rectangularTaylorAlgHom n tau) (primeRectangular_maps_maximal Q tau hzero n hn)) := by
  intro z
  obtain ⟨x, hx⟩ := prime_cotangent_evaluation_surjective Q v hv
    (rectangularCotangentFirstCoefficients n hn z)
  refine ⟨x, ?_⟩
  apply rectangularCotangentFirstCoefficients_injective n hn
  rw [← hx]
  obtain ⟨a, rfl⟩ :=
    (IsLocalRing.maximalIdeal (Localization.AtPrime Q)).toCotangent_surjective x
  funext j
  rw [Ideal.mapCotangent_toCotangent, rectangularCotangentFirstCoefficients_toCotangent]
  change rectangularFirstCoefficients n hn
    (Ideal.Quotient.mk (rectangularIdeal (K := Q.ResidueField) n) (tau a.1)) j = _
  rw [rectangularFirstCoefficients_mk, hfirst]
  exact (primeNormalPairing_toCotangent Q (v j) a).symm

omit [CharZero C] [Fintype σ] [DecidableEq σ] in

theorem prime_localizedTaylor_firstCoefficient
    (tau : MvPolynomial ι C →+* MvPowerSeries σ Q.ResidueField)
    (hzero : ∀ p, constantCoeff (tau p) =
      algebraMap (Localization.AtPrime Q) Q.ResidueField
        (algebraMap (MvPolynomial ι C) (Localization.AtPrime Q) p))
    (v : σ → ι → Q.ResidueField)
    (hfirst : ∀ j p, coeff (Finsupp.single j 1) (tau p) =
      ∑ i, v j i * primeResidueMap Q (MvPolynomial.pderiv i p))
    (j : σ) (x : Localization.AtPrime Q) :
    coeff (Finsupp.single j 1)
      (localizedTaylorMap Q.primeCompl tau
        (algebraMap (Localization.AtPrime Q) Q.ResidueField) hzero x) =
      primeLocalDirectional Q (v j) x := by
  apply localizedTaylorMap_linearCoefficient Q.primeCompl tau
    (algebraMap (Localization.AtPrime Q) Q.ResidueField) hzero j
      (primeLocalDirectional Q (v j))
  · intro a b
    simp only [Derivation.leibniz, Algebra.smul_def]
  · intro p
    rw [hfirst, primeLocalDirectional_polynomial]

end PiExponent

end

end OAI

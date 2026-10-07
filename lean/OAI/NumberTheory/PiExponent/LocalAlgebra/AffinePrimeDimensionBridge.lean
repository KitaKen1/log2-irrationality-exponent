/-
Modification notice for the LogTwo project.
Derived from openai/math (Apache-2.0), revision adc7f1241b42e322a6451854ab7e4b4c146bf78a.
Original source: lean/OAI/NumberTheory/PiExponent/LocalAlgebra/AffinePrimeDimensionBridge.lean
Changes: Convert module/import declarations to the Lean 4.34 public module format.
See ../../../../../THIRD_PARTY_NOTICES.txt for provenance and the recorded changes.
-/

module

public import OAI.NumberTheory.PiExponent.LocalAlgebra.AffineResidueTranscendence
public import OAI.NumberTheory.PiExponent.LocalAlgebra.ClosedPointLocalDimension

@[expose] public section

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

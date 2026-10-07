/-
Modification notice for the LogTwo project.
Derived from openai/math (Apache-2.0), revision adc7f1241b42e322a6451854ab7e4b4c146bf78a.
Original source: lean/OAI/NumberTheory/PiExponent/LocalAlgebra/SplitCoordinateClosedPoint.lean
Changes: Convert module/import declarations to the Lean 4.34 public module format.
See ../../../../../THIRD_PARTY_NOTICES.txt for provenance and the recorded changes.
-/

module

public import OAI.NumberTheory.PiExponent.Polynomials.CoefficientLocalizationMaximal
public import OAI.NumberTheory.PiExponent.Polynomials.PolynomialCoefficientLocalization
public import OAI.NumberTheory.PiExponent.Polynomials.RationalResidueCoefficientField

@[expose] public section

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

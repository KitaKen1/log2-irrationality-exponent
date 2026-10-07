/-
Modification notice for the LogTwo project.
Derived from openai/math (Apache-2.0), revision adc7f1241b42e322a6451854ab7e4b4c146bf78a.
Original source: lean/OAI/NumberTheory/PiExponent/Polynomials/PolynomialLocalLowExt.lean
Changes: Convert module/import declarations to the Lean 4.34 public module format.
See ../../../../../THIRD_PARTY_NOTICES.txt for provenance and the recorded changes.
-/

module

public import OAI.NumberTheory.PiExponent.LocalAlgebra.RegularSequenceLowExt
public import OAI.NumberTheory.PiExponent.Polynomials.PolynomialLocalRegularParameters

@[expose] public section

namespace OAI

noncomputable section
namespace PiExponentSiegelAux.W30
open CategoryTheory CategoryTheory.Abelian
universe u

theorem polynomialLocal_residueExt_below_height
    (K : Type u) [Field K] (n : ℕ)
    (Q : Ideal (MvPolynomial (Fin n) K)) [Q.IsPrime]
    (i : ℕ) (hi : (i : ℕ∞) < Q.height) :
    Subsingleton (Ext
      (ModuleCat.of (Localization.AtPrime Q)
        (IsLocalRing.ResidueField (Localization.AtPrime Q)))
      (ModuleCat.of (Localization.AtPrime Q) (Localization.AtPrime Q)) i) := by
  obtain ⟨h, hh, xs, hlen, hreg, hmax⟩ :=
    PiExponentJets.PolynomialLocalResidueResolution.exists_regularParameters_actual_height K n Q
  apply residueFieldExt_below_regular_length xs hreg hmax i
  rw [hlen]
  exact ENat.natCast_lt_natCast.mp (by simpa only [hh] using hi)

end PiExponentSiegelAux.W30

end

end OAI

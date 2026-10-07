/-
Modification notice for the LogTwo project.
Derived from openai/math (Apache-2.0), revision adc7f1241b42e322a6451854ab7e4b4c146bf78a.
Original source: lean/OAI/NumberTheory/PiExponent/LocalAlgebra/LocalizedOneCutPropagation.lean
Changes: Convert module/import declarations to the Lean 4.34 public module format.
See ../../../../../THIRD_PARTY_NOTICES.txt for provenance and the recorded changes.
-/

module

public import OAI.NumberTheory.PiExponent.LocalAlgebra.LocalIntersectionFormula
public import OAI.NumberTheory.PiExponent.LocalAlgebra.LocalizedMinimalPrimeFamily

@[expose] public section

namespace OAI

namespace PiExponentJets.W22

open PiExponentJets.W28.LocalIntersection
open scoped BigOperators Classical

variable {A : Type*} [CommRing A] [IsNoetherianRing A]

noncomputable def globalParentCutSum (I Q : Ideal A) [Q.IsPrime] (x : A) : ℕ∞ :=
  ∑ P : MinimalParentsBelow I Q,
    Module.length (Localization.AtPrime P.val)
      (Localization.AtPrime P.val ⧸ I.map (algebraMap A (Localization.AtPrime P.val))) *
    Module.length (Localization.AtPrime Q)
      (Localization.AtPrime Q ⧸ (P.val ⊔ Ideal.span {x}).map
        (algebraMap A (Localization.AtPrime Q)))

omit [IsNoetherianRing A] in
theorem localization_map_cut (I Q : Ideal A) [Q.IsPrime] (x : A) :
    (I ⊔ Ideal.span {x}).map (algebraMap A (Localization.AtPrime Q)) =
      I.map (algebraMap A (Localization.AtPrime Q)) ⊔
        Ideal.span {algebraMap A (Localization.AtPrime Q) x} := by
  rw [Ideal.map_sup, Ideal.map_span, Set.image_singleton]

theorem minimalPrimeCutSum_localization (I Q : Ideal A) [Q.IsPrime] (x : A) :
    minimalPrimeCutSum (I.map (algebraMap A (Localization.AtPrime Q)))
      (algebraMap A (Localization.AtPrime Q) x) = globalParentCutSum I Q x := by
  classical
  let : Fintype (I.map (algebraMap A (Localization.AtPrime Q))).minimalPrimes :=
    ((I.map (algebraMap A (Localization.AtPrime Q))).finite_minimalPrimes_of_isNoetherianRing
      (Localization.AtPrime Q)).fintype
  unfold minimalPrimeCutSum globalParentCutSum
  apply Fintype.sum_equiv (localizedMinimalPrimesEquiv I Q)
  intro p
  let : p.val.IsPrime := p.property.1.1
  have htower := localPrimeTower_quotient_length Q p.val I
  have hcut :
      ((p.val.comap (algebraMap A (Localization.AtPrime Q))) ⊔ Ideal.span {x}).map
        (algebraMap A (Localization.AtPrime Q)) =
      p.val ⊔ Ideal.span {algebraMap A (Localization.AtPrime Q) x} := by
    rw [Ideal.map_sup, Ideal.map_span, Set.image_singleton,
      IsLocalization.map_under Q.primeCompl (Localization.AtPrime Q) p.val]
  have hcutlen := congrArg
    (fun K : Ideal (Localization.AtPrime Q) =>
      Module.length (Localization.AtPrime Q) (Localization.AtPrime Q ⧸ K)) hcut
  exact congrArg₂ HMul.hMul htower.symm hcutlen.symm

theorem localized_onecut_parent_recurrence
    (I Q : Ideal A) [Q.IsPrime] (x : A)
    (hdim : ringKrullDim (Localization.AtPrime Q ⧸
      I.map (algebraMap A (Localization.AtPrime Q))) = 1)
    (hregular : Function.Injective
      (quotientMul (I.map (algebraMap A (Localization.AtPrime Q)))
        (algebraMap A (Localization.AtPrime Q) x))) :
    Module.length (Localization.AtPrime Q)
      (Localization.AtPrime Q ⧸ (I ⊔ Ideal.span {x}).map
        (algebraMap A (Localization.AtPrime Q))) = globalParentCutSum I Q x := by
  rw [localization_map_cut]
  exact (local_onecut_length _ _ hdim hregular).trans
    (minimalPrimeCutSum_localization I Q x)

end PiExponentJets.W22

end OAI

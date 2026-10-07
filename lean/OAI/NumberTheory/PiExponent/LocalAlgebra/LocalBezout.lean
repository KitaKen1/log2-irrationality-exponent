/-
Modification notice for the LogTwo project.
Derived from openai/math (Apache-2.0), revision adc7f1241b42e322a6451854ab7e4b4c146bf78a.
Original source: lean/OAI/NumberTheory/PiExponent/LocalAlgebra/LocalBezout.lean
Changes: Convert module/import declarations to the Lean 4.34 public module format.
See ../../../../../THIRD_PARTY_NOTICES.txt for provenance and the recorded changes.
-/

module

public import OAI.NumberTheory.PiExponent.LocalAlgebra.AffineLocalRegularBezout
public import OAI.NumberTheory.PiExponent.LocalAlgebra.RegularParameterSelection

@[expose] public section

namespace OAI

namespace PiExponent

open PiExponentJets.W22

theorem localIsolatedBezout
    (k : Type) [Field k] [Infinite k] (n : ℕ)
    {J : Type*} (f : J → MvPolynomial (Fin n) k) (D h : ℕ)
    (hdegree : ∀ j, (f j).totalDegree ≤ D)
    (P : Ideal (MvPolynomial (Fin n) k)) [P.IsPrime]
    (hminimal : P ∈ (Ideal.span (Set.range f)).minimalPrimes)
    (hheight : P.height = (h : ℕ∞)) (hbound : h ≤ n) :
    Module.length (Localization.AtPrime P)
      (Localization.AtPrime P ⧸ (Ideal.span (Set.range f)).map
        (algebraMap (MvPolynomial (Fin n) k) (Localization.AtPrime P))) ≤
      ((D ^ h : ℕ) : ℕ∞) := by
  have hrad := localized_radical_eq_maximal_of_mem_minimalPrimes
    (Ideal.span (Set.range f)) P hminimal
  obtain ⟨cs, _hcslength, hgslen, hgsdegree, hgscontained, hgsreg, hgsrad⟩ :=
    PiExponentSiegel.W58.polynomialLocal_exists_degree_bounded_regular_parameters
      k n P f D h hdegree hheight hrad
  let gs := cs.map (Finsupp.linearCombination k f)
  have hlen : gs.length = h := hgslen
  have hgsmin : P ∈ (Ideal.ofList gs).minimalPrimes :=
    mem_minimalPrimes_of_localized_radical (Ideal.ofList gs) P hgsrad
  have hselected := affine_local_regular_list_bezout n P gs D
    hgsdegree hgsreg (hlen.le.trans hbound) hgsmin
  have htransfer := ideal_quotient_length_le_of_bound
    (Ideal.map_mono hgscontained) hselected
  simpa only [hlen] using htransfer

end PiExponent

end OAI

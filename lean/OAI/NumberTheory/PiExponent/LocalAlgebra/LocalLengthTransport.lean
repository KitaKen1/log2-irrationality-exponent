/-
Modification notice for the LogTwo project.
Derived from openai/math (Apache-2.0), revision adc7f1241b42e322a6451854ab7e4b4c146bf78a.
Original source: lean/OAI/NumberTheory/PiExponent/LocalAlgebra/LocalLengthTransport.lean
Changes: Convert module/import declarations to the Lean 4.34 public module format.
See ../../../../../THIRD_PARTY_NOTICES.txt for provenance and the recorded changes.
-/

module

public import Mathlib.RingTheory.Localization.AtPrime.Basic
public import OAI.NumberTheory.PiExponent.LocalAlgebra.QuotientLengthEquivalence

@[expose] public section

namespace OAI

noncomputable section
namespace PiExponent.LocalLengthTransport

abbrev localLength {R : Type*} [CommRing R]
    (P : Ideal R) [P.IsPrime] (I : Ideal R) : ℕ∞ :=
  Module.length (Localization.AtPrime P)
    (Localization.AtPrime P ⧸ I.map (algebraMap R (Localization.AtPrime P)))

theorem localLength_congr {R : Type*} [CommRing R]
    (P Q : Ideal R) [P.IsPrime] [Q.IsPrime] (hPQ : P = Q) (I : Ideal R) :
    localLength P I = localLength Q I := by
  subst Q
  rfl

variable {R S : Type*} [CommRing R] [CommRing S]
variable (P : Ideal R) (Q : Ideal S) [P.IsPrime] [Q.IsPrime]

theorem localizedIdeal_map_eq
    (f : R →+* S) (e : Localization.AtPrime P ≃+* Localization.AtPrime Q)
    (he : ∀ r : R, e (algebraMap R (Localization.AtPrime P) r) =
      algebraMap S (Localization.AtPrime Q) (f r))
    (I : Ideal R) :
    (I.map (algebraMap R (Localization.AtPrime P))).map e.toRingHom =
      (I.map f).map (algebraMap S (Localization.AtPrime Q)) := by
  rw [Ideal.map_map, Ideal.map_map]
  congr 1
  exact RingHom.ext he

theorem localLength_eq_map
    (f : R →+* S) (e : Localization.AtPrime P ≃+* Localization.AtPrime Q)
    (he : ∀ r : R, e (algebraMap R (Localization.AtPrime P) r) =
      algebraMap S (Localization.AtPrime Q) (f r))
    (I : Ideal R) :
    localLength P I = localLength Q (I.map f) :=
  PiExponentJets.W22.quotient_length_eq_of_ringEquiv e _ _
    (localizedIdeal_map_eq P Q f e he I).symm

theorem localLength_eq_of_localizedIdeal_map
    (e : Localization.AtPrime P ≃+* Localization.AtPrime Q)
    (I : Ideal R) (J : Ideal S)
    (hIJ : (I.map (algebraMap R (Localization.AtPrime P))).map e.toRingHom =
      J.map (algebraMap S (Localization.AtPrime Q))) :
    localLength P I = localLength Q J :=
  PiExponentJets.W22.quotient_length_eq_of_ringEquiv e _ _ hIJ.symm

end PiExponent.LocalLengthTransport

end

end OAI

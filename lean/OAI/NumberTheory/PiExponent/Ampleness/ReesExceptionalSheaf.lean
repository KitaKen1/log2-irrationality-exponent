/-
Modification notice for the LogTwo project.
Derived from openai/math (Apache-2.0), revision adc7f1241b42e322a6451854ab7e4b4c146bf78a.
Original source: lean/OAI/NumberTheory/PiExponent/Ampleness/ReesExceptionalSheaf.lean
Changes: Convert module/import declarations to the Lean 4.34 public module format.
See ../../../../../THIRD_PARTY_NOTICES.txt for provenance and the recorded changes.
-/

module

public import OAI.NumberTheory.PiExponent.Ampleness.ReesExceptional

@[expose] public section

namespace OAI

namespace PiExponentSeshadri.ReesGrading
noncomputable section
variable {R : Type} [CommRing R] (I : Ideal R)

theorem exceptionalLineBundle_sheaf_eq :
    (exceptionalLineBundle I).sheaf = IdealModule.closedModule (exceptionalIdeal I) := rfl

end
end PiExponentSeshadri.ReesGrading

end OAI

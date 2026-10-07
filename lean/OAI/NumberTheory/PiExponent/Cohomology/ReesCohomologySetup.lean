/-
Modification notice for the LogTwo project.
Derived from openai/math (Apache-2.0), revision adc7f1241b42e322a6451854ab7e4b4c146bf78a.
Original source: lean/OAI/NumberTheory/PiExponent/Cohomology/ReesCohomologySetup.lean
Changes: Convert module/import declarations to the Lean 4.34 public module format.
See ../../../../../THIRD_PARTY_NOTICES.txt for provenance and the recorded changes.
-/

module

public import OAI.NumberTheory.PiExponent.Ampleness.ReesExceptional
public import OAI.NumberTheory.PiExponent.Geometry.LineBundleCoherent

@[expose] public section

namespace OAI

namespace PiExponent.ReesCohomologySetup
noncomputable section
open AlgebraicGeometry PiExponentSeshadri.ReesGrading
variable {R : Type} [CommRing R] (I : Ideal R)

instance [IsNoetherianRing R] : IsNoetherian (affineBlowup I) := by
  let : CompactSpace (affineBlowup I) :=
    QuasiCompact.compactSpace_of_compactSpace (projection I)
  exact { __ := LocallyOfFiniteType.isLocallyNoetherian (projection I) }

theorem exceptionalPower_isQuasicoherent (n : ℕ) :
    ((exceptionalLineBundle I).pow n).sheaf.IsQuasicoherent :=
  GeometrySupport.LineBundleCoherent.modulePow_isQuasicoherent (exceptionalLineBundle I) n

end
end PiExponent.ReesCohomologySetup

end OAI

/-
Modification notice for the LogTwo project.
Derived from openai/math (Apache-2.0), revision adc7f1241b42e322a6451854ab7e4b4c146bf78a.
Original source: lean/OAI/NumberTheory/PiExponent/Ampleness/ProjectiveO1Ample.lean
Changes: Convert module/import declarations to the Lean 4.34 public module format.
See ../../../../../THIRD_PARTY_NOTICES.txt for provenance and the recorded changes.
-/

module

public import OAI.NumberTheory.PiExponent.Ampleness.AmpleFromCover
public import OAI.NumberTheory.PiExponent.Geometry.ProjectiveO1Identity
public import OAI.NumberTheory.PiExponent.Geometry.ProjectiveSpaceIntegral

@[expose] public section

namespace OAI

noncomputable section

namespace PiExponent.ProjectiveO1

open AlgebraicGeometry CategoryTheory
open PiExponentSeshadri.Geometry

variable {R σ : Type} [CommRing R] [IsDomain R] [Finite σ] [Nonempty σ]

theorem lineBundle_ample : (lineBundle (R := R) (σ := σ)).IsAmple := by
  let : CompactSpace (projectiveSpace R σ) :=
    QuasiCompact.compactSpace_of_compactSpace (polynomialProjectiveProjection R σ)
  exact LineBundle.ample_of_affine_section_cover (lineBundle (R := R) (σ := σ))
    coordinateSection coordinateSection_cover coordinateSection_isAffineOpen

end PiExponent.ProjectiveO1

end

end OAI

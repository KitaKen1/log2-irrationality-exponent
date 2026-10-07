/-
Modification notice for the LogTwo project.
Derived from openai/math (Apache-2.0), revision adc7f1241b42e322a6451854ab7e4b4c146bf78a.
Original source: lean/OAI/NumberTheory/PiExponent/Geometry/ProjectiveO1Identity.lean
Changes: Convert module/import declarations to the Lean 4.34 public module format.
See ../../../../../THIRD_PARTY_NOTICES.txt for provenance and the recorded changes.
-/

module

public import OAI.NumberTheory.PiExponent.Geometry.ProjectiveO1Morphism

@[expose] public section

namespace OAI

noncomputable section

namespace PiExponent.ProjectiveO1

open AlgebraicGeometry CategoryTheory TopologicalSpace
open PiExponentSeshadri.Projective PiExponentSeshadri.Frames PiExponentSeshadri.LineBundleGluing

attribute [local irreducible] lineBundle coordinateSection scalars sectionsMorphism

variable {R σ : Type} [CommRing R]

theorem coordinateSection_isoOpen (i : σ) :
    PiExponentSeshadri.SectionOpens.isoOpen (coordinateSection (R := R) i) = coordinateOpen i := by
  exact identityCoordinateOpen (lineBundle (R := R) (σ := σ)).sheaf
    (scalars (R := R) (σ := σ)) (coordinateSection (R := R) (σ := σ))
    (coordinateSection_cover (R := R) (σ := σ))
    (coordinate_sectionsMorphism_identity (R := R) (σ := σ)) i

theorem coordinateSection_isAffineOpen (i : σ) :
    IsAffineOpen (PiExponentSeshadri.SectionOpens.isoOpen (coordinateSection (R := R) i)) := by
  rw [coordinateSection_isoOpen]
  exact standardChart_isAffineOpen i

end PiExponent.ProjectiveO1

end

end OAI

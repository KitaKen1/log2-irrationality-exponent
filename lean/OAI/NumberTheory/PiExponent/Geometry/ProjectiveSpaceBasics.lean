/-
Modification notice for the LogTwo project.
Derived from openai/math (Apache-2.0), revision adc7f1241b42e322a6451854ab7e4b4c146bf78a.
Original source: lean/OAI/NumberTheory/PiExponent/Geometry/ProjectiveSpaceBasics.lean
Changes: Convert module/import declarations to the Lean 4.34 public module format.
See ../../../../../THIRD_PARTY_NOTICES.txt for provenance and the recorded changes.
-/

module

public import OAI.NumberTheory.PiExponent.Cohomology.CurveEuler
public import OAI.NumberTheory.PiExponent.Geometry.ProjectiveO1ChartMap

@[expose] public section

namespace OAI

namespace PiExponent.ProjectiveO1
noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace
open PiExponentSeshadri.Geometry
variable (R σ : Type) [CommRing R]

instance projectiveSpace_noetherian [IsNoetherianRing R] [Finite σ] :
    IsNoetherian (projectiveSpace R σ) := by
  let : IsLocallyNoetherian (projectiveSpace R σ) :=
    LocallyOfFiniteType.isLocallyNoetherian (polynomialProjectiveProjection R σ)
  let : CompactSpace (projectiveSpace R σ) :=
    QuasiCompact.compactSpace_of_compactSpace (polynomialProjectiveProjection R σ)
  exact {}

instance projectiveSpace_separated [Finite σ] : (projectiveSpace R σ).IsSeparated := by
  constructor
  have h : IsSeparated (polynomialProjectiveProjection R σ ≫
      terminal.from (Spec (CommRingCat.of R))) := inferInstance
  simpa only [terminal.comp_from] using h

instance projectiveSpace_diagonal_affine [Finite σ] :
    IsAffineHom (pullback.diagonal (terminal.from (projectiveSpace R σ))) := by
  infer_instance

theorem scalars_eq_baseScalars :
    scalars (R := ℂ) (σ := σ) = baseScalars (polynomialProjectiveProjection ℂ σ) := rfl

end
end PiExponent.ProjectiveO1

end OAI

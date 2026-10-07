/-
Modification notice for the LogTwo project.
Derived from openai/math (Apache-2.0), revision adc7f1241b42e322a6451854ab7e4b4c146bf78a.
Original source: lean/OAI/NumberTheory/PiExponent/Geometry/WeightedProjectiveStructure.lean
Changes: Convert module/import declarations to the Lean 4.34 public module format.
See ../../../../../THIRD_PARTY_NOTICES.txt for provenance and the recorded changes.
-/

module

public import OAI.NumberTheory.PiExponent.Approximation.WeightedCompactificationImmersion
public import OAI.NumberTheory.PiExponent.Geometry.PolynomialProjectiveStructure

@[expose] public section

namespace OAI

noncomputable section

namespace PiExponent.WeightedCompactification

open MvPolynomial AlgebraicGeometry CategoryTheory

universe u
variable {R ι σ : Type u} [CommRing R]

attribute [local instance] MvPolynomial.gradedAlgebra

def projection (a : σ → ι →₀ ℕ) :
    Proj (imageGrade (R := R) a) ⟶ Spec (CommRingCat.of R) :=
  projectiveMonomialMap a ≫ polynomialProjectiveProjection R σ

instance projection_proper [Finite σ] (a : σ → ι →₀ ℕ) :
    IsProper (projection (R := R) a) := by
  have : IsProper (projectiveMonomialMap (R := R) a) := inferInstance
  exact MorphismProperty.comp_mem (@IsProper) _ _ inferInstance inferInstance

theorem projection_closed_projective_factorization [Finite σ] (a : σ → ι →₀ ℕ) :
    ∃ e : Proj (imageGrade (R := R) a) ⟶ Proj (homogeneousSubmodule σ R),
      IsClosedImmersion e ∧ e ≫ polynomialProjectiveProjection R σ = projection a :=
  ⟨projectiveMonomialMap a, inferInstance, rfl⟩

end PiExponent.WeightedCompactification

end

end OAI

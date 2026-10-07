/-
Modification notice for the LogTwo project.
Derived from openai/math (Apache-2.0), revision adc7f1241b42e322a6451854ab7e4b4c146bf78a.
Original source: lean/OAI/NumberTheory/PiExponent/Cohomology/CohomologyFinite.lean
Changes: Convert module/import declarations to the Lean 4.34 public module format.
See ../../../../../THIRD_PARTY_NOTICES.txt for provenance and the recorded changes.
-/

module

public import OAI.NumberTheory.PiExponent.Geometry.ProjectiveCoordinateFinite

@[expose] public section

namespace OAI

namespace PiExponent.CohomologyFiniteness
noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace
open PiExponentSeshadri.Geometry PiExponentSeshadri.Projective
open GeometrySupport.ProjectiveCoordinateFinite
attribute [local instance] MvPolynomial.gradedAlgebra
variable {X Y : Scheme.{0}}

def CohomologyFinite (p : X ⟶ Spec (CommRingCat.of ℂ)) (M : X.Modules) (q : ℕ) : Prop :=
  letI := Module.compHom (cohomology M q) (baseScalars p)
  FiniteDimensional ℂ (cohomology M q)

theorem finiteDimensional (p : X ⟶ Spec (CommRingCat.of ℂ)) (M : X.Modules) (q : ℕ)
    (h : CohomologyFinite p M q) :
    letI := Module.compHom (cohomology M q) (baseScalars p)
    FiniteDimensional ℂ (cohomology M q) := h

theorem coordinateBundle_finite [IsNoetherian X]
    [IsAffineHom (pullback.diagonal (terminal.from X))]
    (p : X ⟶ Spec (CommRingCat.of ℂ)) (L : LineBundle X) (l : ℕ) (hl : 0 < l)
    (s : Fin l → (structureSheaf X ⟶ L.sheaf))
    (hc : (⨆ i, PiExponentSeshadri.SectionOpens.isoOpen (s i)) = ⊤)
    (f : X ≅ Proj (PolyGrade ℂ (Fin l)))
    (hf : sectionsMorphism (baseScalars p) s hc = f.hom)
    (M : X.Modules) [M.IsFinitePresentation] (q : ℕ) : CohomologyFinite p M q :=
  coordinateBundle_cohomology_finite p L l hl s hc f hf M q

theorem closedPushforward_finite (i : X ⟶ Y) [IsClosedImmersion i]
    (p : Y ⟶ Spec (CommRingCat.of ℂ)) (M : X.Modules) (q : ℕ)
    (h : CohomologyFinite p ((Scheme.Modules.pushforward i).obj M) q) :
    CohomologyFinite (i ≫ p) M q :=
  ClosedImmersionSerreTransfer.finiteDimensional_of_pushforward i p M q h

end
end PiExponent.CohomologyFiniteness

end OAI

/-
Modification notice for the LogTwo project.
Derived from openai/math (Apache-2.0), revision adc7f1241b42e322a6451854ab7e4b4c146bf78a.
Original source: lean/OAI/NumberTheory/PiExponent/Geometry/ProjectiveCoordinateFinite.lean
Changes: Convert module/import declarations to the Lean 4.34 public module format.
See ../../../../../THIRD_PARTY_NOTICES.txt for provenance and the recorded changes.
-/

module

public import OAI.NumberTheory.PiExponent.Cohomology.LaurentExtFinite
public import OAI.NumberTheory.PiExponent.Geometry.ProjectiveNegativeScalars
public import OAI.NumberTheory.PiExponent.LocalAlgebra.CoherentInverseFinite

@[expose] public section

namespace OAI

namespace PiExponent.GeometrySupport.ProjectiveCoordinateFinite
noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace
open PiExponentSeshadri.Geometry PiExponentSeshadri.Projective
open ProjectiveTupleCharts
attribute [local instance] MvPolynomial.gradedAlgebra
attribute [local irreducible] negativeCoordinateLaurentPresentation
  coordinateFramedTuple negativeCoordinateFrame LineBundle.inverse lineTensorInverseIso
variable {X Y : Scheme.{0}} {K σ : Type} [Field K] [Fintype σ]

theorem inversePower_cohomology_finite [IsNoetherian X]
    [IsAffineHom (pullback.diagonal (terminal.from X))]
    (L : LineBundle X) (s : σ → (structureSheaf X ⟶ L.sheaf)) (k : K →+* Γ(X,⊤))
    (hc : (⨆ i, PiExponentSeshadri.SectionOpens.isoOpen (s i)) = ⊤)
    (f : X ≅ Proj (PolyGrade K σ)) (hf : sectionsMorphism k s hc = f.hom)
    (n q : ℕ) :
    letI := Module.compHom (cohomology (L.pow n).inverse.sheaf q) k
    Module.Finite K (cohomology (L.pow n).inverse.sheaf q) := by
  let := LineBundleCoherent.lineBundle_isFinitePresentation (L.pow n).inverse
  let : (L.pow n).inverse.sheaf.IsQuasicoherent :=
    (SheafOfModules.IsFinitePresentation.exists_quasicoherentData
      (L.pow n).inverse.sheaf).choose.isQuasicoherent
  exact ActualLaurentExtFinite.cohomology_finite k
    (negativeCoordinateLaurentPresentation L.sheaf s k hc f hf n _
      (lineTensorInverseIso (L.pow n)))
    (negativeCoordinateLaurentPresentation_smul L.sheaf s k hc f hf n _
      (lineTensorInverseIso (L.pow n)))
    hc.ge
    (fun r t => IsAffineOpen.iInf
      (fun i => coordinateOpen_isAffine L.sheaf s k hc f hf (t i))) q

theorem coordinateBundle_cohomology_finite [IsNoetherian X]
    [IsAffineHom (pullback.diagonal (terminal.from X))]
    (p : X ⟶ Spec (CommRingCat.of ℂ)) (L : LineBundle X) (l : ℕ) (hl : 0 < l)
    (s : Fin l → (structureSheaf X ⟶ L.sheaf))
    (hc : (⨆ i, PiExponentSeshadri.SectionOpens.isoOpen (s i)) = ⊤)
    (f : X ≅ Proj (PolyGrade ℂ (Fin l)))
    (hf : sectionsMorphism (baseScalars p) s hc = f.hom)
    (M : X.Modules) [M.IsFinitePresentation] (q : ℕ) :
    letI := Module.compHom (cohomology M q) (baseScalars p)
    FiniteDimensional ℂ (cohomology M q) := by
  exact CoherentProjectiveFinite.coherent_cohomology_finite_of_inverse_powers
    p L l hl s hc (coordinateOpen_isAffine L.sheaf s (baseScalars p) hc f hf)
    (inversePower_cohomology_finite L s (baseScalars p) hc f hf) M q

theorem closed_coordinateBundle_cohomology_finite [IsNoetherian Y]
    [IsAffineHom (pullback.diagonal (terminal.from Y))]
    (i : X ⟶ Y) [IsClosedImmersion i]
    (p : Y ⟶ Spec (CommRingCat.of ℂ)) (L : LineBundle Y) (l : ℕ) (hl : 0 < l)
    (s : Fin l → (structureSheaf Y ⟶ L.sheaf))
    (hc : (⨆ j, PiExponentSeshadri.SectionOpens.isoOpen (s j)) = ⊤)
    (f : Y ≅ Proj (PolyGrade ℂ (Fin l)))
    (hf : sectionsMorphism (baseScalars p) s hc = f.hom)
    (M : X.Modules) [M.IsFinitePresentation] (q : ℕ) :
    letI := Module.compHom (cohomology M q) (baseScalars (i ≫ p))
    FiniteDimensional ℂ (cohomology M q) := by
  exact CoherentProjectiveFinite.closed_coherent_cohomology_finite_of_inverse_powers
    i p L l hl s hc (coordinateOpen_isAffine L.sheaf s (baseScalars p) hc f hf)
    (inversePower_cohomology_finite L s (baseScalars p) hc f hf) M q

end
end PiExponent.GeometrySupport.ProjectiveCoordinateFinite

end OAI

/-
Modification notice for the LogTwo project.
Derived from openai/math (Apache-2.0), revision adc7f1241b42e322a6451854ab7e4b4c146bf78a.
Original source: lean/OAI/NumberTheory/PiExponent/Cohomology/AmpleLineCohomology.lean
Changes: Convert module/import declarations to the Lean 4.34 public module format.
See ../../../../../THIRD_PARTY_NOTICES.txt for provenance and the recorded changes.
-/

module

public import OAI.NumberTheory.PiExponent.Cohomology.AmpleCohomologyFinite
public import OAI.NumberTheory.PiExponent.Cohomology.CartierEulerPair
public import OAI.NumberTheory.PiExponent.Cohomology.FiniteLineEuler

@[expose] public section

namespace OAI

namespace PiExponent.NumericalAmpleness
noncomputable section
open AlgebraicGeometry CategoryTheory
open PiExponentSeshadri.Geometry
variable {X : Scheme.{0}}
theorem line_cohomology_finite_of_ample_all
    (p : X ⟶ Spec (CommRingCat.of ℂ)) [IsProper p]
    (H : LineBundle X) (hH : H.IsAmple) (L : LineBundle X) (q : ℕ) :
    letI := Module.compHom (cohomology L.sheaf q) (baseScalars p)
    FiniteDimensional ℂ (cohomology L.sheaf q) := by
  cases isEmpty_or_nonempty X with
  | inr hX =>
    let := hX
    let := GeometrySupport.LineBundleCoherent.lineBundle_isFinitePresentation L
    exact AmpleCohomologyFinite.cohomology_finite_of_ample p H hH L.sheaf q
  | inl hX =>
    let := hX
    let := Module.compHom (cohomology L.sheaf q) (baseScalars p)
    let M := (Scheme.Modules.pushforward (𝟙 X)).obj L.sheaf
    let := Module.compHom (cohomology M q) (baseScalars p)
    let : FiniteDimensional ℂ (cohomology M q) :=
      PiExponentSeshadri.FiniteSupport.finite_line_pushforward_finiteDimensional (𝟙 X) p L q
    let e := PiExponent.ClosedImmersionSerreTransfer.cohomologyLinearEquiv (𝟙 X) p L.sheaf q
    exact FiniteDimensional.of_surjective e.symm.toLinearMap e.symm.surjective
end
end PiExponent.NumericalAmpleness

end OAI

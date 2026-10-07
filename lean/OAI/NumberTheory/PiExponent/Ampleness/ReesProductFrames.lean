/-
Modification notice for the LogTwo project.
Derived from openai/math (Apache-2.0), revision adc7f1241b42e322a6451854ab7e4b4c146bf78a.
Original source: lean/OAI/NumberTheory/PiExponent/Ampleness/ReesProductFrames.lean
Changes: Convert module/import declarations to the Lean 4.34 public module format.
See ../../../../../THIRD_PARTY_NOTICES.txt for provenance and the recorded changes.
-/

module

public import OAI.NumberTheory.PiExponent.Ampleness.ExceptionalAffineChart
public import OAI.NumberTheory.PiExponent.Ampleness.ReesExceptionalSheaf
public import OAI.NumberTheory.PiExponent.Ampleness.ReesProductSchemeChart

@[expose] public section

namespace OAI

noncomputable section
open CategoryTheory AlgebraicGeometry
open PiExponentSeshadri.Geometry PiExponentSeshadri.Frames
namespace PiExponent.ReesProductPowerSections
open PiExponentSeshadri.ReesGrading PiExponent.ReesProductChart
variable {R J : Type} [CommRing R] [Fintype J] [DecidableEq J]
variable (I : Ideal R) (a : J → I) {s : Finset J} (hs : s.Nonempty)
variable {p : J} (hp : p ∈ s)
attribute [local irreducible] affineBlowup projection exceptionalLineBundle exceptionalInclusion exceptionalIdeal
  PiExponentSeshadri.Geometry.LineBundle.pow PiExponentSeshadri.Geometry.PresentsPullbackIdeal
  PiExponent.ExceptionalAffineChart.sectionsEquiv PiExponent.ExceptionalAffineChart.idealChartFrame

include hp in

theorem chartFrame_nonempty :
    Nonempty ((exceptionalLineBundle I).sheaf.restrict (chartOpen I a hs).1.ι ≅
      O (chartOpen I a hs).1.toScheme) := by
  rw [exceptionalLineBundle_sheaf_eq]
  exact ⟨ExceptionalAffineChart.idealChartFrame (Y := affineBlowup I) (chartMorphism I a hs) (exceptionalIdeal I)
    (chartEquation I a (s := s) (p := p))
    (exceptional_chart I a hs hp) (chartEquation_regular I a hp)⟩

def chartFrame :
    (exceptionalLineBundle I).sheaf.restrict (chartOpen I a hs).1.ι ≅
      O (chartOpen I a hs).1.toScheme :=
  (chartFrame_nonempty I a hs hp).some

end PiExponent.ReesProductPowerSections
end

end OAI

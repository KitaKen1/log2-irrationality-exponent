/-
Modification notice for the LogTwo project.
Derived from openai/math (Apache-2.0), revision adc7f1241b42e322a6451854ab7e4b4c146bf78a.
Original source: lean/OAI/NumberTheory/PiExponent/Ampleness/ReesFixedFrames.lean
Changes: Convert module/import declarations to the Lean 4.34 public module format.
See ../../../../../THIRD_PARTY_NOTICES.txt for provenance and the recorded changes.
-/

module

public import OAI.NumberTheory.PiExponent.Ampleness.ReesFixedChart

@[expose] public section

namespace OAI

namespace PiExponent.ReesFrozenChart
noncomputable section
open CategoryTheory AlgebraicGeometry
open PiExponentSeshadri.ReesGrading PiExponent.ReesProductChart
attribute [local irreducible] affineBlowup projection exceptionalLineBundle exceptionalInclusion exceptionalIdeal
  PiExponentSeshadri.Geometry.LineBundle.pow
variable {R J : Type} [CommRing R] [Fintype J] [DecidableEq J]
variable (I : Ideal R) (a : J → I) {s : Finset J} (hs : s.Nonempty)

theorem frame_nonempty_congr {X : Scheme} (M : X.Modules) {U V : X.Opens}
    (h : U = V)
    (he : Nonempty (M.restrict U.ι ≅ PiExponentSeshadri.Frames.O U.toScheme)) :
    Nonempty (M.restrict V.ι ≅ PiExponentSeshadri.Frames.O V.toScheme) := by
  subst V
  exact he

theorem chartFrame_nonempty {p : J} (hp : p ∈ s) :
    Nonempty ((exceptionalLineBundle I).sheaf.restrict (chartOpen I a hs).1.ι ≅
      PiExponentSeshadri.Frames.O (chartOpen I a hs).1.toScheme) :=
  frame_nonempty_congr (exceptionalLineBundle I).sheaf (chartOpen_eq I a hs).symm
    (ReesProductPowerSections.chartFrame_nonempty I a hs hp)

def chartFrame {p : J} (hp : p ∈ s) :
    (exceptionalLineBundle I).sheaf.restrict (chartOpen I a hs).1.ι ≅
      PiExponentSeshadri.Frames.O (chartOpen I a hs).1.toScheme :=
  (chartFrame_nonempty I a hs hp).some

end
end PiExponent.ReesFrozenChart

end OAI

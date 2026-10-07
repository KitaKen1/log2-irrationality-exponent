/-
Modification notice for the LogTwo project.
Derived from openai/math (Apache-2.0), revision adc7f1241b42e322a6451854ab7e4b4c146bf78a.
Original source: lean/OAI/NumberTheory/PiExponent/Ampleness/ReesSheafCanonicalValue.lean
Changes: Convert module/import declarations to the Lean 4.34 public module format.
Expose private helpers and adjust helper names where needed for module compatibility.
See ../../../../../THIRD_PARTY_NOTICES.txt for provenance and the recorded changes.
-/

module

public import OAI.NumberTheory.PiExponent.Ampleness.ReesSectionInclusion
public import OAI.NumberTheory.PiExponent.Cohomology.ReesSheafCechRecovery

@[expose] public section

namespace OAI

namespace PiExponent.ReesSheafCechRecovery
noncomputable section
open CategoryTheory AlgebraicGeometry TopologicalSpace
open PiExponentSeshadri.ReesGrading PiExponentSeshadri.ModuleFlasque
open PiExponentSeshadri.Geometry PiExponentSeshadri.Frames
open PiExponent.GeometrySupport PiExponent.ReesSheafCechBase
open PiExponent.GradedPolynomialLaurent PiExponent.GradedCech
attribute [local irreducible] affineBlowup projection exceptionalLineBundle exceptionalInclusion exceptionalIdeal
  PiExponentSeshadri.Geometry.LineBundle.pow PiExponentSeshadri.Geometry.PresentsPullbackIdeal
variable {R J : Type} [CommRing R] [Fintype J] [DecidableEq J]
variable (I : Ideal R) (a : J → I)

abbrev chartMap {s : Finset J} (hs : s.Nonempty) :
    Spec (CommRingCat.of (ReesFrozenChart.coordinateRing I a s)) ⟶ affineBlowup I :=
  ReesFrozenChart.chart I a hs

local instance chartOpenImmersion {s : Finset J} (hs : s.Nonempty) :
    IsOpenImmersion (chartMap I a hs) :=
  ReesFrozenChart.instIsOpenImmersionChart I a hs

theorem ordinaryGlobalSection_chart_inclusion
    (ha : Ideal.span (Set.range fun j => (a j).val) = I) (n : ℕ)
    (b : ↥(I^n : Ideal R)) (t : Fin 1 → J) :
    ExceptionalAffineChart.functionsOnOpenEquiv
      (chartMap I a (tuple_nonempty 0 t))
      ((affineBlowup I).presheaf.map (homOfLE le_top).op
        ((idealPowerInclusion (exceptionalLineBundle I) (exceptionalInclusion I) n).app ⊤
          (ordinaryGlobalSection I a ha n b))) =
      ReesFrozenChart.base I a (tupleSet t) b.val :=
  ReesSectionInclusion.section_chart_inclusion I a n
    (ordinarySectionHom I a ha n b) b.val
    (fun t => ordinarySectionHom_frozenChartValue I a ha n b t) t

theorem ordinaryGlobalSection_inclusion
    (ha : Ideal.span (Set.range fun j => (a j).val) = I) (n : ℕ)
    (b : ↥(I^n : Ideal R)) :
    (idealPowerInclusion (exceptionalLineBundle I) (exceptionalInclusion I) n).app ⊤
      (ordinaryGlobalSection I a ha n b) =
    (projection I).appTop ((Scheme.ΓSpecIso (CommRingCat.of R)).inv b.val) :=
  ReesSectionInclusion.section_inclusion I a ha n
    (ordinarySectionHom I a ha n b) b.val
    (fun t => ordinarySectionHom_frozenChartValue I a ha n b t)

end
end PiExponent.ReesSheafCechRecovery

end OAI

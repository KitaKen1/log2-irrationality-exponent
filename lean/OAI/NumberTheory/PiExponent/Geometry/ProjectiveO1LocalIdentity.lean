/-
Modification notice for the LogTwo project.
Derived from openai/math (Apache-2.0), revision adc7f1241b42e322a6451854ab7e4b4c146bf78a.
Original source: lean/OAI/NumberTheory/PiExponent/Geometry/ProjectiveO1LocalIdentity.lean
Changes: Convert module/import declarations to the Lean 4.34 public module format.
See ../../../../../THIRD_PARTY_NOTICES.txt for provenance and the recorded changes.
-/

module

public import OAI.NumberTheory.PiExponent.Geometry.ProjectiveFramedAtlas
public import OAI.NumberTheory.PiExponent.Geometry.ProjectiveO1ChartMap
public import OAI.NumberTheory.PiExponent.Geometry.ProjectiveO1Sections

@[expose] public section

namespace OAI

noncomputable section
namespace PiExponent.ProjectiveO1
open AlgebraicGeometry CategoryTheory TopologicalSpace
open PiExponentSeshadri.Projective PiExponentSeshadri.Frames PiExponentSeshadri.LineBundleGluing
variable {R σ : Type} [CommRing R]

theorem coordinateSection_localMap (i : σ) :
    coordinatesMap (coordinateOpen (R := R) i).toScheme
      ((coordinateOpen i).ι.appTop.hom.comp (scalars (R := R) (σ := σ)))
      (fun j => coefficient (openFrame (coordinateCocycle (R := R) (σ := σ)) i (coordinateOpen i) le_rfl)
        (restrictSection (coordinateOpen i).ι (coordinateSection (R := R) j))) i
      (coordinateSection_normalized i (coordinateOpen i) le_rfl) = (coordinateOpen i).ι := by
  have htuple : (fun j => coefficient
      (openFrame (coordinateCocycle (R := R) (σ := σ)) i (coordinateOpen (R := R) i) le_rfl)
      (restrictSection (coordinateOpen i).ι (coordinateSection (R := R) j))) = chartRatios (R := R) i := by
    funext j
    exact coordinateSection_coefficient_eq i j (coordinateOpen i) le_rfl
  exact (coordinatesMap_congr _ htuple i _ (chartRatios_self i)).trans
    (coordinatesMap_chartRatios (R := R) i)

end PiExponent.ProjectiveO1

end

end OAI

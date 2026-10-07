/-
Modification notice for the LogTwo project.
Derived from openai/math (Apache-2.0), revision adc7f1241b42e322a6451854ab7e4b4c146bf78a.
Original source: lean/OAI/NumberTheory/PiExponent/Ampleness/ReesProductSchemeRestriction.lean
Changes: Convert module/import declarations to the Lean 4.34 public module format.
See ../../../../../THIRD_PARTY_NOTICES.txt for provenance and the recorded changes.
-/

module

public import OAI.NumberTheory.PiExponent.Ampleness.ReesProductRestriction
public import OAI.NumberTheory.PiExponent.Ampleness.ReesProductSchemeChart

@[expose] public section

namespace OAI

namespace PiExponent.ReesProductSchemeRestriction
noncomputable section
open CategoryTheory AlgebraicGeometry
open PiExponentSeshadri.ReesGrading
open PiExponent.ReesProductChart PiExponent.ReesProductRestriction
open PiExponent.ReesProductPowerSections
variable {R J : Type} [CommRing R] [Fintype J] [DecidableEq J]
variable (I : Ideal R) (a : J → I)

theorem chartRestriction_chartMorphism {s t : Finset J} (hs : s.Nonempty)
    (ht : t.Nonempty) (hst : s ⊆ t) :
    Spec.map (CommRingCat.ofHom (chartRestriction I a hst)) ≫ chartMorphism I a hs =
      chartMorphism I a ht := by
  have h := Proj.SpecMap_awayMap_awayι (piece I)
    (productGenerator_mem I a s) (Finset.card_pos.mpr hs)
    (productGenerator_mem I a (t \ s)) (productGenerator_factor I a hst)
  rw [chartMorphism_eq, chartMorphism_eq]
  unfold chartRestriction
  simpa only [Proj.awayι, Proj.basicOpenIsoSpec, affineBlowup] using h

end
end PiExponent.ReesProductSchemeRestriction

end OAI

/-
Modification notice for the LogTwo project.
Adapted from openai/math (Apache-2.0), revision adc7f1241b42e322a6451854ab7e4b4c146bf78a.
Changes: Extract generic weighted-section lemmas, change namespaces/imports and omit fixed-center wrappers.
See ../../../THIRD_PARTY_NOTICES.txt for provenance and the recorded changes.
-/

module

public import OAI.NumberTheory.PiExponent.Geometry.WeightedProjectiveEmbedding
public import OAI.NumberTheory.PiExponent.Approximation.WeightedCompactificationGeometry

@[expose] public section

/-! Generic weighted-section lemma extracted from the pinned openai/math source.
Fixed-center admissible wrappers are excluded; proof bodies are preserved.
See THIRD_PARTY_NOTICES.txt. -/


namespace LogTwo.Geometry.WeightedAffineFrame
noncomputable section
open OAI PiExponent AlgebraicGeometry CategoryTheory
open PiExponentSeshadri.Geometry PiExponentSeshadri.Projective PiExponentSeshadri.Frames
open PiExponent.WeightedCompactification

theorem frame_nonempty_of_isoOpen_eq {X : Scheme} (M : X.Modules)
    (s : O X ⟶ M) (U : X.Opens) (h : PiExponentSeshadri.SectionOpens.isoOpen s = U) :
    Nonempty (M.restrict U.ι ≅ O U.toScheme) := by
  subst U
  exact ⟨sectionFrame s⟩

variable {R ι σ : Type} [CommRing R]

attribute [local irreducible] WeightedCompactification.lineBundle
  WeightedCompactification.affineChartMap WeightedCompactification.coordinateSection

theorem affineChart_isoOpen (a : σ → ι →₀ ℕ) (z : σ) (hz : a z = 0)
    (coordinate : ι → σ) (hcoordinate : ∀ i, a (coordinate i) = Finsupp.single i 1) :
    PiExponentSeshadri.SectionOpens.isoOpen (coordinateSection (R := R) a z) =
      (affineChartMap (R := R) a z hz coordinate hcoordinate).opensRange := by
  rw [coordinateSection_isoOpen]
  apply TopologicalSpace.Opens.ext
  exact (affineChartMap_range (R := R) a z hz coordinate hcoordinate).symm

theorem affineFrame_nonempty (a : σ → ι →₀ ℕ) (z : σ) (hz : a z = 0)
    (coordinate : ι → σ) (hcoordinate : ∀ i, a (coordinate i) = Finsupp.single i 1) :
    Nonempty ((lineBundle (R := R) a).sheaf.restrict
      (affineChartMap (R := R) a z hz coordinate hcoordinate).opensRange.ι ≅
        O (affineChartMap (R := R) a z hz coordinate hcoordinate).opensRange.toScheme) :=
  frame_nonempty_of_isoOpen_eq (lineBundle (R := R) a).sheaf (coordinateSection (R := R) a z)
    (affineChartMap (R := R) a z hz coordinate hcoordinate).opensRange
    (affineChart_isoOpen (R := R) a z hz coordinate hcoordinate)

end
end LogTwo.Geometry.WeightedAffineFrame

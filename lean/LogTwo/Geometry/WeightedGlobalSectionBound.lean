/-
Modification notice for the LogTwo project.
Adapted from openai/math (Apache-2.0), revision adc7f1241b42e322a6451854ab7e4b4c146bf78a.
Changes: Extract generic weighted-section lemmas, change namespaces/imports and omit fixed-center wrappers.
See ../../../THIRD_PARTY_NOTICES.txt for provenance and the recorded changes.
-/

module

public import LogTwo.Geometry.WeightedPullbackDegree
public import OAI.NumberTheory.PiExponent.Geometry.ProjectiveCoefficientBound
public import LogTwo.Geometry.WeightedHomogeneousSubstitution

@[expose] public section

/-! Generic weighted-section lemma extracted from the pinned openai/math source.
Fixed-center admissible wrappers are excluded; proof bodies are preserved.
See THIRD_PARTY_NOTICES.txt. -/


noncomputable section
namespace LogTwo.Geometry.WeightedGlobalSectionBound
open OAI PiExponent AlgebraicGeometry CategoryTheory
open PiExponentSeshadri.Geometry
open PiExponent.WeightedCompactification PiExponent.WeightedSliceDegree
open PiExponent.AffineJetCoefficientInterface PiExponent.ProjectiveCoefficientBound
variable {K ι σ : Type} [Field K] [Fintype σ]
attribute [local irreducible] Frame Sections AffineJetCoefficientInterface.coefficient
  LineBundle.pullback EventualBound ProjectiveO1.lineBundle
  WeightedCompactification.affineChartMap

theorem eventual_supportBound (a : σ → ι →₀ ℕ) (z : σ) (hz : a z = 0)
    (coordinate : ι → σ) (hcoordinate : ∀ i, a (coordinate i) = Finsupp.single i 1)
    (ρ : ι → ℝ) (B : ℝ) (ha : ∀ j, Finsupp.weight ρ (a j) ≤ B) :
    EventualBound (affineChartMap (R := K) a z hz coordinate hcoordinate)
      (OAI.PiExponent.WeightedCompactification.lineBundle (R := K) a) ρ B := by
  let : Nonempty σ := ⟨z⟩
  apply eventual_of_homogeneous (X := Proj (imageGrade (R := K) a))
    (K := K) (ι := ι) (σ := σ) (projectiveMonomialMap (R := K) a)
    (affineChartMap (R := K) a z hz coordinate hcoordinate) ρ B
  intro n e t p hp
  exact LogTwo.Geometry.WeightedPullbackDegree.pullback_supportBound (K := K) (ι := ι) (σ := σ)
    a z hz coordinate hcoordinate ρ B ha n e t p (hp z)

end LogTwo.Geometry.WeightedGlobalSectionBound
end

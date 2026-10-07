/-
Modification notice for the LogTwo project.
Derived from openai/math (Apache-2.0), revision adc7f1241b42e322a6451854ab7e4b4c146bf78a.
Original source: lean/OAI/NumberTheory/PiExponent/Geometry/ProjectiveCoefficientBound.lean
Changes: Convert module/import declarations to the Lean 4.34 public module format.
See ../../../../../THIRD_PARTY_NOTICES.txt for provenance and the recorded changes.
-/

module

public import OAI.NumberTheory.PiExponent.Approximation.WeightedSliceDegree
public import OAI.NumberTheory.PiExponent.Geometry.ProjectiveSectionInterface

@[expose] public section

namespace OAI

noncomputable section
namespace PiExponent.ProjectiveCoefficientBound
open AlgebraicGeometry CategoryTheory
open PiExponentSeshadri.Geometry PiExponentSeshadri.Projective
open PiExponent.AffineJetCoefficientInterface PiExponent.WeightedSliceDegree

def EventualBound {X : Scheme} {K ι : Type} [Field K]
    (φ : Spec (CommRingCat.of (MvPolynomial ι K)) ⟶ X) [IsOpenImmersion φ]
    (L : LineBundle X) (ρ : ι → ℝ) (B : ℝ) : Prop :=
  ∃ N, ∀ n, N ≤ n → ∀ e : Frame φ L, ∀ s : Sections L n,
    SupportBound ρ ((n : ℝ) * B) (AffineJetCoefficientInterface.coefficient φ L n e s)

variable {X : Scheme.{0}} {K ι σ : Type} [Field K] [Fintype σ] [Nonempty σ]

def HomogeneousPullbackBound
    (f : X ⟶ ProjectiveO1.projectiveSpace K σ)
    (φ : Spec (CommRingCat.of (MvPolynomial ι K)) ⟶ X) [IsOpenImmersion φ]
    (ρ : ι → ℝ) (B : ℝ) : Prop :=
  ∀ n, ∀ e : Frame φ ((ProjectiveO1.lineBundle (R := K) (σ := σ)).pullback f),
    ∀ t : Sections (ProjectiveO1.lineBundle (R := K) (σ := σ)) n,
    ∀ p : MvPolynomial.homogeneousSubmodule σ K n,
    (∀ z, dehomogenize z p.val = ProjectiveO1.globalSectionChartPolynomial (R := K) n z
      (ProjectiveSectionInterface.sectionHom (ProjectiveO1.lineBundle (R := K) (σ := σ)) n t)) →
    SupportBound ρ ((n : ℝ) * B)
      (AffineJetCoefficientInterface.coefficient φ
        ((ProjectiveO1.lineBundle (R := K) (σ := σ)).pullback f) n e
        (ProjectiveSectionInterface.pullback (ProjectiveO1.lineBundle (R := K) (σ := σ)) f n t))

theorem eventual_of_homogeneous
    (f : X ⟶ ProjectiveO1.projectiveSpace K σ) [IsClosedImmersion f]
    (φ : Spec (CommRingCat.of (MvPolynomial ι K)) ⟶ X) [IsOpenImmersion φ]
    (ρ : ι → ℝ) (B : ℝ) (h : HomogeneousPullbackBound f φ ρ B) :
    EventualBound φ ((ProjectiveO1.lineBundle (R := K) (σ := σ)).pullback f) ρ B := by
  obtain ⟨N, hN⟩ := ProjectiveSectionInterface.eventual_homogeneous_extension f
  refine ⟨N, fun n hn e s => ?_⟩
  obtain ⟨t, p, ht, hp⟩ := hN n hn s
  rw [← ht]
  exact h n e t p hp

end PiExponent.ProjectiveCoefficientBound
end

end OAI

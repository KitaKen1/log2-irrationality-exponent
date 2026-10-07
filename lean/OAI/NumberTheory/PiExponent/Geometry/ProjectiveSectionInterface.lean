/-
Modification notice for the LogTwo project.
Derived from openai/math (Apache-2.0), revision adc7f1241b42e322a6451854ab7e4b4c146bf78a.
Original source: lean/OAI/NumberTheory/PiExponent/Geometry/ProjectiveSectionInterface.lean
Changes: Convert module/import declarations to the Lean 4.34 public module format.
See ../../../../../THIRD_PARTY_NOTICES.txt for provenance and the recorded changes.
-/

module

public import OAI.NumberTheory.PiExponent.Geometry.ProjectiveSectionPullback
public import OAI.NumberTheory.PiExponent.Jets.AffineJetCoefficientInterface

@[expose] public section

namespace OAI

namespace PiExponent.ProjectiveSectionInterface
noncomputable section
open AlgebraicGeometry CategoryTheory
open PiExponentSeshadri.Geometry
open PiExponent.AffineJetCoefficientInterface

variable {X Y : Scheme.{0}}

def sectionHom (L : LineBundle X) (n : ℕ) :
    Sections L n → GlobalSections X (modulePow X L.sheaf n) := fun s => s

def ofSectionHom (L : LineBundle X) (n : ℕ) :
    GlobalSections X (modulePow X L.sheaf n) → Sections L n := fun s => s

@[simp]
theorem sectionHom_ofSectionHom (L : LineBundle X) (n : ℕ)
    (s : GlobalSections X (modulePow X L.sheaf n)) :
    sectionHom L n (ofSectionHom L n s) = s := rfl

@[simp]
theorem ofSectionHom_sectionHom (L : LineBundle X) (n : ℕ) (s : Sections L n) :
    ofSectionHom L n (sectionHom L n s) = s := rfl

theorem sectionHom_injective (L : LineBundle X) (n : ℕ) :
    Function.Injective (sectionHom L n) := fun _ _ h => h

def pullback (L : LineBundle Y) (f : X ⟶ Y) (n : ℕ) :
    Sections L n → Sections (L.pullback f) n := fun s =>
  ofSectionHom (L.pullback f) n (pullbackPowerSection L f n (sectionHom L n s))

@[simp]
theorem sectionHom_pullback (L : LineBundle Y) (f : X ⟶ Y) (n : ℕ)
    (s : Sections L n) :
    sectionHom (L.pullback f) n (pullback L f n s) =
      pullbackPowerSection L f n (sectionHom L n s) := rfl

attribute [local irreducible] AffineJetCoefficientInterface.Frame
  AffineJetCoefficientInterface.Sections

theorem eventual_homogeneous_extension
    {R σ : Type} [CommRing R] [IsNoetherianRing R] [Fintype σ] [Nonempty σ]
    (f : X ⟶ ProjectiveO1.projectiveSpace R σ) [IsClosedImmersion f] :
    ∃ N, ∀ n, N ≤ n →
      ∀ s : Sections ((ProjectiveO1.lineBundle (R := R) (σ := σ)).pullback f) n,
      ∃ t : Sections (ProjectiveO1.lineBundle (R := R) (σ := σ)) n,
      ∃ p : MvPolynomial.homogeneousSubmodule σ R n,
        pullback (ProjectiveO1.lineBundle (R := R) (σ := σ)) f n t = s ∧
        ∀ z, PiExponentSeshadri.Projective.dehomogenize z p.val =
          ProjectiveO1.globalSectionChartPolynomial n z
            (sectionHom (ProjectiveO1.lineBundle (R := R) (σ := σ)) n t) := by
  obtain ⟨N, hN⟩ := ProjectiveSectionExtension.eventual_projective_homogeneous_extension f
  refine ⟨N, fun n hn s => ?_⟩
  obtain ⟨t, p, ht, hp⟩ := hN n hn
    (sectionHom ((ProjectiveO1.lineBundle (R := R) (σ := σ)).pullback f) n s)
  refine ⟨ofSectionHom (ProjectiveO1.lineBundle (R := R) (σ := σ)) n t, p, ?_, ?_⟩
  · apply sectionHom_injective ((ProjectiveO1.lineBundle (R := R) (σ := σ)).pullback f) n
    rw [sectionHom_pullback, sectionHom_ofSectionHom, ht]
  · simpa only [sectionHom_ofSectionHom] using hp

end
end PiExponent.ProjectiveSectionInterface

end OAI

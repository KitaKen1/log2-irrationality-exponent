/-
Modification notice for the LogTwo project.
Derived from openai/math (Apache-2.0), revision adc7f1241b42e322a6451854ab7e4b4c146bf78a.
Original source: lean/OAI/NumberTheory/PiExponent/Geometry/WeightedProjectiveLineBundle.lean
Changes: Convert module/import declarations to the Lean 4.34 public module format.
See ../../../../../THIRD_PARTY_NOTICES.txt for provenance and the recorded changes.
-/

module

public import OAI.NumberTheory.PiExponent.Approximation.FramedPullback
public import OAI.NumberTheory.PiExponent.Geometry.ProjectiveO1Sections
public import OAI.NumberTheory.PiExponent.Geometry.WeightedProjectiveStructure

@[expose] public section

namespace OAI

noncomputable section

namespace PiExponent.WeightedCompactification

open AlgebraicGeometry CategoryTheory TopologicalSpace
open PiExponentSeshadri.Geometry PiExponentSeshadri.Frames PiExponentSeshadri.LineBundleGluing

variable {R ι σ : Type} [CommRing R]

def lineBundle (a : σ → ι →₀ ℕ) : LineBundle (Proj (imageGrade (R := R) a)) :=
  (ProjectiveO1.lineBundle (R := R) (σ := σ)).pullback (projectiveMonomialMap a)

def coordinateSection (a : σ → ι →₀ ℕ) (s : σ) :
    O (Proj (imageGrade (R := R) a)) ⟶ (lineBundle a).sheaf :=
  pullbackSection (projectiveMonomialMap a) (ProjectiveO1.coordinateSection s)

theorem lineBundle_closedImmersion_witness (a : σ → ι →₀ ℕ) :
    ∃ f : Proj (imageGrade (R := R) a) ⟶ ProjectiveO1.projectiveSpace R σ,
      IsClosedImmersion f ∧
      Nonempty ((lineBundle a).sheaf ≅
        (Scheme.Modules.pullback f).obj (ProjectiveO1.lineBundle (R := R) (σ := σ)).sheaf) := by
  exact ⟨projectiveMonomialMap a, inferInstance, ⟨Iso.refl _⟩⟩


theorem coordinateSection_frame (a : σ → ι →₀ ℕ) (i s : σ) :
    ∃ e : (lineBundle (R := R) a).sheaf.restrict
        (projectiveMonomialMap a ⁻¹ᵁ ProjectiveO1.coordinateOpen i).ι ≅
          O (projectiveMonomialMap a ⁻¹ᵁ ProjectiveO1.coordinateOpen i).toScheme,
      coefficient e
        (restrictSection (projectiveMonomialMap a ⁻¹ᵁ ProjectiveO1.coordinateOpen i).ι
          (coordinateSection a s)) =
        (projectiveMonomialMap a ∣_ ProjectiveO1.coordinateOpen i).appTop
          ((ProjectiveO1.coordinateOpen i).topIso.inv
            (ProjectiveO1.coordinateRatio i s (ProjectiveO1.coordinateOpen i) le_rfl)) := by
  obtain ⟨e, he⟩ := exists_restricted_pullback_frame (projectiveMonomialMap (R := R) a)
    (ProjectiveO1.coordinateOpen i)
    (openFrame ProjectiveO1.coordinateCocycle i (ProjectiveO1.coordinateOpen i) le_rfl)
    (ProjectiveO1.coordinateSection s)
  exact ⟨e, he.trans (congrArg
    (fun c => (projectiveMonomialMap (R := R) a ∣_ ProjectiveO1.coordinateOpen i).appTop c)
    (ProjectiveO1.coordinateSection_coefficient_eq i s (ProjectiveO1.coordinateOpen i) le_rfl))⟩

end PiExponent.WeightedCompactification

end

end OAI

/-
Modification notice for the LogTwo project.
Derived from openai/math (Apache-2.0), revision adc7f1241b42e322a6451854ab7e4b4c146bf78a.
Original source: lean/OAI/NumberTheory/PiExponent/Ampleness/ExceptionalRepresentedOpaque.lean
Changes: Convert module/import declarations to the Lean 4.34 public module format.
Expose private helpers and adjust helper names where needed for module compatibility.
See ../../../../../THIRD_PARTY_NOTICES.txt for provenance and the recorded changes.
-/

module

public import OAI.NumberTheory.PiExponent.Ampleness.ExceptionalRepresentedValue

@[expose] public section

namespace OAI

namespace PiExponent.ExceptionalAffineChart
noncomputable section
open CategoryTheory AlgebraicGeometry
open PiExponentSeshadri.Geometry PiExponentSeshadri.Frames
open PiExponentSeshadri.ModuleFlasque PiExponentSeshadri.IdealPullback
abbrev exceptionalOpaqueFreeOpen (Y : Scheme) (U : Y.Opens) : Y.Modules :=
  freeOpen Y.ringCatSheaf U

variable {R A : Type} [CommRing R] [CommRing A] {Y : Scheme}
variable (I : Ideal R) (f : Y ⟶ Spec (CommRingCat.of R))
  (j : Spec (CommRingCat.of A) ⟶ Y) [IsOpenImmersion j]
  (φ : R →+* A) (hf : j ≫ f = Spec.map (CommRingCat.ofHom φ))
  (L : LineBundle Y) (ι : L.sheaf ⟶ O Y)
  (hL : PresentsPullbackIdeal (specIdeal I) f L ι)
  (e : L.sheaf.restrict (chartOpen j).1.ι ≅ O (chartOpen j).1.toScheme)

theorem exists_representedSectionsOpaque (n : ℕ) :
    ∃ E : (exceptionalOpaqueFreeOpen Y j.opensRange ⟶ (L.pow n).sheaf) ≃+
      ↥((I^n).map φ), E = representedSectionsEquiv I f j φ hf L ι hL e n :=
  ⟨_, rfl⟩

def representedSectionsOpaque (n : ℕ) :
    (exceptionalOpaqueFreeOpen Y j.opensRange ⟶ (L.pow n).sheaf) ≃+ ↥((I^n).map φ) :=
  (exists_representedSectionsOpaque I f j φ hf L ι hL e n).choose

theorem representedSectionsOpaque_eq (n : ℕ) :
    representedSectionsOpaque I f j φ hf L ι hL e n =
      representedSectionsEquiv I f j φ hf L ι hL e n :=
  (exists_representedSectionsOpaque I f j φ hf L ι hL e n).choose_spec

theorem representedSectionsOpaque_apply (n : ℕ)
    (b : exceptionalOpaqueFreeOpen Y j.opensRange ⟶ (L.pow n).sheaf) :
    representedSectionsOpaque I f j φ hf L ι hL e n b =
      representedSectionsEquiv I f j φ hf L ι hL e n b :=
  congrArg (fun E => E b) (representedSectionsOpaque_eq I f j φ hf L ι hL e n)

end
end PiExponent.ExceptionalAffineChart

end OAI

/-
Modification notice for the LogTwo project.
Derived from openai/math (Apache-2.0), revision adc7f1241b42e322a6451854ab7e4b4c146bf78a.
Original source: lean/OAI/NumberTheory/PiExponent/Ampleness/ExceptionalTypedTransport.lean
Changes: Convert module/import declarations to the Lean 4.34 public module format.
Expose private helpers and adjust helper names where needed for module compatibility.
See ../../../../../THIRD_PARTY_NOTICES.txt for provenance and the recorded changes.
-/

module

public import OAI.NumberTheory.PiExponent.Ampleness.ExceptionalRepresentedTypes

@[expose] public section

namespace OAI

namespace PiExponent.ExceptionalRepresentedTypes
noncomputable section
open CategoryTheory AlgebraicGeometry
open PiExponentSeshadri.Geometry PiExponentSeshadri.Frames
open PiExponentSeshadri.ModuleFlasque
abbrev schemeFreeOpen (Y : Scheme) (U : Y.Opens) : Y.Modules :=
  freeOpen Y.ringCatSheaf U

variable {A : Type} [CommRing A] {Y : Scheme}
variable (j : Spec (CommRingCat.of A) ⟶ Y) [IsOpenImmersion j]
  (L : LineBundle Y)

theorem frame_nonempty_of_open {U : Y.Opens} (h : U = j.opensRange)
    (he : Nonempty (L.sheaf.restrict U.ι ≅ O U.toScheme)) :
    Nonempty (Frame j L) := by
  subst U
  exact he

def transportSections (n : ℕ) {V : Y.Opens} (h : j.opensRange = V) :
    (schemeFreeOpen Y V ⟶ (L.pow n).sheaf) ≃+ Sections j L n where
  toFun b := freeOpenMap Y.ringCatSheaf (eqToHom h) ≫ b
  invFun b := freeOpenMap Y.ringCatSheaf (eqToHom h.symm) ≫ b
  left_inv b := by
    subst V
    simp [freeOpenMap]
    exact (Category.id_comp _).trans (Category.id_comp b)
  right_inv b := by
    subst V
    simp [freeOpenMap]
    exact (Category.id_comp _).trans (Category.id_comp b)
  map_add' b c := Preadditive.comp_add _ _ _ _ b c

theorem transportSections_apply (n : ℕ) {V : Y.Opens} (h : j.opensRange = V)
    (b : schemeFreeOpen Y V ⟶ (L.pow n).sheaf) :
    transportSections j L n h b = freeOpenMap Y.ringCatSheaf (eqToHom h) ≫ b := rfl

end
end PiExponent.ExceptionalRepresentedTypes

end OAI

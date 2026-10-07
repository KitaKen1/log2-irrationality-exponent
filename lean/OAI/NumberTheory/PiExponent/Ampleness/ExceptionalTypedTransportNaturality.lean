/-
Modification notice for the LogTwo project.
Derived from openai/math (Apache-2.0), revision adc7f1241b42e322a6451854ab7e4b4c146bf78a.
Original source: lean/OAI/NumberTheory/PiExponent/Ampleness/ExceptionalTypedTransportNaturality.lean
Changes: Convert module/import declarations to the Lean 4.34 public module format.
See ../../../../../THIRD_PARTY_NOTICES.txt for provenance and the recorded changes.
-/

module

public import OAI.NumberTheory.PiExponent.Ampleness.ExceptionalTypedRestriction
public import OAI.NumberTheory.PiExponent.Ampleness.ExceptionalTypedTransport

@[expose] public section

namespace OAI

namespace PiExponent.ExceptionalRepresentedTypes
noncomputable section
open CategoryTheory AlgebraicGeometry
open PiExponentSeshadri.Geometry PiExponentSeshadri.ModuleFlasque
variable {A B : Type} [CommRing A] [CommRing B] {Y : Scheme}
variable (j : Spec (CommRingCat.of A) ⟶ Y) [IsOpenImmersion j]
  (j' : Spec (CommRingCat.of B) ⟶ Y) [IsOpenImmersion j']
  (θ : A →+* B) (hchart : Spec.map (CommRingCat.ofHom θ) ≫ j = j')

theorem transportSections_restrict (L : LineBundle Y) (n : ℕ)
    {U V : Y.Opens} (hU : j.opensRange = U) (hV : j'.opensRange = V)
    (hVU : V ≤ U) (b : freeOpen Y.ringCatSheaf U ⟶ (L.pow n).sheaf) :
    transportSections j' L n hV (freeOpenMap Y.ringCatSheaf (homOfLE hVU) ≫ b) =
      restrictSections j j' θ hchart L n (transportSections j L n hU b) := by
  subst U V
  simp [transportSections, restrictSections, freeOpenMap]
  change (𝟙 _ ≫ (freeOpenMap Y.ringCatSheaf (homOfLE hVU) ≫ b)) =
    freeOpenMap Y.ringCatSheaf (homOfLE hVU) ≫ (𝟙 _ ≫ b)
  exact (Category.id_comp _).trans
    (congrArg (fun c => freeOpenMap Y.ringCatSheaf (homOfLE hVU) ≫ c)
      (Category.id_comp b).symm)

end
end PiExponent.ExceptionalRepresentedTypes

end OAI

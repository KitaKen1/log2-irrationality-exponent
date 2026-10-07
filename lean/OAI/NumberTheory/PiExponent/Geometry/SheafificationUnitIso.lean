/-
Modification notice for the LogTwo project.
Derived from openai/math (Apache-2.0), revision adc7f1241b42e322a6451854ab7e4b4c146bf78a.
Original source: lean/OAI/NumberTheory/PiExponent/Geometry/SheafificationUnitIso.lean
Changes: Convert module/import declarations to the Lean 4.34 public module format.
See ../../../../../THIRD_PARTY_NOTICES.txt for provenance and the recorded changes.
-/

module

public import OAI.NumberTheory.PiExponent.Approximation.TensorPure

@[expose] public section

namespace OAI

namespace PiExponentSeshadri.Geometry
noncomputable section
open AlgebraicGeometry CategoryTheory
variable {X : Scheme}

theorem sheafification_unit_isIso (M : X.Modules) :
    IsIso ((PiExponentSeshadri.TensorPure.adj X).unit.app M.val) := by
  exact (PiExponentSeshadri.TensorPure.adj X).isIso_unit_app_of_iso (Iso.refl M.val)

theorem sheafification_unit_isIso_of_iso (P : PresheafOfModules X.ringCatSheaf.obj)
    (M : X.Modules) (e : P ≅ M.val) :
    IsIso ((PiExponentSeshadri.TensorPure.adj X).unit.app P) :=
  (PiExponentSeshadri.TensorPure.adj X).isIso_unit_app_of_iso e

end
end PiExponentSeshadri.Geometry

end OAI

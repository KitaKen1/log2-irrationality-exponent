/-
Modification notice for the LogTwo project.
Derived from openai/math (Apache-2.0), revision adc7f1241b42e322a6451854ab7e4b4c146bf78a.
Original source: lean/OAI/NumberTheory/PiExponent/Geometry/LineBundleCoherent.lean
Changes: Convert module/import declarations to the Lean 4.34 public module format.
See ../../../../../THIRD_PARTY_NOTICES.txt for provenance and the recorded changes.
-/

module

public import OAI.NumberTheory.PiExponent.LocalAlgebra.FiniteGlobalPresentation

@[expose] public section

namespace OAI

namespace PiExponent.GeometrySupport.LineBundleCoherent

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open PiExponentSeshadri.Geometry

variable {X : Scheme}

theorem structureSheaf_isFinitePresentation : (structureSheaf X).IsFinitePresentation := by
  let e : SheafOfModules.free (R := X.ringCatSheaf) PUnit ≅ structureSheaf X :=
    coproductUniqueIso (fun _ : PUnit => structureSheaf X)
  exact (SheafOfModules.isFinitePresentation X.ringCatSheaf).prop_of_iso e
    (PiExponent.FiniteGlobalPresentation.free_isFinitePresentation X PUnit)

theorem lineBundle_isFinitePresentation (L : LineBundle X) : L.sheaf.IsFinitePresentation := by
  let : (structureSheaf X).IsFinitePresentation := structureSheaf_isFinitePresentation
  apply PiExponent.FiniteGlobalPresentation.isFinitePresentation_of_locally_iso
    (structureSheaf X) L.sheaf
  intro x
  obtain ⟨U, hx, ⟨e⟩⟩ := L.locallyRankOne x
  exact ⟨U, hx, ⟨e ≪≫ (Scheme.Modules.restrictUnitIso U.ι).symm⟩⟩

theorem modulePow_isFinitePresentation (L : LineBundle X) (n : ℕ) :
    (modulePow X L.sheaf n).IsFinitePresentation :=
  lineBundle_isFinitePresentation (L.pow n)

theorem modulePow_isQuasicoherent (L : LineBundle X) (n : ℕ) :
    (modulePow X L.sheaf n).IsQuasicoherent := by
  have := modulePow_isFinitePresentation L n
  exact (SheafOfModules.IsFinitePresentation.exists_quasicoherentData
    (modulePow X L.sheaf n)).choose.isQuasicoherent

end
end PiExponent.GeometrySupport.LineBundleCoherent

end OAI

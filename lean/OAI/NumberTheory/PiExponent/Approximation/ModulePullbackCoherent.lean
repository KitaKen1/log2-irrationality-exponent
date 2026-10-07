/-
Modification notice for the LogTwo project.
Derived from openai/math (Apache-2.0), revision adc7f1241b42e322a6451854ab7e4b4c146bf78a.
Original source: lean/OAI/NumberTheory/PiExponent/Approximation/ModulePullbackCoherent.lean
Changes: Convert module/import declarations to the Lean 4.34 public module format.
Expose private helpers and adjust helper names where needed for module compatibility.
See ../../../../../THIRD_PARTY_NOTICES.txt for provenance and the recorded changes.
-/

module

public import OAI.NumberTheory.PiExponent.Approximation.FramedPullback
public import OAI.NumberTheory.PiExponent.LocalAlgebra.FiniteGlobalPresentation

@[expose] public section

namespace OAI

namespace PiExponentSeshadri.Geometry
noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace
open PiExponent.FiniteGlobalPresentation

def presentationOfIso (X : Scheme.{0})
    {M N : SheafOfModules X.ringCatSheaf} (e : M ≅ N)
    (P : M.Presentation) : N.Presentation := by
  let : IsIso e.hom := e.isIso_hom
  exact P.ofIsIso e.hom

theorem pullback_isFinitePresentation {X Y : Scheme.{0}} (f : Y ⟶ X)
    (M : X.Modules) [M.IsFinitePresentation] :
    ((Scheme.Modules.pullback f).obj M).IsFinitePresentation := by
  apply isFinitePresentation_of_localPresentations
  intro y
  obtain ⟨U, hy, P, hP⟩ := exists_local_finitePresentation M (f y)
  let F : SheafOfModules U.toScheme.ringCatSheaf ⥤
      SheafOfModules (f ⁻¹ᵁ U).toScheme.ringCatSheaf :=
    Scheme.Modules.pullback (f ∣_ U)
  let : PreservesColimitsOfSize.{0,0} F :=
    (Scheme.Modules.pullbackPushforwardAdjunction (f ∣_ U)).leftAdjoint_preservesColimits
  let Q := P.map F (pullbackUnitIso (f ∣_ U)).symm
  let e := (pullbackRestrictNatIso f U).app M
  exact ⟨f ⁻¹ᵁ U, hy, presentationOfIso (f ⁻¹ᵁ U).toScheme e.symm Q,
    ⟨⟨hP.isFiniteType_generators.finite⟩, ⟨hP.isFiniteType_relations.finite⟩⟩⟩

end
end PiExponentSeshadri.Geometry

end OAI

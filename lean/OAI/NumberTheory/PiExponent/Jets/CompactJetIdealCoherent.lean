/-
Modification notice for the LogTwo project.
Derived from openai/math (Apache-2.0), revision adc7f1241b42e322a6451854ab7e4b4c146bf78a.
Original source: lean/OAI/NumberTheory/PiExponent/Jets/CompactJetIdealCoherent.lean
Changes: Convert module/import declarations to the Lean 4.34 public module format.
See ../../../../../THIRD_PARTY_NOTICES.txt for provenance and the recorded changes.
-/

module

public import OAI.NumberTheory.PiExponent.Approximation.ClosedPushforwardCoherent
public import OAI.NumberTheory.PiExponent.Geometry.LineBundleCoherent
public import OAI.NumberTheory.PiExponent.Jets.CompactJetIdeal
public import OAI.NumberTheory.PiExponent.LocalAlgebra.IdealModule

@[expose] public section

namespace OAI

noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
namespace PiExponent.CompactJetIdeal


theorem closedModule_isFinitePresentation {X : Scheme} [IsLocallyNoetherian X]
    (I : X.IdealSheafData) :
    (PiExponentSeshadri.IdealModule.closedModule I).IsFinitePresentation := by
  let : (PiExponentSeshadri.IdealModule.unit X).IsFinitePresentation :=
    GeometrySupport.LineBundleCoherent.structureSheaf_isFinitePresentation
  let : (PiExponentSeshadri.IdealModule.unit I.subscheme).IsFinitePresentation :=
    GeometrySupport.LineBundleCoherent.structureSheaf_isFinitePresentation
  let : ((Scheme.Modules.pushforward I.subschemeι).obj
      (PiExponentSeshadri.IdealModule.unit I.subscheme)).IsQuasicoherent :=
    (SheafOfModules.IsFinitePresentation.exists_quasicoherentData
      ((Scheme.Modules.pushforward I.subschemeι).obj
        (PiExponentSeshadri.IdealModule.unit I.subscheme))).choose.isQuasicoherent
  exact FiniteGlobalPresentation.kernel_isFinitePresentation
    (PiExponentSeshadri.IdealModule.structureMap I.subschemeι)

theorem extend_isFinitePresentation {U X : Scheme} [IsLocallyNoetherian X]
    (I : U.IdealSheafData) (j : U ⟶ X) :
    (PiExponentSeshadri.IdealModule.closedModule (extend I j)).IsFinitePresentation :=
  closedModule_isFinitePresentation (extend I j)

end PiExponent.CompactJetIdeal
end

end OAI

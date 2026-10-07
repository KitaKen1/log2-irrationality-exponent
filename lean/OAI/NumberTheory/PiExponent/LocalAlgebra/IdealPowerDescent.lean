/-
Modification notice for the LogTwo project.
Derived from openai/math (Apache-2.0), revision adc7f1241b42e322a6451854ab7e4b4c146bf78a.
Original source: lean/OAI/NumberTheory/PiExponent/LocalAlgebra/IdealPowerDescent.lean
Changes: Convert module/import declarations to the Lean 4.34 public module format.
See ../../../../../THIRD_PARTY_NOTICES.txt for provenance and the recorded changes.
-/

module

public import OAI.NumberTheory.PiExponent.Approximation.GlobalClosedAnnihilatedDescent
public import OAI.NumberTheory.PiExponent.Approximation.ModulePullbackCoherent
public import OAI.NumberTheory.PiExponent.LocalAlgebra.IdealPowerRestriction

@[expose] public section

namespace OAI

namespace PiExponentSeshadri.IdealModule
noncomputable section
open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite
open PiExponentSeshadri.Geometry PiExponentSeshadri.ClosedAnnihilatedDescent
variable {X : Scheme.{0}}

theorem powerLayer_locallyAnnihilated (I : X.IdealSheafData) (n : ℕ) :
    LocallyAnnihilated I.subschemeι (powerLayer I n) := by
  intro U r hr
  apply Module.mem_annihilator.mpr
  intro x
  exact powerLayer_restrict_kernel_smul_eq_zero I n U r hr x

def descendedPowerLayer (I : X.IdealSheafData) (n : ℕ) : I.subscheme.Modules :=
  (Scheme.Modules.pullback I.subschemeι).obj (powerLayer I n)

instance descendedPowerLayer_isFinitePresentation [IsLocallyNoetherian X]
    (I : X.IdealSheafData) (n : ℕ) : (descendedPowerLayer I n).IsFinitePresentation := by
  have := powerLayer_isFinitePresentation I n
  exact pullback_isFinitePresentation I.subschemeι (powerLayer I n)

def powerLayerPushforwardIso [IsLocallyNoetherian X] (I : X.IdealSheafData) (n : ℕ) :
    (Scheme.Modules.pushforward I.subschemeι).obj (descendedPowerLayer I n) ≅ powerLayer I n := by
  have := powerLayer_isFinitePresentation I n
  let : (powerLayer I n).IsQuasicoherent :=
    (SheafOfModules.IsFinitePresentation.exists_quasicoherentData
      (powerLayer I n)).choose.isQuasicoherent
  exact closedDescentPushforwardIso I.subschemeι (powerLayer I n)
    (powerLayer_locallyAnnihilated I n)

end
end PiExponentSeshadri.IdealModule

end OAI

/-
Modification notice for the LogTwo project.
Derived from openai/math (Apache-2.0), revision adc7f1241b42e322a6451854ab7e4b4c146bf78a.
Original source: lean/OAI/NumberTheory/PiExponent/Approximation/GlobalClosedAnnihilatedDescent.lean
Changes: Convert module/import declarations to the Lean 4.34 public module format.
See ../../../../../THIRD_PARTY_NOTICES.txt for provenance and the recorded changes.
-/

module

public import OAI.NumberTheory.PiExponent.Approximation.AffineClosedAnnihilatedDescent
public import OAI.NumberTheory.PiExponent.Approximation.ClosedImmersionModules
public import OAI.NumberTheory.PiExponent.Approximation.ClosedPullbackUnitRestriction
public import OAI.NumberTheory.PiExponent.Approximation.ModulePullbackCoherent

@[expose] public section

namespace OAI

namespace PiExponentSeshadri.ClosedAnnihilatedDescent
noncomputable section
open CategoryTheory AlgebraicGeometry TopologicalSpace Opposite
variable {X Y : Scheme.{0}} (f : Y ⟶ X)

def LocallyAnnihilated (M : X.Modules) : Prop :=
  ∀ U : X.affineOpens,
    RingHom.ker (f ∣_ U.1).appTop.hom ≤
      Module.annihilator Γ(U.1.toScheme,⊤) Γ(M.restrict U.1.ι,⊤)

theorem unit_isIso_of_locallyAnnihilated [IsClosedImmersion f]
    (M : X.Modules) [M.IsQuasicoherent] (h : LocallyAnnihilated f M) :
    IsIso ((Scheme.Modules.pullbackPushforwardAdjunction f).unit.app M) := by
  apply ClosedPullbackUnitRestriction.unit_isIso_of_affine f M
  intro U
  let : IsAffine U.1.toScheme := U.2
  obtain ⟨N, ⟨e⟩⟩ := exists_affine_closed_descent (f ∣_ U.1) (M.restrict U.1.ι) (h U)
  exact ClosedImmersionModules.unit_isIso_of_pushforward (f ∣_ U.1) e.symm

def closedDescentPushforwardIso [IsClosedImmersion f]
    (M : X.Modules) [M.IsQuasicoherent] (h : LocallyAnnihilated f M) :
    (Scheme.Modules.pushforward f).obj ((Scheme.Modules.pullback f).obj M) ≅ M := by
  let := unit_isIso_of_locallyAnnihilated f M h
  exact (asIso ((Scheme.Modules.pullbackPushforwardAdjunction f).unit.app M)).symm

theorem exists_closed_descent [IsClosedImmersion f]
    (M : X.Modules) [M.IsQuasicoherent] (h : LocallyAnnihilated f M) :
    ∃ N : Y.Modules, Nonempty ((Scheme.Modules.pushforward f).obj N ≅ M) :=
  ⟨(Scheme.Modules.pullback f).obj M, ⟨closedDescentPushforwardIso f M h⟩⟩

theorem exists_closed_coherent_descent [IsClosedImmersion f]
    (M : X.Modules) [M.IsFinitePresentation] (h : LocallyAnnihilated f M) :
    ∃ N : Y.Modules, N.IsFinitePresentation ∧
      Nonempty ((Scheme.Modules.pushforward f).obj N ≅ M) := by
  let : M.IsQuasicoherent :=
    (SheafOfModules.IsFinitePresentation.exists_quasicoherentData M).choose.isQuasicoherent
  exact ⟨(Scheme.Modules.pullback f).obj M, Geometry.pullback_isFinitePresentation f M,
    ⟨closedDescentPushforwardIso f M h⟩⟩

end
end PiExponentSeshadri.ClosedAnnihilatedDescent

end OAI

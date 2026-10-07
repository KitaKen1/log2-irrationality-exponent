module
public meta import Lean.Elab.Tactic
public meta import Lean.Elab.BuiltinEvalCommand
public import Lean.Elab.Tactic
@[expose] public section
-- Browser memory improvement: omit proof-internal goal/hover history for dependencies.
-- Outer command information remains, as required by rc4's language server.
-- Proof elaboration, kernel checking, errors and the final axiom audit remain enabled.
set_option Elab.async false
set_option linter.all false
namespace LogTwoWebMemory
syntax (name := quietProof) "logtwo_quiet " tacticSeq : tactic
@[tactic quietProof] meta def evalQuietProof : Lean.Elab.Tactic.Tactic :=
  fun stx => Lean.Elab.withEnableInfoTree false do
    Lean.Elab.Tactic.evalTactic stx[1]
end LogTwoWebMemory

theorem paste_hidden : 2 + 3 = 3 + 2 := by logtwo_quiet
  exact Nat.add_comm 2 3
example : False := by logtwo_quiet exact True.intro

-- The independent public definition and final target use normal editor information.
-- Proof-internal wrappers are only inserted in the dependency blocks above.

run_cmd Lean.logInfo m!"PASTE_OUTER_INFO={(← Lean.Elab.getInfoState).enabled}"
theorem paste_visible : 2 + 3 = 3 + 2 := by
  exact Nat.add_comm 2 3
#print axioms paste_hidden
#print axioms paste_visible
run_cmd Lean.logInfo "PASTE_EDITOR_DONE"

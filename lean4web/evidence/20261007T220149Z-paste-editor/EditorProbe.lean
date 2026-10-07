module
public meta import Lean.Elab.Term
public meta import Lean.Elab.BuiltinEvalCommand
public import Lean.Elab.Tactic
@[expose] public section
-- Browser memory improvement: omit proof-internal goal/hover history for dependencies.
-- Outer command information remains, as required by rc4's language server.
-- Proof elaboration, kernel checking, errors and the final axiom audit remain enabled.
set_option Elab.async false
set_option linter.all false
namespace LogTwoWebMemory
syntax (name := quietProof) "logtwo_quiet% " term : term
@[term_elab quietProof] meta def elabQuietProof : Lean.Elab.Term.TermElab :=
  fun stx expectedType? => Lean.Elab.withEnableInfoTree false do
    Lean.Elab.Term.elabTerm stx[1] expectedType?
end LogTwoWebMemory

theorem paste_hidden : 2 + 3 = 3 + 2 := logtwo_quiet% by
  exact Nat.add_comm 2 3
example : False := logtwo_quiet% by exact True.intro

-- The independent public definition and final target use normal editor information.
-- Proof-internal wrappers are only inserted in the dependency blocks above.

run_cmd Lean.logInfo m!"PASTE_OUTER_INFO={(← Lean.Elab.getInfoState).enabled}"
theorem paste_visible : 2 + 3 = 3 + 2 := by
  exact Nat.add_comm 2 3
#print axioms paste_hidden
#print axioms paste_visible
run_cmd Lean.logInfo "PASTE_EDITOR_DONE"

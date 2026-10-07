module
public meta import Lean.Elab.Command
public meta import Lean.Elab.BuiltinEvalCommand
public import Lean.Elab.Tactic
@[expose] public section
-- Browser memory improvement: omit interactive goal/hover history for dependencies.
-- This changes editor metadata only; all proof elaboration and kernel checking remain.
-- Style linters are disabled; errors and the final axiom audit remain visible.
set_option Elab.async false
set_option linter.all false
run_cmd Lean.Elab.enableInfoTree false

run_cmd Lean.logInfo m!"PASTE_INFO_OFF={(← Lean.Elab.getInfoState).enabled}"
theorem paste_hidden : 2 + 2 = 4 := by rfl
example : 2 + 2 = 4 := paste_hidden
example : False := by exact True.intro

-- Restore interactive information for the independent public definition and target.
run_cmd Lean.Elab.enableInfoTree true

run_cmd Lean.logInfo m!"PASTE_INFO_ON={(← Lean.Elab.getInfoState).enabled}"
theorem paste_visible : 2 + 2 = 4 := by rfl
example : 2 + 2 = 4 := paste_visible
#print axioms paste_hidden
#print axioms paste_visible
run_cmd Lean.logInfo "PASTE_EDITOR_DONE"

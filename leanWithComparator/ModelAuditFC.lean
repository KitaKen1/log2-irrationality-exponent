import SolutionFC
import Mathlib

/-! Check the exact compiled definition and target against the raw PR snapshot.
The PR's mathematical namespace body is unchanged; only imports are adapted
from FC's Lean 4.33.1 to the pinned proof's Lean 4.34.1. -/
open Lean Elab Command Meta in
run_cmd do
  let (data, _) ← readModuleData (← findOLean `RawPRFC)
  let mut reference : NameMap ConstantInfo := {}
  for info in data.constants do
    reference := reference.insert info.name info
  let models := #[`LogTwo.irrationalityExponent]
  let targets := #[`LogTwo.irrationalityExponent_log_two]
  for name in models ++ targets do
    let some original := reference.find? name
      | throwError "Missing raw PR declaration: {name}"
    liftTermElabM do
      let proved ← getConstInfo name
      unless proved.levelParams == original.levelParams &&
          (← isDefEq proved.type original.type) do
        throwError "Raw PR declaration type mismatch: {name}"
      if models.contains name then
        match proved.value?, original.value? with
        | some a, some b =>
          unless ← isDefEq a b do
            throwError "Raw PR definition mismatch: {name}"
        | none, none => pure ()
        | _, _ => throwError "Raw PR declaration kind mismatch: {name}"
  logInfo m!"Exact raw PR model/target agreement: {models.size + targets.size} declarations"

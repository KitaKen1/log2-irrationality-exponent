import LogTwo.Target
import Lean

open Lean Elab Command in
set_option maxHeartbeats 0 in
run_cmd do
  let env ← getEnv
  let rows ← env.constants.foldM (init := #[]) fun rows name ci => do
    let some mod ← findModuleOf? name | return rows
    let modName := mod.toString
    unless modName.startsWith "LogTwo" || modName.startsWith "OAI." do
      return rows
    let mut deps := ci.type.getUsedConstants
    if let some value := ci.value? true then
      deps := deps ++ value.getUsedConstants
    let row := Json.mkObj [
      ("name", toJson name.toString),
      ("module", toJson modName),
      ("dependencies", toJson (deps.map Name.toString))]
    return rows.push row
  liftIO <| IO.FS.writeFile "evidence/declaration-dependencies.json" (Json.arr rows).compress
  logInfo m!"Exported kernel dependency references for {rows.size} declarations"

#print axioms LogTwo.irrationalityExponent_log_two

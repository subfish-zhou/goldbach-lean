import Lean

/-! Parser-backed proof-body source positions. Never rewrite equation/where declarations. -/
namespace ProofOpt.SourceSpan
open Lean Elab Command

partial def outerValues (stx : Syntax) : Array Syntax :=
  if stx.isOfKind ``Parser.Command.declValSimple then #[stx]
  else stx.getArgs.foldl (fun out s => out ++ outerValues s) #[]

syntax "#proofopt_body " str : command
elab_rules : command
  | `(#proofopt_body $path:str) => do
    let text ← IO.FS.readFile path.getString
    let parsed ← match Parser.runParserCategory (← getEnv) `command text with
      | .ok s => pure s
      | .error e => throwError "source parser rejected declaration: {e}"
    let values := outerValues parsed
    unless values.size == 1 do throwError "expected exactly one simple declaration body"
    let value := values[0]!
    unless value.getArgs.size == 4 do throwError "unsupported declValSimple parser schema"
    unless value[2].getPos?.isNone && value[3].getPos?.isNone do
      throwError "termination/where suffix requires a dedicated rewrite"
    let body := value[1]
    let some start := body.getPos? | throwError "missing original body start"
    let some stop := body.getTailPos? | throwError "missing original body end"
    logInfo m!"PROOFOPT_BODY {(Json.mkObj [("start_byte", toJson start.byteIdx), ("end_byte", toJson stop.byteIdx)]).compress}"

end ProofOpt.SourceSpan

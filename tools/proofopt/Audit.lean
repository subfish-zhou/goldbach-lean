import Lean

/-! Independent proof-cone and actual-consumption checks for a frozen candidate. -/
namespace ProofOpt.Audit
open Lean Elab Command

syntax "#proofopt_axioms " ident : command
elab_rules : command
  | `(#proofopt_axioms $decl:ident) => do
    let env := (← getEnv).setExporting false
    let name := decl.getId
    unless (env.find? name).isSome do throwError "missing audit declaration {name}"
    let axioms ← withEnv env <| Lean.collectAxioms name
    let allowed := #[``propext, ``Classical.choice, ``Quot.sound]
    unless axioms.all allowed.contains do throwError "unexpected mathematical premise in {name}: {axioms}"
    logInfo m!"PROOFOPT_AXIOMS {(Json.mkObj [("name",toJson name.toString),("axioms",toJson (axioms.map Name.toString))]).compress}"

syntax "#proofopt_consumes " ident ident : command
elab_rules : command
  | `(#proofopt_consumes $source:ident $target:ident) => do
    let env := (← getEnv).setExporting false
    let mut todo := [(source.getId, [source.getId])]
    let mut seen : Std.HashSet Name := {}
    let mut path : List Name := []
    while !todo.isEmpty && path.isEmpty do
      let (n, revPath) := todo.head!
      todo := todo.tail!
      if seen.contains n then continue
      seen := seen.insert n
      if n == target.getId then
        path := revPath.reverse
      else if let some ci := env.find? n then
        -- Follow value dependencies only. Mere imports/type mentions are not consumption.
        if let some value := ci.value? (allowOpaque := true) then
          for next in value.getUsedConstants do
            todo := (next, next :: revPath) :: todo
    unless !path.isEmpty do throwError "no actual proof path {source.getId} -> {target.getId}"
    logInfo m!"PROOFOPT_CONSUMPTION {(Json.mkObj [("source",toJson source.getId.toString),("target",toJson target.getId.toString),("path",toJson (path.map Name.toString))]).compress}"

end ProofOpt.Audit

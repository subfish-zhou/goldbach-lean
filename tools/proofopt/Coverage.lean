import Lean

/-! Explicit-pair, bounded theorem coverage probe. No environment-wide proof search.
    Usage: #proofopt_coverage Fully.Qualified.target Fully.Qualified.provider -/
namespace ProofOpt.Coverage
open Lean Meta Elab Command

register_option proofopt.coverage.maxHeartbeats : Nat := {
  defValue := 200000
  descr := "Per-pair heartbeat budget (Lean user units); zero is rejected"
}

/-- Only literal type/value references; no extractor or structural-edge dependency. -/
def refs (ci : ConstantInfo) : Array Name :=
  ci.type.getUsedConstants ++
    ((ci.value? (allowOpaque := true)).map Expr.getUsedConstants).getD #[]

/-- Inspect the entire dependency cone, returning an explicit forbidden path.
    Also disallow sorryAx transitively, not just at the expression root. -/
def forbiddenPath (roots : Array Name) (target : Name) : MetaM (Option (List Name)) := do
  let env ← getEnv
  let mut seen : NameSet := {}
  let mut queue := roots.map fun n => (n, [n])
  let mut i := 0
  while i < queue.size do
    checkSystem "proofopt.coverage.dependencies"
    let (n, path) := queue[i]!
    i := i + 1
    if n == target || n == ``sorryAx then return some path.reverse
    if seen.contains n then continue
    seen := seen.insert n
    let some ci := env.find? n | throwError "dependency unavailable: {n}"
    for next in refs ci do
      unless seen.contains next do
        queue := queue.push (next, next :: path)
  return none

def ppOptions (o : Options) : Options :=
  o.setBool `pp.all true |>.setBool `pp.fullNames true
    |>.setBool `pp.universes true |>.setBool `pp.proofs true
    |>.setBool `pp.explicit true |>.setBool `pp.notation false
    |>.setBool `pp.fieldNotation false |>.setBool `pp.funBinderTypes true
    |>.setBool `pp.piBinderTypes true |>.setBool `pp.deepTerms true
    |>.set `pp.maxSteps (1000000 : Nat)

def result (target provider : Name) (status reason : String)
    (fields : List (String × Json) := []) : Json :=
  Json.mkObj ([ ("target", toJson target.toString), ("provider", toJson provider.toString),
    ("status", toJson status), ("reason", toJson reason) ] ++ fields)

def pathText (path : List Name) : String :=
  String.intercalate " -> " (path.map Name.toString)

/-- The command lift runs this with a fresh Meta.State. Only provider universe
    levels are flexible; target levels remain the original rigid parameters. -/
def probe (target provider : Name) : TermElabM Json := do
  if target == provider then
    return result target provider "rejected" "self_reference"
  let env ← getEnv
  let some tc := env.find? target |
    return result target provider "rejected" "unknown_target"
  let some pc := env.find? provider |
    return result target provider "rejected" "unknown_provider"
  unless tc.isTheorem && pc.isTheorem do
    return result target provider "rejected" "both_names_must_be_theorems"
  if let some path ← forbiddenPath #[provider] target then
    return result target provider "rejected" s!"provider_dependency: {pathText path}"
  let ty := tc.type
  unless ← isProp ty do
    return result target provider "rejected" "target_not_proposition"
  let root ← mkFreshExprSyntheticOpaqueMVar ty
  let (_, goal) ← root.mvarId!.intros
  let providerExpr ← mkConstWithFreshMVarLevels provider
  let goals ← try
    goal.apply providerExpr
  catch ex =>
    let rendered ← goal.withContext do pure (← ppGoal goal).pretty
    return result target provider "not_covered" s!"apply_failed: {← (← addMessageContext ex.toMessageData).toString}"
      [("remaining", toJson #[rendered])]
  -- simp only [*] uses local hypotheses, not the ambient global simp database.
  -- No exact?/apply? or global search which might rediscover the target.
  let closeTac ← `(tactic| first | assumption | rfl | (simp only [*]; done) | skip)
  let mut residualIds : Array MVarId := #[]
  for g in goals do
    unless ← g.isAssigned do
      let rest ← Tactic.run g (Tactic.evalTactic closeTac)
      checkSystem "proofopt.coverage.close"
      residualIds := residualIds ++ rest.toArray
  -- Later sibling goals can assign earlier shared metavariables.
  let mut remaining : Array String := #[]
  for r in residualIds do
    unless ← r.isAssigned do
      remaining := remaining.push (← r.withContext do pure (← ppGoal r).pretty)
  let proof ← instantiateMVars root
  if proof.hasMVar || !remaining.isEmpty then
    return result target provider "not_covered" "remaining_goals_or_unresolved_metavariables"
      [("remaining", toJson remaining)]
  if proof.hasFVar || proof.hasLooseBVars || proof.hasSorry then
    return result target provider "rejected" "nonclosed_or_sorry_proof"
  if let some path ← forbiddenPath proof.getUsedConstants target then
    return result target provider "rejected" s!"proof_dependency: {pathText path}"
  -- Meta check is supplementary; the subsequent isolated kernel declaration
  -- checks the *original complete target type*, not just the introduced goal.
  check proof
  unless ← isDefEq (← inferType proof) ty do
    return result target provider "rejected" "proof_type_mismatch"
  let checkName ← mkFreshUserName `ProofOpt.coverageCertificate
  let decl := Declaration.thmDecl {
    name := checkName, levelParams := tc.levelParams, type := ty, value := proof
  }
  let ctx ← readThe Core.Context
  match env.addDeclCore ctx.maxHeartbeats.toUSize ctx.maxRecDepth.toUSize decl ctx.cancelTk? true with
  | .error ex =>
    return result target provider "rejected" s!"kernel_check_failed: {← (ex.toMessageData (← getOptions)).toString}"
  | .ok _ => pure () -- discard checked environment: never install a declaration
  let (proofText, typeText) ← withOptions ppOptions do
    pure ((← ppExpr proof).pretty, (← ppExpr ty).pretty)
  return result target provider "success" "closed_kernel_checked_proof"
    [("remaining", toJson (#[] : Array String)), ("proof", toJson proofText),
     ("type", toJson typeText), ("levels", toJson (tc.levelParams.map Name.toString)),
     ("kernel_checked", toJson true), ("has_mvar", toJson false), ("has_sorry", toJson false)]

syntax (name := coverageCommand) "#proofopt_coverage " ident ident : command

elab_rules : command
  | `(#proofopt_coverage $target:ident $provider:ident) => do
    let t := target.getId
    let p := provider.getId
    let budget := proofopt.coverage.maxHeartbeats.get (← getOptions)
    let output ← if budget == 0 then
      pure (result t p "rejected" "zero_heartbeat_budget_forbidden")
    else
      try
        -- liftTermElabM starts from empty Meta.State (pinned Command.lean:743).
        liftTermElabM <| withTheReader Core.Context
          (fun ctx => { ctx with maxHeartbeats := budget * 1000 }) <|
          withCurrHeartbeats <| probe t p
      catch ex =>
        pure (result t p "error" (← (← addMessageContext ex.toMessageData).toString))
    logInfo m!"PROOFOPT_COVERAGE {output.compress}"

end ProofOpt.Coverage

import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Tactic.Convert
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

open Lean Meta Elab Tactic
namespace GoldbachProofTools.Elementary

/-- Construct a derivative proof from a bounded real-expression grammar. Supplied
    derivative facts are reused; nonzero obligations are ordinary metavariable goals. -/
private partial def derive (x point : Expr) (known : Array Expr)
    (nonzero : Expr → MetaM Expr) (body : Expr) : MetaM Expr := do
  let e := body.consumeMData
  if !e.containsFVar x.fvarId! then
    return ← mkAppM ``hasDerivAt_const #[point,e]
  if e == x then return ← mkAppM ``hasDerivAt_id #[point]
  for h in known do
    let t := (← inferType h).consumeMData
    unless t.isAppOf ``HasDerivAt do throwError "elementary_deriv: expected derivative fact"
    let as := t.getAppArgs
    let f := as[as.size-3]!
    let atX := (mkApp f x).headBeta
    if atX.getAppFn.constName? == e.getAppFn.constName? then
      if ← isDefEq atX e then
        unless ← isDefEq as.back! point do throwError "derivative fact has wrong evaluation point"
        return h
  let as := e.getAppArgs
  let go := derive x point known nonzero
  match e.getAppFn.constName? with
  | some ``HAdd.hAdd => mkAppM ``HasDerivAt.add #[← go as[as.size-2]!, ← go as.back!]
  | some ``HSub.hSub => mkAppM ``HasDerivAt.sub #[← go as[as.size-2]!, ← go as.back!]
  | some ``HMul.hMul => mkAppM ``HasDerivAt.mul #[← go as[as.size-2]!, ← go as.back!]
  | some ``Neg.neg => mkAppM ``HasDerivAt.neg #[← go as.back!]
  | some ``HPow.hPow =>
    let n := as.back!
    unless (← isDefEq (← inferType n) (mkConst ``Nat)) && !n.containsFVar x.fvarId! do
      throwError "elementary_deriv: expected variable-independent natural power"
    mkAppM ``HasDerivAt.pow #[← go as[as.size-2]!, n]
  | some ``HDiv.hDiv =>
    let f ← go as[as.size-2]!
    let d := as.back!
    if !d.containsFVar x.fvarId! then return ← mkAppM ``HasDerivAt.div_const #[f,d]
    mkAppM ``HasDerivAt.div #[f,← go d,← nonzero (d.replaceFVar x point)]
  | some ``Inv.inv =>
    let d := as.back!
    mkAppM ``HasDerivAt.inv #[← go d,← nonzero (d.replaceFVar x point)]
  | some ``Real.log =>
    let d := as.back!
    mkAppM ``HasDerivAt.log #[← go d,← nonzero (d.replaceFVar x point)]
  | some ``Real.exp => mkAppM ``HasDerivAt.exp #[← go as.back!]
  | _ => throwError "elementary_deriv: unsupported expression; supply its derivative: {e}"

elab "elementary_deriv" "[" facts:term,* "]" : tactic => withMainContext do
  let target := (← getMainTarget).consumeMData
  unless target.isAppOf ``HasDerivAt do throwError "elementary_deriv: expected HasDerivAt"
  let args := target.getAppArgs
  let point := args.back!
  unless ← isDefEq (← inferType point) (mkConst ``Real) do
    throwError "elementary_deriv: currently supports real scalar functions"
  let f := args[args.size-3]!
  let known ← facts.getElems.mapM fun stx => Term.elabTerm stx none
  let lctx ← getLCtx
  let insts ← getLocalInstances
  let obligations ← IO.mkRef (#[] : Array MVarId)
  let proof ← withLocalDeclD `x (mkConst ``Real) fun x => do
    let nonzero := fun d => withLCtx lctx insts do
      if d.containsFVar x.fvarId! then throwError "escaped differentiation variable"
      let zero ← mkAppOptM ``OfNat.ofNat #[some (mkConst ``Real), some (mkNatLit 0), none]
      let ty ← mkAppM ``Ne #[d,zero]
      let m ← mkFreshExprMVar ty MetavarKind.syntheticOpaque
      obligations.modify (·.push m.mvarId!)
      return m
    let f' ← if f.isConstOf ``Real.log || f.isConstOf ``Real.exp then pure f else whnf f
    let e := (mkApp f' x).headBeta
    derive x point known nonzero e
  let stx ← Term.exprToSyntax (← instantiateMVars proof)
  evalTactic (← `(tactic| convert $stx:term using 1))
  evalTactic (← `(tactic| all_goals try rfl))
  evalTactic (← `(tactic| all_goals try simp only [Pi.pow_apply, Pi.mul_apply,
    Pi.add_apply, Pi.sub_apply, Pi.neg_apply, Pi.inv_apply, Pi.div_apply, id_eq]))
  evalTactic (← `(tactic| all_goals try rfl))
  let equations ← getGoals
  let mut pending := []
  for g in ← obligations.get do
    unless ← g.isAssigned do pending := pending ++ [g]
  setGoals pending
  evalTactic (← `(tactic| all_goals try first | assumption | positivity | (apply ne_of_gt; positivity) | linarith))
  let residual ← getUnsolvedGoals
  setGoals (residual ++ equations)

end GoldbachProofTools.Elementary

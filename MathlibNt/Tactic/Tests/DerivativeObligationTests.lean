import MathlibNt.Tactic.ElementaryDeriv
open Lean Meta Elab Tactic

-- Inspect the actual goal queue: failure to close must be a remaining nonzero
-- obligation, not failure of the differentiation procedure itself.
example (_x : ℝ) : True := by
  run_tac withMainContext do
    let saved ← saveState
    let x ← Term.elabTerm (mkIdent `_x) none
    let sx ← Term.exprToSyntax x
    let ty ← Term.elabType (← `(HasDerivAt Real.log (1 / $sx:term) $sx:term))
    let goal ← mkFreshExprMVar ty MetavarKind.syntheticOpaque
    setGoals [goal.mvarId!]
    evalTactic (← `(tactic| elementary_deriv []))
    let goals ← getUnsolvedGoals
    unless goals.length == 1 do throwError "expected one explicit domain obligation"
    let actual ← goals.head!.getType
    let expected ← Term.elabType (← `($sx:term ≠ 0))
    unless ← isDefEq actual expected do throwError "wrong domain obligation"
    IO.println "EXPLICIT_NONZERO_GOAL_VERIFIED"
    saved.restore
    evalTactic (← `(tactic| trivial))

import Mathlib.Analysis.Calculus.Deriv.Polynomial
import Mathlib.Tactic.Convert
import Mathlib.Tactic.Ring

open Lean Meta Elab Tactic

namespace GoldbachProofTools

/-- Reify a univariate ring expression. Anything independent of the variable is
    a coefficient; unsupported variable-dependent operations are rejected. -/
private def coefficient (e : Expr) : MetaM Expr := do
  let c ← mkAppOptM ``Polynomial.C #[some (← inferType e), none]
  mkAppM ``DFunLike.coe #[c, e]

private partial def reify (x : Expr) (e : Expr) : MetaM Expr := do
  let e := e.consumeMData
  if !e.containsFVar x.fvarId! then
    return ← coefficient e
  if e == x then
    return ← mkAppOptM ``Polynomial.X #[some (← inferType x), none]
  let args := e.getAppArgs
  match e.getAppFn.constName? with
  | some ``HAdd.hAdd =>
    mkAppM ``HAdd.hAdd #[← reify x args[args.size-2]!, ← reify x args[args.size-1]!]
  | some ``HSub.hSub =>
    mkAppM ``HSub.hSub #[← reify x args[args.size-2]!, ← reify x args[args.size-1]!]
  | some ``HMul.hMul =>
    mkAppM ``HMul.hMul #[← reify x args[args.size-2]!, ← reify x args[args.size-1]!]
  | some ``Neg.neg => mkAppM ``Neg.neg #[← reify x args.back!]
  | some ``HPow.hPow =>
    let n := args.back!
    unless ← isDefEq (← inferType n) (mkConst ``Nat) do
      throwError "polynomial_deriv: only natural powers are supported"
    unless !n.containsFVar x.fvarId! do
      throwError "polynomial_deriv: exponent depends on the variable"
    mkAppM ``HPow.hPow #[← reify x args[args.size-2]!, n]
  | some ``HDiv.hDiv =>
    let d := args.back!
    if d.containsFVar x.fvarId! then
      throwError "polynomial_deriv: variable-dependent denominator"
    let c ← coefficient (← mkAppM ``Inv.inv #[d])
    mkAppM ``HMul.hMul #[← reify x args[args.size-2]!, c]
  | _ => throwError "polynomial_deriv: unsupported variable-dependent expression {e}"

/-- Use Mathlib's polynomial derivative theorem, leaving only the derivative
    value equality. This tactic generates an ordinary kernel-checked proof. -/
elab "polynomial_deriv" : tactic => withMainContext do
  let target ← getMainTarget
  unless target.isAppOf ``HasDerivAt do
    throwError "polynomial_deriv: expected HasDerivAt"
  let args := target.getAppArgs
  let f := args[args.size-3]!
  let point := args.back!
  let p ← withLocalDeclD `x (← inferType point) fun x => do
    let e := (mkApp (← whnf f) x).headBeta
    reify x e
  let proof ← mkAppOptM ``Polynomial.hasDerivAt #[some args[0]!, some args[1]!, some p, some point]
  let stx ← Term.exprToSyntax proof
  evalTactic (← `(tactic|
    convert $stx:term using 1 <;>
      try simp only [Polynomial.eval_add, Polynomial.eval_sub, Polynomial.eval_mul,
        Polynomial.eval_neg, Polynomial.eval_pow, Polynomial.eval_C, Polynomial.eval_X,
        Polynomial.eval_zero, Polynomial.eval_one, Polynomial.eval_natCast,
        Polynomial.derivative_add, Polynomial.derivative_sub, Polynomial.derivative_mul,
        Polynomial.derivative_neg, Polynomial.derivative_pow, Polynomial.derivative_C,
        Polynomial.derivative_X, div_eq_mul_inv] <;> try rfl))

  evalTactic (← `(tactic| all_goals try rfl))

end GoldbachProofTools

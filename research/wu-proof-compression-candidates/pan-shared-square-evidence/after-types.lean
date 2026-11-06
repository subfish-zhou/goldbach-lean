import Lean
import AnalyticNumberTheory.Sieve.PanV3SquareMean
open Lean
namespace PublicInterfaceAudit

private def node (tag : String) (args : Array Json := #[]) : Json :=
  .arr (#[toJson tag] ++ args)

private def nameTree : Name → Json
  | .anonymous => node "anonymous"
  | .str p s => node "str" #[nameTree p, toJson s]
  | .num p n => node "num" #[nameTree p, toJson n]

private def paramIndex (n : Name) : List Name → Option Nat
  | [] => none
  | p :: ps => if n == p then some 0 else (paramIndex n ps).map (· + 1)

private partial def levelTree (ps : List Name) : Level → Except String Json
  | .zero => return node "zero"
  | .succ u => return node "succ" #[← levelTree ps u]
  | .max u v => return node "max" #[← levelTree ps u, ← levelTree ps v]
  | .imax u v => return node "imax" #[← levelTree ps u, ← levelTree ps v]
  | .param p => match paramIndex p ps with
    | some i => return node "param" #[toJson i]
    | none => throw s!"Undeclared universe parameter: {p}"
  | .mvar _ => throw "Universe metavariable in public declaration"

private def binderTree : BinderInfo → Json
  | .default => toJson "default"
  | .implicit => toJson "implicit"
  | .strictImplicit => toJson "strictImplicit"
  | .instImplicit => toJson "instImplicit"

private partial def exprTree (ps : List Name) : Expr → Except String Json
  | .bvar i => return node "bvar" #[toJson i]
  | .fvar _ => throw "Free variable in public declaration"
  | .mvar _ => throw "Expression metavariable in public declaration"
  | .sort u => return node "sort" #[← levelTree ps u]
  | .const n us => do
    let levels ← us.mapM (levelTree ps)
    return node "const" #[nameTree n, .arr levels.toArray]
  | .app f x => return node "app" #[← exprTree ps f, ← exprTree ps x]
  | .lam _ t b bi => return node "lam" #[binderTree bi, ← exprTree ps t, ← exprTree ps b]
  | .forallE _ t b bi => return node "forall" #[binderTree bi, ← exprTree ps t, ← exprTree ps b]
  | .letE _ t v b nondep => return node "let" #[toJson nondep, ← exprTree ps t, ← exprTree ps v, ← exprTree ps b]
  | .lit (.natVal n) => return node "nat" #[toJson n]
  | .lit (.strVal s) => return node "string" #[toJson s]
  | .mdata _ e => exprTree ps e
  | .proj n i e => return node "proj" #[nameTree n, toJson i, ← exprTree ps e]

private def kind : ConstantInfo → String
  | .axiomInfo _ => "axiom" | .defnInfo _ => "definition"
  | .thmInfo _ => "theorem" | .opaqueInfo _ => "opaque"
  | .quotInfo _ => "quotient" | .inductInfo _ => "inductive"
  | .ctorInfo _ => "constructor" | .recInfo _ => "recursor"

private def declaration (ci : ConstantInfo) (includeDefinitions : Bool) : Except String Json := do
  let ty ← exprTree ci.levelParams ci.type
  let value ←
    if includeDefinitions then
      match ci with
      | .defnInfo d => exprTree ci.levelParams d.value
      | _ => throw s!"Requested definition value for non-definition: {ci.name}"
    else pure Json.null
  return Json.mkObj [
    ("name", toJson ci.name.toString), ("kind", toJson (kind ci)),
    ("levelParamCount", toJson ci.levelParams.length),
    ("type", ty), ("definitionValue", value)]

run_cmd do
  let env ← Lean.getEnv
  let requested : List Name := [`AnalyticNumberTheory.Sieve.v3_moebius_abs_le_one, `AnalyticNumberTheory.Sieve.vaughanThird_zero, `AnalyticNumberTheory.Sieve.v3_vonMangoldt_nonneg, `AnalyticNumberTheory.Sieve.vaughanThird_abs_le, `AnalyticNumberTheory.Sieve.v3_harmonic_Icc_le, `AnalyticNumberTheory.Sieve.v3_card_multiples_Icc, `AnalyticNumberTheory.Sieve.v3_lcm_inv_sum_le, `AnalyticNumberTheory.Sieve.v3_divisorCountSq_sum_le, `AnalyticNumberTheory.Sieve.panTypeIICharSqSum_le_additiveSieve, `AnalyticNumberTheory.Sieve.panTypeIICharSqrtMeanMaxY_le_sum]
  let mut entries : Array Json := #[]
  for n in requested do
    let some ci := env.find? n | throwError "missing declaration {n}"
    match declaration ci false with
    | .error e => throwError "{e}"
    | .ok j => entries := entries.push j
  Lean.Elab.Command.liftIO <| IO.FS.writeFile "/tmp/wu-pan-shared-square-v1/after-types.json" (Json.arr entries).compress
end PublicInterfaceAudit
#print axioms AnalyticNumberTheory.Sieve.v3_moebius_abs_le_one
#print axioms AnalyticNumberTheory.Sieve.vaughanThird_zero
#print axioms AnalyticNumberTheory.Sieve.v3_vonMangoldt_nonneg
#print axioms AnalyticNumberTheory.Sieve.vaughanThird_abs_le
#print axioms AnalyticNumberTheory.Sieve.v3_harmonic_Icc_le
#print axioms AnalyticNumberTheory.Sieve.v3_card_multiples_Icc
#print axioms AnalyticNumberTheory.Sieve.v3_lcm_inv_sum_le
#print axioms AnalyticNumberTheory.Sieve.v3_divisorCountSq_sum_le
#print axioms AnalyticNumberTheory.Sieve.panTypeIICharSqSum_le_additiveSieve
#print axioms AnalyticNumberTheory.Sieve.panTypeIICharSqrtMeanMaxY_le_sum

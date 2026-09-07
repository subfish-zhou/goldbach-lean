import MathlibNt.SieveTheory.LiLiuGoldbachG11AuthorQuantitative
import Lean.Util.FoldConsts

open Lean Elab Command
set_option maxHeartbeats 0
set_option maxRecDepth 10000
set_option pp.deepTerms true
set_option pp.proofs true
set_option pp.explicit true
set_option pp.maxSteps 1000000

-- This is an audit command, not a mathematical premise or proof producer.
elab "auditG11QuantitativeMembers" : command => do
  let env ← getEnv
  let payload : Array Name := #[`MathlibNt.SieveTheory.LiLiuGoldbachG11AuthorReusedCounts, `MathlibNt.SieveTheory.LiLiuGoldbachG11AuthorCountLedger, `MathlibNt.SieveTheory.LiLiuGoldbachG11AuthorQuantitative]
  let mut seen : NameSet := {}
  let mut count : Nat := 0
  let mut matched : Nat := 0
  for (mn, md) in env.header.moduleNames.zip env.header.moduleData do
    if payload.contains mn then
      matched := matched + 1
      for n in md.constNames do
        if !seen.contains n then
          seen := seen.insert n
          count := count + 1
          logInfo m!"G11_QUANT_MEMBER {n.toString}"
          elabCommand (← `(command| set_option pp.universes true in #check $(mkIdent n)))
          elabCommand (← `(command| set_option pp.universes false in #print axioms $(mkIdent n)))
  unless matched == payload.size do throwError "missing payload modules: {matched}/{payload.size}"
  logInfo m!"G11_QUANT_MEMBER_COUNT {count}"
  let top := `MathlibNt.SieveTheory.LiLiuOnePlusOneNine.GoldbachBig.goldbach_D19_gt_paper_0004
  let mut visited : NameSet := {}
  let mut queued : NameSet := ({} : NameSet).insert top
  let mut todo : Array Name := #[top]
  let mut coneCount : Nat := 0
  while !todo.isEmpty do
    let n := todo.back!
    todo := todo.pop
    visited := visited.insert n
    coneCount := coneCount + 1
    if n == `sorryAx || n == `Lean.ofReduceBool || n == `Lean.trustCompiler then
      throwError "forbidden reachable constant: {n}"
    if n == `MathlibNt.SieveTheory.LiLiuOnePlusOneNine.GoldbachBig.goldbachWeightG11_le_uniformScalar_numeric_fixed ||
        n == `MathlibNt.SieveTheory.LiLiuOnePlusOneNine.GoldbachBig.goldbachWeightG11_le_sharpBuchstabIntegral then
      throwError "old uniform-count route reached: {n}"
    let some ci := env.find? n | throwError "missing reachable constant: {n}"
    match ci with
    | .axiomInfo _ =>
      unless #[`propext, `Classical.choice, `Quot.sound].contains n do
        throwError "nonstandard reachable axiom: {n}"
    | _ => pure ()
    let ds := ci.type.getUsedConstants ++ ((ci.value? true).map Expr.getUsedConstants).getD #[]
    for d in ds do
      if !queued.contains d then
        queued := queued.insert d
        todo := todo.push d
  let required : Array (String × Array Name) := #[("MathlibNt.SieveTheory.LiLiuOnePlusOneNine.GoldbachBig.goldbachWeightG11_le_authorScalar_direct", #[`MathlibNt.SieveTheory.LiLiuOnePlusOneNine.GoldbachBig.goldbachWeightG11_le_authorScalar_direct]),
    ("MathlibNt.SieveTheory.LiLiuOnePlusOneNine.GoldbachBig.goldbachG11Author_reused_pair_lower", #[`MathlibNt.SieveTheory.LiLiuOnePlusOneNine.GoldbachBig.goldbachG11Author_reused_pair_lower]),
    ("MathlibNt.SieveTheory.LiLiuOnePlusOneNine.GoldbachBig.goldbachG11Author_reused_cross_upper", #[`MathlibNt.SieveTheory.LiLiuOnePlusOneNine.GoldbachBig.goldbachG11Author_reused_cross_upper]),
    ("MathlibNt.SieveTheory.LiLiuOnePlusOneNine.GoldbachBig.goldbachWeight_paperSplit_authorG11_consumed_small_epsilon", #[`MathlibNt.SieveTheory.LiLiuOnePlusOneNine.GoldbachBig.goldbachWeight_paperSplit_authorG11_consumed_small_epsilon]),
    ("MathlibNt.SieveTheory.LiLiuOnePlusOneNine.GoldbachBig.goldbachWeight_remainingFive_allRetained_small_epsilon", #[`MathlibNt.SieveTheory.LiLiuOnePlusOneNine.GoldbachBig.goldbachWeight_remainingFive_allRetained_small_epsilon]),
    ("MathlibNt.SieveTheory.LiLiuOnePlusOneNine.GoldbachBig.goldbachG67IntegralConstant_lower_certified", #[`MathlibNt.SieveTheory.LiLiuOnePlusOneNine.GoldbachBig.goldbachG67IntegralConstant_lower_certified]),
    ("MathlibNt.SieveTheory.LiLiuOnePlusOneNine.GoldbachBig.G9Analytic.actual_le_target", #[`MathlibNt.SieveTheory.LiLiuOnePlusOneNine.GoldbachBig.G9Analytic.actual_le_target]),
    ("G12AnalyticCertificate.actual_le_target", #[`G12AnalyticCertificate.actual_le_target]),
    ("G12SharpOutput.original_total_integral", #[`G12SharpOutput.original_total_integral])]
  for (label, ns) in required do
    unless ns.any (fun n => visited.contains n) do
      throwError "required actual producer branch not reached: {label}"
    logInfo m!"G11_QUANT_REQUIRED_BRANCH {label}"
  logInfo m!"G11_QUANT_CONE_PASS {coneCount}"

auditG11QuantitativeMembers
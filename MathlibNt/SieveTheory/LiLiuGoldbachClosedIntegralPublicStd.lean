import MathlibNt.SieveTheory.LiLiuGoldbachG12LowRectangle
import MathlibNt.SieveTheory.LiLiuGoldbachG12IntegralReduction
import MathlibNt.SieveTheory.LiLiuGoldbachG67ElementaryIntegral
import MathlibNt.SieveTheory.LiLiuGoldbachG67ElementaryIntegralBridge
import MathlibNt.SieveTheory.LiLiuGoldbachG12LowRectangleC2
import MathlibNt.SieveTheory.LiLiuGoldbachClosedCrossIntegralLedger
import Lean
set_option pp.deepTerms true
set_option pp.proofs true
set_option pp.maxSteps 1000000
open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let targets : List Name := [`MathlibNt.SieveTheory.LiLiuGoldbachG12LowRectangle, `MathlibNt.SieveTheory.LiLiuGoldbachG12IntegralReduction, `MathlibNt.SieveTheory.LiLiuGoldbachG67ElementaryIntegral, `MathlibNt.SieveTheory.LiLiuGoldbachG67ElementaryIntegralBridge, `MathlibNt.SieveTheory.LiLiuGoldbachG12LowRectangleC2, `MathlibNt.SieveTheory.LiLiuGoldbachClosedCrossIntegralLedger]
  for m in env.header.moduleNames do
    if m.toString.startsWith "LiLiu" then
      throwError "UNQUALIFIED_PROJECT_IMPORT {m}"
  let mut seen : NameSet := {}
  for i in [:env.header.moduleNames.size] do
    if targets.contains env.header.moduleNames[i]! then
      for n in env.header.moduleData[i]!.constNames do
        if !n.isInternal && !seen.contains n then
          seen := seen.insert n
          let id := mkIdent n
          elabCommand (← `(command| #check @$id:ident))
          elabCommand (← `(command| #print axioms $id:ident))
          logInfo m!"G9_MEMBER_CHECKED {n}"

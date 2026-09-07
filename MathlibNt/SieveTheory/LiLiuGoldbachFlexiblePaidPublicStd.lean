import MathlibNt.SieveTheory.LiLiuGoldbachG12FlexibleWF
import MathlibNt.SieveTheory.LiLiuGoldbachG12FlexibleWFRemainder
import MathlibNt.SieveTheory.LiLiuGoldbachG12FlexibleWFOutput
import MathlibNt.SieveTheory.LiLiuGoldbachG12OutsideBudget
import MathlibNt.SieveTheory.LiLiuGoldbachG12OutsideBudgetTransport
import MathlibNt.SieveTheory.LiLiuGoldbachG12OutsideBudgetLogSaving
import MathlibNt.SieveTheory.LiLiuGoldbachG12RectangleGate
import MathlibNt.SieveTheory.LiLiuGoldbachG12RectangleGateSaving
import MathlibNt.SieveTheory.LiLiuGoldbachG12FlexibleCorrectionBudget
import MathlibNt.SieveTheory.LiLiuGoldbachG12FlexiblePaidSieve
import MathlibNt.SieveTheory.LiLiuGoldbachG12FlexibleCorrectionSaving
import MathlibNt.SieveTheory.LiLiuGoldbachG12FlexiblePaidC2Sieve
import Lean
set_option pp.deepTerms true
set_option pp.proofs true
set_option pp.maxSteps 1000000
open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let targets : List Name := [`MathlibNt.SieveTheory.LiLiuGoldbachG12FlexibleWF, `MathlibNt.SieveTheory.LiLiuGoldbachG12FlexibleWFRemainder, `MathlibNt.SieveTheory.LiLiuGoldbachG12FlexibleWFOutput, `MathlibNt.SieveTheory.LiLiuGoldbachG12OutsideBudget, `MathlibNt.SieveTheory.LiLiuGoldbachG12OutsideBudgetTransport, `MathlibNt.SieveTheory.LiLiuGoldbachG12OutsideBudgetLogSaving, `MathlibNt.SieveTheory.LiLiuGoldbachG12RectangleGate, `MathlibNt.SieveTheory.LiLiuGoldbachG12RectangleGateSaving, `MathlibNt.SieveTheory.LiLiuGoldbachG12FlexibleCorrectionBudget, `MathlibNt.SieveTheory.LiLiuGoldbachG12FlexiblePaidSieve, `MathlibNt.SieveTheory.LiLiuGoldbachG12FlexibleCorrectionSaving, `MathlibNt.SieveTheory.LiLiuGoldbachG12FlexiblePaidC2Sieve]
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

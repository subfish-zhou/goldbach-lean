import MathlibNt.SieveTheory.LiLiuGoldbachG12CrossSwitch
import MathlibNt.SieveTheory.LiLiuGoldbachProductCoefficientCap
import MathlibNt.SieveTheory.LiLiuGoldbachG12CrossProduct
import MathlibNt.SieveTheory.LiLiuGoldbachG12CrossProductPaid
import MathlibNt.SieveTheory.LiLiuGoldbachCrossProductLedger
import MathlibNt.SieveTheory.LiLiuGoldbachG12ActiveProduct
import MathlibNt.SieveTheory.LiLiuGoldbachG12LinkedWindow
import MathlibNt.SieveTheory.LiLiuGoldbachG12LinkedWindowAP
import MathlibNt.SieveTheory.LiLiuGoldbachG12LinkedDistribution
import MathlibNt.SieveTheory.LiLiuGoldbachActiveCrossLedger
import Lean
set_option pp.deepTerms true
set_option pp.proofs true
set_option pp.maxSteps 1000000
open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let targets : List Name := [`MathlibNt.SieveTheory.LiLiuGoldbachG12CrossSwitch, `MathlibNt.SieveTheory.LiLiuGoldbachProductCoefficientCap, `MathlibNt.SieveTheory.LiLiuGoldbachG12CrossProduct, `MathlibNt.SieveTheory.LiLiuGoldbachG12CrossProductPaid, `MathlibNt.SieveTheory.LiLiuGoldbachCrossProductLedger, `MathlibNt.SieveTheory.LiLiuGoldbachG12ActiveProduct, `MathlibNt.SieveTheory.LiLiuGoldbachG12LinkedWindow, `MathlibNt.SieveTheory.LiLiuGoldbachG12LinkedWindowAP, `MathlibNt.SieveTheory.LiLiuGoldbachG12LinkedDistribution, `MathlibNt.SieveTheory.LiLiuGoldbachActiveCrossLedger]
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

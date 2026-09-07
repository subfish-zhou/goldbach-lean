import MathlibNt.SieveTheory.LiLiuGoldbachG12GateBudget
import MathlibNt.SieveTheory.LiLiuGoldbachG12LinkedDivisorDistribution
import MathlibNt.SieveTheory.LiLiuGoldbachG12CommonMass
import MathlibNt.SieveTheory.LiLiuGoldbachIdealPairKernel
import MathlibNt.SieveTheory.LiLiuGoldbachG67ActualIntegral
import MathlibNt.SieveTheory.LiLiuGoldbachPairIntegralLedger
import MathlibNt.SieveTheory.LiLiuGoldbachG12CommonMassBuchstab
import Lean
set_option pp.deepTerms true
set_option pp.proofs true
set_option pp.maxSteps 1000000
open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let targets : List Name := [`MathlibNt.SieveTheory.LiLiuGoldbachG12GateBudget, `MathlibNt.SieveTheory.LiLiuGoldbachG12LinkedDivisorDistribution, `MathlibNt.SieveTheory.LiLiuGoldbachG12CommonMass, `MathlibNt.SieveTheory.LiLiuGoldbachIdealPairKernel, `MathlibNt.SieveTheory.LiLiuGoldbachG67ActualIntegral, `MathlibNt.SieveTheory.LiLiuGoldbachPairIntegralLedger, `MathlibNt.SieveTheory.LiLiuGoldbachG12CommonMassBuchstab]
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

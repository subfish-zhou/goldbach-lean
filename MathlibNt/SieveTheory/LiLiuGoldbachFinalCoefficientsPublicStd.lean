import MathlibNt.SieveTheory.LiLiuGoldbachG67CenteredPolynomial
import MathlibNt.SieveTheory.LiLiuGoldbachG12EvaluationPrimitives
import MathlibNt.SieveTheory.LiLiuGoldbachG12EvaluationFTC
import MathlibNt.SieveTheory.LiLiuGoldbachG12EvaluationScalar
import MathlibNt.SieveTheory.LiLiuGoldbachG67CenteredError
import MathlibNt.SieveTheory.LiLiuGoldbachG67CenteredBranches
import MathlibNt.SieveTheory.LiLiuGoldbachG67CenteredBridge
import MathlibNt.SieveTheory.LiLiuGoldbachG67Constants
import MathlibNt.SieveTheory.LiLiuGoldbachG67Forms
import MathlibNt.SieveTheory.LiLiuGoldbachG67Integral1
import MathlibNt.SieveTheory.LiLiuGoldbachG67Integral2
import MathlibNt.SieveTheory.LiLiuGoldbachG67Integral3
import MathlibNt.SieveTheory.LiLiuGoldbachG67Integral4
import MathlibNt.SieveTheory.LiLiuGoldbachG67Integral5
import MathlibNt.SieveTheory.LiLiuGoldbachG67CenteredEndpoint
import MathlibNt.SieveTheory.LiLiuGoldbachOneNineUnconditional
import Lean
set_option pp.deepTerms true
set_option pp.proofs true
set_option pp.maxSteps 1000000
open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let targets : List Name := [`MathlibNt.SieveTheory.LiLiuGoldbachG67CenteredPolynomial, `MathlibNt.SieveTheory.LiLiuGoldbachG12EvaluationPrimitives, `MathlibNt.SieveTheory.LiLiuGoldbachG12EvaluationFTC, `MathlibNt.SieveTheory.LiLiuGoldbachG12EvaluationScalar, `MathlibNt.SieveTheory.LiLiuGoldbachG67CenteredError, `MathlibNt.SieveTheory.LiLiuGoldbachG67CenteredBranches, `MathlibNt.SieveTheory.LiLiuGoldbachG67CenteredBridge, `MathlibNt.SieveTheory.LiLiuGoldbachG67Constants, `MathlibNt.SieveTheory.LiLiuGoldbachG67Forms, `MathlibNt.SieveTheory.LiLiuGoldbachG67Integral1, `MathlibNt.SieveTheory.LiLiuGoldbachG67Integral2, `MathlibNt.SieveTheory.LiLiuGoldbachG67Integral3, `MathlibNt.SieveTheory.LiLiuGoldbachG67Integral4, `MathlibNt.SieveTheory.LiLiuGoldbachG67Integral5, `MathlibNt.SieveTheory.LiLiuGoldbachG67CenteredEndpoint, `MathlibNt.SieveTheory.LiLiuGoldbachOneNineUnconditional]
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

import MathlibNt.SieveTheory.LiLiuGoldbachG9AnalyticEnvelope
import MathlibNt.SieveTheory.LiLiuGoldbachG9AnalyticPrimitives
import MathlibNt.SieveTheory.LiLiuGoldbachG9AnalyticLogBounds
import MathlibNt.SieveTheory.LiLiuGoldbachG9AnalyticScalar
import MathlibNt.SieveTheory.LiLiuGoldbachG67Analytic
import MathlibNt.SieveTheory.LiLiuGoldbachG67RationalLower
import MathlibNt.SieveTheory.LiLiuGoldbachG12AnalyticEnvelope
import MathlibNt.SieveTheory.LiLiuGoldbachG12AnalyticPrimitives
import MathlibNt.SieveTheory.LiLiuGoldbachOneNineLiteralExponent
import MathlibNt.SieveTheory.LiLiuGoldbachSharpG9CertifiedLedger
import Lean
set_option pp.deepTerms true
set_option pp.proofs true
set_option pp.maxSteps 1000000
open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let targets : List Name := [`MathlibNt.SieveTheory.LiLiuGoldbachG9AnalyticEnvelope, `MathlibNt.SieveTheory.LiLiuGoldbachG9AnalyticPrimitives, `MathlibNt.SieveTheory.LiLiuGoldbachG9AnalyticLogBounds, `MathlibNt.SieveTheory.LiLiuGoldbachG9AnalyticScalar, `MathlibNt.SieveTheory.LiLiuGoldbachG67Analytic, `MathlibNt.SieveTheory.LiLiuGoldbachG67RationalLower, `MathlibNt.SieveTheory.LiLiuGoldbachG12AnalyticEnvelope, `MathlibNt.SieveTheory.LiLiuGoldbachG12AnalyticPrimitives, `MathlibNt.SieveTheory.LiLiuGoldbachOneNineLiteralExponent, `MathlibNt.SieveTheory.LiLiuGoldbachSharpG9CertifiedLedger]
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

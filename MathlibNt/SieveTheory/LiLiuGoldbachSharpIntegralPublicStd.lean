import MathlibNt.SieveTheory.LiLiuGoldbachG12SharpWeight
import MathlibNt.SieveTheory.LiLiuGoldbachG12SharpGeometry
import MathlibNt.SieveTheory.LiLiuGoldbachG12SharpRough
import MathlibNt.SieveTheory.LiLiuGoldbachG12SharpTerminal
import MathlibNt.SieveTheory.LiLiuGoldbachG12SharpEnvelope
import MathlibNt.SieveTheory.LiLiuGoldbachG12SharpIntegralSplit
import MathlibNt.SieveTheory.LiLiuGoldbachG12SharpQuadrature
import MathlibNt.SieveTheory.LiLiuGoldbachG67SumGeometry
import MathlibNt.SieveTheory.LiLiuGoldbachG67SumDensity
import MathlibNt.SieveTheory.LiLiuGoldbachG67SumFubini
import MathlibNt.SieveTheory.LiLiuGoldbachG67SumWeightProperties
import MathlibNt.SieveTheory.LiLiuGoldbachG67G67Specialization
import MathlibNt.SieveTheory.LiLiuGoldbachG67G67Truncation
import MathlibNt.SieveTheory.LiLiuGoldbachG67G67Piecewise
import MathlibNt.SieveTheory.LiLiuGoldbachG12SharpMassIntegral
import MathlibNt.SieveTheory.LiLiuGoldbachG12SharpOutputIntegral
import MathlibNt.SieveTheory.LiLiuGoldbachSharpCrossIntegralLedger
import MathlibNt.SieveTheory.LiLiuGoldbachSharpPiecewiseLedger
import Lean
set_option pp.deepTerms true
set_option pp.proofs true
set_option pp.maxSteps 1000000
open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let targets : List Name := [`MathlibNt.SieveTheory.LiLiuGoldbachG12SharpWeight, `MathlibNt.SieveTheory.LiLiuGoldbachG12SharpGeometry, `MathlibNt.SieveTheory.LiLiuGoldbachG12SharpRough, `MathlibNt.SieveTheory.LiLiuGoldbachG12SharpTerminal, `MathlibNt.SieveTheory.LiLiuGoldbachG12SharpEnvelope, `MathlibNt.SieveTheory.LiLiuGoldbachG12SharpIntegralSplit, `MathlibNt.SieveTheory.LiLiuGoldbachG12SharpQuadrature, `MathlibNt.SieveTheory.LiLiuGoldbachG67SumGeometry, `MathlibNt.SieveTheory.LiLiuGoldbachG67SumDensity, `MathlibNt.SieveTheory.LiLiuGoldbachG67SumFubini, `MathlibNt.SieveTheory.LiLiuGoldbachG67SumWeightProperties, `MathlibNt.SieveTheory.LiLiuGoldbachG67G67Specialization, `MathlibNt.SieveTheory.LiLiuGoldbachG67G67Truncation, `MathlibNt.SieveTheory.LiLiuGoldbachG67G67Piecewise, `MathlibNt.SieveTheory.LiLiuGoldbachG12SharpMassIntegral, `MathlibNt.SieveTheory.LiLiuGoldbachG12SharpOutputIntegral, `MathlibNt.SieveTheory.LiLiuGoldbachSharpCrossIntegralLedger, `MathlibNt.SieveTheory.LiLiuGoldbachSharpPiecewiseLedger]
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

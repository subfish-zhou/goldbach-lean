import MathlibNt.SieveTheory.LiLiuGoldbachG12ClippedGeometry
import MathlibNt.SieveTheory.LiLiuGoldbachG12ClippedDistribution
import MathlibNt.SieveTheory.LiLiuGoldbachG12ClippedMass
import MathlibNt.SieveTheory.LiLiuGoldbachG12ClippedConsumers
import MathlibNt.SieveTheory.LiLiuGoldbachG12ClippedSemantics
import MathlibNt.SieveTheory.LiLiuGoldbachG12GridBoundary
import MathlibNt.SieveTheory.LiLiuGoldbachG12GridBoundaryBudget
import MathlibNt.SieveTheory.LiLiuGoldbachG12GridAdmission
import MathlibNt.SieveTheory.LiLiuGoldbachG12OccupiedSource
import MathlibNt.SieveTheory.LiLiuGoldbachG12CutoffSlicePayment
import MathlibNt.SieveTheory.LiLiuGoldbachG12OccupiedC2Sieve
import MathlibNt.SieveTheory.LiLiuGoldbachG12BoundarySource
import MathlibNt.SieveTheory.LiLiuGoldbachG12OriginalPaidGrid
import Lean
set_option pp.deepTerms true
set_option pp.proofs true
set_option pp.maxSteps 1000000
open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let targets : List Name := [`MathlibNt.SieveTheory.LiLiuGoldbachG12ClippedGeometry, `MathlibNt.SieveTheory.LiLiuGoldbachG12ClippedDistribution, `MathlibNt.SieveTheory.LiLiuGoldbachG12ClippedMass, `MathlibNt.SieveTheory.LiLiuGoldbachG12ClippedConsumers, `MathlibNt.SieveTheory.LiLiuGoldbachG12ClippedSemantics, `MathlibNt.SieveTheory.LiLiuGoldbachG12GridBoundary, `MathlibNt.SieveTheory.LiLiuGoldbachG12GridBoundaryBudget, `MathlibNt.SieveTheory.LiLiuGoldbachG12GridAdmission, `MathlibNt.SieveTheory.LiLiuGoldbachG12OccupiedSource, `MathlibNt.SieveTheory.LiLiuGoldbachG12CutoffSlicePayment, `MathlibNt.SieveTheory.LiLiuGoldbachG12OccupiedC2Sieve, `MathlibNt.SieveTheory.LiLiuGoldbachG12BoundarySource, `MathlibNt.SieveTheory.LiLiuGoldbachG12OriginalPaidGrid]
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

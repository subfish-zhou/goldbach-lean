import MathlibNt.SieveTheory.LiLiuGoldbachG12BandOutput
import MathlibNt.SieveTheory.LiLiuGoldbachG12BandWindows
import MathlibNt.SieveTheory.LiLiuGoldbachG12BandMass
import MathlibNt.SieveTheory.LiLiuGoldbachG12BoundaryOutputBudget
import MathlibNt.SieveTheory.LiLiuGoldbachG12SafeGridBudget
import MathlibNt.SieveTheory.LiLiuGoldbachG12LogBudgetTools
import MathlibNt.SieveTheory.LiLiuGoldbachG12PaidRectangle
import MathlibNt.SieveTheory.LiLiuGoldbachG12PaidSafeCell
import MathlibNt.SieveTheory.LiLiuGoldbachG12PaidFixedGrid
import MathlibNt.SieveTheory.LiLiuGoldbachG12SafeGridTerminal
import MathlibNt.SieveTheory.LiLiuGoldbachG12AuthorWeightBounds
import MathlibNt.SieveTheory.LiLiuGoldbachG12AuthorWeightedTransport
import MathlibNt.SieveTheory.LiLiuGoldbachG12AuthorWeightedSource
import MathlibNt.SieveTheory.LiLiuGoldbachG12AuthorWeightedIntegral
import MathlibNt.SieveTheory.LiLiuGoldbachG12AuthorSourceBudget
import MathlibNt.SieveTheory.LiLiuGoldbachG12AuthorLowHigh
import MathlibNt.SieveTheory.LiLiuGoldbachG12AuthorAssemblyTools
import MathlibNt.SieveTheory.LiLiuGoldbachG12AuthorOutputIntegral
import MathlibNt.SieveTheory.LiLiuGoldbachAuthorCrossIntegralLedger
import MathlibNt.SieveTheory.LiLiuGoldbachG12AuthorBranchForm
import Lean
set_option pp.deepTerms true
set_option pp.proofs true
set_option pp.maxSteps 1000000
open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let targets : List Name := [`MathlibNt.SieveTheory.LiLiuGoldbachG12BandOutput, `MathlibNt.SieveTheory.LiLiuGoldbachG12BandWindows, `MathlibNt.SieveTheory.LiLiuGoldbachG12BandMass, `MathlibNt.SieveTheory.LiLiuGoldbachG12BoundaryOutputBudget, `MathlibNt.SieveTheory.LiLiuGoldbachG12SafeGridBudget, `MathlibNt.SieveTheory.LiLiuGoldbachG12LogBudgetTools, `MathlibNt.SieveTheory.LiLiuGoldbachG12PaidRectangle, `MathlibNt.SieveTheory.LiLiuGoldbachG12PaidSafeCell, `MathlibNt.SieveTheory.LiLiuGoldbachG12PaidFixedGrid, `MathlibNt.SieveTheory.LiLiuGoldbachG12SafeGridTerminal, `MathlibNt.SieveTheory.LiLiuGoldbachG12AuthorWeightBounds, `MathlibNt.SieveTheory.LiLiuGoldbachG12AuthorWeightedTransport, `MathlibNt.SieveTheory.LiLiuGoldbachG12AuthorWeightedSource, `MathlibNt.SieveTheory.LiLiuGoldbachG12AuthorWeightedIntegral, `MathlibNt.SieveTheory.LiLiuGoldbachG12AuthorSourceBudget, `MathlibNt.SieveTheory.LiLiuGoldbachG12AuthorLowHigh, `MathlibNt.SieveTheory.LiLiuGoldbachG12AuthorAssemblyTools, `MathlibNt.SieveTheory.LiLiuGoldbachG12AuthorOutputIntegral, `MathlibNt.SieveTheory.LiLiuGoldbachAuthorCrossIntegralLedger, `MathlibNt.SieveTheory.LiLiuGoldbachG12AuthorBranchForm]
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

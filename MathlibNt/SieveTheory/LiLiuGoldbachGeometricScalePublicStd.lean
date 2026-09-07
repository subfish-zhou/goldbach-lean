import MathlibNt.SieveTheory.LiLiuGoldbachG12LocalScale
import MathlibNt.SieveTheory.LiLiuGoldbachG12LocalScaleUniform
import MathlibNt.SieveTheory.LiLiuGoldbachG12LocalScaleCoefficient
import MathlibNt.SieveTheory.LiLiuGoldbachG12LocalScalePackage
import MathlibNt.SieveTheory.LiLiuGoldbachG12FineGrid
import MathlibNt.SieveTheory.LiLiuGoldbachG12FineGridMother
import MathlibNt.SieveTheory.LiLiuGoldbachG12FineGridSafety
import MathlibNt.SieveTheory.LiLiuGoldbachG12LowHighOutput
import MathlibNt.SieveTheory.LiLiuGoldbachG12LowHighOutputWindow
import MathlibNt.SieveTheory.LiLiuGoldbachG12ScaledC2Sieve
import MathlibNt.SieveTheory.LiLiuGoldbachG12OriginalGridPartition
import Lean
set_option pp.deepTerms true
set_option pp.proofs true
set_option pp.maxSteps 1000000
open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let targets : List Name := [`MathlibNt.SieveTheory.LiLiuGoldbachG12LocalScale, `MathlibNt.SieveTheory.LiLiuGoldbachG12LocalScaleUniform, `MathlibNt.SieveTheory.LiLiuGoldbachG12LocalScaleCoefficient, `MathlibNt.SieveTheory.LiLiuGoldbachG12LocalScalePackage, `MathlibNt.SieveTheory.LiLiuGoldbachG12FineGrid, `MathlibNt.SieveTheory.LiLiuGoldbachG12FineGridMother, `MathlibNt.SieveTheory.LiLiuGoldbachG12FineGridSafety, `MathlibNt.SieveTheory.LiLiuGoldbachG12LowHighOutput, `MathlibNt.SieveTheory.LiLiuGoldbachG12LowHighOutputWindow, `MathlibNt.SieveTheory.LiLiuGoldbachG12ScaledC2Sieve, `MathlibNt.SieveTheory.LiLiuGoldbachG12OriginalGridPartition]
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

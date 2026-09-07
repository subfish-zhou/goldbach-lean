import MathlibNt.SieveTheory.LiLiuGoldbachG12ClippedOutput
import MathlibNt.SieveTheory.LiLiuGoldbachG12ClippedRosser
import MathlibNt.SieveTheory.LiLiuGoldbachG12ClippedUniform
import MathlibNt.SieveTheory.LiLiuGoldbachG12ClippedOutputSemantics
import MathlibNt.SieveTheory.LiLiuGoldbachG12RoughElementary
import MathlibNt.SieveTheory.LiLiuGoldbachG12RoughTransport
import MathlibNt.SieveTheory.LiLiuGoldbachG12RoughBudget
import MathlibNt.SieveTheory.LiLiuGoldbachG12MovingEuler
import MathlibNt.SieveTheory.LiLiuGoldbachG12ScaledNormalized
import MathlibNt.SieveTheory.LiLiuGoldbachG12OriginalHighNormalized
import MathlibNt.SieveTheory.LiLiuGoldbachG12RawBoundarySmallMesh
import Lean
set_option pp.deepTerms true
set_option pp.proofs true
set_option pp.maxSteps 1000000
open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let targets : List Name := [`MathlibNt.SieveTheory.LiLiuGoldbachG12ClippedOutput, `MathlibNt.SieveTheory.LiLiuGoldbachG12ClippedRosser, `MathlibNt.SieveTheory.LiLiuGoldbachG12ClippedUniform, `MathlibNt.SieveTheory.LiLiuGoldbachG12ClippedOutputSemantics, `MathlibNt.SieveTheory.LiLiuGoldbachG12RoughElementary, `MathlibNt.SieveTheory.LiLiuGoldbachG12RoughTransport, `MathlibNt.SieveTheory.LiLiuGoldbachG12RoughBudget, `MathlibNt.SieveTheory.LiLiuGoldbachG12MovingEuler, `MathlibNt.SieveTheory.LiLiuGoldbachG12ScaledNormalized, `MathlibNt.SieveTheory.LiLiuGoldbachG12OriginalHighNormalized, `MathlibNt.SieveTheory.LiLiuGoldbachG12RawBoundarySmallMesh]
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

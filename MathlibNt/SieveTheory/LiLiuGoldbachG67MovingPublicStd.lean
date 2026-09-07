import MathlibNt.SieveTheory.LiLiuGoldbachOrdinaryLowerDensityFactors
import MathlibNt.SieveTheory.LiLiuGoldbachOrdinaryLowerDensity
import MathlibNt.SieveTheory.LiLiuGoldbachPairLayerCoordinate
import MathlibNt.SieveTheory.LiLiuGoldbachPairLayerCoordinateConsumers
import MathlibNt.SieveTheory.LiLiuGoldbachCompositeDimension
import MathlibNt.SieveTheory.LiLiuGoldbachCompositeMovingDensity
import MathlibNt.SieveTheory.LiLiuGoldbachCompositeMovingCount
import MathlibNt.SieveTheory.LiLiuGoldbachPairMovingKernel
import MathlibNt.SieveTheory.LiLiuGoldbachG67MovingLower
import Lean
open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let targets : List Name := [`MathlibNt.SieveTheory.LiLiuGoldbachOrdinaryLowerDensityFactors, `MathlibNt.SieveTheory.LiLiuGoldbachOrdinaryLowerDensity, `MathlibNt.SieveTheory.LiLiuGoldbachPairLayerCoordinate, `MathlibNt.SieveTheory.LiLiuGoldbachPairLayerCoordinateConsumers, `MathlibNt.SieveTheory.LiLiuGoldbachCompositeDimension, `MathlibNt.SieveTheory.LiLiuGoldbachCompositeMovingDensity, `MathlibNt.SieveTheory.LiLiuGoldbachCompositeMovingCount, `MathlibNt.SieveTheory.LiLiuGoldbachPairMovingKernel, `MathlibNt.SieveTheory.LiLiuGoldbachG67MovingLower]
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

import MathlibNt.SieveTheory.LiLiuGoldbachG12RoughConnection
import MathlibNt.SieveTheory.LiLiuGoldbachQuadrupleExceptionFibers
import MathlibNt.SieveTheory.LiLiuGoldbachQuadrupleExceptionBudget
import MathlibNt.SieveTheory.LiLiuGoldbachG12BuchstabGeometry
import MathlibNt.SieveTheory.LiLiuGoldbachG12RoughPaid
import Lean
open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let targets : List Name := [`MathlibNt.SieveTheory.LiLiuGoldbachG12RoughConnection, `MathlibNt.SieveTheory.LiLiuGoldbachQuadrupleExceptionFibers, `MathlibNt.SieveTheory.LiLiuGoldbachQuadrupleExceptionBudget, `MathlibNt.SieveTheory.LiLiuGoldbachG12BuchstabGeometry, `MathlibNt.SieveTheory.LiLiuGoldbachG12RoughPaid]
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

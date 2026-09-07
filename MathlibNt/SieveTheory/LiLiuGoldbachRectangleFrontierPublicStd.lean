import MathlibNt.SieveTheory.LiLiuGoldbachG12FlexibleRectangle
import MathlibNt.SieveTheory.LiLiuGoldbachG12FlexibleRectangleC2
import MathlibNt.SieveTheory.LiLiuGoldbachG12RectangleWF
import MathlibNt.SieveTheory.LiLiuGoldbachG12RectangleWFSieve
import MathlibNt.SieveTheory.LiLiuGoldbachG12RectangleWFRemainder
import MathlibNt.SieveTheory.LiLiuGoldbachG12RectangleWFOutput
import MathlibNt.SieveTheory.LiLiuGoldbachG12RectangleWFSmall
import MathlibNt.SieveTheory.LiLiuGoldbachG12ThinCofactorMass
import MathlibNt.SieveTheory.LiLiuGoldbachG12ThinIntegralBudget
import MathlibNt.SieveTheory.LiLiuGoldbachG12RectangleC2Sieve
import Lean
set_option pp.deepTerms true
set_option pp.proofs true
set_option pp.maxSteps 1000000
open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let targets : List Name := [`MathlibNt.SieveTheory.LiLiuGoldbachG12FlexibleRectangle, `MathlibNt.SieveTheory.LiLiuGoldbachG12FlexibleRectangleC2, `MathlibNt.SieveTheory.LiLiuGoldbachG12RectangleWF, `MathlibNt.SieveTheory.LiLiuGoldbachG12RectangleWFSieve, `MathlibNt.SieveTheory.LiLiuGoldbachG12RectangleWFRemainder, `MathlibNt.SieveTheory.LiLiuGoldbachG12RectangleWFOutput, `MathlibNt.SieveTheory.LiLiuGoldbachG12RectangleWFSmall, `MathlibNt.SieveTheory.LiLiuGoldbachG12ThinCofactorMass, `MathlibNt.SieveTheory.LiLiuGoldbachG12ThinIntegralBudget, `MathlibNt.SieveTheory.LiLiuGoldbachG12RectangleC2Sieve]
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

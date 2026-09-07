import MathlibNt.SieveTheory.LiLiuGoldbachCoprimePrimeBox
import MathlibNt.SieveTheory.LiLiuGoldbachCoprimePrimeBoxRectangle
import MathlibNt.SieveTheory.LiLiuGoldbachLogDarboux
import MathlibNt.SieveTheory.LiLiuGoldbachSymmetricPairs
import MathlibNt.SieveTheory.LiLiuGoldbachPrimeDarbouxLower
import MathlibNt.SieveTheory.LiLiuGoldbachG67KernelQuadrature
import MathlibNt.SieveTheory.LiLiuGoldbachG12BuchstabUpperMass
import MathlibNt.SieveTheory.LiLiuGoldbachG12MainMassTransport
import Lean
set_option pp.deepTerms true
set_option pp.proofs true
set_option pp.maxSteps 1000000
open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let targets : List Name := [`MathlibNt.SieveTheory.LiLiuGoldbachCoprimePrimeBox, `MathlibNt.SieveTheory.LiLiuGoldbachCoprimePrimeBoxRectangle, `MathlibNt.SieveTheory.LiLiuGoldbachLogDarboux, `MathlibNt.SieveTheory.LiLiuGoldbachSymmetricPairs, `MathlibNt.SieveTheory.LiLiuGoldbachPrimeDarbouxLower, `MathlibNt.SieveTheory.LiLiuGoldbachG67KernelQuadrature, `MathlibNt.SieveTheory.LiLiuGoldbachG12BuchstabUpperMass, `MathlibNt.SieveTheory.LiLiuGoldbachG12MainMassTransport]
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

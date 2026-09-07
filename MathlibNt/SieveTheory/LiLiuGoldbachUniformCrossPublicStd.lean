import MathlibNt.SieveTheory.LiLiuGoldbachG12BoundingSieve
import MathlibNt.SieveTheory.LiLiuGoldbachG12LinkedSifted
import MathlibNt.SieveTheory.LiLiuGoldbachG12RosserFactor
import MathlibNt.SieveTheory.LiLiuGoldbachG12PaidRosser
import MathlibNt.SieveTheory.LiLiuGoldbachG12OutputEnvelope
import MathlibNt.SieveTheory.LiLiuGoldbachG12PrimeKernel
import MathlibNt.SieveTheory.LiLiuGoldbachG12PrimeKernelLimit
import MathlibNt.SieveTheory.LiLiuGoldbachG12CrossMesh
import MathlibNt.SieveTheory.LiLiuGoldbachG12PrimeKernelIntegralBound
import MathlibNt.SieveTheory.LiLiuGoldbachG12BuchstabMajorantPolynomials
import MathlibNt.SieveTheory.LiLiuGoldbachG12BuchstabMajorant
import MathlibNt.SieveTheory.LiLiuGoldbachG12BuchstabSieve
import MathlibNt.SieveTheory.LiLiuGoldbachG12BuchstabKernelMass
import MathlibNt.SieveTheory.LiLiuGoldbachG12NormalizedIntegralEnvelope
import MathlibNt.SieveTheory.LiLiuGoldbachG12NormalizedIntegralBound
import MathlibNt.SieveTheory.LiLiuGoldbachUniformCrossIntegralLedger
import Lean
set_option pp.deepTerms true
set_option pp.proofs true
set_option pp.maxSteps 1000000
open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let targets : List Name := [`MathlibNt.SieveTheory.LiLiuGoldbachG12BoundingSieve, `MathlibNt.SieveTheory.LiLiuGoldbachG12LinkedSifted, `MathlibNt.SieveTheory.LiLiuGoldbachG12RosserFactor, `MathlibNt.SieveTheory.LiLiuGoldbachG12PaidRosser, `MathlibNt.SieveTheory.LiLiuGoldbachG12OutputEnvelope, `MathlibNt.SieveTheory.LiLiuGoldbachG12PrimeKernel, `MathlibNt.SieveTheory.LiLiuGoldbachG12PrimeKernelLimit, `MathlibNt.SieveTheory.LiLiuGoldbachG12CrossMesh, `MathlibNt.SieveTheory.LiLiuGoldbachG12PrimeKernelIntegralBound, `MathlibNt.SieveTheory.LiLiuGoldbachG12BuchstabMajorantPolynomials, `MathlibNt.SieveTheory.LiLiuGoldbachG12BuchstabMajorant, `MathlibNt.SieveTheory.LiLiuGoldbachG12BuchstabSieve, `MathlibNt.SieveTheory.LiLiuGoldbachG12BuchstabKernelMass, `MathlibNt.SieveTheory.LiLiuGoldbachG12NormalizedIntegralEnvelope, `MathlibNt.SieveTheory.LiLiuGoldbachG12NormalizedIntegralBound, `MathlibNt.SieveTheory.LiLiuGoldbachUniformCrossIntegralLedger]
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

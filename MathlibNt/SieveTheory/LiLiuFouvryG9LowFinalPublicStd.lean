import MathlibNt.SieveTheory.LiLiuFouvryG9AnalyticDensity
import MathlibNt.SieveTheory.LiLiuFouvryG9AnalyticSieve
import MathlibNt.SieveTheory.LiLiuFouvryG9BaseEuler
import MathlibNt.SieveTheory.LiLiuFouvryG9DimensionOne
import MathlibNt.SieveTheory.LiLiuFouvryG9EulerCorrection
import MathlibNt.SieveTheory.LiLiuFouvryG9EulerCorrectionActual
import MathlibNt.SieveTheory.LiLiuFouvryG9EulerCorrectionObstruction
import MathlibNt.SieveTheory.LiLiuFouvryG9EulerEventual
import MathlibNt.SieveTheory.LiLiuFouvryG9ExtendedUpper
import MathlibNt.SieveTheory.LiLiuFouvryG9ExtendedUpperEdge
import MathlibNt.SieveTheory.LiLiuFouvryG9ExtendedUpperScalar
import MathlibNt.SieveTheory.LiLiuFouvryG9ExternalError
import MathlibNt.SieveTheory.LiLiuFouvryG9ExternalExceptional
import MathlibNt.SieveTheory.LiLiuFouvryG9FamilyCost
import MathlibNt.SieveTheory.LiLiuFouvryG9FiniteTransport
import MathlibNt.SieveTheory.LiLiuFouvryG9IntegerFibre
import MathlibNt.SieveTheory.LiLiuFouvryG9KernelBudget
import MathlibNt.SieveTheory.LiLiuFouvryG9LiteralMother
import MathlibNt.SieveTheory.LiLiuFouvryG9LowFinal
import MathlibNt.SieveTheory.LiLiuFouvryG9MainNormalization
import MathlibNt.SieveTheory.LiLiuFouvryG9MainScalar
import MathlibNt.SieveTheory.LiLiuFouvryG9MainUpper
import MathlibNt.SieveTheory.LiLiuFouvryG9MassKernel
import MathlibNt.SieveTheory.LiLiuFouvryG9MotherSieve
import MathlibNt.SieveTheory.LiLiuFouvryG9NormalizedError
import MathlibNt.SieveTheory.LiLiuFouvryG9NormalizedMass
import MathlibNt.SieveTheory.LiLiuFouvryG9PairPrefixPNT
import MathlibNt.SieveTheory.LiLiuFouvryG9PrefixWeights
import MathlibNt.SieveTheory.LiLiuFouvryG9PrimeMassUpper
import MathlibNt.SieveTheory.LiLiuFouvryG9ProductFibre
import MathlibNt.SieveTheory.LiLiuFouvryG9ProductFibreActual
import MathlibNt.SieveTheory.LiLiuFouvryG9ProgressionDensity
import MathlibNt.SieveTheory.LiLiuFouvryG9ProgressionDensityDimension
import MathlibNt.SieveTheory.LiLiuFouvryG9RectanglePrefixFinite
import MathlibNt.SieveTheory.LiLiuFouvryG9RectanglePrefixPNT
import MathlibNt.SieveTheory.LiLiuFouvryG9RectangleSieve
import MathlibNt.SieveTheory.LiLiuFouvryG9ReducedWeights
import MathlibNt.SieveTheory.LiLiuFouvryG9RelaxedIntegral
import MathlibNt.SieveTheory.LiLiuFouvryG9RelaxedIntegralContinuous
import MathlibNt.SieveTheory.LiLiuFouvryG9RelaxedIntegralEventual
import MathlibNt.SieveTheory.LiLiuFouvryG9RelaxedIntegralFinite
import MathlibNt.SieveTheory.LiLiuFouvryG9RelaxedMass
import MathlibNt.SieveTheory.LiLiuFouvryG9RemainderMajorant
import MathlibNt.SieveTheory.LiLiuFouvryG9RemainderMajorantActual
import MathlibNt.SieveTheory.LiLiuFouvryG9RemainderMajorantCounting
import MathlibNt.SieveTheory.LiLiuFouvryG9RemainderMajorantDiscrepancy
import MathlibNt.SieveTheory.LiLiuFouvryG9S5Kernel
import MathlibNt.SieveTheory.LiLiuFouvryG9S5MassUpper
import MathlibNt.SieveTheory.LiLiuFouvryG9SieveTotal
import MathlibNt.SieveTheory.LiLiuFouvryG9SiftedMassUpper
import MathlibNt.SieveTheory.LiLiuFouvryG9SmallOutput
import MathlibNt.SieveTheory.LiLiuFouvryG9SmallOutputPrime
import MathlibNt.SieveTheory.LiLiuFouvryG9ThirdPrimeEventual
import MathlibNt.SieveTheory.LiLiuFouvryG9TransportPayment
import MathlibNt.SieveTheory.LiLiuFouvryG9WFBridge
import MathlibNt.SieveTheory.LiLiuFouvryG9WFFamily
import MathlibNt.SieveTheory.LiLiuFouvryG9WFLevel
import MathlibNt.SieveTheory.LiLiuFouvryG9WeightedBoundary
import MathlibNt.SieveTheory.LiLiuFouvryG9WeightedBoundaryGeometry
import MathlibNt.SieveTheory.LiLiuFouvryG9WeightedBoundaryIntegral
import MathlibNt.SieveTheory.LiLiuFouvryG9WeightedBoundaryKernel
import MathlibNt.SieveTheory.LiLiuFouvryG9WeightedPrefix
import MathlibNt.SieveTheory.LiLiuFouvryG9WeightedSieve
import Lean
open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let targets : List Name := [`MathlibNt.SieveTheory.LiLiuPrereqWFDividedPowers, `MathlibNt.SieveTheory.LiLiuPrereqWFBoxSquarefree, `MathlibNt.SieveTheory.LiLiuPrereqWFBoxAllocation, `MathlibNt.SieveTheory.LiLiuPrereqWFCommon, `MathlibNt.SieveTheory.LiLiuPrereqWFSeparated, `MathlibNt.SieveTheory.LiLiuPrereqWFBoxCoefficients, `MathlibNt.SieveTheory.LiLiuPrereqWFAdmissibility, `MathlibNt.SieveTheory.LiLiuPrereqWFBoxFamily, `MathlibNt.SieveTheory.LiLiuPrereqWFGeometry, `MathlibNt.SieveTheory.LiLiuPrereqWFGeometricBoxes, `MathlibNt.SieveTheory.LiLiuPrereqWFSmallRosser, `MathlibNt.SieveTheory.LiLiuPrereqWFRoundedAdmissibility, `MathlibNt.SieveTheory.LiLiuPrereqWFSignedRounding, `MathlibNt.SieveTheory.LiLiuPrereqWFBoxProfiles, `MathlibNt.SieveTheory.LiLiuPrereqWFSignedFamily, `MathlibNt.SieveTheory.LiLiuPrereqWFSignedSieve, `MathlibNt.SieveTheory.LiLiuPrereqWFSmallDensity, `MathlibNt.SieveTheory.LiLiuPrereqWFRounding, `MathlibNt.SieveTheory.LiLiuPrereqWFBoundaryLayers, `MathlibNt.SieveTheory.LiLiuPrereqWFIntervalDensity, `MathlibNt.SieveTheory.LiLiuPrereqWFZeroDensity, `MathlibNt.SieveTheory.LiLiuPrereqWFParameters, `MathlibNt.SieveTheory.LiLiuPrereqWFAnalytic, `MathlibNt.SieveTheory.LiLiuPrereqWFProducerBridgeCoefficients, `MathlibNt.SieveTheory.LiLiuPrereqWFProducerBridgeSieve, `MathlibNt.SieveTheory.LiLiuPrereqWFProducerBridgeSmall, `MathlibNt.SieveTheory.LiLiuPrereqWFProducerBridge, `MathlibNt.SieveTheory.LiLiuPrereqWFFundamentalLemma, `MathlibNt.SieveTheory.LiLiuPrereqWFSignedDensity, `MathlibNt.SieveTheory.LiLiuPrereqWFRoughComparison, `MathlibNt.SieveTheory.LiLiuPrereqWFRoughEuler, `MathlibNt.SieveTheory.LiLiuPrereqWFCollisionAnalytic, `MathlibNt.SieveTheory.LiLiuPrereqWFBoundaryAnalytic, `MathlibNt.SieveTheory.LiLiuPrereqWFBoundaryAnalyticMass, `MathlibNt.SieveTheory.LiLiuPrereqWFBoundaryAnalyticTarget, `MathlibNt.SieveTheory.LiLiuPrereqWFRoughDensityTarget, `MathlibNt.SieveTheory.LiLiuPrereqWFCoarseDensitySource, `MathlibNt.SieveTheory.LiLiuPrereqWFCoarseDensity, `MathlibNt.SieveTheory.LiLiuPrereqWFCoarseDensityTarget, `MathlibNt.SieveTheory.LiLiuPrereqWFFamilyDensity, `MathlibNt.SieveTheory.LiLiuPrereqWFTagCardinality, `MathlibNt.SieveTheory.LiLiuPrereqWFTagCardinalityExp, `MathlibNt.SieveTheory.LiLiuPrereqWFSignedRemainder, `MathlibNt.SieveTheory.LiLiuPrereqWFInternalSieve, `MathlibNt.SieveTheory.LiLiuPrereqWFPrimeSquareMass, `MathlibNt.SieveTheory.LiLiuPrereqWFUnmaskedSupport, `MathlibNt.SieveTheory.LiLiuPrereqWFUnmaskedRemainder, `MathlibNt.SieveTheory.LiLiuPrereqWFExternalParameters, `MathlibNt.SieveTheory.LiLiuPrereqWFExternalFamily, `MathlibNt.SieveTheory.LiLiuPrereqWFProgressionAdapter, `MathlibNt.SieveTheory.LiLiuPrereqWFExternalTransport, `MathlibNt.SieveTheory.LiLiuPrereqWFExternalPrimeDensity, `MathlibNt.SieveTheory.LiLiuPrereqWFEdgeDensityBounds, `MathlibNt.SieveTheory.LiLiuPrereqWFEdgeDensityScalar, `MathlibNt.SieveTheory.LiLiuPrereqWFCoordinateShift, `MathlibNt.SieveTheory.LiLiuPrereqWFEdgeDensity, `MathlibNt.SieveTheory.LiLiuPrereqWFExternalSieve, `MathlibNt.SieveTheory.LiLiuFouvryG9ProgressionDensity, `MathlibNt.SieveTheory.LiLiuFouvryG9ProgressionDensityDimension, `MathlibNt.SieveTheory.LiLiuFouvryG9ExtendedUpperScalar, `MathlibNt.SieveTheory.LiLiuFouvryG9ExtendedUpperEdge, `MathlibNt.SieveTheory.LiLiuFouvryG9ExtendedUpper, `MathlibNt.SieveTheory.LiLiuFouvryG9IntegerFibre, `MathlibNt.SieveTheory.LiLiuFouvryG9WeightedSieve, `MathlibNt.SieveTheory.LiLiuFouvryG9ProductFibre, `MathlibNt.SieveTheory.LiLiuFouvryG9ProductFibreActual, `MathlibNt.SieveTheory.LiLiuFouvryG9RectangleSieve, `MathlibNt.SieveTheory.LiLiuFouvryG9RemainderMajorant, `MathlibNt.SieveTheory.LiLiuFouvryG9RemainderMajorantCounting, `MathlibNt.SieveTheory.LiLiuFouvryG9RemainderMajorantDiscrepancy, `MathlibNt.SieveTheory.LiLiuFouvryG9RemainderMajorantActual, `MathlibNt.SieveTheory.LiLiuFouvryG9WFBridge, `MathlibNt.SieveTheory.LiLiuFouvryG9WFLevel, `MathlibNt.SieveTheory.LiLiuPrereqWFTransportAbsorption, `MathlibNt.SieveTheory.LiLiuFouvryG9TransportPayment, `MathlibNt.SieveTheory.LiLiuFouvryG9ExternalExceptional, `MathlibNt.SieveTheory.LiLiuFouvryG9ReducedWeights, `MathlibNt.SieveTheory.LiLiuFouvryG9FiniteTransport, `MathlibNt.SieveTheory.LiLiuFouvryG9MainNormalization, `MathlibNt.SieveTheory.LiLiuFouvryG9FamilyCost, `MathlibNt.SieveTheory.LiLiuFouvryG9WFFamily, `MathlibNt.SieveTheory.LiLiuFouvryG9ExternalError, `MathlibNt.SieveTheory.LiLiuFouvryG9SieveTotal, `MathlibNt.SieveTheory.LiLiuFouvryG9MotherSieve, `MathlibNt.SieveTheory.LiLiuFouvryG9AnalyticDensity, `MathlibNt.SieveTheory.LiLiuFouvryG9MainUpper, `MathlibNt.SieveTheory.LiLiuFouvryG9AnalyticSieve, `MathlibNt.SieveTheory.LiLiuFouvryG9BaseEuler, `MathlibNt.SieveTheory.LiLiuFouvryG9DimensionOne, `MathlibNt.SieveTheory.LiLiuFouvryG9EulerCorrection, `MathlibNt.SieveTheory.LiLiuFouvryG9EulerCorrectionActual, `MathlibNt.SieveTheory.LiLiuFouvryG9EulerCorrectionObstruction, `MathlibNt.SieveTheory.LiLiuFouvryG9ThirdPrimeEventual, `MathlibNt.SieveTheory.LiLiuFouvryG9RelaxedMass, `MathlibNt.SieveTheory.LiLiuFouvryG9EulerEventual, `MathlibNt.SieveTheory.LiLiuFouvryG9RelaxedIntegral, `MathlibNt.SieveTheory.LiLiuFouvryG9RelaxedIntegralFinite, `MathlibNt.SieveTheory.LiLiuFouvryG9RelaxedIntegralEventual, `MathlibNt.SieveTheory.LiLiuFouvryG9RelaxedIntegralContinuous, `MathlibNt.SieveTheory.LiLiuFouvryG9WeightedBoundary, `MathlibNt.SieveTheory.LiLiuFouvryG9WeightedBoundaryGeometry, `MathlibNt.SieveTheory.LiLiuFouvryG9WeightedBoundaryKernel, `MathlibNt.SieveTheory.LiLiuFouvryG9WeightedBoundaryIntegral, `MathlibNt.SieveTheory.LiLiuFouvryG9MainScalar, `MathlibNt.SieveTheory.LiLiuFouvryG9KernelBudget, `MathlibNt.SieveTheory.LiLiuFouvryG9SmallOutput, `MathlibNt.SieveTheory.LiLiuFouvryG9SmallOutputPrime, `MathlibNt.SieveTheory.LiLiuFouvryG9LiteralMother, `MathlibNt.SieveTheory.LiLiuFouvryG9SiftedMassUpper, `MathlibNt.SieveTheory.LiLiuFouvryG9S5MassUpper, `MathlibNt.SieveTheory.LiLiuFouvryG9NormalizedMass, `MathlibNt.SieveTheory.LiLiuFouvryG9NormalizedError, `MathlibNt.SieveTheory.LiLiuFouvryG9RectanglePrefixFinite, `MathlibNt.SieveTheory.LiLiuFouvryG9RectanglePrefixPNT, `MathlibNt.SieveTheory.LiLiuFouvryG9WeightedPrefix, `MathlibNt.SieveTheory.LiLiuFouvryG9PrefixWeights, `MathlibNt.SieveTheory.LiLiuFouvryG9PairPrefixPNT, `MathlibNt.SieveTheory.LiLiuFouvryG9MassKernel, `MathlibNt.SieveTheory.LiLiuFouvryG9S5Kernel, `MathlibNt.SieveTheory.LiLiuFouvryG9LowFinal, `MathlibNt.SieveTheory.LiLiuFouvryG9PrimeMassUpper]
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

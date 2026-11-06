-- UNCOMPILED scratch template. Requires a future root-scheduled Lean check.
-- Reuses ConstantInfo kind classification and binder/mdata traversal from
-- research/chen-audit/TypeCensus.lean; emits full trees, not Lean hash values.
import Lean
import AnalyticNumberTheory.PrimeDistribution.PrimeNumberTheorem
import AnalyticNumberTheory.Sieve.SelbergUpperBound
import Hf4QuadAggregate
import Hf4QuadBatch0
import Hf4QuadBatch1
import Hf4QuadBatch10
import Hf4QuadBatch11
import Hf4QuadBatch12
import Hf4QuadBatch2
import Hf4QuadBatch3
import Hf4QuadBatch4
import Hf4QuadBatch5
import Hf4QuadBatch6
import Hf4QuadBatch7
import Hf4QuadBatch8
import Hf4QuadBatch9
import Hf4QuadCompactKernel
import Hf4QuadCompactKernelCore
import Hf4QuadEndpointBridges
import Hf4QuadExactOperations
import Hf4QuadIntegral
import Hf4QuadKernel
import Hf4QuadKernelData
import Hf4QuadModel
import Hf4QuadModelBasic
import Hf4QuadModelRadical
import Hf4QuadPanel0
import Hf4QuadRatCore
import Hf4QuadRationalModel
import Hf4QuadRationalModelCore
import Hf4RadicalBounds
import Hf4TargetConstants
import MathlibNt.AnalyticNumberTheory.LargeSieve.BombieriDavenport
import MathlibNt.SieveTheory.Distribution.LiuPan.LiuPanAggregatePsiCharacters
import MathlibNt.SieveTheory.Distribution.LiuPan.LiuPanAggregatePsiDyadic
import MathlibNt.SieveTheory.Distribution.LiuPan.LiuPanCombinedAbel
import MathlibNt.SieveTheory.Distribution.LiuPan.LiuPanCombinedInverseLog
import MathlibNt.SieveTheory.Distribution.LiuPan.LiuPanPrimePowerCharacters
import MathlibNt.SieveTheory.Distribution.LiuPan.LiuPanPrimePowerLargeSieve
import MathlibNt.SieveTheory.Distribution.LiuPan.LiuPanPrimitivePerron
import MathlibNt.SieveTheory.JurkatRichert1965ChenGammaOneQOne
import MathlibNt.SieveTheory.LiLiuGoldbachB10LogGridLimit
import MathlibNt.SieveTheory.LiLiuPrereqBuchstabPNT
import MathlibNt.SieveTheory.LinearSieve.Suzuki.SuzukiSection13PairingZero
import MathlibNt.SieveTheory.Liu.PrimePairs.LiuLogCoordinates
import MathlibNt.SieveTheory.Liu.PrimePairs.LiuPrimePairLogGridLimit
import MathlibNt.SieveTheory.Selberg.Liu.LiuSelbergOptimalWeights
import MathlibNt.SieveTheory.Selberg.TruncatedOptimalWeights
import PrimeNumberTheoremAnd.MediumPNTQualitativeBridge
import PrimeNumberTheoremAnd.PNTEnvironmentCompat
import SigmaRationalOuterActual
import SigmaRationalOuterData
import TerminalEPrimitive
import TerminalERadical

open Lean
namespace PublicInterfaceAudit

private def node (tag : String) (args : Array Json := #[]) : Json :=
  .arr (#[toJson tag] ++ args)

private def nameTree : Name → Json
  | .anonymous => node "anonymous"
  | .str p s => node "str" #[nameTree p, toJson s]
  | .num p n => node "num" #[nameTree p, toJson n]

private def paramIndex (n : Name) : List Name → Option Nat
  | [] => none
  | p :: ps => if n == p then some 0 else (paramIndex n ps).map (· + 1)

private partial def levelTree (ps : List Name) : Level → Except String Json
  | .zero => return node "zero"
  | .succ u => return node "succ" #[← levelTree ps u]
  | .max u v => return node "max" #[← levelTree ps u, ← levelTree ps v]
  | .imax u v => return node "imax" #[← levelTree ps u, ← levelTree ps v]
  | .param p => match paramIndex p ps with
    | some i => return node "param" #[toJson i]
    | none => throw s!"Undeclared universe parameter: {p}"
  | .mvar _ => throw "Universe metavariable in public declaration"

private def binderTree : BinderInfo → Json
  | .default => toJson "default"
  | .implicit => toJson "implicit"
  | .strictImplicit => toJson "strictImplicit"
  | .instImplicit => toJson "instImplicit"

private partial def exprTree (ps : List Name) : Expr → Except String Json
  | .bvar i => return node "bvar" #[toJson i]
  | .fvar _ => throw "Free variable in public declaration"
  | .mvar _ => throw "Expression metavariable in public declaration"
  | .sort u => return node "sort" #[← levelTree ps u]
  | .const n us => do
    let levels ← us.mapM (levelTree ps)
    return node "const" #[nameTree n, .arr levels.toArray]
  | .app f x => return node "app" #[← exprTree ps f, ← exprTree ps x]
  | .lam _ t b bi => return node "lam" #[binderTree bi, ← exprTree ps t, ← exprTree ps b]
  | .forallE _ t b bi => return node "forall" #[binderTree bi, ← exprTree ps t, ← exprTree ps b]
  | .letE _ t v b nondep => return node "let" #[toJson nondep, ← exprTree ps t, ← exprTree ps v, ← exprTree ps b]
  | .lit (.natVal n) => return node "nat" #[toJson n]
  | .lit (.strVal s) => return node "string" #[toJson s]
  | .mdata _ e => exprTree ps e
  | .proj n i e => return node "proj" #[nameTree n, toJson i, ← exprTree ps e]

private def kind : ConstantInfo → String
  | .axiomInfo _ => "axiom" | .defnInfo _ => "definition"
  | .thmInfo _ => "theorem" | .opaqueInfo _ => "opaque"
  | .quotInfo _ => "quotient" | .inductInfo _ => "inductive"
  | .ctorInfo _ => "constructor" | .recInfo _ => "recursor"

private def declaration (ci : ConstantInfo) (includeDefinitions : Bool) : Except String Json := do
  let ty ← exprTree ci.levelParams ci.type
  let value ←
    if includeDefinitions then
      match ci with
      | .defnInfo d => exprTree ci.levelParams d.value
      | _ => throw s!"Requested definition value for non-definition: {ci.name}"
    else pure Json.null
  return Json.mkObj [
    ("name", toJson ci.name.toString), ("kind", toJson (kind ci)),
    ("levelParamCount", toJson ci.levelParams.length),
    ("type", ty), ("definitionValue", value)]

run_cmd do
  let env ← Lean.getEnv
  let requested : List Name := [(Name.str (Name.str (Name.str Name.anonymous "AnalyticNumberTheory") "LargeSieve") "primitiveCharacterInvEquiv"), (Name.str (Name.str (Name.str Name.anonymous "AnalyticNumberTheory") "PrimeDistribution") "NatPrimeCountingPNT"), (Name.str (Name.str (Name.str Name.anonymous "AnalyticNumberTheory") "Sieve") "UniformSelbergUpperBound"), (Name.str (Name.str (Name.str Name.anonymous "AnalyticNumberTheory") "Sieve") "optimalSelbergWeight"), (Name.str (Name.str (Name.str Name.anonymous "AnalyticNumberTheory") "Sieve") "optimalSelbergX"), (Name.str (Name.str (Name.str Name.anonymous "AnalyticNumberTheory") "Sieve") "selbergLambdaSquared"), (Name.str (Name.str (Name.str Name.anonymous "AnalyticNumberTheory") "Sieve") "selbergMainTerm"), (Name.str (Name.str (Name.str Name.anonymous "Hf4Quad") "Cubic") "eval"), (Name.str (Name.str (Name.str Name.anonymous "Hf4Quad") "Cubic") "norm"), (Name.str (Name.str (Name.str Name.anonymous "Hf4Quad") "Cubic") "primitive"), (Name.str (Name.str Name.anonymous "Hf4Quad") "Model"), (Name.str (Name.str (Name.str (Name.str Name.anonymous "Hf4Quad") "RationalModel") "Certificate") "Valid"), (Name.str (Name.str (Name.str (Name.str Name.anonymous "Hf4Quad") "RationalModel") "Certificate") "cubic"), (Name.str (Name.str (Name.str (Name.str Name.anonymous "Hf4Quad") "RationalModel") "Certificate") "norm"), (Name.str (Name.str (Name.str Name.anonymous "Hf4Quad") "RationalModel") "addCondition"), (Name.str (Name.str (Name.str Name.anonymous "Hf4Quad") "RationalModel") "addExact"), (Name.str (Name.str (Name.str Name.anonymous "Hf4Quad") "RationalModel") "invCondition"), (Name.str (Name.str (Name.str Name.anonymous "Hf4Quad") "RationalModel") "lower"), (Name.str (Name.str (Name.str Name.anonymous "Hf4Quad") "RationalModel") "mulCondition"), (Name.str (Name.str (Name.str Name.anonymous "Hf4Quad") "RationalModel") "neg"), (Name.str (Name.str (Name.str Name.anonymous "Hf4Quad") "RationalModel") "residual"), (Name.str (Name.str (Name.str Name.anonymous "Hf4Quad") "RationalModel") "scale"), (Name.str (Name.str Name.anonymous "Hf4Quad") "compactKernel"), (Name.str (Name.str Name.anonymous "Hf4Quad") "kernel"), (Name.str (Name.str Name.anonymous "Hf4Quad") "low"), (Name.str (Name.str Name.anonymous "Hf4Quad") "lowZ"), (Name.str (Name.str Name.anonymous "Hf4Quad") "mulError"), (Name.str (Name.str Name.anonymous "Hf4Quad") "sl"), (Name.str (Name.str Name.anonymous "Hf4Quad") "slCompact"), (Name.str (Name.str Name.anonymous "Hf4Quad") "su"), (Name.str (Name.str Name.anonymous "Hf4Quad") "suCompact"), (Name.str (Name.str Name.anonymous "Hf4Quad") "up"), (Name.str (Name.str Name.anonymous "Hf4Quad") "upZ"), (Name.str (Name.str Name.anonymous "LiLiuPrereqBuchstab") "primeErrorEnvelope"), (Name.str (Name.str Name.anonymous "LiLiuPrereqBuchstab") "primeErrorStart"), (Name.str (Name.str Name.anonymous "LiLiuPrereqBuchstab") "primePi"), (Name.str (Name.str Name.anonymous "LiLiuPrereqBuchstab") "primeRelativeError"), (Name.str (Name.str (Name.str (Name.str (Name.str Name.anonymous "MathlibNt") "SieveTheory") "JurkatRichert1965ChenGammaOneQOne") "RegularSource") "boundingSieve"), (Name.str (Name.str (Name.str (Name.str (Name.str Name.anonymous "MathlibNt") "SieveTheory") "JurkatRichert1965ChenGammaOneQOne") "RegularSource") "levelSelbergDenominator"), (Name.str (Name.str (Name.str (Name.str (Name.str Name.anonymous "MathlibNt") "SieveTheory") "JurkatRichert1965ChenGammaOneQOne") "RegularSource") "levelSelbergWeight"), (Name.str (Name.str (Name.str (Name.str (Name.str Name.anonymous "MathlibNt") "SieveTheory") "JurkatRichert1965ChenGammaOneQOne") "RegularSource") "literalQuotient"), (Name.str (Name.str (Name.str (Name.str (Name.str Name.anonymous "MathlibNt") "SieveTheory") "JurkatRichert1965ChenGammaOneQOne") "RegularSource") "realLevelSelbergDenominator"), (Name.str (Name.str (Name.str (Name.str (Name.str Name.anonymous "MathlibNt") "SieveTheory") "JurkatRichert1965ChenGammaOneQOne") "RegularSource") "realLevelSelbergWeight"), (Name.str (Name.str (Name.str (Name.str Name.anonymous "MathlibNt") "SieveTheory") "JurkatRichert1965ChenGammaOneQOne") "alternatingSign"), (Name.str (Name.str (Name.str (Name.str Name.anonymous "MathlibNt") "SieveTheory") "JurkatRichert1965ChenGammaOneQOne") "alternatingSum"), (Name.str (Name.str (Name.str (Name.str Name.anonymous "MathlibNt") "SieveTheory") "JurkatRichert1965ChenGammaOneQOne") "chainCutoff"), (Name.str (Name.str (Name.str (Name.str Name.anonymous "MathlibNt") "SieveTheory") "JurkatRichert1965ChenGammaOneQOne") "chainScale"), (Name.str (Name.str (Name.str (Name.str Name.anonymous "MathlibNt") "SieveTheory") "JurkatRichert1965ChenGammaOneQOne") "chainSiftedCount"), (Name.str (Name.str (Name.str (Name.str Name.anonymous "MathlibNt") "SieveTheory") "JurkatRichert1965ChenGammaOneQOne") "conditionedCarrier"), (Name.str (Name.str (Name.str (Name.str Name.anonymous "MathlibNt") "SieveTheory") "JurkatRichert1965ChenGammaOneQOne") "conditionedSiftedCountOn"), (Name.str (Name.str (Name.str (Name.str Name.anonymous "MathlibNt") "SieveTheory") "JurkatRichert1965ChenGammaOneQOne") "excludedSiftingFactor"), (Name.str (Name.str (Name.str (Name.str Name.anonymous "MathlibNt") "SieveTheory") "JurkatRichert1965ChenGammaOneQOne") "excludedSiftingPrimes"), (Name.str (Name.str (Name.str (Name.str Name.anonymous "MathlibNt") "SieveTheory") "JurkatRichert1965ChenGammaOneQOne") "finiteExpansion"), (Name.str (Name.str (Name.str (Name.str Name.anonymous "MathlibNt") "SieveTheory") "JurkatRichert1965ChenGammaOneQOne") "fourOneCutoff"), (Name.str (Name.str (Name.str (Name.str Name.anonymous "MathlibNt") "SieveTheory") "JurkatRichert1965ChenGammaOneQOne") "literalQuotientCarrier"), (Name.str (Name.str (Name.str (Name.str Name.anonymous "MathlibNt") "SieveTheory") "JurkatRichert1965ChenGammaOneQOne") "localDensity"), (Name.str (Name.str (Name.str (Name.str Name.anonymous "MathlibNt") "SieveTheory") "JurkatRichert1965ChenGammaOneQOne") "natReciprocalMonoidHom"), (Name.str (Name.str (Name.str (Name.str Name.anonymous "MathlibNt") "SieveTheory") "JurkatRichert1965ChenGammaOneQOne") "radicalQuotientEmbedding"), (Name.str (Name.str (Name.str (Name.str Name.anonymous "MathlibNt") "SieveTheory") "JurkatRichert1965ChenGammaOneQOne") "reciprocalTotientArithmeticFunction"), (Name.str (Name.str (Name.str (Name.str Name.anonymous "MathlibNt") "SieveTheory") "JurkatRichert1965ChenGammaOneQOne") "selbergPsi"), (Name.str (Name.str (Name.str (Name.str Name.anonymous "MathlibNt") "SieveTheory") "JurkatRichert1965ChenGammaOneQOne") "selbergPsiCarrier"), (Name.str (Name.str (Name.str (Name.str Name.anonymous "MathlibNt") "SieveTheory") "JurkatRichert1965ChenGammaOneQOne") "selbergRealPsi"), (Name.str (Name.str (Name.str (Name.str Name.anonymous "MathlibNt") "SieveTheory") "JurkatRichert1965ChenGammaOneQOne") "selbergRealPsiCarrier"), (Name.str (Name.str (Name.str (Name.str Name.anonymous "MathlibNt") "SieveTheory") "JurkatRichert1965ChenGammaOneQOne") "selbergRealReciprocalTotientCarrier"), (Name.str (Name.str (Name.str (Name.str Name.anonymous "MathlibNt") "SieveTheory") "JurkatRichert1965ChenGammaOneQOne") "selbergRealReciprocalTotientSum"), (Name.str (Name.str (Name.str (Name.str Name.anonymous "MathlibNt") "SieveTheory") "JurkatRichert1965ChenGammaOneQOne") "selbergRealSmoothReciprocalSum"), (Name.str (Name.str (Name.str (Name.str Name.anonymous "MathlibNt") "SieveTheory") "JurkatRichert1965ChenGammaOneQOne") "selbergReciprocalTotientCarrier"), (Name.str (Name.str (Name.str (Name.str Name.anonymous "MathlibNt") "SieveTheory") "JurkatRichert1965ChenGammaOneQOne") "selbergReciprocalTotientSum"), (Name.str (Name.str (Name.str (Name.str Name.anonymous "MathlibNt") "SieveTheory") "JurkatRichert1965ChenGammaOneQOne") "selbergSmoothReciprocalSum"), (Name.str (Name.str (Name.str (Name.str Name.anonymous "MathlibNt") "SieveTheory") "JurkatRichert1965ChenGammaOneQOne") "selbergSmoothRpowSum"), (Name.str (Name.str (Name.str (Name.str Name.anonymous "MathlibNt") "SieveTheory") "JurkatRichert1965ChenGammaOneQOne") "sieveProduct"), (Name.str (Name.str (Name.str (Name.str Name.anonymous "MathlibNt") "SieveTheory") "JurkatRichert1965ChenGammaOneQOne") "siftedCount"), (Name.str (Name.str (Name.str (Name.str Name.anonymous "MathlibNt") "SieveTheory") "JurkatRichert1965ChenGammaOneQOne") "siftedCountOn"), (Name.str (Name.str (Name.str (Name.str Name.anonymous "MathlibNt") "SieveTheory") "JurkatRichert1965ChenGammaOneQOne") "siftingPrimes"), (Name.str (Name.str (Name.str (Name.str Name.anonymous "MathlibNt") "SieveTheory") "JurkatRichert1965ChenGammaOneQOne") "terminalTheta"), (Name.str (Name.str (Name.str (Name.str Name.anonymous "MathlibNt") "SieveTheory") "JurkatRichert1965ChenGammaOneQOne") "theoremOneBoundaryChain"), (Name.str (Name.str (Name.str (Name.str Name.anonymous "MathlibNt") "SieveTheory") "JurkatRichert1965ChenGammaOneQOne") "theoremOneBoundaryCumulative"), (Name.str (Name.str (Name.str (Name.str Name.anonymous "MathlibNt") "SieveTheory") "JurkatRichert1965ChenGammaOneQOne") "theoremOneBoundaryDepthSum"), (Name.str (Name.str (Name.str (Name.str Name.anonymous "MathlibNt") "SieveTheory") "JurkatRichert1965ChenGammaOneQOne") "theoremOneBoundaryPrimes"), (Name.str (Name.str (Name.str (Name.str Name.anonymous "MathlibNt") "SieveTheory") "JurkatRichert1965ChenGammaOneQOne") "theoremOneInteriorChain"), (Name.str (Name.str (Name.str (Name.str Name.anonymous "MathlibNt") "SieveTheory") "JurkatRichert1965ChenGammaOneQOne") "theoremOneInteriorCumulative"), (Name.str (Name.str (Name.str (Name.str Name.anonymous "MathlibNt") "SieveTheory") "JurkatRichert1965ChenGammaOneQOne") "theoremOneInteriorDepthSum"), (Name.str (Name.str (Name.str (Name.str Name.anonymous "MathlibNt") "SieveTheory") "JurkatRichert1965ChenGammaOneQOne") "theoremOneInteriorPrimes"), (Name.str (Name.str (Name.str (Name.str Name.anonymous "MathlibNt") "SieveTheory") "JurkatRichert1965ChenGammaOneQOne") "theoremOneRecursiveExpansion"), (Name.str (Name.str (Name.str (Name.str Name.anonymous "MathlibNt") "SieveTheory") "JurkatRichert1965ChenGammaOneQOne") "theoremOneTerminalDepthSum"), (Name.str (Name.str (Name.str (Name.str Name.anonymous "MathlibNt") "SieveTheory") "JurkatRichert1965ChenGammaOneQOne") "threeNineCutoff"), (Name.str (Name.str (Name.str (Name.str (Name.str Name.anonymous "MathlibNt") "SieveTheory") "LiLiuOnePlusOneNine") "GoldbachBig") "goldbachB10MainIntegral"), (Name.str (Name.str (Name.str (Name.str Name.anonymous "MathlibNt") "SieveTheory") "LiuWeight") "LiuSelbergDenominatorLowerBound"), (Name.str (Name.str (Name.str (Name.str Name.anonymous "MathlibNt") "SieveTheory") "LiuWeight") "liuLogAmbientBox"), (Name.str (Name.str (Name.str (Name.str Name.anonymous "MathlibNt") "SieveTheory") "LiuWeight") "liuLogDensity"), (Name.str (Name.str (Name.str (Name.str Name.anonymous "MathlibNt") "SieveTheory") "LiuWeight") "liuLogExcessStrip"), (Name.str (Name.str (Name.str (Name.str Name.anonymous "MathlibNt") "SieveTheory") "LiuWeight") "liuLogGridCell"), (Name.str (Name.str (Name.str (Name.str Name.anonymous "MathlibNt") "SieveTheory") "LiuWeight") "liuLogGridRegion"), (Name.str (Name.str (Name.str (Name.str Name.anonymous "MathlibNt") "SieveTheory") "LiuWeight") "liuLogGridUpperIntegrand"), (Name.str (Name.str (Name.str (Name.str Name.anonymous "MathlibNt") "SieveTheory") "LiuWeight") "liuLogIntegrand"), (Name.str (Name.str (Name.str (Name.str Name.anonymous "MathlibNt") "SieveTheory") "LiuWeight") "liuLogKernel"), (Name.str (Name.str (Name.str (Name.str Name.anonymous "MathlibNt") "SieveTheory") "LiuWeight") "liuLogSourceRegion"), (Name.str (Name.str (Name.str (Name.str Name.anonymous "MathlibNt") "SieveTheory") "LiuWeight") "liuPanAPPsi"), (Name.str (Name.str (Name.str (Name.str Name.anonymous "MathlibNt") "SieveTheory") "LiuWeight") "liuPanAPPsiDiscrepancy"), (Name.str (Name.str (Name.str (Name.str Name.anonymous "MathlibNt") "SieveTheory") "LiuWeight") "liuPanAbelSourceCutoff"), (Name.str (Name.str (Name.str (Name.str Name.anonymous "MathlibNt") "SieveTheory") "LiuWeight") "liuPanAggregateAPPsiDiscrepancy"), (Name.str (Name.str (Name.str (Name.str Name.anonymous "MathlibNt") "SieveTheory") "LiuWeight") "liuPanAggregateInverseLogDeterministicMaxL"), (Name.str (Name.str (Name.str (Name.str Name.anonymous "MathlibNt") "SieveTheory") "LiuWeight") "liuPanAggregateInverseLogDeterministicMaxY"), (Name.str (Name.str (Name.str (Name.str Name.anonymous "MathlibNt") "SieveTheory") "LiuWeight") "liuPanAggregateInverseLogDeterministicTerm"), (Name.str (Name.str (Name.str (Name.str Name.anonymous "MathlibNt") "SieveTheory") "LiuWeight") "liuPanAggregateInverseLogNoncoprimeCorrection"), (Name.str (Name.str (Name.str (Name.str Name.anonymous "MathlibNt") "SieveTheory") "LiuWeight") "liuPanAggregateInverseLogNonprincipalPsiTerm"), (Name.str (Name.str (Name.str (Name.str Name.anonymous "MathlibNt") "SieveTheory") "LiuWeight") "liuPanAggregateInverseLogPrincipalNoncoprimePsiTerm"), (Name.str (Name.str (Name.str (Name.str Name.anonymous "MathlibNt") "SieveTheory") "LiuWeight") "liuPanAggregateInverseLogPrincipalPsiTerm"), (Name.str (Name.str (Name.str (Name.str Name.anonymous "MathlibNt") "SieveTheory") "LiuWeight") "liuPanAggregateInverseLogPsiCharacterTerm"), (Name.str (Name.str (Name.str (Name.str Name.anonymous "MathlibNt") "SieveTheory") "LiuWeight") "liuPanAggregateInverseLogPsiMaxL"), (Name.str (Name.str (Name.str (Name.str Name.anonymous "MathlibNt") "SieveTheory") "LiuWeight") "liuPanAggregateInverseLogPsiMaxY"), (Name.str (Name.str (Name.str (Name.str Name.anonymous "MathlibNt") "SieveTheory") "LiuWeight") "liuPanAggregateInverseLogPsiTerm"), (Name.str (Name.str (Name.str (Name.str Name.anonymous "MathlibNt") "SieveTheory") "LiuWeight") "liuPanAggregateLogLambdaConductorSum"), (Name.str (Name.str (Name.str (Name.str Name.anonymous "MathlibNt") "SieveTheory") "LiuWeight") "liuPanAggregateLogLambdaLowConductorPrimitiveDilationSum"), (Name.str (Name.str (Name.str (Name.str Name.anonymous "MathlibNt") "SieveTheory") "LiuWeight") "liuPanAggregateLogLambdaLowConductorSum"), (Name.str (Name.str (Name.str (Name.str Name.anonymous "MathlibNt") "SieveTheory") "LiuWeight") "liuPanAggregateLogLambdaMediumHighConductorSum"), (Name.str (Name.str (Name.str (Name.str Name.anonymous "MathlibNt") "SieveTheory") "LiuWeight") "liuPanAggregateLogLambdaPrimitiveLiftSum"), (Name.str (Name.str (Name.str (Name.str Name.anonymous "MathlibNt") "SieveTheory") "LiuWeight") "liuPanAggregateNoncoprimePsiCorrection"), (Name.str (Name.str (Name.str (Name.str Name.anonymous "MathlibNt") "SieveTheory") "LiuWeight") "liuPanAggregateNonprincipalLogLambdaHyperbola"), (Name.str (Name.str (Name.str (Name.str Name.anonymous "MathlibNt") "SieveTheory") "LiuWeight") "liuPanAggregateNonprincipalPsiTerm"), (Name.str (Name.str (Name.str (Name.str Name.anonymous "MathlibNt") "SieveTheory") "LiuWeight") "liuPanAggregatePrincipalNoncoprimePsiTerm"), (Name.str (Name.str (Name.str (Name.str Name.anonymous "MathlibNt") "SieveTheory") "LiuWeight") "liuPanAggregatePrincipalPsiTerm"), (Name.str (Name.str (Name.str (Name.str Name.anonymous "MathlibNt") "SieveTheory") "LiuWeight") "liuPanAggregatePsiCharacterExpansion"), (Name.str (Name.str (Name.str (Name.str Name.anonymous "MathlibNt") "SieveTheory") "LiuWeight") "liuPanAggregatePsiCharacterProduct"), (Name.str (Name.str (Name.str (Name.str Name.anonymous "MathlibNt") "SieveTheory") "LiuWeight") "liuPanAggregatePsiConductorSum"), (Name.str (Name.str (Name.str (Name.str Name.anonymous "MathlibNt") "SieveTheory") "LiuWeight") "liuPanAggregatePsiPrimitiveLiftSum"), (Name.str (Name.str (Name.str (Name.str Name.anonymous "MathlibNt") "SieveTheory") "LiuWeight") "liuPanCombinedInverseLogDiscrepancy"), (Name.str (Name.str (Name.str (Name.str Name.anonymous "MathlibNt") "SieveTheory") "LiuWeight") "liuPanCombinedInverseLogMaxL"), (Name.str (Name.str (Name.str (Name.str Name.anonymous "MathlibNt") "SieveTheory") "LiuWeight") "liuPanCombinedInverseLogMaxY"), (Name.str (Name.str (Name.str (Name.str Name.anonymous "MathlibNt") "SieveTheory") "LiuWeight") "liuPanDiscreteInverseLogMain"), (Name.str (Name.str (Name.str (Name.str Name.anonymous "MathlibNt") "SieveTheory") "LiuWeight") "liuPanInverseLogAbelWeight"), (Name.str (Name.str (Name.str (Name.str Name.anonymous "MathlibNt") "SieveTheory") "LiuWeight") "liuPanLambdaCharacterPrefix"), (Name.str (Name.str (Name.str (Name.str Name.anonymous "MathlibNt") "SieveTheory") "LiuWeight") "liuPanLogLambdaCharacterPrefix"), (Name.str (Name.str (Name.str (Name.str Name.anonymous "MathlibNt") "SieveTheory") "LiuWeight") "liuPanLogLambdaCoefficient"), (Name.str (Name.str (Name.str (Name.str Name.anonymous "MathlibNt") "SieveTheory") "LiuWeight") "liuPanLogNoncoprimeCorrection"), (Name.str (Name.str (Name.str (Name.str Name.anonymous "MathlibNt") "SieveTheory") "LiuWeight") "liuPanLogPNTError"), (Name.str (Name.str (Name.str (Name.str Name.anonymous "MathlibNt") "SieveTheory") "LiuWeight") "liuPanPNTError"), (Name.str (Name.str (Name.str (Name.str Name.anonymous "MathlibNt") "SieveTheory") "LiuWeight") "liuPanPerronDirichletPolynomial"), (Name.str (Name.str (Name.str (Name.str Name.anonymous "MathlibNt") "SieveTheory") "LiuWeight") "liuPanPerronHalfStep"), (Name.str (Name.str (Name.str (Name.str Name.anonymous "MathlibNt") "SieveTheory") "LiuWeight") "liuPanPerronHyperbolaSum"), (Name.str (Name.str (Name.str (Name.str Name.anonymous "MathlibNt") "SieveTheory") "LiuWeight") "liuPanPerronLine"), (Name.str (Name.str (Name.str (Name.str Name.anonymous "MathlibNt") "SieveTheory") "LiuWeight") "liuPanPerronNatPower"), (Name.str (Name.str (Name.str (Name.str Name.anonymous "MathlibNt") "SieveTheory") "LiuWeight") "liuPanPerronPoissonContourIntegrand"), (Name.str (Name.str (Name.str (Name.str Name.anonymous "MathlibNt") "SieveTheory") "LiuWeight") "liuPanPerronProductCoefficient"), (Name.str (Name.str (Name.str (Name.str Name.anonymous "MathlibNt") "SieveTheory") "LiuWeight") "liuPanPerronZeroExtension"), (Name.str (Name.str (Name.str (Name.str Name.anonymous "MathlibNt") "SieveTheory") "LiuWeight") "liuPanPrimePowerJ9Mass"), (Name.str (Name.str (Name.str (Name.str Name.anonymous "MathlibNt") "SieveTheory") "LiuWeight") "liuPanPrimePowerNonprincipalCharacters"), (Name.str (Name.str (Name.str (Name.str Name.anonymous "MathlibNt") "SieveTheory") "LiuWeight") "liuPanPrimePowerPrimitiveCharacters"), (Name.str (Name.str (Name.str (Name.str Name.anonymous "MathlibNt") "SieveTheory") "LiuWeight") "liuPanPrimitiveDilationLogLambdaHyperbola"), (Name.str (Name.str (Name.str (Name.str Name.anonymous "MathlibNt") "SieveTheory") "LiuWeight") "liuPanPsiAbelMajorant"), (Name.str (Name.str (Name.str (Name.str Name.anonymous "MathlibNt") "SieveTheory") "LiuWeight") "liuPanPsiNoncoprimeCorrection"), (Name.str (Name.str (Name.str (Name.str Name.anonymous "MathlibNt") "SieveTheory") "LiuWeight") "liuPanPsiPrefix"), (Name.str (Name.str (Name.str (Name.str Name.anonymous "MathlibNt") "SieveTheory") "LiuWeight") "liuPanSourceCharacterPrefix"), (Name.str (Name.str (Name.str (Name.str Name.anonymous "MathlibNt") "SieveTheory") "LiuWeight") "liuPanSourceLogLambdaCharacterHyperbola"), (Name.str (Name.str (Name.str (Name.str Name.anonymous "MathlibNt") "SieveTheory") "LiuWeight") "liuPanSourceWeightedPsiAbelMajorant"), (Name.str (Name.str (Name.str (Name.str Name.anonymous "MathlibNt") "SieveTheory") "LiuWeight") "liuPanSourceWeightedPsiAbelMaxL"), (Name.str (Name.str (Name.str (Name.str Name.anonymous "MathlibNt") "SieveTheory") "LiuWeight") "liuPanSourceWeightedPsiAbelMaxY"), (Name.str (Name.str (Name.str (Name.str Name.anonymous "MathlibNt") "SieveTheory") "LiuWeight") "liuPanSourceZeroExtension"), (Name.str (Name.str (Name.str (Name.str Name.anonymous "MathlibNt") "SieveTheory") "LiuWeight") "liuPanTruncatedPerronError"), (Name.str (Name.str (Name.str (Name.str Name.anonymous "MathlibNt") "SieveTheory") "LiuWeight") "liuPanTruncatedPerronIntegral"), (Name.str (Name.str (Name.str (Name.str Name.anonymous "MathlibNt") "SieveTheory") "LiuWeight") "liuPanTruncatedPerronKernel"), (Name.str (Name.str (Name.str (Name.str Name.anonymous "MathlibNt") "SieveTheory") "LiuWeight") "liuSelbergDenominator"), (Name.str (Name.str (Name.str (Name.str Name.anonymous "MathlibNt") "SieveTheory") "LiuWeight") "liuSelbergOptimalLambda"), (Name.str (Name.str (Name.str (Name.str Name.anonymous "MathlibNt") "SieveTheory") "LiuWeight") "liuSelbergOptimalX"), (Name.str (Name.str (Name.str (Name.str Name.anonymous "MathlibNt") "SieveTheory") "LiuWeight") "liuSelbergTerm"), (Name.str (Name.str (Name.str (Name.str Name.anonymous "MathlibNt") "SieveTheory") "LiuWeight") "truncatedSelbergCarrier"), (Name.str (Name.str (Name.str (Name.str Name.anonymous "MathlibNt") "SieveTheory") "LiuWeight") "truncatedSelbergDenominator"), (Name.str (Name.str (Name.str (Name.str Name.anonymous "MathlibNt") "SieveTheory") "LiuWeight") "truncatedSelbergOptimalLambda"), (Name.str (Name.str (Name.str (Name.str Name.anonymous "MathlibNt") "SieveTheory") "LiuWeight") "truncatedSelbergOptimalX"), (Name.str (Name.str (Name.str (Name.str (Name.str Name.anonymous "MathlibNt") "SieveTheory") "SwitchingPrinciple") "SuzukiLemma144KappaOne") "Section13HatExponentialDecay"), (Name.str (Name.str (Name.str Name.anonymous "MathlibNt") "SieveTheory") "characterPrefixSquare"), (Name.str (Name.str Name.anonymous "SigmaRationalOuterFTC") "homogeneousWeight"), (Name.str (Name.str Name.anonymous "SigmaRationalOuterFTC") "jointDen"), (Name.str (Name.str Name.anonymous "SigmaRationalOuterFTC") "jointNum"), (Name.str (Name.str Name.anonymous "SigmaRationalOuterFTC") "negD"), (Name.str (Name.str Name.anonymous "SigmaRationalOuterFTC") "negN"), (Name.str (Name.str Name.anonymous "SigmaRationalOuterFTC") "outerQ"), (Name.str (Name.str Name.anonymous "SigmaRationalOuterFTC") "radD"), (Name.str (Name.str Name.anonymous "SigmaRationalOuterFTC") "radN"), (Name.str (Name.str Name.anonymous "TerminalE") "primitive"), (Name.str (Name.str Name.anonymous "TerminalE") "quadraticPrimitive"), (Name.str (Name.str Name.anonymous "TerminalE") "radical"), (Name.str Name.anonymous "instMeasurableSpace")]
  let includeDefinitions := true
  let mut records : Array Json := #[]
  for n in requested do
    let some ci := env.find? n | throwError "Missing public declaration: {n}"
    match declaration ci includeDefinitions with
    | .error message => throwError "{message}"
    | .ok row => records := records.push row
  let payload := Json.mkObj [
    ("schema", toJson "wu-public-interface-v1"),
    ("normalization", toJson "erase-mdata-binder-names; levelParams-positional-alpha-v1"),
    ("requested_names", toJson (requested.map Name.toString)),
    ("include_definitions", toJson includeDefinitions),
    ("declarations", Json.arr records)]
  Lean.Elab.Command.liftIO <| IO.FS.writeFile "/tmp/wu-hf4-installed-v7-resume-v1/validation-1793186938467236335/before-values.json" payload.compress

end PublicInterfaceAudit

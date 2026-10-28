import MathlibNt.SieveTheory.Switching.PrimePenaltyAsymptotics
import MathlibNt.SieveTheory.LinearSieve.JurkatRichert.JurkatRichert1965Section13HatSource
import MathlibNt.SieveTheory.LinearSieve.Suzuki.SuzukiChenVaryingFamilyLowerDensity
import MathlibNt.SieveTheory.LinearSieve.Suzuki.SuzukiUpperRosserDensityEndpointDirect
import MathlibNt.SieveTheory.Distribution.Bombieri1965RichertWeightedConsumer

/-!
# The actual Chen--Richert consumer with its sieve inputs discharged

The Goldbach sources have density `1 / (p - 1)`, not the literal JR1965
density `1 / p`. The connection here is analytic, not an identification of
the two sieves: the constructed JR delay functions supply the concrete
Section 13 majorants, and the existing modern Suzuki comparisons give the
required lower and uniformly conditioned upper sieve estimates.

The lower route is already specialized to Chen's varying source family.
The upper route uses the proved modern all-depth comparison internally;
it is not attributed to the literal 1965 Theorem 5. The public endpoints
below concern the actual Chen sources and carry no imported sieve or
distribution premise.
-/

open Filter
open scoped Topology

namespace MathlibNt.SieveTheory.JurkatRichert1965ChenRichertConsumer

open SwitchingPrinciple
open SwitchingPrinciple.SuzukiLemma144KappaOne
open JurkatRichert1965ChenGammaOneQOne

private theorem modernUpperDensity :
    DimensionOneUpperRosserDensityFundamentalLemma :=
  dimensionOneUpperRosserDensityFundamentalLemma_of_suzuki_allDepth
    jr1965Section13HatLayers jr1965Section13HatSourceContract
    (show SuzukiClaim145SourceParameters (16 : ℝ) (1 / 2 : ℝ) (7 : ℝ) by
      constructor <;> norm_num)

/-- The actual base Goldbach sieve, including its genuine finite remainder. -/
theorem chenBaseLowerSieve :
    ChenJurkatRichertBaseLowerSieveFundamentalLemma :=
  chenJurkatRichertBaseLowerSieveFundamentalLemma_of_section13HatSource
    jr1965Section13HatLayers jr1965Section13HatSourceContract

/-- The base lower asymptotic after the unconditional modern distribution
producer pays the actual Goldbach remainder. -/
theorem chenBaseLowerAsymptotic :
    ChenJurkatRichertBaseLowerSieveAsymptotic :=
  chenJurkatRichertBaseLowerSieveAsymptotic_of_inputs chenBaseLowerSieve
    (chenJurkatRichertBaseGoldbachDistribution_of_standardBV
      AnalyticNumberTheory.LargeSieve.Bombieri1965Richert418.standardBombieriVinogradov)


/-- Both actual upper-sieve inputs are now theorems, not external premises. -/
private theorem chenUpperInput : ChenJurkatRichertVaryingQUpperSieveStandardInput :=
  ⟨modernUpperDensity, Bombieri1965RichertWeightedConsumer.chenWeightedBombieriVinogradov⟩


/-- The literal distinct-medium-prime weighted lower bound of Chen Lemma 9. -/
theorem chenDistinctWeightedLowerBound :
    ChenJurkatRichertDistinctWeightedLowerBound :=
  chenJurkatRichertDistinctWeightedLowerBound_of_asymptotics
    chenBaseLowerAsymptotic chenUpperInput

/-- The production weighted lower bound, including the existing correction
from the distinct source weight to its valuation-based consumer. -/
theorem chenWeightedLowerBound :
    ChenJurkatRichertWeightedLowerBound :=
  chenJurkatRichertWeightedLowerBound_of_distinct chenDistinctWeightedLowerBound

end MathlibNt.SieveTheory.JurkatRichert1965ChenRichertConsumer

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

/-- The exact varying-medium-prime density aggregate, with all medium primes
paid under one eventual threshold. -/
theorem chenVaryingQUpperDensity
    (ε : ℝ) (hε : 0 < ε) (hεSmall : ε < 1 / 60)
    (δ : ℝ) (hδ : 0 < δ) :
    ∀ᶠ N : ℕ in atTop, Even N →
      jurkatRichertSourceVaryingQMainSum N ε ≤
        jurkatRichertSourceVaryingQDensityModel N ε +
          δ * SingularSeries.liuSingularSeries N * (N : ℝ) /
            Real.log N ^ (2 : ℕ) :=
  chenJurkatRichertVaryingQUpperDensity_of_fundamentalLemma
    modernUpperDensity ε hε hεSmall δ hδ

/-- Both actual upper-sieve inputs are now theorems, not external premises. -/
private theorem chenUpperInput : ChenJurkatRichertVaryingQUpperSieveStandardInput :=
  ⟨modernUpperDensity, Bombieri1965RichertWeightedConsumer.chenWeightedBombieriVinogradov⟩

theorem chenVaryingQUpperAsymptotic :
    ChenJurkatRichertVaryingQUpperSieveAsymptotic :=
  chenJurkatRichertVaryingQUpperSieveAsymptotic_of_standardInput chenUpperInput

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

/-- The actual Richert source chain with all sieve and distribution inputs
discharged. The finite stages retain exactly their original quantifiers. -/
theorem chenFacingSourceChainCertificate :
    Richert1969.ChenFacingSourceChainCertificate where
  theoremOneFinite := Richert1969.theoremOneFiniteLowerBound
  lowerS := Richert1969.Chen.lowerS_eq_candidateCard
  conditionedUpperS := Richert1969.Chen.primeConditionedUpperS_eq_candidateCard
  weightedObject := Richert1969.Chen.weightedLowerObject_eq_lower_sub_half_conditioned
  squarefulA4 := Richert1969.theoremOneSquarefulCorrection_le_sum_A4
  stieltjesPrimeIntegral := Richert1969.Chen.stieltjesPrimeIntegral
  weightedBombieri := Bombieri1965RichertWeightedConsumer.chenWeightedBombieriVinogradov
  weightedLowerBound := chenWeightedLowerBound

end MathlibNt.SieveTheory.JurkatRichert1965ChenRichertConsumer

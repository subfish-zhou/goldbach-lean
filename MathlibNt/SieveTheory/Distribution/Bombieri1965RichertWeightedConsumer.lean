import MathlibNt.AnalyticNumberTheory.BombieriVinogradov.Bombieri1965Richert418Unconditional
import MathlibNt.SieveTheory.LinearSieve.Richert.Richert1969Ordinary418Specialization

/-!
# The modern Bombieri producer in Richert's weighted source chain

The unconditional modern Standard BV theorem discharges the distribution
premise in the existing ordinary-to-weighted Richert argument. The two
Jurkat--Richert Theorem A density lemmas remain explicit assumptions; neither
the historical Bombieri density proof nor a generic sieve theorem is claimed.
-/

namespace MathlibNt.SieveTheory.Bombieri1965RichertWeightedConsumer

open SwitchingPrinciple

/-- Richert's actual varying-level weighted error bound, now with no
distribution hypothesis. The existing payment uses ordinary exponent
`2 * A + 10` and retains the combined-modulus and coprimality restrictions. -/
theorem chenWeightedBombieriVinogradov :
    ChenJurkatRichertVaryingQWeightedBombieriVinogradov :=
  Richert1969.chenWeightedBombieriVinogradov_of_standard
    AnalyticNumberTheory.LargeSieve.Bombieri1965Richert418.standardBombieriVinogradov

/-- Only the lower and upper Jurkat--Richert Theorem A inputs remain in the
Chen-facing weighted lower bound. -/
theorem chenWeightedLowerBound_of_importedTheoremA
    (hLowerTheoremA : DimensionOneLowerRosserDensityFundamentalLemma)
    (hUpperTheoremA : DimensionOneUpperRosserDensityFundamentalLemma) :
    ChenJurkatRichertWeightedLowerBound :=
  Richert1969.chenWeightedLowerBound_of_importedTheoremA_and_standardBombieri
    hLowerTheoremA
    AnalyticNumberTheory.LargeSieve.Bombieri1965Richert418.standardBombieriVinogradov
    hUpperTheoremA

/-- The existing literal Richert source certificate with its ordinary BV
premise discharged by the proved modern producer, not by an added axiom. -/
theorem chenFacingSourceChainCertificate_of_importedTheoremA
    (hLowerTheoremA : DimensionOneLowerRosserDensityFundamentalLemma)
    (hUpperTheoremA : DimensionOneUpperRosserDensityFundamentalLemma) :
    Richert1969.ChenFacingSourceChainCertificate :=
  Richert1969.chenFacingSourceChainCertificate_of_importedTheoremA_and_standardBombieri
    hLowerTheoremA
    AnalyticNumberTheory.LargeSieve.Bombieri1965Richert418.standardBombieriVinogradov
    hUpperTheoremA

end MathlibNt.SieveTheory.Bombieri1965RichertWeightedConsumer

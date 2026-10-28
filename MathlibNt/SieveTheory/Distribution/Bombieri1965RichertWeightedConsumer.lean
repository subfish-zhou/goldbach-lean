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


end MathlibNt.SieveTheory.Bombieri1965RichertWeightedConsumer

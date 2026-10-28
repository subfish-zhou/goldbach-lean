import MathlibNt.AnalyticNumberTheory.BombieriVinogradov.Bombieri1965Richert418Unconditional

/-! # Shared unconditional distribution endpoints for switched-source consumers

These consumer names use the canonical proved Siegel--Walfisz and Standard BV
producer also used by the base Chen sieve.
-/

namespace AnalyticNumberTheory.LargeSieve

theorem fourFactor_nonprincipalPrimitivePsiSiegelWalfiszSource :
    NonprincipalPrimitivePsiSiegelWalfiszSource :=
  Bombieri1965Richert418.nonprincipalPrimitivePsiSiegelWalfiszSource

theorem fourFactor_standardBombieriVinogradov :
    MathlibNt.SieveTheory.BombieriVinogradov.StandardBombieriVinogradov :=
  Bombieri1965Richert418.standardBombieriVinogradov

end AnalyticNumberTheory.LargeSieve

module

public import MathlibNt.AnalyticNumberTheory.LargeSieve.StandardBVFinalLowOnlyProducer
public import MathlibNt.AnalyticNumberTheory.LargeSieve.PrincipalPNTSourceFromMediumPNT

@[expose] public section

namespace AnalyticNumberTheory.LargeSieve

/-- With the principal source discharged by `MediumPNT` and the chosen high
source unconditional, Standard Bombieri--Vinogradov retains only the genuine
nonprincipal primitive Siegel--Walfisz input. -/
theorem standardBombieriVinogradov_of_nonprincipalPrimitivePsi
    (hSW : NonprincipalPrimitivePsiSiegelWalfiszSource) :
    MathlibNt.SieveTheory.BombieriVinogradov.StandardBombieriVinogradov :=
  standardBombieriVinogradov_of_nonprincipalPrimitivePsi_lowOnly
    hSW globalChebyshevToLiPrincipalPNTSource

end AnalyticNumberTheory.LargeSieve
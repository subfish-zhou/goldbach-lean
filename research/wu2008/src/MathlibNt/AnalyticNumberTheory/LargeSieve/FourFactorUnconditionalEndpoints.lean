import MathlibNt.AnalyticNumberTheory.Siegel.Bombieri1965Theorem4RawSiegel
import MathlibNt.AnalyticNumberTheory.LargeSieve.LandauSiegelToStandardBVCanonicalSmoothing
import MathlibNt.AnalyticNumberTheory.Chen1973.Chen1973Lemma6AllLevelSmall

noncomputable section
namespace AnalyticNumberTheory.LargeSieve

/-- The existing low source with its raw Siegel input now proved internally. -/
theorem fourFactor_nonprincipalPrimitivePsiSiegelWalfiszSource :
    NonprincipalPrimitivePsiSiegelWalfiszSource :=
  nonprincipalPrimitivePsiSiegelWalfiszSource_of_rawLandauSiegelLowerBound
    fourFactor_rawLandauSiegelLowerBound
    standardBVCanonicalSmoothing_contDiff standardBVCanonicalSmoothing_nonneg
    standardBVCanonicalSmoothing_support standardBVCanonicalSmoothing_mass_one

/-- Unconditional Standard BV through the preserved nonprincipal-primitive endpoint. -/
theorem fourFactor_standardBombieriVinogradov :
    MathlibNt.SieveTheory.BombieriVinogradov.StandardBombieriVinogradov :=
  standardBombieriVinogradov_of_nonprincipalPrimitivePsi
    fourFactor_nonprincipalPrimitivePsiSiegelWalfiszSource


end AnalyticNumberTheory.LargeSieve

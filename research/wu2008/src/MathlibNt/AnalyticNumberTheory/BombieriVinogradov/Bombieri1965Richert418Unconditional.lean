import MathlibNt.AnalyticNumberTheory.Siegel.Bombieri1965Theorem4SiegelLowerBound
import MathlibNt.AnalyticNumberTheory.LargeSieve.LandauSiegelToStandardBVCanonicalSmoothing
import MathlibNt.AnalyticNumberTheory.BombieriVinogradov.Bombieri1965Richert418

/-!
# Unconditional modern producer for Richert (4.18)

The proved fixed-witness Siegel theorem supplies the actual low-conductor
primitive character estimate. The existing large-sieve/Vaughan argument and
literal logarithmic-integral comparison then give the maximal prime-AP
estimate. No analytic source proposition is assumed.

This is a modern replacement proof, not a transcription of Bombieri's
Theorem 5 density argument or of an uninspected Prachar proof.
-/

namespace AnalyticNumberTheory.LargeSieve.Bombieri1965Richert418

/-- The exact raw interface is supplied by the proved, conductor-uniform
quadratic L-value theorem. -/
theorem rawLandauSiegelLowerBound : RawLandauSiegelLowerBound := by
  intro η hη
  obtain ⟨c, hc, hbound⟩ :=
    Bombieri1965Theorem4.exists_uniform_quadratic_LFunction_one_lower_bound η hη
  exact ⟨c, hc, fun q _ χ hprim hquad hχ => hbound q χ hprim hχ hquad⟩

/-- The genuine nonprincipal primitive low-conductor Siegel--Walfisz input,
with the smoothing function constructed rather than postulated. -/
theorem nonprincipalPrimitivePsiSiegelWalfiszSource :
    NonprincipalPrimitivePsiSiegelWalfiszSource :=
  nonprincipalPrimitivePsiSiegelWalfiszSource_of_rawLandauSiegelLowerBound
    rawLandauSiegelLowerBound standardBVCanonicalSmoothing_contDiff
    standardBVCanonicalSmoothing_nonneg standardBVCanonicalSmoothing_support
    standardBVCanonicalSmoothing_mass_one

/-- Unconditional maximal Standard BV, before the literal `li` normalization
comparison. -/
theorem standardBombieriVinogradov :
    MathlibNt.SieveTheory.BombieriVinogradov.StandardBombieriVinogradov :=
  standardBombieriVinogradov_of_nonprincipalPrimitivePsi
    nonprincipalPrimitivePsiSiegelWalfiszSource

/-- Richert's exact nested integer-prefix and reduced-residue maximum,
with `li(x) = integral_2^x dt/log(t)` and the full stated modulus range. -/
theorem richert418 : Richert418BombieriVinogradov :=
  richert418_of_nonprincipalPrimitivePsi nonprincipalPrimitivePsiSiegelWalfiszSource

end AnalyticNumberTheory.LargeSieve.Bombieri1965Richert418

import MathlibNt.SieveTheory.LinearSieve.Suzuki.SuzukiProposition118SourcePairingFinal
import MathlibNt.SieveTheory.LinearSieve.Suzuki.SuzukiLemma147LowerFiniteFactor

/-!
# Suzuki's lower sieve factor on the first interval

This module passes the exact finite conservation identity to the genuine source
series limit.  For `2 ≤ s ≤ 4`, the finite even partial sums converge to
Suzuki's `T⁻(s)`, while the finite amplitude and boundary residuals vanish.
Consequently the explicit first-interval factor is exactly `1 - T⁻(s)`.
-/

open scoped Classical BigOperators Interval
open Filter Topology MeasureTheory intervalIntegral

namespace MathlibNt.SieveTheory

open SuzukiFiniteContinuousLayers
open SwitchingPrinciple
open SwitchingPrinciple.SuzukiLemma144KappaOne

set_option autoImplicit false

/-- On Suzuki's first lower interval, the genuine lower factor is exactly one
minus the limiting even source series.  The only premise is the production
all-depth source contract; no factor identity or limiting conclusion is assumed. -/
theorem one_sub_suzukiProposition118SourceTMinus_eq_lowerSieveFactorFirstInterval
    {H : Section13HatLayers} (hH : Section13HatSourceContract H)
    {s : ℝ} (hs2 : 2 ≤ s) (hs4 : s ≤ 4) :
    1 - suzukiProposition118SourceTMinus s =
      suzukiLowerSieveFactorFirstInterval s := by
  have hpartial : Tendsto (fun m => suzukiEvenSourceLowerPartialSum m s) atTop
      (𝓝 (suzukiProposition118SourceTMinus s)) := by
    simpa only [suzukiProposition118SourceTMinus_eq] using
      tendsto_suzukiEvenSourceLowerPartialSum_real hH hs2
  have hleft : Tendsto
      (fun m => 1 - suzukiEvenSourceLowerPartialSum m s) atTop
      (𝓝 (1 - suzukiProposition118SourceTMinus s)) :=
    tendsto_const_nhds.sub hpartial
  have hboundary : Tendsto suzukiFiniteLowerBoundary atTop (𝓝 0) := by
    simpa only [suzukiLowerBoundaryLimit_eq_zero_of_sourceContract hH] using
      tendsto_suzukiFiniteLowerBoundary hH
  have hamplitude := tendsto_suzukiFiniteLowerAmplitude_residual_zero hH s
  have hboundaryDiv : Tendsto (fun m => suzukiFiniteLowerBoundary m / s) atTop
      (𝓝 0) := by
    simpa using hboundary.div_const s
  have hfactor : Tendsto
      (fun _ : ℕ => suzukiLowerSieveFactorFirstInterval s) atTop
      (𝓝 (suzukiLowerSieveFactorFirstInterval s)) := tendsto_const_nhds
  have hright : Tendsto
      (fun m =>
        suzukiLowerSieveFactorFirstInterval s +
          suzukiFiniteLowerBoundary m / s +
          (suzukiFiniteLowerAmplitude m - suzukiLowerSieveAmplitude) / s *
            (∫ t in (2 : ℝ)..s, (t - 1)⁻¹))
      atTop (𝓝 (suzukiLowerSieveFactorFirstInterval s)) := by
    simpa using ((hfactor.add hboundaryDiv).add hamplitude)
  have heq :
      (fun m => 1 - suzukiEvenSourceLowerPartialSum m s) =ᶠ[atTop]
        (fun m =>
          suzukiLowerSieveFactorFirstInterval s +
            suzukiFiniteLowerBoundary m / s +
            (suzukiFiniteLowerAmplitude m - suzukiLowerSieveAmplitude) / s *
              (∫ t in (2 : ℝ)..s, (t - 1)⁻¹)) := by
    filter_upwards [eventually_ge_atTop 1] with m hm
    exact one_sub_evenPartialSum_eq_firstInterval_add_residuals hm hs2 hs4
  exact tendsto_nhds_unique hleft (hright.congr' heq.symm)

/-- The honest finite lower factors at even depths converge to the now-identified
first-interval factor. -/
theorem tendsto_suzukiFiniteLowerFactor_even_firstInterval
    {H : Section13HatLayers} (hH : Section13HatSourceContract H)
    {s : ℝ} (hs2 : 2 ≤ s) (hs4 : s ≤ 4) :
    Tendsto (fun m => suzukiFiniteLowerFactor (2 * m) s) atTop
      (𝓝 (suzukiLowerSieveFactorFirstInterval s)) := by
  have hpartial := tendsto_suzukiEvenSourceLowerPartialSum_real hH hs2
  have hsub : Tendsto
      (fun m => 1 - suzukiEvenSourceLowerPartialSum m s) atTop
      (𝓝 (1 - suzukiEvenSourceLowerLayerLimit s)) :=
    tendsto_const_nhds.sub hpartial
  rw [← suzukiProposition118SourceTMinus_eq] at hsub
  rw [one_sub_suzukiProposition118SourceTMinus_eq_lowerSieveFactorFirstInterval
    hH hs2 hs4] at hsub
  simpa [suzukiFiniteLowerFactor, finiteSourceLayer_two_mul_eq_sum_evenLayers,
    suzukiEvenSourceLowerPartialSum] using hsub

/-- The unconditional `ℝ≥0∞` supremum is the image of the genuine source
`T⁻` series once the production source contract supplies real summability. -/
theorem suzukiEvenSourceLowerLayerSup_eq_ofReal_sourceTMinus
    {H : Section13HatLayers} (hH : Section13HatSourceContract H)
    {s : ℝ} (hs2 : 2 ≤ s) :
    suzukiEvenSourceLowerLayerSup s =
      ENNReal.ofReal (suzukiProposition118SourceTMinus s) := by
  simpa only [suzukiProposition118SourceTMinus_eq] using
    suzukiEvenSourceLowerLayerSup_eq_ofReal_limit hH hs2

/-- On the first interval, the same supremum is `ofReal (1-F⁻(s))`, linking the
extended monotone limit directly to the explicit lower factor. -/
theorem suzukiEvenSourceLowerLayerSup_eq_ofReal_one_sub_lowerSieveFactorFirstInterval
    {H : Section13HatLayers} (hH : Section13HatSourceContract H)
    {s : ℝ} (hs2 : 2 ≤ s) (hs4 : s ≤ 4) :
    suzukiEvenSourceLowerLayerSup s =
      ENNReal.ofReal (1 - suzukiLowerSieveFactorFirstInterval s) := by
  rw [suzukiEvenSourceLowerLayerSup_eq_ofReal_sourceTMinus hH hs2]
  congr 1
  have hfactor :=
    one_sub_suzukiProposition118SourceTMinus_eq_lowerSieveFactorFirstInterval
      hH hs2 hs4
  linarith


end MathlibNt.SieveTheory

module

public import MathlibNt.SieveTheory.SuzukiUpperRosserDensityEndpointDirect
public import MathlibNt.SieveTheory.JurkatRichert1965Section13HatSource

@[expose] public section

open MathlibNt.SieveTheory.SuzukiFiniteContinuousLayers
open MathlibNt.SieveTheory.SwitchingPrinciple
open MathlibNt.SieveTheory.JurkatRichert1965ChenGammaOneQOne

namespace MathlibNt.SieveTheory.LiLiuOnePlusOneNine.GoldbachBig

set_option autoImplicit false

noncomputable section

/-- The genuine source upper factor bounds the actual upper Rosser main sum
uniformly on `[3/2,6]`, with no residual analytic source hypothesis. -/
theorem goldbach_upperRosserDensity_six :
    ∀ K ρ : ℝ, 1 < K → 0 < ρ →
      ∃ z₀ : ℝ, ∀ S : BoundingSieve, ∀ z Δ s : ℝ,
        z₀ ≤ z → 2 ≤ z → 0 < Δ →
        HasDimensionOneLocalProductBound S K →
        (∀ p ∈ S.prodPrimes.primeFactors, (p : ℝ) ≤ z) →
        s = Real.log Δ / Real.log z → 3 / 2 ≤ s → s ≤ 6 →
        S.mainSum (LinearSieve.upperRosserWeight S.prodPrimes (Nat.floor Δ + 1)) ≤
          (suzukiContinuousUpperFactor s + ρ) *
            AnalyticNumberTheory.Sieve.sieveProductPrimeFactors S := by
  have hsrc : SuzukiClaim145SourceParameters (16 : ℝ) (1 / 2 : ℝ) (7 : ℝ) := by
    constructor <;> norm_num
  exact suzukiUpperRosserDensity_uniform_of_le
    jr1965Section13HatLayers jr1965Section13HatSourceContract hsrc 6

end
end MathlibNt.SieveTheory.LiLiuOnePlusOneNine.GoldbachBig

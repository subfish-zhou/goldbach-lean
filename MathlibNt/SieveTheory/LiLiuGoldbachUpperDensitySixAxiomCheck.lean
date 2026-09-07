import MathlibNt.SieveTheory.LiLiuGoldbachUpperDensitySix

open MathlibNt.SieveTheory
open MathlibNt.SieveTheory.SwitchingPrinciple
open MathlibNt.SieveTheory.SwitchingPrinciple.SuzukiLemma144KappaOne

namespace MathlibNt.SieveTheory.LiLiuOnePlusOneNine.GoldbachBig

set_option autoImplicit false

#check goldbach_upperRosserDensity_six
#print axioms goldbach_upperRosserDensity_six

/-- The actual `45/8 > 5` endpoint is an instance of the full six-window result. -/
theorem goldbach_upperRosserDensity_fortyFiveEighths_audit :
    ∀ K ρ : ℝ, 1 < K → 0 < ρ →
      ∃ z₀ : ℝ, ∀ S : BoundingSieve, ∀ z Δ : ℝ,
        z₀ ≤ z → 2 ≤ z → 0 < Δ →
        HasDimensionOneLocalProductBound S K →
        (∀ p ∈ S.prodPrimes.primeFactors, (p : ℝ) ≤ z) →
        (45 / 8 : ℝ) = Real.log Δ / Real.log z →
        S.mainSum (LinearSieve.upperRosserWeight S.prodPrimes (Nat.floor Δ + 1)) ≤
          (suzukiContinuousUpperFactor (45 / 8) + ρ) *
            AnalyticNumberTheory.Sieve.sieveProductPrimeFactors S := by
  intro K ρ hK hρ
  obtain ⟨z₀, h⟩ := goldbach_upperRosserDensity_six K ρ hK hρ
  refine ⟨z₀, ?_⟩
  intro S z Δ hz₀ hz2 hΔ hlocal hcut hs
  exact h S z Δ (45 / 8) hz₀ hz2 hΔ hlocal hcut hs (by norm_num) (by norm_num)

#check goldbach_upperRosserDensity_fortyFiveEighths_audit
#print axioms goldbach_upperRosserDensity_fortyFiveEighths_audit

end MathlibNt.SieveTheory.LiLiuOnePlusOneNine.GoldbachBig
import MathlibNt.SieveTheory.LinearSieve.DimensionOneLowerFactor
import MathlibNt.SieveTheory.Switching.SuzukiPrimeSums
import MathlibNt.SieveTheory.LinearSieve.UpperRosserDensity
import AnalyticNumberTheory.Sieve.LinearSieve

/-! Generic upper factor and its fundamental-lemma interface.
Chen applications consume this interface; the generic producer has no Chen source. -/

noncomputable section
namespace MathlibNt.SieveTheory.SwitchingPrinciple

/-- The dimension-one upper linear-sieve factor on the range used in Chen's
q-sum.  The integral branch is the one whose partial summation contributes
`K / 2`. -/
noncomputable def jurkatRichertUpperLinearSieveFactor (s : ℝ) : ℝ :=
  if s ≤ 3 then
    2 * Real.exp Real.eulerMascheroniConstant / s
  else
    2 * Real.exp Real.eulerMascheroniConstant / s *
      (1 + jurkatRichertInnerIntegral s)

/-- The generic dimension-one upper fundamental lemma for the explicit Rosser
coefficient.  The only analytic input is local: for a sieve whose primes lie
below `z`, at real level `Δ` and ratio `s = log Δ / log z`, the Rosser density
sum is at most `(F(s) + ρ) V(S)`. -/
def DimensionOneUpperRosserDensityFundamentalLemma : Prop :=
  ∀ K ρ : ℝ, 1 < K → 0 < ρ →
    ∃ z₀ : ℝ, ∀ (S : BoundingSieve) (z Δ s : ℝ),
      z₀ ≤ z → 2 ≤ z → 0 < Δ →
      HasDimensionOneLocalProductBound S K →
      (∀ p ∈ S.prodPrimes.primeFactors, (p : ℝ) ≤ z) →
      s = Real.log Δ / Real.log z →
      3 / 2 ≤ s → s ≤ 4 →
      S.mainSum
          (LinearSieve.upperRosserWeight S.prodPrimes (Nat.floor Δ + 1)) ≤
        (jurkatRichertUpperLinearSieveFactor s + ρ) *
          AnalyticNumberTheory.Sieve.sieveProductPrimeFactors S

end MathlibNt.SieveTheory.SwitchingPrinciple

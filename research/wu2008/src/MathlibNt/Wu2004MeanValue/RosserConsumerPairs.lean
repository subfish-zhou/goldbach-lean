import MathlibNt.Wu2004MeanValue.RosserConsumer
import MathlibNt.Wu2004MeanValue.LiMass
import MathlibNt.Wu2004MeanValue.BlockMassEndpoints

/-! Actual tail and block sieve consumers, with their actual nonnegative
logarithmic-integral masses and actual common-X remainders. -/

namespace Wu2004MeanValue

open scoped BigOperators
open MathlibNt.SieveTheory.SwitchingPrinciple

theorem tailSiftedCount_upper_rosser (ρ : ℝ) (hρ : 0 < ρ) :
    ∃ z₀ : ℝ, 2 ≤ z₀ ∧ ∀ (N : ℕ) (c τ η Q : ℝ),
      Even N → 0 < η → η ≤ 1 → (2 / η) ^ 2 ≤ (N : ℝ) →
      4 ≤ Q → z₀ ≤ Real.sqrt Q →
      3 / 2 ≤ Real.log (Q / 2) / Real.log (Real.sqrt Q) →
      Real.log (Q / 2) / Real.log (Real.sqrt Q) ≤ 4 →
      (tailSiftedCount N c τ η (Real.sqrt Q) : ℝ) ≤
        tailMass N c τ η *
          (∏ p ∈ siftingPrimes N (Real.sqrt Q), (1 - 1 / ((p : ℝ) - 1))) *
          (jurkatRichertUpperLinearSieveFactor
            (Real.log (Q / 2) / Real.log (Real.sqrt Q)) + ρ) +
        ∑ d ∈ sieveDivisors N Q, (((ArithmeticFunction.moebius d : ℤ) : ℝ) ^ 2) *
          |tailRemainder N c τ η d| := by
  obtain ⟨z₀, hz₀, hbound⟩ := indexedSiftedCount_upper_rosser ρ hρ
  refine ⟨z₀, hz₀, ?_⟩
  intro N c τ η Q hN hη hη1 hNη hQ hz hslo hshi
  exact hbound N (tailPairs N c τ η) (tailMass N c τ η) Q hN
    (tailMass_nonneg hη hη1 hNη) hQ hz hslo hshi

theorem blockSiftedCount_upper_rosser (ρ : ℝ) (hρ : 0 < ρ) :
    ∃ z₀ : ℝ, 2 ≤ z₀ ∧ ∀ (H : ℝ) (N : ℕ) (a η Q : ℝ),
      Even N → 4 ≤ Q → z₀ ≤ Real.sqrt Q →
      3 / 2 ≤ Real.log (Q / 2) / Real.log (Real.sqrt Q) →
      Real.log (Q / 2) / Real.log (Real.sqrt Q) ≤ 4 →
      (blockSiftedCount H N a η (Real.sqrt Q) : ℝ) ≤
        blockMass H N a η *
          (∏ p ∈ siftingPrimes N (Real.sqrt Q), (1 - 1 / ((p : ℝ) - 1))) *
          (jurkatRichertUpperLinearSieveFactor
            (Real.log (Q / 2) / Real.log (Real.sqrt Q)) + ρ) +
        ∑ d ∈ sieveDivisors N Q, (((ArithmeticFunction.moebius d : ℤ) : ℝ) ^ 2) *
          |blockRemainder H N a η d| := by
  obtain ⟨z₀, hz₀, hbound⟩ := indexedSiftedCount_upper_rosser ρ hρ
  refine ⟨z₀, hz₀, ?_⟩
  intro H N a η Q hN hQ hz hslo hshi
  exact hbound N (blockPairs H N a η) (blockMass H N a η) Q hN
    (blockMass_nonneg H N a η) hQ hz hslo hshi

end Wu2004MeanValue

import MathlibNt.AnalyticNumberTheory.LargeSieve.StandardBVBlockL1WeightedPrimitive

namespace AnalyticNumberTheory.LargeSieve

open Classical Finset Filter
open scoped BigOperators ArithmeticFunction Topology

noncomputable section


set_option maxHeartbeats 3000000 in
/-- The complete weighted small square ledger is paid for any eventually
balanced-bounded cutoff, with no coefficient zeroing. -/
theorem standardBVSmall_squareLedger_payable_of_le_balanced
    (cutoff : ℕ → ℕ)
    (hcutoff : ∀ᶠ N : ℕ in Filter.atTop,
      cutoff N ≤ standardBVBalancedSmallCutoff N)
    (A κ B C : ℕ) :
    ∃ K₀ : ℝ, 0 < K₀ ∧
      ∀ᶠ N : ℕ in Filter.atTop,
        let Q := MathlibNt.SieveTheory.LiuWeight.panModulusCutoff N (B : ℝ)
        let R := logConductorThreshold N C
        let P := 4 * discreteAbelAmplifierPrefixMax N * conductorHarmonicFactor Q ^ 2
        let X := (N : ℝ) / Real.log N ^ (A + κ)
        P ^ 2 * (3 * highConductorHarmonicFactor Q R *
            primitivePrefixSquareLedgerOn
              (vaughanSmallCoeff vaughanUnitIntegerCoeff
                (cutoff N)) N
              (highConductorSet N Q C)) ≤ (K₀ * X) ^ 2 := by
  exact standardBVSmall_weightedSquareLedger_payable cutoff hcutoff A κ B C


end
end AnalyticNumberTheory.LargeSieve

import MathlibNt.Analysis.RealLogPowerThreshold
import MathlibNt.SieveTheory.LiLiuPrereqWFUnmaskedRemainder
import MathlibNt.SieveTheory.LiLiuPrereqWFTagCardinalityExp



/-!
# Uniform envelopes for the actual transport costs

The family-size factor is the cardinality of the actual signed tags, bounded
by the proved source estimate, not by a cardinality assumption. The remaining
envelopes involve only the consumer scale and the positive power saving.
-/

namespace MathlibNt.SieveTheory.LiLiuPrereqWF

open scoped Classical

namespace TransportAbsorption

theorem log_nat_le {T N : ℕ} (hTN : T ≤ N) :
    Real.log (T : ℝ) ≤ Real.log (N : ℝ) := by
  by_cases hT : T = 0
  · simpa [hT] using Real.log_natCast_nonneg N
  · exact Real.log_le_log (by exact_mod_cast Nat.pos_of_ne_zero hT)
      (by exact_mod_cast hTN)

theorem floor_log_bound {Q : ℝ} {N : ℕ} (hQ : Q ≤ N)
    (hN : 1 ≤ Real.log (N : ℝ)) :
    0 ≤ 1 + Real.log (⌊Q⌋₊ : ℝ) ∧
      1 + Real.log (⌊Q⌋₊ : ℝ) ≤ 2 * Real.log (N : ℝ) := by
  have hf : ⌊Q⌋₊ ≤ N := Nat.floor_le_of_le hQ
  have hl := log_nat_le hf
  constructor
  · linarith [Real.log_natCast_nonneg ⌊Q⌋₊]
  · linarith

/-- A fixed multiple of any real logarithmic power is eventually smaller
than any positive power. The constant may in particular be exponential in ε⁻³. -/
theorem eventually_log_power_budget (C A : ℝ) {s : ℝ} (hs : 0 < s) :
    ∀ᶠ x : ℝ in Filter.atTop, C * Real.log x ^ A ≤ x ^ s := by
  exact MathlibNt.Analysis.eventually_const_mul_log_rpow_le_rpow C A hs

end TransportAbsorption


end MathlibNt.SieveTheory.LiLiuPrereqWF

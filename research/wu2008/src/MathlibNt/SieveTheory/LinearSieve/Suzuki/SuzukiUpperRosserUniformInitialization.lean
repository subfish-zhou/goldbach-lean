import MathlibNt.SieveTheory.LinearSieve.Suzuki.SuzukiUpperRosserRelativeFiniteDepth

/-!
# Power-controlled initialization for the relative upper Rosser iterate

The relative finite-depth estimate carries the one-time factor
`log (z + 1) / log (q + 1)`.  This module removes that factor only under the
explicit, quantitatively sufficient hypothesis
`z + 1 ≤ ((q : ℝ) + 1) ^ C`.

The Chen upper-source window assumption `s ≤ 4` does not by itself have this
shape: the currently callable upper Rosser producers assume only that every
carrier prime is at most `z`.  Thus the final definition records the exact
additional bridge needed to make the estimate uniform over all large terminal
primes in a carrier; no such bridge is asserted here.
-/

namespace MathlibNt.SieveTheory.SwitchingPrinciple

noncomputable section

/-- A power comparison gives the strongest corresponding logarithmic
initialization-ratio comparison.  Positivity of the denominator is supplied by
primality, while `q ≤ z` supplies positivity of `z + 1`. -/
theorem log_add_one_div_log_nat_add_one_le_of_le_rpow
    {q : ℕ} {z C : ℝ} (hq : q.Prime) (hqz : (q : ℝ) ≤ z)
    (hpow : z + 1 ≤ ((q : ℝ) + 1) ^ C) :
    Real.log (z + 1) / Real.log ((q : ℝ) + 1) ≤ C := by
  have hqone : 0 < (q : ℝ) + 1 := by positivity
  have hzone : 0 < z + 1 := by
    have hq0 : (0 : ℝ) ≤ q := by positivity
    linarith
  have hlogq : 0 < Real.log ((q : ℝ) + 1) :=
    Real.log_pos (by exact_mod_cast Nat.lt_add_one_iff.mpr hq.pos)
  have hlogle : Real.log (z + 1) ≤
      Real.log (((q : ℝ) + 1) ^ C) :=
    Real.strictMonoOn_log.monotoneOn hzone
      (Real.rpow_pos_of_pos hqone C) hpow
  rw [Real.log_rpow hqone] at hlogle
  exact (div_le_iff₀ hlogq).2 (by simpa [mul_comm] using hlogle)



/-- Exact missing interface for using the preceding theorem uniformly over the
large-terminal part of an upper Rosser carrier. -/
def UpperRosserLargeTerminalInitializationPowerBound
    (C Q z : ℝ) (S : BoundingSieve) : Prop :=
  ∀ q : ℕ, Q ≤ q → q ∈ S.prodPrimes.primeFactors →
    z + 1 ≤ ((q : ℝ) + 1) ^ C

/-- The missing bridge in the actual Chen upper-source parameter window, stated
with the same `q,z` information exposed by the current finite-prefix and
adaptive-tail producers.  In particular, `s ≤ 4` and
`s = log Δ / log z` are recorded, but the existing carrier hypothesis only says
`q ≤ z`; it does not prove the reverse power comparison required above. -/
def UpperRosserChenWindowInitializationPowerBridge (C : ℝ) : Prop :=
  ∃ Q : ℝ, 2 ≤ Q ∧
    ∀ (S : BoundingSieve) (z Δ s : ℝ),
      2 ≤ z → 0 < Δ → s = Real.log Δ / Real.log z →
      3 / 2 ≤ s → s ≤ 4 →
      (∀ p ∈ S.prodPrimes.primeFactors, (p : ℝ) ≤ z) →
      UpperRosserLargeTerminalInitializationPowerBound C Q z S


end

end MathlibNt.SieveTheory.SwitchingPrinciple

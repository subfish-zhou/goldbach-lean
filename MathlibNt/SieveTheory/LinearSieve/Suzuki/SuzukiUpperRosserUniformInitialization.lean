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

/-- The relative reverse-pair iterate is genuinely uniform in the carrier once
one supplies a fixed power bound between its ambient endpoint and terminal.
The factor `101/100` is the already proved one-time local-product payment. -/
theorem exists_upperRosserAlternatingPairDiscreteRelativeIterate_finiteDepth_uniform_of_rpow
    (K : ℝ) (hK : 1 ≤ K) (C : ℝ) :
    ∃ Q : ℝ, 2 ≤ Q ∧
      ∀ (S : BoundingSieve) (k q : ℕ) (r z : ℝ) (P : Finset ℕ),
        Q ≤ q → q.Prime → HasDimensionOneLocalProductBound S K →
        3 ≤ r → (q : ℝ) ≤ z →
        P ⊆ S.prodPrimes.primeFactors →
        (∀ p ∈ P, q < p) → (∀ p ∈ P, (p : ℝ) ≤ z) →
        z + 1 ≤ ((q : ℝ) + 1) ^ C →
        upperRosserAlternatingPairDiscreteRelativeIterate S.nu k q r P ≤
          (101 / 100 : ℝ) * C * (9 / 10 : ℝ) ^ k * r ^ 2 := by
  obtain ⟨Q, hQ, hrelative⟩ :=
    exists_upperRosserAlternatingPairDiscreteRelativeIterate_finiteDepth_geometric K hK
  refine ⟨Q, hQ, ?_⟩
  intro S k q r z P hQq hq hlocal hr hqz hP hqP hzP hpow
  have hbound := hrelative S k q r z P hQq hq hlocal hr hqz hP hqP hzP
  have hratio := log_add_one_div_log_nat_add_one_le_of_le_rpow hq hqz hpow
  calc
    upperRosserAlternatingPairDiscreteRelativeIterate S.nu k q r P ≤
        (101 / 100 : ℝ) *
          (Real.log (z + 1) / Real.log ((q : ℝ) + 1)) *
            (9 / 10 : ℝ) ^ k * r ^ 2 := hbound
    _ = ((101 / 100 : ℝ) * (9 / 10 : ℝ) ^ k * r ^ 2) *
          (Real.log (z + 1) / Real.log ((q : ℝ) + 1)) := by ring
    _ ≤ ((101 / 100 : ℝ) * (9 / 10 : ℝ) ^ k * r ^ 2) * C :=
      mul_le_mul_of_nonneg_left hratio (by positivity)
    _ = (101 / 100 : ℝ) * C * (9 / 10 : ℝ) ^ k * r ^ 2 := by ring

/-- Uniform-in-carrier fixed-depth estimate for the actual relative boundary
chain density, conditional only on the explicit endpoint power comparison. -/
theorem exists_upperRosserBoundaryChainsFixedDepthRelativeDensity_uniform_of_rpow
    (K : ℝ) (hK : 1 ≤ K) (C : ℝ) :
    ∃ Q : ℝ, 2 ≤ Q ∧
      ∀ (S : BoundingSieve) (k q : ℕ) (z Δ s : ℝ),
        Q ≤ q → 2 ≤ z → 0 < Δ → s = Real.log Δ / Real.log z →
        HasDimensionOneLocalProductBound S K →
        (∀ p ∈ S.prodPrimes.primeFactors, (p : ℝ) ≤ z) →
        q ∈ S.prodPrimes.primeFactors →
        z + 1 ≤ ((q : ℝ) + 1) ^ C →
        LinearSieve.upperRosserBoundaryChainsFixedDepthRelativeDensity
            S.nu (Nat.floor Δ + 1) q
            (S.prodPrimes.primeFactors.filter (fun p => q < p)) k ≤
          9 * (101 / 100 : ℝ) * C * (9 / 10 : ℝ) ^ k := by
  obtain ⟨Q, hQ, hrelative⟩ :=
    exists_upperRosserBoundaryChainsFixedDepthRelativeDensity_geometric K hK
  refine ⟨Q, hQ, ?_⟩
  intro S k q z Δ s hQq hz hΔ hs hlocal hcut hq hpow
  have hbound := hrelative S k q z Δ s hQq hz hΔ hs hlocal hcut hq
  have hqPrime : q.Prime := Nat.prime_of_mem_primeFactors hq
  have hqz : (q : ℝ) ≤ z := hcut q hq
  have hratio :=
    log_add_one_div_log_nat_add_one_le_of_le_rpow hqPrime hqz hpow
  calc
    LinearSieve.upperRosserBoundaryChainsFixedDepthRelativeDensity
        S.nu (Nat.floor Δ + 1) q
        (S.prodPrimes.primeFactors.filter (fun p => q < p)) k ≤
      9 * (101 / 100 : ℝ) *
        (Real.log (z + 1) / Real.log ((q : ℝ) + 1)) *
          (9 / 10 : ℝ) ^ k := hbound
    _ = (9 * (101 / 100 : ℝ) * (9 / 10 : ℝ) ^ k) *
          (Real.log (z + 1) / Real.log ((q : ℝ) + 1)) := by ring
    _ ≤ (9 * (101 / 100 : ℝ) * (9 / 10 : ℝ) ^ k) * C :=
      mul_le_mul_of_nonneg_left hratio (by positivity)
    _ = 9 * (101 / 100 : ℝ) * C * (9 / 10 : ℝ) ^ k := by ring

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

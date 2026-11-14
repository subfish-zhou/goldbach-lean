module

public import MathlibNt.SieveTheory.Arithmetic.MertensTheorem

/-!
# Prime reciprocal sums on logarithmic intervals

This module turns the uniform error term in Mertens' second theorem into the
fixed-endpoint limit

`∑_{N^a < p ≤ N^b} 1 / p → log (b / a)`

for `0 < a < b`.  Both cutoffs are real powers; the finite carrier uses the
floor of the upper cutoff, and the lower endpoint remains strict.
-/

@[expose] public section

namespace MathlibNt.SieveTheory.PrimeReciprocalLogScale

open Filter Real Finset
open scoped Topology

/-- The natural cutoff obtained by flooring the real power `N ^ a`. -/
noncomputable def rpowFloor (N : ℕ) (a : ℝ) : ℕ :=
  Nat.floor ((N : ℝ) ^ a)

/-- The reciprocal sum over primes in the real interval `N ^ a < p ≤ N ^ b`. -/
noncomputable def primeReciprocalLogInterval (N : ℕ) (a b : ℝ) : ℝ :=
  ((Finset.range (rpowFloor N b + 1)).filter fun p : ℕ =>
    p.Prime ∧ (N : ℝ) ^ a < (p : ℝ) ∧ (p : ℝ) ≤ (N : ℝ) ^ b).sum
      (fun p => 1 / (p : ℝ))

/-- A positive real power, restricted to natural inputs and then floored,
tends to infinity. -/
theorem tendsto_rpowFloor_atTop {a : ℝ} (ha : 0 < a) :
    Tendsto (fun N : ℕ => rpowFloor N a) atTop atTop :=
  MertensTheorem.tendsto_rpowFloor_atTop ha

/-- In particular, the floored power is eventually in the range where the
uniform Mertens estimate applies. -/
theorem eventually_two_le_rpowFloor {a : ℝ} (ha : 0 < a) :
    ∀ᶠ N : ℕ in atTop, 2 ≤ rpowFloor N a :=
  MertensTheorem.eventually_two_le_rpowFloor ha

/-- Flooring a positive real power changes it by a relative error tending to
zero. -/
theorem tendsto_rpowFloor_div_rpow {a : ℝ} (ha : 0 < a) :
    Tendsto (fun N : ℕ => (rpowFloor N a : ℝ) / ((N : ℝ) ^ a))
      atTop (nhds 1) :=
  MertensTheorem.tendsto_rpowFloor_div_rpow ha

/-- The logarithm of a floored positive power tends to infinity. -/
theorem tendsto_log_rpowFloor_atTop {a : ℝ} (ha : 0 < a) :
    Tendsto (fun N : ℕ => Real.log (rpowFloor N a : ℝ)) atTop atTop :=
  MertensTheorem.tendsto_log_rpowFloor_atTop ha

/-- The first logarithm is unchanged asymptotically by flooring. -/
theorem tendsto_log_rpowFloor_sub_log_rpow {a : ℝ} (ha : 0 < a) :
    Tendsto (fun N : ℕ =>
      Real.log (rpowFloor N a : ℝ) - Real.log ((N : ℝ) ^ a))
      atTop (nhds 0) :=
  MertensTheorem.tendsto_log_rpowFloor_sub_log_rpow ha

/-- Supporting log--log asymptotic, including the exact `log (N ^ a) = a log N`
algebra: `log log floor(N^a) = log a + log log N + o(1)`. -/
theorem tendsto_log_log_rpowFloor_sub {a : ℝ} (ha : 0 < a) :
    Tendsto (fun N : ℕ =>
      Real.log (Real.log (rpowFloor N a : ℝ)) -
        (Real.log a + Real.log (Real.log (N : ℝ)))) atTop (nhds 0) :=
  MertensTheorem.tendsto_log_log_rpowFloor_sub ha

/-- The real-cutoff interval sum is exactly the difference of the two Mertens
prefixes.  Thus the lower endpoint is strict and the upper endpoint is
non-strict, with no rounding error term. -/
theorem primeReciprocalLogInterval_eq_sub (N : ℕ) {a b : ℝ}
    (hN : 1 ≤ N) (hab : a ≤ b) :
    primeReciprocalLogInterval N a b =
      MertensTheorem.primeReciprocalSum (rpowFloor N b) -
      MertensTheorem.primeReciprocalSum (rpowFloor N a) := by
  let upper := (Finset.range (rpowFloor N b + 1)).filter Nat.Prime
  let lower := (Finset.range (rpowFloor N a + 1)).filter Nat.Prime
  have hbase : (1 : ℝ) ≤ N := by
    exact_mod_cast hN
  have hpows : (N : ℝ) ^ a ≤ (N : ℝ) ^ b :=
    Real.rpow_le_rpow_of_exponent_le hbase hab
  have hfloors : rpowFloor N a ≤ rpowFloor N b :=
    Nat.floor_mono hpows
  have hsub : lower ⊆ upper := by
    intro p hp
    simp only [lower, upper, Finset.mem_filter, Finset.mem_range] at hp ⊢
    exact ⟨lt_of_lt_of_le hp.1 (Nat.add_le_add_right hfloors 1), hp.2⟩
  change (∑ p ∈ (Finset.range (rpowFloor N b + 1)).filter (fun p : ℕ =>
      p.Prime ∧ (N : ℝ) ^ a < (p : ℝ) ∧ (p : ℝ) ≤ (N : ℝ) ^ b),
        1 / (p : ℝ)) =
    (∑ p ∈ upper, 1 / (p : ℝ)) - ∑ p ∈ lower, 1 / (p : ℝ)
  rw [← Finset.sum_sdiff_eq_sub hsub]
  apply Finset.sum_congr
  · ext p
    simp only [upper, lower, Finset.mem_filter, Finset.mem_range,
      Finset.mem_sdiff, Nat.lt_add_one_iff]
    have hpa : 0 ≤ (N : ℝ) ^ a :=
      Real.rpow_nonneg (Nat.cast_nonneg N) _
    have hpb : 0 ≤ (N : ℝ) ^ b :=
      Real.rpow_nonneg (Nat.cast_nonneg N) _
    -- Translate both floored cutoffs before comparing the prime supports.
    simp only [rpowFloor, Nat.le_floor_iff hpa, Nat.le_floor_iff hpb]
    by_cases hprime : p.Prime <;>
      simp [hprime, not_le, and_comm]
  · intro p hp
    rfl

/-- For fixed `0 < a < b`, the reciprocal sum over the real interval
`N^a < p ≤ N^b` tends to `log (b / a)`. -/
theorem tendsto_primeReciprocalLogInterval {a b : ℝ}
    (ha : 0 < a) (hab : a < b) :
    Tendsto (fun N : ℕ => primeReciprocalLogInterval N a b)
      atTop (nhds (Real.log (b / a))) := by
  have h := MertensTheorem.tendsto_weightedPrimeReciprocalLogSum_const (c := 1) ha hab
  simp only [one_mul] at h
  apply h.congr'
  filter_upwards [eventually_gt_atTop (1 : ℕ)] with N hN
  have hweighted := MertensTheorem.weightedPrimeReciprocalLogSum_eq_sub_sub_integral
    ha hab.le (f := fun _ => 1) (f' := fun _ => 0)
    (fun x => hasDerivAt_const x 1) continuous_const hN
  simpa only [rpowFloor, MertensTheorem.rpowFloor, MertensTheorem.logScaleDeriv, zero_div, zero_mul, MeasureTheory.integral_zero,
    sub_zero, one_mul, primeReciprocalLogInterval_eq_sub N (by omega : 1 ≤ N) hab.le]
    using hweighted


end MathlibNt.SieveTheory.PrimeReciprocalLogScale

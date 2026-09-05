import MathlibNt.SieveTheory.Arithmetic.MertensTheorem

/-!
# Prime reciprocal sums on logarithmic intervals

This module turns the uniform error term in Mertens' second theorem into the
fixed-endpoint limit

`∑_{N^a < p ≤ N^b} 1 / p → log (b / a)`

for `0 < a < b`.  Both cutoffs are real powers; the finite carrier uses the
floor of the upper cutoff, and the lower endpoint remains strict.
-/

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
    Tendsto (fun N : ℕ => rpowFloor N a) atTop atTop := by
  exact tendsto_nat_floor_atTop.comp
    ((tendsto_rpow_atTop ha).comp tendsto_natCast_atTop_atTop)

/-- In particular, the floored power is eventually in the range where the
uniform Mertens estimate applies. -/
theorem eventually_two_le_rpowFloor {a : ℝ} (ha : 0 < a) :
    ∀ᶠ N : ℕ in atTop, 2 ≤ rpowFloor N a :=
  (tendsto_rpowFloor_atTop ha).eventually (eventually_ge_atTop 2)

/-- Flooring a positive real power changes it by a relative error tending to
zero. -/
theorem tendsto_rpowFloor_div_rpow {a : ℝ} (ha : 0 < a) :
    Tendsto (fun N : ℕ => (rpowFloor N a : ℝ) / ((N : ℝ) ^ a))
      atTop (nhds 1) := by
  have hpow : Tendsto (fun N : ℕ => (N : ℝ) ^ a) atTop atTop :=
    (tendsto_rpow_atTop ha).comp tendsto_natCast_atTop_atTop
  have hlower : Tendsto (fun N : ℕ => 1 - 1 / ((N : ℝ) ^ a))
      atTop (nhds 1) := by
    simpa using (hpow.const_div_atTop 1).const_sub 1
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le'
    hlower tendsto_const_nhds ?_ ?_
  · filter_upwards [hpow.eventually (eventually_gt_atTop 0)] with N hpos
    have hfloorlt : ((N : ℝ) ^ a) < (rpowFloor N a : ℝ) + 1 := by
      exact_mod_cast Nat.lt_floor_add_one ((N : ℝ) ^ a)
    rw [sub_le_iff_le_add, ← add_div, le_div_iff₀ hpos]
    simpa only [one_mul] using le_of_lt hfloorlt
  · filter_upwards [hpow.eventually (eventually_gt_atTop 0)] with N hpos
    rw [div_le_one hpos]
    exact Nat.floor_le (le_of_lt hpos)

/-- The logarithm of a floored positive power tends to infinity. -/
theorem tendsto_log_rpowFloor_atTop {a : ℝ} (ha : 0 < a) :
    Tendsto (fun N : ℕ => Real.log (rpowFloor N a : ℝ)) atTop atTop := by
  exact Real.tendsto_log_atTop.comp
    (tendsto_natCast_atTop_atTop.comp (tendsto_rpowFloor_atTop ha))

/-- The first logarithm is unchanged asymptotically by flooring. -/
theorem tendsto_log_rpowFloor_sub_log_rpow {a : ℝ} (ha : 0 < a) :
    Tendsto (fun N : ℕ =>
      Real.log (rpowFloor N a : ℝ) - Real.log ((N : ℝ) ^ a))
      atTop (nhds 0) := by
  have hpow : Tendsto (fun N : ℕ => (N : ℝ) ^ a) atTop atTop :=
    (tendsto_rpow_atTop ha).comp tendsto_natCast_atTop_atTop
  have h := (tendsto_rpowFloor_div_rpow ha).log one_ne_zero
  simpa only [Real.log_one] using h.congr' (by
    filter_upwards [eventually_two_le_rpowFloor ha,
      hpow.eventually (eventually_gt_atTop 0)] with N hfloor hpowPos
    rw [Real.log_div (by positivity) (ne_of_gt hpowPos)])

/-- Supporting log--log asymptotic, including the exact `log (N ^ a) = a log N`
algebra: `log log floor(N^a) = log a + log log N + o(1)`. -/
theorem tendsto_log_log_rpowFloor_sub {a : ℝ} (ha : 0 < a) :
    Tendsto (fun N : ℕ =>
      Real.log (Real.log (rpowFloor N a : ℝ)) -
        (Real.log a + Real.log (Real.log (N : ℝ)))) atTop (nhds 0) := by
  have hpow : Tendsto (fun N : ℕ => (N : ℝ) ^ a) atTop atTop :=
    (tendsto_rpow_atTop ha).comp tendsto_natCast_atTop_atTop
  have hlogpow : Tendsto (fun N : ℕ => Real.log ((N : ℝ) ^ a))
      atTop atTop :=
    Real.tendsto_log_atTop.comp hpow
  have hsmallRatio : Tendsto (fun N : ℕ =>
      (Real.log (rpowFloor N a : ℝ) - Real.log ((N : ℝ) ^ a)) /
        Real.log ((N : ℝ) ^ a)) atTop (nhds 0) :=
    (tendsto_log_rpowFloor_sub_log_rpow ha).div_atTop hlogpow
  have hden : ∀ᶠ N : ℕ in atTop, Real.log ((N : ℝ) ^ a) ≠ 0 := by
    filter_upwards [hlogpow.eventually (eventually_gt_atTop 0)] with N hN
    exact ne_of_gt hN
  have hlogRatio : Tendsto (fun N : ℕ =>
      Real.log (rpowFloor N a : ℝ) / Real.log ((N : ℝ) ^ a))
      atTop (nhds 1) := by
    simpa only [zero_add] using (hsmallRatio.add_const 1).congr' (by
      filter_upwards [hden] with N hN
      field_simp [hN]
      ring)
  have hloglogRatio := hlogRatio.log one_ne_zero
  simpa only [Real.log_one] using hloglogRatio.congr' (by
    filter_upwards [eventually_two_le_rpowFloor ha,
      hlogpow.eventually (eventually_gt_atTop 0),
      eventually_gt_atTop (1 : ℕ)] with N hfloor hlogpowPos hN
    have hNpos : (0 : ℝ) < N := by
      exact_mod_cast Nat.zero_lt_of_lt hN
    have hlogNpos : 0 < Real.log (N : ℝ) :=
      Real.log_pos (by exact_mod_cast hN)
    have hlogfloorPos : 0 < Real.log (rpowFloor N a : ℝ) :=
      Real.log_pos (by
        exact_mod_cast lt_of_lt_of_le Nat.one_lt_two hfloor)
    rw [Real.log_div (ne_of_gt hlogfloorPos) (ne_of_gt hlogpowPos)]
    congr 1
    rw [Real.log_rpow hNpos,
      Real.log_mul (ne_of_gt ha) (ne_of_gt hlogNpos)])

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
    constructor
    · rintro ⟨prange, hprime, hlow, hupp⟩
      refine ⟨⟨prange, hprime⟩, ?_⟩
      intro hlower
      have hlower' := hlower.1
      change p ≤ Nat.floor ((N : ℝ) ^ a) at hlower'
      have hle : (p : ℝ) ≤ (N : ℝ) ^ a :=
        (Nat.le_floor_iff hpa).mp hlower'
      exact (not_le_of_gt hlow) hle
    · rintro ⟨⟨prange, hprime⟩, hlower⟩
      have prange' := prange
      change p ≤ Nat.floor ((N : ℝ) ^ b) at prange'
      have hupp : (p : ℝ) ≤ (N : ℝ) ^ b :=
        (Nat.le_floor_iff hpb).mp prange'
      refine ⟨prange, hprime, ?_, hupp⟩
      rw [← Nat.floor_lt hpa]
      by_contra hnot
      apply hlower
      refine ⟨?_, hprime⟩
      simpa only [rpowFloor] using le_of_not_gt hnot
  · intro p hp
    rfl

/-- The uniform Mertens error tends to zero along a floored positive power. -/
private theorem tendsto_mertens_error_rpowFloor {a B C : ℝ} (ha : 0 < a)
    (hM : ∀ x : ℕ, 2 ≤ x →
      |MertensTheorem.primeReciprocalSum x -
          (Real.log (Real.log x) + B)| ≤ C / Real.log x) :
    Tendsto (fun N : ℕ =>
      MertensTheorem.primeReciprocalSum (rpowFloor N a) -
        (Real.log (Real.log (rpowFloor N a)) + B)) atTop (nhds 0) := by
  rw [tendsto_zero_iff_norm_tendsto_zero]
  have hupper : Tendsto
      (fun N : ℕ => C / Real.log (rpowFloor N a : ℝ))
      atTop (nhds 0) :=
    (tendsto_log_rpowFloor_atTop ha).const_div_atTop C
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le'
    tendsto_const_nhds hupper
    (Filter.Eventually.of_forall fun N => norm_nonneg _) ?_
  filter_upwards [eventually_two_le_rpowFloor ha] with N hN
  simpa only [Real.norm_eq_abs] using hM (rpowFloor N a) hN

/-- Mertens' prefix at `floor (N^a)`, with its common `log log N` term
removed, tends to `log a + B`. -/
private theorem tendsto_mertens_prefix_normalized {a B C : ℝ} (ha : 0 < a)
    (hM : ∀ x : ℕ, 2 ≤ x →
      |MertensTheorem.primeReciprocalSum x -
          (Real.log (Real.log x) + B)| ≤ C / Real.log x) :
    Tendsto (fun N : ℕ =>
      MertensTheorem.primeReciprocalSum (rpowFloor N a) -
        (Real.log a + Real.log (Real.log (N : ℝ)) + B))
      atTop (nhds 0) := by
  have h := (tendsto_mertens_error_rpowFloor ha hM).add
    (tendsto_log_log_rpowFloor_sub ha)
  convert h using 1
  · funext N
    ring
  · ring_nf

/-- For fixed `0 < a < b`, the reciprocal sum over the real interval
`N^a < p ≤ N^b` tends to `log (b / a)`. -/
theorem tendsto_primeReciprocalLogInterval {a b : ℝ}
    (ha : 0 < a) (hab : a < b) :
    Tendsto (fun N : ℕ => primeReciprocalLogInterval N a b)
      atTop (nhds (Real.log (b / a))) := by
  obtain ⟨B, C, hM⟩ := MertensTheorem.mertens_second_theorem
  have hb : 0 < b := lt_trans ha hab
  have haLimit := tendsto_mertens_prefix_normalized ha hM
  have hbLimit := tendsto_mertens_prefix_normalized hb hM
  have hdiff : Tendsto (fun N : ℕ =>
      MertensTheorem.primeReciprocalSum (rpowFloor N b) -
        MertensTheorem.primeReciprocalSum (rpowFloor N a))
      atTop (nhds (Real.log b - Real.log a)) := by
    have h := (hbLimit.sub haLimit).add_const (Real.log b - Real.log a)
    convert h using 1
    · funext N
      ring
    · ring_nf
  rw [Real.log_div (ne_of_gt hb) (ne_of_gt ha)]
  apply hdiff.congr'
  filter_upwards [eventually_ge_atTop (1 : ℕ)] with N hN
  exact (primeReciprocalLogInterval_eq_sub N hN (le_of_lt hab)).symm

/-- Quantitative eventual form of the fixed-cell limit.  It is directly
suitable for taking a maximum of the finitely many thresholds belonging to a
fixed partition. -/
theorem eventually_abs_primeReciprocalLogInterval_sub_lt {a b ε : ℝ}
    (ha : 0 < a) (hab : a < b) (hε : 0 < ε) :
    ∀ᶠ N : ℕ in atTop,
      |primeReciprocalLogInterval N a b - Real.log (b / a)| < ε := by
  have h := tendsto_primeReciprocalLogInterval ha hab
  rw [Metric.tendsto_nhds] at h
  filter_upwards [h ε hε] with N hN
  simpa only [Real.dist_eq] using hN

/-- Threshold form of the quantitative fixed-cell estimate. -/
theorem exists_abs_primeReciprocalLogInterval_sub_lt {a b ε : ℝ}
    (ha : 0 < a) (hab : a < b) (hε : 0 < ε) :
    ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
      |primeReciprocalLogInterval N a b - Real.log (b / a)| < ε := by
  simpa only [eventually_atTop] using
    (eventually_abs_primeReciprocalLogInterval_sub_lt ha hab hε)

end MathlibNt.SieveTheory.PrimeReciprocalLogScale

import MathlibNt.SieveTheory.Switching.ScreenedResidual

/-!
# Rosser lower sieves and Mertens normalization

Depth-zero boundary assembly, lower Rosser density inputs, and standard
Bombieri--Vinogradov distribution bounds combine with explicit Mertens and
singular-series normalization to give the base lower-sieve asymptotic.

All declarations retain the `MathlibNt.SieveTheory.SwitchingPrinciple` namespace.
-/

open scoped ArithmeticFunction.Moebius
open scoped ArithmeticFunction.zeta

set_option maxHeartbeats 6000000

namespace MathlibNt.SieveTheory.SwitchingPrinciple

open Real Finset
open MeasureTheory intervalIntegral

open scoped Classical
open scoped Asymptotics

namespace Internal
end Internal

open Internal

/-- The complete depth-zero outer Rosser contribution is controlled by one
dimension-one logarithmic interval.  This is the base case for the recursive
fixed-depth Darboux comparison. -/
theorem sum_mul_upperRosserBoundaryChainsFixedDepthDensity_zero_le_log_interval
    {S : BoundingSieve} {K z Δ s : ℝ}
    (hz : 2 ≤ z) (hΔ : 0 < Δ)
    (hlocal : HasDimensionOneLocalProductBound S K)
    (hcut : ∀ p ∈ S.prodPrimes.primeFactors, (p : ℝ) ≤ z)
    (hs : s = Real.log Δ / Real.log z) (hslo : 3 / 2 ≤ s)
    (hshi : s < 3) (hpow : 2 ≤ z ^ (s / 3)) :
    ∑ q ∈ S.prodPrimes.primeFactors,
        (S.nu q / (1 - S.nu q)) *
          LinearSieve.upperRosserBoundaryChainsFixedDepthDensity
            (fun p => S.nu p / (1 - S.nu p)) (Nat.floor Δ + 1) q
            (S.prodPrimes.primeFactors.filter (fun p => q < p)) 0 ≤
      Real.log (z + 1) / Real.log (z ^ (s / 3)) *
          (1 + K / Real.log (z ^ (s / 3))) - 1 := by
  have hD : 1 < Nat.floor Δ + 1 := by
    have htwo : 2 < Nat.floor Δ + 1 :=
      lt_floor_add_one_of_le_of_log_ratio (p := 2) hz hΔ hz hs hslo
    omega
  rw [LinearSieve.sum_mul_upperRosserBoundaryChainsFixedDepthDensity_zero
    (hD := hD) (hprime := fun p hp => Nat.prime_of_mem_primeFactors hp)]
  apply sum_nu_div_one_sub_le_of_subset_interval hlocal hpow
  · calc
      z ^ (s / 3) ≤ z ^ (1 : ℝ) :=
        Real.rpow_le_rpow_of_exponent_le (by linarith) (by linarith)
      _ = z := by simp
      _ ≤ z + 1 := by linarith
  · intro q hq
    exact (Finset.mem_filter.mp hq).1
  · intro q hq
    have hqS := (Finset.mem_filter.mp hq).1
    have hcube := (Finset.mem_filter.mp hq).2
    have hqPrime : q.Prime := Nat.prime_of_mem_primeFactors hqS
    have hterminal := LinearSieve.log_div_log_lt_of_floor_add_one_le
      (by linarith : 1 < z) hΔ hcube
    have hcoord : s / 3 < Real.log q / Real.log z := by
      rw [← hs] at hterminal
      rw [Nat.cast_pow, Real.log_pow] at hterminal
      calc
        s / 3 < (3 * Real.log q / Real.log z) / 3 :=
          div_lt_div_of_pos_right hterminal (by norm_num)
        _ = Real.log q / Real.log z := by ring
    have hzpos : 0 < z := by linarith
    have hqpos : (0 : ℝ) < q := by exact_mod_cast hqPrime.pos
    constructor
    · calc
        z ^ (s / 3) ≤ z ^ (Real.log q / Real.log z) :=
          (Real.rpow_lt_rpow_of_exponent_lt (by linarith) hcoord).le
        _ = (q : ℝ) := by
          simpa [Real.logb] using
            (Real.rpow_logb (x := (q : ℝ)) hzpos
              (by linarith : z ≠ 1) hqpos)
    · linarith [hcut q hqS]

/-- Quantitative depth-zero Darboux comparison.  Once the two elementary
logarithmic errors are at most `η`, the full outer cubic shell differs from its
continuous boundary integral by at most `4η + 2η²`, uniformly in
`3 / 2 ≤ s < 3`. -/
theorem sum_mul_upperRosserBoundaryChainsFixedDepthDensity_zero_le_integral_add
    {S : BoundingSieve} {K z Δ s η : ℝ}
    (hK : 0 ≤ K) (hη : 0 ≤ η)
    (hz : 2 ≤ z) (hΔ : 0 < Δ)
    (hlocal : HasDimensionOneLocalProductBound S K)
    (hcut : ∀ p ∈ S.prodPrimes.primeFactors, (p : ℝ) ≤ z)
    (hs : s = Real.log Δ / Real.log z) (hslo : 3 / 2 ≤ s)
    (hshi : s < 3) (hpow : 2 ≤ z ^ (s / 3))
    (hlogRatio : Real.log (z + 1) / Real.log z ≤ 1 + η)
    (herror : K / ((s / 3) * Real.log z) ≤ η) :
    ∑ q ∈ S.prodPrimes.primeFactors,
        (S.nu q / (1 - S.nu q)) *
          LinearSieve.upperRosserBoundaryChainsFixedDepthDensity
            (fun p => S.nu p / (1 - S.nu p)) (Nat.floor Δ + 1) q
            (S.prodPrimes.primeFactors.filter (fun p => q < p)) 0 ≤
      (∫ a in Set.Ioo 0 1, a⁻¹ * a⁻¹ *
        LinearSieve.upperRosserBoundaryMass 0 s a) + 4 * η + 2 * η ^ 2 := by
  have hbase :=
    sum_mul_upperRosserBoundaryChainsFixedDepthDensity_zero_le_log_interval
      hz hΔ hlocal hcut hs hslo hshi hpow
  have hzpos : 0 < z := by linarith
  have hlogz : 0 < Real.log z := Real.log_pos (by linarith)
  have hspos : 0 < s := by linarith
  have hratioNonneg : 0 ≤ Real.log (z + 1) / Real.log z :=
    div_nonneg (Real.log_nonneg (by linarith)) hlogz.le
  have herrorNonneg : 0 ≤ K / ((s / 3) * Real.log z) :=
    div_nonneg hK (mul_nonneg (by positivity) hlogz.le)
  have hproduct :
      Real.log (z + 1) / Real.log z *
          (1 + K / ((s / 3) * Real.log z)) ≤ (1 + η) * (1 + η) :=
    mul_le_mul hlogRatio (by linarith) (by linarith) (by linarith)
  have hdelta :
      Real.log (z + 1) / Real.log z *
          (1 + K / ((s / 3) * Real.log z)) - 1 ≤ 2 * η + η ^ 2 := by
    nlinarith
  have hsratioNonneg : 0 ≤ 3 / s := div_nonneg (by norm_num) hspos.le
  have hsratioLe : 3 / s ≤ 2 := by
    apply (div_le_iff₀ hspos).2
    nlinarith
  have hscaled :
      (3 / s) * (Real.log (z + 1) / Real.log z *
          (1 + K / ((s / 3) * Real.log z)) - 1) ≤
        2 * (2 * η + η ^ 2) :=
    (mul_le_mul_of_nonneg_left hdelta hsratioNonneg).trans
      (mul_le_mul_of_nonneg_right hsratioLe (by positivity))
  calc
    ∑ q ∈ S.prodPrimes.primeFactors,
        (S.nu q / (1 - S.nu q)) *
          LinearSieve.upperRosserBoundaryChainsFixedDepthDensity
            (fun p => S.nu p / (1 - S.nu p)) (Nat.floor Δ + 1) q
            (S.prodPrimes.primeFactors.filter (fun p => q < p)) 0 ≤
        Real.log (z + 1) / Real.log (z ^ (s / 3)) *
          (1 + K / Real.log (z ^ (s / 3))) - 1 := hbase
    _ = 3 / s * (Real.log (z + 1) / Real.log z) *
          (1 + K / ((s / 3) * Real.log z)) - 1 := by
      rw [Real.log_rpow hzpos]
      field_simp [hspos.ne', hlogz.ne']
    _ = 3 / s - 1 + (3 / s) *
          (Real.log (z + 1) / Real.log z *
            (1 + K / ((s / 3) * Real.log z)) - 1) := by ring
    _ ≤ 3 / s - 1 + 2 * (2 * η + η ^ 2) := by linarith
    _ = (∫ a in Set.Ioo 0 1, a⁻¹ * a⁻¹ *
          LinearSieve.upperRosserBoundaryMass 0 s a) + 4 * η + 2 * η ^ 2 := by
      rw [LinearSieve.integral_upperRosserBoundaryMass_zero hspos hshi]
      ring

/-- For `s ≥ 3`, the depth-zero outer cubic shell is empty: all sieving primes
lie below `z`, while the Rosser level lies above `z³`. -/
theorem sum_mul_upperRosserBoundaryChainsFixedDepthDensity_zero_eq_zero
    {S : BoundingSieve} {z Δ s : ℝ}
    (hz : 2 ≤ z) (hΔ : 0 < Δ)
    (hcut : ∀ p ∈ S.prodPrimes.primeFactors, (p : ℝ) ≤ z)
    (hs : s = Real.log Δ / Real.log z) (hs3 : 3 ≤ s) :
    ∑ q ∈ S.prodPrimes.primeFactors,
        (S.nu q / (1 - S.nu q)) *
          LinearSieve.upperRosserBoundaryChainsFixedDepthDensity
            (fun p => S.nu p / (1 - S.nu p)) (Nat.floor Δ + 1) q
            (S.prodPrimes.primeFactors.filter (fun p => q < p)) 0 = 0 := by
  have hslo : 3 / 2 ≤ s := by linarith
  have hD : 1 < Nat.floor Δ + 1 := by
    have htwo : 2 < Nat.floor Δ + 1 :=
      lt_floor_add_one_of_le_of_log_ratio (p := 2) hz hΔ hz hs hslo
    omega
  rw [LinearSieve.sum_mul_upperRosserBoundaryChainsFixedDepthDensity_zero
    (hD := hD) (hprime := fun p hp => Nat.prime_of_mem_primeFactors hp)]
  apply Finset.sum_eq_zero
  intro q hq
  exfalso
  have hqS := (Finset.mem_filter.mp hq).1
  have hcube := (Finset.mem_filter.mp hq).2
  have hzpos : 0 < z := by linarith
  have hlogz : 0 < Real.log z := Real.log_pos (by linarith)
  have hlogΔ : Real.log Δ = s * Real.log z := by
    rw [hs]
    field_simp
  have hlogcube : Real.log (z ^ (3 : ℕ)) = 3 * Real.log z := by
    rw [Real.log_pow]
    norm_num
  have hzCubePos : 0 < z ^ (3 : ℕ) := pow_pos hzpos 3
  have hzCubeLeΔ : z ^ (3 : ℕ) ≤ Δ := by
    apply (Real.strictMonoOn_log.le_iff_le hzCubePos hΔ).mp
    rw [hlogcube, hlogΔ]
    exact mul_le_mul_of_nonneg_right hs3 hlogz.le
  have hqCubeLe : ((q : ℝ) ^ (3 : ℕ)) ≤ z ^ (3 : ℕ) :=
    pow_le_pow_left₀ (by positivity) (hcut q hqS) 3
  have hqFloor : q ^ 3 ≤ Nat.floor Δ := by
    apply Nat.le_floor
    norm_num at hqCubeLe ⊢
    exact hqCubeLe.trans hzCubeLeΔ
  omega

/-- Uniform cutoff form of the depth-zero Darboux comparison.  This discharges
the power-cutoff, endpoint-logarithm, and local-product errors simultaneously. -/
theorem exists_sum_mul_upperRosserBoundaryChainsFixedDepthDensity_zero_le_integral_add
    (K ρ : ℝ) (hK : 0 ≤ K) (hρ : 0 < ρ) :
    ∃ z₀ : ℝ, 2 ≤ z₀ ∧ ∀ (S : BoundingSieve) (z Δ s : ℝ),
      z₀ ≤ z → 0 < Δ → HasDimensionOneLocalProductBound S K →
      (∀ p ∈ S.prodPrimes.primeFactors, (p : ℝ) ≤ z) →
      s = Real.log Δ / Real.log z → 3 / 2 ≤ s → s < 3 →
      ∑ q ∈ S.prodPrimes.primeFactors,
          (S.nu q / (1 - S.nu q)) *
            LinearSieve.upperRosserBoundaryChainsFixedDepthDensity
              (fun p => S.nu p / (1 - S.nu p)) (Nat.floor Δ + 1) q
              (S.prodPrimes.primeFactors.filter (fun p => q < p)) 0 ≤
        (∫ a in Set.Ioo 0 1, a⁻¹ * a⁻¹ *
          LinearSieve.upperRosserBoundaryMass 0 s a) + ρ := by
  let η := min 1 (ρ / 6)
  have hη : 0 < η := lt_min (by norm_num) (div_pos hρ (by norm_num))
  have hηone : η ≤ 1 := min_le_left _ _
  have hηρ : η ≤ ρ / 6 := min_le_right _ _
  obtain ⟨zA, hzA2, hzA⟩ :=
    exists_localProduct_error_cutoff (K := 1) (η := η) (c := 1)
      hη (by norm_num)
  obtain ⟨zK, hzK2, hzK⟩ :=
    exists_localProduct_error_cutoff (K := K) (η := η) (c := 1 / 2)
      hη (by norm_num)
  refine ⟨max 4 (max zA zK), by simp [hzA2], ?_⟩
  intro S z Δ s hz hΔ hlocal hcut hs hslo hshi
  have hz4 : 4 ≤ z := (le_max_left _ _).trans hz
  have hzA_le : zA ≤ z := (le_max_left zA zK).trans
    ((le_max_right 4 (max zA zK)).trans hz)
  have hzK_le : zK ≤ z := (le_max_right zA zK).trans
    ((le_max_right 4 (max zA zK)).trans hz)
  have hz2 : 2 ≤ z := by linarith
  have hz1 : 1 < z := by linarith
  have hzpos : 0 < z := by linarith
  have hlogz : 0 < Real.log z := Real.log_pos hz1
  have hsHalf : (1 / 2 : ℝ) ≤ s / 3 := by linarith
  have hpow : 2 ≤ z ^ (s / 3) := by
    calc
      2 = Real.sqrt 4 := by norm_num
      _ ≤ Real.sqrt z := Real.sqrt_le_sqrt hz4
      _ = z ^ (1 / 2 : ℝ) := Real.sqrt_eq_rpow z
      _ ≤ z ^ (s / 3) :=
        Real.monotone_rpow_of_base_ge_one (by linarith) hsHalf
  have honeLog : 1 / Real.log z ≤ η := by
    simpa using hzA z hzA_le
  have hlogstep : Real.log (z + 1) - Real.log z ≤ 1 / z := by
    rw [← Real.log_div (by positivity) hzpos.ne']
    calc
      Real.log ((z + 1) / z) = Real.log (1 + 1 / z) := by
        congr 1
        field_simp [hzpos.ne']
      _ ≤ (1 + 1 / z) - 1 :=
        Real.log_le_sub_one_of_pos (by positivity)
      _ = 1 / z := by ring
  have hinvz : 1 / z ≤ 1 := by
    apply (div_le_iff₀ hzpos).2
    linarith
  have hone : 1 ≤ η * Real.log z := (div_le_iff₀ hlogz).1 honeLog
  have hlogRatio : Real.log (z + 1) / Real.log z ≤ 1 + η := by
    apply (div_le_iff₀ hlogz).2
    calc
      Real.log (z + 1) ≤ Real.log z + 1 / z := by linarith
      _ ≤ Real.log z + 1 := by linarith
      _ ≤ (1 + η) * Real.log z := by nlinarith
  have herror : K / ((s / 3) * Real.log z) ≤ η :=
    (localProduct_error_le_of_log_coordinate_lower
      hK hz1 (by norm_num) hsHalf).trans (hzK z hzK_le)
  have hbase :=
    sum_mul_upperRosserBoundaryChainsFixedDepthDensity_zero_le_integral_add
      hK hη.le hz2 hΔ hlocal hcut hs hslo hshi hpow hlogRatio herror
  calc
    ∑ q ∈ S.prodPrimes.primeFactors,
        (S.nu q / (1 - S.nu q)) *
          LinearSieve.upperRosserBoundaryChainsFixedDepthDensity
            (fun p => S.nu p / (1 - S.nu p)) (Nat.floor Δ + 1) q
            (S.prodPrimes.primeFactors.filter (fun p => q < p)) 0 ≤
      (∫ a in Set.Ioo 0 1, a⁻¹ * a⁻¹ *
        LinearSieve.upperRosserBoundaryMass 0 s a) + 4 * η + 2 * η ^ 2 := hbase
    _ ≤ (∫ a in Set.Ioo 0 1, a⁻¹ * a⁻¹ *
        LinearSieve.upperRosserBoundaryMass 0 s a) + ρ := by
      have hηsq : η ^ 2 ≤ η := by nlinarith [hη.le]
      linarith

/-- Uniform depth-zero comparison on the whole upper-sieve range.  Below `3` it
is the quantitative logarithmic-interval estimate; from `3` onward both the
discrete cubic shell and its continuous boundary integral vanish. -/
theorem
    exists_sum_mul_upperRosserBoundaryChainsFixedDepthDensity_zero_le_integral_add_of_three_halves_le
    (K ρ : ℝ) (hK : 0 ≤ K) (hρ : 0 < ρ) :
    ∃ z₀ : ℝ, 2 ≤ z₀ ∧ ∀ (S : BoundingSieve) (z Δ s : ℝ),
      z₀ ≤ z → 0 < Δ → HasDimensionOneLocalProductBound S K →
      (∀ p ∈ S.prodPrimes.primeFactors, (p : ℝ) ≤ z) →
      s = Real.log Δ / Real.log z → 3 / 2 ≤ s →
      ∑ q ∈ S.prodPrimes.primeFactors,
          (S.nu q / (1 - S.nu q)) *
            LinearSieve.upperRosserBoundaryChainsFixedDepthDensity
              (fun p => S.nu p / (1 - S.nu p)) (Nat.floor Δ + 1) q
              (S.prodPrimes.primeFactors.filter (fun p => q < p)) 0 ≤
        (∫ a in Set.Ioo 0 1, a⁻¹ * a⁻¹ *
          LinearSieve.upperRosserBoundaryMass 0 s a) + ρ := by
  obtain ⟨z₀, hz₀, hlt⟩ :=
    exists_sum_mul_upperRosserBoundaryChainsFixedDepthDensity_zero_le_integral_add
      K ρ hK hρ
  refine ⟨z₀, hz₀, ?_⟩
  intro S z Δ s hz hΔ hlocal hcut hs hslo
  by_cases hshi : s < 3
  · exact hlt S z Δ s hz hΔ hlocal hcut hs hslo hshi
  · have hs3 : 3 ≤ s := le_of_not_gt hshi
    rw [sum_mul_upperRosserBoundaryChainsFixedDepthDensity_zero_eq_zero
      (hz₀.trans hz) hΔ hcut hs hs3]
    rw [LinearSieve.integral_upperRosserBoundaryMass_eq_zero_of_pow_le 0]
    · simpa using hρ.le
    · norm_num
      exact hs3

/-- Uniform comparison of a complete outer Rosser contribution at an arbitrary
fixed depth with its continuous boundary integral. -/
theorem
    exists_sum_mul_upperRosserBoundaryChainsFixedDepthDensity_le_integral_add_of_three_halves_le
    (k : ℕ) (K ρ : ℝ) (hK : 1 ≤ K) (hρ : 0 < ρ) :
    ∃ z₀ : ℝ, 2 ≤ z₀ ∧
      ∀ (S : BoundingSieve) (z Δ s : ℝ),
        z₀ ≤ z → 0 < Δ → HasDimensionOneLocalProductBound S K →
        (∀ p ∈ S.prodPrimes.primeFactors, (p : ℝ) ≤ z) →
        s = Real.log Δ / Real.log z → 3 / 2 ≤ s → s ≤ 4 →
        ∑ q ∈ S.prodPrimes.primeFactors,
            (S.nu q / (1 - S.nu q)) *
              LinearSieve.upperRosserBoundaryChainsFixedDepthDensity
                (fun p => S.nu p / (1 - S.nu p)) (Nat.floor Δ + 1) q
                (S.prodPrimes.primeFactors.filter (fun p => q < p)) k ≤
          (∫ a in Set.Ioo 0 1, a⁻¹ * a⁻¹ *
            LinearSieve.upperRosserBoundaryMass k s a) + ρ := by
  cases k with
  | zero =>
      obtain ⟨z₀, hz₀, hzero⟩ :=
        exists_sum_mul_upperRosserBoundaryChainsFixedDepthDensity_zero_le_integral_add_of_three_halves_le
          K ρ (zero_le_one.trans hK) hρ
      refine ⟨z₀, hz₀, ?_⟩
      intro S z Δ s hz hΔ hlocal hcut hs hslo hsupper
      exact hzero S z Δ s hz hΔ hlocal hcut hs hslo
  | succ k =>
      exact
        exists_sum_mul_upperRosserBoundaryChainsFixedDepthDensity_succ_le_integral_add_of_three_halves_le
          k K ρ hK hρ

/-- A finite collection of complete outer Rosser depths is uniformly bounded
by the corresponding finite continuous boundary factor.  The cutoff is the
maximum of the finitely many fixed-depth cutoffs, with the error split at each
successor step; the empty range needs no cutoff beyond `2`. -/
theorem
    exists_sum_range_sum_mul_upperRosserBoundaryChainsFixedDepthDensity_le_upperRosserFiniteBoundaryFactor_sub_one_add
    (L : ℕ) (K ρ : ℝ) (hK : 1 ≤ K) (hρ : 0 < ρ) :
    ∃ z₀ : ℝ, 2 ≤ z₀ ∧
      ∀ (S : BoundingSieve) (z Δ s : ℝ),
        z₀ ≤ z → 0 < Δ → HasDimensionOneLocalProductBound S K →
        (∀ p ∈ S.prodPrimes.primeFactors, (p : ℝ) ≤ z) →
        s = Real.log Δ / Real.log z → 3 / 2 ≤ s → s ≤ 4 →
        ∑ k ∈ Finset.range L,
            ∑ q ∈ S.prodPrimes.primeFactors,
              (S.nu q / (1 - S.nu q)) *
                LinearSieve.upperRosserBoundaryChainsFixedDepthDensity
                  (fun p => S.nu p / (1 - S.nu p)) (Nat.floor Δ + 1) q
                  (S.prodPrimes.primeFactors.filter (fun p => q < p)) k ≤
          LinearSieve.upperRosserFiniteBoundaryFactor L s - 1 + ρ := by
  induction L generalizing ρ with
  | zero =>
      refine ⟨2, le_rfl, ?_⟩
      intro S z Δ s hz hΔ hlocal hcut hs hslo hsupper
      simp [LinearSieve.upperRosserFiniteBoundaryFactor, hρ.le]
  | succ L ih =>
      obtain ⟨zPrev, hzPrev, hprev⟩ :=
        ih (ρ / 2) (half_pos hρ)
      obtain ⟨zLast, hzLast, hlast⟩ :=
        exists_sum_mul_upperRosserBoundaryChainsFixedDepthDensity_le_integral_add_of_three_halves_le
          L K (ρ / 2) hK (half_pos hρ)
      let z₀ : ℝ := max zPrev zLast
      refine ⟨z₀, hzPrev.trans (le_max_left _ _), ?_⟩
      intro S z Δ s hz hΔ hlocal hcut hs hslo hsupper
      have hzPrevZ : zPrev ≤ z := (le_max_left _ _).trans hz
      have hzLastZ : zLast ≤ z := (le_max_right _ _).trans hz
      have hprevBound :=
        hprev S z Δ s hzPrevZ hΔ hlocal hcut hs hslo hsupper
      have hlastBound :=
        hlast S z Δ s hzLastZ hΔ hlocal hcut hs hslo hsupper
      rw [Finset.sum_range_succ,
        LinearSieve.upperRosserFiniteBoundaryFactor_succ]
      linarith

/-- Finite upper-sieve bound obtained from the Rosser path expansion and the
dimension-one local-product hypothesis.  The sole remaining analytic quantity
is the selected cubic-boundary chain sum displayed on the right. -/
theorem mainSum_upperRosserWeight_le_boundaryChains
    {S : BoundingSieve} {K z Δ s : ℝ}
    (hz : 2 ≤ z) (hΔ : 0 < Δ)
    (hlocal : HasDimensionOneLocalProductBound S K)
    (hcut : ∀ p ∈ S.prodPrimes.primeFactors, (p : ℝ) ≤ z)
    (hs : s = Real.log Δ / Real.log z) (hslo : 3 / 2 ≤ s) :
    S.mainSum
          (LinearSieve.upperRosserWeight S.prodPrimes (Nat.floor Δ + 1)) ≤
      (1 + ∑ q ∈ S.prodPrimes.primeFactors,
        (S.nu q / (1 - S.nu q)) *
          ((Real.log (z + 1) / Real.log ((q : ℝ) + 1) *
            (1 + K / Real.log ((q : ℝ) + 1))) *
            ∑ t ∈
                (S.prodPrimes.primeFactors.filter (fun p => q < p)).powerset.filter
                  (LinearSieve.UpperRosserBoundarySet (Nat.floor Δ + 1) q),
              ∏ p ∈ t, S.nu p / (1 - S.nu p))) *
        ∏ p ∈ S.prodPrimes.primeFactors, (1 - S.nu p) := by
  have hlevel :
      ∀ p ∈ S.prodPrimes.primeFactors, p < Nat.floor Δ + 1 := by
    intro p hp
    exact lt_floor_add_one_of_le_of_log_ratio hz hΔ (hcut p hp) hs hslo
  have hD : 1 < Nat.floor Δ + 1 :=
    lt_floor_add_one_of_le_of_log_ratio hz hΔ (by norm_num; linarith) hs hslo
  have hratio :=
    upperRosserSetDensityRatio_le_one_add_boundaryChains hD hlocal hcut hlevel
  have hproduct :
      0 < ∏ p ∈ S.prodPrimes.primeFactors, (1 - S.nu p) := by
    apply Finset.prod_pos
    intro p hp
    have hpdvd : p ∣ S.prodPrimes :=
      (Nat.mem_primeFactors_of_ne_zero S.prodPrimes_ne_zero).mp hp |>.2
    exact sub_pos.mpr
      (S.nu_lt_one_of_prime p (Nat.prime_of_mem_primeFactors hp) hpdvd)
  have hmul := mul_le_mul_of_nonneg_right hratio hproduct.le
  rw [div_mul_cancel₀ _ hproduct.ne'] at hmul
  rw [LinearSieve.mainSum_upperRosserWeight_eq_setDensitySum]
  exact hmul

/-- The finite upper-sieve bound with the selected boundary mass indexed directly
by Buchstab pair depth.  This is the exact discrete expression to split into a
fixed-depth approximation and a large-depth tail. -/
theorem mainSum_upperRosserWeight_le_boundaryChains_by_depth
    {S : BoundingSieve} {K z Δ s : ℝ}
    (hz : 2 ≤ z) (hΔ : 0 < Δ)
    (hlocal : HasDimensionOneLocalProductBound S K)
    (hcut : ∀ p ∈ S.prodPrimes.primeFactors, (p : ℝ) ≤ z)
    (hs : s = Real.log Δ / Real.log z) (hslo : 3 / 2 ≤ s) :
    S.mainSum
          (LinearSieve.upperRosserWeight S.prodPrimes (Nat.floor Δ + 1)) ≤
      (1 + ∑ q ∈ S.prodPrimes.primeFactors,
        (S.nu q / (1 - S.nu q)) *
          ((Real.log (z + 1) / Real.log ((q : ℝ) + 1) *
            (1 + K / Real.log ((q : ℝ) + 1))) *
            ∑ k ∈ Finset.range
                ((S.prodPrimes.primeFactors.filter (fun p => q < p)).card + 1),
              LinearSieve.upperRosserBoundaryChainsFixedDepthDensity
                (fun p => S.nu p / (1 - S.nu p)) (Nat.floor Δ + 1) q
                (S.prodPrimes.primeFactors.filter (fun p => q < p)) k)) *
        ∏ p ∈ S.prodPrimes.primeFactors, (1 - S.nu p) := by
  simpa only [LinearSieve.sum_upperRosserBoundary_eq_sum_fixedDepthDensity] using
    mainSum_upperRosserWeight_le_boundaryChains hz hΔ hlocal hcut hs hslo

/-- The literal source sieve inherits the real-endpoint dimension-one estimate
from the Goldbach local-factor interval bound. -/
theorem exists_jurkatRichertSource_dimensionOneLocalProductBound :
    ∃ K : ℝ, 1 < K ∧ ∀ N : ℕ,
      HasDimensionOneLocalProductBound (jurkatRichertSourceBoundingSieve N) K := by
  obtain ⟨K, hK, hinterval⟩ :=
    MertensTheorem.exists_goldbach_inverse_interval_bound
  refine ⟨K, hK, ?_⟩
  intro N z₁ z₂ hz₁ hz₁₂
  let s : Finset ℕ :=
    (jurkatRichertSourceSiftingProduct N).primeFactors.filter
      (fun p : ℕ => z₁ ≤ (p : ℝ) ∧ (p : ℝ) < z₂)
  have hs : ∀ p ∈ s, p.Prime ∧ 2 < p := by
    intro p hp
    have hp' :
        p ∈ (jurkatRichertSourceSiftingProduct N).primeFactors ∧
          z₁ ≤ (p : ℝ) ∧ (p : ℝ) < z₂ := by
      simpa [s] using hp
    have hprime : p.Prime := Nat.prime_of_mem_primeFactors hp'.1
    have hpdiv : p ∣ jurkatRichertSourceSiftingProduct N :=
      (Nat.mem_primeFactors_of_ne_zero
        (jurkatRichertSourceSiftingProduct_ne_zero N)).mp hp'.1 |>.2
    exact ⟨hprime,
      (prime_dvd_jurkatRichertSourceSiftingProduct hprime).mp hpdiv |>.1⟩
  have hsinterval : ∀ p ∈ s, z₁ ≤ (p : ℝ) ∧ (p : ℝ) < z₂ := by
    intro p hp
    have hp' :
        p ∈ (jurkatRichertSourceSiftingProduct N).primeFactors ∧
          z₁ ≤ (p : ℝ) ∧ (p : ℝ) < z₂ := by
      simpa [s] using hp
    exact hp'.2
  have hbound := hinterval s hs z₁ z₂ hz₁ hz₁₂ hsinterval
  change (∏ p ∈ s, (1 - AnalyticNumberTheory.Sieve.goldbachNu p)⁻¹) ≤
    Real.log z₂ / Real.log z₁ * (1 + K / Real.log z₁)
  calc
    (∏ p ∈ s, (1 - AnalyticNumberTheory.Sieve.goldbachNu p)⁻¹) =
        ∏ p ∈ s, (1 - 1 / ((p : ℝ) - 1))⁻¹ := by
      apply Finset.prod_congr rfl
      intro p hp
      rw [AnalyticNumberTheory.Sieve.goldbachNu_apply_prime (hs p hp).1]
    _ ≤ Real.log z₂ / Real.log z₁ * (1 + K / Real.log z₁) := hbound

/-- Before the integer cutoff is taken, Chen's level and sifting powers have the
exact logarithmic ratio `5 - 10ε`. -/
theorem jurkatRichertSourceSieveRatio_eq {N : ℕ} {ε : ℝ} (hN : 1 < N) :
    Real.log ((N : ℝ) ^ (1 / 2 - ε)) /
        Real.log ((N : ℝ) ^ (1 / 10 : ℝ)) =
      5 - 10 * ε := by
  have hlog : Real.log (N : ℝ) ≠ 0 :=
    (Real.log_pos (by exact_mod_cast hN)).ne'
  rw [Real.log_rpow, Real.log_rpow]
  field_simp [hlog]
  ring
  all_goals exact_mod_cast (Nat.zero_lt_of_lt hN)

/-- The standard dimension-one lower linear-sieve factor on `4 ≤ s ≤ 6`.
It is the solution of `(s f(s))' = F(s - 1)` obtained from the preceding
upper-sieve branch. -/
noncomputable def dimensionOneLowerLinearSieveFactor (s : ℝ) : ℝ :=
  (2 * Real.exp Real.eulerMascheroniConstant / s) *
    (Real.log (s - 1) +
      ∫ u in (3 : ℝ)..s - 1, jurkatRichertInnerIntegral u / u)

/-- The generic lower factor at ratio five is exactly Chen's equation (26)
factor. -/
theorem dimensionOneLowerLinearSieveFactor_five :
    dimensionOneLowerLinearSieveFactor 5 =
      jurkatRichertBaseSieveFactor jurkatRichertJ := by
  unfold dimensionOneLowerLinearSieveFactor jurkatRichertBaseSieveFactor
    jurkatRichertJ
  norm_num

private lemma continuousOn_jurkatRichertInnerIntegral_three_five :
    ContinuousOn jurkatRichertInnerIntegral (Set.Icc (3 : ℝ) 5) := by
  let f : ℝ → ℝ := fun t => Real.log (t - 1) / t
  have hf : IntervalIntegrable f volume 2 4 := by
    apply ContinuousOn.intervalIntegrable
    apply ContinuousOn.div
    · apply ContinuousOn.log (continuousOn_id.sub continuousOn_const)
      intro t ht
      change t - 1 ≠ 0
      rw [Set.uIcc_of_le (by norm_num : (2 : ℝ) ≤ 4)] at ht
      linarith [ht.1]
    · exact continuousOn_id
    · intro t ht
      change t ≠ 0
      rw [Set.uIcc_of_le (by norm_num : (2 : ℝ) ≤ 4)] at ht
      linarith [ht.1]
  have hp : ContinuousOn (fun b => ∫ t in (2 : ℝ)..b, f t) (Set.Icc 2 4) := by
    have h := intervalIntegral.continuousOn_primitive_interval' (a := (2 : ℝ)) hf
      (by
        rw [Set.uIcc_of_le (by norm_num : (2 : ℝ) ≤ 4)]
        constructor <;> norm_num)
    simpa [Set.uIcc_of_le (by norm_num : (2 : ℝ) ≤ 4)] using h
  unfold jurkatRichertInnerIntegral
  change ContinuousOn (fun u => (∫ t in (2 : ℝ)..u - 1, f t)) (Set.Icc 3 5)
  apply hp.comp (continuousOn_id.sub continuousOn_const)
  intro u hu
  change 2 ≤ u - 1 ∧ u - 1 ≤ 4
  constructor <;> linarith [hu.1, hu.2]

/-- The standard lower linear-sieve factor is continuous at the ratio used in
Chen's base sieve. -/
theorem dimensionOneLowerLinearSieveFactor_continuousAt_five :
    ContinuousAt dimensionOneLowerLinearSieveFactor 5 := by
  have hinnerDiv : ContinuousOn
      (fun u : ℝ => jurkatRichertInnerIntegral u / u) (Set.Icc (3 : ℝ) 5) := by
    apply ContinuousOn.div continuousOn_jurkatRichertInnerIntegral_three_five
      continuousOn_id
    intro u hu
    change u ≠ 0
    linarith [hu.1]
  have hinnerInt : IntervalIntegrable
      (fun u : ℝ => jurkatRichertInnerIntegral u / u) volume 3 5 := by
    apply ContinuousOn.intervalIntegrable
    rw [Set.uIcc_of_le (by norm_num : (3 : ℝ) ≤ 5)]
    exact hinnerDiv
  have hprimitive : ContinuousOn
      (fun b : ℝ => ∫ u in (3 : ℝ)..b, jurkatRichertInnerIntegral u / u)
      (Set.Icc (3 : ℝ) 5) := by
    have h := intervalIntegral.continuousOn_primitive_interval' (a := (3 : ℝ))
      hinnerInt
      (by
        rw [Set.uIcc_of_le (by norm_num : (3 : ℝ) ≤ 5)]
        constructor <;> norm_num)
    simpa [Set.uIcc_of_le (by norm_num : (3 : ℝ) ≤ 5)] using h
  have houter : ContinuousOn
      (fun s : ℝ => ∫ u in (3 : ℝ)..s - 1, jurkatRichertInnerIntegral u / u)
      (Set.Icc (4 : ℝ) 6) := by
    apply hprimitive.comp (continuousOn_id.sub continuousOn_const)
    intro s hs
    change 3 ≤ s - 1 ∧ s - 1 ≤ 5
    constructor <;> linarith [hs.1, hs.2]
  have hlog : ContinuousOn (fun s : ℝ => Real.log (s - 1))
      (Set.Icc (4 : ℝ) 6) := by
    apply ContinuousOn.log (continuousOn_id.sub continuousOn_const)
    intro s hs
    change s - 1 ≠ 0
    linarith [hs.1]
  have hfactor : ContinuousOn dimensionOneLowerLinearSieveFactor
      (Set.Icc (4 : ℝ) 6) := by
    unfold dimensionOneLowerLinearSieveFactor
    apply (continuousOn_const.div continuousOn_id ?_).mul (hlog.add houter)
    intro s hs
    change s ≠ 0
    linarith [hs.1]
  exact hfactor.continuousAt (Icc_mem_nhds (by norm_num) (by norm_num))

/-- The generic dimension-one lower fundamental lemma for the explicit Rosser
coefficient.  For an arbitrary finite bounding sieve whose primes lie below
`z`, real level `Δ`, and ratio `s = log Δ / log z` near five, the density sum is
at least `(f(s) - ρ) V(S)`. -/
def DimensionOneLowerRosserDensityFundamentalLemma : Prop :=
  ∀ K ρ : ℝ, 1 < K → 0 < ρ →
    ∃ z₀ : ℝ, ∀ (S : BoundingSieve) (z Δ s : ℝ),
      z₀ ≤ z → 2 ≤ z → 0 < Δ →
      HasDimensionOneLocalProductBound S K →
      (∀ p ∈ S.prodPrimes.primeFactors, (p : ℝ) ≤ z) →
      s = Real.log Δ / Real.log z →
      4 ≤ s → s ≤ 6 →
      (dimensionOneLowerLinearSieveFactor s - ρ) *
          AnalyticNumberTheory.Sieve.sieveProductPrimeFactors S ≤
        S.mainSum
          (LinearSieve.lowerRosserWeight S.prodPrimes (Nat.floor Δ + 1))

/-- Compatibility form of the lower density lemma specialized to Chen's source
family.  It is derived below from the generic dimension-one theorem. -/
def ChenJurkatRichertBaseLowerRosserDensityFundamentalLemma : Prop :=
  ∀ K : ℝ, 1 < K →
    (∀ᶠ N : ℕ in Filter.atTop,
      HasDimensionOneLocalProductBound (jurkatRichertSourceBoundingSieve N) K) →
    ∀ δ : ℝ, 0 < δ →
      ∃ ε : ℝ, 0 < ε ∧ ε < 2 / 5 ∧
        ∀ᶠ N : ℕ in Filter.atTop,
          (jurkatRichertBaseSieveFactor jurkatRichertJ - δ) *
              AnalyticNumberTheory.Sieve.sieveProductPrimeFactors
                (jurkatRichertSourceBoundingSieve N) ≤
            (jurkatRichertSourceBoundingSieve N).mainSum
              (jurkatRichertBaseLowerRosserWeight N ε)

/-- The generic dimension-one lower fundamental lemma specializes to Chen's
source family.  Continuity at ratio five absorbs the displacement
`s = 5 - 10ε`, while the source local-product and prime-cutoff facts supply the
generic hypotheses. -/
theorem chenJurkatRichertBaseLowerRosserDensityFundamentalLemma_of_generic
    (hfund : DimensionOneLowerRosserDensityFundamentalLemma) :
    ChenJurkatRichertBaseLowerRosserDensityFundamentalLemma := by
  intro K hK hlocal δ hδ
  let ρ := δ / 2
  have hρ : 0 < ρ := half_pos hδ
  obtain ⟨z₀, hfundAt⟩ := hfund K ρ hK hρ
  have hnear :
      {s : ℝ |
        dimensionOneLowerLinearSieveFactor 5 - ρ <
          dimensionOneLowerLinearSieveFactor s} ∈ nhds 5 :=
    dimensionOneLowerLinearSieveFactor_continuousAt_five.eventually_mem
      (Ioi_mem_nhds (by linarith))
  rw [Metric.mem_nhds_iff] at hnear
  obtain ⟨r, hr, hrball⟩ := hnear
  let ε := min (r / 20) (1 / 20 : ℝ)
  have hε : 0 < ε := lt_min (div_pos hr (by norm_num)) (by norm_num)
  have hεTwoFifths : ε < 2 / 5 := by
    have hle := min_le_right (r / 20) (1 / 20 : ℝ)
    dsimp [ε]
    linarith
  have hεRadius : ε ≤ r / 20 := min_le_left _ _
  have hsNear :
      dimensionOneLowerLinearSieveFactor 5 - ρ <
        dimensionOneLowerLinearSieveFactor (5 - 10 * ε) := by
    apply hrball
    rw [Metric.mem_ball, Real.dist_eq]
    have habs : |(5 - 10 * ε) - 5| = 10 * ε := by
      rw [abs_of_nonpos (by linarith)]
      ring
    rw [habs]
    nlinarith
  have hsLower : 4 ≤ (5 - 10 * ε : ℝ) := by
    have hle := min_le_right (r / 20) (1 / 20 : ℝ)
    dsimp [ε]
    linarith
  have hsUpper : (5 - 10 * ε : ℝ) ≤ 6 := by linarith
  refine ⟨ε, hε, hεTwoFifths, ?_⟩
  have hPow :
      Filter.Tendsto (fun N : ℕ => (N : ℝ) ^ (1 / 10 : ℝ))
        Filter.atTop Filter.atTop :=
    (tendsto_rpow_atTop (by norm_num : 0 < (1 / 10 : ℝ))).comp
      tendsto_natCast_atTop_atTop
  have hCutoffLarge :
      ∀ᶠ N : ℕ in Filter.atTop, max z₀ 2 ≤ (N : ℝ) ^ (1 / 10 : ℝ) :=
    hPow.eventually (Filter.eventually_ge_atTop (max z₀ 2))
  filter_upwards [hlocal, hCutoffLarge, Filter.eventually_ge_atTop 2] with
      N hlocalN hcutoff hN
  have hNOne : 1 < N := by omega
  have hDelta : 0 < (N : ℝ) ^ (1 / 2 - ε) := by positivity
  have hPrime :
      ∀ p ∈ (jurkatRichertSourceBoundingSieve N).prodPrimes.primeFactors,
        (p : ℝ) ≤ (N : ℝ) ^ (1 / 10 : ℝ) := by
    intro p hp
    have hpPrime : p.Prime := Nat.prime_of_mem_primeFactors hp
    have hpDvd : p ∣ jurkatRichertSourceSiftingProduct N :=
      (Nat.mem_primeFactors_of_ne_zero
        (jurkatRichertSourceSiftingProduct_ne_zero N)).mp hp |>.2
    exact
      (prime_dvd_jurkatRichertSourceSiftingProduct hpPrime).mp hpDvd |>.2.1
  have hbound := hfundAt (jurkatRichertSourceBoundingSieve N)
    ((N : ℝ) ^ (1 / 10 : ℝ)) ((N : ℝ) ^ (1 / 2 - ε)) (5 - 10 * ε)
    (le_trans (le_max_left _ _) hcutoff)
    (le_trans (le_max_right _ _) hcutoff) hDelta hlocalN hPrime
    (jurkatRichertSourceSieveRatio_eq hNOne).symm hsLower hsUpper
  have hproduct :
      0 ≤ AnalyticNumberTheory.Sieve.sieveProductPrimeFactors
        (jurkatRichertSourceBoundingSieve N) := by
    unfold AnalyticNumberTheory.Sieve.sieveProductPrimeFactors
    apply Finset.prod_nonneg
    intro p hp
    exact sub_nonneg.mpr
      ((jurkatRichertSourceBoundingSieve N).nu_lt_one_of_prime p
        (Nat.prime_of_mem_primeFactors hp)
        ((Nat.mem_primeFactors_of_ne_zero
          (jurkatRichertSourceSiftingProduct_ne_zero N)).mp hp).2).le
  calc
    (jurkatRichertBaseSieveFactor jurkatRichertJ - δ) *
          AnalyticNumberTheory.Sieve.sieveProductPrimeFactors
            (jurkatRichertSourceBoundingSieve N) ≤
        (dimensionOneLowerLinearSieveFactor (5 - 10 * ε) - ρ) *
          AnalyticNumberTheory.Sieve.sieveProductPrimeFactors
            (jurkatRichertSourceBoundingSieve N) := by
      apply mul_le_mul_of_nonneg_right _ hproduct
      rw [← dimensionOneLowerLinearSieveFactor_five]
      dsimp [ρ] at *
      linarith
    _ ≤ _ := by
      change
        (dimensionOneLowerLinearSieveFactor (5 - 10 * ε) - ρ) *
              AnalyticNumberTheory.Sieve.sieveProductPrimeFactors
                (jurkatRichertSourceBoundingSieve N) ≤
          (jurkatRichertSourceBoundingSieve N).mainSum
            (LinearSieve.lowerRosserWeight
              (jurkatRichertSourceSiftingProduct N)
              (Nat.floor ((N : ℝ) ^ (1 / 2 - ε)) + 1))
      exact hbound

/-- The remaining standard source input is precisely the density-sum fundamental
lemma, since the local-product condition is now proved above. -/
def ChenJurkatRichertBaseLowerRosserStandardInput : Prop :=
  ChenJurkatRichertBaseLowerRosserDensityFundamentalLemma

/-- The source-faithful lower-sieve fundamental lemma at
`D = N^(1/2-ε)`.  It retains the exact finite Goldbach remainder rather than
folding distribution or Mertens normalization into the conclusion. -/
def ChenJurkatRichertBaseLowerSieveFundamentalLemma : Prop :=
  ∀ δ : ℝ, 0 < δ →
    ∃ ε : ℝ, 0 < ε ∧ ε < 1 / 2 ∧
      ∀ᶠ N : ℕ in Filter.atTop, Even N →
        (jurkatRichertBaseSieveFactor jurkatRichertJ - δ) *
              ((jurkatRichertSourceBoundingSieve N).totalMass *
                AnalyticNumberTheory.Sieve.sieveProductPrimeFactors
                  (jurkatRichertSourceBoundingSieve N)) -
            jurkatRichertSourceRemainderSum N ε ≤
          (jurkatRichertSourceBoundingSieve N).siftedSum

/-- The source Rosser coefficient is a finite lower-Möbius weight at its stated
level.  This is the combinatorial half of the fundamental lemma. -/
theorem jurkatRichertBaseLowerRosserWeight_certificate
    {N : ℕ} {ε : ℝ} (hN : 1 ≤ N) (hε : ε < 2 / 5) :
    LinearSieve.IsLowerRosserCertificate
      (jurkatRichertSourceSiftingProduct N)
      (jurkatRichertSourceLowerLevel N ε) := by
  apply LinearSieve.lowerRosserWeight_certificate
    (jurkatRichertSourceSiftingProduct_squarefree N)
    (jurkatRichertSourceSiftingProduct_ne_zero N)
  intro p hp
  have hpPrime : p.Prime := Nat.prime_of_mem_primeFactors hp
  have hpDvd : p ∣ jurkatRichertSourceSiftingProduct N :=
    (Nat.mem_primeFactors_of_ne_zero
      (jurkatRichertSourceSiftingProduct_ne_zero N)).mp hp |>.2
  have hpCutoff :=
    (prime_dvd_jurkatRichertSourceSiftingProduct hpPrime).mp hpDvd |>.2.1
  have hpow :
      (N : ℝ) ^ (1 / 10 : ℝ) ≤ (N : ℝ) ^ (1 / 2 - ε) := by
    apply Real.rpow_le_rpow_of_exponent_le
    · exact_mod_cast hN
    · linarith
  have hpFloor :
      p ≤ Nat.floor ((N : ℝ) ^ (1 / 2 - ε)) := by
    rw [Nat.le_floor_iff (Real.rpow_nonneg (Nat.cast_nonneg N) _)]
    exact hpCutoff.trans hpow
  unfold jurkatRichertSourceLowerLevel
  omega

/-- The Rosser error term is bounded by exactly the level-restricted Goldbach
remainder appearing in the source statement. -/
theorem jurkatRichertBaseLowerRosserError_le
    (N : ℕ) (ε : ℝ) :
    LinearSieve.lowerErrSum (jurkatRichertSourceBoundingSieve N)
        (jurkatRichertSourceLowerLevel N ε)
        (jurkatRichertBaseLowerRosserWeight N ε) ≤
      jurkatRichertSourceRemainderSum N ε := by
  have hfilter :
      (jurkatRichertSourceSiftingProduct N).divisors.filter
          (fun d => d < jurkatRichertSourceLowerLevel N ε) =
        (jurkatRichertSourceSiftingProduct N).divisors.filter
          (fun d : ℕ => (d : ℝ) ≤ (N : ℝ) ^ (1 / 2 - ε)) := by
    ext d
    simp only [Finset.mem_filter]
    unfold jurkatRichertSourceLowerLevel
    rw [Nat.lt_succ_iff, Nat.le_floor_iff
      (Real.rpow_nonneg (Nat.cast_nonneg N) _)]
  unfold LinearSieve.lowerErrSum jurkatRichertSourceRemainderSum
  change
    (∑ d ∈ (jurkatRichertSourceSiftingProduct N).divisors.filter
        (fun d => d < jurkatRichertSourceLowerLevel N ε),
      |jurkatRichertBaseLowerRosserWeight N ε d| *
        |(jurkatRichertSourceBoundingSieve N).rem d|) ≤
      ∑ d ∈ (jurkatRichertSourceSiftingProduct N).divisors.filter
        (fun d : ℕ => (d : ℝ) ≤ (N : ℝ) ^ (1 / 2 - ε)),
        |(jurkatRichertSourceBoundingSieve N).rem d|
  rw [hfilter]
  apply Finset.sum_le_sum
  intro d hd
  have hbnd :=
    LinearSieve.abs_lowerRosserWeight_le_one
      (jurkatRichertSourceSiftingProduct N)
      (jurkatRichertSourceLowerLevel N ε) d
  simpa [jurkatRichertBaseLowerRosserWeight] using
    mul_le_mul_of_nonneg_right hbnd
      (abs_nonneg ((jurkatRichertSourceBoundingSieve N).rem d))

/-- The standard density-sum fundamental lemma, together with the fully finite
Rosser expansion above, proves Chen's base lower-sieve statement. -/
theorem chenJurkatRichertBaseLowerSieveFundamentalLemma_of_density
    (hinput : ChenJurkatRichertBaseLowerRosserStandardInput) :
    ChenJurkatRichertBaseLowerSieveFundamentalLemma := by
  obtain ⟨K, hK, hdimension⟩ :=
    exists_jurkatRichertSource_dimensionOneLocalProductBound
  intro δ hδ
  rcases hinput K hK (Filter.Eventually.of_forall hdimension) δ hδ with
    ⟨ε, hε, hεTwoFifths, hdensity⟩
  refine ⟨ε, hε, by linarith, ?_⟩
  filter_upwards [hdensity, Filter.eventually_ge_atTop 2] with N hdensityN hN
  intro _hEven
  let S := jurkatRichertSourceBoundingSieve N
  let D := jurkatRichertSourceLowerLevel N ε
  let mu := jurkatRichertBaseLowerRosserWeight N ε
  have hcert : LinearSieve.IsLowerRosserCertificate
      (jurkatRichertSourceSiftingProduct N) D := by
    simpa [D] using
      jurkatRichertBaseLowerRosserWeight_certificate (by omega) hεTwoFifths
  have hfinite :
      S.totalMass * S.mainSum mu - LinearSieve.lowerErrSum S D mu ≤
        S.siftedSum := by
    exact LinearSieve.mainSum_sub_lowerErrSum_le_siftedSum D mu hcert
      (LinearSieve.lowerRosserWeight_hasLowerLevelSupport
        (jurkatRichertSourceSiftingProduct N) D)
  have hmass : 0 ≤ S.totalMass := by
    dsimp [S, jurkatRichertSourceBoundingSieve]
    exact LiuWeight.liuLogarithmicIntegral_nonneg
      (2 / Real.log 2) (by positivity) (by exact_mod_cast hN)
  have hmain :
      S.totalMass *
          ((jurkatRichertBaseSieveFactor jurkatRichertJ - δ) *
            AnalyticNumberTheory.Sieve.sieveProductPrimeFactors S) ≤
        S.totalMass * S.mainSum mu :=
    mul_le_mul_of_nonneg_left (by simpa [S, mu] using hdensityN) hmass
  have herr :
      LinearSieve.lowerErrSum S D mu ≤
        jurkatRichertSourceRemainderSum N ε := by
    simpa [S, D, mu] using jurkatRichertBaseLowerRosserError_le N ε
  calc
    (jurkatRichertBaseSieveFactor jurkatRichertJ - δ) *
            (S.totalMass *
             AnalyticNumberTheory.Sieve.sieveProductPrimeFactors S) -
          jurkatRichertSourceRemainderSum N ε ≤
        S.totalMass * S.mainSum mu - LinearSieve.lowerErrSum S D mu := by
      nlinarith
    _ ≤ S.siftedSum := hfinite

/-- The Goldbach AP distribution input required by the base lower sieve:
the exact squarefree remainder sum through `N^(1/2-ε)` is negligible on the
`𝔖(N) N / log² N` scale. -/
def ChenJurkatRichertBaseGoldbachDistribution : Prop :=
  ∀ ε : ℝ, 0 < ε → ε < 1 / 2 → ∀ δ : ℝ, 0 < δ →
    ∀ᶠ N : ℕ in Filter.atTop, Even N →
      jurkatRichertSourceRemainderSum N ε ≤
        δ * SingularSeries.liuSingularSeries N * (N : ℝ) /
          Real.log N ^ (2 : ℕ)

/-- The standard Bombieri--Vinogradov literature interface supplies precisely
the base Goldbach distribution estimate needed by the source lower sieve.  The
proof retains the finite source support, reduces its moduli to canonical
reduced residues, and absorbs the exceptional cutoff-prime fibres by their
unconditional power-saving endpoint bound. -/
theorem chenJurkatRichertBaseGoldbachDistribution_of_standardBV
    (hBV : BombieriVinogradov.StandardBombieriVinogradov) :
    ChenJurkatRichertBaseGoldbachDistribution := by
  intro ε hε hεHalf δ hδ
  rcases BombieriVinogradov.endpoint_bound hBV 3 (by norm_num) with
    ⟨B, hB, C, hC, hBV⟩
  let U := SingularSeries.liuUniversalProduct
  have hU : 0 < U := by
    simpa [U] using SingularSeries.liuUniversalProduct_pos
  let cerr := 4 * C / (δ * U)
  obtain ⟨N₀, hcerr⟩ := errLogCube_negligible cerr
  have hcut :=
    LiuWeight.eventually_liuSourceDEpsilon_le_panModulusCutoff ε B hε hB
  have hendpoint :=
    eventually_jurkatRichertSource_exceptional_endpoint_small ε (δ / 2)
      hε (by linarith)
  filter_upwards [hBV, hcut, hendpoint,
      Filter.eventually_ge_atTop (max N₀ 3)] with N hBVN hcutN hendpointN hN
  intro hEven
  have hN₂ : 2 ≤ N := by omega
  have hNgt : 2 < N := by omega
  let D := (jurkatRichertSourceSiftingProduct N).divisors.filter
    (fun d : ℕ => (d : ℝ) ≤ (N : ℝ) ^ (1 / 2 - ε))
  let E := jurkatRichertSourceExceptionalPrimes N
  let Q := Finset.Icc 1 (LiuWeight.panModulusCutoff N B)
  have hDsub : D ⊆ Q := by
    intro d hd
    rcases Finset.mem_filter.mp hd with ⟨hdDiv, hdLevel⟩
    have hdvd : d ∣ jurkatRichertSourceSiftingProduct N :=
      Nat.dvd_of_mem_divisors hdDiv
    have hd0 : d ≠ 0 := by
      intro hd0
      subst d
      have hP0 : jurkatRichertSourceSiftingProduct N = 0 := by simpa using hdvd
      exact jurkatRichertSourceSiftingProduct_ne_zero N hP0
    rw [Finset.mem_Icc]
    constructor
    · exact Nat.one_le_iff_ne_zero.mpr hd0
    · have hdFloor : d ≤ LiuWeight.liuSourceDEpsilon N ε := by
        exact Nat.le_floor hdLevel
      exact hdFloor.trans hcutN
  have hmaxSum :
      (∑ d ∈ D, BombieriVinogradov.standardPrimeAPMaxError N d) ≤
        ∑ q ∈ Q, BombieriVinogradov.standardPrimeAPMaxError N q :=
    Finset.sum_le_sum_of_subset_of_nonneg hDsub
      (fun q _ _ => BombieriVinogradov.standardPrimeAPMaxError_nonneg N q)
  have hBVsum :
      (∑ q ∈ Q, BombieriVinogradov.standardPrimeAPMaxError N q) ≤
        C * (N : ℝ) / Real.log N ^ (3 : ℕ) := by
    simpa [Q, Real.rpow_natCast] using hBVN hN₂
  have hN₀ : N₀ ≤ N := le_trans (le_max_left _ _) hN
  have hcerrN := hcerr N hN₀ hEven
  have hlog : 0 < Real.log (N : ℝ) :=
    Real.log_pos (by exact_mod_cast (show 1 < N by omega))
  have hδU : 0 < δ * U := mul_pos hδ hU
  have hBVtiny :
      C * (N : ℝ) / Real.log N ^ (3 : ℕ) ≤
        (δ * U / 16) * (N : ℝ) / Real.log N ^ (2 : ℕ) := by
    have hscaled := mul_le_mul_of_nonneg_left hcerrN
      (show 0 ≤ δ * U / 4 by positivity)
    calc
      C * (N : ℝ) / Real.log N ^ (3 : ℕ) =
          (δ * U / 4) *
            (cerr * (N : ℝ) / Real.log N ^ (3 : ℕ)) := by
        dsimp [cerr]
        field_simp [hδU.ne']
      _ ≤ (δ * U / 4) *
          ((1 / 4 : ℝ) * (N : ℝ) / Real.log N ^ (2 : ℕ)) := hscaled
      _ = (δ * U / 16) * (N : ℝ) / Real.log N ^ (2 : ℕ) := by ring
  have hscale : 0 ≤ (N : ℝ) / Real.log N ^ (2 : ℕ) :=
    div_nonneg (Nat.cast_nonneg N) (sq_nonneg _)
  have hUle : U ≤ SingularSeries.liuSingularSeries N := by
    simpa [U] using SingularSeries.liuUniversalProduct_le_liuSingularSeries N
  have hcoeff :
      δ * U / 16 ≤ δ / 2 * SingularSeries.liuSingularSeries N := by
    calc
      δ * U / 16 = (δ / 16) * U := by ring
      _ ≤ (δ / 16) * SingularSeries.liuSingularSeries N :=
        mul_le_mul_of_nonneg_left hUle (by positivity)
      _ ≤ (δ / 2) * SingularSeries.liuSingularSeries N :=
        mul_le_mul_of_nonneg_right (by linarith) (SingularSeries.liuSingularSeries_pos N).le
  have hBVsmall :
      (∑ d ∈ D, BombieriVinogradov.standardPrimeAPMaxError N d) ≤
        (δ / 2) * SingularSeries.liuSingularSeries N * (N : ℝ) /
          Real.log N ^ (2 : ℕ) := by
    calc
      (∑ d ∈ D, BombieriVinogradov.standardPrimeAPMaxError N d) ≤
          ∑ q ∈ Q, BombieriVinogradov.standardPrimeAPMaxError N q := hmaxSum
      _ ≤ C * (N : ℝ) / Real.log N ^ (3 : ℕ) := hBVsum
      _ ≤ (δ * U / 16) * (N : ℝ) / Real.log N ^ (2 : ℕ) := hBVtiny
      _ ≤ (δ / 2) * SingularSeries.liuSingularSeries N * (N : ℝ) /
          Real.log N ^ (2 : ℕ) := by
        simpa [mul_div_assoc] using mul_le_mul_of_nonneg_right hcoeff hscale
  have hEndpoint :
      (D.card : ℝ) * E.card ≤
        (δ / 2) * SingularSeries.liuSingularSeries N * (N : ℝ) /
          Real.log N ^ (2 : ℕ) := by
    calc
      (D.card : ℝ) * E.card ≤
          2 * (N : ℝ) ^ (1 / 2 - ε) * Real.log N / Real.log 2 := by
        simpa [D, E] using
          jurkatRichertSource_exceptional_endpoint_le N ε hN₂ hε hεHalf
      _ ≤ (δ / 2) * U * (N : ℝ) / Real.log N ^ (2 : ℕ) := hendpointN
      _ ≤ (δ / 2) * SingularSeries.liuSingularSeries N * (N : ℝ) /
          Real.log N ^ (2 : ℕ) := by
        have hhalfU :
            (δ / 2) * U ≤ (δ / 2) * SingularSeries.liuSingularSeries N :=
          mul_le_mul_of_nonneg_left hUle (by positivity)
        simpa [mul_div_assoc] using mul_le_mul_of_nonneg_right hhalfU hscale
  have hreduction :=
    jurkatRichertSourceRemainderSum_le_standardMax_add_exceptional N ε hEven hNgt
  change jurkatRichertSourceRemainderSum N ε ≤ _
  calc
    jurkatRichertSourceRemainderSum N ε ≤
        (∑ d ∈ D, BombieriVinogradov.standardPrimeAPMaxError N d) +
          (D.card : ℝ) * E.card := by
      simpa [D, E] using hreduction
    _ ≤ (δ / 2) * SingularSeries.liuSingularSeries N * (N : ℝ) /
          Real.log N ^ (2 : ℕ) +
        ((δ / 2) * SingularSeries.liuSingularSeries N * (N : ℝ) /
          Real.log N ^ (2 : ℕ)) :=
      add_le_add hBVsmall hEndpoint
    _ = δ * SingularSeries.liuSingularSeries N * (N : ℝ) /
          Real.log N ^ (2 : ℕ) := by ring

/-- Chen equation (25), in the one-sided form needed here: the source
Goldbach main term has normalization `20 exp(-γ) 𝔖(N) N / log² N`. -/
def ChenJurkatRichertBaseMertensNormalization : Prop :=
  ∀ δ : ℝ, 0 < δ →
    ∀ᶠ N : ℕ in Filter.atTop, Even N →
      (jurkatRichertMertensFactor - δ) *
            SingularSeries.liuSingularSeries N * (N : ℝ) /
              Real.log N ^ (2 : ℕ) ≤
        (jurkatRichertSourceBoundingSieve N).totalMass *
          AnalyticNumberTheory.Sieve.sieveProductPrimeFactors
            (jurkatRichertSourceBoundingSieve N)

/-- The literal source cutoff has logarithmic scale `1/10`. -/
theorem tendsto_log_jurkatRichertSourceZ_sub_one_div_log :
    Filter.Tendsto (fun N : ℕ =>
      Real.log ((jurkatRichertSourceZ N - 1 : ℕ) : ℝ) / Real.log (N : ℝ))
      Filter.atTop (nhds (1 / 10 : ℝ)) := by
  simpa [jurkatRichertSourceZ] using
    (LiuWeight.tendsto_log_floor_rpow_div_log (1 / 10 : ℝ) (by norm_num))

/-- Eventually the source cutoff is one past the corrected cutoff. -/
private theorem eventually_jurkatRichertSourceZ_sub_one_eq_correctedChenZ :
    ∀ᶠ N : ℕ in Filter.atTop,
      jurkatRichertSourceZ N - 1 = correctedChenZ N := by
  filter_upwards [Filter.eventually_ge_atTop (3 ^ 10)] with N hN
  have hz : 2 ≤ correctedChenZ N - 1 :=
    correctedChenZ_sub_one_ge_of_N_ge (k := 2) (by norm_num) (by simpa using hN)
  have hf : 2 ≤ Nat.floor ((N : ℝ) ^ (1 / 10 : ℝ)) := by
    unfold correctedChenZ at hz
    omega
  unfold jurkatRichertSourceZ correctedChenZ
  rw [max_eq_right hf]
  omega

private theorem tendsto_jurkatRichertSourceZ_sub_one_atTop :
    Filter.Tendsto (fun N : ℕ => jurkatRichertSourceZ N - 1)
      Filter.atTop Filter.atTop := by
  apply Filter.tendsto_atTop.2
  intro b
  filter_upwards [eventually_jurkatRichertSourceZ_sub_one_eq_correctedChenZ,
      tendsto_correctedChenZ_sub_one_atTop.eventually
        (Filter.eventually_ge_atTop b)] with N heq hN
  rw [heq]
  omega

/-- Adjoining one cutoff point loses at most its universal local factor. -/
private theorem singularSeriesTruncated_one_step_lower (N m : ℕ) (hm : 3 ≤ m) :
    (1 - 1 / ((m : ℝ) - 1) ^ 2) *
        SingularSeries.singularSeriesTruncated N (m - 1) ≤
      SingularSeries.singularSeriesTruncated N m := by
  unfold SingularSeries.singularSeriesTruncated
  rw [Nat.sub_add_cancel (by omega : 1 ≤ m)]
  simp only [Finset.prod_filter, Finset.prod_range_succ]
  have hprod : 0 ≤ ∏ x ∈ Finset.range m,
      if x.Prime then SingularSeries.localFactor x N else 1 := by
    apply Finset.prod_nonneg
    intro p hp
    split_ifs with hprime
    · exact (SingularSeries.localFactor_pos hprime).le
    · norm_num
  have hfactor : 1 - 1 / ((m : ℝ) - 1) ^ 2 ≤
      if m.Prime then SingularSeries.localFactor m N else 1 := by
    have hmR : (3 : ℝ) ≤ m := by exact_mod_cast hm
    have hm1 : (0 : ℝ) < (m : ℝ) - 1 := by linarith
    by_cases hp : m.Prime
    · simp only [hp, if_true]
      by_cases hpdvd : m ∣ N
      · rw [SingularSeries.localFactor_of_dvd hp (by omega) hpdvd]
        field_simp [hm1.ne']
        nlinarith [show (0 : ℝ) ≤ m by positivity]
      · rw [SingularSeries.localFactor_of_not_dvd hp (by omega) hpdvd]
        field_simp [hm1.ne']
        ring_nf
        rfl
    · simp only [hp, if_false]
      have : 0 ≤ 1 / ((m : ℝ) - 1) ^ 2 := by positivity
      linarith
  calc
    (1 - 1 / ((m : ℝ) - 1) ^ 2) *
          (∏ x ∈ Finset.range m,
            if x.Prime then SingularSeries.localFactor x N else 1) =
        (∏ x ∈ Finset.range m,
            if x.Prime then SingularSeries.localFactor x N else 1) *
          (1 - 1 / ((m : ℝ) - 1) ^ 2) := by ring
    _ ≤ (∏ x ∈ Finset.range m,
            if x.Prime then SingularSeries.localFactor x N else 1) *
          (if m.Prime then SingularSeries.localFactor m N else 1) :=
      mul_le_mul_of_nonneg_left hfactor hprod

private theorem tendsto_source_cutoff_one_step_factor :
    Filter.Tendsto (fun N : ℕ =>
      1 - 1 / ((correctedChenZ N - 1 : ℕ) : ℝ) ^ 2)
      Filter.atTop (nhds 1) := by
  have hz : Filter.Tendsto
      (fun N : ℕ => ((correctedChenZ N - 1 : ℕ) : ℝ))
      Filter.atTop Filter.atTop :=
    tendsto_natCast_atTop_atTop.comp tendsto_correctedChenZ_sub_one_atTop
  have hinv : Filter.Tendsto
      (fun N : ℕ => (((correctedChenZ N - 1 : ℕ) : ℝ))⁻¹)
      Filter.atTop (nhds 0) :=
    tendsto_inv_atTop_zero.comp hz
  have hone : Filter.Tendsto (fun _ : ℕ => (1 : ℝ))
      Filter.atTop (nhds 1) := tendsto_const_nhds
  simpa [one_div, inv_pow] using hone.sub (hinv.pow 2)

/-- Uniform varying-`N` comparison at Chen's literal source cutoff. -/
theorem eventually_two_mul_liuSingularSeries_le_source_truncated
    (η : ℝ) (hη : 0 < η) :
    ∀ᶠ N : ℕ in Filter.atTop, Even N →
      2 * SingularSeries.liuSingularSeries N ≤
        (1 + η) * AnalyticNumberTheory.Sieve.singularSeriesTruncated N
          (jurkatRichertSourceZ N - 1) := by
  have hold :=
    eventually_two_mul_liuSingularSeries_le_truncated (η / 2) (by positivity)
  have hthreshold : (1 + η / 2) / (1 + η) < (1 : ℝ) := by
    rw [div_lt_one (by linarith)]
    linarith
  have hfactor :=
    tendsto_source_cutoff_one_step_factor.eventually
      (Ici_mem_nhds hthreshold)
  filter_upwards [hold, hfactor,
      eventually_jurkatRichertSourceZ_sub_one_eq_correctedChenZ,
      Filter.eventually_ge_atTop (3 ^ 10)] with N holdN hfactorN heq hN
  intro hEven
  let a : ℝ := 1 - 1 / ((correctedChenZ N - 1 : ℕ) : ℝ) ^ 2
  have ha : (1 + η / 2) / (1 + η) ≤ a := by
    simpa [a] using hfactorN
  have ha_pos : 0 < a := lt_of_lt_of_le (by positivity) ha
  have hcoef : 1 + η / 2 ≤ a * (1 + η) := by
    rw [div_le_iff₀ (by linarith : 0 < 1 + η)] at ha
    nlinarith
  have hm : 3 ≤ correctedChenZ N := by
    have := correctedChenZ_sub_one_ge_of_N_ge (k := 2) (by norm_num)
      (show (2 + 1) ^ 10 ≤ N by simpa using hN)
    omega
  have hstep := singularSeriesTruncated_one_step_lower N (correctedChenZ N) hm
  have hstep' :
      a * SingularSeries.singularSeriesTruncated N (correctedChenZ N - 1) ≤
        SingularSeries.singularSeriesTruncated N (correctedChenZ N) := by
    dsimp [a]
    convert hstep using 1
    rw [Nat.cast_sub (by omega : 1 ≤ correctedChenZ N)]
    norm_num
  have holdN' : 2 * SingularSeries.liuSingularSeries N ≤
      (1 + η / 2) * SingularSeries.singularSeriesTruncated N
        (correctedChenZ N - 1) := by
    simpa only [singularSeriesTruncated_eq_ant] using holdN hEven
  have htruncpos :
      0 < SingularSeries.singularSeriesTruncated N (correctedChenZ N) :=
    SingularSeries.singularSeriesTruncated_pos N _ (by omega)
  apply le_of_mul_le_mul_left _ ha_pos
  calc
    a * (2 * SingularSeries.liuSingularSeries N) ≤
        a * ((1 + η / 2) *
          SingularSeries.singularSeriesTruncated N
            (correctedChenZ N - 1)) :=
      mul_le_mul_of_nonneg_left holdN' ha_pos.le
    _ = (1 + η / 2) *
          (a * SingularSeries.singularSeriesTruncated N
            (correctedChenZ N - 1)) := by ring
    _ ≤ (1 + η / 2) *
          SingularSeries.singularSeriesTruncated N (correctedChenZ N) :=
      mul_le_mul_of_nonneg_left hstep' (by linarith)
    _ ≤ (a * (1 + η)) *
          SingularSeries.singularSeriesTruncated N (correctedChenZ N) :=
      mul_le_mul_of_nonneg_right hcoef htruncpos.le
    _ = a * ((1 + η) *
          AnalyticNumberTheory.Sieve.singularSeriesTruncated N
            (jurkatRichertSourceZ N - 1)) := by
      rw [heq, ← singularSeriesTruncated_eq_ant]
      ring

private theorem tendsto_jurkatRichertMertensCoefficient (C : ℝ) :
    Filter.Tendsto (fun N : ℕ =>
      Real.log (N : ℝ) *
        (Real.exp (-Real.eulerMascheroniConstant) /
            Real.log ((jurkatRichertSourceZ N - 1 : ℕ) : ℝ) -
          C / Real.log ((jurkatRichertSourceZ N - 1 : ℕ) : ℝ) ^ 2))
      Filter.atTop
      (nhds (10 * Real.exp (-Real.eulerMascheroniConstant))) := by
  have hqinv := tendsto_log_jurkatRichertSourceZ_sub_one_div_log.inv₀
    (by norm_num : (1 / 10 : ℝ) ≠ 0)
  have hmR : Filter.Tendsto
      (fun N : ℕ => ((jurkatRichertSourceZ N - 1 : ℕ) : ℝ))
      Filter.atTop Filter.atTop :=
    tendsto_natCast_atTop_atTop.comp tendsto_jurkatRichertSourceZ_sub_one_atTop
  have hlogm : Filter.Tendsto
      (fun N : ℕ => Real.log ((jurkatRichertSourceZ N - 1 : ℕ) : ℝ))
      Filter.atTop Filter.atTop :=
    Real.tendsto_log_atTop.comp hmR
  have hloginv : Filter.Tendsto
      (fun N : ℕ => (Real.log ((jurkatRichertSourceZ N - 1 : ℕ) : ℝ))⁻¹)
      Filter.atTop (nhds 0) :=
    tendsto_inv_atTop_zero.comp hlogm
  have hE : Filter.Tendsto
      (fun _ : ℕ => Real.exp (-Real.eulerMascheroniConstant))
      Filter.atTop (nhds (Real.exp (-Real.eulerMascheroniConstant))) :=
    tendsto_const_nhds
  have hC : Filter.Tendsto (fun _ : ℕ => C) Filter.atTop (nhds C) :=
    tendsto_const_nhds
  have hmain := (hE.mul hqinv).sub ((hC.mul hqinv).mul hloginv)
  have hmain' : Filter.Tendsto (fun N : ℕ =>
      Real.exp (-Real.eulerMascheroniConstant) *
          (Real.log ((jurkatRichertSourceZ N - 1 : ℕ) : ℝ) /
            Real.log (N : ℝ))⁻¹ -
        (C * (Real.log ((jurkatRichertSourceZ N - 1 : ℕ) : ℝ) /
            Real.log (N : ℝ))⁻¹) *
          (Real.log ((jurkatRichertSourceZ N - 1 : ℕ) : ℝ))⁻¹)
      Filter.atTop
      (nhds (10 * Real.exp (-Real.eulerMascheroniConstant))) := by
    convert hmain using 1
    norm_num
    ring
  apply hmain'.congr'
  filter_upwards [eventually_jurkatRichertSourceZ_sub_one_eq_correctedChenZ,
      Filter.eventually_ge_atTop (3 ^ 10)] with N heq hN
  have hNpos : 0 < Real.log (N : ℝ) :=
    Real.log_pos (by exact_mod_cast (by omega : 1 < N))
  have hc := correctedChenZ_sub_one_ge_of_N_ge (k := 2) (by norm_num)
    (show (2 + 1) ^ 10 ≤ N by simpa using hN)
  have hm : 3 ≤ jurkatRichertSourceZ N - 1 := by
    rw [heq]
    omega
  have hmlog :
      0 < Real.log ((jurkatRichertSourceZ N - 1 : ℕ) : ℝ) :=
    Real.log_pos
      (by exact_mod_cast (by omega : 1 < jurkatRichertSourceZ N - 1))
  field_simp [hNpos.ne', hmlog.ne']

/-- Mertens' product theorem at the literal source cutoff, uniformly in `N`. -/
theorem eventually_jurkatRichertSourceGoldbachSieveProduct_lower
    (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ N : ℕ in Filter.atTop, Even N →
      (10 * Real.exp (-Real.eulerMascheroniConstant) - ε) *
          AnalyticNumberTheory.Sieve.singularSeriesTruncated N
            (jurkatRichertSourceZ N - 1) / Real.log (N : ℝ) ≤
        MertensTheorem.goldbachSieveProduct N (jurkatRichertSourceZ N) := by
  obtain ⟨C, hC⟩ := MertensTheorem.sieve_product_asymptotic
  have hcoef := (tendsto_jurkatRichertMertensCoefficient C).eventually
    (Ici_mem_nhds (by linarith :
      10 * Real.exp (-Real.eulerMascheroniConstant) - ε <
        10 * Real.exp (-Real.eulerMascheroniConstant)))
  filter_upwards [hcoef,
      eventually_jurkatRichertSourceZ_sub_one_eq_correctedChenZ,
      Filter.eventually_ge_atTop (3 ^ 10)] with N hcoefN heq hN
  intro hEven
  have hN4 : 4 ≤ N := by omega
  have hz3 : 3 ≤ jurkatRichertSourceZ N := by
    have hc := correctedChenZ_sub_one_ge_of_N_ge (k := 2) (by norm_num)
      (show (2 + 1) ^ 10 ≤ N by simpa using hN)
    have hc3 : 3 ≤ correctedChenZ N := by omega
    have hs3 : 3 ≤ jurkatRichertSourceZ N - 1 := by
      rw [heq]
      exact hc3
    omega
  have hlogN : 0 < Real.log (N : ℝ) :=
    Real.log_pos (by exact_mod_cast (by omega : 1 < N))
  have htruncpos : 0 < SingularSeries.singularSeriesTruncated N
      (jurkatRichertSourceZ N - 1) :=
    SingularSeries.singularSeriesTruncated_pos N _ (by omega)
  have hasym := hC N (jurkatRichertSourceZ N) hz3 hEven hN4
  have hlower := (abs_le.mp hasym).1
  have hproduct :
      SingularSeries.singularSeriesTruncated N (jurkatRichertSourceZ N - 1) *
          Real.exp (-Real.eulerMascheroniConstant) /
            Real.log ((jurkatRichertSourceZ N - 1 : ℕ) : ℝ) -
        C * SingularSeries.singularSeriesTruncated N
            (jurkatRichertSourceZ N - 1) /
          Real.log ((jurkatRichertSourceZ N - 1 : ℕ) : ℝ) ^ 2 ≤
        MertensTheorem.goldbachSieveProduct N (jurkatRichertSourceZ N) := by
    linarith
  have hcoeffdiv :
      (10 * Real.exp (-Real.eulerMascheroniConstant) - ε) /
          Real.log (N : ℝ) ≤
        Real.exp (-Real.eulerMascheroniConstant) /
            Real.log ((jurkatRichertSourceZ N - 1 : ℕ) : ℝ) -
          C / Real.log ((jurkatRichertSourceZ N - 1 : ℕ) : ℝ) ^ 2 := by
    rw [div_le_iff₀ hlogN]
    nlinarith
  calc
    (10 * Real.exp (-Real.eulerMascheroniConstant) - ε) *
          AnalyticNumberTheory.Sieve.singularSeriesTruncated N
            (jurkatRichertSourceZ N - 1) / Real.log (N : ℝ) =
        ((10 * Real.exp (-Real.eulerMascheroniConstant) - ε) /
          Real.log (N : ℝ)) *
          SingularSeries.singularSeriesTruncated N
            (jurkatRichertSourceZ N - 1) := by
      rw [singularSeriesTruncated_eq_ant]
      ring
    _ ≤ (Real.exp (-Real.eulerMascheroniConstant) /
            Real.log ((jurkatRichertSourceZ N - 1 : ℕ) : ℝ) -
          C / Real.log ((jurkatRichertSourceZ N - 1 : ℕ) : ℝ) ^ 2) *
          SingularSeries.singularSeriesTruncated N
            (jurkatRichertSourceZ N - 1) :=
      mul_le_mul_of_nonneg_right hcoeffdiv htruncpos.le
    _ ≤ MertensTheorem.goldbachSieveProduct N (jurkatRichertSourceZ N) := by
      convert hproduct using 1
      ring

/-- Chen's equation (25) follows from the exact Goldbach product identity,
Mertens' product theorem, and the uniform source-cutoff singular-series bridge. -/
theorem chenJurkatRichertBaseMertensNormalization :
    ChenJurkatRichertBaseMertensNormalization := by
  intro δ hδ
  let B := jurkatRichertMertensFactor
  have hB : 0 < B := by
    simpa [B] using jurkatRichertMertensFactor_pos
  let δ' := min δ (B / 2)
  have hδ' : 0 < δ' := lt_min hδ (half_pos hB)
  have hδ'δ : δ' ≤ δ := min_le_left _ _
  have hδ'B : δ' ≤ B / 2 := min_le_right _ _
  let η := δ' / (2 * B)
  let ε := δ' / 8
  have hη : 0 < η := div_pos hδ' (by positivity)
  have hε : 0 < ε := by positivity
  have hseries :=
    eventually_two_mul_liuSingularSeries_le_source_truncated η hη
  have hmertens :=
    eventually_jurkatRichertSourceGoldbachSieveProduct_lower ε hε
  filter_upwards [hseries, hmertens,
      eventually_jurkatRichertSourceZ_sub_one_eq_correctedChenZ,
      Filter.eventually_ge_atTop (3 ^ 10)] with N hseriesN hmertensN heq hN
  intro hEven
  have hlogN : 0 < Real.log (N : ℝ) :=
    Real.log_pos (by exact_mod_cast (by omega : 1 < N))
  let S := SingularSeries.liuSingularSeries N
  let T := AnalyticNumberTheory.Sieve.singularSeriesTruncated N
    (jurkatRichertSourceZ N - 1)
  have hS : 0 < S := by
    simpa [S] using SingularSeries.liuSingularSeries_pos N
  have hT : 0 < T := by
    dsimp [T]
    rw [← singularSeriesTruncated_eq_ant]
    apply SingularSeries.singularSeriesTruncated_pos N _
    have hc := correctedChenZ_sub_one_ge_of_N_ge (k := 2) (by norm_num)
      (show (2 + 1) ^ 10 ≤ N by simpa using hN)
    rw [heq]
    omega
  have hseriesN' : 2 * S ≤ (1 + η) * T := by
    simpa [S, T] using hseriesN hEven
  have hBdef : B = 20 * Real.exp (-Real.eulerMascheroniConstant) := by
    rfl
  have hBminus : 0 ≤ B - δ' := by nlinarith
  have hcoef :
      (B - δ') * (1 + η) / 2 ≤
        10 * Real.exp (-Real.eulerMascheroniConstant) - ε := by
    dsimp [η, ε]
    rw [hBdef]
    field_simp [hB.ne']
    nlinarith [sq_nonneg δ']
  have hseriesScaled :
      (B - δ) * S ≤
        (10 * Real.exp (-Real.eulerMascheroniConstant) - ε) * T := by
    calc
      (B - δ) * S ≤ (B - δ') * S :=
        mul_le_mul_of_nonneg_right (by linarith) hS.le
      _ = ((B - δ') / 2) * (2 * S) := by ring
      _ ≤ ((B - δ') / 2) * ((1 + η) * T) :=
        mul_le_mul_of_nonneg_left hseriesN'
          (div_nonneg hBminus (by norm_num))
      _ = ((B - δ') * (1 + η) / 2) * T := by ring
      _ ≤ (10 * Real.exp (-Real.eulerMascheroniConstant) - ε) * T :=
        mul_le_mul_of_nonneg_right hcoef hT.le
  have hscale : 0 ≤ (N : ℝ) / Real.log (N : ℝ) ^ (2 : ℕ) :=
    div_nonneg (Nat.cast_nonneg N) (sq_nonneg _)
  have hleft :
      (B - δ) * S * (N : ℝ) / Real.log (N : ℝ) ^ (2 : ℕ) ≤
        (10 * Real.exp (-Real.eulerMascheroniConstant) - ε) * T *
          (N : ℝ) / Real.log (N : ℝ) ^ (2 : ℕ) := by
    simpa [mul_div_assoc] using
      (mul_le_mul_of_nonneg_right hseriesScaled hscale)
  have hmertensN' :
      (10 * Real.exp (-Real.eulerMascheroniConstant) - ε) * T /
          Real.log (N : ℝ) ≤
        MertensTheorem.goldbachSieveProduct N (jurkatRichertSourceZ N) := by
    simpa [T] using hmertensN hEven
  have hmass : 0 ≤ (N : ℝ) / Real.log (N : ℝ) :=
    div_nonneg (Nat.cast_nonneg N) hlogN.le
  have hright := mul_le_mul_of_nonneg_left hmertensN' hmass
  have hproduct : 0 ≤ MertensTheorem.goldbachSieveProduct N
      (jurkatRichertSourceZ N) := by
    rw [← jurkatRichertSourceSieveProduct_eq_goldbachSieveProduct N hEven]
    unfold AnalyticNumberTheory.Sieve.sieveProductPrimeFactors
    apply Finset.prod_nonneg
    intro p hp
    exact sub_nonneg.mpr
      ((jurkatRichertSourceBoundingSieve N).nu_lt_one_of_prime p
        (Nat.prime_of_mem_primeFactors hp)
        ((Nat.mem_primeFactors_of_ne_zero
          (jurkatRichertSourceSiftingProduct_ne_zero N)).mp hp).2).le
  have hmassLower :
      (N : ℝ) / Real.log (N : ℝ) ≤
        LiuWeight.liuLogarithmicIntegral (2 / Real.log 2) N := by
    apply LiuWeight.div_log_le_liuLogarithmicIntegral
    exact_mod_cast (show 2 ≤ N by omega)
  calc
    (jurkatRichertMertensFactor - δ) *
          SingularSeries.liuSingularSeries N * (N : ℝ) /
          Real.log N ^ (2 : ℕ) =
        (B - δ) * S * (N : ℝ) / Real.log (N : ℝ) ^ (2 : ℕ) := by
      rfl
    _ ≤ (10 * Real.exp (-Real.eulerMascheroniConstant) - ε) * T *
          (N : ℝ) / Real.log (N : ℝ) ^ (2 : ℕ) := hleft
    _ = ((N : ℝ) / Real.log (N : ℝ)) *
          ((10 * Real.exp (-Real.eulerMascheroniConstant) - ε) * T /
            Real.log (N : ℝ)) := by ring
    _ ≤ ((N : ℝ) / Real.log (N : ℝ)) *
          MertensTheorem.goldbachSieveProduct N (jurkatRichertSourceZ N) :=
      hright
    _ ≤ LiuWeight.liuLogarithmicIntegral (2 / Real.log 2) N *
          MertensTheorem.goldbachSieveProduct N (jurkatRichertSourceZ N) :=
      mul_le_mul_of_nonneg_right hmassLower hproduct
    _ = (jurkatRichertSourceBoundingSieve N).totalMass *
          AnalyticNumberTheory.Sieve.sieveProductPrimeFactors
           (jurkatRichertSourceBoundingSieve N) := by
      rw [jurkatRichertSourceSieveProduct_eq_goldbachSieveProduct N hEven]
      rfl

private theorem tendsto_jurkatRichertMertensUpperCoefficient (C : ℝ) :
    Filter.Tendsto (fun N : ℕ =>
      Real.log (N : ℝ) *
        (Real.exp (-Real.eulerMascheroniConstant) /
            Real.log ((jurkatRichertSourceZ N - 1 : ℕ) : ℝ) +
          C / Real.log ((jurkatRichertSourceZ N - 1 : ℕ) : ℝ) ^ 2))
      Filter.atTop
      (nhds (10 * Real.exp (-Real.eulerMascheroniConstant))) := by
  have hqinv := tendsto_log_jurkatRichertSourceZ_sub_one_div_log.inv₀
    (by norm_num : (1 / 10 : ℝ) ≠ 0)
  have hmR : Filter.Tendsto
      (fun N : ℕ => ((jurkatRichertSourceZ N - 1 : ℕ) : ℝ))
      Filter.atTop Filter.atTop :=
    tendsto_natCast_atTop_atTop.comp tendsto_jurkatRichertSourceZ_sub_one_atTop
  have hlogm : Filter.Tendsto
      (fun N : ℕ => Real.log ((jurkatRichertSourceZ N - 1 : ℕ) : ℝ))
      Filter.atTop Filter.atTop :=
    Real.tendsto_log_atTop.comp hmR
  have hloginv : Filter.Tendsto
      (fun N : ℕ => (Real.log ((jurkatRichertSourceZ N - 1 : ℕ) : ℝ))⁻¹)
      Filter.atTop (nhds 0) :=
    tendsto_inv_atTop_zero.comp hlogm
  have hE : Filter.Tendsto
      (fun _ : ℕ => Real.exp (-Real.eulerMascheroniConstant))
      Filter.atTop (nhds (Real.exp (-Real.eulerMascheroniConstant))):=
    tendsto_const_nhds
  have hC : Filter.Tendsto (fun _ : ℕ => C) Filter.atTop (nhds C) :=
    tendsto_const_nhds
  have hmain := (hE.mul hqinv).add ((hC.mul hqinv).mul hloginv)
  have hmain' : Filter.Tendsto (fun N : ℕ =>
      Real.exp (-Real.eulerMascheroniConstant) *
          (Real.log ((jurkatRichertSourceZ N - 1 : ℕ) : ℝ) /
            Real.log (N : ℝ))⁻¹ +
        (C * (Real.log ((jurkatRichertSourceZ N - 1 : ℕ) : ℝ) /
            Real.log (N : ℝ))⁻¹) *
          (Real.log ((jurkatRichertSourceZ N - 1 : ℕ) : ℝ))⁻¹)
      Filter.atTop
      (nhds (10 * Real.exp (-Real.eulerMascheroniConstant))) := by
    convert hmain using 1
    norm_num
    ring
  apply hmain'.congr'
  filter_upwards [eventually_jurkatRichertSourceZ_sub_one_eq_correctedChenZ,
      Filter.eventually_ge_atTop (3 ^ 10)] with N heq hN
  have hNpos : 0 < Real.log (N : ℝ) :=
    Real.log_pos (by exact_mod_cast (by omega : 1 < N))
  have hc := correctedChenZ_sub_one_ge_of_N_ge (k := 2) (by norm_num)
    (show (2 + 1) ^ 10 ≤ N by simpa using hN)
  have hm : 3 ≤ jurkatRichertSourceZ N - 1 := by
    rw [heq]
    omega
  have hmlog :
      0 < Real.log ((jurkatRichertSourceZ N - 1 : ℕ) : ℝ) :=
    Real.log_pos
      (by exact_mod_cast (by omega : 1 < jurkatRichertSourceZ N - 1))
  field_simp [hNpos.ne', hmlog.ne']

/-- Mertens' product theorem at the literal source cutoff, with Liu's genuine
normalization and an upper error uniform in the even integer `N`. -/
theorem eventually_jurkatRichertSourceGoldbachSieveProduct_upper
    (η : ℝ) (hη : 0 < η) :
    ∀ᶠ N : ℕ in Filter.atTop, Even N →
      MertensTheorem.goldbachSieveProduct N (jurkatRichertSourceZ N) ≤
        (20 * Real.exp (-Real.eulerMascheroniConstant) + η) *
          SingularSeries.liuSingularSeries N / Real.log (N : ℝ) := by
  let B := 10 * Real.exp (-Real.eulerMascheroniConstant)
  have hB : 0 < B := by positivity
  let d := min 1 (η / (4 * (B + 2)))
  have hd : 0 < d := lt_min (by norm_num)
    (div_pos hη (by positivity))
  have hd1 : d ≤ 1 := min_le_left _ _
  have hdη : d * (B + 2) ≤ η / 4 := by
    have := min_le_right (1 : ℝ) (η / (4 * (B + 2)))
    dsimp [d] at *
    apply (le_div_iff₀ (by positivity : 0 < 4 * (B + 2))).mp at this
    nlinarith
  obtain ⟨C, hC⟩ := MertensTheorem.sieve_product_asymptotic
  have hcoef := (tendsto_jurkatRichertMertensUpperCoefficient C).eventually
    (Iic_mem_nhds (by linarith :
      B < B + d))
  have hseriesRaw :=
    SingularSeries.eventually_liuSingularSeriesTruncated_le d hd
  have hzAtTop := tendsto_jurkatRichertSourceZ_sub_one_atTop.eventually hseriesRaw
  filter_upwards [hcoef, hzAtTop,
      Filter.eventually_ge_atTop (3 ^ 10),
      eventually_jurkatRichertSourceZ_sub_one_eq_correctedChenZ] with
      N hcoefN hseriesN hN heq
  intro hEven
  have hN4 : 4 ≤ N := by omega
  have hz3 : 3 ≤ jurkatRichertSourceZ N := by
    have hc := correctedChenZ_sub_one_ge_of_N_ge (k := 2) (by norm_num)
      (show (2 + 1) ^ 10 ≤ N by simpa using hN)
    have : 3 ≤ correctedChenZ N := by omega
    rw [← heq] at this
    omega
  have hlogN : 0 < Real.log (N : ℝ) :=
    Real.log_pos (by exact_mod_cast (by omega : 1 < N))
  have hz2 : 2 ≤ jurkatRichertSourceZ N - 1 := by omega
  let T := SingularSeries.singularSeriesTruncated N
    (jurkatRichertSourceZ N - 1)
  let S := SingularSeries.liuSingularSeries N
  have hT : 0 < T := by
    dsimp [T]
    exact SingularSeries.singularSeriesTruncated_pos N _ (by omega)
  have hS : 0 < S := by
    simpa [S] using SingularSeries.liuSingularSeries_pos N
  have hasym := hC N (jurkatRichertSourceZ N) hz3 hEven hN4
  have hproduct :
      MertensTheorem.goldbachSieveProduct N (jurkatRichertSourceZ N) ≤
        T * (Real.exp (-Real.eulerMascheroniConstant) /
            Real.log ((jurkatRichertSourceZ N - 1 : ℕ) : ℝ) +
          C / Real.log ((jurkatRichertSourceZ N - 1 : ℕ) : ℝ) ^ 2) := by
    calc
      MertensTheorem.goldbachSieveProduct N (jurkatRichertSourceZ N) ≤
          T * Real.exp (-Real.eulerMascheroniConstant) /
              Real.log ((jurkatRichertSourceZ N - 1 : ℕ) : ℝ) +
            C * T / Real.log ((jurkatRichertSourceZ N - 1 : ℕ) : ℝ) ^ 2 := by
        dsimp [T]
        linarith [(abs_le.mp hasym).2]
      _ = T * (Real.exp (-Real.eulerMascheroniConstant) /
              Real.log ((jurkatRichertSourceZ N - 1 : ℕ) : ℝ) +
            C / Real.log ((jurkatRichertSourceZ N - 1 : ℕ) : ℝ) ^ 2) := by ring
  have hcoefficient :
      Real.exp (-Real.eulerMascheroniConstant) /
            Real.log ((jurkatRichertSourceZ N - 1 : ℕ) : ℝ) +
          C / Real.log ((jurkatRichertSourceZ N - 1 : ℕ) : ℝ) ^ 2 ≤
        (B + d) / Real.log (N : ℝ) := by
    apply (le_div_iff₀ hlogN).2
    simpa [B, mul_comm] using hcoefN
  have hlegacy : T ≤ 2 * (1 + d) * S := by
    rw [show T = 2 * SingularSeries.liuSingularSeriesTruncated N
        (jurkatRichertSourceZ N - 1) by
      dsimp [T]
      exact SingularSeries.singularSeriesTruncated_eq_two_mul_liuSingularSeriesTruncated
        N _ hEven hz2]
    simpa [S, mul_assoc] using
      mul_le_mul_of_nonneg_left (hseriesN N (by omega)) (by norm_num : (0 : ℝ) ≤ 2)
  have hfinalCoefficient : 2 * (B + d) * (1 + d) ≤ 2 * B + η := by
    have hdsq : d ^ 2 ≤ d := by nlinarith [mul_nonneg hd.le (sub_nonneg.mpr hd1)]
    nlinarith
  calc
    MertensTheorem.goldbachSieveProduct N (jurkatRichertSourceZ N) ≤
        T * (Real.exp (-Real.eulerMascheroniConstant) /
            Real.log ((jurkatRichertSourceZ N - 1 : ℕ) : ℝ) +
          C / Real.log ((jurkatRichertSourceZ N - 1 : ℕ) : ℝ) ^ 2) := hproduct
    _ ≤ T * ((B + d) / Real.log (N : ℝ)) :=
      mul_le_mul_of_nonneg_left hcoefficient hT.le
    _ ≤ (2 * (1 + d) * S) * ((B + d) / Real.log (N : ℝ)) :=
      mul_le_mul_of_nonneg_right hlegacy
        (div_nonneg (by linarith) hlogN.le)
    _ = (2 * (B + d) * (1 + d)) * S / Real.log (N : ℝ) := by ring
    _ ≤ (2 * B + η) * S / Real.log (N : ℝ) := by
      exact div_le_div_of_nonneg_right
        (mul_le_mul_of_nonneg_right hfinalCoefficient hS.le) hlogN.le
    _ = (20 * Real.exp (-Real.eulerMascheroniConstant) + η) *
          SingularSeries.liuSingularSeries N / Real.log (N : ℝ) := by
      dsimp [B, S]
      ring

/-- The genuine logarithmic integral has the sharp upper normalization needed
when it is multiplied by the Mertens sieve product. -/
theorem eventually_liuLogarithmicIntegral_le
    (η : ℝ) (hη : 0 < η) :
    ∀ᶠ N : ℕ in Filter.atTop,
      LiuWeight.liuLogarithmicIntegral (2 / Real.log 2) N ≤
        (1 + η) * (N : ℝ) / Real.log (N : ℝ) := by
  obtain ⟨C, hC, hrem⟩ :=
    LiuWeight.eventually_abs_liuLogarithmicIntegralRemainder_le
      (2 / Real.log 2)
  have hlogAtTop : Filter.Tendsto (fun N : ℕ => Real.log (N : ℝ))
      Filter.atTop Filter.atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hlarge := hlogAtTop.eventually
    (Filter.eventually_ge_atTop (C / η))
  have hremNat := tendsto_natCast_atTop_atTop.eventually hrem
  filter_upwards [hremNat, hlarge, Filter.eventually_ge_atTop 2] with N hremN hlargeN hN
  have hlogN : 0 < Real.log (N : ℝ) :=
    Real.log_pos (by exact_mod_cast (show 1 < N by omega))
  have hCoverLog : C / Real.log (N : ℝ) ≤ η := by
    rw [div_le_iff₀ hlogN]
    have := (div_le_iff₀ hη).mp hlargeN
    nlinarith
  have hscale : 0 ≤ (N : ℝ) / Real.log (N : ℝ) := by positivity
  have herror :
      C * (N : ℝ) / Real.log (N : ℝ) ^ 2 ≤
        η * ((N : ℝ) / Real.log (N : ℝ)) := by
    calc
      C * (N : ℝ) / Real.log (N : ℝ) ^ 2 =
          (C / Real.log (N : ℝ)) * ((N : ℝ) / Real.log (N : ℝ)) := by ring
      _ ≤ η * ((N : ℝ) / Real.log (N : ℝ)) :=
        mul_le_mul_of_nonneg_right hCoverLog hscale
  have hremainder :
      LiuWeight.liuLogarithmicIntegralRemainder (2 / Real.log 2) N ≤
        η * ((N : ℝ) / Real.log (N : ℝ)) :=
    (le_abs_self _).trans ((hremN (by exact_mod_cast hN)).trans herror)
  unfold LiuWeight.liuLogarithmicIntegralRemainder at hremainder
  calc
    LiuWeight.liuLogarithmicIntegral (2 / Real.log 2) N =
        (N : ℝ) / Real.log (N : ℝ) +
          (LiuWeight.liuLogarithmicIntegral (2 / Real.log 2) N -
            (N : ℝ) / Real.log (N : ℝ)) := by ring
    _ ≤ (N : ℝ) / Real.log (N : ℝ) +
        η * ((N : ℝ) / Real.log (N : ℝ)) :=
      by simpa [add_comm] using
        add_le_add_left hremainder ((N : ℝ) / Real.log (N : ℝ))
    _ = (1 + η) * (N : ℝ) / Real.log (N : ℝ) := by ring

/-- The common mass in every conditioned source sieve has the sharp
Liu-normalized upper asymptotic. -/
theorem eventually_jurkatRichertSourceCommonDensity_upper
    (η : ℝ) (hη : 0 < η) :
    ∀ᶠ N : ℕ in Filter.atTop, Even N →
      LiuWeight.liuLogarithmicIntegral (2 / Real.log 2) N *
          AnalyticNumberTheory.Sieve.sieveProductPrimeFactors
            (jurkatRichertSourceBoundingSieve N) ≤
        (20 * Real.exp (-Real.eulerMascheroniConstant) + η) *
          SingularSeries.liuSingularSeries N * (N : ℝ) /
            Real.log (N : ℝ) ^ (2 : ℕ) := by
  let B := 20 * Real.exp (-Real.eulerMascheroniConstant)
  have hB : 0 < B := by positivity
  let d := min 1 (η / (B + 2))
  have hd : 0 < d := lt_min (by norm_num) (div_pos hη (by positivity))
  have hd1 : d ≤ 1 := min_le_left _ _
  have hdη : d * (B + 2) ≤ η := by
    have := min_le_right (1 : ℝ) (η / (B + 2))
    dsimp [d] at *
    exact (le_div_iff₀ (by positivity : 0 < B + 2)).mp this
  have hcoef : (1 + d) * (B + d) ≤ B + η := by
    have hdsq : d ^ 2 ≤ d := by
      nlinarith [mul_nonneg hd.le (sub_nonneg.mpr hd1)]
    nlinarith
  have hli := eventually_liuLogarithmicIntegral_le d hd
  have hproduct := eventually_jurkatRichertSourceGoldbachSieveProduct_upper d hd
  filter_upwards [hli, hproduct, Filter.eventually_ge_atTop 2] with
      N hliN hproductN hN
  intro hEven
  have hlogN : 0 < Real.log (N : ℝ) :=
    Real.log_pos (by exact_mod_cast (show 1 < N by omega))
  have hgoldbachNonneg :
      0 ≤ MertensTheorem.goldbachSieveProduct N (jurkatRichertSourceZ N) := by
    rw [← jurkatRichertSourceSieveProduct_eq_goldbachSieveProduct N hEven]
    unfold AnalyticNumberTheory.Sieve.sieveProductPrimeFactors
    apply Finset.prod_nonneg
    intro p hp
    exact sub_nonneg.mpr
      ((jurkatRichertSourceBoundingSieve N).nu_lt_one_of_prime p
        (Nat.prime_of_mem_primeFactors hp)
        ((Nat.mem_primeFactors_of_ne_zero
          (jurkatRichertSourceSiftingProduct_ne_zero N)).mp hp).2).le
  have hscale : 0 ≤ (1 + d) * (N : ℝ) / Real.log (N : ℝ) := by positivity
  have hS : 0 ≤ SingularSeries.liuSingularSeries N :=
    (SingularSeries.liuSingularSeries_pos N).le
  calc
    LiuWeight.liuLogarithmicIntegral (2 / Real.log 2) N *
          AnalyticNumberTheory.Sieve.sieveProductPrimeFactors
            (jurkatRichertSourceBoundingSieve N) =
        LiuWeight.liuLogarithmicIntegral (2 / Real.log 2) N *
          MertensTheorem.goldbachSieveProduct N (jurkatRichertSourceZ N) := by
      rw [jurkatRichertSourceSieveProduct_eq_goldbachSieveProduct N hEven]
    _ ≤ ((1 + d) * (N : ℝ) / Real.log (N : ℝ)) *
          MertensTheorem.goldbachSieveProduct N (jurkatRichertSourceZ N) :=
      mul_le_mul_of_nonneg_right hliN hgoldbachNonneg
    _ ≤ ((1 + d) * (N : ℝ) / Real.log (N : ℝ)) *
          ((B + d) * SingularSeries.liuSingularSeries N /
            Real.log (N : ℝ)) :=
      mul_le_mul_of_nonneg_left (by simpa [B] using hproductN hEven) hscale
    _ = ((1 + d) * (B + d)) * SingularSeries.liuSingularSeries N *
          (N : ℝ) / Real.log (N : ℝ) ^ (2 : ℕ) := by ring
    _ ≤ (B + η) * SingularSeries.liuSingularSeries N *
          (N : ℝ) / Real.log (N : ℝ) ^ (2 : ℕ) := by
      have hright : 0 ≤ SingularSeries.liuSingularSeries N * (N : ℝ) /
          Real.log (N : ℝ) ^ (2 : ℕ) := by positivity
      simpa [mul_assoc, mul_div_assoc] using
        mul_le_mul_of_nonneg_right hcoef hright
    _ = (20 * Real.exp (-Real.eulerMascheroniConstant) + η) *
          SingularSeries.liuSingularSeries N * (N : ℝ) /
            Real.log (N : ℝ) ^ (2 : ℕ) := by rfl

/-- The base term in Chen's equation (26), using equation (25) for its
Mertens normalization. -/
def ChenJurkatRichertBaseLowerSieveAsymptotic : Prop :=
  ∀ η : ℝ, 0 < η →
    ∀ᶠ N : ℕ in Filter.atTop, Even N →
      (jurkatRichertBaseMainCoefficient jurkatRichertJ - η) *
            SingularSeries.liuSingularSeries N * (N : ℝ) /
              Real.log N ^ (2 : ℕ) ≤
        ((jurkatRichertSourceCandidates N).card : ℝ)

/-- The literal base asymptotic follows from the level-`N^(1/2-ε)` lower-sieve
fundamental lemma and Goldbach AP distribution for its finite remainder.
Equation (25)'s Mertens normalization is unconditional. -/
theorem chenJurkatRichertBaseLowerSieveAsymptotic_of_inputs
    (hlower : ChenJurkatRichertBaseLowerSieveFundamentalLemma)
    (hdistribution : ChenJurkatRichertBaseGoldbachDistribution) :
    ChenJurkatRichertBaseLowerSieveAsymptotic := by
  intro η hη
  let A := jurkatRichertBaseSieveFactor jurkatRichertJ
  let B := jurkatRichertMertensFactor
  let C := jurkatRichertBaseMainCoefficient jurkatRichertJ
  have hA : 0 < A := by
    simpa [A] using jurkatRichertBaseSieveFactor_pos
  have hB : 0 < B := by
    simpa [B] using jurkatRichertMertensFactor_pos
  have hAB : A * B = C := by
    simpa [A, B, C] using jurkatRichert_sieveFactor_mul_mertensFactor
  have hC : 0 < C := by rw [← hAB]; positivity
  let η' := min η (C / 2)
  have hη' : 0 < η' := lt_min hη (half_pos hC)
  have hη'η : η' ≤ η := min_le_left _ _
  have hη'C : η' ≤ C / 2 := min_le_right _ _
  let δA := η' / (8 * B)
  let δB := η' / (8 * A)
  let δR := η' / 2
  have hδA : 0 < δA := div_pos hη' (by positivity)
  have hδB : 0 < δB := div_pos hη' (by positivity)
  have hδR : 0 < δR := half_pos hη'
  have hδAB : δA * B = η' / 8 := by
    dsimp [δA]
    field_simp [hB.ne']
  have hAδB : A * δB = η' / 8 := by
    dsimp [δB]
    field_simp [hA.ne']
  have hδAle : δA ≤ A / 16 := by
    by_contra hnot
    have hlt : A / 16 < δA := lt_of_not_ge hnot
    have hmul := mul_lt_mul_of_pos_right hlt hB
    have hleft : A / 16 * B = C / 16 := by rw [← hAB]; ring
    rw [hleft, hδAB] at hmul
    nlinarith
  have hδBle : δB ≤ B / 16 := by
    by_contra hnot
    have hlt : B / 16 < δB := lt_of_not_ge hnot
    have hmul := mul_lt_mul_of_pos_right hlt hA
    have hleft : B / 16 * A = C / 16 := by rw [← hAB]; ring
    rw [hleft, mul_comm δB A, hAδB] at hmul
    nlinarith
  have hAminus : 0 ≤ A - δA := by nlinarith
  have hBminus : 0 ≤ B - δB := by nlinarith
  rcases hlower δA hδA with ⟨ε, hε, hεHalf, hLower⟩
  have hDistribution :=
    hdistribution ε hε hεHalf δR hδR
  have hMertens := chenJurkatRichertBaseMertensNormalization δB hδB
  filter_upwards [hLower, hDistribution, hMertens,
      Filter.eventually_ge_atTop 3] with N hLowerN hDistributionN hMertensN hN
  intro hEven
  have hLowerN' := hLowerN hEven
  have hDistributionN' := hDistributionN hEven
  have hMertensN' := hMertensN hEven
  let M : ℝ :=
    SingularSeries.liuSingularSeries N * (N : ℝ) /
      Real.log N ^ (2 : ℕ)
  have hM : 0 ≤ M := by
    dsimp [M]
    exact div_nonneg
      (mul_nonneg (SingularSeries.liuSingularSeries_pos N).le (Nat.cast_nonneg N))
      (sq_nonneg (Real.log N))
  have hMain :
      (B - δB) * M ≤
        (jurkatRichertSourceBoundingSieve N).totalMass *
          AnalyticNumberTheory.Sieve.sieveProductPrimeFactors
            (jurkatRichertSourceBoundingSieve N) := by
    convert hMertensN' using 1
    dsimp [B, M]
    ring
  have hScaled := mul_le_mul_of_nonneg_left hMain hAminus
  have hRemainder :
      jurkatRichertSourceRemainderSum N ε ≤ δR * M := by
    convert hDistributionN' using 1
    dsimp [δR, M]
    ring
  have hFinite :
      (A - δA) * ((B - δB) * M) - δR * M ≤
        (jurkatRichertSourceBoundingSieve N).siftedSum := by
    have hLowerRewritten :
        (A - δA) *
              ((jurkatRichertSourceBoundingSieve N).totalMass *
                AnalyticNumberTheory.Sieve.sieveProductPrimeFactors
                  (jurkatRichertSourceBoundingSieve N)) -
            jurkatRichertSourceRemainderSum N ε ≤
          (jurkatRichertSourceBoundingSieve N).siftedSum := by
      simpa [A] using hLowerN'
    linarith
  have hδProduct : 0 ≤ δA * δB := mul_nonneg hδA.le hδB.le
  have hCoefficient :
      C - η ≤ (A - δA) * (B - δB) - δR := by
    dsimp [δR]
    rw [← hAB]
    nlinarith
  have hTargetScale :
      (C - η) * M ≤ ((A - δA) * (B - δB) - δR) * M :=
    mul_le_mul_of_nonneg_right hCoefficient hM
  have hTarget :
      (C - η) * M ≤
        (jurkatRichertSourceBoundingSieve N).siftedSum := by
    calc
      (C - η) * M ≤ ((A - δA) * (B - δB) - δR) * M :=
        hTargetScale
      _ = (A - δA) * ((B - δB) * M) - δR * M := by ring
      _ ≤ (jurkatRichertSourceBoundingSieve N).siftedSum := hFinite
  rw [jurkatRichertSourceBoundingSieve_siftedSum_eq_card N] at hTarget
  convert hTarget using 1
  dsimp [C, M]
  ring

/-- The base asymptotic directly from its two literature inputs.  The lower
Rosser density fundamental lemma and standard Bombieri--Vinogradov are converted
to the finite lower-sieve and Goldbach-distribution APIs above. -/
theorem chenJurkatRichertBaseLowerSieveAsymptotic_of_literature_inputs
    (hLowerDensity : DimensionOneLowerRosserDensityFundamentalLemma)
    (hBV : BombieriVinogradov.StandardBombieriVinogradov) :
    ChenJurkatRichertBaseLowerSieveAsymptotic :=
  chenJurkatRichertBaseLowerSieveAsymptotic_of_inputs
    (chenJurkatRichertBaseLowerSieveFundamentalLemma_of_density
      (chenJurkatRichertBaseLowerRosserDensityFundamentalLemma_of_generic
        hLowerDensity))
    (chenJurkatRichertBaseGoldbachDistribution_of_standardBV hBV)

end MathlibNt.SieveTheory.SwitchingPrinciple

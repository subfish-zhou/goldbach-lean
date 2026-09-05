/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nous Research
-/
import MathlibNt.SieveTheory.LinearSieve.Suzuki.SuzukiLowerSieveFactorFirstInterval

/-!
# Finite conservation behind Suzuki's first lower interval

This module freezes the normalization in Suzuki Proposition 9.3(iv)--(v) before
any passage to the parity-layer limit.  At `κ = 1`, `β = 2`, the finite constants
are

* `A_m = 3 (1 + T_{2m-1}(3))`, and
* `B_m = 2 (1 - T_{2m}(2))`.

The main theorem proves the exact finite identity

`1 - T_{2m}(s) = B_m / s + A_m / s * ∫₂ˢ dt/(t-1)`

for `m ≥ 1` and `2 ≤ s ≤ 4`.  Its final corollary isolates, without a
conclusion-shaped hypothesis, the two genuine tails still needed to identify the
explicit first-interval factor with `1` minus the even continuous-layer limit.
-/

open scoped Classical BigOperators Interval
open Finset MeasureTheory intervalIntegral

namespace MathlibNt.SieveTheory

open SuzukiFiniteContinuousLayers

/-- Suzuki's odd finite partial sum `T_{2m-1}`. -/
noncomputable def suzukiOddSourceUpperPartialSum (m : ℕ) (s : ℝ) : ℝ :=
  ∑ k ∈ Finset.range m, suzukiLayer 1 2 (2 * k + 1) s

/-- The finite constant `A_{2m-1}` in Proposition 9.3(iv). -/
noncomputable def suzukiFiniteLowerAmplitude (m : ℕ) : ℝ :=
  3 * (1 + suzukiOddSourceUpperPartialSum m 3)

/-- The finite constant `B_{2m}` in Proposition 9.3(v). -/
noncomputable def suzukiFiniteLowerBoundary (m : ℕ) : ℝ :=
  2 * (1 - suzukiEvenSourceLowerPartialSum m 2)

/-- For every odd source layer beyond the base layer, its weighted value is
constant on Suzuki's first upper strip `1 < u ≤ 3`. -/
theorem mul_suzukiLayer_one_two_odd_eq_three_mul_at_three
    {n : ℕ} (hn : n % 2 = 1) (hn3 : 3 ≤ n) {u : ℝ}
    (hu1 : 1 ≤ u) (hu3 : u ≤ 3) :
    u * suzukiLayer 1 2 n u = 3 * suzukiLayer 1 2 n 3 := by
  obtain ⟨j, rfl⟩ : ∃ j, n = j + 2 := by
    exact ⟨n - 2, (Nat.sub_add_cancel (by omega)).symm⟩
  have heps : sourceEpsilon (j + 2) = 1 := by
    unfold sourceEpsilon
    omega
  have hlower_u : recursionLower 2 u (j + 2) = 3 := by
    unfold recursionLower
    rw [heps]
    norm_num
    rw [max_eq_right hu3]
    apply min_eq_left
    have hj0 : (0 : ℝ) ≤ (j : ℝ) := Nat.cast_nonneg j
    linarith
  have hlower_three : recursionLower 2 3 (j + 2) = 3 := by
    unfold recursionLower
    rw [heps]
    norm_num
    have hj0 : (0 : ℝ) ≤ (j : ℝ) := Nat.cast_nonneg j
    linarith
  rw [suzukiLayer_succ_succ, suzukiLayer_succ_succ, hlower_u, hlower_three]
  have hu0 : u ≠ 0 := ne_of_gt (by linarith)
  norm_num [Real.rpow_one, hu0]
  ring_nf

/-- Finite Proposition 9.3(iv), specialized to `κ = 1`, `β = 2` and the odd
partial sum ending at `2m-1`. -/
theorem mul_suzukiOddSourceUpperPartialSum_eq_finiteAmplitude_sub
    {m : ℕ} (hm : 1 ≤ m) {u : ℝ} (hu1 : 1 ≤ u) (hu3 : u ≤ 3) :
    u * suzukiOddSourceUpperPartialSum m u =
      suzukiFiniteLowerAmplitude m - u := by
  rw [suzukiOddSourceUpperPartialSum, mul_sum]
  have hterm (k : ℕ) (hk : k ∈ Finset.range m) :
      u * suzukiLayer 1 2 (2 * k + 1) u =
        3 * suzukiLayer 1 2 (2 * k + 1) 3 +
          (if k = 0 then 3 - u else 0) := by
    by_cases hk0 : k = 0
    · subst k
      simp only [mul_zero, zero_add]
      rw [SuzukiFiniteContinuousLayers.suzukiLayer_one_one_two
        (by linarith) hu3,
        SuzukiFiniteContinuousLayers.suzukiLayer_one_one_two_eq_zero_of_three_le
          (by norm_num : (3 : ℝ) ≤ 3)]
      simp only [mul_zero, zero_add, if_pos]
      field_simp
    · rw [if_neg hk0, add_zero]
      apply mul_suzukiLayer_one_two_odd_eq_three_mul_at_three
      · omega
      · omega
      · exact hu1
      · exact hu3
  rw [Finset.sum_congr rfl hterm, Finset.sum_add_distrib]
  have hzero : 0 ∈ Finset.range m := by
    simp only [Finset.mem_range]
    omega
  rw [Finset.sum_ite_eq', if_pos hzero]
  unfold suzukiFiniteLowerAmplitude suzukiOddSourceUpperPartialSum
  rw [← Finset.mul_sum]
  ring

/-- On `2 ≤ t ≤ 4`, the preceding odd partial sum has the exact integrand
`A_m/(t-1)-1` used in Proposition 9.3(v). -/
theorem suzukiOddSourceUpperPartialSum_sub_one
    {m : ℕ} (hm : 1 ≤ m) {t : ℝ} (ht2 : 2 ≤ t) (ht4 : t ≤ 4) :
    suzukiOddSourceUpperPartialSum m (t - 1) =
      suzukiFiniteLowerAmplitude m / (t - 1) - 1 := by
  have hweighted := mul_suzukiOddSourceUpperPartialSum_eq_finiteAmplitude_sub
    hm (u := t - 1) (by linarith) (by linarith)
  have ht0 : t - 1 ≠ 0 := ne_of_gt (by linarith)
  apply (mul_left_cancel₀ ht0)
  field_simp
  nlinarith

/-- Each even layer is obtained by integrating its preceding odd layer from the
current point to its closed support endpoint. -/
theorem mul_suzukiLayer_one_two_even_eq_integral
    (k : ℕ) {s : ℝ} (hs2 : 2 ≤ s) (hs4 : s ≤ 4) :
    s * suzukiLayer 1 2 (2 * (k + 1)) s =
      ∫ t in s..(2 + (2 * (k + 1) : ℕ)),
        suzukiLayer 1 2 (2 * k + 1) (t - 1) := by
  rw [show 2 * (k + 1) = (2 * k) + 2 by omega,
    suzukiLayer_succ_succ]
  have heps : sourceEpsilon (2 * k + 2) = 0 := by
    unfold sourceEpsilon
    omega
  have hlower : recursionLower 2 s (2 * k + 2) = s := by
    unfold recursionLower
    rw [heps]
    norm_num
    rw [max_eq_left hs2]
    apply min_eq_left
    have hk0 : (0 : ℝ) ≤ (k : ℝ) := Nat.cast_nonneg k
    linarith
  rw [hlower]
  have hs0 : s ≠ 0 := ne_of_gt (by linarith)
  norm_num [dPowDensity, Real.rpow_one, hs0]

/-- Moving the lower endpoint from `2` to `s` gives one exact finite
conservation step. -/
theorem mul_suzukiLayer_one_two_even_eq_at_two_sub_integral
    (k : ℕ) {s : ℝ} (hs2 : 2 ≤ s) (hs4 : s ≤ 4) :
    s * suzukiLayer 1 2 (2 * (k + 1)) s =
      2 * suzukiLayer 1 2 (2 * (k + 1)) 2 -
        ∫ t in (2 : ℝ)..s, suzukiLayer 1 2 (2 * k + 1) (t - 1) := by
  let f : ℝ → ℝ := fun t => suzukiLayer 1 2 (2 * k + 1) (t - 1)
  let b : ℝ := 2 + (2 * (k + 1) : ℕ)
  have hsb : s ≤ b := by
    dsimp [b]
    have hk0 : (0 : ℝ) ≤ (k : ℝ) := Nat.cast_nonneg k
    norm_num [Nat.cast_add, Nat.cast_mul]
    linarith
  have hcont : ContinuousOn f (Set.Icc (2 : ℝ) b) := by
    have hc : ContinuousOn (suzukiLayer 1 2 (2 * k + 1))
        (SuzukiFiniteContinuousLayers.KappaOneModel.closedDomain 2 (2 * k + 1)) := by
      exact (SuzukiFiniteContinuousLayers.KappaOneModel.regular
          (β := (2 : ℝ)) (by norm_num) (2 * k + 1)).continuous.congr
        (fun u _ =>
          (SuzukiFiniteContinuousLayers.KappaOneModel.layer_eq_suzukiLayer
            2 (2 * k + 1) u).symm)
    change ContinuousOn
      ((fun u => suzukiLayer 1 2 (2 * k + 1) u) ∘ fun t => t - 1)
      (Set.Icc (2 : ℝ) b)
    apply hc.comp (continuous_id.sub continuous_const).continuousOn
    intro t ht
    unfold SuzukiFiniteContinuousLayers.KappaOneModel.closedDomain
    simp only [Set.mem_Ici, SuzukiFiniteContinuousLayers.KappaOneModel.eps]
    have hodd : (2 * k + 1) % 2 = 1 := by omega
    rw [hodd]
    norm_num
    linarith [ht.1]
  have hInt2b : IntervalIntegrable f MeasureTheory.volume 2 b :=
    by
      apply ContinuousOn.intervalIntegrable
      rwa [Set.uIcc_of_le (by linarith : (2 : ℝ) ≤ b)]
  have hInt2s : IntervalIntegrable f MeasureTheory.volume 2 s :=
    hInt2b.mono_set (by
      rw [Set.uIcc_of_le (by linarith : (2 : ℝ) ≤ b), Set.uIcc_of_le hs2]
      exact Set.Icc_subset_Icc_right hsb)
  have hIntsb : IntervalIntegrable f MeasureTheory.volume s b :=
    hInt2b.mono_set (by
      rw [Set.uIcc_of_le (by linarith : (2 : ℝ) ≤ b), Set.uIcc_of_le hsb]
      exact Set.Icc_subset_Icc_left hs2)
  rw [mul_suzukiLayer_one_two_even_eq_integral k hs2 hs4,
    mul_suzukiLayer_one_two_even_eq_integral k (by norm_num) (by norm_num)]
  change (∫ t in s..b, f t) = (∫ t in (2 : ℝ)..b, f t) - ∫ t in (2 : ℝ)..s, f t
  rw [eq_sub_iff_add_eq]
  simpa [add_comm] using intervalIntegral.integral_add_adjacent_intervals hInt2s hIntsb

/-- Exact finite form of Suzuki Proposition 9.3(v) on the first lower interval. -/
theorem suzuki_even_partial_finite_conservation
    {m : ℕ} (hm : 1 ≤ m) {s : ℝ} (hs2 : 2 ≤ s) (hs4 : s ≤ 4) :
    s * suzukiEvenSourceLowerPartialSum m s =
      -suzukiFiniteLowerBoundary m + s -
        suzukiFiniteLowerAmplitude m *
          (∫ t in (2 : ℝ)..s, (t - 1)⁻¹) := by
  rw [suzukiEvenSourceLowerPartialSum, mul_sum]
  have hterm (k : ℕ) (hk : k ∈ Finset.range m) :=
    mul_suzukiLayer_one_two_even_eq_at_two_sub_integral k hs2 hs4
  rw [Finset.sum_congr rfl hterm, Finset.sum_sub_distrib]
  have hInts : ∀ k ∈ Finset.range m,
      IntervalIntegrable (fun t : ℝ => suzukiLayer 1 2 (2 * k + 1) (t - 1))
        MeasureTheory.volume 2 s := by
    intro k _hk
    apply ContinuousOn.intervalIntegrable
    rw [Set.uIcc_of_le hs2]
    have hc : ContinuousOn (suzukiLayer 1 2 (2 * k + 1))
        (SuzukiFiniteContinuousLayers.KappaOneModel.closedDomain 2 (2 * k + 1)) := by
      exact (SuzukiFiniteContinuousLayers.KappaOneModel.regular
          (β := (2 : ℝ)) (by norm_num) (2 * k + 1)).continuous.congr
        (fun u _ =>
          (SuzukiFiniteContinuousLayers.KappaOneModel.layer_eq_suzukiLayer
            2 (2 * k + 1) u).symm)
    change ContinuousOn
      ((fun u => suzukiLayer 1 2 (2 * k + 1) u) ∘ fun t => t - 1)
      (Set.Icc (2 : ℝ) s)
    apply hc.comp (continuous_id.sub continuous_const).continuousOn
    intro t ht
    unfold SuzukiFiniteContinuousLayers.KappaOneModel.closedDomain
    simp only [Set.mem_Ici, SuzukiFiniteContinuousLayers.KappaOneModel.eps]
    have hodd : (2 * k + 1) % 2 = 1 := by omega
    rw [hodd]
    norm_num
    linarith [ht.1]
  rw [← intervalIntegral.integral_finsetSum hInts]
  have hsumfun : (fun t : ℝ => ∑ k ∈ Finset.range m,
      suzukiLayer 1 2 (2 * k + 1) (t - 1)) =
      fun t => suzukiOddSourceUpperPartialSum m (t - 1) := by
    funext t
    rfl
  rw [hsumfun]
  have hcongr :
      (∫ t in (2 : ℝ)..s, suzukiOddSourceUpperPartialSum m (t - 1)) =
        ∫ t in (2 : ℝ)..s,
          suzukiFiniteLowerAmplitude m * (t - 1)⁻¹ - 1 := by
    apply intervalIntegral.integral_congr
    intro t ht
    have ht' : t ∈ Set.Icc (2 : ℝ) s := by
      simpa [Set.uIcc_of_le hs2] using ht
    change suzukiOddSourceUpperPartialSum m (t - 1) =
      suzukiFiniteLowerAmplitude m * (t - 1)⁻¹ - 1
    rw [suzukiOddSourceUpperPartialSum_sub_one hm ht'.1 (ht'.2.trans hs4)]
    ring
  rw [hcongr]
  have hInvInt : IntervalIntegrable (fun t : ℝ => (t - 1)⁻¹)
      MeasureTheory.volume 2 s := by
    exact ((continuousOn_id.sub continuousOn_const).inv₀
      (fun t ht => by
        rw [Set.uIcc_of_le hs2] at ht
        change t - 1 ≠ 0
        exact ne_of_gt (by linarith [ht.1]))).intervalIntegrable
  rw [intervalIntegral.integral_sub
      (hInvInt.const_mul (suzukiFiniteLowerAmplitude m))
      intervalIntegrable_const,
    intervalIntegral.integral_const_mul, intervalIntegral.integral_const]
  unfold suzukiFiniteLowerBoundary suzukiEvenSourceLowerPartialSum
  simp only [smul_eq_mul, mul_one]
  rw [← Finset.mul_sum]
  ring

/-- The finite lower factor is exactly the source first-interval expression plus
its two honest truncation residuals.  No convergence premise is hidden here. -/
theorem one_sub_evenPartialSum_eq_firstInterval_add_residuals
    {m : ℕ} (hm : 1 ≤ m) {s : ℝ} (hs2 : 2 ≤ s) (hs4 : s ≤ 4) :
    1 - suzukiEvenSourceLowerPartialSum m s =
      SuzukiFiniteContinuousLayers.suzukiLowerSieveFactorFirstInterval s +
        suzukiFiniteLowerBoundary m / s +
        (suzukiFiniteLowerAmplitude m -
            SuzukiFiniteContinuousLayers.suzukiLowerSieveAmplitude) / s *
          (∫ t in (2 : ℝ)..s, (t - 1)⁻¹) := by
  have hcon := suzuki_even_partial_finite_conservation hm hs2 hs4
  rw [SuzukiFiniteContinuousLayers.suzukiLowerSieveFactorFirstInterval]
  change 1 - suzukiEvenSourceLowerPartialSum m s =
    SuzukiFiniteContinuousLayers.suzukiLowerSieveAmplitude / s *
        (∫ t in (2 : ℝ)..s, (t - 1)⁻¹) +
      suzukiFiniteLowerBoundary m / s +
      (suzukiFiniteLowerAmplitude m -
          SuzukiFiniteContinuousLayers.suzukiLowerSieveAmplitude) / s *
        (∫ t in (2 : ℝ)..s, (t - 1)⁻¹)
  have hs0 : s ≠ 0 := ne_of_gt (by linarith)
  simp only [inv_eq_one_div] at hcon
  field_simp
  linear_combination -hcon


end MathlibNt.SieveTheory

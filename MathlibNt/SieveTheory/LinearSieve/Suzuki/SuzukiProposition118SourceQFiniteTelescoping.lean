import MathlibNt.SieveTheory.LinearSieve.Suzuki.SuzukiProposition118FinitePrefixPairing

/-!
# Finite source-Q weighted derivatives and telescoping

This module closes the finite, source-level calculus behind Suzuki Proposition
9.3(iii) and Proposition 9.4(vi), specialized to `κ = 1`, `β = 2`.

The base layer is kept separate.  On `2 < s < 3`, its weighted derivative is
`-1`; this is the term which combines with the even-layer derivatives to recover
the prescribed history `Q(s-1) = A_m/(s-1)`.  Above `3`, the ordinary layer
recurrences telescope, leaving only the last even layer.
-/

open scoped Classical BigOperators Interval
open Finset Set Filter Topology MeasureTheory intervalIntegral

namespace MathlibNt.SieveTheory

open SuzukiFiniteContinuousLayers

set_option autoImplicit false
set_option maxHeartbeats 800000

/-- The exceptional `f₁` derivative on the first source strip.  This is the
base term used in the `2 < s < 3` finite-`Q` equation. -/
theorem hasDerivAt_weighted_suzukiLayer_one_one_two_of_lt_three
    {s : ℝ} (hs0 : 0 < s) (hs3 : s < 3) :
    HasDerivAt (fun u => u * suzukiLayer 1 2 1 u) (-1) s := by
  have hlin : HasDerivAt (fun u : ℝ => 3 - u) (-1) s := by
    exact (hasDerivAt_id s).const_sub 3
  apply hlin.congr_of_eventuallyEq
  filter_upwards [Ioi_mem_nhds hs0, Iio_mem_nhds hs3] with u hu0 hu3
  change 0 < u at hu0
  change u < 3 at hu3
  rw [SuzukiFiniteContinuousLayers.suzukiLayer_one_one_two hu0 hu3.le]
  field_simp [ne_of_gt hu0]

/-- Above the support endpoint of `f₁`, its weighted derivative is zero. -/
theorem hasDerivAt_weighted_suzukiLayer_one_one_two_of_three_lt
    {s : ℝ} (hs3 : 3 < s) :
    HasDerivAt (fun u => u * suzukiLayer 1 2 1 u) 0 s := by
  apply (hasDerivAt_const s 0).congr_of_eventuallyEq
  filter_upwards [Ioi_mem_nhds hs3] with u hu
  rw [SuzukiFiniteContinuousLayers.suzukiLayer_one_one_two_eq_zero_of_three_le hu.le,
    mul_zero]

/-- The ordinary recursive weighted derivative, stated separately from the
exceptional base layer. -/
theorem hasDerivAt_weighted_suzukiLayer_one_two_of_two_le
    {s : ℝ} {n : ℕ} (hn : 2 ≤ n)
    (hs : 2 + sourceEpsilon n < s) :
    HasDerivAt (fun u => u * suzukiLayer 1 2 n u)
      (-suzukiLayer 1 2 (n - 1) (s - 1)) s := by
  exact hasDerivAt_weighted_suzukiLayer_of_threshold_lt
    (by norm_num : (1 : ℝ) < 2) hn hs

/-- The even predecessors of the first `m` odd layers are exactly the first
`m` even layers with the terminal even layer removed.  This is the finite
index telescope in Proposition 9.3(iii). -/
theorem sum_range_suzukiLayer_even_predecessors
    (m : ℕ) (x : ℝ) :
    (∑ k ∈ Finset.range m, suzukiLayer 1 2 (2 * k) x) =
      suzukiEvenSourceLowerPartialSum m x - suzukiLayer 1 2 (2 * m) x := by
  induction m with
  | zero => simp [suzukiEvenSourceLowerPartialSum]
  | succ m ih =>
      rw [Finset.sum_range_succ, ih]
      unfold suzukiEvenSourceLowerPartialSum
      rw [Finset.sum_range_succ]
      ring

/-- The predecessors of the first `m` even layers are exactly the first `m`
odd layers. -/
theorem sum_range_suzukiLayer_odd_predecessors
    (m : ℕ) (x : ℝ) :
    (∑ k ∈ Finset.range m,
      suzukiLayer 1 2 (2 * (k + 1) - 1) x) =
      suzukiOddSourceUpperPartialSum m x := by
  unfold suzukiOddSourceUpperPartialSum
  apply Finset.sum_congr rfl
  intro k _
  congr 2

private theorem hasDerivAt_weighted_evenPartialSum
    (m : ℕ) {s : ℝ} (hs2 : 2 < s) :
    HasDerivAt (fun u => u * suzukiEvenSourceLowerPartialSum m u)
      (-suzukiOddSourceUpperPartialSum m (s - 1)) s := by
  unfold suzukiEvenSourceLowerPartialSum
  have hsum : HasDerivAt
      (fun u => ∑ k ∈ Finset.range m,
        u * suzukiLayer 1 2 (2 * (k + 1)) u)
      (∑ k ∈ Finset.range m,
        -suzukiLayer 1 2 (2 * (k + 1) - 1) (s - 1)) s := by
    apply HasDerivAt.fun_sum
    intro k hk
    apply hasDerivAt_weighted_suzukiLayer_one_two_of_two_le
    · omega
    · have heps : sourceEpsilon (2 * (k + 1)) = 0 := by
        unfold sourceEpsilon
        omega
      rw [heps]
      norm_num
      exact hs2
  rw [Finset.sum_neg_distrib, sum_range_suzukiLayer_odd_predecessors] at hsum
  simpa only [Finset.mul_sum] using hsum

private theorem hasDerivAt_weighted_oddPartialSum_low
    {m : ℕ} (hm : 1 ≤ m) {s : ℝ} (hs1 : 1 < s) (hs3 : s < 3) :
    HasDerivAt (fun u => u * suzukiOddSourceUpperPartialSum m u) (-1) s := by
  have hlin : HasDerivAt (fun u : ℝ => suzukiFiniteLowerAmplitude m - u) (-1) s := by
    exact (hasDerivAt_id s).const_sub (suzukiFiniteLowerAmplitude m)
  apply hlin.congr_of_eventuallyEq
  filter_upwards [Ioi_mem_nhds hs1, Iio_mem_nhds hs3] with u hu1 hu3
  exact mul_suzukiOddSourceUpperPartialSum_eq_finiteAmplitude_sub
    hm hu1.le hu3.le

private theorem hasDerivAt_weighted_oddPartialSum_high
    (m : ℕ) {s : ℝ} (hs3 : 3 < s) :
    HasDerivAt (fun u => u * suzukiOddSourceUpperPartialSum m u)
      (-(suzukiEvenSourceLowerPartialSum m (s - 1) -
        suzukiLayer 1 2 (2 * m) (s - 1))) s := by
  unfold suzukiOddSourceUpperPartialSum
  have hsum : HasDerivAt
      (fun u => ∑ k ∈ Finset.range m,
        u * suzukiLayer 1 2 (2 * k + 1) u)
      (∑ k ∈ Finset.range m, -suzukiLayer 1 2 (2 * k) (s - 1)) s := by
    apply HasDerivAt.fun_sum
    intro k hk
    by_cases hk0 : k = 0
    · subst k
      simpa using hasDerivAt_weighted_suzukiLayer_one_one_two_of_three_lt hs3
    · have hn : 2 ≤ 2 * k + 1 := by omega
      have heps : sourceEpsilon (2 * k + 1) = 1 := by
        unfold sourceEpsilon
        omega
      have hpred : 2 * k + 1 - 1 = 2 * k := by omega
      simpa only [hpred] using
        hasDerivAt_weighted_suzukiLayer_one_two_of_two_le
          (s := s) hn (by rw [heps]; norm_num; exact hs3)
  rw [Finset.sum_neg_distrib, sum_range_suzukiLayer_even_predecessors] at hsum
  simpa only [Finset.mul_sum] using hsum

/-- On the missing window `2 < s < 3`, the finite source prefix satisfies the
exact weighted delay equation with no residual.  The `-1` from `f₁` is essential:
it turns `1 + T_{2m-1}(s-1)` into the prescribed history `A_m/(s-1)`. -/
theorem hasDerivAt_weighted_suzukiProposition118SourceQPrefix_low
    {m : ℕ} (hm : 1 ≤ m) {s : ℝ} (hs2 : 2 < s) (hs3 : s < 3) :
    HasDerivAt (fun u => u * suzukiProposition118SourceQPrefix m u)
      (-suzukiProposition118SourceQPrefix m (s - 1)) s := by
  have hodd := hasDerivAt_weighted_oddPartialSum_low hm
    (s := s) (by linarith) hs3
  have heven := hasDerivAt_weighted_evenPartialSum m hs2
  have hadd := hodd.add heven
  have hevent : (fun u =>
      u * suzukiOddSourceUpperPartialSum m u +
        u * suzukiEvenSourceLowerPartialSum m u) =ᶠ[𝓝 s]
      (fun u => u * suzukiProposition118SourceQPrefix m u) := by
    filter_upwards [Ioi_mem_nhds hs2] with u hu
    rw [suzukiProposition118SourceQPrefix, if_neg (not_lt.mpr hu.le)]
    ring
  have hmain := hadd.congr_of_eventuallyEq hevent.symm
  have hcoef :
      -1 + -suzukiOddSourceUpperPartialSum m (s - 1) =
        -suzukiProposition118SourceQPrefix m (s - 1) := by
    rw [suzukiProposition118SourceQPrefix, if_pos (by linarith : s - 1 < 2)]
    have hprev := mul_suzukiOddSourceUpperPartialSum_eq_finiteAmplitude_sub
      hm (u := s - 1) (by linarith) (by linarith)
    have hs1 : s - 1 ≠ 0 := ne_of_gt (by linarith)
    field_simp [hs1]
    linarith
  rw [hcoef] at hmain
  exact hmain

/-- Above the common differentiability threshold `3`, all recursive layers
differentiate and telescope; only the last even layer remains. -/
theorem hasDerivAt_weighted_suzukiProposition118SourceQPrefix_high
    (m : ℕ) {s : ℝ} (hs3 : 3 < s) :
    HasDerivAt (fun u => u * suzukiProposition118SourceQPrefix m u)
      (-suzukiProposition118SourceQPrefix m (s - 1) +
        suzukiLayer 1 2 (2 * m) (s - 1)) s := by
  have hodd := hasDerivAt_weighted_oddPartialSum_high m hs3
  have heven := hasDerivAt_weighted_evenPartialSum m (by linarith : 2 < s)
  have hadd := hodd.add heven
  have hevent : (fun u =>
      u * suzukiOddSourceUpperPartialSum m u +
        u * suzukiEvenSourceLowerPartialSum m u) =ᶠ[𝓝 s]
      (fun u => u * suzukiProposition118SourceQPrefix m u) := by
    filter_upwards [Ioi_mem_nhds (by linarith : 2 < s)] with u hu
    rw [suzukiProposition118SourceQPrefix, if_neg (not_lt.mpr hu.le)]
    ring
  have hmain := hadd.congr_of_eventuallyEq hevent.symm
  have hcoef :
      -(suzukiEvenSourceLowerPartialSum m (s - 1) -
          suzukiLayer 1 2 (2 * m) (s - 1)) +
          -suzukiOddSourceUpperPartialSum m (s - 1) =
        -suzukiProposition118SourceQPrefix m (s - 1) +
          suzukiLayer 1 2 (2 * m) (s - 1) := by
    rw [suzukiProposition118SourceQPrefix,
      if_neg (not_lt.mpr (by linarith : 2 ≤ s - 1))]
    ring
  rw [hcoef] at hmain
  exact hmain

/-- Unified finite telescoping equation away from the genuine source kink
`s = 3`.  The residual is exactly `suzukiProposition118SourceQTerminal`. -/
theorem hasDerivAt_weighted_suzukiProposition118SourceQPrefix
    {m : ℕ} (hm : 1 ≤ m) {s : ℝ} (hs2 : 2 < s) (hs3 : s ≠ 3) :
    HasDerivAt (fun u => u * suzukiProposition118SourceQPrefix m u)
      (-suzukiProposition118SourceQPrefix m (s - 1) +
        suzukiProposition118SourceQTerminal m s) s := by
  rcases lt_or_gt_of_ne hs3 with hslt | hsgt
  · rw [suzukiProposition118SourceQTerminal, if_neg (not_lt.mpr hslt.le), add_zero]
    exact hasDerivAt_weighted_suzukiProposition118SourceQPrefix_low hm hs2 hslt
  · rw [suzukiProposition118SourceQTerminal, if_pos hsgt]
    exact hasDerivAt_weighted_suzukiProposition118SourceQPrefix_high m hsgt


end MathlibNt.SieveTheory

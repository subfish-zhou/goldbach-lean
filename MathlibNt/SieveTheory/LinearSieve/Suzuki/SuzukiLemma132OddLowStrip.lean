import MathlibNt.SieveTheory.LinearSieve.Suzuki.SuzukiFiniteSourceLayerProp93

open scoped Classical BigOperators Interval
open Filter Finset MeasureTheory Set Topology

namespace MathlibNt.SieveTheory

open SuzukiFiniteContinuousLayers

set_option autoImplicit false

private lemma suzukiLayerNumerator_eq_sourceRecursion_of_two_le
    (β s : ℝ) {n : ℕ} (hn : 2 ≤ n) :
    suzukiLayerNumerator 1 β n s =
      ∫ t in recursionLower β s n..(β + n),
        suzukiLayer 1 β (n - 1) (t - 1) := by
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 2 := ⟨n - 2, by omega⟩
  simpa [dPowDensity, Nat.cast_add, Nat.cast_ofNat] using
    suzukiLayerNumerator_succ_succ (1 : ℝ) β s k

private lemma weighted_suzukiLayer_odd_lowStrip
    {n : ℕ} (hn : 3 ≤ n) (hodd : n % 2 = 1)
    {x : ℝ} (hx0 : 0 < x) (hx3 : x ≤ 3) :
    x * suzukiLayer 1 2 n x = 3 * suzukiLayer 1 2 n 3 := by
  have hlowerx : recursionLower 2 x n = 3 := by
    unfold recursionLower sourceEpsilon
    rw [hodd]
    norm_num
    rw [max_eq_right hx3]
    apply min_eq_left
    have hnR : (3 : ℝ) ≤ n := by exact_mod_cast hn
    linarith
  have hlower3 : recursionLower 2 3 n = 3 := by
    unfold recursionLower sourceEpsilon
    rw [hodd]
    norm_num
    have hnR : (3 : ℝ) ≤ n := by exact_mod_cast hn
    linarith
  have hnum : suzukiLayerNumerator 1 2 n x =
      suzukiLayerNumerator 1 2 n 3 := by
    rw [suzukiLayerNumerator_eq_sourceRecursion_of_two_le 2 x (by omega),
      suzukiLayerNumerator_eq_sourceRecursion_of_two_le 2 3 (by omega),
      hlowerx, hlower3]
  rw [suzukiLayer_eq_inv_rpow_mul_numerator,
    suzukiLayer_eq_inv_rpow_mul_numerator,
    show x ^ (1 : ℝ) = x by norm_num,
    show (3 : ℝ) ^ (1 : ℝ) = 3 by norm_num,
    ← mul_assoc, mul_inv_cancel₀ hx0.ne', one_mul,
    ← mul_assoc]
  norm_num [hnum]

private lemma weighted_suzukiLayer_one_lowStrip
    {x : ℝ} (hx0 : 0 < x) (hx3 : x ≤ 3) :
    x * suzukiLayer 1 2 1 x = 3 - x := by
  rw [suzukiLayer_one]
  norm_num [baseLower, min_eq_left hx3, dPowDensity]
  field_simp

/-- For every odd finite depth at least three, the part of the weighted source
layer visible below the recursive clamp `3` consists exactly of the first-layer
segment `3 - x`; every higher odd summand has the same weighted numerator as at
`x = 3`. -/
theorem finiteSourceLayer_odd_lowStrip_exact
    (N : ℕ) (x : ℝ) (hN : 3 ≤ N) (hodd : N % 2 = 1)
    (hx1 : 1 < x) (hx3 : x ≤ 3) :
    x * finiteSourceLayer 1 2 N x =
      (3 - x) + 3 * finiteSourceLayer 1 2 N 3 := by
  classical
  have hx0 : 0 < x := by linarith
  have hbase := weighted_suzukiLayer_one_lowStrip hx0 hx3
  let S : Finset ℕ := Finset.Icc 1 N
  have hmem : 1 ∈ S := by
    simp [S]
    omega
  have hpoint : ∀ n ∈ S,
      x * (if n % 2 = N % 2 then suzukiLayer 1 2 n x else 0) =
        (if n = 1 then 3 - x else 0) +
          3 * (if n % 2 = N % 2 then suzukiLayer 1 2 n 3 else 0) := by
    intro n hn
    by_cases hn1 : n = 1
    · subst n
      have hz : suzukiLayer 1 2 1 3 = 0 := by
        apply suzukiLayer_eq_zero_of_le
        norm_num
      simp only [Nat.one_mod, hodd, if_true, hz, mul_zero, add_zero]
      exact hbase
    · by_cases hnpar : n % 2 = N % 2
      · have hnodd : n % 2 = 1 := by omega
        have hnIcc : n ∈ Finset.Icc 1 N := hn
        have hn3 : 3 ≤ n := by
          have hn_ge_one : 1 ≤ n := (Finset.mem_Icc.mp hnIcc).1
          omega
        simp only [hn1, if_false, zero_add, hnpar, if_true]
        exact weighted_suzukiLayer_odd_lowStrip hn3 hnodd hx0 hx3
      · simp [hn1, hnpar]
  have hfirst : (∑ n ∈ S, if n = 1 then (3 - x) else 0) = 3 - x := by
    simp [hmem]
  unfold finiteSourceLayer
  change x * (∑ n ∈ S,
      if n % 2 = N % 2 then suzukiLayer 1 2 n x else 0) =
    (3 - x) + 3 * (∑ n ∈ S,
      if n % 2 = N % 2 then suzukiLayer 1 2 n 3 else 0)
  rw [Finset.mul_sum]
  calc
    (∑ n ∈ S,
        x * (if n % 2 = N % 2 then suzukiLayer 1 2 n x else 0)) =
        ∑ n ∈ S, ((if n = 1 then 3 - x else 0) +
          3 * (if n % 2 = N % 2 then suzukiLayer 1 2 n 3 else 0)) := by
      apply Finset.sum_congr rfl
      exact hpoint
    _ = (∑ n ∈ S, if n = 1 then 3 - x else 0) +
        ∑ n ∈ S, 3 * (if n % 2 = N % 2 then suzukiLayer 1 2 n 3 else 0) := by
      rw [Finset.sum_add_distrib]
    _ = (3 - x) + 3 * (∑ n ∈ S,
        if n % 2 = N % 2 then suzukiLayer 1 2 n 3 else 0) := by
      rw [hfirst, Finset.mul_sum]


end MathlibNt.SieveTheory

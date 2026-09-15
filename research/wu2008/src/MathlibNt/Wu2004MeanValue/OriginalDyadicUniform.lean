import MathlibNt.Wu2004MeanValue.OriginalDyadicSummation

/-! One threshold is chosen before every retained scale and logarithmic sieve
exponent. This is the uniformity needed before the moving dyadic sum. -/

namespace Wu2004MeanValue

open Filter

noncomputable section

theorem dyadicScale_twice_le {η x : ℝ} (hη : 0 < η) (hx : 0 < x) (j : ℕ) :
    2 * dyadicScale η x j ≤ η * x := by
  have h := dyadicScale_antitone hη hx (Nat.zero_le j)
  rw [dyadicScale_zero] at h
  linarith

theorem real_block_cutoff_le_half {x H B : ℝ} (hx : 16 ≤ x)
    (hupper : 2 * H ≤ x) (hlog : 1 ≤ Real.log (2 * H)) (hB : 0 ≤ B) :
    Real.sqrt (Real.sqrt (2 * H) / Real.log (2 * H) ^ B) ≤ x / 2 := by
  have hsx : Real.sqrt x ≤ x / 2 := Real.sqrt_le_iff.mpr ⟨by linarith, by nlinarith⟩
  have hlevel : Real.sqrt (2 * H) / Real.log (2 * H) ^ B ≤ x := by
    calc
      _ ≤ Real.sqrt (2 * H) :=
        div_le_self (Real.sqrt_nonneg _) (Real.one_le_rpow hlog hB)
      _ ≤ Real.sqrt x := Real.sqrt_le_sqrt hupper
      _ ≤ x := by linarith
  exact (Real.sqrt_le_sqrt hlevel).trans hsx

theorem half_lt_sub_of_small_product {η x t : ℝ} (hx : 0 < x)
    (hη : η < 1 / 2) (ht : t ≤ η * x) :
    x / 2 < x - t := by
  nlinarith [mul_lt_mul_of_pos_right hη hx]

/-- At one common eventual threshold, every retained scale passes an arbitrary
fixed block threshold. Cutoff control is uniform even in all `B ≥ 0`. -/
theorem eventually_dyadic_uniform (η H₀ : ℝ) (hη : 0 < η) (hη2 : η < 1 / 2) :
    ∀ᶠ x : ℝ in atTop,
      16 ≤ x ∧ Real.sqrt x ≤ dyadicScale η x 0 ∧
        ∀ j ≤ dyadicLast η x,
          H₀ < dyadicScale η x j ∧
          Real.sqrt x / 2 ≤ dyadicScale η x j ∧
          2 * dyadicScale η x j ≤ η * x ∧
          Real.log x / 4 ≤ Real.log (dyadicScale η x j) ∧
          1 ≤ Real.log (2 * dyadicScale η x j) ∧
          ∀ B : ℝ, 0 ≤ B →
            Real.sqrt (Real.sqrt (2 * dyadicScale η x j) /
              Real.log (2 * dyadicScale η x j) ^ B) ≤ x / 2 := by
  filter_upwards [eventually_ge_atTop (16 : ℝ),
    Real.tendsto_sqrt_atTop.eventually (eventually_ge_atTop (2 / η)),
    Real.tendsto_sqrt_atTop.eventually (eventually_gt_atTop (2 * H₀)),
    Real.tendsto_sqrt_atTop.eventually (eventually_ge_atTop (Real.exp 1))]
    with x hx hηsqrt hHsqrt hexp
  have hx0 : 0 < x := by linarith
  have hs0 := Real.sqrt_nonneg x
  have hfirst : Real.sqrt x ≤ dyadicScale η x 0 := by
    have hm := (div_le_iff₀ hη).mp hηsqrt
    have hp := mul_le_mul_of_nonneg_right hm hs0
    have heq : Real.sqrt x * η * Real.sqrt x = η * x := by
      calc
        _ = η * (Real.sqrt x * Real.sqrt x) := by ring
        _ = η * x := by rw [Real.mul_self_sqrt hx0.le]
    rw [heq] at hp
    rw [dyadicScale_zero]
    linarith
  refine ⟨hx, hfirst, ?_⟩
  intro j hj
  have hlower := dyadicScale_retained_lower hη hx0 hfirst hj
  have hupper := dyadicScale_twice_le hη hx0 j
  have hlog : 1 ≤ Real.log (2 * dyadicScale η x j) := by
    calc
      1 = Real.log (Real.exp 1) := (Real.log_exp 1).symm
      _ ≤ Real.log (2 * dyadicScale η x j) :=
        Real.log_le_log (Real.exp_pos 1) (by linarith)
  refine ⟨by linarith, hlower, hupper,
    dyadicScale_log_lower hη hx hfirst hj, hlog, ?_⟩
  intro B hB
  exact real_block_cutoff_le_half hx (by nlinarith) hlog hB

/-- Real threshold version, including the already-proved moving-sum and
absolute logarithmic block-count bounds. -/
theorem dyadic_uniform_threshold (η H₀ : ℝ) (hη : 0 < η) (hη2 : η < 1 / 2) :
    ∃ x₀ : ℝ, 16 ≤ x₀ ∧ ∀ x : ℝ, x₀ ≤ x →
      Real.sqrt x ≤ dyadicScale η x 0 ∧
      (∀ j ≤ dyadicLast η x,
        H₀ < dyadicScale η x j ∧
        Real.sqrt x / 2 ≤ dyadicScale η x j ∧
        2 * dyadicScale η x j ≤ η * x ∧
        Real.log x / 4 ≤ Real.log (dyadicScale η x j) ∧
        ∀ B : ℝ, 0 ≤ B →
          Real.sqrt (Real.sqrt (2 * dyadicScale η x j) /
            Real.log (2 * dyadicScale η x j) ^ B) ≤ x / 2) ∧
      (∑ j ∈ Finset.range (dyadicLast η x + 1),
        dyadicScale η x j / Real.log (dyadicScale η x j) ^ 2) ≤
          16 * η * x / Real.log x ^ 2 ∧
      ((dyadicLast η x + 1 : ℕ) : ℝ) ≤ (1 / Real.log 2) * Real.log x := by
  obtain ⟨T, hT⟩ := eventually_atTop.mp (eventually_dyadic_uniform η H₀ hη hη2)
  refine ⟨max 16 T, le_max_left _ _, ?_⟩
  intro x hx
  obtain ⟨hx16, hfirst, hj⟩ := hT x ((le_max_right _ _).trans hx)
  refine ⟨hfirst, ?_, sum_dyadicScale_div_log_sq_le hη hx16 hfirst,
    dyadicLast_add_one_le_log hη (by linarith) hx16 hfirst⟩
  intro j hjJ
  obtain ⟨hthreshold, hlower, hupper, hlog, _, hcut⟩ := hj j hjJ
  exact ⟨hthreshold, hlower, hupper, hlog, hcut⟩

/-- Natural `N` version with the threshold preceding the index and sieve
exponent. No pointwise eventual estimate is invoked inside a finite sum. -/
theorem dyadic_uniform_nat_threshold (η H₀ : ℝ) (hη : 0 < η)
    (hη2 : η < 1 / 2) :
    ∃ N₀ : ℕ, 16 ≤ N₀ ∧ ∀ N : ℕ, N₀ ≤ N →
      Real.sqrt (N : ℝ) ≤ dyadicScale η N 0 ∧
      (∀ j ≤ dyadicLast η N,
        H₀ < dyadicScale η N j ∧
        Real.sqrt (N : ℝ) / 2 ≤ dyadicScale η N j ∧
        2 * dyadicScale η N j ≤ η * N ∧
        Real.log (N : ℝ) / 4 ≤ Real.log (dyadicScale η N j) ∧
        ∀ B : ℝ, 0 ≤ B →
          Real.sqrt (Real.sqrt (2 * dyadicScale η N j) /
            Real.log (2 * dyadicScale η N j) ^ B) ≤ (N : ℝ) / 2) ∧
      (∑ j ∈ Finset.range (dyadicLast η N + 1),
        dyadicScale η N j / Real.log (dyadicScale η N j) ^ 2) ≤
          16 * η * N / Real.log (N : ℝ) ^ 2 ∧
      ((dyadicLast η N + 1 : ℕ) : ℝ) ≤ (1 / Real.log 2) * Real.log (N : ℝ) := by
  obtain ⟨x₀, hx₀, h⟩ := dyadic_uniform_threshold η H₀ hη hη2
  obtain ⟨n, hn⟩ := exists_nat_gt x₀
  refine ⟨max 16 n, le_max_left _ _, ?_⟩
  intro N hN
  apply h
  have hcast : (n : ℝ) ≤ N := by exact_mod_cast (le_max_right 16 n).trans hN
  exact hn.le.trans hcast

end
end Wu2004MeanValue

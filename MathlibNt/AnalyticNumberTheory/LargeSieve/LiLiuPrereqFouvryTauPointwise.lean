import MathlibNt.AnalyticNumberTheory.LargeSieve.LiLiuPrereqFouvryWeilBridge

/-!
# Fixed-order divisor coefficients are subpolynomial

The proved moment estimate, with an arbitrarily large fixed moment, pays
every positive power. No divisor bound is assumed.
-/

noncomputable section

open Finset Filter
open scoped Topology

namespace MathlibNt.AnalyticNumberTheory.LargeSieve.LiLiuPrereqFouvry

theorem eventually_fouvryTau_le_rpow {k : ℕ} (hk : 1 ≤ k)
    {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ n : ℕ in atTop, (fouvryTau k n : ℝ) ≤ (n : ℝ) ^ ε := by
  obtain ⟨r, hr⟩ := exists_nat_gt (1 / ε)
  have hr0 : r ≠ 0 := by
    intro h
    subst r
    simp only [Nat.cast_zero] at hr
    have := one_div_pos.mpr hε
    linarith
  have hgap : 0 < ε * r - 1 := by
    have := (div_lt_iff₀ hε).mp hr
    nlinarith
  let K := k ^ r - 1
  have hs : (fun x : ℝ ↦ Real.log x ^ K) =o[atTop]
      (fun x ↦ x ^ (ε * r - 1)) := by
    simpa only [Real.rpow_natCast] using isLittleO_log_rpow_rpow_atTop (K : ℕ) hgap
  have hb := (hs.const_mul_left ((2 : ℝ) ^ K)).bound (by norm_num : (0 : ℝ) < 1)
  have hevent : ∀ᶠ x : ℝ in atTop,
      1 ≤ Real.log x ∧ 1 ≤ x ∧ 2 ^ K * Real.log x ^ K ≤ x ^ (ε * r - 1) := by
    filter_upwards [hb, Real.tendsto_log_atTop.eventually_ge_atTop 1,
      eventually_ge_atTop (1 : ℝ)] with x hx hl hx1
    refine ⟨hl, hx1, ?_⟩
    simpa only [Real.norm_eq_abs, abs_of_nonneg (by positivity :
      0 ≤ (2 : ℝ) ^ K * Real.log x ^ K),
      abs_of_nonneg (Real.rpow_nonneg (by linarith : 0 ≤ x) _), one_mul] using hx
  filter_upwards [tendsto_natCast_atTop_atTop.eventually hevent,
    eventually_ge_atTop (1 : ℕ)] with n hn hn1
  rcases hn with ⟨hlog, hnR, hpay⟩
  have hn0 : (0 : ℝ) < n := by positivity
  apply le_of_pow_le_pow_left₀ hr0 (Real.rpow_nonneg hn0.le ε)
  calc
    (fouvryTau k n : ℝ) ^ r ≤ (n : ℝ) * (1 + Real.log n) ^ K :=
      fouvryTau_pow_pointwise k r hk (by omega)
    _ ≤ (n : ℝ) * (2 * Real.log n) ^ K := by gcongr; linarith
    _ = (n : ℝ) * (2 ^ K * Real.log n ^ K) := by rw [mul_pow]
    _ ≤ (n : ℝ) * (n : ℝ) ^ (ε * r - 1) :=
      mul_le_mul_of_nonneg_left hpay hn0.le
    _ = ((n : ℝ) ^ ε) ^ r := by
      rw [← Real.rpow_mul_natCast hn0.le, mul_comm (n : ℝ),
        ← Real.rpow_add_one hn0.ne', sub_add_cancel]

/-- The constant depends only on the fixed order and exponent. -/
theorem fouvryTau_le_const_rpow {k : ℕ} (hk : 1 ≤ k)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ n : ℕ, 0 < n →
      (fouvryTau k n : ℝ) ≤ C * (n : ℝ) ^ ε := by
  obtain ⟨N, hN⟩ := eventually_atTop.mp (eventually_fouvryTau_le_rpow hk hε)
  let C : ℝ := 1 + ∑ n ∈ range N, (fouvryTau k n : ℝ)
  have hC : 1 ≤ C := le_add_of_nonneg_right (by positivity)
  refine ⟨C, zero_lt_one.trans_le hC, fun n hn ↦ ?_⟩
  by_cases hlarge : N ≤ n
  · exact (hN n hlarge).trans (le_mul_of_one_le_left (by positivity) hC)
  · have hsmall : (fouvryTau k n : ℝ) ≤ C := by
      have := single_le_sum (f := fun n ↦ (fouvryTau k n : ℝ))
        (s := range N) (fun _ _ ↦ by positivity) (mem_range.mpr (by omega : n < N))
      dsimp [C]
      linarith
    exact hsmall.trans (le_mul_of_one_le_right (by linarith)
      (Real.one_le_rpow (by exact_mod_cast hn : (1 : ℝ) ≤ n) hε.le))

end MathlibNt.AnalyticNumberTheory.LargeSieve.LiLiuPrereqFouvry

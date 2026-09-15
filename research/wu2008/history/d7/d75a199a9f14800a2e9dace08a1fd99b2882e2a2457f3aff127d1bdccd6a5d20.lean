import MathlibNt.Wu2004MeanValue.ManuscriptPairs

/-!
# Direct integral estimates for the manuscript's moving block endpoints

All endpoints are the literal max/min expressions from `ManuscriptPairs`.
The lower prime argument is `max (H / m) m`, hence at least `sqrt H`.
The integral estimate below uses no asymptotic formula for li.
-/

namespace Wu2004MeanValue

open Finset
open MathlibNt.SieveTheory.LiuWeight

theorem blockLower_div_eq_max {H : ℝ} {m : ℕ} (hm : 0 < m) :
    blockLower H m / m = max (H / m) (m : ℝ) := by
  have hm0 : (0 : ℝ) < m := by exact_mod_cast hm
  rw [blockLower, ← max_div_div_right hm0.le]
  congr 1
  field_simp

theorem sqrt_le_blockLower_div {H : ℝ} {m : ℕ} (hH : 0 ≤ H) (hm : 0 < m) :
    Real.sqrt H ≤ blockLower H m / m := by
  rw [blockLower_div_eq_max hm]
  by_cases hsm : Real.sqrt H ≤ (m : ℝ)
  · exact hsm.trans (le_max_right _ _)
  · apply le_trans _ (le_max_left _ _)
    have hm0 : (0 : ℝ) < m := by exact_mod_cast hm
    apply (le_div_iff₀ hm0).mpr
    calc
      Real.sqrt H * m ≤ Real.sqrt H * Real.sqrt H :=
        mul_le_mul_of_nonneg_left (le_of_not_ge hsm) (Real.sqrt_nonneg H)
      _ = H := by nlinarith [Real.sq_sqrt hH]

private theorem block_wuLi_difference_eq_integral {l u : ℝ}
    (hl : 2 ≤ l) (hlu : l ≤ u) :
    wuLi u - wuLi l = ∫ t in l..u, 1 / Real.log t := by
  have hi := liuLogarithmicIntegrand_intervalIntegrable hl
  have hj := liuLogarithmicIntegrand_intervalIntegrable_of_two_le hl hlu
  have h := intervalIntegral.integral_add_adjacent_intervals hi hj
  simp only [wuLi, liuLogarithmicIntegral, zero_add]
  linarith

/-- Nonempty-source filtering alone ensures nonnegativity, even before an
asymptotic threshold and without any restriction on `eta`. -/
theorem blockMass_nonneg (H : ℝ) (N : ℕ) (a η : ℝ) :
    0 ≤ blockMass H N a η := by
  unfold blockMass intervalMass
  apply sum_nonneg
  intro m hm
  have hs := mem_blockSource.mp hm
  have hd := block_prime_endpoint_domain H N a η m hs.1 hs.2.2.2.2
  have hlu := div_le_div_of_nonneg_right hs.2.2.2.2.le (Nat.cast_nonneg m)
  rw [block_wuLi_difference_eq_integral hd.1.1 hlu]
  exact intervalIntegral.integral_nonneg hlu
    (fun t ht => liuLogarithmicIntegrand_nonneg (hd.1.1.trans ht.1))

/-- Each actual nonempty interval contributes at most `4H/(m log H)`.
Both moving endpoints remain in the left-hand side. -/
theorem blockMass_term_le {H : ℝ} {N m : ℕ} {a η : ℝ}
    (hH : 1 < H) (hm : m ∈ blockSource H N a η) :
    wuLi (blockUpper H N a η m / m) - wuLi (blockLower H m / m) ≤
      (4 * H / Real.log H) * (1 / (m : ℝ)) := by
  have hs := mem_blockSource.mp hm
  have hm0 : (0 : ℝ) < m := by exact_mod_cast hs.1.pos
  have hd := block_prime_endpoint_domain H N a η m hs.1 hs.2.2.2.2
  have hlu := div_le_div_of_nonneg_right hs.2.2.2.2.le hm0.le
  have hlog : 0 < Real.log H := Real.log_pos hH
  have hsqrt := sqrt_le_blockLower_div (by linarith : 0 ≤ H) hs.1.pos
  rw [block_wuLi_difference_eq_integral hd.1.1 hlu]
  calc
    (∫ t in (blockLower H m / m)..(blockUpper H N a η m / m),
        1 / Real.log t) ≤
        ∫ _t in (blockLower H m / m)..(blockUpper H N a η m / m),
          2 / Real.log H := by
      apply intervalIntegral.integral_mono_on hlu
        (liuLogarithmicIntegrand_intervalIntegrable_of_two_le hd.1.1 hlu)
        intervalIntegrable_const
      intro t ht
      calc
        1 / Real.log t ≤ 1 / (Real.log H / 2) := by
          apply one_div_le_one_div_of_le (by positivity)
          calc
            Real.log H / 2 = Real.log (Real.sqrt H) :=
              (Real.log_sqrt (by linarith)).symm
            _ ≤ Real.log t := Real.log_le_log
              (Real.sqrt_pos.mpr (by linarith)) (hsqrt.trans ht.1)
        _ = 2 / Real.log H := by field_simp
    _ = (blockUpper H N a η m / m - blockLower H m / m) *
        (2 / Real.log H) := by
      simp only [intervalIntegral.integral_const, smul_eq_mul]
    _ ≤ (2 * H / m) * (2 / Real.log H) := by
      apply mul_le_mul_of_nonneg_right _ (by positivity)
      have hu : blockUpper H N a η m ≤ 2 * H :=
        (min_le_left _ _).trans (min_le_left _ _)
      have hquot := div_le_div_of_nonneg_right hu hm0.le
      linarith [hd.1.1]
    _ = (4 * H / Real.log H) * (1 / (m : ℝ)) := by ring

end Wu2004MeanValue

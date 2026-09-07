import MathlibNt.AnalyticNumberTheory.LargeSieve.LiLiuPrereqFouvryWModulusSupportPaymentDyadic

noncomputable section
open Filter
namespace MathlibNt.AnalyticNumberTheory.LargeSieve.LiLiuPrereqFouvry

/-- The enlarged short-variable range still pays the progression endpoint. -/
theorem kModSupport_eventually_level_le_long :
    ∀ᶠ x : ℝ in atTop, ∀ M T L : ℝ,
      0 < T → 4 * M * T = x → T ≤ x ^ (1 / 9 : ℝ) →
      L ≤ x ^ (5 / 9 : ℝ) → L ≤ M := by
  filter_upwards [betaPayment_eventually_log_mul_rpow_le 4 (by norm_num) 0
    (b := (1 / 9 : ℝ) + 5 / 9) (d := 1) (by norm_num),
    eventually_gt_atTop (0 : ℝ)] with x hlong hx
  intro M T L hT hscale hhigh hlevel
  apply hlevel.trans
  have hbound : 4 * T * x ^ (5 / 9 : ℝ) ≤ 4 * T * M := by
    calc
      _ ≤ 4 * x ^ (1 / 9 : ℝ) * x ^ (5 / 9 : ℝ) := by gcongr
      _ = 4 * x ^ ((1 / 9 : ℝ) + 5 / 9) := by
        rw [mul_assoc, ← Real.rpow_add hx]
      _ ≤ x := by simpa only [pow_zero, mul_one, Real.rpow_one] using hlong
      _ = _ := by rw [← hscale]; ring
  exact le_of_mul_le_mul_left hbound (by positivity)

end MathlibNt.AnalyticNumberTheory.LargeSieve.LiLiuPrereqFouvry

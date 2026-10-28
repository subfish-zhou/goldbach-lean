import MathlibNt.SieveTheory.LinearSieve.Suzuki.SuzukiCaseIISourceSigmaDecay

namespace MathlibNt.SieveTheory.SwitchingPrinciple.SuzukiLemma144KappaOne

/-- The real-power source bracket loses at least its linear tangent gap.
This is the weighted AM--GM (equivalently, concavity/Bernoulli) inequality. -/
theorem rpow_contraction_gap
    {Δ σ : ℝ} (hΔ0 : 0 < Δ) (hΔ1 : Δ < 1) (hσ : 1 < σ) :
    (1 - Δ) / σ ≤ 1 - (1 - 1 / σ) ^ (1 - Δ) := by
  have hσ0 : 0 < σ := zero_lt_one.trans hσ
  have hbase0 : 0 ≤ 1 - 1 / σ := by
    rw [sub_nonneg, div_le_one hσ0]
    exact hσ.le
  have hamgm := Real.geom_mean_le_arith_mean2_weighted
    (show 0 ≤ 1 - Δ by linarith) hΔ0.le hbase0 (show 0 ≤ (1 : ℝ) by norm_num)
    (show (1 - Δ) + Δ = 1 by ring)
  rw [Real.one_rpow, mul_one] at hamgm
  calc
    (1 - Δ) / σ = 1 - ((1 - Δ) * (1 - 1 / σ) + Δ * 1) := by
      field_simp [ne_of_gt hσ0]
      ring
    _ ≤ 1 - (1 - 1 / σ) ^ (1 - Δ) := sub_le_sub_left hamgm 1

/-- For every positive source exponent parameter, Suzuki's exact cutoff is
strictly larger than one beyond the explicit threshold `exp (exp 1)`. -/
theorem sourceSigma_gt_one_of_large
    {D d : ℝ} (hd : 0 < d) (hD : Real.exp (Real.exp 1) ≤ D) :
    1 < sourceSigma D d := by
  have hDpos : 0 < D := (Real.exp_pos (Real.exp 1)).trans_le hD
  have hlogExp : Real.exp 1 ≤ Real.log D :=
    (Real.le_log_iff_exp_le hDpos).2 hD
  have hexp1 : 1 < Real.exp 1 := Real.one_lt_exp_iff.mpr zero_lt_one
  have hlog1 : 1 ≤ Real.log D := (le_of_lt hexp1).trans hlogExp
  have hlog27D : Real.log (27 * D) = Real.log 27 + Real.log D := by
    rw [Real.log_mul (by norm_num : (27 : ℝ) ≠ 0) (ne_of_gt hDpos)]
  have hlog27pos : 0 < Real.log (27 : ℝ) := Real.log_pos (by norm_num)
  have hinnerpos : 0 < Real.log (27 * D) := by
    rw [hlog27D]
    positivity
  have hinnerexp : Real.exp 1 < Real.log (27 * D) := by
    rw [hlog27D]
    linarith
  have hll1 : 1 < Real.log (Real.log (27 * D)) :=
    (Real.lt_log_iff_exp_lt hinnerpos).2 hinnerexp
  have hfirst1 : 1 ≤ (Real.log D) ^ (1 / d) :=
    Real.one_le_rpow hlog1 (one_div_nonneg.mpr hd.le)
  have hfirstpos : 0 < (Real.log D) ^ (1 / d) := by positivity
  rw [sourceSigma]
  calc
    1 ≤ (Real.log D) ^ (1 / d) := hfirst1
    _ < (Real.log D) ^ (1 / d) * Real.log (Real.log (27 * D)) := by
      simpa only [mul_one] using mul_lt_mul_of_pos_left hll1 hfirstpos


end MathlibNt.SieveTheory.SwitchingPrinciple.SuzukiLemma144KappaOne

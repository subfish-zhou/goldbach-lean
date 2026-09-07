import MathlibNt.SieveTheory.LiLiuGoldbachPi10IntegralUpper
import MathlibNt.SieveTheory.LiLiuGoldbachG10SwitchBudget

namespace MathlibNt.SieveTheory.LiLiuOnePlusOneNine.GoldbachBig

/-- The separately named corrected G10 has the actual integral upper bound.
This does not identify the corrected count with the original printed G10. -/
theorem goldbachG10Corrected_I10_upper (δ : ℝ) (hδ : 0 < δ) :
    ∀ ε : ℝ, 0 < ε → ε < 1 →
      ∃ N₀ : ℕ, 4 ≤ N₀ ∧ ∀ N : ℕ, N₀ ≤ N → Even N →
        (goldbachG10Corrected (goldbachDifferenceCarrier N ε) N
          ((N : ℝ) ^ goldbachB10Beta) ((N : ℝ) ^ goldbachB10Gamma) : ℝ) ≤
          (8 * (1 - ε) * goldbachB10I10 + δ) *
            (MathlibNt.SieveTheory.SingularSeries.liuSingularSeries N * (N : ℝ) /
              Real.log (N : ℝ) ^ 2) := by
  have hδ2 : 0 < δ / 2 := by positivity
  obtain ⟨Ne, _hNe, he⟩ := goldbach_power_error_le_log_scale_eventually
    880 goldbachB10Beta ((δ / 2) * SingularSeries.liuUniversalProduct)
    (by norm_num) (by norm_num [goldbachB10Beta])
    (mul_pos hδ2 SingularSeries.liuUniversalProduct_pos)
  intro ε hε hεlt
  obtain ⟨Np, hNp, hp⟩ := goldbachPi10_I10_upper (δ / 2) hδ2 ε hε hεlt
  obtain ⟨Ng, hg⟩ := goldbachG10Corrected_eventually_le_pi10_add_880 ε hε
  refine ⟨max Np (max Ng Ne), hNp.trans (le_max_left _ _), ?_⟩
  intro N hN hEven
  have hNp' : Np ≤ N := (le_max_left _ _).trans hN
  have hNr : max Ng Ne ≤ N := (le_max_right _ _).trans hN
  have hNg : Ng ≤ N := (le_max_left _ _).trans hNr
  have hNe : Ne ≤ N := (le_max_right _ _).trans hNr
  let A := SingularSeries.liuSingularSeries N * (N : ℝ) / Real.log (N : ℝ) ^ 2
  have hraw : 880 * (N : ℝ) ^ (1 - goldbachB10Beta) ≤
      ((δ / 2) * SingularSeries.liuUniversalProduct) * ((N : ℝ) / Real.log (N : ℝ) ^ 2) := by
    simpa only [Real.rpow_two, mul_div_assoc] using he N hNe goldbachB10Beta le_rfl
  have hseries := mul_le_mul_of_nonneg_left
    (SingularSeries.liuUniversalProduct_le_liuSingularSeries N) hδ2.le
  have hscale : 0 ≤ (N : ℝ) / Real.log (N : ℝ) ^ 2 := by positivity
  have hpay : 880 * (N : ℝ) ^ (1 - goldbachB10Beta) ≤ (δ / 2) * A := by
    simpa only [A, mul_div_assoc, mul_assoc] using
      hraw.trans (mul_le_mul_of_nonneg_right hseries hscale)
  have hG := hg N hNg goldbachB10Beta goldbachB10Gamma
    (by norm_num [goldbachB10Beta])
    (by norm_num [goldbachB10Beta])
    (by norm_num [goldbachB10Beta, goldbachB10Gamma])
    (by norm_num [goldbachB10Gamma])
  have hP := hp N hNp' hEven
  change _ ≤ (8 * (1 - ε) * goldbachB10I10 + δ) * A
  calc
    _ ≤ (goldbachPi10 N ε ((N : ℝ) ^ goldbachB10Beta) ((N : ℝ) ^ goldbachB10Gamma) : ℝ) +
        880 * (N : ℝ) ^ (1 - goldbachB10Beta) := hG
    _ ≤ (8 * (1 - ε) * goldbachB10I10 + δ / 2) * A + (δ / 2) * A :=
      add_le_add hP hpay
    _ = _ := by ring

end MathlibNt.SieveTheory.LiLiuOnePlusOneNine.GoldbachBig
import RMapMDebitSubstitution

noncomputable section
open Real Set MeasureTheory Wu2008DoubleSieve
open scoped Interval

namespace WuPaper.RMapMDebit

theorem C8_large_integrable :
    IntervalIntegrable (fun t : ℝ => log (2 - 3 * t) / (t * (1 - t)))
      volume (1 / 10) (1 / 3) :=
  (SeventhEighth.eighth_integrand_continuous.mono (by
    intro t ht
    exact ⟨parameters.2.1.le.trans ht.1, ht.2⟩)).intervalIntegrable_of_Icc (by norm_num)

theorem C8_original_triangle :
    C8 =
      (36 / 5) * (∫ t in alpha..(1 / 10),
        (∫ v in (1 / 3 : ℝ)..((1 - t) / 2), SeventhEighth.classicalKernel t v) /
          (1 - t)) +
      8 * (∫ t in (1 / 10 : ℝ)..(1 / 3),
        ∫ v in (1 / 3 : ℝ)..((1 - t) / 2), SeventhEighth.classicalKernel t v) := by
  have hs : (∫ t in alpha..(1 / 10), log (2 - 3 * t) / (t * (1 - t)^2)) =
      ∫ t in alpha..(1 / 10),
        (∫ v in (1 / 3 : ℝ)..((1 - t) / 2), SeventhEighth.classicalKernel t v) /
          (1 - t) := by
    apply intervalIntegral.integral_congr
    intro t ht
    rw [uIcc_of_le parameters.2.1.le] at ht
    dsimp only
    rw [SeventhEighth.eighth_slice ⟨ht.1, ht.2.trans (by norm_num)⟩]
    ring
  have hl : (∫ t in (1 / 10 : ℝ)..(1 / 3), log (2 - 3 * t) / (t * (1 - t))) =
      ∫ t in (1 / 10 : ℝ)..(1 / 3),
        ∫ v in (1 / 3 : ℝ)..((1 - t) / 2), SeventhEighth.classicalKernel t v := by
    apply intervalIntegral.integral_congr
    intro t ht
    rw [uIcc_of_le (by norm_num : (1 / 10 : ℝ) ≤ 1 / 3)] at ht
    exact (SeventhEighth.eighth_slice ⟨parameters.2.1.le.trans ht.1, ht.2⟩).symm
  unfold C8
  rw [hs, hl]

theorem C9_original_triangle :
    C9 = 8 * ∫ t in beta..sigma,
      ∫ v in sigma..((1 - t) / 2), SeventhEighth.classicalKernel t v := by
  unfold C9
  congr 1
  apply intervalIntegral.integral_congr
  intro t ht
  rw [uIcc_of_le parameters.2.2.2.1.le] at ht
  have hs0 : 0 < sigma := lt_trans (by norm_num) parameters.2.2.2.2.1
  have hs3 : sigma < (1 / 3 : ℝ) := parameters.2.2.2.2.2.1
  have ht0 := (ninth_domain ht).1
  dsimp only
  rw [SeventhEighth.classical_slice_integral ht0 hs0 (by linarith [ht.2])]
  rw [show 1 - t - sigma = 1 - sigma - t by ring, ninth_log_argument]

theorem C7_upper_of_pointwise {g : ℝ → ℝ}
    (hg : IntervalIntegrable g volume 2 (2 / (1 - 6 * alpha) - 1))
    (h : ∀ t ∈ Icc (2 : ℝ) (2 / (1 - 6 * alpha) - 1), log (t - 1) / t ≤ g t) :
    C7 ≤ 8 * ∫ t in (2 : ℝ)..(2 / (1 - 6 * alpha) - 1), g t := by
  unfold C7
  apply mul_le_mul_of_nonneg_left _ (by norm_num)
  exact intervalIntegral.integral_mono_on
    (by norm_num [alpha, SeventhEighth.alpha]) C7_integrable hg h

theorem C8_upper_of_pointwise {gSmall gLarge : ℝ → ℝ}
    (hs : IntervalIntegrable gSmall volume alpha (1 / 10))
    (hl : IntervalIntegrable gLarge volume (1 / 10) (1 / 3))
    (hsmall : ∀ t ∈ Icc alpha (1 / 10 : ℝ),
      log (2 - 3 * t) / (t * (1 - t)^2) ≤ gSmall t)
    (hlarge : ∀ t ∈ Icc (1 / 10 : ℝ) (1 / 3),
      log (2 - 3 * t) / (t * (1 - t)) ≤ gLarge t) :
    C8 ≤ (36 / 5) * (∫ t in alpha..(1 / 10), gSmall t) +
      8 * (∫ t in (1 / 10 : ℝ)..(1 / 3), gLarge t) := by
  unfold C8
  exact add_le_add
    (mul_le_mul_of_nonneg_left
      (intervalIntegral.integral_mono_on parameters.2.1.le C8_small_integrable hs hsmall)
      (by norm_num))
    (mul_le_mul_of_nonneg_left
      (intervalIntegral.integral_mono_on (by norm_num : (1 / 10 : ℝ) ≤ 1 / 3)
        C8_large_integrable hl hlarge) (by norm_num))

theorem C9_upper_of_pointwise {g : ℝ → ℝ}
    (hg : IntervalIntegrable g volume beta sigma)
    (h : ∀ t ∈ Icc beta sigma,
      log ((1 + 6 * alpha - 2 * t) / (1 - 6 * alpha)) / (t * (1 - t)) ≤ g t) :
    C9 ≤ 8 * ∫ t in beta..sigma, g t := by
  unfold C9
  exact mul_le_mul_of_nonneg_left
    (intervalIntegral.integral_mono_on parameters.2.2.2.1.le C9_integrable hg h)
    (by norm_num)

theorem existing_directed_integral_upper :
    2 * C7 + C8 + C9 ≤ WuTarget.W12.analyticUpper := by
  rw [weighted_original_identity]
  exact WuTarget.W12.weightedDebit_le_analyticUpper

end WuPaper.RMapMDebit

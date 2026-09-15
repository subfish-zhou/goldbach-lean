import MathlibNt.Wu2008DoubleSieve.FourthRowClassicalCoefficientLog

namespace Wu2008DoubleSieve
open Set MeasureTheory Real
open scoped Interval

/-- The original Gamma5 mass, not a replacement constant. -/
theorem fourthRowClassical_C5_triangle :
    gamma5MassC5 = fourthRowClassicalTriangle (103 / 25) (291 / 100) := by
  norm_num [gamma5MassC5, fourthRowClassicalTriangle, gamma5MassA,
    gamma5ClassicalS, gamma5ClassicalB]

theorem fourthRowClassical_C678_slice {t : ℝ}
    (ht : t ∈ Icc gamma5MassA gamma6BaseB) :
    (∫ u in t..gamma6BaseF, gamma5MassKernel t u) =
      (∫ u in gamma78GainStart true t..gamma78GainUpper true, gamma5MassKernel t u) +
      (∫ u in gamma78GainStart false t..gamma78GainUpper false, gamma5MassKernel t u) +
      ∫ u in gamma6BaseC..gamma6BaseF, gamma5MassKernel t u := by
  have h7 := gamma78Gain_C_inner_integrable true ht
  have h8 := gamma78Gain_C_inner_integrable false ht
  have h6 := gamma6Base_inner_integrable ht.1 ht.2 le_rfl
    (by norm_num [gamma6BaseC, gamma6BaseF]) le_rfl
  simp only [gamma78GainStart, gamma78GainUpper, Bool.false_eq_true, if_false, if_true] at h7 h8 ⊢
  simp only [show gamma5ClassicalB = gamma6BaseC from rfl] at h8 ⊢
  have h78 := intervalIntegral.integral_add_adjacent_intervals h7 h8
  have hall := intervalIntegral.integral_add_adjacent_intervals (h7.trans h8) h6
  linarith

/-- Joining the actual three adjacent u intervals before splitting t. -/
theorem fourthRowClassical_C678_strip :
    gamma6BaseC6 + gamma78GainC true + gamma78GainC false =
      ∫ t in gamma5MassA..gamma6BaseB,
        ∫ u in t..gamma6BaseF, gamma5MassKernel t u := by
  have h7 := gamma78Gain_C_outer_integrable true
  have h8 := gamma78Gain_C_outer_integrable false
  have h6 := gamma6Base_outer_integrable le_rfl
    (show gamma5MassA ≤ gamma6BaseB by norm_num [gamma5MassA, gamma5ClassicalS, gamma6BaseB])
    le_rfl le_rfl (by norm_num [gamma6BaseC, gamma6BaseF]) le_rfl
  have he : (∫ t in gamma5MassA..gamma6BaseB,
      ∫ u in t..gamma6BaseF, gamma5MassKernel t u) =
      gamma78GainC true + gamma78GainC false + gamma6BaseC6 := by
    calc
      _ = ∫ t in gamma5MassA..gamma6BaseB,
          (∫ u in gamma78GainStart true t..gamma78GainUpper true, gamma5MassKernel t u) +
          (∫ u in gamma78GainStart false t..gamma78GainUpper false, gamma5MassKernel t u) +
          ∫ u in gamma6BaseC..gamma6BaseF, gamma5MassKernel t u := by
        apply intervalIntegral.integral_congr
        intro t ht
        apply fourthRowClassical_C678_slice
        simpa only [uIcc_of_le (show gamma5MassA ≤ gamma6BaseB by
          norm_num [gamma5MassA, gamma5ClassicalS, gamma6BaseB])] using ht
      _ = _ := by
        rw [intervalIntegral.integral_add (h7.add h8) h6, intervalIntegral.integral_add h7 h8]
        rfl
  linarith

/-- Full triangle minus its upper t triangle is exactly the C6+C7+C8 strip. -/
theorem fourthRowClassical_C678_triangle :
    gamma6BaseC6 + gamma78GainC true + gamma78GainC false =
      fourthRowClassicalTriangle (103 / 25) (5 / 2) -
      fourthRowClassicalTriangle (89 / 25) (5 / 2) := by
  have ha : 0 < gamma5MassA := by norm_num [gamma5MassA, gamma5ClassicalS]
  have hab : gamma5MassA ≤ gamma6BaseB := by norm_num [gamma5MassA, gamma5ClassicalS, gamma6BaseB]
  have hbf : gamma6BaseB ≤ gamma6BaseF := by norm_num [gamma6BaseB, gamma6BaseF]
  have hf : gamma6BaseF < 1 / 2 := by norm_num [gamma6BaseF]
  have hi := (fourthRowClassical_triangle_fubini ha (hab.trans hbf) hf).1
  have hi1 : IntervalIntegrable (fun t => ∫ u in t..gamma6BaseF, gamma5MassKernel t u)
      volume gamma5MassA gamma6BaseB := hi.mono_set (by
    rw [uIcc_of_le hab, uIcc_of_le (hab.trans hbf)]
    exact Icc_subset_Icc_right hbf)
  have hi2 : IntervalIntegrable (fun t => ∫ u in t..gamma6BaseF, gamma5MassKernel t u)
      volume gamma6BaseB gamma6BaseF := hi.mono_set (by
    rw [uIcc_of_le hbf, uIcc_of_le (hab.trans hbf)]
    exact Icc_subset_Icc_left hab)
  have hadd := intervalIntegral.integral_add_adjacent_intervals hi1 hi2
  rw [fourthRowClassical_C678_strip]
  have h1 : fourthRowClassicalTriangle (103 / 25) (5 / 2) =
      ∫ t in gamma5MassA..gamma6BaseF, ∫ u in t..gamma6BaseF, gamma5MassKernel t u := by
    norm_num [fourthRowClassicalTriangle, gamma5MassA, gamma5ClassicalS, gamma6BaseF]
  have h2 : fourthRowClassicalTriangle (89 / 25) (5 / 2) =
      ∫ t in gamma6BaseB..gamma6BaseF, ∫ u in t..gamma6BaseF, gamma5MassKernel t u := by
    norm_num [fourthRowClassicalTriangle, gamma6BaseB, gamma6BaseF]
  rw [h1, h2]
  linarith

theorem fourthRowClassical_C5_log :
    gamma5MassC5 = fourthRowClassicalJ (291 / 100) (103 / 25) -
      (fourthRowClassicalL (103 / 25) - fourthRowClassicalL (291 / 100)) := by
  rw [fourthRowClassical_C5_triangle]
  exact fourthRowClassical_triangle_eq_log (by norm_num) (by norm_num)

theorem fourthRowClassical_C678_log :
    gamma6BaseC6 + gamma78GainC true + gamma78GainC false =
      fourthRowClassicalJ (5 / 2) (103 / 25) - fourthRowClassicalJ (5 / 2) (89 / 25) -
      fourthRowClassicalL (103 / 25) + fourthRowClassicalL (89 / 25) := by
  rw [fourthRowClassical_C678_triangle,
    fourthRowClassical_triangle_eq_log (by norm_num : (5 / 2 : ℝ) ≤ 103 / 25) (by norm_num),
    fourthRowClassical_triangle_eq_log (by norm_num : (5 / 2 : ℝ) ≤ 89 / 25) (by norm_num)]
  ring

/-- The exact fourth-row classical coefficient with the original four masses. -/
theorem fourthRowClassical_coefficient_eq_log :
    (5 * wuUpperCoefficient (5 / 2) - 4 * wuUpperCoefficient (103 / 25) -
      wuUpperCoefficient (89 / 25) + 2 * fourthRowClassicalJ (5 / 2) (103 / 25) +
      fourthRowClassicalJ (291 / 100) (103 / 25) - gamma5MassC5 - gamma6BaseC6 -
      gamma78GainC true - gamma78GainC false) / 5 =
      -(2 / 5) * fourthRowClassicalL (103 / 25) - (2 / 5) * fourthRowClassicalL (89 / 25) -
      (1 / 5) * fourthRowClassicalL (291 / 100) + (1 / 5) * fourthRowClassicalJ (5 / 2) (103 / 25) +
      (1 / 5) * fourthRowClassicalJ (5 / 2) (89 / 25) := by
  have hS := firstFunctionalGain_coefficient_eq_log
    (by norm_num : (2 : ℝ) ≤ 5 / 2) (by norm_num : (5 / 2 : ℝ) ≤ 3)
    (by norm_num : (3 : ℝ) ≤ 103 / 25) (by norm_num : (103 / 25 : ℝ) ≤ 5)
  have hB := firstFunctionalGain_coefficient_eq_log
    (by norm_num : (2 : ℝ) ≤ 5 / 2) (by norm_num : (5 / 2 : ℝ) ≤ 3)
    (by norm_num : (3 : ℝ) ≤ 89 / 25) (by norm_num : (89 / 25 : ℝ) ≤ 5)
  change wuUpperCoefficient (5 / 2) - wuUpperCoefficient (103 / 25) =
    -fourthRowClassicalL (103 / 25) at hS
  change wuUpperCoefficient (5 / 2) - wuUpperCoefficient (89 / 25) =
    -fourthRowClassicalL (89 / 25) at hB
  have h5 := fourthRowClassical_C5_log
  have h678 := fourthRowClassical_C678_log
  linarith

end Wu2008DoubleSieve

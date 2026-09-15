import Wu08OriginalFirstFormula

noncomputable section
open Real Set MeasureTheory
open scoped Interval
open Wu2008DoubleSieve Wu08OriginalFirstSteps
open MathlibNt.SieveTheory.JurkatRichert1965ChenGammaOneQOne

namespace WuPaper.RMapMFirst

theorem normalized_Aa_eq (s : ℝ) :
    wuUpperCoefficient s = s * jr1965F s / (2 * exp eulerMascheroniConstant) ∧
    wuLowerCoefficient s = s * jr1965f s / (2 * exp eulerMascheroniConstant) :=
  ⟨rfl, rfl⟩

theorem original_initial {s : ℝ} (hs : 0 < s) (hs2 : s ≤ 2) :
    jr1965F s = 2 * exp eulerMascheroniConstant / s ∧ jr1965f s = 0 ∧
      wuUpperCoefficient s = 1 ∧ wuLowerCoefficient s = 0 := by
  refine ⟨jr1965F_initial hs2, jr1965f_initial hs2,
    jr1965F_normalized_initial hs (by linarith), ?_⟩
  simp only [wuLowerCoefficient, jr1965f_initial hs2, mul_zero, zero_div]

theorem original_delay_system {s : ℝ} (hs : 2 < s) :
    HasDerivAt (fun t => t * jr1965F t) (jr1965f (s - 1)) s ∧
    HasDerivAt (fun t => t * jr1965f t) (jr1965F (s - 1)) s :=
  ⟨hasDerivAt_mul_jr1965F hs, hasDerivAt_mul_jr1965f hs⟩

theorem a_middle_original {s : ℝ} (hs : 4 ≤ s) (hs6 : s ≤ 6) :
    wuLowerCoefficient s = log (s - 1) +
      (∫ t in (3 : ℝ)..(s - 1),
        (∫ u in (2 : ℝ)..(t - 1), log (u - 1) / u) / t) := by
  rw [lower_middle hs hs6, C_literal hs]

theorem A_middle_original {s : ℝ} (hs : 3 ≤ s) (hs5 : s ≤ 5) :
    wuUpperCoefficient s = 1 +
      (∫ t in (2 : ℝ)..(s - 1), log (t - 1) / t) := by
  rw [upper_initial hs hs5, B_literal hs]

theorem A_high_original {s : ℝ} (hs : 5 ≤ s) (hs7 : s ≤ 7) :
    wuUpperCoefficient s = 1 +
      (∫ t in (2 : ℝ)..(s - 1), log (t - 1) / t) +
      (∫ t in (4 : ℝ)..(s - 1),
        (∫ u in (3 : ℝ)..(t - 1),
          (∫ v in (2 : ℝ)..(u - 1), log (v - 1) / v) / u) / t) := by
  rw [upper_middle hs hs7, B_literal (by linarith), D_literal hs]

theorem a_piecewise_original {s : ℝ} (hs : 0 < s) (hs8 : s ≤ 8) :
    wuLowerCoefficient s =
      if s ≤ 2 then 0
      else if s ≤ 4 then log (s - 1)
      else if s ≤ 6 then log (s - 1) +
        (∫ t in (3 : ℝ)..(s - 1),
          (∫ u in (2 : ℝ)..(t - 1), log (u - 1) / u) / t)
      else log (s - 1) +
        (∫ t in (3 : ℝ)..(s - 1),
          (∫ u in (2 : ℝ)..(t - 1), log (u - 1) / u) / t) +
        (∫ t in (5 : ℝ)..(s - 1),
          (∫ u in (4 : ℝ)..(t - 1),
            (∫ v in (3 : ℝ)..(u - 1),
              (∫ w in (2 : ℝ)..(v - 1), log (w - 1) / w) / v) / u) / t) := by
  split_ifs with h2 h4 h6
  · exact (original_initial hs h2).2.2.2
  · exact jr1965f_normalized_firstInterval (by linarith) h4
  · exact a_middle_original (by linarith) h6
  · exact original_formula (by linarith) hs8

theorem A_piecewise_original {s : ℝ} (hs : 0 < s) (hs7 : s ≤ 7) :
    wuUpperCoefficient s =
      if s ≤ 3 then 1
      else if s ≤ 5 then 1 +
        (∫ t in (2 : ℝ)..(s - 1), log (t - 1) / t)
      else 1 + (∫ t in (2 : ℝ)..(s - 1), log (t - 1) / t) +
        (∫ t in (4 : ℝ)..(s - 1),
          (∫ u in (3 : ℝ)..(t - 1),
            (∫ v in (2 : ℝ)..(u - 1), log (v - 1) / v) / u) / t) := by
  split_ifs with h3 h5
  · exact jr1965F_normalized_initial hs h3
  · exact A_middle_original (by linarith) h5
  · exact A_high_original (by linarith) hs7

theorem original_log_integrable {s : ℝ} (hs : 3 ≤ s) :
    IntervalIntegrable (fun t => log (t - 1) / t) volume 2 (s - 1) := by
  apply IntervalIntegrable.congr _ (k_continuous.intervalIntegrable _ _)
  intro t ht
  rw [uIoc_of_le (by linarith : (2 : ℝ) ≤ s - 1)] at ht
  exact k_literal ht.1.le

theorem original_double_integrable {s : ℝ} (hs : 4 ≤ s) :
    IntervalIntegrable
      (fun t => (∫ u in (2 : ℝ)..(t - 1), log (u - 1) / u) / t)
      volume 3 (s - 1) := by
  apply IntervalIntegrable.congr _
    ((div_continuous B_continuous).intervalIntegrable _ _)
  intro t ht
  rw [uIoc_of_le (by linarith : (3 : ℝ) ≤ s - 1)] at ht
  dsimp only
  rw [B_literal ht.1.le, max_eq_right (by linarith [ht.1] : (1 : ℝ) ≤ t)]

theorem original_triple_integrable {s : ℝ} (hs : 5 ≤ s) :
    IntervalIntegrable
      (fun t => (∫ u in (3 : ℝ)..(t - 1),
        (∫ v in (2 : ℝ)..(u - 1), log (v - 1) / v) / u) / t)
      volume 4 (s - 1) := by
  apply IntervalIntegrable.congr _
    ((div_continuous C_continuous).intervalIntegrable _ _)
  intro t ht
  rw [uIoc_of_le (by linarith : (4 : ℝ) ≤ s - 1)] at ht
  dsimp only
  rw [C_literal ht.1.le, max_eq_right (by linarith [ht.1] : (1 : ℝ) ≤ t)]

theorem original_quadruple_integrable {s : ℝ} (hs : 6 ≤ s) :
    IntervalIntegrable
      (fun t => (∫ u in (4 : ℝ)..(t - 1),
        (∫ v in (3 : ℝ)..(u - 1),
          (∫ w in (2 : ℝ)..(v - 1), log (w - 1) / w) / v) / u) / t)
      volume 5 (s - 1) := by
  apply IntervalIntegrable.congr _
    ((div_continuous D_continuous).intervalIntegrable _ _)
  intro t ht
  rw [uIoc_of_le (by linarith : (5 : ℝ) ≤ s - 1)] at ht
  dsimp only
  rw [D_literal ht.1.le, max_eq_right (by linarith [ht.1] : (1 : ℝ) ≤ t)]

theorem Aa_continuous :
    ContinuousOn wuUpperCoefficient (Ioi 0) ∧ ContinuousOn wuLowerCoefficient (Ioi 0) :=
  ⟨continuousOn_wuUpperCoefficient, continuousOn_wuLowerCoefficient⟩

theorem Aa_nonnegative {s : ℝ} (hs : 0 < s) :
    0 ≤ wuUpperCoefficient s ∧ 0 ≤ wuLowerCoefficient s := by
  constructor
  · exact div_nonneg (mul_nonneg hs.le (jr1965F_pos hs).le) (by positivity)
  · exact div_nonneg (mul_nonneg hs.le (jr1965f_nonneg hs)) (by positivity)

theorem recurrence_join_values : B 3 = 0 ∧ C 4 = 0 ∧ D 5 = 0 ∧ E 6 = 0 := by
  norm_num [B, C, D, E]

theorem Aa_closed_endpoints :
    wuLowerCoefficient 2 = 0 ∧ wuUpperCoefficient 3 = 1 ∧
    wuLowerCoefficient 4 = log 3 ∧ wuUpperCoefficient 5 = 1 + B 5 ∧
    wuLowerCoefficient 6 = log 5 + C 6 ∧
    wuUpperCoefficient 7 = 1 + B 7 + D 7 ∧
    wuLowerCoefficient 8 = log 7 + C 8 + E 8 := by
  refine ⟨(original_initial (by norm_num) le_rfl).2.2.2,
    jr1965F_normalized_initial (by norm_num) le_rfl, ?_,
    upper_initial (by norm_num) le_rfl, ?_,
    upper_middle (by norm_num) le_rfl, ?_⟩
  · exact BaseRecurrenceLower.lower_four_value
  · simpa only [show (6 : ℝ) - 1 = 5 by norm_num] using
      lower_middle (s := 6) (by norm_num) le_rfl
  · simpa only [show (8 : ℝ) - 1 = 7 by norm_num] using
      lower_terminal (s := 8) (by norm_num) le_rfl

#check @normalized_Aa_eq
#print axioms normalized_Aa_eq
#check @original_initial
#print axioms original_initial
#check @original_delay_system
#print axioms original_delay_system
#check @a_middle_original
#print axioms a_middle_original
#check @A_middle_original
#print axioms A_middle_original
#check @A_high_original
#print axioms A_high_original
#check @a_piecewise_original
#print axioms a_piecewise_original
#check @A_piecewise_original
#print axioms A_piecewise_original
#check @original_log_integrable
#print axioms original_log_integrable
#check @original_double_integrable
#print axioms original_double_integrable
#check @original_triple_integrable
#print axioms original_triple_integrable
#check @original_quadruple_integrable
#print axioms original_quadruple_integrable
#check @Aa_continuous
#print axioms Aa_continuous
#check @Aa_nonnegative
#print axioms Aa_nonnegative
#check @recurrence_join_values
#print axioms recurrence_join_values
#check @Aa_closed_endpoints
#print axioms Aa_closed_endpoints

end WuPaper.RMapMFirst

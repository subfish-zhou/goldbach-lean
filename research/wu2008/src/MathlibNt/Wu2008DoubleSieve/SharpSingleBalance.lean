import MathlibNt.Wu2008DoubleSieve.SharpLogRecurrence

namespace Wu2008DoubleSieve.SharpSingleBalance
open Real Set MeasureTheory ClassicalAnalyticLeaves SharpLogRecurrence
open scoped Interval
open MathlibNt.SieveTheory.JurkatRichert1965ChenGammaOneQOne

noncomputable abbrev a : ℝ := truncatedSixthLowerAlpha
noncomputable abbrev s : ℝ := truncatedSixthLowerSigma
noncomputable def c (j : ℝ) : ℝ := 1/2-j*a

/-- The quotient, not the normalized coefficient itself, is antitone. -/
theorem upper_ratio_antitone {j u : ℝ} (hj : 0 < j) (hju : j ≤ u) :
    wuUpperCoefficient u/u ≤ wuUpperCoefficient j/j := by
  have hu := hj.trans_le hju
  rw [wuUpperCoefficient_div hu.ne',wuUpperCoefficient_div hj.ne']
  exact div_le_div_of_nonneg_right (antitoneOn_jr1965F hj hu hju) (by positivity)

theorem g_endpoint {j t : ℝ} (hj : 0 < j) (ht : a ≤ t) (htj : t ≤ c j) :
    ClassicalSingleBounds.g t ≤ (wuUpperCoefficient j/j)/a*(1/t) := by
  have ha := truncatedSixthLower_parameters.1
  have ht0 := ha.trans_le ht
  have hju : j ≤ (1/2-t)/a := (le_div_iff₀ ha).2 (by dsimp [c] at htj; linarith)
  have h := div_le_div_of_nonneg_right (upper_ratio_antitone hj hju) (mul_pos ha ht0).le
  calc
    ClassicalSingleBounds.g t = (wuUpperCoefficient ((1/2-t)/a)/((1/2-t)/a))/(a*t) := by
      unfold ClassicalSingleBounds.g
      field_simp
    _ ≤ (wuUpperCoefficient j/j)/(a*t) := h
    _ = _ := by ring

theorem g_segment {j l r : ℝ} (hj : 0 < j) (hl : a ≤ l) (hr : r ≤ c j)
    (hr3 : r ≤ 1/3) (hlr : l ≤ r) :
    (∫ t in l..r, ClassicalSingleBounds.g t) ≤
      (wuUpperCoefficient j/j)/a*(log r-log l) := by
  have hl0 := truncatedSixthLower_parameters.1.trans_le hl
  have hi : IntervalIntegrable (fun t => (wuUpperCoefficient j/j)/a*(1/t)) volume l r := by
    apply ContinuousOn.intervalIntegrable
    exact continuousOn_const.mul (continuousOn_const.div continuousOn_id (fun t ht => by
      rw [uIcc_of_le hlr] at ht; exact (hl0.trans_le ht.1).ne'))
  have h := intervalIntegral.integral_mono_on hlr
    (ClassicalSingleBounds.g_integrable hl hr3 hlr) hi
    (fun t ht => g_endpoint hj (hl.trans ht.1) (ht.2.trans hr))
  rw [intervalIntegral.integral_const_mul,integral_reciprocal hl0 hlr] at h
  exact h

theorem G_pair_segmented :
    SingleUpperClassicalLimit.Glin (1/3)+SingleUpperClassicalLimit.Glin s ≤
      (8/a)*((42823/151875)*log (c 5/a)+(311/1080)*log (c 4/c 5)+
        (1/3)*log (s/c 4))+8*log (6*a/s) := by
  have ha := truncatedSixthLower_parameters.1
  have h5 : a ≤ c 5 := by norm_num [c,a,truncatedSixthLowerAlpha]
  have h54 : c 5 ≤ c 4 := by norm_num [c,a,truncatedSixthLowerAlpha]
  have h4s : c 4 ≤ s := by norm_num [c,a,s,truncatedSixthLowerAlpha,truncatedSixthLowerSigma]
  have hs3 : s ≤ 1/3 := truncatedSixthLower_parameters.2.2.2.1.le
  have hseg5 := g_segment (by norm_num : (0 : ℝ) < 5) le_rfl le_rfl
    (h54.trans (h4s.trans hs3)) h5
  have hseg4 := g_segment (by norm_num : (0 : ℝ) < 4) h5 le_rfl (h4s.trans hs3) h54
  have hseg3 := g_segment (by norm_num : (0 : ℝ) < 3) (h5.trans h54)
    (le_rfl : s ≤ c 3) hs3 h4s
  have hq3 : wuUpperCoefficient 3 = 1 := jr1965F_normalized_initial (by norm_num) le_rfl
  rw [hq3] at hseg3
  have hl5 : 0 ≤ log (c 5)-log a := sub_nonneg.mpr (log_le_log ha h5)
  have hl4 : 0 ≤ log (c 4)-log (c 5) := sub_nonneg.mpr (log_le_log (ha.trans_le h5) h54)
  have hq5 := mul_le_mul_of_nonneg_right
    (div_le_div_of_nonneg_right upper_five_div ha.le) hl5
  have hq4 := mul_le_mul_of_nonneg_right
    (div_le_div_of_nonneg_right upper_four_div ha.le) hl4
  have hi5 := ClassicalSingleBounds.g_integrable le_rfl (h54.trans (h4s.trans hs3)) h5
  have hi4 := ClassicalSingleBounds.g_integrable h5 (h4s.trans hs3) h54
  have hi3 := ClassicalSingleBounds.g_integrable (h5.trans h54) hs3 h4s
  have his := ClassicalSingleBounds.g_integrable le_rfl hs3 (h5.trans (h54.trans h4s))
  have hih := ClassicalSingleBounds.g_integrable (h5.trans (h54.trans h4s)) le_rfl hs3
  have he54 := intervalIntegral.integral_add_adjacent_intervals hi5 hi4
  have he43 := intervalIntegral.integral_add_adjacent_intervals (hi5.trans hi4) hi3
  have hesh := intervalIntegral.integral_add_adjacent_intervals his hih
  have heh := ClassicalSingleBounds.high_integral_eq
  change (∫ t in s..(1/3 : ℝ), ClassicalSingleBounds.g t) = 2*log (6*a/s) at heh
  have he1 : SingleUpperClassicalLimit.Glin (1/3) =
      4*∫ t in a..(1/3 : ℝ), ClassicalSingleBounds.g t := by
    simp only [SingleUpperClassicalLimit.Glin,SingleUpperClassicalLimit.Gdelta,sub_zero,ClassicalSingleBounds.g,a,ClassicalSingleBounds.a]
  have he2 : SingleUpperClassicalLimit.Glin s =
      4*∫ t in a..s, ClassicalSingleBounds.g t := by
    simp only [SingleUpperClassicalLimit.Glin,SingleUpperClassicalLimit.Gdelta,sub_zero,ClassicalSingleBounds.g,a,ClassicalSingleBounds.a]
  rw [he1,he2,log_div (ha.trans_le h5).ne' ha.ne',
    log_div (ha.trans_le (h5.trans h54)).ne' (ha.trans_le h5).ne',
    log_div (ha.trans_le (h5.trans (h54.trans h4s))).ne' (ha.trans_le (h5.trans h54)).ne']
  norm_num [a,ClassicalSingleBounds.a,truncatedSixthLowerAlpha] at hq5 hq4 hseg3 hseg5 hseg4 he54 he43 hesh heh ⊢
  linarith

theorem G_pair_lt_179_quarters :
    SingleUpperClassicalLimit.Glin (1/3)+SingleUpperClassicalLimit.Glin s < 179/4 := by
  have h := G_pair_segmented
  have h1 := log_upper (t := c 5/a) (by norm_num [c,a,truncatedSixthLowerAlpha])
  have h2 := log_upper (t := c 4/c 5) (by norm_num [c,a,truncatedSixthLowerAlpha])
  have h3 := log_upper (t := s/c 4)
    (by norm_num [s,c,a,truncatedSixthLowerAlpha,truncatedSixthLowerSigma])
  have h4 := log_upper (t := 6*a/s)
    (by norm_num [s,a,truncatedSixthLowerAlpha,truncatedSixthLowerSigma])
  norm_num [upperLog,s,c,a,truncatedSixthLowerAlpha,truncatedSixthLowerSigma] at h1 h2 h3 h4 h ⊢
  linarith

/-- True quadratic surplus from the original upper recurrence on its first nonconstant interval. -/
theorem upper_quadratic {u : ℝ} (hu : 3 ≤ u) (hu4 : u ≤ 4) :
    1+(u-3)^2/9 ≤ wuUpperCoefficient u := by
  have hr := wuUpperCoefficient_sub_eq_integral (by norm_num : (2 : ℝ) ≤ 3) hu
  have he : wuUpperCoefficient 3 = 1 := jr1965F_normalized_initial (by norm_num) le_rfl
  have hab : 2 ≤ u-1 := by linarith
  have hpoint (v : ℝ) (hv : v ∈ Icc 2 (u-1)) :
      2*(v-2)/9 ≤ wuLowerCoefficient v/v := by
    have hv0 : 0 < v := by linarith [hv.1]
    have hv3 : v ≤ 3 := by linarith [hv.2]
    have hlog := ClassicalLogBounds.log_tangent_lower (a := (1 : ℝ))
      (b := v-1) (by norm_num) (by linarith [hv.1])
    have heq : wuLowerCoefficient v = log (v-1) :=
      jr1965f_normalized_firstInterval hv.1 (by linarith)
    rw [heq]
    norm_num only [log_one,sub_zero] at hlog
    have hh : 2*(v-2)/v ≤ log (v-1) := by convert hlog using 1; ring
    apply (le_div_iff₀ hv0).2
    apply le_trans _ hh
    apply (le_div_iff₀ hv0).2
    have hm := mul_nonneg (by linarith [hv.1] : 0 ≤ v-2)
      (show 0 ≤ 9-v^2 by nlinarith)
    nlinarith
  have hi := intervalIntegral.integral_mono_on hab
    ((by fun_prop : Continuous (fun v : ℝ => 2*(v-2)/9)).intervalIntegrable 2 (u-1))
    (wuLowerCoefficient_div_intervalIntegrable (by norm_num) hab) hpoint
  have hd (v : ℝ) (_hv : v ∈ uIcc 2 (u-1)) :
      HasDerivAt (fun v : ℝ => (v-2)^2/9) (2*(v-2)/9) v := by
    convert (((hasDerivAt_id v).sub_const 2).pow 2).div_const 9 using 1 <;> first | rfl | (dsimp; ring)
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hd
    ((by fun_prop : Continuous (fun v : ℝ => 2*(v-2)/9)).intervalIntegrable 2 (u-1))] at hi
  norm_num only [show (3 : ℝ)-1=2 by norm_num,he] at hr
  norm_num at hi
  nlinarith

theorem lower_five_surplus : 2*log 2+1/108 ≤ wuLowerCoefficient 5 := by
  have hr := wuLowerCoefficient_sub_eq_integral (by norm_num : (2 : ℝ) ≤ 4)
    (by norm_num : (4 : ℝ) ≤ 5)
  have he : wuLowerCoefficient 4 = log 3 := by
    simpa only [wuLowerCoefficient,show (4 : ℝ)-1=3 by norm_num] using
      (jr1965f_normalized_firstInterval (s := 4) (by norm_num) le_rfl)
  have hi1 : IntervalIntegrable (fun v : ℝ => 1/v+(v-3)^2/36) volume 3 4 := by
    apply ContinuousOn.intervalIntegrable
    apply ContinuousOn.add
    · exact continuousOn_const.div continuousOn_id (fun v hv => by
        rw [uIcc_of_le (by norm_num : (3 : ℝ) ≤ 4)] at hv; linarith [hv.1])
    · fun_prop
  have hpoint (v : ℝ) (hv : v ∈ Icc (3 : ℝ) 4) :
      1/v+(v-3)^2/36 ≤ wuUpperCoefficient v/v := by
    have hv0 : 0 < v := by linarith [hv.1]
    apply (le_div_iff₀ hv0).2
    have hh := upper_quadratic hv.1 hv.2
    have hm := mul_nonneg (sq_nonneg (v-3)) (show 0 ≤ 4-v by linarith [hv.2])
    have hcancel : (1/v)*v = 1 := by field_simp
    nlinarith
  have hi := intervalIntegral.integral_mono_on (by norm_num : (3 : ℝ) ≤ 4) hi1
    (wuUpperCoefficient_div_intervalIntegrable (by norm_num) (by norm_num)) hpoint
  have hd (v : ℝ) (hv : v ∈ uIcc (3 : ℝ) 4) :
      HasDerivAt (fun v : ℝ => log v+(v-3)^3/108) (1/v+(v-3)^2/36) v := by
    rw [uIcc_of_le (by norm_num : (3 : ℝ) ≤ 4)] at hv
    have h := (hasDerivAt_log (by linarith [hv.1] : v ≠ 0)).add
      ((((hasDerivAt_id v).sub_const 3).pow 3).div_const 108)
    convert h using 1 <;> first | rfl | (simp; ring)
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hd hi1] at hi
  have h4 : log (4 : ℝ) = 2*log 2 := by
    have hh := log_pow (2 : ℝ) 2; norm_num at hh; exact hh
  norm_num [h4] at hi
  norm_num only [show (4 : ℝ)-1=3 by norm_num,show (5 : ℝ)-1=4 by norm_num,he] at hr
  linarith

theorem lower_ratio_transport {j u : ℝ} (hj : 0 < j) (hju : j ≤ u) :
    (u/j)*wuLowerCoefficient j ≤ wuLowerCoefficient u := by
  have hu := hj.trans_le hju
  have hf := monotoneOn_jr1965f hj hu hju
  have hh := div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hf hu.le)
    (by positivity : (0 : ℝ) ≤ 2*exp eulerMascheroniConstant)
  change _ ≤ wuLowerCoefficient u at hh
  convert hh using 1
  dsimp [wuLowerCoefficient]
  field_simp

theorem base_sharp_lower :
    (54035471/1012500 : ℝ) ≤
      24*wuLowerCoefficient (1/(2*truncatedSixthLowerAlpha))+
      8*wuLowerCoefficient (1/(2*truncatedSixthLowerBeta)) := by
  have h1 := lower_ratio_transport (j := 5) (u := 1/(2*truncatedSixthLowerAlpha))
    (by norm_num) (by norm_num [truncatedSixthLowerAlpha])
  have h2 := ClassicalLogBounds.lower_linear_four (s := 1/(2*truncatedSixthLowerBeta))
    (by norm_num [truncatedSixthLowerBeta])
  have h5 := lower_five_surplus
  obtain ⟨hl2,_⟩ := log_two_bounds
  obtain ⟨hl3,_⟩ := log_three_bounds
  norm_num [truncatedSixthLowerAlpha,truncatedSixthLowerBeta] at h1 h2 ⊢
  linarith

end Wu2008DoubleSieve.SharpSingleBalance

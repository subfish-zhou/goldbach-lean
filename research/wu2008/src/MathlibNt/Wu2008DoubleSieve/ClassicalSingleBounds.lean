import MathlibNt.Wu2008DoubleSieve.ClassicalLogBounds

namespace Wu2008DoubleSieve.ClassicalSingleBounds
open Real Set MeasureTheory ClassicalAnalyticLeaves ClassicalLogBounds SingleUpperClassicalLimit
open scoped Interval

noncomputable abbrev a : ℝ := truncatedSixthLowerAlpha
noncomputable abbrev s : ℝ := truncatedSixthLowerSigma
noncomputable def g (t : ℝ) : ℝ := wuUpperCoefficient ((1/2-t)/a)/(t*(1/2-t))

theorem g_integrable {l r : ℝ} (hl : a ≤ l) (hr : r ≤ 1/3) (hlr : l ≤ r) :
    IntervalIntegrable g volume l r := by
  have hc : Continuous (fun t : ℝ => regularKernel 0 t) :=
    regular_continuous.comp (f := fun t : ℝ => (0,t)) (by fun_prop)
  apply (hc.intervalIntegrable l r).congr
  intro t ht
  rw [uIoc_of_le hlr] at ht
  simpa [g] using regular_eq (δ := 0) (by norm_num : (0 : ℝ) ≤ 1/100)
    ⟨hl.trans ht.1.le, ht.2.trans hr⟩

theorem g_low {t : ℝ} (ht : t ∈ Icc a s) : g t ≤ (1/(3*a))*(1/t) := by
  have ha := truncatedSixthLower_parameters.1
  have ht0 := ha.trans_le ht.1
  have hd : 0 < 1/2-t := by
    have hs := truncatedSixthLower_parameters.2.2.2.1
    linarith [ht.2]
  have hu : 3 ≤ (1/2-t)/a := by
    apply (le_div_iff₀ ha).2
    have ht2 : t ≤ 1/2-3*a := ht.2
    linarith
  have h := div_le_div_of_nonneg_right (upper_div_le_third hu) (mul_pos ha ht0).le
  calc
    g t = (wuUpperCoefficient ((1/2-t)/a)/((1/2-t)/a))/(a*t) := by
      unfold g; field_simp
    _ ≤ (1/3)/(a*t) := h
    _ = _ := by ring

theorem g_high {t : ℝ} (ht : t ∈ Icc s (1/3 : ℝ)) : g t = 1/(t*(1/2-t)) := by
  have ha := truncatedSixthLower_parameters.1
  have hd : 0 < 1/2-t := by linarith [ht.2]
  have hu : (1/2-t)/a ≤ 3 := by
    apply (div_le_iff₀ ha).2
    have ht1 : 1/2-3*a ≤ t := ht.1
    linarith
  have he : wuUpperCoefficient ((1/2-t)/a) = 1 :=
    jr1965F_normalized_initial (div_pos hd ha) hu
  simp only [g, he]

theorem low_integral_upper : (∫ t in a..s, g t) ≤ (1/(3*a))*(log s-log a) := by
  have hp := truncatedSixthLower_parameters
  have has : a ≤ s := hp.2.1.le.trans hp.2.2.1.le
  have hi := intervalIntegral.integral_mono_on has (g_integrable le_rfl hp.2.2.2.1.le has)
    ((continuousOn_const.mul (continuousOn_const.div continuousOn_id (fun t ht => by
      rw [uIcc_of_le has] at ht
      exact (hp.1.trans_le ht.1).ne'))).intervalIntegrable)
    (fun t ht => g_low ht)
  change (∫ t in a..s, g t) ≤ ∫ t in a..s, (1/(3*a))*(1/t) at hi
  rw [intervalIntegral.integral_const_mul, integral_reciprocal hp.1 has] at hi
  exact hi

theorem high_integral_eq : (∫ t in s..(1/3 : ℝ), g t) = 2*log (6*a/s) := by
  have hp := truncatedSixthLower_parameters
  have hs0 : 0 < s := hp.1.trans (hp.2.1.trans hp.2.2.1)
  have hs3 : s ≤ 1/3 := hp.2.2.2.1.le
  have hd (t : ℝ) (ht : t ∈ uIcc s (1/3 : ℝ)) :
      HasDerivAt (fun t => 2*(log t-log (1/2-t))) (g t) t := by
    rw [uIcc_of_le hs3] at ht
    have ht0 := hs0.trans_le ht.1
    have hc : 0 < 1/2-t := by linarith [ht.2]
    rw [g_high ht]
    have h := ((hasDerivAt_log ht0.ne').sub
      (((hasDerivAt_const t (1/2 : ℝ)).sub (hasDerivAt_id t)).log hc.ne')).const_mul 2
    have hc2 : 1-t*2 ≠ 0 := by linarith
    convert h using 1 <;> first | rfl | (dsimp; field_simp [hc2]; ring)
  have he := intervalIntegral.integral_eq_sub_of_hasDerivAt hd
    (g_integrable (hp.2.1.le.trans hp.2.2.1.le) le_rfl hs3)
  have hid : (6*a/s) = ((1/3 : ℝ)/(1/2-1/3))*((1/2-s)/s) := by
    unfold s truncatedSixthLowerSigma
    field_simp
    ring
  have hc : (1/2-s) ≠ 0 := by norm_num [s,a,truncatedSixthLowerSigma,truncatedSixthLowerAlpha]
  have hl1 := log_div (by norm_num : (1/3 : ℝ) ≠ 0)
    (by norm_num : (1/2-1/3 : ℝ) ≠ 0)
  have hl2 := log_div hc hs0.ne'
  have hl3 := log_mul (by norm_num : (1/3 : ℝ)/(1/2-1/3) ≠ 0)
    (div_ne_zero hc hs0.ne')
  rw [← hid] at hl3
  linarith

/-- The signed two-G contribution is bounded on its two original intervals. -/
theorem G_pair_log_upper : Glin (1/3) + Glin s ≤
    (8/(3*a))*log (s/a) + 8*log (6*a/s) := by
  have hp := truncatedSixthLower_parameters
  have has := hp.2.1.le.trans hp.2.2.1.le
  have hs0 := hp.1.trans (hp.2.1.trans hp.2.2.1)
  have hadd := intervalIntegral.integral_add_adjacent_intervals
    (g_integrable le_rfl hp.2.2.2.1.le has)
    (g_integrable has le_rfl hp.2.2.2.1.le)
  have he1 : Glin (1/3) = 4*∫ t in a..(1/3 : ℝ), g t := by simp only [Glin, Gdelta, sub_zero, g, a]
  have he2 : Glin s = 4*∫ t in a..s, g t := by simp only [Glin, Gdelta, sub_zero, g, a]
  rw [he1, he2, ← hadd, high_integral_eq, log_div hs0.ne' hp.1.ne']
  have h := low_integral_upper
  norm_num [a, s, truncatedSixthLowerAlpha, truncatedSixthLowerSigma] at h ⊢
  linarith

theorem G_pair_lt_fifty_two : Glin (1/3) + Glin s < 52 := by
  have h1 := log_two_upper
  have h2 := SecondFunctionalFourSevenths.log_chord_bound
    (a := 2*a) (b := s) (by norm_num [a, truncatedSixthLowerAlpha])
    (by norm_num [s,a,truncatedSixthLowerSigma,truncatedSixthLowerAlpha])
  have h3 := SecondFunctionalFourSevenths.log_chord_bound
    (a := (1 : ℝ)) (b := 6*a/s) (by norm_num)
    (by norm_num [s,a,truncatedSixthLowerSigma,truncatedSixthLowerAlpha])
  have hid : log (s/a) = log 2 + log (s/(2*a)) := by
    rw [← log_mul (by norm_num : (2 : ℝ) ≠ 0) (by
      norm_num [s,a,truncatedSixthLowerSigma,truncatedSixthLowerAlpha])]
    congr 1
    ring
  have h := G_pair_log_upper
  rw [hid] at h
  norm_num [s,a,truncatedSixthLowerSigma,truncatedSixthLowerAlpha] at h2 h3 h ⊢
  linarith

end Wu2008DoubleSieve.ClassicalSingleBounds

import MathlibNt.Wu2008DoubleSieve.VariableUpperEnvelope

namespace Wu2008DoubleSieve.VariableGIntegral
open Real Set MeasureTheory ClassicalAnalyticLeaves SharpLogRecurrence VariableUpperEnvelope
open scoped Interval

noncomputable abbrev a : ℝ := truncatedSixthLowerAlpha
noncomputable abbrev s : ℝ := truncatedSixthLowerSigma
noncomputable abbrev c (j : ℝ) : ℝ := SharpSingleBalance.c j
noncomputable def logCoefficient : ℝ := -1/(48*a^3)+1/(2*a^2)-15/(4*a)+11
noncomputable def linearCoefficient : ℝ := 1/(12*a^3)-1/a^2
noncomputable def majorant (t : ℝ) : ℝ := cubic ((1/2-t)/a)/(t*(1/2-t))
noncomputable def primitive (t : ℝ) : ℝ :=
  logCoefficient*log t+linearCoefficient*t-t^2/(24*a^3)-11*log (1/2-t)

 theorem geometry : 0 < a ∧ a ≤ c 4 ∧ c 4 ≤ s ∧ s ≤ 1/3 := by
  norm_num [a,s,c,SharpSingleBalance.c,SharpSingleBalance.a,
    truncatedSixthLowerAlpha,truncatedSixthLowerSigma]

 theorem pointwise_upper {t : ℝ} (ht : t ∈ Icc (c 4) s) :
    ClassicalSingleBounds.g t ≤ majorant t := by
  have ht0 : 0 < t := geometry.1.trans_le (geometry.2.1.trans ht.1)
  have hd : 0 < 1/2-t := by linarith [ht.2, geometry.2.2.2]
  have hu : 3 ≤ (1/2-t)/a := (le_div_iff₀ geometry.1).2 (by
    have hh : t ≤ 1/2-3*a := ht.2
    linarith)
  have hu4 : (1/2-t)/a ≤ 4 := (div_le_iff₀ geometry.1).2 (by
    have hh : 1/2-4*a ≤ t := ht.1
    linarith)
  exact div_le_div_of_nonneg_right (upper_cubic hu hu4) (mul_pos ht0 hd).le

 theorem derivative {t : ℝ} (ht : t ≠ 0) (hd : 1/2-t ≠ 0) :
    HasDerivAt primitive (majorant t) t := by
  have ha : a ≠ 0 := geometry.1.ne'
  have hd2 : 1-t*2 ≠ 0 := by intro h; apply hd; linarith
  have h := ((((hasDerivAt_log ht).const_mul logCoefficient).add
    ((hasDerivAt_id t).const_mul linearCoefficient)).sub
    (((hasDerivAt_id t).pow 2).div_const (24*a^3))).sub
    ((((hasDerivAt_const t (1/2 : ℝ)).sub (hasDerivAt_id t)).log hd).const_mul 11)
  convert h using 1 <;> first | rfl | (dsimp [majorant,cubic,logCoefficient,linearCoefficient]; field_simp [ha,hd2]; ring_nf; field_simp [hd2]; ring)

 theorem integrable : IntervalIntegrable majorant volume (c 4) s := by
  apply ContinuousOn.intervalIntegrable
  unfold majorant cubic
  apply ContinuousOn.div
  · fun_prop
  · fun_prop
  · intro t ht
    rw [uIcc_of_le geometry.2.2.1] at ht
    have ht0 := geometry.1.trans_le (geometry.2.1.trans ht.1)
    have hd : 0 < 1/2-t := by linarith [ht.2,geometry.2.2.2]
    exact (mul_pos ht0 hd).ne'

 theorem integral_upper :
    (∫ t in c 4..s, ClassicalSingleBounds.g t) ≤ primitive s-primitive (c 4) := by
  have hi := intervalIntegral.integral_mono_on geometry.2.2.1
    (ClassicalSingleBounds.g_integrable geometry.2.1 geometry.2.2.2 geometry.2.2.1)
    integrable (fun t ht => pointwise_upper ht)
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt _ integrable] at hi
  · exact hi
  · intro t ht
    rw [uIcc_of_le geometry.2.2.1] at ht
    exact derivative (geometry.1.trans_le (geometry.2.1.trans ht.1)).ne'
      (show 1/2-t ≠ 0 by linarith [ht.2,geometry.2.2.2])

 theorem endpoint : primitive s-primitive (c 4) =
    logCoefficient*log (s/c 4)+linearCoefficient*(s-c 4)-
      (s^2-(c 4)^2)/(24*a^3)+11*log (4/3 : ℝ) := by
  have hc0 : 0 < c 4 := geometry.1.trans_le geometry.2.1
  have hs0 : 0 < s := hc0.trans_le geometry.2.2.1
  have he : log (1/2-c 4)-log (1/2-s) = log (4/3 : ℝ) := by
    rw [← log_div (by norm_num [c,SharpSingleBalance.c,SharpSingleBalance.a,truncatedSixthLowerAlpha])
      (by norm_num [s,truncatedSixthLowerSigma,truncatedSixthLowerAlpha])]
    congr 1
    norm_num [s,c,SharpSingleBalance.c,SharpSingleBalance.a,truncatedSixthLowerAlpha,truncatedSixthLowerSigma]
  rw [log_div hs0.ne' hc0.ne']
  unfold primitive
  rw [← he]
  ring

/-- The new variable estimate replaces only the old constant payment on [c(4),sigma]. -/
 theorem full_G_upper :
    SingleUpperClassicalLimit.Glin (1/3)+SingleUpperClassicalLimit.Glin s ≤
      (8/a)*((42823/151875)*log (c 5/a)+(311/1080)*log (c 4/c 5))+
        8*(primitive s-primitive (c 4))+8*log (6*a/s) := by
  have ha := geometry.1
  have h5 : a ≤ c 5 := by norm_num [c,SharpSingleBalance.c,SharpSingleBalance.a,a,truncatedSixthLowerAlpha]
  have h54 : c 5 ≤ c 4 := by norm_num [c,SharpSingleBalance.c,SharpSingleBalance.a,truncatedSixthLowerAlpha]
  have hseg5 := SharpSingleBalance.g_segment (by norm_num : (0 : ℝ) < 5) le_rfl le_rfl
    (h54.trans (geometry.2.2.1.trans geometry.2.2.2)) h5
  have hseg4 := SharpSingleBalance.g_segment (by norm_num : (0 : ℝ) < 4) h5 le_rfl
    (geometry.2.2.1.trans geometry.2.2.2) h54
  have hl5 : 0 ≤ log (c 5)-log a := sub_nonneg.mpr (log_le_log ha h5)
  have hl4 : 0 ≤ log (c 4)-log (c 5) := sub_nonneg.mpr (log_le_log (ha.trans_le h5) h54)
  have hq5 := mul_le_mul_of_nonneg_right
    (div_le_div_of_nonneg_right upper_five_div ha.le) hl5
  have hq4 := mul_le_mul_of_nonneg_right
    (div_le_div_of_nonneg_right upper_four_div ha.le) hl4
  have hi5 := ClassicalSingleBounds.g_integrable h5 (geometry.2.2.1.trans geometry.2.2.2) h54
  have hi0 := ClassicalSingleBounds.g_integrable le_rfl
    (h54.trans (geometry.2.2.1.trans geometry.2.2.2)) h5
  have hi4 := ClassicalSingleBounds.g_integrable geometry.2.1 geometry.2.2.2 geometry.2.2.1
  have his := hi0.trans (hi5.trans hi4)
  have hih := ClassicalSingleBounds.g_integrable (geometry.2.1.trans geometry.2.2.1) le_rfl geometry.2.2.2
  have he54 := intervalIntegral.integral_add_adjacent_intervals hi0 hi5
  have he43 := intervalIntegral.integral_add_adjacent_intervals (hi0.trans hi5) hi4
  have hesh := intervalIntegral.integral_add_adjacent_intervals his hih
  have heh := ClassicalSingleBounds.high_integral_eq
  have hnew := integral_upper
  have he1 : SingleUpperClassicalLimit.Glin (1/3) =
      4*∫ t in a..(1/3 : ℝ), ClassicalSingleBounds.g t := by
    simp only [SingleUpperClassicalLimit.Glin,SingleUpperClassicalLimit.Gdelta,sub_zero,
      ClassicalSingleBounds.g,a,ClassicalSingleBounds.a]
  have he2 : SingleUpperClassicalLimit.Glin s =
      4*∫ t in a..s, ClassicalSingleBounds.g t := by
    simp only [SingleUpperClassicalLimit.Glin,SingleUpperClassicalLimit.Gdelta,sub_zero,
      ClassicalSingleBounds.g,a,ClassicalSingleBounds.a]
  rw [he1,he2,log_div (ha.trans_le h5).ne' ha.ne',
    log_div (ha.trans_le geometry.2.1).ne' (ha.trans_le h5).ne']
  change (∫ t in s..(1/3 : ℝ), ClassicalSingleBounds.g t) = 2*log (6*a/s) at heh
  change (∫ t in a..c 5, ClassicalSingleBounds.g t) ≤
    (wuUpperCoefficient 5/5)/a*(log (c 5)-log a) at hseg5
  change (∫ t in c 5..c 4, ClassicalSingleBounds.g t) ≤
    (wuUpperCoefficient 4/4)/a*(log (c 4)-log (c 5)) at hseg4
  norm_num [a,ClassicalSingleBounds.a,truncatedSixthLowerAlpha] at hq5 hq4 hseg5 hseg4 he54 he43 hesh heh ⊢
  linarith

end Wu2008DoubleSieve.VariableGIntegral

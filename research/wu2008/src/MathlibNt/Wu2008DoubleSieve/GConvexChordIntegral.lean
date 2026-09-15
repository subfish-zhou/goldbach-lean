import MathlibNt.Wu2008DoubleSieve.GConvexChord

namespace Wu2008DoubleSieve.GConvexChord
open Real Set MeasureTheory SharpLogRecurrence
open scoped Interval
open VariableGIntegral (a s c)

noncomputable def majorant (t : ℝ) : ℝ := m/(a*t)+C/(t*(1/2-t))
noncomputable def primitive (t : ℝ) : ℝ := (m/a+2*C)*log t-2*C*log (1/2-t)
noncomputable def endpoint : ℝ := (m/a+2*C)*log (c 4/c 5)+2*C*log (5/4 : ℝ)

theorem geometry : 0 < a ∧ a ≤ c 5 ∧ c 5 ≤ c 4 ∧ c 4 ≤ s ∧ s ≤ 1/3 := by
  norm_num [a,s,c,SharpSingleBalance.c,SharpSingleBalance.a,
    truncatedSixthLowerAlpha,truncatedSixthLowerSigma]

theorem pointwise_upper {t : ℝ} (ht : t ∈ Icc (c 5) (c 4)) :
    ClassicalSingleBounds.g t ≤ majorant t := by
  have ht0 : 0 < t := geometry.1.trans_le (geometry.2.1.trans ht.1)
  have hd : 0 < 1/2-t := by linarith [ht.2,geometry.2.2.2.1,geometry.2.2.2.2]
  have hu : (1/2-t)/a ∈ Icc (4 : ℝ) 5 := by
    constructor
    · apply (le_div_iff₀ geometry.1).2
      have hh : t ≤ 1/2-4*a := ht.2
      linarith
    · apply (div_le_iff₀ geometry.1).2
      have hh : 1/2-5*a ≤ t := ht.1
      linarith
  have h := div_le_div_of_nonneg_right (upper_chord hu) (mul_pos ht0 hd).le
  change wuUpperCoefficient ((1/2-t)/a)/(t*(1/2-t)) ≤ _
  apply h.trans_eq
  dsimp [majorant]
  have hd2 : 1-t*2 ≠ 0 := by intro h; apply hd.ne'; linarith
  field_simp [ht0.ne',hd.ne',hd2]
  ring_nf
  field_simp [hd2]
  ring

theorem primitive_derivative {t : ℝ} (ht : t ≠ 0) (hd : 1/2-t ≠ 0) :
    HasDerivAt primitive (majorant t) t := by
  have h := ((hasDerivAt_log ht).const_mul (m/a+2*C)).sub
    ((((hasDerivAt_const t (1/2 : ℝ)).sub (hasDerivAt_id t)).log hd).const_mul (2*C))
  have hd2 : 1-t*2 ≠ 0 := by intro h; apply hd; linarith
  convert h using 1 <;> first | rfl | (dsimp [majorant]; field_simp [ht,hd,hd2]; ring)

theorem majorant_integrable : IntervalIntegrable majorant volume (c 5) (c 4) := by
  apply ContinuousOn.intervalIntegrable
  intro t ht
  rw [uIcc_of_le geometry.2.2.1] at ht
  have ht0 := geometry.1.trans_le (geometry.2.1.trans ht.1)
  have hd : 0 < 1/2-t := by linarith [ht.2,geometry.2.2.2.1,geometry.2.2.2.2]
  unfold majorant
  apply ContinuousAt.continuousWithinAt
  exact (continuousAt_const.div (continuousAt_const.mul continuousAt_id)
    (mul_pos geometry.1 ht0).ne').add
    (continuousAt_const.div (continuousAt_id.mul (continuousAt_const.sub continuousAt_id))
      (mul_pos ht0 hd).ne')

theorem primitive_endpoint : primitive (c 4)-primitive (c 5) = endpoint := by
  have h5 : 0 < c 5 := geometry.1.trans_le geometry.2.1
  have h4 : 0 < c 4 := h5.trans_le geometry.2.2.1
  have he : log (1/2-c 5)-log (1/2-c 4) = log (5/4 : ℝ) := by
    rw [← log_div (by norm_num [c,SharpSingleBalance.c,SharpSingleBalance.a,truncatedSixthLowerAlpha])
      (by norm_num [c,SharpSingleBalance.c,SharpSingleBalance.a,truncatedSixthLowerAlpha])]
    congr 1
    norm_num [c,SharpSingleBalance.c,SharpSingleBalance.a,truncatedSixthLowerAlpha]
  unfold endpoint primitive
  rw [log_div h4.ne' h5.ne',← he]
  ring

/-- FTC is applied to the original variable, not to numerical quadrature. -/
theorem majorant_integral_eq : (∫ t in c 5..c 4, majorant t) = endpoint := by
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt _ majorant_integrable,primitive_endpoint]
  intro t ht
  rw [uIcc_of_le geometry.2.2.1] at ht
  exact primitive_derivative (geometry.1.trans_le (geometry.2.1.trans ht.1)).ne'
    (show 1/2-t ≠ 0 by linarith [ht.2,geometry.2.2.2.1,geometry.2.2.2.2])

theorem integral_upper : (∫ t in c 5..c 4, ClassicalSingleBounds.g t) ≤ endpoint := by
  rw [← majorant_integral_eq]
  exact intervalIntegral.integral_mono_on geometry.2.2.1
    (ClassicalSingleBounds.g_integrable geometry.2.1
      (geometry.2.2.2.1.trans geometry.2.2.2.2) geometry.2.2.1)
    majorant_integrable (fun _ ht => pointwise_upper ht)

/-- Assemble all four actual integral segments by integrability and additivity. -/
theorem full_G_upper :
    SingleUpperClassicalLimit.Glin (1/3)+SingleUpperClassicalLimit.Glin s ≤
      (8/a)*(42823/151875)*log (c 5/a)+8*endpoint+
      8*(VariableGIntegral.primitive s-VariableGIntegral.primitive (c 4))+8*log (6*a/s) := by
  have ha := geometry.1
  have h5 := geometry.2.1
  have h54 := geometry.2.2.1
  have h4s := geometry.2.2.2.1
  have hs := geometry.2.2.2.2
  have ha4 := h5.trans h54
  have hseg5 := SharpSingleBalance.g_segment (by norm_num : (0 : ℝ) < 5) le_rfl le_rfl
    (h54.trans (h4s.trans hs)) h5
  have hl5 : 0 ≤ log (c 5)-log a := sub_nonneg.mpr (log_le_log ha h5)
  have hq5 := mul_le_mul_of_nonneg_right
    (div_le_div_of_nonneg_right upper_five_div ha.le) hl5
  have hi5 := ClassicalSingleBounds.g_integrable h5 (h4s.trans hs) h54
  have hi0 := ClassicalSingleBounds.g_integrable le_rfl (h54.trans (h4s.trans hs)) h5
  have hi4 := ClassicalSingleBounds.g_integrable ha4 hs h4s
  have his := hi0.trans (hi5.trans hi4)
  have hih := ClassicalSingleBounds.g_integrable (ha4.trans h4s) le_rfl hs
  have he54 := intervalIntegral.integral_add_adjacent_intervals hi0 hi5
  have he43 := intervalIntegral.integral_add_adjacent_intervals (hi0.trans hi5) hi4
  have hesh := intervalIntegral.integral_add_adjacent_intervals his hih
  have heh := ClassicalSingleBounds.high_integral_eq
  have hchord := integral_upper
  have hcubic := VariableGIntegral.integral_upper
  have he1 : SingleUpperClassicalLimit.Glin (1/3) =
      4*∫ t in a..(1/3 : ℝ), ClassicalSingleBounds.g t := by
    simp only [SingleUpperClassicalLimit.Glin,SingleUpperClassicalLimit.Gdelta,sub_zero,
      ClassicalSingleBounds.g,a,ClassicalSingleBounds.a]
  have he2 : SingleUpperClassicalLimit.Glin s =
      4*∫ t in a..s, ClassicalSingleBounds.g t := by
    simp only [SingleUpperClassicalLimit.Glin,SingleUpperClassicalLimit.Gdelta,sub_zero,
      ClassicalSingleBounds.g,a,ClassicalSingleBounds.a]
  rw [he1,he2,log_div (ha.trans_le h5).ne' ha.ne']
  change (∫ t in s..(1/3 : ℝ), ClassicalSingleBounds.g t) = 2*log (6*a/s) at heh
  change (∫ t in a..c 5, ClassicalSingleBounds.g t) ≤
    (wuUpperCoefficient 5/5)/a*(log (c 5)-log a) at hseg5
  norm_num [a,ClassicalSingleBounds.a,truncatedSixthLowerAlpha] at hq5 hseg5 he54 he43 hesh heh ⊢
  linarith

end Wu2008DoubleSieve.GConvexChord

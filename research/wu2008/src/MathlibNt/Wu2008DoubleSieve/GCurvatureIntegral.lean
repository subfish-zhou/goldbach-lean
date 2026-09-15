import MathlibNt.Wu2008DoubleSieve.GCurvatureChord
import MathlibNt.Wu2008DoubleSieve.GConvexChordCount

namespace Wu2008DoubleSieve.GCurvatureChord
open Real Set MeasureTheory SharpLogRecurrence
open scoped Interval
open VariableGIntegral (a s c logCoefficient linearCoefficient)
open GConvexChord (geometry endpoint)

noncomputable def deficitPrimitive (t : ℝ) : ℝ :=
  (-t^3/3+(c 4+c 5)*t^2/2-c 4*c 5*t)/(9*a^2)

theorem deficit_derivative (t : ℝ) : HasDerivAt deficitPrimitive (deficit t) t := by
  convert (((((hasDerivAt_id t).pow 3).neg.div_const 3).add
    (((hasDerivAt_id t).pow 2).const_mul (c 4+c 5) |>.div_const 2)).sub
    ((hasDerivAt_id t).const_mul (c 4*c 5))).div_const (9*a^2) using 1 <;>
    first | rfl | (dsimp [deficit]; ring)

theorem deficit_integrable (x y : ℝ) : IntervalIntegrable deficit volume x y := by
  apply Continuous.intervalIntegrable
  unfold deficit
  fun_prop

/-- A genuine polynomial FTC; no numerical integral is used. -/
theorem deficit_integral_eq : (∫ t in c 5..c 4, deficit t) = a/54 := by
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (fun t _ => deficit_derivative t)
    (deficit_integrable _ _)]
  norm_num [deficitPrimitive,c,a,SharpSingleBalance.c,SharpSingleBalance.a,
    truncatedSixthLowerAlpha]

theorem integral_joint_upper :
    (∫ t in c 5..c 4, ClassicalSingleBounds.g t)+a/54 ≤ endpoint := by
  have hg := ClassicalSingleBounds.g_integrable geometry.2.1
    (geometry.2.2.2.1.trans geometry.2.2.2.2) geometry.2.2.1
  have h := intervalIntegral.integral_mono_on geometry.2.2.1
    (hg.add (deficit_integrable _ _)) GConvexChord.majorant_integrable
    (fun _ ht => pointwise_joint ht)
  rw [intervalIntegral.integral_add hg (deficit_integrable _ _),
    deficit_integral_eq,GConvexChord.majorant_integral_eq] at h
  exact h

noncomputable def deltaG : ℝ := 4*a/27

theorem deltaG_exact : deltaG = (400/35829 : ℝ) := by
  norm_num [deltaG,a,truncatedSixthLowerAlpha]

theorem deltaG_pos : 0 < deltaG := by rw [deltaG_exact]; norm_num

/-- Assemble all four actual integral segments by integrability and additivity. -/
theorem full_G_upper :
    SingleUpperClassicalLimit.Glin (1/3)+SingleUpperClassicalLimit.Glin s ≤
      (8/a)*(42823/151875)*log (c 5/a)+8*endpoint+
      8*(VariableGIntegral.primitive s-VariableGIntegral.primitive (c 4))+8*log (6*a/s)-deltaG := by
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
  have hchord := integral_joint_upper
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
  dsimp [deltaG]
  linarith

theorem full_G_rational :
    SingleUpperClassicalLimit.Glin (1/3)+SingleUpperClassicalLimit.Glin s ≤ GConvexChord.rationalG-deltaG := by
  have h := full_G_upper
  rw [VariableGIntegral.endpoint] at h
  have h1 := log_upper (t := c 5/a)
    (by norm_num [c,SharpSingleBalance.c,SharpSingleBalance.a,a,truncatedSixthLowerAlpha])
  have h2 := log_upper (t := c 4/c 5)
    (by norm_num [c,SharpSingleBalance.c,SharpSingleBalance.a,truncatedSixthLowerAlpha])
  have h3 := log_upper (t := s/c 4)
    (by norm_num [s,c,SharpSingleBalance.c,SharpSingleBalance.a,truncatedSixthLowerAlpha,truncatedSixthLowerSigma])
  have h4 := log_upper (t := (4/3 : ℝ)) (by norm_num)
  have h5 := log_upper (t := 6*a/s)
    (by norm_num [s,a,truncatedSixthLowerAlpha,truncatedSixthLowerSigma])
  have h6 := log_upper (t := (5/4 : ℝ)) (by norm_num)
  unfold GConvexChord.rationalG GConvexChord.endpoint at *
  norm_num [GConvexChord.m,GConvexChord.C,GConvexChord.r4,GConvexChord.r5,logCoefficient,linearCoefficient,a,truncatedSixthLowerAlpha] at h h1 h5 ⊢
  linarith

theorem full_G_strict :
    SingleUpperClassicalLimit.Glin (1/3)+SingleUpperClassicalLimit.Glin s <
      GConvexChord.rationalG := by
  linarith only [full_G_rational,deltaG_pos]

end Wu2008DoubleSieve.GCurvatureChord

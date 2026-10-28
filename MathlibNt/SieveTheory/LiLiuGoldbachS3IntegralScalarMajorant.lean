import MathlibNt.SieveTheory.LiLiuGoldbachS3IntegralScalarBase

open Set MeasureTheory
open MathlibNt.SieveTheory.SwitchingPrinciple

namespace MathlibNt.SieveTheory.LiLiuOnePlusOneNine.GoldbachBig

/-- A whole-interval pointwise bound for the derivative of the inner integral. -/
theorem goldbachS3_inner_derivative_quadratic_majorant {t : ℝ} (ht : 3 ≤ t) :
    Real.log (t - 2) / (t - 1) ≤ (t - 3) / 2 := by
  have hlog : Real.log (t - 2) ≤ t - 3 := by
    have h := Real.log_le_sub_one_of_pos (show 0 < t - 2 by linarith)
    linarith
  apply (div_le_iff₀ (show 0 < t - 1 by linarith)).2
  nlinarith [sq_nonneg (t - 3)]

/-- The shift needed for the analytic envelope, retaining the actual inner integral. -/
theorem goldbachS3_inner_shift (s : ℝ) :
    jurkatRichertInnerIntegral s =
      ∫ t in (3 : ℝ)..s, Real.log (t - 2) / (t - 1) := by
  unfold jurkatRichertInnerIntegral
  have h := intervalIntegral.integral_comp_sub_right
    (a := (3 : ℝ)) (b := s) (fun t : ℝ => Real.log (t - 1) / t) 1
  norm_num only at h
  simpa only [sub_sub, show (1 + 1 : ℝ) = 2 by norm_num] using h.symm

/-- Local analytic regularity used in the envelope comparison. -/
theorem goldbachS3_inner_kernel_continuousOn {a b : ℝ} (ha : 3 ≤ a) :
    ContinuousOn (fun t : ℝ => Real.log (t - 2) / (t - 1)) (Icc a b) := by
  apply ContinuousOn.div
  · exact (continuousOn_id.sub continuousOn_const).log
      (fun t ht => by dsimp; linarith [ht.1])
  · exact continuousOn_id.sub continuousOn_const
  · intro t ht
    dsimp
    linarith [ht.1]

/-- A closed, quadratic envelope for the actual inner integral. -/
theorem goldbachS3_inner_quadratic_majorant {s : ℝ} (hs : 3 ≤ s) :
    jurkatRichertInnerIntegral s ≤ (s - 3)^2 / 4 := by
  rw [goldbachS3_inner_shift]
  have hf : IntervalIntegrable (fun t : ℝ => Real.log (t - 2) / (t - 1)) volume 3 s := by
    apply ContinuousOn.intervalIntegrable
    rw [uIcc_of_le hs]
    exact goldbachS3_inner_kernel_continuousOn le_rfl
  have hg : IntervalIntegrable (fun t : ℝ => (t - 3) / 2) volume 3 s :=
    ((continuous_id.sub continuous_const).div_const 2).intervalIntegrable _ _
  have h := intervalIntegral.integral_mono_on hs hf hg
    (fun t ht => goldbachS3_inner_derivative_quadratic_majorant ht.1)
  have he : (∫ t in (3 : ℝ)..s, (t - 3) / 2) = (s - 3)^2 / 4 := by
    have hd : ∀ t ∈ uIcc (3 : ℝ) s,
        HasDerivAt (fun t : ℝ => (t - 3)^2 / 4) ((t - 3) / 2) t := by
      intro t _
      convert (((hasDerivAt_id t).sub_const 3).pow 2).div_const 4 using 1 <;> first | rfl | (simp only [id_eq]; ring)
    simpa using intervalIntegral.integral_eq_sub_of_hasDerivAt hd hg
  exact he ▸ h

/-- Inner-integral continuity on arbitrary compact positive ranges. -/
theorem goldbachS3_inner_continuousOn {b : ℝ} (hb : 3 ≤ b) :
    ContinuousOn jurkatRichertInnerIntegral (Icc 3 b) := by
  have hi : IntervalIntegrable (fun t : ℝ => Real.log (t - 2) / (t - 1)) volume 3 b := by
    apply ContinuousOn.intervalIntegrable
    rw [uIcc_of_le hb]
    exact goldbachS3_inner_kernel_continuousOn le_rfl
  have h := intervalIntegral.continuousOn_primitive_interval' hi
    (show (3 : ℝ) ∈ uIcc 3 b by rw [uIcc_of_le hb]; exact ⟨le_rfl, hb⟩)
  rw [uIcc_of_le hb] at h
  exact h.congr (fun s _ => goldbachS3_inner_shift s)


/-- Continuity of the inner correction as a function of the upper variable. -/
theorem goldbachS3_nested_inner_continuousOn {b : ℝ} (hb : 5 ≤ b) :
    ContinuousOn (fun t : ℝ => ∫ v in (3 : ℝ)..t - 2,
      jurkatRichertInnerIntegral v / v) (Icc 5 b) := by
  have hb3 : 3 ≤ b - 2 := by linarith
  have hi : IntervalIntegrable (fun v : ℝ => jurkatRichertInnerIntegral v / v)
      volume 3 (b - 2) := by
    apply ContinuousOn.intervalIntegrable
    rw [uIcc_of_le hb3]
    exact (goldbachS3_inner_continuousOn hb3).div continuousOn_id
      (fun v hv => by dsimp; linarith [hv.1])
  have h := intervalIntegral.continuousOn_primitive_interval' hi
    (show (3 : ℝ) ∈ uIcc 3 (b - 2) by rw [uIcc_of_le hb3]; exact ⟨le_rfl, hb3⟩)
  rw [uIcc_of_le hb3] at h
  exact h.comp (continuousOn_id.sub continuousOn_const)
    (fun t ht => ⟨by linarith [ht.1], by linarith [ht.2]⟩)


/-- The log part of the third branch is exactly the increment of the inner integral. -/
theorem goldbachS3_inner_increment {s : ℝ} (hs : 5 ≤ s) :
    jurkatRichertInnerIntegral 5 + (∫ t in (5 : ℝ)..s,
      Real.log (t - 2) / (t - 1)) = jurkatRichertInnerIntegral s := by
  rw [goldbachS3_inner_shift, goldbachS3_inner_shift]
  apply intervalIntegral.integral_add_adjacent_intervals
  · apply ContinuousOn.intervalIntegrable
    rw [uIcc_of_le (by norm_num : (3 : ℝ) ≤ 5)]
    exact goldbachS3_inner_kernel_continuousOn le_rfl
  · apply ContinuousOn.intervalIntegrable
    rw [uIcc_of_le hs]
    exact goldbachS3_inner_kernel_continuousOn (by norm_num)

/-- The third numerator is the full inner integral plus its genuine correction. -/
theorem goldbachS3_third_body_split {s : ℝ} (hs : 5 ≤ s) :
    1 + jurkatRichertInnerIntegral 5 + (∫ t in (5 : ℝ)..s,
      (Real.log (t - 2) + ∫ v in (3 : ℝ)..t - 2,
        jurkatRichertInnerIntegral v / v) / (t - 1)) =
    1 + jurkatRichertInnerIntegral s + (∫ t in (5 : ℝ)..s,
      (∫ v in (3 : ℝ)..t - 2, jurkatRichertInnerIntegral v / v) / (t - 1)) := by
  have hlog : IntervalIntegrable (fun t : ℝ => Real.log (t - 2) / (t - 1)) volume 5 s := by
    apply ContinuousOn.intervalIntegrable
    rw [uIcc_of_le hs]
    exact goldbachS3_inner_kernel_continuousOn (by norm_num)
  have hcorr : IntervalIntegrable (fun t : ℝ => (∫ v in (3 : ℝ)..t - 2,
      jurkatRichertInnerIntegral v / v) / (t - 1)) volume 5 s := by
    apply ContinuousOn.intervalIntegrable
    rw [uIcc_of_le hs]
    exact (goldbachS3_nested_inner_continuousOn hs).div
      (continuousOn_id.sub continuousOn_const) (fun t ht => by dsimp; linarith [ht.1])
  simp_rw [add_div]
  rw [intervalIntegral.integral_add hlog hcorr]
  linarith [goldbachS3_inner_increment hs]


end MathlibNt.SieveTheory.LiLiuOnePlusOneNine.GoldbachBig
import MathlibNt.Wu2008DoubleSieve.ClassicalLogFourBounds

namespace Wu2008DoubleSieve.ClassicalPositiveBounds
open Real Set MeasureTheory ClassicalAnalyticLeaves ClassicalLogBounds
open scoped Interval

noncomputable abbrev a : ℝ := truncatedSixthLowerAlpha
noncomputable abbrev b : ℝ := truncatedSixthLowerBeta
noncomputable abbrev s : ℝ := truncatedSixthLowerSigma

/-- A whole-box polynomial comparison, not a finite sample certificate. -/
theorem denominator_box {x y X Y : ℝ} (hx0 : 0 ≤ x) (hy0 : 0 ≤ y)
    (hx : x ≤ X) (hy : y ≤ Y) (hgate : X+2*Y ≤ 1/2) (hxy : X ≤ Y) :
    x*y*(1/2-x-y) ≤ X*Y*(1/2-X-Y) := by
  have h1 : 0 ≤ (X-x)*y*(1/2-X-x-y) :=
    mul_nonneg (mul_nonneg (sub_nonneg.mpr hx) hy0) (by linarith)
  have h2 : 0 ≤ X*(Y-y)*(1/2-X-Y-y) :=
    mul_nonneg (mul_nonneg (hx0.trans hx) (sub_nonneg.mpr hy)) (by linarith)
  nlinarith

theorem lower_seed_half {u : ℝ} (hu : 8/3 ≤ u) : 1/2 ≤ wuLowerCoefficient u := by
  have hm := lower_mono (by norm_num : (2 : ℝ) ≤ 8/3) hu
  have hl := lower_ge_log (by norm_num : (2 : ℝ) ≤ 8/3)
  have ht := log_tangent_lower (a := (1 : ℝ)) (b := 5/3) (by norm_num) (by norm_num)
  norm_num at hl ht
  linarith

theorem lower_seed_four_fifths {u : ℝ} (hu : 10/3 ≤ u) : 4/5 ≤ wuLowerCoefficient u := by
  have hm := lower_mono (by norm_num : (2 : ℝ) ≤ 10/3) hu
  have hl := lower_ge_log (by norm_num : (2 : ℝ) ≤ 10/3)
  have ht := log_tangent_lower (a := (1 : ℝ)) (b := 7/3) (by norm_num) (by norm_num)
  norm_num at hl ht
  linarith

theorem fifth_regular_eq {x y : ℝ} (hx : a ≤ x) (hxy : x ≤ y) (hy : y ≤ b) :
    fifthPairRegular 0 (x,y) =
      wuLowerCoefficient (truncatedSixthLowerS 0 x y)/(x*y*(1/2-x-y)) := by
  have hv : (x,y) ∈ fifthPairRegion := ⟨hx,hxy,hy⟩
  have h := fifthPair_kernel_original (by norm_num : (0 : ℝ) ≤ 0) (by norm_num) hv
  rw [fifthPair_kernel_regular (by norm_num) (by norm_num), indicator_of_mem hv] at h
  simpa [truncatedSixthLowerC] using h

theorem fifth_seed {x y : ℝ} (hx : a ≤ x) (hxy : x ≤ y) (hy : y ≤ b) :
    200 ≤ fifthPairRegular 0 (x,y) := by
  have ha := truncatedSixthLower_parameters.1
  have hx0 := ha.trans_le hx
  have hy0 := hx0.trans_le hxy
  have hu : 10/3 ≤ truncatedSixthLowerS 0 x y := by
    apply (le_div_iff₀ ha).2
    dsimp [truncatedSixthLowerC]
    have hx2 := hxy.trans hy
    norm_num [a,b,truncatedSixthLowerAlpha,truncatedSixthLowerBeta] at hx hx2 hy ⊢
    linarith
  have hl := lower_seed_four_fifths hu
  have hd := denominator_box hx0.le hy0.le (hxy.trans hy) hy
    (by norm_num [b,truncatedSixthLowerBeta]) le_rfl
  have hdp : 0 < x*y*(1/2-x-y) := by
    have hp : 0 < (1/2 : ℝ)-x-y := by
      have hb : b < 1/4 := by norm_num [b,truncatedSixthLowerBeta]
      linarith
    exact mul_pos (mul_pos hx0 hy0) hp
  rw [fifth_regular_eq hx hxy hy]
  apply (le_div_iff₀ hdp).2
  norm_num [b,truncatedSixthLowerBeta] at hd
  linarith

theorem fifth_gt_four_fifths : (4/5 : ℝ) < fifthPairFlin := by
  have hp := truncatedSixthLower_parameters
  have hc : Continuous (fun v : ℝ × ℝ => fifthPairRegular 0 (v.1,v.2)) :=
    fifthPair_regular_continuous.comp (f := fun v : ℝ × ℝ => (0,v)) (by fun_prop)
  have hinner : Continuous (fun y : ℝ => ∫ x in a..y, fifthPairRegular 0 (x,y)) := by
    apply gamma5Gain_moving_integral (f := fun y x : ℝ => fifthPairRegular 0 (x,y))
    · exact hc.comp (f := fun v : ℝ × ℝ => (v.2,v.1)) (by fun_prop)
    · fun_prop
    · fun_prop
  have hi : (∫ y in a..b, 200*(y-a)) ≤
      ∫ y in a..b, ∫ x in a..y, fifthPairRegular 0 (x,y) := by
    apply intervalIntegral.integral_mono_on (μ := volume) hp.2.1.le
      ((by fun_prop : Continuous (fun y : ℝ => 200*(y-a))).intervalIntegrable a b)
      (hinner.intervalIntegrable a b)
    intro y hy
    have h := intervalIntegral.integral_mono_on (μ := volume) hy.1
      (intervalIntegrable_const (c := (200 : ℝ)))
      ((hc.comp (f := fun x : ℝ => (x,y)) (by fun_prop)).intervalIntegrable a y)
      (fun x hx => fifth_seed hx.1 hx.2 hy.2)
    simpa only [intervalIntegral.integral_const, smul_eq_mul, mul_comm, Function.comp_apply] using h
  have he : (∫ y in a..b, 200*(y-a)) = 100*(b-a)^2 := by
    rw [intervalIntegral.integral_const_mul,
      intervalIntegral.integral_sub ((continuous_id' : Continuous (fun x : ℝ => x)).intervalIntegrable a b)
        (intervalIntegrable_const (c := a) (μ := volume)),
      integral_id, intervalIntegral.integral_const]
    simp only [smul_eq_mul]
    ring
  rw [he] at hi
  have hf : fifthPairFlin = 4*∫ y in a..b, ∫ x in a..y, fifthPairRegular 0 (x,y) := by
    unfold fifthPairFlin fifthPairFdelta
    congr 1
    apply intervalIntegral.integral_congr
    intro y hy
    rw [uIcc_of_le hp.2.1.le] at hy
    apply intervalIntegral.integral_congr
    intro x hx
    rw [uIcc_of_le hy.1] at hx
    simpa [truncatedSixthLowerC] using (fifth_regular_eq hx.1 hx.2 hy.2).symm
  rw [hf]
  norm_num [a,b,truncatedSixthLowerAlpha,truncatedSixthLowerBeta] at hi ⊢
  linarith

/-- This rectangle is contained in the retained region; no discarded sixth mass is restored. -/
theorem sixth_seed {x y : ℝ} (hx : x ∈ Icc a b) (hy : y ∈ Icc b (1/6 : ℝ)) :
    100 ≤ truncatedSixthZeroDeltaRegular 0 (x,y) := by
  have hp := truncatedSixthLower_parameters
  have hyS : y ≤ s := hy.2.trans (by norm_num [s,truncatedSixthLowerSigma,truncatedSixthLowerAlpha])
  have hr : truncatedSixthLowerRegion 0 x y := by
    refine ⟨hx.1,hx.2,hy.1,hyS,?_⟩
    have hx2 := hx.2
    norm_num [b,truncatedSixthLowerBeta,truncatedSixthLowerC,truncatedSixthLowerAlpha] at hx2 ⊢
    linarith [hy.2]
  have hbounds := truncatedSixthLower_region_bounds (by norm_num : (0 : ℝ) ≤ 0) hr
  have hu : 8/3 ≤ truncatedSixthLowerS 0 x y := by
    apply (le_div_iff₀ hp.1).2
    have hx2 := hx.2
    norm_num [b,truncatedSixthLowerBeta,truncatedSixthLowerC,truncatedSixthLowerAlpha] at hx2 ⊢
    linarith [hy.2]
  have hl := lower_seed_half hu
  have hd := denominator_box hbounds.1.le hbounds.2.1.le hx.2 hy.2
    (by norm_num [b,truncatedSixthLowerBeta])
    (by norm_num [b,truncatedSixthLowerBeta])
  rw [truncatedSixthZeroDelta_regular_eq (by norm_num) hx ⟨hy.1,hyS⟩, if_pos hr]
  apply (le_div_iff₀ (mul_pos (mul_pos hbounds.1 hbounds.2.1)
    ((mul_pos (by norm_num : (0 : ℝ) < 2) hp.1).trans_le hbounds.2.2.1))).2
  norm_num [truncatedSixthLowerC,b,truncatedSixthLowerBeta] at hd ⊢
  linarith

theorem sixth_regular_nonneg {x y : ℝ} (hx : x ∈ Icc a b) (hy : y ∈ Icc b s) :
    0 ≤ truncatedSixthZeroDeltaRegular 0 (x,y) := by
  rw [truncatedSixthZeroDelta_regular_eq (by norm_num) hx hy]
  split_ifs with hr
  · have hb := truncatedSixthLower_region_bounds (by norm_num : (0 : ℝ) ≤ 0) hr
    apply div_nonneg (lower_nonneg (by linarith [hb.2.2.2.1]))
    exact (mul_pos (mul_pos hb.1 hb.2.1)
      ((mul_pos (by norm_num : (0 : ℝ) < 2) truncatedSixthLower_parameters.1).trans_le hb.2.2.1)).le
  · exact le_rfl

theorem sixth_gt_four_fifths : (4/5 : ℝ) < truncatedSixthLowerF6lin := by
  have hp := truncatedSixthLower_parameters
  have hbm : b ≤ (1/6 : ℝ) := by norm_num [b,truncatedSixthLowerBeta]
  have hms : (1/6 : ℝ) ≤ s := by norm_num [s,truncatedSixthLowerSigma,truncatedSixthLowerAlpha]
  have hc : Continuous (fun v : ℝ × ℝ => truncatedSixthZeroDeltaRegular 0 (v.1,v.2)) :=
    truncatedSixthZeroDelta_regular_continuous.comp (f := fun v : ℝ × ℝ => (0,v)) (by fun_prop)
  have hinner : Continuous (fun x : ℝ => ∫ y in b..s, truncatedSixthZeroDeltaRegular 0 (x,y)) := by
    apply gamma5Gain_moving_integral
      (f := fun x y : ℝ => truncatedSixthZeroDeltaRegular 0 (x,y)) hc <;> fun_prop
  have hpoint (x : ℝ) (hx : x ∈ Icc a b) :
      100*(1/6-b) ≤ ∫ y in b..s, truncatedSixthZeroDeltaRegular 0 (x,y) := by
    have hc1 := hc.comp (f := fun y : ℝ => (x,y)) (by fun_prop)
    have hi := intervalIntegral.integral_mono_on (μ := volume) hbm
      (intervalIntegrable_const (c := (100 : ℝ))) (hc1.intervalIntegrable b (1/6))
      (fun y hy => sixth_seed hx hy)
    have hn : 0 ≤ ∫ y in (1/6 : ℝ)..s, truncatedSixthZeroDeltaRegular 0 (x,y) :=
      intervalIntegral.integral_nonneg hms (fun y hy => sixth_regular_nonneg hx ⟨hbm.trans hy.1,hy.2⟩)
    have he := intervalIntegral.integral_add_adjacent_intervals (μ := volume)
      (hc1.intervalIntegrable b (1/6)) (hc1.intervalIntegrable (1/6) s)
    simp only [intervalIntegral.integral_const, smul_eq_mul, Function.comp_apply] at hi he
    linarith
  have hi := intervalIntegral.integral_mono_on (μ := volume) hp.2.1.le
    (intervalIntegrable_const (c := 100*(1/6-b))) (hinner.intervalIntegrable a b) hpoint
  simp only [intervalIntegral.integral_const, smul_eq_mul] at hi
  have he := truncatedSixthZeroDelta_extension_eq (by norm_num : (0 : ℝ) ≤ 0)
  change (4*∫ x in a..b, ∫ y in b..s, truncatedSixthZeroDeltaRegular 0 (x,y)) =
    truncatedSixthLowerF6lin at he
  norm_num [a,b,truncatedSixthLowerAlpha,truncatedSixthLowerBeta] at hi he
  linarith

end Wu2008DoubleSieve.ClassicalPositiveBounds

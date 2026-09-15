import MathlibNt.Wu2008DoubleSieve.RationalMovingSixth

namespace Wu2008DoubleSieve.FixedCoefficientScalarEnclosure
open Real Set MeasureTheory ClassicalAnalyticLeaves SharpLogRecurrence
open MathlibNt.SieveTheory.JurkatRichert1965ChenGammaOneQOne
open scoped Interval

/-- A global continuation bound; the initial equality is used only at four. -/
theorem lower_affine_upper {s : ℝ} (hs : 4 ≤ s) :
    wuLowerCoefficient s ≤ log 3+(s-4)/3 := by
  have hr := wuLowerCoefficient_sub_eq_integral (by norm_num : (2 : ℝ) ≤ 4) hs
  have he : wuLowerCoefficient 4 = log 3 := by
    convert jr1965f_normalized_firstInterval (s := 4) (by norm_num) le_rfl using 1 <;> norm_num [wuLowerCoefficient]
  have hab : 3 ≤ s-1 := by linarith
  have hi := intervalIntegral.integral_mono_on hab
    (wuUpperCoefficient_div_intervalIntegrable (by norm_num) hab)
    (intervalIntegrable_const (c := (1/3 : ℝ)) (μ := volume))
    (fun u hu => ClassicalLogBounds.upper_div_le_third hu.1)
  simp only [intervalIntegral.integral_const, smul_eq_mul] at hi
  norm_num only [show (4 : ℝ)-1=3 by norm_num, he] at hr
  linarith

theorem lower_ratio_mono {s t : ℝ} (hs : 0 < s) (hst : s ≤ t) :
    wuLowerCoefficient s/s ≤ wuLowerCoefficient t/t := by
  have ht := hs.trans_le hst
  have hf := monotoneOn_jr1965f hs ht hst
  have hd : 0 < 2*exp eulerMascheroniConstant := by positivity
  have hm := div_le_div_of_nonneg_right hf hd.le
  simpa [wuLowerCoefficient, mul_div_assoc, hs.ne', ht.ne'] using hm

theorem lower_five_ratio : wuLowerCoefficient 5/5 ≤ 43/150 := by
  have h := lower_affine_upper (s := 5) (by norm_num)
  have h3 := log_three_bounds.2
  linarith

theorem lower_linear_upper {s : ℝ} (hs : 0 < s) (hs5 : s ≤ 5) :
    wuLowerCoefficient s ≤ (43/150)*s := by
  exact (div_le_iff₀ hs).mp ((lower_ratio_mono hs hs5).trans lower_five_ratio)

noncomputable def quartic (s : ℝ) : ℝ :=
  log (s-1)+(s-4)^3/36-(s-4)^4/144

theorem quartic_density {u : ℝ} (hu : 3 ≤ u) (hu4 : u ≤ 4) :
    wuUpperCoefficient u/u ≤ 1/u+(u-3)^2/12-(u-3)^3/36 := by
  have hu0 : 0 < u := by linarith
  have h := div_le_div_of_nonneg_right (VariableUpperEnvelope.upper_cubic hu hu4) hu0.le
  apply h.trans
  apply (div_le_iff₀ hu0).2
  dsimp [VariableUpperEnvelope.cubic]
  have hp := mul_nonneg (pow_nonneg (show 0 ≤ u-3 by linarith) 3)
    (show 0 ≤ 6-u by linarith)
  have hc : 1/u*u = 1 := div_mul_cancel₀ 1 hu0.ne'
  nlinarith only [hp, hc]

theorem lower_quartic_upper {s : ℝ} (hs : 4 ≤ s) (hs5 : s ≤ 5) :
    wuLowerCoefficient s ≤ quartic s := by
  have hr := wuLowerCoefficient_sub_eq_integral (by norm_num : (2 : ℝ) ≤ 4) hs
  have he : wuLowerCoefficient 4 = log 3 := by
    convert jr1965f_normalized_firstInterval (s := 4) (by norm_num) le_rfl using 1 <;> norm_num [wuLowerCoefficient]
  have hab : 3 ≤ s-1 := by linarith
  have hi : IntervalIntegrable (fun u : ℝ => 1/u+(u-3)^2/12-(u-3)^3/36)
      volume 3 (s-1) := by
    apply ContinuousOn.intervalIntegrable
    apply ContinuousOn.sub
    · apply ContinuousOn.add
      · exact continuousOn_const.div continuousOn_id (fun u hu => by
          rw [uIcc_of_le hab] at hu
          linarith [hu.1])
      · fun_prop
    · fun_prop
  have hm := intervalIntegral.integral_mono_on hab
    (wuUpperCoefficient_div_intervalIntegrable (by norm_num) hab) hi
    (fun u hu => quartic_density hu.1 (by linarith [hu.2]))
  have hd (u : ℝ) (hu : u ∈ uIcc 3 (s-1)) :
      HasDerivAt (fun u : ℝ => log u+(u-3)^3/36-(u-3)^4/144)
        (1/u+(u-3)^2/12-(u-3)^3/36) u := by
    rw [uIcc_of_le hab] at hu
    have h := ((hasDerivAt_log (by linarith [hu.1] : u ≠ 0)).add
      ((((hasDerivAt_id u).sub_const 3).pow 3).div_const 36)).sub
      ((((hasDerivAt_id u).sub_const 3).pow 4).div_const 144)
    convert h using 1 <;> first | rfl | (dsimp; ring)
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hd hi] at hm
  norm_num only [show (4 : ℝ)-1=3 by norm_num, he] at hr
  norm_num at hm
  dsimp [quartic]
  linarith

noncomputable def lowerPrimitive (v : ℝ) : ℝ :=
  (8/3)*log v+8/v-4/v^2+16/(9*v^3)

theorem lowerPrimitive_derivative {v : ℝ} (hv : 2 ≤ v) :
    HasDerivAt lowerPrimitive (lowerLog (v-1)/v) v := by
  have hv0 : v ≠ 0 := by linarith
  have h := (((((hasDerivAt_log hv0).const_mul (8/3)).add
    ((hasDerivAt_const v (8 : ℝ)).div (hasDerivAt_id v) hv0)).sub
    ((hasDerivAt_const v (4 : ℝ)).div ((hasDerivAt_id v).pow 2) (pow_ne_zero 2 hv0))).add
    ((hasDerivAt_const v (16 : ℝ)).div (((hasDerivAt_id v).pow 3).const_mul 9)
      (mul_ne_zero (by norm_num) (pow_ne_zero 3 hv0))))
  convert h using 1 <;> first | rfl | (dsimp [lowerLog]; field_simp [hv0]; ring)

/-- Global lower recurrence envelope, with its actual primitive and domain. -/
theorem upper_global_lower {u : ℝ} (hu : 3 ≤ u) :
    1+lowerPrimitive (u-1)-lowerPrimitive 2 ≤ wuUpperCoefficient u := by
  have hr := wuUpperCoefficient_sub_eq_integral (by norm_num : (2 : ℝ) ≤ 3) hu
  have he : wuUpperCoefficient 3 = 1 := jr1965F_normalized_initial (by norm_num) le_rfl
  have hab : 2 ≤ u-1 := by linarith
  have hi : IntervalIntegrable (fun v => lowerLog (v-1)/v) volume 2 (u-1) := by
    apply ContinuousOn.intervalIntegrable
    have hv0 (v : ℝ) (hv : v ∈ uIcc 2 (u-1)) : v ≠ 0 := by
      rw [uIcc_of_le hab] at hv
      linarith [hv.1]
    have hv : ContinuousOn (fun v : ℝ => (v-1-1)/(v-1+1)) (uIcc 2 (u-1)) :=
      (by fun_prop : ContinuousOn (fun v : ℝ => v-1-1) _).div (by fun_prop)
        (fun v hv => by simpa using hv0 v hv)
    exact (((hv.const_mul 2).add ((hv.pow 3).const_mul 2 |>.div_const 3)).div
      continuousOn_id hv0)
  have hm := intervalIntegral.integral_mono_on hab hi
    (wuLowerCoefficient_div_intervalIntegrable (by norm_num) hab) (fun v hv =>
      div_le_div_of_nonneg_right
        ((log_lower (by linarith [hv.1])).trans (lower_ge_log hv.1)) (by linarith [hv.1]))
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun v hv => lowerPrimitive_derivative (by rw [uIcc_of_le hab] at hv; exact hv.1)) hi] at hm
  norm_num only [show (3 : ℝ)-1=2 by norm_num, he] at hr
  linarith

end Wu2008DoubleSieve.FixedCoefficientScalarEnclosure

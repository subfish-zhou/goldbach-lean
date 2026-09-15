import F1KernelUpperAssembly

noncomputable section
open Real Set Wu2008DoubleSieve SharpLogRecurrence FirstIntegralRecovery
open F1FullRecoveryPayment F1RemainingRecovery
namespace F1UnpaidRecovery

/-- The ratio forced by the right endpoint of the original C projection. -/
def secondFactorRatio : ℝ :=
  ((927/200+2)^3*((927/200)^2+16*(927/200)+4)) /
  ((3*(927/200)-2)^3*(21*(927/200)^2-24*(927/200)+4))

theorem secondFactorRatio_pos : 0 < secondFactorRatio := by
  norm_num [secondFactorRatio]

/-- Rational expression of the existing lower-error payment, with no new approximation. -/
theorem lower_error_rational {x : ℝ} (hx : 1 ≤ x) :
    lowerGapPayment x = (x-1)^5/((x+1)^3*(x^2+8*x+1)) := by
  have hx0 : x ≠ 0 := by linarith
  have hx1 : x+1 ≠ 0 := by linarith
  have hq : x^2+8*x+1 ≠ 0 := by positivity
  dsimp [lowerGapPayment,upperLog,lowerLog]
  field_simp
  ring

/-- Both errors belong to the SAME prescribed single split; no repeated splitting. -/
theorem both_split_errors {u : ℝ} (hu : 2 ≤ u) :
    (u-2)^5/((u+2)^3*(u^2+16*u+4)) +
      (u-2)^5/((3*u-2)^3*(21*u^2-24*u+4)) ≤
        log (u-1)-splitL (u-1) := by
  have hx : 1 ≤ u-1 := by linarith
  have h1 := lowerGapPayment_le (split_arguments hx).1
  have h2 := lowerGapPayment_le (split_arguments hx).2
  have hid := split_log_identity hx
  have hu0 : u ≠ 0 := by linarith
  have hu2 : u+2 ≠ 0 := by linarith
  have hu3 : 3*u-2 ≠ 0 := by linarith
  have hq1 : u^2+16*u+4 ≠ 0 := by positivity
  have hq2p : 0 < 21*u^2-24*u+4 := by nlinarith [sq_nonneg (u-2)]
  have hp1 : lowerGapPayment ((1+(u-1))/2) =
      (u-2)^5/((u+2)^3*(u^2+16*u+4)) := by
    dsimp [lowerGapPayment,upperLog,lowerLog]
    field_simp
    ring
  have hp2 : lowerGapPayment (2*(u-1)/(1+(u-1))) =
      (u-2)^5/((3*u-2)^3*(21*u^2-24*u+4)) := by
    rw [lower_error_rational (split_arguments hx).2]
    have he : 1+(u-1)=u := by ring
    rw [he]
    have hx2 : 1 ≤ 2*(u-1)/u := by
      simpa only [he] using (split_arguments hx).2
    have hd : ((2*(u-1)/u+1)^3*((2*(u-1)/u)^2+8*(2*(u-1)/u)+1)) ≠ 0 := by positivity
    apply (div_eq_div_iff hd (mul_ne_zero (pow_ne_zero 3 hu3) hq2p.ne')).mpr
    field_simp [hu0]
    ring
  rw [hp1] at h1
  rw [hp2] at h2
  unfold splitL
  linarith only [h1,h2,hid]

/-- Endpoint monotonicity of the ratio of the two exact error denominators. -/
theorem second_factor_comparison {u : ℝ} (hu : u ∈ Icc 2 (927/200)) :
    secondFactorRatio*((u-2)^5/((u+2)^3*(u^2+16*u+4))) ≤
      (u-2)^5/((3*u-2)^3*(21*u^2-24*u+4)) := by
  have hu0 : 0 < u := by linarith [hu.1]
  have hp : 0 < u+2 := by linarith [hu.1]
  have ht : 0 < 3*u-2 := by linarith [hu.1]
  have hq : 0 < u^2+16*u+4 := by positivity
  have hr : 0 < 21*u^2-24*u+4 := by nlinarith [hu.1,sq_nonneg (u-2)]
  let r : ℝ := (3*(927/200)-2)/(927/200+2)
  let q : ℝ := (21*(927/200)^2-24*(927/200)+4)/((927/200)^2+16*(927/200)+4)
  have hlin : 3*u-2 ≤ r*(u+2) := by dsimp [r]; nlinarith [hu.2]
  have hquad : 21*u^2-24*u+4 ≤ q*(u^2+16*u+4) := by
    have hprod := mul_nonneg (sub_nonneg.mpr hu.2)
      (show 0 ≤ 360*u*(927/200)+80*(927/200+u)-160 by linarith [hu.1])
    dsimp [q]
    nlinarith only [hprod]
  have hden : (3*u-2)^3*(21*u^2-24*u+4) ≤
      (r*(u+2))^3*(q*(u^2+16*u+4)) := by gcongr
  have hscaled : secondFactorRatio*((3*u-2)^3*(21*u^2-24*u+4)) ≤
      (u+2)^3*(u^2+16*u+4) := by
    have h := mul_le_mul_of_nonneg_left hden secondFactorRatio_pos.le
    convert h using 1 <;> first | rfl | (dsimp [secondFactorRatio,r,q]; ring)
  apply (le_div_iff₀ (mul_pos (pow_pos ht _) hr)).mpr
  rw [show secondFactorRatio*((u-2)^5/((u+2)^3*(u^2+16*u+4)))*
      ((3*u-2)^3*(21*u^2-24*u+4)) =
      ((u-2)^5*(secondFactorRatio*((3*u-2)^3*(21*u^2-24*u+4)))) /
      ((u+2)^3*(u^2+16*u+4)) by ring]
  apply (div_le_iff₀ (mul_pos (pow_pos hp 3) hq)).mpr
  exact mul_le_mul_of_nonneg_left hscaled (pow_nonneg (sub_nonneg.mpr hu.1) 5)

/-- New quantitative payment in the first logarithm, using its previously unpaid factor. -/
theorem first_log_augmented {u : ℝ} (hu : u ∈ Icc 2 (927/200)) :
    (1+secondFactorRatio)*((u-2)^5/((u+2)^3*(u^2+16*u+4))) ≤
      log (u-1)-splitL (u-1) := by
  have ha := both_split_errors hu.1
  have hb := second_factor_comparison hu
  nlinarith only [ha,hb]

end F1UnpaidRecovery

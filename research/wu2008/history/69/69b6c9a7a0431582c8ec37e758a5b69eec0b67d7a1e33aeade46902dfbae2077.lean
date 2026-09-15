import E05SixthEnvelope

noncomputable section
open Real Set MeasureTheory
open Wu2008DoubleSieve
open Wu2008DoubleSieve.PositiveSixthFTC
open Wu2008DoubleSieve.DynamicSixthEnvelope
open Wu2008DoubleSieve.SharpLogRecurrence
open Wu2008DoubleSieve.SharpMassBalance
open Wu2008DoubleSieve.ClassicalLossBottleneck
open scoped Interval

namespace WuTarget.E05Sixth

theorem fifth_kernel_identity {x y : ℝ} (hx : x ∈ Icc a b)
    (hy : y ∈ Icc b (lam-x)) :
    Phase25.exactKernel x y+
        (2/5)*(lam-x-y)^5/(x*y*(1/2-x-y)^6) =
      (lowerLog (truncatedSixthLowerS 0 x y-1)+
        fifthLogTerm (truncatedSixthLowerS 0 x y-1))/(x*y*(1/2-x-y)) := by
  have hg := Phase25.mask_geometry hx hy
  have hp := truncatedSixthLower_parameters
  have hz' : 1-x*2-y*2 ≠ 0 := by linarith [hg.2.2.2.1]
  simp only [Phase25.exactKernel,lowerLog,fifthLogTerm,
    truncatedSixthLowerS,truncatedSixthLowerC,lam,sub_zero]
  field_simp [hp.1.ne',hg.1.ne',hg.2.1.ne',hg.2.2.2.1.ne',hz']
  ring

theorem corrected_kernel_le_log {x y : ℝ} (hx : x ∈ Icc a b)
    (hy : y ∈ Icc b (lam-x)) :
    Phase25.exactKernel x y+correctionKernel x y ≤ sixthLogRegular x y := by
  have hg := Phase25.mask_geometry hx hy
  have hw : 0 ≤ lam-x-y := by linarith [hy.2]
  have hu : 2 ≤ truncatedSixthLowerS 0 x y := by
    apply (le_div_iff₀ truncatedSixthLower_parameters.1).2
    change 2*truncatedSixthLowerAlpha ≤ 1/2-0-x-y
    simpa only [sub_zero] using hg.2.2.2.2
  have hdiv := div_le_div_of_nonneg_left
    (mul_nonneg (by norm_num : (0:ℝ) ≤ 2/5) (pow_nonneg hw 5))
    (mul_pos (mul_pos hg.1 hg.2.1) (pow_pos hg.2.2.2.1 6))
    (denominator_bound hx hy)
  calc
    _ ≤ Phase25.exactKernel x y+
        (2/5)*(lam-x-y)^5/(x*y*(1/2-x-y)^6) :=
      add_le_add (le_refl _) hdiv
    _ = (lowerLog (truncatedSixthLowerS 0 x y-1)+
        fifthLogTerm (truncatedSixthLowerS 0 x y-1))/(x*y*(1/2-x-y)) :=
      fifth_kernel_identity hx hy
    _ ≤ log (truncatedSixthLowerS 0 x y-1)/(x*y*(1/2-x-y)) :=
      div_le_div_of_nonneg_right (log_fifth_lower (by linarith))
        (mul_pos (mul_pos hg.1 hg.2.1) hg.2.2.2.1).le
    _ = sixthLogRegular x y := (sixth_log_retained hx hy).symm

theorem correction_inner_ftc (x : ℝ) :
    (∫ y in b..(lam-x), correctionKernel x y) = correctionInner x := by
  have hd (y : ℝ) (_hy : y ∈ uIcc b (lam-x)) :
      HasDerivAt (fun y : ℝ => -(lam-x-y)^6/(15*denominatorCap))
        (correctionKernel x y) y := by
    convert (((((hasDerivAt_const y (lam-x)).sub (hasDerivAt_id y)).pow 6).neg).div_const
      (15*denominatorCap)) using 1 <;>
      first | rfl | (dsimp [correctionKernel]; ring)
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hd
    ((by unfold correctionKernel; fun_prop :
      Continuous (correctionKernel x)).intervalIntegrable b (lam-x))]
  simp only [sub_self,zero_pow (by decide : (6:ℕ) ≠ 0),neg_zero,zero_div,zero_sub,
    correctionInner]
  ring

theorem correction_outer_ftc :
    (4*∫ x in a..b, correctionInner x) = sixthCredit := by
  have hd (x : ℝ) (_hx : x ∈ uIcc a b) :
      HasDerivAt (fun x : ℝ => -(lam-x-b)^7/(105*denominatorCap))
        (correctionInner x) x := by
    convert ((((((hasDerivAt_const x lam).sub (hasDerivAt_id x)).sub_const b).pow 7).neg).div_const
      (105*denominatorCap)) using 1 <;>
      first | rfl | (dsimp [correctionInner]; ring)
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hd
    ((by unfold correctionInner; fun_prop :
      Continuous correctionInner).intervalIntegrable a b)]
  unfold sixthCredit
  have he : lam-b-b = lam-2*b := by ring
  rw [he]
  ring

theorem corrected_inner_le_log {x : ℝ} (hx : x ∈ Icc a b) :
    Phase25.rationalInner (1/2-x)+correctionInner x ≤
      ∫ y in b..s, sixthLogRegular x y := by
  have hc : Continuous (fun y : ℝ => sixthLogRegular x y) :=
    sixth_log_continuous.comp (f := fun y : ℝ => (x,y)) (by fun_prop)
  have hiCorrection : IntervalIntegrable (correctionKernel x) volume b (lam-x) :=
    (by unfold correctionKernel; fun_prop : Continuous (correctionKernel x)).intervalIntegrable _ _
  have hi := intervalIntegral.integral_mono_on (μ := volume) (moving_geometry hx).1
    ((Phase25.inner_integrable hx).add hiCorrection) (hc.intervalIntegrable b (lam-x))
    (fun y hy => corrected_kernel_le_log hx hy)
  rw [intervalIntegral.integral_add (Phase25.inner_integrable hx) hiCorrection,
    Phase25.inner_ftc hx,correction_inner_ftc] at hi
  have hn : 0 ≤ ∫ y in (lam-x)..s, sixthLogRegular x y :=
    intervalIntegral.integral_nonneg (moving_geometry hx).2
      (fun y _ => sixth_log_nonnegative x y)
  have he := intervalIntegral.integral_add_adjacent_intervals (μ := volume)
    (hc.intervalIntegrable b (lam-x)) (hc.intervalIntegrable (lam-x) s)
  linarith only [hi,hn,he,Phase25.rationalInner_lower hx]

theorem endpoint_add_credit_le_log :
    4*(Phase25.outerPrimitive b-Phase25.outerPrimitive a)+sixthCredit ≤
      sixthLogIntegral := by
  have hc : Continuous (fun x : ℝ => ∫ y in b..s, sixthLogRegular x y) := by
    apply gamma5Gain_moving_integral (f := sixthLogRegular) sixth_log_continuous <;> fun_prop
  have hiCorrection : IntervalIntegrable correctionInner volume a b :=
    (by unfold correctionInner; fun_prop : Continuous correctionInner).intervalIntegrable _ _
  have hi := intervalIntegral.integral_mono_on (μ := volume) geometry.2.1
    (Phase25.rationalInner_integrable.add hiCorrection) (hc.intervalIntegrable a b)
    (fun x hx => corrected_inner_le_log hx)
  rw [intervalIntegral.integral_add Phase25.rationalInner_integrable hiCorrection,
    Phase25.outer_ftc] at hi
  unfold sixthLogIntegral
  linarith only [hi,correction_outer_ftc]

theorem newSixth_add_credit_le_log :
    Phase25.newSixth+sixthCredit ≤ sixthLogIntegral :=
  (add_le_add Phase25.newSixth_lower (le_refl sixthCredit)).trans endpoint_add_credit_le_log

theorem newSixth_add_credit_le_actual :
    Phase25.newSixth+sixthCredit ≤ truncatedSixthLowerF6lin := by
  linarith only [newSixth_add_credit_le_log,sixth_recurrence_integral_cap.1]

end WuTarget.E05Sixth

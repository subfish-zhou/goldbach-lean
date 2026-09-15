import MathlibNt.Wu2008DoubleSieve.SecondFunctionalSignedConsumers

namespace Wu2008DoubleSieve.SecondFunctionalRationalCost
open Set MeasureTheory

 theorem directedL_upper {c : ℝ} (hc : 2 < c) (hc3 : c < 3) :
    fourthRowClassicalL c ≤ (3-c)^2 / (2*(c-2)*(c-1)) := by
  have hab : c-1 ≤ 2 := by linarith
  have hd : 0 < (c-2)*(c-1) := mul_pos (by linarith) (by linarith)
  have hf : ContinuousOn (fun v : ℝ => -Real.log (v-1)/v) (Icc (c-1) 2) := by
    apply ContinuousOn.div
    · apply ContinuousOn.neg
      apply ContinuousOn.log (continuousOn_id.sub continuousOn_const)
      intro v hv
      exact ne_of_gt (show 0 < v-1 by linarith [hv.1])
    · exact continuousOn_id
    · intro v hv
      exact ne_of_gt (by linarith [hv.1])
  have hg : Continuous (fun v : ℝ => (2-v)/((c-2)*(c-1))) :=
    (continuous_const.sub continuous_id).div_const _
  have hpoint (v : ℝ) (hv : v ∈ Icc (c-1) 2) :
      -Real.log (v-1)/v ≤ (2-v)/((c-2)*(c-1)) := by
    have hv0 : 0 < v := by linarith [hv.1]
    have hv1 : 0 < v-1 := by linarith [hv.1]
    have hl := Real.log_le_sub_one_of_pos (inv_pos.mpr hv1)
    rw [Real.log_inv] at hl
    have hlog : -Real.log (v-1) ≤ (2-v)/(v-1) := by
      convert hl using 1; field_simp; ring
    have hden : (c-2)*(c-1) ≤ (v-1)*v := by
      nlinarith [hv.1]
    calc
      _ ≤ ((2-v)/(v-1))/v := div_le_div_of_nonneg_right hlog hv0.le
      _ = (2-v)/((v-1)*v) := by rw [div_div]
      _ ≤ _ := div_le_div_of_nonneg_left (by linarith [hv.2]) hd hden
  have hmono := intervalIntegral.integral_mono_on (μ := volume) hab
    (hf.intervalIntegrable_of_Icc hab) (hg.intervalIntegrable _ _) hpoint
  have heval : (∫ v in (c-1)..2, (2-v)/((c-2)*(c-1))) =
      (3-c)^2/(2*(c-2)*(c-1)) := by
    have hdv (v : ℝ) : HasDerivAt
        (fun v : ℝ => (2*v-v^2/2)/((c-2)*(c-1)))
        ((2-v)/((c-2)*(c-1))) v := by
      convert! (((hasDerivAt_id v).const_mul 2).sub
        (((hasDerivAt_id v).pow 2).div_const 2)).div_const ((c-2)*(c-1)) using 1; simp only [id_eq]; ring
    rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (fun v _ => hdv v)
      (hg.intervalIntegrable _ _)]
    field_simp
   ; ring
  rw [heval] at hmono
  unfold fourthRowClassicalL
  rw [intervalIntegral.integral_symm]
  convert hmono using 1
  rw [← intervalIntegral.integral_neg]
  apply intervalIntegral.integral_congr
  intro v _
  dsimp only
  ring

end Wu2008DoubleSieve.SecondFunctionalRationalCost

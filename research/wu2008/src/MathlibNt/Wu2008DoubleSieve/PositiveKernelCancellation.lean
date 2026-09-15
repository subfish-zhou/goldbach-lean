import MathlibNt.Wu2008DoubleSieve.PositiveKernelIntegral

namespace Wu2008DoubleSieve
open Set MeasureTheory Real
open scoped Interval

/-- Positive rectangular domain for the genuine mixed derivative. -/
theorem positiveKernel_mixed_pos {a v t : ℝ} (ha : 2 < a) (hv : a ≤ v) (ht : a ≤ t) :
    0 < (v-1)*t-v := by
  have h1 : 0 < v-2 := by linarith
  have h2 : 0 < t-1 := by linarith
  nlinarith [mul_pos h1 h2]

/-- Genuine inner parameter FTC, on the full positive rectangle. -/
theorem positiveKernel_inner_parameter {a b t : ℝ} (ha : 2 < a)
    (ht : t ∈ Icc a b) :
    (∫ v in t..b, 1/((v-1)*t-v)) =
      log (b-1-b/t)/(t-1)-log (t-2)/(t-1) := by
  have ht0 : 0 < t := by linarith [ht.1]
  have ht1 : t-1 ≠ 0 := by linarith [ht.1]
  have hp (v : ℝ) (hv : v ∈ uIcc t b) : 0 < (v-1)*t-v := by
    rw [uIcc_of_le ht.2] at hv
    exact positiveKernel_mixed_pos ha (ht.1.trans hv.1) ht.1
  have he (v : ℝ) : v-1-v/t = ((v-1)*t-v)/t := by
    field_simp
  have hd (v : ℝ) (hv : v ∈ uIcc t b) :
      HasDerivAt (fun v : ℝ => log (v-1-v/t)/(t-1)) (1/((v-1)*t-v)) v := by
    have harg : v-1-v/t ≠ 0 := by rw [he]; exact (div_pos (hp v hv) ht0).ne'
    convert! (((((hasDerivAt_id v).sub_const 1).sub
      ((hasDerivAt_id v).div_const t)).log harg).div_const (t-1)) using 1
    dsimp only [Pi.sub_apply, id_eq]
    rw [he]
    field_simp [ht0.ne', ht1, (hp v hv).ne',
      (show t*(v-1)-v ≠ 0 by nlinarith [hp v hv])]
  have hi : IntervalIntegrable (fun v : ℝ => 1/((v-1)*t-v)) volume t b :=
    (continuousOn_const.div
      (((continuousOn_id.sub continuousOn_const).mul continuousOn_const).sub continuousOn_id)
      (fun v hv => (hp v hv).ne')).intervalIntegrable
  have h := intervalIntegral.integral_eq_sub_of_hasDerivAt hd hi
  have htarg : t-1-t/t = t-2 := by rw [div_self ht0.ne']; ring
  rwa [htarg] at h

/-- Genuine inner spatial FTC after reversing the integration order. -/
theorem positiveKernel_inner_spatial {a b v : ℝ} (ha : 2 < a)
    (hv : v ∈ Icc a b) :
    (∫ t in a..v, 1/((v-1)*t-v)) =
      (log (v*(v-2))-log ((a-1)*v-a))/(v-1) := by
  have hv1 : v-1 ≠ 0 := by linarith [hv.1]
  have hp (t : ℝ) (ht : t ∈ uIcc a v) : 0 < (v-1)*t-v := by
    rw [uIcc_of_le hv.1] at ht
    exact positiveKernel_mixed_pos ha hv.1 ht.1
  have hd (t : ℝ) (ht : t ∈ uIcc a v) :
      HasDerivAt (fun t : ℝ => log ((v-1)*t-v)/(v-1)) (1/((v-1)*t-v)) t := by
    convert! (((((hasDerivAt_id t).const_mul (v-1)).sub_const v).log
      (hp t ht).ne').div_const (v-1)) using 1
    dsimp only [id_eq]
    field_simp [hv1]
  have hi : IntervalIntegrable (fun t : ℝ => 1/((v-1)*t-v)) volume a v :=
    (continuousOn_const.div
      ((continuousOn_const.mul continuousOn_id).sub continuousOn_const)
      (fun t ht => (hp t ht).ne')).intervalIntegrable
  have h := intervalIntegral.integral_eq_sub_of_hasDerivAt hd hi
  rw [show (v-1)*v-v = v*(v-2) by ring,
    show (v-1)*a-v = (a-1)*v-a by ring] at h
  simpa only [sub_div] using h

/-- Exact cancellation of the original J against its diagonal log integral, by true Fubini. -/
theorem positiveKernel_J_cancel {a b : ℝ} (ha : 2 < a) (hab : a ≤ b) :
    fourthRowClassicalJ a b =
      ∫ v in a..b, 2*(log (v-2)/(v-1)) + log (v/((a-1)*v-a))/(v-1) := by
  let k : ℝ → ℝ → ℝ := fun t v => 1/((v-1)*t-v)
  have hk : ContinuousOn (Function.uncurry k) (Icc a b ×ˢ Icc a b) := by
    apply continuousOn_const.div
      (((continuous_snd.continuousOn.sub continuousOn_const).mul continuous_fst.continuousOn).sub
        continuous_snd.continuousOn)
    intro p hp
    exact (positiveKernel_mixed_pos ha hp.2.1 hp.1.1).ne'
  have hf := firstFeedback_triangle (a := a) (c := b) (d := 0)
    (f := fun _ => 1) (k := k) (by simpa using hab) intervalIntegrable_const
    (by simpa using hk)
  simp only [sub_zero, add_zero, one_mul] at hf
  have hc : ContinuousOn (fun t : ℝ => log (t-2)/(t-1)) (Icc a b) := by
    exact ((continuousOn_id.sub continuousOn_const).log
      (fun t ht => ne_of_gt (by change 0 < t-2; linarith [ht.1]))).div
      (continuousOn_id.sub continuousOn_const)
      (fun t ht => by change t-1 ≠ 0; linarith [ht.1])
  have hi : IntervalIntegrable (fun t : ℝ => log (t-2)/(t-1)) volume a b :=
    hc.intervalIntegrable_of_Icc hab
  rw [positiveKernel_J_transform ha hab]
  calc
    _ = ∫ t in a..b, log (t-2)/(t-1) + ∫ v in t..b, k t v := by
      apply intervalIntegral.integral_congr
      intro t ht
      rw [uIcc_of_le hab] at ht
      dsimp only
      rw [show (∫ v in t..b, k t v) = _ from positiveKernel_inner_parameter ha ht]
      ring
    _ = (∫ t in a..b, log (t-2)/(t-1)) + ∫ v in a..b, ∫ t in a..v, k t v := by
      rw [intervalIntegral.integral_add hi hf.1, hf.2.2]
    _ = ∫ v in a..b, log (v-2)/(v-1) + ∫ t in a..v, k t v := by
      rw [intervalIntegral.integral_add hi hf.2.1]
    _ = _ := by
      apply intervalIntegral.integral_congr
      intro v hv
      rw [uIcc_of_le hab] at hv
      dsimp only
      rw [show (∫ t in a..v, k t v) = _ from positiveKernel_inner_spatial ha hv]
      have hv0 : v ≠ 0 := by linarith [hv.1]
      have hv2 : v-2 ≠ 0 := by linarith [hv.1]
      have hd : (a-1)*v-a ≠ 0 := by
        have := positiveKernel_mixed_pos ha hv.1 (le_refl a)
        nlinarith
      rw [log_mul hv0 hv2, log_div hv0 hd]
      ring

end Wu2008DoubleSieve

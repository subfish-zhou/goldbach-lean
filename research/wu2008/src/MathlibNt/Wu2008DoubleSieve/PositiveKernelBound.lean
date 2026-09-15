import MathlibNt.Wu2008DoubleSieve.PositiveKernelCancellation

namespace Wu2008DoubleSieve
open Set MeasureTheory Real
open scoped Interval

/-- Internal regularity of the two cancelled densities on any admissible J interval. -/
theorem positiveKernel_cancel_continuous {a b : ℝ} (ha : 2 < a) :
    ContinuousOn (fun v : ℝ => log (v-2)/(v-1)) (Icc a b) ∧
    ContinuousOn (fun v : ℝ => log (v/((a-1)*v-a))/(v-1)) (Icc a b) := by
  have hd (v : ℝ) (hv : v ∈ Icc a b) : 0 < (a-1)*v-a :=
    positiveKernel_mixed_pos ha (le_refl a) hv.1
  constructor
  · exact ((continuousOn_id.sub continuousOn_const).log
      (fun v hv => ne_of_gt (by change 0 < v-2; linarith [hv.1]))).div
      (continuousOn_id.sub continuousOn_const)
      (fun v hv => by change v-1 ≠ 0; linarith [hv.1])
  · apply ContinuousOn.div
      ((continuousOn_id.div
        ((continuousOn_const.mul continuousOn_id).sub continuousOn_const)
        (fun v hv => (hd v hv).ne')).log
        (fun v hv => (div_pos (by change 0 < v; linarith [hv.1]) (hd v hv)).ne'))
      (continuousOn_id.sub continuousOn_const)
      (fun v hv => by change v-1 ≠ 0; linarith [hv.1])

/-- The original directed L is shifted, not replaced by a positive-part convention. -/
theorem positiveKernel_L_shift (b : ℝ) :
    fourthRowClassicalL b = ∫ v in (3 : ℝ)..b, log (v-2)/(v-1) := by
  have h := intervalIntegral.integral_comp_sub_right
    (fun v : ℝ => log (v-1)/v) 1 (a := 3) (b := b)
  norm_num only [show (3 : ℝ)-1 = 2 by norm_num] at h
  change _ = fourthRowClassicalL b at h
  rw [← h]
  apply intervalIntegral.integral_congr
  intro v _
  dsimp
  rw [show v-1-1 = v-2 by ring]

/-- Actual signed positive-kernel decomposition, obtained from two FTC steps and Fubini. -/
theorem positiveKernel_original_decomposition {a b : ℝ} (ha : 2 < a) (ha3 : a < 3)
    (hb : 3 ≤ b) :
    fourthRowClassicalJ a b - 2*fourthRowClassicalL b =
      fourthRowClassicalJ a 3 - 2*fourthRowClassicalL 3 +
        ∫ v in (3 : ℝ)..b, log (v/((a-1)*v-a))/(v-1) := by
  let l : ℝ → ℝ := fun v => log (v-2)/(v-1)
  let q : ℝ → ℝ := fun v => log (v/((a-1)*v-a))/(v-1)
  have hab : a ≤ b := ha3.le.trans hb
  have hc := positiveKernel_cancel_continuous (b := b) ha
  have hi : IntervalIntegrable (fun v => 2*l v + q v) volume a b :=
    ((continuousOn_const.mul hc.1).add hc.2).intervalIntegrable_of_Icc hab
  have hsub : uIcc a 3 ⊆ uIcc a b := by
    rw [uIcc_of_le ha3.le, uIcc_of_le hab]
    intro v hv
    exact ⟨hv.1, hv.2.trans hb⟩
  have hsub' : uIcc 3 b ⊆ uIcc a b := by
    rw [uIcc_of_le hb, uIcc_of_le hab]
    intro v hv
    exact ⟨ha3.le.trans hv.1, hv.2⟩
  have hl : IntervalIntegrable l volume 3 b :=
    (hc.1.intervalIntegrable_of_Icc hab).mono_set hsub'
  have hq : IntervalIntegrable q volume 3 b :=
    (hc.2.intervalIntegrable_of_Icc hab).mono_set hsub'
  have he := intervalIntegral.integral_interval_sub_left hi (hi.mono_set hsub)
  change (∫ v in a..b, 2*l v + q v) - (∫ v in a..3, 2*l v + q v) = _ at he
  rw [intervalIntegral.integral_add (hl.const_mul 2) hq,
    intervalIntegral.integral_const_mul] at he
  rw [positiveKernel_J_cancel ha hab, positiveKernel_J_cancel ha ha3.le,
    positiveKernel_L_shift b, positiveKernel_L_shift 3]
  change (∫ v in a..b, 2*l v + q v) - 2*(∫ v in 3..b, l v) =
    (∫ v in a..3, 2*l v + q v) - 2*(∫ v in 3..3, l v) + ∫ v in 3..b, q v
  rw [intervalIntegral.integral_same]
  linarith

/-- Strict rational lower bound for the literal original functional on the entire closed b-range. -/
theorem positiveKernel_original_strict_lower {a b : ℝ} (ha : 2 < a) (ha3 : a < 3)
    (hb : 3 ≤ b) (hcap : b ≤ a/(a-2)) :
    -(3-a)^2*(1/36+1/(3*(2*a-3)*(a-1))) +
      (2/a)*(1-2/(b-1)-(a-2)*((((b-1)/2)^2-1)/(2*((b-1)/2)))) <
      fourthRowClassicalJ a b - 2*fourthRowClassicalL b := by
  rw [positiveKernel_original_decomposition ha ha3 hb]
  exact add_lt_add_of_lt_of_le (positiveKernel_original_anchor_lower ha ha3)
    (positiveKernel_integral_lower ha hb hcap)

end Wu2008DoubleSieve

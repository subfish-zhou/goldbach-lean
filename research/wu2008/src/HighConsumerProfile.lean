import HighConsumerBox

namespace HighConsumer
open Real Set MeasureTheory QuarterTrim Wu08G6High Wu2008DoubleSieve
open scoped Classical
noncomputable section

/-- Elementary fixed-delta logarithmic loss; delta is not swallowed by N. -/
theorem logarithm_shift_loss {s u : ℝ} (hs : 2 ≤ s) (hsu : s ≤ u) :
    log (u-1) - log (s-1) ≤ u-s := by
  have hs0 : 0 < s-1 := by linarith
  have hu0 : 0 < u-1 := by linarith
  have hl := log_le_sub_one_of_pos (div_pos hu0 hs0)
  rw [log_div hu0.ne' hs0.ne'] at hl
  have hd : (u-1)/(s-1)-1 ≤ u-s := by
    apply (sub_le_iff_le_add).mpr
    apply (div_le_iff₀ hs0).mpr
    nlinarith only [mul_nonneg (show 0 ≤ u-s by linarith) (show 0 ≤ s-2 by linarith)]
  exact hl.trans hd

/-- The explicit new profile is antitone where it is used, not H or h in delta. -/
theorem correction_antitone {s u : ℝ} (hs : 1 < s) (hsu : s ≤ u) :
    PositiveH.lowerCorrection u ≤ PositiveH.lowerCorrection s := by
  apply mul_le_mul_of_nonneg_left _ (by norm_num : (0 : ℝ) ≤ 1/20000)
  apply log_le_log (div_pos (by norm_num) (by linarith))
  exact div_le_div_of_nonneg_left (by norm_num) (by linarith) (by linarith)

/-- Pointwise paid comparison to the original u, retaining the exact delta debit. -/
theorem original_profile_delta_debit {δ x y : ℝ} (hδ : 0 ≤ δ)
    (hr : truncatedSixthLowerRegion δ x y) :
    log (u x y-1)+PositiveH.lowerCorrection (u x y)-δ/alpha ≤
      log (truncatedSixthLowerS δ x y-1)+
        PositiveH.lowerCorrection (truncatedSixthLowerS δ x y) := by
  have hs := (truncatedSixthLower_region_bounds hδ hr).2.2.2.1
  have he := source_parameter_exact δ x y
  have hd : 0 ≤ δ/alpha := div_nonneg hδ alpha_pos.le
  have hsu : truncatedSixthLowerS δ x y ≤ u x y := by linarith only [he,hd]
  have hl := logarithm_shift_loss hs hsu
  have hh := correction_antitone (by linarith : 1 < truncatedSixthLowerS δ x y) hsu
  linarith only [he,hl,hh]

/-- The entire original high triangle lies inside the newly proved source interval at delta zero. -/
theorem original_high_parameters {x y : ℝ} (h : (x,y) ∈ highDomain) :
    2 ≤ u x y ∧ u x y ≤ 29/10 := by
  have hr : truncatedSixthLowerRegion 0 x y := by
    obtain ⟨⟨ha,hb,hc,hd⟩,hy⟩ := h
    refine ⟨ha,hb,hc,?_,?_⟩
    · change y ≤ 1/2-3*alpha
      linarith
    · change x+y ≤ 1/2-0-2*alpha
      linarith
  simpa only [source_parameter_exact,zero_div,sub_zero] using high_source_bounds (δ := 0) le_rfl hr h.2

/-- Literal original integral; factor four is not absorbed into the mother yet. -/
def highGainKernel (v : ℝ × ℝ) : ℝ :=
  highDomain.indicator (fun v => PositiveH.lowerCorrection (u v.1 v.2) /
    (v.1*v.2*(1/2-v.1-v.2))) v

def highGain : ℝ := 4 * ∫ v : ℝ × ℝ, highGainKernel v

private theorem correction_continuousOn : ContinuousOn
    (fun v : ℝ × ℝ => PositiveH.lowerCorrection (u v.1 v.2)/
      (v.1*v.2*(1/2-v.1-v.2)))
    (Icc alpha (1/4-2*alpha) ×ˢ Icc (1/4) (1/2-3*alpha)) := by
  apply ContinuousOn.div
  · apply ContinuousOn.const_mul
    apply ContinuousOn.log
    · apply ContinuousOn.div continuousOn_const
      · exact ((continuous_const.sub continuous_fst).sub continuous_snd).div_const alpha |>.sub continuous_const |>.continuousOn
      · intro v hv
        apply ne_of_gt
        dsimp [u]
        apply sub_pos.mpr
        apply (lt_div_iff₀ alpha_pos).mpr
        have hx := hv.1.2
        have hy := hv.2.2
        norm_num [alpha] at hx hy ⊢
        linarith
    · intro v hv
      have hu : 0 < u v.1 v.2-1 := by
        dsimp [u]
        apply sub_pos.mpr
        apply (lt_div_iff₀ alpha_pos).mpr
        have hx := hv.1.2
        have hy := hv.2.2
        norm_num [alpha] at hx hy ⊢
        linarith
      exact (div_pos (by norm_num) hu).ne'
  · exact ((continuous_fst.mul continuous_snd).mul ((continuous_const.sub continuous_fst).sub continuous_snd)).continuousOn
  · intro v hv
    have hx := alpha_pos.trans_le hv.1.1
    have hy : 0 < v.2 := lt_of_lt_of_le (by norm_num) hv.2.1
    have hz : 0 < 1/2-v.1-v.2 := by
      have hxx := hv.1.2
      have hyy := hv.2.2
      norm_num [alpha] at hxx hyy ⊢
      linarith
    exact (mul_pos (mul_pos hx hy) hz).ne'

 theorem highGain_integrable : Integrable highGainKernel := by
  have hsub : highDomain ⊆ Icc alpha (1/4-2*alpha) ×ˢ Icc (1/4) (1/2-3*alpha) := by
    intro v hv
    obtain ⟨hx,hy⟩ := (high_iff v.1 v.2).mp hv
    exact ⟨hx,hy.1.le,by linarith [hy.2,hx.1]⟩
  apply (integrable_indicator_iff high_measurable).mpr
  exact (correction_continuousOn.integrableOn_compact (isCompact_Icc.prod isCompact_Icc)).mono_set hsub

 theorem highGainKernel_nonneg (v : ℝ × ℝ) : 0 ≤ highGainKernel v := by
  by_cases hv : v ∈ highDomain
  · rw [highGainKernel,indicator_of_mem hv]
    have hs := original_high_parameters hv
    exact div_nonneg (PositiveH.lowerCorrection_pos (by linarith [hs.1]) (by linarith [hs.2])).le
      (published_denominator hv.1).1.le
  · simp [highGainKernel,hv]

 theorem highGain_pos : 0 < highGain := by
  apply mul_pos (by norm_num)
  apply (integral_pos_iff_support_of_nonneg highGainKernel_nonneg highGain_integrable).mpr
  let U : Set (ℝ × ℝ) := {v | alpha < v.1 ∧ 1/4 < v.2 ∧ v.1+v.2 < 1/2-2*alpha}
  have hUopen : IsOpen U :=
    (isOpen_lt continuous_const continuous_fst).inter
      ((isOpen_lt continuous_const continuous_snd).inter
        (isOpen_lt (continuous_fst.add continuous_snd) continuous_const))
  have hUnonempty : U.Nonempty := by
    refine ⟨(alpha+(1/4-3*alpha)/3,1/4+(1/4-3*alpha)/3),?_⟩
    dsimp [U]
    norm_num [alpha]
  have hsub : U ⊆ Function.support highGainKernel := by
    intro v hv
    have hv' : v ∈ highDomain := by
      apply (high_iff v.1 v.2).mpr
      exact ⟨⟨hv.1.le,by linarith [hv.2.1,hv.2.2]⟩,hv.2.1,by linarith [hv.2.2]⟩
    have hs := original_high_parameters hv'
    rw [Function.mem_support,highGainKernel,indicator_of_mem hv']
    exact (div_pos (PositiveH.lowerCorrection_pos (by linarith [hs.1]) (by linarith [hs.2]))
      (published_denominator hv'.1).1).ne'
  exact (hUopen.measure_pos volume hUnonempty).trans_le (measure_mono hsub)

end
end HighConsumer

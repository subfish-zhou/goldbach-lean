import WE07FifthSourceRoot
import PositiveCoreFifth

namespace WuSource.SrcFifthGain
open Wu2008DoubleSieve WuTarget.Wu08FifthSource SharpMassBalance
open MeasureTheory Set Real
open scoped Interval
noncomputable section

def profileKernel (p : ℝ → ℝ) (v : ℝ × ℝ) : ℝ :=
  fifthPairRegion.indicator
    (fun v => p ((1/2-v.1-v.2)/a)/(v.1*v.2*(1/2-v.1-v.2))) v

def triangleGain (p : ℝ → ℝ) : ℝ := 4*∫ v, profileKernel p v

theorem triangle_parameter {v : ℝ × ℝ} (hv : v ∈ fifthPairRegion) :
    ((1/2-v.1-v.2)/a) ∈ Icc s0 FifthClassicalShape.q := by
  have ha := truncatedSixthLower_parameters.1
  change a ≤ v.1 ∧ v.1 ≤ v.2 ∧ v.2 ≤ b at hv
  constructor
  · unfold s0
    exact div_le_div_of_nonneg_right (by linarith [hv.1, hv.2.1, hv.2.2]) ha.le
  · unfold FifthClassicalShape.q
    exact div_le_div_of_nonneg_right (by linarith [hv.1, hv.2.1]) ha.le

theorem parameter_in_core {s : ℝ} (hs : s ∈ Icc s0 FifthClassicalShape.q) :
    s ∈ Icc (2 : ℝ) 10 := by
  have hp := FifthClassicalShape.parameters
  exact ⟨by linarith [hp.1, hs.1], by linarith [hp.2.2, hs.2]⟩

theorem zero_denominator_pos {v : ℝ × ℝ} (hv : v ∈ fifthPairRegion) :
    0 < v.1*v.2*((1/2 : ℝ)-v.1-v.2) := by
  have hb := fifthPair_region_bounds (δ := 0) le_rfl (by norm_num) hv
  have hz : 0 < (1/2 : ℝ)-v.1-v.2 := by
    have h := hb.2.2.1
    norm_num [truncatedSixthLowerC] at h
    linarith [truncatedSixthLower_parameters.1]
  exact mul_pos (mul_pos hb.1 hb.2.1) hz

theorem profile_kernel_measurable {p : ℝ → ℝ} (hp : Measurable p) :
    Measurable (profileKernel p) := by
  apply Measurable.indicator _ fifthPair_region_compact.measurableSet
  exact (hp.comp (by fun_prop)).div (by fun_prop)

theorem profile_kernel_integrable {p : ℝ → ℝ} {M : ℝ}
    (hp : Measurable p)
    (hb : ∀ s ∈ Icc s0 FifthClassicalShape.q, |p s| ≤ M) :
    Integrable (profileKernel p) := by
  have hi : Integrable (profileKernel (fun _ => M)) := by
    apply (ContinuousOn.integrableOn_compact fifthPair_region_compact
      (continuousOn_const.div (by fun_prop)
        (fun v hv => (zero_denominator_pos hv).ne'))).integrable_indicator
      fifthPair_region_compact.measurableSet
  apply hi.mono' (profile_kernel_measurable hp).aestronglyMeasurable
  filter_upwards [] with v
  by_cases hv : v ∈ fifthPairRegion
  · simp only [profileKernel, indicator_of_mem hv, Real.norm_eq_abs, abs_div,
      abs_of_pos (zero_denominator_pos hv)]
    exact div_le_div_of_nonneg_right (hb _ (triangle_parameter hv))
      (zero_denominator_pos hv).le
  · simp [profileKernel, hv]

theorem profile_kernel_le_actual {p : ℝ → ℝ} {δ : ℝ}
    (hδ : 0 < δ) (hd : δ ≤ 1/1000)
    (hn : ∀ s ∈ Icc s0 FifthClassicalShape.q, 0 ≤ p s)
    (hc : ∀ s ∈ Icc s0 FifthClassicalShape.q, p s ≤ wuImprovementLimit false δ s)
    (v : ℝ × ℝ) :
    profileKernel p v ≤ fifthHOnlyKernel δ v := by
  by_cases hv : v ∈ fifthPairRegion
  · rw [profileKernel, indicator_of_mem hv, fifthHOnlyKernel, if_pos hv]
    have hb := fifthPair_region_bounds hδ.le hd hv
    have h0 := fifthPair_region_bounds (δ := 0) le_rfl (by norm_num) hv
    have hs := triangle_parameter hv
    have hmove : truncatedSixthLowerS δ v.1 v.2 ≤ (1/2-v.1-v.2)/a := by
      unfold truncatedSixthLowerS truncatedSixthLowerC
      apply div_le_div_of_nonneg_right _ truncatedSixthLower_parameters.1.le
      linarith
    have hh := (hc _ hs).trans (wuImprovementLimit_lower_antitone hδ (by linarith)
      ⟨hb.2.2.2.1, hb.2.2.2.2.trans (by norm_num)⟩ (parameter_in_core hs) hmove)
    have hden : v.1*v.2*(truncatedSixthLowerC δ-v.1-v.2) ≤
        v.1*v.2*(1/2-v.1-v.2) := by
      apply mul_le_mul_of_nonneg_left _ (mul_nonneg h0.1.le h0.2.1.le)
      unfold truncatedSixthLowerC
      linarith
    have hdpos := (fifthH_denominator_bounds hδ hd hv).1
    exact (div_le_div_of_nonneg_left (hn _ hs) hdpos hden).trans
      (div_le_div_of_nonneg_right hh hdpos.le)
  · simp [profileKernel, fifthHOnlyKernel, hv]

theorem triangle_gain_uniform {p : ℝ → ℝ} {δ : ℝ}
    (hi : Integrable (profileKernel p)) (hδ : 0 < δ) (hd : δ ≤ 1/1000)
    (hn : ∀ s ∈ Icc s0 FifthClassicalShape.q, 0 ≤ p s)
    (hc : ∀ s ∈ Icc s0 FifthClassicalShape.q, p s ≤ wuImprovementLimit false δ s) :
    triangleGain p ≤ fifthHOnlyIntegral δ := by
  have h := integral_mono hi (fifthH_only_integrable hδ hd)
    (profile_kernel_le_actual hδ hd hn hc)
  unfold triangleGain fifthHOnlyIntegral
  linarith only [h]

theorem profile_count {p : ℝ → ℝ}
    (hi : Integrable (profileKernel p))
    (hn : ∀ s ∈ Icc s0 FifthClassicalShape.q, 0 ≤ p s)
    (hc : ∀ δ : ℝ, 0 < δ → δ ≤ 1/1000 →
      ∀ s ∈ Icc s0 FifthClassicalShape.q, p s ≤ wuImprovementLimit false δ s)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ T : ℕ, 4 ≤ T ∧ ∀ N : ℕ, T ≤ N → Even N →
      (fifthPairFlin+triangleGain p-ε)*wuSingularSeries N*N/log N^(2 : ℕ) ≤
        (fifthPairCount N : ℝ) := by
  obtain ⟨δ, hδ, hd, hclose⟩ := fifthPair_Fdelta_close (half_pos hε)
  obtain ⟨T, hT, hcount⟩ := fifthH_actual_Fdelta_lower hδ hd (half_pos hε)
  have hg := triangle_gain_uniform hi hδ hd hn (hc δ hδ hd)
  have hs := fifthH_actual_integral_split hδ hd
  have hcoef : fifthPairFlin+triangleGain p-ε ≤ fifthHFdelta δ-ε/2 := by
    linarith [(abs_lt.mp hclose).1]
  refine ⟨T, hT, fun N hN he => ?_⟩
  have h := (mul_le_mul_of_nonneg_right hcoef
    (truncatedSixthClosure_scale_nonneg (hT.trans hN))).trans (hcount N hN he)
  simpa only [truncatedSixthMassScale, mul_div_assoc, mul_assoc] using h

theorem replacement_coefficient (g : ℝ) :
    fifthPairFlin+PositiveCoreResume.fifthGain+
      (g-PositiveCoreResume.fifthGain) = fifthPairFlin+g := by ring

end
end WuSource.SrcFifthGain

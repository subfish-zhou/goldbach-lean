import FifthLogTotalMagnitude
import PositiveCoreFifth

noncomputable section
open Real Set MeasureTheory Wu2008DoubleSieve
open SharpMassBalance

namespace WuTarget.W14

def fifthSeed : ℝ := (11/2-FifthClassicalShape.q)^3/70875

def fifthDenominator : ℝ := b^2*(1/2-2*b)

def fifthGainLower : ℝ := 2*(b-a)^2*fifthSeed/fifthDenominator

theorem fifth_seed_nonneg : 0 ≤ fifthSeed := by
  norm_num [fifthSeed, FifthClassicalShape.q, a, truncatedSixthLowerAlpha]

theorem fifth_denominator_pos : 0 < fifthDenominator := by
  norm_num [fifthDenominator, b, truncatedSixthLowerBeta]

theorem fifth_profile_lower {v : ℝ × ℝ} (hv : v ∈ fifthPairRegion) :
    fifthSeed ≤ PositiveCoreResume.fifthProfile v := by
  have hq := (FifthActualIntegralRecovery.parameter_range hv.1 hv.2.1 hv.2.2).2
  have hm : max 4 (truncatedSixthLowerS 0 v.1 v.2) ≤ FifthClassicalShape.q :=
    max_le (by norm_num [FifthClassicalShape.q, a, truncatedSixthLowerAlpha]) hq
  have hp := pow_le_pow_left₀
    (by norm_num [FifthClassicalShape.q, a, truncatedSixthLowerAlpha] :
      (0 : ℝ) ≤ 11/2-FifthClassicalShape.q)
    (show 11/2-FifthClassicalShape.q ≤
      11/2-max 4 (truncatedSixthLowerS 0 v.1 v.2) by linarith only [hm]) 3
  exact div_le_div_of_nonneg_right hp (by norm_num)

theorem fifth_denominator_upper {v : ℝ × ℝ} (hv : v ∈ fifthPairRegion) :
    v.1*v.2*(truncatedSixthLowerC 0-v.1-v.2) ≤ fifthDenominator := by
  have hb := fifthPair_region_bounds (δ := 0) le_rfl (by norm_num) hv
  have h := ClassicalPositiveBounds.denominator_box hb.1.le hb.2.1.le
    (hv.2.1.trans hv.2.2) hv.2.2
    (show b+2*b ≤ 1/2 by norm_num [b, truncatedSixthLowerBeta]) le_rfl
  unfold fifthDenominator
  dsimp only [truncatedSixthLowerC, sub_zero]
  calc
    _ ≤ b*b*(1/2-b-b) := h
    _ = _ := by ring

theorem fifth_gain_lower : fifthGainLower ≤ PositiveCoreResume.fifthGain := by
  have hi : Integrable (fifthPairRegion.indicator
      (fun _ : ℝ × ℝ => fifthSeed/fifthDenominator)) :=
    (integrableOn_const fifthPair_region_compact.measure_lt_top.ne).integrable_indicator
      fifthPair_region_compact.measurableSet
  have hm := integral_mono hi PositiveCoreResume.minorant_integrable (fun v => by
    by_cases hv : v ∈ fifthPairRegion
    · rw [indicator_of_mem hv, PositiveCoreResume.fifthMinorant, indicator_of_mem hv]
      have hb := fifthPair_region_bounds (δ := 0) le_rfl (by norm_num) hv
      have hd : 0 < v.1*v.2*(truncatedSixthLowerC 0-v.1-v.2) :=
        mul_pos (mul_pos hb.1 hb.2.1)
          (by linarith [hb.2.2.1, truncatedSixthLower_parameters.1])
      exact (div_le_div_of_nonneg_left fifth_seed_nonneg hd
        (fifth_denominator_upper hv)).trans
        (div_le_div_of_nonneg_right (fifth_profile_lower hv) hd.le)
    · simp [PositiveCoreResume.fifthMinorant, hv])
  rw [fifthH_triangle_constant] at hm
  unfold fifthGainLower PositiveCoreResume.fifthGain
  dsimp only [a, b]
  convert (mul_le_mul_of_nonneg_left hm (by norm_num : (0 : ℝ) ≤ 4)) using 1 <;> ring

theorem fifth_gain_lower_exact :
    fifthGainLower = 134930927046659/13229419344750000000 := by
  norm_num [fifthGainLower, fifthSeed, fifthDenominator, FifthClassicalShape.q,
    a, b, truncatedSixthLowerAlpha, truncatedSixthLowerBeta]

end WuTarget.W14

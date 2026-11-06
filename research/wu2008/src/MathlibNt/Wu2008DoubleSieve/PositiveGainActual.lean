import MathlibNt.Wu2008DoubleSieve.PositiveGainSeed
import MathlibNt.Wu2008DoubleSieve.FirstFunctionalGainSource
import MathlibNt.Wu2008DoubleSieve.ImprovementCrossLower

/-!
# Positive seeds for the actual fixed-delta improvement functions

The scalar analytic seed is consumed by the parent-accepted first functional
inequality. All functions below are the existing ordered threshold/depth limits.
This is not the final eleven-term count or the 0.899 estimate.
-/

namespace Wu2008DoubleSieve
open Real Set MeasureTheory
open scoped Interval

theorem positiveGain_actual_upper_seed {δ : ℝ} (hδ : 0 < δ) (hδhi : δ ≤ 1/10) :
    (1/5000 : ℝ) ≤ wuImprovementLimit true δ (29/10) := by
  have hpsi : (1/5000 : ℝ) ≤ firstFunctionalGainPsi δ (29/10) (31/10) := by
    rw [firstFunctionalGainPsi_eq_log δ (by norm_num) (by norm_num)
      (by norm_num) (by norm_num)]
    convert positiveGain_explicit_seed hδhi using 1
    norm_num
  have hf := wuImprovementLimit_firstFunctionalGain hδ hδhi
    (by norm_num : (2 : ℝ) ≤ 29/10) (by norm_num : (29/10 : ℝ) ≤ 3)
    (by norm_num : (3 : ℝ) ≤ 31/10) (by norm_num : (31/10 : ℝ) ≤ 5) (by norm_num)
  have hn := wuImprovementLimit_nonneg true hδ (by linarith : δ < 1/2)
    (by norm_num : (1 : ℝ) ≤ 31/10) (by norm_num : (31/10 : ℝ) ≤ 10)
  have hi := firstFunctionalGain_integral_nonneg hδ (by linarith : δ < 1/2)
    (by norm_num : (2 : ℝ) ≤ 29/10) (by norm_num : (29/10 : ℝ) ≤ 31/10)
    (by norm_num : (3 : ℝ) ≤ 31/10) (by norm_num : (31/10 : ℝ) ≤ 5)
  linarith

/-- A uniform positive lower bound on the actual upper gain, not a scalar model. -/
theorem positiveGain_actual_upper_range {δ s : ℝ} (hδ : 0 < δ) (hδhi : δ ≤ 1/10)
    (hs : 1 ≤ s) (hst : s ≤ 29/10) :
    (1/5000 : ℝ) ≤ wuImprovementLimit true δ s := by
  exact (positiveGain_actual_upper_seed hδ hδhi).trans
    (wuImprovementLimit_upper_antitone hδ hδhi
      ⟨hs, by linarith⟩ ⟨by norm_num, by norm_num⟩ hst)


end Wu2008DoubleSieve

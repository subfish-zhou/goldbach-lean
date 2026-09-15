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

/-- The accepted cross inequality transports the upper seed to the actual lower gain. -/
theorem positiveGain_actual_lower_range {δ s : ℝ} (hδ : 0 < δ) (hδhi : δ ≤ 1/10)
    (hs : 2 ≤ s) (hst : s ≤ 39/10) :
    (39/10-s)/14500 ≤ wuImprovementLimit false δ s := by
  have hhalf : δ < 1/2 := by linarith
  have hc := (wu08_38 hδ hδhi hs hst (by norm_num : (39/10 : ℝ) ≤ 10)).1
  have hn := wuImprovementLimit_nonneg false hδ hhalf
    (by norm_num : (1 : ℝ) ≤ 39/10) (by norm_num : (39/10 : ℝ) ≤ 10)
  have hab : s-1 ≤ (29/10 : ℝ) := by linarith
  have hm : (∫ u in (s-1)..(29/10), (1/14500 : ℝ)) ≤
      ∫ u in (s-1)..(29/10), wuImprovementLimit true δ u/u := by
    apply intervalIntegral.integral_mono_on hab intervalIntegrable_const
      (wuImprovementLimit_div_intervalIntegrable true hδ hhalf
        (by linarith) hab (by norm_num))
    intro u hu
    have hu0 : 0 < u := by linarith [hu.1]
    apply (le_div_iff₀ hu0).mpr
    calc
      (1/14500 : ℝ)*u ≤ (1/14500 : ℝ)*(29/10) :=
        mul_le_mul_of_nonneg_left hu.2 (by norm_num)
      _ = 1/5000 := by norm_num
      _ ≤ _ := positiveGain_actual_upper_range hδ hδhi (by linarith [hu.1]) hu.2
  norm_num at hc
  have he : (∫ u in (s-1)..(29/10), (1/14500 : ℝ)) = (39/10-s)/14500 := by
    simp
    ring
  rw [he] at hm
  linarith

end Wu2008DoubleSieve

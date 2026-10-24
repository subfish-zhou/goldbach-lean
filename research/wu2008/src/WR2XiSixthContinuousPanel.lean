import WR2XiSixthRationalH
import WR2XiSixthContinuousDensity

noncomputable section
namespace WuPaper.R2Xi.SixthContinuous
open Real Set MeasureTheory WuTarget.W01Continuous WuSource.SrcSixthGain
open scoped Classical Interval

/-- A density bound on a whole panel combines with the right endpoint profile bound. -/
theorem panel_integrand_lower {a b d s : ℝ} (ha : 2 ≤ a) (hb : b ≤ 41/10)
    (hd : 0 ≤ d) (hs : s ∈ Icc a b) (hds : d ≤ density s) :
    d*pointLower b ≤ density s*hContinuous RationalCandidate.lowerH s := by
  have hp := (pointLower_le (by linarith [hs.1,hs.2]) hb).trans
    (hContinuous_antitone RationalCandidate.lowerH_nonneg hs.2)
  exact mul_le_mul hds hp (pointLower_nonneg b) (hd.trans hds)

/-- Integration uses the panel inequality everywhere, rather than sampled values. -/
theorem panel_integral_lower {a b d : ℝ} (ha : 2 ≤ a) (hab : a ≤ b)
    (hb : b ≤ endpoint) (hd : 0 ≤ d) (hds : ∀ s ∈ Icc a b, d ≤ density s) :
    (b-a)*(d*pointLower b) ≤
      ∫ s in a..b, density s*hContinuous RationalCandidate.lowerH s := by
  have hb4 : b ≤ 41/10 := by
    have he : endpoint ≤ (41:ℝ)/10 := by norm_num [endpoint, QuarterTrim.alpha, QuarterTrim.beta]
    exact hb.trans he
  have hi := (gain_integrand_integrable RationalCandidate.lowerH).mono_set
    (show uIcc a b ⊆ uIcc 2 endpoint by
      rw [uIcc_of_le hab,uIcc_of_le scalar_interval]
      exact Icc_subset_Icc ha hb)
  have h := intervalIntegral.integral_mono_on hab intervalIntegrable_const hi
    (fun s hs => panel_integrand_lower ha hb4 hd hs (hds s hs))
  simpa only [intervalIntegral.integral_const,smul_eq_mul] using h

end WuPaper.R2Xi.SixthContinuous
#print axioms WuPaper.R2Xi.SixthContinuous.panel_integral_lower

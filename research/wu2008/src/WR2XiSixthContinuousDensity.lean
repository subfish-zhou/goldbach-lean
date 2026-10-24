import WR2XiSixthContinuousReduction
import WSrcSixthGainWeights

noncomputable section
namespace WuPaper.R2Xi.SixthContinuous
open Real Set MeasureTheory QuarterTrim NodeExtension Wu2008DoubleSieve
open WuTarget.W01Continuous WuSource.SrcSixthGain
open scoped Classical Interval

theorem density_nonneg {s : ℝ} (hs : s ∈ Icc 2 endpoint) : 0 ≤ density s := by
  have hg := slice_bounds (scalar_bounds hs)
  let z := 1/2-alpha*s
  change 0 < lowerX z ∧ lowerX z ≤ upperX z ∧ 0 < z-upperX z ∧
    0 < z ∧ 0 < 1/2-z at hg
  have hden : 0 < lowerX z*(z-upperX z) := mul_pos hg.1 hg.2.2.1
  have hratio : 1 ≤ upperX z*(z-lowerX z)/(lowerX z*(z-upperX z)) := by
    apply (one_le_div hden).mpr
    nlinarith [mul_nonneg hg.2.2.2.1.le (sub_nonneg.mpr hg.2.1)]
  unfold density
  change 0 ≤ log _ / _
  exact div_nonneg (log_nonneg hratio)
    (mul_nonneg (by linarith [hs.1]) (by dsimp [z] at hg; linarith [hg.2.2.2.1]))

theorem density_continuous : ContinuousOn density (Icc 2 endpoint) := by
  have hU : Continuous (fun s : ℝ => upperX (1/2-alpha*s)) := by unfold upperX; fun_prop
  have hL : Continuous (fun s : ℝ => lowerX (1/2-alpha*s)) := by unfold lowerX; fun_prop
  apply ContinuousOn.div
  · apply ContinuousOn.log
    · exact (hU.continuousOn.mul ((by fun_prop : ContinuousOn (fun s : ℝ => 1/2-alpha*s) _).sub hL.continuousOn)).div
        (hL.continuousOn.mul ((by fun_prop : ContinuousOn (fun s : ℝ => 1/2-alpha*s) _).sub hU.continuousOn))
        (fun s hs => (mul_pos (slice_bounds (scalar_bounds hs)).1 (slice_bounds (scalar_bounds hs)).2.2.1).ne')
    · intro s hs
      have hg := slice_bounds (scalar_bounds hs)
      exact (div_pos (mul_pos (hg.1.trans_le hg.2.1) (by linarith [hg.2.1,hg.2.2.1]))
        (mul_pos hg.1 hg.2.2.1)).ne'
  · fun_prop
  · intro s hs
    have hg := slice_bounds (scalar_bounds hs)
    exact (mul_pos (by linarith [hs.1]) (by linarith [hg.2.2.2.1])).ne'

theorem density_integrable : IntervalIntegrable density volume 2 endpoint := by
  apply ContinuousOn.intervalIntegrable
  simpa only [uIcc_of_le scalar_interval] using density_continuous

theorem gain_integrand_integrable (x : Fin 9 → ℝ) :
    IntervalIntegrable (fun s => density s*hContinuous x s) volume 2 endpoint :=
  density_integrable.mul_continuousOn (hContinuous_continuous x).continuousOn

end WuPaper.R2Xi.SixthContinuous
#print axioms WuPaper.R2Xi.SixthContinuous.gain_integrand_integrable

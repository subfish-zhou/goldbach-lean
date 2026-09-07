import MathlibNt.SieveTheory.LiLiuPrereqWFCoarseDensitySource

set_option autoImplicit false
set_option warningAsError true

namespace MathlibNt.SieveTheory

open JurkatRichert1965ChenGammaOneQOne LiLiuPrereqWF.CoarseDensity
open SuzukiFiniteContinuousLayers

/-- The full legal continuous lower factor is the constructed JR lower function. -/
theorem continuousLowerFactor_eq_jr1965f {s : ℝ} (hs : 2 ≤ s) :
    suzukiContinuousLowerFactor s = jr1965f s := by
  rw [suzukiContinuousLowerFactor, suzukiContinuousLowerTail,
    (sourceParity_eq_jr1965 hs).2]
  ring

/-- The first interval formula, with the same constructed source and amplitude. -/
theorem jr1965f_eq_first_log {s : ℝ} (hs2 : 2 ≤ s) (hs4 : s ≤ 4) :
    jr1965f s = 2 * Real.exp Real.eulerMascheroniConstant * Real.log (s - 1) / s := by
  have h := one_sub_suzukiProposition118SourceTMinus_eq_lowerSieveFactorFirstInterval
    jr1965Section13HatSourceContract hs2 hs4
  rw [(sourceParity_eq_jr1965 hs2).2,
    suzukiLowerSieveFactorFirstInterval_eq_log hs2 hs4,
    suzukiLowerSieveAmplitude_eq_two_mul_exp_eulerMascheroni_of_sourceContract
      jr1965Section13HatSourceContract] at h
  linarith

end MathlibNt.SieveTheory

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


end MathlibNt.SieveTheory

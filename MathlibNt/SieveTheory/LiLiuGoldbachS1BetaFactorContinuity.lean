import MathlibNt.SieveTheory.LinearSieve.DimensionOneLowerFactor

open Set Filter MeasureTheory
open scoped Topology
open MathlibNt.SieveTheory.SwitchingPrinciple

namespace MathlibNt.SieveTheory.LiLiuOnePlusOneNine.GoldbachBig

/-- Li-Liu's ratio lies in the shared continuity interval. -/
theorem goldbachS1_lowerFactor_continuousAt_betaRatio :
    ContinuousAt dimensionOneLowerLinearSieveFactor (33 / 8 : ℝ) :=
  dimensionOneLowerLinearSieveFactor_continuousOn_four_six.continuousAt
    (Icc_mem_nhds (by norm_num) (by norm_num))

/-- Choose a fixed admissible ratio strictly below the endpoint before selecting N. -/
theorem goldbachS1_exists_betaRatio_below (η : ℝ) (hη : 0 < η) :
    ∃ s : ℝ, 4 ≤ s ∧ s < (33 / 8 : ℝ) ∧
      dimensionOneLowerLinearSieveFactor (33 / 8 : ℝ) - η ≤ dimensionOneLowerLinearSieveFactor s := by
  have hf : ∀ᶠ s : ℝ in 𝓝 (33 / 8 : ℝ),
      dimensionOneLowerLinearSieveFactor (33 / 8 : ℝ) - η < dimensionOneLowerLinearSieveFactor s :=
    goldbachS1_lowerFactor_continuousAt_betaRatio.eventually_mem (Ioi_mem_nhds (by linarith))
  have hfour : ∀ᶠ s : ℝ in 𝓝 (33 / 8 : ℝ), (4 : ℝ) < s :=
    eventually_gt_nhds (by norm_num)
  have hw := (hf.and hfour).filter_mono (nhdsWithin_le_nhds : 𝓝[<] (33 / 8 : ℝ) ≤ 𝓝 (33 / 8 : ℝ))
  have hlt : ∀ᶠ s : ℝ in 𝓝[<] (33 / 8 : ℝ), s < (33 / 8 : ℝ) := self_mem_nhdsWithin
  obtain ⟨s, ⟨hfs, hs4⟩, hslt⟩ := (hw.and hlt).exists
  exact ⟨s, hs4.le, hslt, hfs.le⟩

end MathlibNt.SieveTheory.LiLiuOnePlusOneNine.GoldbachBig
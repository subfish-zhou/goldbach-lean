import MathlibNt.SieveTheory.SwitchingPrinciple

open Set Filter MeasureTheory
open scoped Topology
open MathlibNt.SieveTheory.SwitchingPrinciple

namespace MathlibNt.SieveTheory.LiLiuOnePlusOneNine.GoldbachBig

private theorem S1BetaFactorContinuity_inner_continuous :
    ContinuousOn jurkatRichertInnerIntegral (Set.Icc (3 : ℝ) 5) := by
  let f : ℝ → ℝ := fun t => Real.log (t - 1) / t
  have hf : IntervalIntegrable f volume 2 4 := by
    apply ContinuousOn.intervalIntegrable
    apply ContinuousOn.div
    · apply ContinuousOn.log (continuousOn_id.sub continuousOn_const)
      intro t ht
      change t - 1 ≠ 0
      rw [Set.uIcc_of_le (by norm_num : (2 : ℝ) ≤ 4)] at ht
      linarith [ht.1]
    · exact continuousOn_id
    · intro t ht
      change t ≠ 0
      rw [Set.uIcc_of_le (by norm_num : (2 : ℝ) ≤ 4)] at ht
      linarith [ht.1]
  have hp : ContinuousOn (fun b => ∫ t in (2 : ℝ)..b, f t) (Set.Icc 2 4) := by
    have h := intervalIntegral.continuousOn_primitive_interval' (a := (2 : ℝ)) hf
      (by
        rw [Set.uIcc_of_le (by norm_num : (2 : ℝ) ≤ 4)]
        constructor <;> norm_num)
    simpa [Set.uIcc_of_le (by norm_num : (2 : ℝ) ≤ 4)] using h
  unfold jurkatRichertInnerIntegral
  change ContinuousOn (fun u => (∫ t in (2 : ℝ)..u - 1, f t)) (Set.Icc 3 5)
  apply hp.comp (continuousOn_id.sub continuousOn_const)
  intro u hu
  change 2 ≤ u - 1 ∧ u - 1 ≤ 4
  constructor <;> linarith [hu.1, hu.2]

/-- The same actual integral formula used at five is continuous at the beta ratio. -/
theorem goldbachS1_lowerFactor_continuousAt_betaRatio :
    ContinuousAt dimensionOneLowerLinearSieveFactor (33 / 8 : ℝ) := by
  have hinnerDiv : ContinuousOn
      (fun u : ℝ => jurkatRichertInnerIntegral u / u) (Set.Icc (3 : ℝ) 5) := by
    apply ContinuousOn.div S1BetaFactorContinuity_inner_continuous continuousOn_id
    intro u hu
    change u ≠ 0
    linarith [hu.1]
  have hinnerInt : IntervalIntegrable
      (fun u : ℝ => jurkatRichertInnerIntegral u / u) volume 3 5 := by
    apply ContinuousOn.intervalIntegrable
    rw [Set.uIcc_of_le (by norm_num : (3 : ℝ) ≤ 5)]
    exact hinnerDiv
  have hprimitive : ContinuousOn
      (fun b : ℝ => ∫ u in (3 : ℝ)..b, jurkatRichertInnerIntegral u / u)
      (Set.Icc (3 : ℝ) 5) := by
    have h := intervalIntegral.continuousOn_primitive_interval' (a := (3 : ℝ)) hinnerInt
      (by
        rw [Set.uIcc_of_le (by norm_num : (3 : ℝ) ≤ 5)]
        constructor <;> norm_num)
    simpa [Set.uIcc_of_le (by norm_num : (3 : ℝ) ≤ 5)] using h
  have houter : ContinuousOn
      (fun s : ℝ => ∫ u in (3 : ℝ)..s - 1, jurkatRichertInnerIntegral u / u)
      (Set.Icc (4 : ℝ) 6) := by
    apply hprimitive.comp (continuousOn_id.sub continuousOn_const)
    intro s hs
    change 3 ≤ s - 1 ∧ s - 1 ≤ 5
    constructor <;> linarith [hs.1, hs.2]
  have hlog : ContinuousOn (fun s : ℝ => Real.log (s - 1)) (Set.Icc (4 : ℝ) 6) := by
    apply ContinuousOn.log (continuousOn_id.sub continuousOn_const)
    intro s hs
    change s - 1 ≠ 0
    linarith [hs.1]
  have hfactor : ContinuousOn dimensionOneLowerLinearSieveFactor (Set.Icc (4 : ℝ) 6) := by
    unfold dimensionOneLowerLinearSieveFactor
    apply (continuousOn_const.div continuousOn_id ?_).mul (hlog.add houter)
    intro s hs
    change s ≠ 0
    linarith [hs.1]
  exact hfactor.continuousAt (Icc_mem_nhds (by norm_num) (by norm_num))

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
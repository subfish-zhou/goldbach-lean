import MathlibNt.SieveTheory.SuzukiUpperSourcePTail
import MathlibNt.SieveTheory.SuzukiUpperRosserDensityProducer
import MathlibNt.SieveTheory.JurkatRichert1965Section13HatSource

open Set Filter MeasureTheory
open MathlibNt.SieveTheory.SwitchingPrinciple
open MathlibNt.SieveTheory.JurkatRichert1965ChenGammaOneQOne
open MathlibNt.SieveTheory.SuzukiFiniteContinuousLayers
open MathlibNt.SieveTheory.SwitchingPrinciple.SuzukiLemma144KappaOne

namespace MathlibNt.SieveTheory.LiLiuOnePlusOneNine.GoldbachBig

private theorem UpperThird_inner_continuous :
    ContinuousOn jurkatRichertInnerIntegral (Set.Icc (3 : ℝ) 5) := by
  exact continuousOn_jurkatRichertInnerIntegral_three_five

theorem goldbach_lowerFactor_continuousOn_four_six :
    ContinuousOn dimensionOneLowerLinearSieveFactor (Icc (4 : ℝ) 6) := by
  exact dimensionOneLowerLinearSieveFactor_continuousOn_four_six

/-- The third upper interval in same-source integrated-lower form.
This is not yet the paper's reordered double-integral presentation. -/
noncomputable def goldbachUpperThirdIntervalFactor (s : ℝ) : ℝ :=
  (2 * Real.exp Real.eulerMascheroniConstant * (1 + jurkatRichertInnerIntegral 5) +
    ∫ t in (5 : ℝ)..s, dimensionOneLowerLinearSieveFactor (t - 1)) / s

private theorem UpperThird_shift_continuous :
    ContinuousOn (fun t : ℝ => dimensionOneLowerLinearSieveFactor (t - 1))
      (Icc (5 : ℝ) 7) := by
  apply goldbach_lowerFactor_continuousOn_four_six.comp
    (continuousOn_id.sub continuousOn_const)
  intro t ht
  change 4 ≤ t - 1 ∧ t - 1 ≤ 6
  constructor <;> linarith [ht.1, ht.2]

/-- The actual source-series upper factor on the entire third interval.
All source contracts and the amplitude normalization are supplied internally. -/
theorem goldbach_suzukiUpperFactor_eq_third {s : ℝ} (hs5 : 5 ≤ s) (hs7 : s ≤ 7) :
    suzukiContinuousUpperFactor s = goldbachUpperThirdIntervalFactor s := by
  have hH := jr1965Section13HatSourceContract
  have hsource := suzukiProposition118SourceTPlus_weighted_sub hH
    (x := (5 : ℝ)) (y := s) (by norm_num) hs5
  have hpoint : ∀ t ∈ Set.uIcc (5 : ℝ) s,
      suzukiProposition118SourceTMinus (t - 1) =
        1 - dimensionOneLowerLinearSieveFactor (t - 1) := by
    intro t ht
    rw [Set.uIcc_of_le hs5] at ht
    have hh := suzukiContinuousLowerFactor_eq_dimensionOne_of_sourceContract hH
      (s := t - 1) (by linarith [ht.1]) (by linarith [ht.2])
    dsimp only [suzukiContinuousLowerFactor, suzukiContinuousLowerTail] at hh
    linarith
  have hint : IntervalIntegrable
      (fun t : ℝ => dimensionOneLowerLinearSieveFactor (t - 1)) volume 5 s := by
    apply ContinuousOn.intervalIntegrable
    apply UpperThird_shift_continuous.mono
    rw [Set.uIcc_of_le hs5]
    exact Icc_subset_Icc le_rfl hs7
  rw [intervalIntegral.integral_congr hpoint,
    intervalIntegral.integral_sub (continuousOn_const.intervalIntegrable) hint,
    intervalIntegral.integral_const] at hsource
  have hbase := suzukiContinuousUpperFactor_eq_second_source_formula hH
    (u := (5 : ℝ)) (by norm_num) (by norm_num)
  rw [suzukiLowerSieveAmplitude_eq_two_mul_exp_eulerMascheroni_of_sourceContract hH] at hbase
  change suzukiContinuousUpperFactor 5 =
    2 * Real.exp Real.eulerMascheroniConstant / 5 *
      (1 + jurkatRichertInnerIntegral 5) at hbase
  unfold goldbachUpperThirdIntervalFactor
  apply (eq_div_iff (show s ≠ 0 by linarith)).2
  dsimp only [suzukiContinuousUpperFactor] at hbase ⊢
  simp only [smul_eq_mul, mul_one] at hsource
  nlinarith [hsource, hbase]

theorem goldbachUpperThirdIntervalFactor_continuousOn :
    ContinuousOn goldbachUpperThirdIntervalFactor (Icc (5 : ℝ) 7) := by
  have hint : IntervalIntegrable
      (fun t : ℝ => dimensionOneLowerLinearSieveFactor (t - 1)) volume 5 7 := by
    apply ContinuousOn.intervalIntegrable
    simpa only [Set.uIcc_of_le (by norm_num : (5 : ℝ) ≤ 7)] using UpperThird_shift_continuous
  have hp := intervalIntegral.continuousOn_primitive_interval' (a := (5 : ℝ)) hint
    (by norm_num [Set.mem_uIcc])
  have hc : ContinuousOn
      (fun s : ℝ => ∫ t in (5 : ℝ)..s, dimensionOneLowerLinearSieveFactor (t - 1))
      (Icc (5 : ℝ) 7) := by
    simpa only [Set.uIcc_of_le (by norm_num : (5 : ℝ) ≤ 7)] using hp
  unfold goldbachUpperThirdIntervalFactor
  apply (continuousOn_const.add hc).div continuousOn_id
  intro s hs
  change s ≠ 0
  linarith [hs.1]

/-- All three actual source intervals glue continuously, including 3 and 5. -/
theorem goldbach_suzukiUpperFactor_continuousOn_threeHalves_seven :
    ContinuousOn suzukiContinuousUpperFactor (Icc (3 / 2 : ℝ) 7) := by
  have hH := jr1965Section13HatSourceContract
  have hc1 : ContinuousOn (fun s : ℝ => suzukiLowerSieveAmplitude / s)
      (Icc (3 / 2 : ℝ) 3) := by
    apply continuousOn_const.div continuousOn_id
    intro s hs
    change s ≠ 0
    linarith [hs.1]
  have h1 : ContinuousOn suzukiContinuousUpperFactor (Icc (3 / 2 : ℝ) 3) := by
    apply hc1.congr
    intro s hs
    exact suzukiContinuousUpperFactorFirstIntervalIdentity_of_sourceContract
      jr1965Section13HatLayers hH s hs.1 hs.2
  have hc2 : ContinuousOn (fun s : ℝ => suzukiLowerSieveAmplitude / s *
      (1 + jurkatRichertInnerIntegral s)) (Icc (3 : ℝ) 5) := by
    apply (continuousOn_const.div continuousOn_id ?_).mul
      (continuousOn_const.add UpperThird_inner_continuous)
    intro s hs
    change s ≠ 0
    linarith [hs.1]
  have h2 : ContinuousOn suzukiContinuousUpperFactor (Icc (3 : ℝ) 5) := by
    apply hc2.congr
    intro s hs
    exact suzukiContinuousUpperFactor_eq_second_source_formula hH hs.1 hs.2
  have h3 : ContinuousOn suzukiContinuousUpperFactor (Icc (5 : ℝ) 7) := by
    apply goldbachUpperThirdIntervalFactor_continuousOn.congr
    intro s hs
    exact goldbach_suzukiUpperFactor_eq_third hs.1 hs.2
  have h12 := h1.union_of_isClosed h2 isClosed_Icc isClosed_Icc
  have h123 := h12.union_of_isClosed h3 (isClosed_Icc.union isClosed_Icc) isClosed_Icc
  apply h123.mono
  intro s hs
  by_cases hs3 : s ≤ 3
  · exact Or.inl (Or.inl ⟨hs.1, hs3⟩)
  · by_cases hs5 : s ≤ 5
    · exact Or.inl (Or.inr ⟨by linarith, hs5⟩)
    · exact Or.inr ⟨by linarith, hs.2⟩

/-- Nonnegative odd source layers give the sign needed for weighted upper sums. -/
theorem goldbach_one_le_suzukiUpperFactor {s : ℝ} (hs : 1 < s) :
    1 ≤ suzukiContinuousUpperFactor s := by
  have hsum : 0 ≤ suzukiProposition118SourceTPlus s := by
    unfold suzukiProposition118SourceTPlus
    exact tsum_nonneg (fun k => suzukiLayer_one_two_odd_nonneg hs k)
  unfold suzukiContinuousUpperFactor
  linarith

end MathlibNt.SieveTheory.LiLiuOnePlusOneNine.GoldbachBig
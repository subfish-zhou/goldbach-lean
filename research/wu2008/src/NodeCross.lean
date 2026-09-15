import MathlibNt.Wu2008DoubleSieve.ImprovementCrossLower

namespace NodeExtension
open Real
open scoped Interval

noncomputable def sigma (a b c : ℝ) : ℝ :=
  ∫ v in a..b, log (c / (v - 1)) / v

noncomputable def D0 : ℝ := sigma 3 5 4

theorem sigma_integrable {a b c : ℝ} (ha : 1 < a) (hab : a ≤ b) (hc : 0 < c) :
    IntervalIntegrable (fun v => log (c / (v - 1)) / v) MeasureTheory.volume a b := by
  apply ContinuousOn.intervalIntegrable
  rw [Set.uIcc_of_le hab]
  apply ContinuousOn.div
  · apply ContinuousOn.log
    · exact continuousOn_const.div (continuousOn_id.sub continuousOn_const)
        (fun v hv => by dsimp; linarith [hv.1])
    · intro v hv
      exact ne_of_gt (div_pos hc (by linarith [hv.1]))
  · exact continuousOn_id
  · intro v hv
    dsimp
    linarith [hv.1]

theorem D0_bounds : 0 ≤ D0 ∧ D0 ≤ 2 / 3 := by
  have hi := sigma_integrable (a := 3) (b := 5) (c := 4)
    (by norm_num) (by norm_num) (by norm_num)
  have hn (v : ℝ) (hv : v ∈ Set.Icc 3 5) : 0 ≤ log (4 / (v - 1)) / v := by
    apply div_nonneg
    · apply log_nonneg
      apply (le_div_iff₀ (by linarith [hv.1] : 0 < v - 1)).2
      linarith [hv.2]
    · linarith [hv.1]
  have hu (v : ℝ) (hv : v ∈ Set.Icc 3 5) : log (4 / (v - 1)) / v ≤ 1 / 3 := by
    have hp : 0 < v - 1 := by linarith [hv.1]
    have hq : 4 / (v - 1) ≤ 2 := (div_le_iff₀ hp).2 (by linarith [hv.1])
    have hl : log (4 / (v - 1)) ≤ 1 := by
      have hlog := log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)
      have hm := log_le_log (div_pos (by norm_num) hp) hq
      linarith
    apply (div_le_iff₀ (by linarith [hv.1] : 0 < v)).2
    linarith [hv.1]
  constructor
  · exact intervalIntegral.integral_nonneg (by norm_num) hn
  · have h := intervalIntegral.integral_mono_on (by norm_num : (3 : ℝ) ≤ 5)
      hi (intervalIntegrable_const : IntervalIntegrable (fun _ : ℝ => (1 : ℝ) / 3)
        MeasureTheory.volume 3 5) hu
    norm_num [D0, sigma] at h ⊢
    exact h

theorem D0_lt_one : D0 < 1 := by linarith [D0_bounds.2]

theorem actual_h4_tail {δ : ℝ} (hd : 0 < δ) (hdhi : δ ≤ 1 / 10) :
    (∫ v in (3 : ℝ)..5, Wu2008DoubleSieve.wuImprovementLimit true δ v / v) ≤
      Wu2008DoubleSieve.wuImprovementLimit false δ 4 := by
  have hc := Wu2008DoubleSieve.wuImprovementLimit_lower_cross hd hdhi
    (s := 4) (t := 6) (by norm_num) (by norm_num) (by norm_num)
  have hn := Wu2008DoubleSieve.wuImprovementLimit_nonneg false hd
    (by linarith : δ < 1 / 2) (s := 6) (by norm_num) (by norm_num)
  norm_num at hc
  linarith

end NodeExtension

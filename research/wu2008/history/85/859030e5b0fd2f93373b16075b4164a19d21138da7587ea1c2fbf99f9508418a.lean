import WE07FifthSourceRecurrence

namespace WuTarget.Wu08FifthSource
open Real Set MeasureTheory Wu2008DoubleSieve SharpMassBalance
open scoped Interval
noncomputable section

def reducedWeight (s : ℝ) : ℝ :=
  log (((1/2-a*s)-sliceLower (1/2-a*s))/sliceLower (1/2-a*s)) /
    (s*(1/2-a*s))

theorem reduced_weight_bounds {s : ℝ} (hs : s ∈ Icc s0 FifthClassicalShape.q) :
    0 ≤ reducedWeight s ∧ reducedWeight s ≤ 2 := by
  let z := 1/2-a*s
  let l := sliceLower z
  have hz := scalar_geometry hs
  have hg := slice_geometry hz
  have ha : 0 < a := truncatedSixthLower_parameters.1
  have hl : 0 < l := hg.1
  have hzl : 0 < z-l := by dsimp only [z, l]; linarith [hg.2.1, hg.2.2.1]
  have hr1 : 1 ≤ (z-l)/l := (le_div_iff₀ hl).2 (by
    dsimp only [z, l]
    linarith [hg.2.1])
  have hla : a ≤ l := le_max_left _ _
  have hzb : z-l ≤ b := by
    have h := le_max_right a (z-b)
    change z-b ≤ l at h
    linarith
  have hb0 : 0 ≤ b :=
    (truncatedSixthLower_parameters.1.trans truncatedSixthLower_parameters.2.1).le
  have hr2 : (z-l)/l ≤ b/a :=
    (div_le_div_of_nonneg_right hzb hl.le).trans
      (div_le_div_of_nonneg_left hb0 ha hla)
  have hlog : log ((z-l)/l) ≤ 2/3 := by
    have h := log_le_sub_one_of_pos (div_pos hzl hl)
    have hb : b/a-1 ≤ (2/3 : ℝ) := by
      norm_num [a, b, truncatedSixthLowerAlpha, truncatedSixthLowerBeta]
    linarith only [h, hr2, hb]
  have hs3 : (3 : ℝ) ≤ s := FifthClassicalShape.parameters.1.le.trans hs.1
  have hden : (1/3 : ℝ) ≤ s*z := by
    have hm := mul_le_mul hs3 hz.1 (by positivity : (0 : ℝ) ≤ 2*a) (by linarith)
    have hn : (1/3 : ℝ) ≤ 3*(2*a) := by norm_num [a, truncatedSixthLowerAlpha]
    exact hn.trans hm
  change 0 ≤ log ((z-l)/l)/(s*z) ∧ log ((z-l)/l)/(s*z) ≤ 2
  refine ⟨div_nonneg (log_nonneg hr1) (by linarith), ?_⟩
  apply (div_le_iff₀ (by linarith : 0 < s*z)).2
  linarith only [hlog, hden]

theorem reduced_weight_continuous :
    ContinuousOn reducedWeight (Icc s0 FifthClassicalShape.q) := by
  have hp := FifthClassicalShape.parameters
  have hz (s : ℝ) (hs : s ∈ Icc s0 FifthClassicalShape.q) :=
    slice_geometry (scalar_geometry hs)
  have hl : Continuous (fun s : ℝ => sliceLower (1/2-a*s)) := by
    unfold sliceLower
    fun_prop
  have hr : ContinuousOn
      (fun s : ℝ => ((1/2-a*s)-sliceLower (1/2-a*s))/sliceLower (1/2-a*s))
      (Icc s0 FifthClassicalShape.q) :=
    ((by fun_prop : ContinuousOn (fun s : ℝ => 1/2-a*s) _).sub hl.continuousOn).div
      hl.continuousOn (fun s hs => (hz s hs).1.ne')
  unfold reducedWeight
  apply ContinuousOn.div
  · apply hr.log
    intro s hs
    have hh := hz s hs
    exact (div_pos (by linarith [hh.2.1, hh.2.2.1]) hh.1).ne'
  · fun_prop
  · intro s hs
    exact mul_ne_zero (by linarith [hp.1, hs.1] : s ≠ 0) (hz s hs).2.2.1.ne'

theorem scalar_weight_identity (s : ℝ) :
    scalarReduced s = wuLowerCoefficient s*reducedWeight s := by
  unfold scalarReduced reducedWeight
  ring

theorem coefficient_error_transport {p : ℝ → ℝ} {e : ℝ} (he : 0 ≤ e)
    (hp : ContinuousOn p (Icc s0 FifthClassicalShape.q))
    (herr : ∀ s ∈ Icc s0 FifthClassicalShape.q, |wuLowerCoefficient s-p s| ≤ e) :
    |Wu08TerminalAlignment.fifthMain-
      4*(∫ s in s0..FifthClassicalShape.q, p s*reducedWeight s)| ≤ 10*e := by
  have hab := FifthClassicalShape.parameters.2.1.le
  have hi : IntervalIntegrable (fun s => p s*reducedWeight s)
      volume s0 FifthClassicalShape.q := by
    apply ContinuousOn.intervalIntegrable
    rw [uIcc_of_le hab]
    exact hp.mul reduced_weight_continuous
  have hd := scalar_interval_integrable.sub hi
  have hb (s : ℝ) (hs : s ∈ Icc s0 FifthClassicalShape.q) :
      -(2*e) ≤ scalarReduced s-p s*reducedWeight s ∧
        scalarReduced s-p s*reducedWeight s ≤ 2*e := by
    have hw := reduced_weight_bounds hs
    have hh := abs_le.mp (herr s hs)
    have hm1 := mul_le_mul_of_nonneg_right hh.1 hw.1
    have hm2 := mul_le_mul_of_nonneg_right hh.2 hw.1
    have hm3 := mul_le_mul_of_nonneg_left hw.2 he
    rw [scalar_weight_identity]
    constructor <;> nlinarith only [hm1, hm2, hm3]
  have hlo := intervalIntegral.integral_mono_on hab (intervalIntegrable_const (c := -(2*e)))
    hd (fun s hs => (hb s hs).1)
  have hhi := intervalIntegral.integral_mono_on hab hd (intervalIntegrable_const (c := 2*e))
    (fun s hs => (hb s hs).2)
  rw [intervalIntegral.integral_const, smul_eq_mul,
    intervalIntegral.integral_sub scalar_interval_integrable hi] at hlo hhi
  have hlen : FifthClassicalShape.q-s0 ≤ (5/4 : ℝ) := by
    norm_num [FifthClassicalShape.q, s0, a, b,
      truncatedSixthLowerAlpha, truncatedSixthLowerBeta]
  have hmul := mul_le_mul_of_nonneg_right hlen he
  rw [scalar_parameter_transport]
  apply abs_le.mpr
  constructor <;> nlinarith only [hlo, hhi, hmul]

end
end WuTarget.Wu08FifthSource

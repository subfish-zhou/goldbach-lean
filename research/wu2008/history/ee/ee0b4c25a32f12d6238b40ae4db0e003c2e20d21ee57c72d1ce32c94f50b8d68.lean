import MathlibNt.Wu2008DoubleSieve.ImprovementIntegrals
import Mathlib.MeasureTheory.Integral.DominatedConvergence

/-!
# Literal kernels for Wu's first feedback inequality

Wu04, author TeX lines 1202–1259 and 2539–2619. The characteristic
functions below are of closed intervals, exactly as in the source.
The denominator estimate is analytic, not a numerical table input.
-/

namespace Wu2008DoubleSieve

open Set Real MeasureTheory
open scoped Interval

noncomputable def firstFeedbackSigma (a b c : ℝ) : ℝ :=
  ∫ u in a..b, log (c / (u - 1)) / u

noncomputable def firstFeedbackSigmaZero (x : ℝ) : ℝ :=
  firstFeedbackSigma 3 (x + 2) (x + 1) / (1 - firstFeedbackSigma 3 5 4)

noncomputable def firstFeedbackXi (x s t : ℝ) : ℝ :=
  firstFeedbackSigmaZero x / (2 * x) * log (16 / ((s - 1) * (t - 1))) +
  (Icc (t - 2) 3).indicator (fun _ : ℝ => (1 : ℝ)) x / (2 * x) *
    log ((x + 1) ^ 2 / ((s - 1) * (t - 1))) +
  (Icc (t - t / s - 1) (t - 2)).indicator (fun _ : ℝ => (1 : ℝ)) x /
    (2 * x) * log ((x + 1) / ((s - 1) * (t - 1 - x)))

theorem firstFeedbackSigma_integrand_continuousOn {a b c : ℝ}
    (ha : 1 < a) (hab : a ≤ b) (hc : 0 < c) :
    ContinuousOn (fun u => log (c / (u - 1)) / u) (uIcc a b) := by
  rw [uIcc_of_le hab]
  apply ContinuousOn.div
  · apply ContinuousOn.log
    · exact continuousOn_const.div (continuousOn_id.sub continuousOn_const)
        (fun u hu => by change u - 1 ≠ 0; linarith [hu.1])
    · intro u hu
      exact ne_of_gt (div_pos hc (by linarith [hu.1]))
  · exact continuousOn_id
  · intro u hu
    change u ≠ 0
    linarith [hu.1]

theorem firstFeedbackSigma_intervalIntegrable {a b c : ℝ}
    (ha : 1 < a) (hab : a ≤ b) (hc : 0 < c) :
    IntervalIntegrable (fun u => log (c / (u - 1)) / u) volume a b :=
  (firstFeedbackSigma_integrand_continuousOn ha hab hc).intervalIntegrable

theorem firstFeedbackSigma_nonneg {a b c : ℝ}
    (ha : 1 < a) (hab : a ≤ b) (hbc : b - 1 ≤ c) :
    0 ≤ firstFeedbackSigma a b c := by
  apply intervalIntegral.integral_nonneg hab
  intro u hu
  apply div_nonneg _ (by linarith [hu.1])
  apply Real.log_nonneg
  exact (le_div_iff₀ (by linarith [hu.1] : 0 < u - 1)).2
    (by nlinarith [hu.2])

theorem firstFeedbackSigma_three_five_four_le :
    firstFeedbackSigma 3 5 4 ≤ 2 / 3 := by
  have hi := firstFeedbackSigma_intervalIntegrable
    (by norm_num : (1 : ℝ) < 3) (by norm_num : (3 : ℝ) ≤ 5)
    (by norm_num : (0 : ℝ) < 4)
  have hb : ∀ u ∈ Icc (3 : ℝ) 5, log (4 / (u - 1)) / u ≤ (1 : ℝ) / 3 := by
    intro u hu
    have hu0 : 0 < u := by linarith [hu.1]
    have hv0 : 0 < u - 1 := by linarith [hu.1]
    have hq : 4 / (u - 1) ≤ 2 := (div_le_iff₀ hv0).2 (by linarith [hu.1])
    have hl : log (4 / (u - 1)) ≤ 1 :=
      (Real.log_le_sub_one_of_pos (div_pos (by norm_num) hv0)).trans (by linarith)
    exact (div_le_iff₀ hu0).2 (by linarith [hu.1])
  have h := intervalIntegral.integral_mono_on (by norm_num : (3 : ℝ) ≤ 5)
    hi (intervalIntegrable_const : IntervalIntegrable (fun _ : ℝ => (1 : ℝ) / 3)
      volume 3 5) hb
  norm_num [firstFeedbackSigma, intervalIntegral.integral_const] at h ⊢
  exact h

theorem firstFeedbackSigma_denominator_pos :
    0 < 1 - firstFeedbackSigma 3 5 4 := by
  linarith [firstFeedbackSigma_three_five_four_le]

theorem firstFeedbackSigmaZero_nonneg {x : ℝ} (hx : x ∈ Icc (1 : ℝ) 3) :
    0 ≤ firstFeedbackSigmaZero x :=
  div_nonneg (firstFeedbackSigma_nonneg (by norm_num) (by linarith [hx.1])
    (by linarith)) firstFeedbackSigma_denominator_pos.le

theorem firstFeedbackSigma_split {b c : ℝ}
    (hb : 3 ≤ b) (hc : 0 < c) :
    firstFeedbackSigma 3 b c =
      log c * (∫ u in (3 : ℝ)..b, 1 / u) -
        ∫ u in (3 : ℝ)..b, log (u - 1) / u := by
  have hi : ContinuousOn (fun u : ℝ => 1 / u) (uIcc 3 b) := by
    apply continuousOn_const.div continuousOn_id
    intro u hu
    rw [uIcc_of_le hb] at hu
    change u ≠ 0
    linarith [hu.1]
  have hj : ContinuousOn (fun u : ℝ => log (u - 1) / u) (uIcc 3 b) := by
    apply ((continuousOn_id.sub continuousOn_const).log ?_).div continuousOn_id
    · intro u hu
      rw [uIcc_of_le hb] at hu
      change u ≠ 0
      linarith [hu.1]
    · intro u hu
      rw [uIcc_of_le hb] at hu
      change u - 1 ≠ 0
      linarith [hu.1]
  rw [← intervalIntegral.integral_const_mul,
    ← intervalIntegral.integral_sub (hi.intervalIntegrable.const_mul _) hj.intervalIntegrable]
  apply intervalIntegral.integral_congr
  intro u hu
  rw [uIcc_of_le hb] at hu
  dsimp only
  rw [Real.log_div hc.ne' (by linarith [hu.1] : u - 1 ≠ 0)]
  ring

theorem firstFeedbackSigma_variable_continuousOn :
    ContinuousOn (fun x => firstFeedbackSigma 3 (x + 2) (x + 1)) (Icc (1 : ℝ) 3) := by
  have hi : ContinuousOn (fun u : ℝ => 1 / u) (uIcc 3 5) := by
    apply continuousOn_const.div continuousOn_id
    intro u hu
    rw [uIcc_of_le (by norm_num : (3 : ℝ) ≤ 5)] at hu
    change u ≠ 0
    linarith [hu.1]
  have hj : ContinuousOn (fun u : ℝ => log (u - 1) / u) (uIcc 3 5) := by
    apply ((continuousOn_id.sub continuousOn_const).log ?_).div continuousOn_id
    · intro u hu
      rw [uIcc_of_le (by norm_num : (3 : ℝ) ≤ 5)] at hu
      change u ≠ 0
      linarith [hu.1]
    · intro u hu
      rw [uIcc_of_le (by norm_num : (3 : ℝ) ≤ 5)] at hu
      change u - 1 ≠ 0
      linarith [hu.1]
  have hm : MapsTo (fun x : ℝ => x + 2) (Icc 1 3) (uIcc 3 5) := by
    intro x hx
    rw [uIcc_of_le (by norm_num : (3 : ℝ) ≤ 5)]
    constructor <;> linarith [hx.1, hx.2]
  have hpi := (intervalIntegral.continuousOn_primitive_interval' (μ := volume)
    hi.intervalIntegrable (left_mem_uIcc : (3 : ℝ) ∈ uIcc 3 5)).comp
      (continuousOn_id.add continuousOn_const) hm
  have hpj := (intervalIntegral.continuousOn_primitive_interval' (μ := volume)
    hj.intervalIntegrable (left_mem_uIcc : (3 : ℝ) ∈ uIcc 3 5)).comp
      (continuousOn_id.add continuousOn_const) hm
  have hl : ContinuousOn (fun x : ℝ => log (x + 1)) (Icc 1 3) :=
    (continuousOn_id.add continuousOn_const).log
      (fun x hx => by change x + 1 ≠ 0; linarith [hx.1])
  apply (hl.mul hpi |>.sub hpj).congr
  intro x hx
  exact firstFeedbackSigma_split (by linarith [hx.1]) (by linarith [hx.1])

theorem firstFeedbackSigmaZero_continuousOn :
    ContinuousOn firstFeedbackSigmaZero (Icc (1 : ℝ) 3) :=
  firstFeedbackSigma_variable_continuousOn.div_const _

theorem firstFeedbackSigmaZero_intervalIntegrable :
    IntervalIntegrable firstFeedbackSigmaZero volume 1 3 := by
  apply ContinuousOn.intervalIntegrable
  simpa only [uIcc_of_le (by norm_num : (1 : ℝ) ≤ 3)] using
    firstFeedbackSigmaZero_continuousOn

theorem firstFeedbackSigmaZero_div_continuousOn :
    ContinuousOn (fun x => firstFeedbackSigmaZero x / x) (Icc (1 : ℝ) 3) :=
  firstFeedbackSigmaZero_continuousOn.div continuousOn_id
    (fun x hx => by change x ≠ 0; linarith [hx.1])

theorem firstFeedbackSigmaZero_div_intervalIntegrable :
    IntervalIntegrable (fun x => firstFeedbackSigmaZero x / x) volume 1 3 := by
  apply ContinuousOn.intervalIntegrable
  simpa only [uIcc_of_le (by norm_num : (1 : ℝ) ≤ 3)] using
    firstFeedbackSigmaZero_div_continuousOn

theorem firstFeedbackSigmaZero_one : firstFeedbackSigmaZero 1 = 0 := by
  norm_num [firstFeedbackSigmaZero, firstFeedbackSigma]

theorem firstFeedbackSigmaZero_gain_intervalIntegrable (upper : Bool) {δ : ℝ}
    (hδ : 0 < δ) (hδhi : δ < 1 / 2) :
    IntervalIntegrable (fun x =>
      wuImprovementLimit upper δ x * firstFeedbackSigmaZero x / x) volume 1 3 := by
  have hc : ContinuousOn (fun x => firstFeedbackSigmaZero x / x) (uIcc 1 3) := by
    simpa only [uIcc_of_le (by norm_num : (1 : ℝ) ≤ 3)] using
      firstFeedbackSigmaZero_div_continuousOn
  simpa only [mul_div_assoc] using
    (wuImprovementLimit_intervalIntegrable upper hδ hδhi
      (by norm_num : (1 : ℝ) ≤ 1) (by norm_num : (1 : ℝ) ≤ 3)
      (by norm_num : (3 : ℝ) ≤ 10)).mul_continuousOn hc

end Wu2008DoubleSieve

import E09JointMainMajorCurvature

noncomputable section
open Real Set MeasureTheory Wu2008DoubleSieve
open scoped Interval

namespace WuTarget.E09JointMainMajor
open FixedCoefficientUpperEnclosure (a s)
open FixedCoefficientHLowerEnclosure (c)
open Phase22 (u)

def upperFour : ℝ :=
  (3 * (13 / 18 + 7 * upperLog (3 / 2) / 6 - lowerLog (4 / 3) / 6) +
    2 * (-20 / 9 + (8 / 3) * upperLog (3 / 2) + 8 / 3 - 4 / 9 + 16 / 243)) / 5

def upperFive : ℝ :=
  (3 * (2 / 3 + (7 / 6) * (upperLog (4 / 3) + upperLog (3 / 2)) -
      lowerLog (3 / 2) / 6) +
    2 * (-20 / 9 + (8 / 3) * (upperLog (4 / 3) + upperLog (3 / 2)) +
      2 - 1 / 4 + 1 / 36)) / 5

theorem upperFour_paid : wuUpperCoefficient 4 ≤ upperFour := by
  have h := (HighSharedKernelMagnitude.initial_sandwich
    (by norm_num : (3 : ℝ) ≤ 4) (by norm_num)).2
  have l1 := log_lower (by norm_num : (1 : ℝ) ≤ 4 / 3)
  have u2 := log_upper (by norm_num : (1 : ℝ) ≤ 3 / 2)
  have he : log (3 : ℝ) = log 2 + log (3 / 2 : ℝ) := by
    rw [← log_mul (by norm_num) (by norm_num)]
    norm_num
  have he2 : log (2 : ℝ) = log (4 / 3 : ℝ) + log (3 / 2 : ℝ) := by
    rw [← log_mul (by norm_num) (by norm_num)]
    norm_num
  norm_num [HighSharedKernelMagnitude.lowerPrimitive, SharpLogRecurrence.upperPrimitive] at h
  unfold upperFour
  linarith only [h, l1, u2, he, he2]

theorem upperFive_paid : wuUpperCoefficient 5 ≤ upperFive := by
  have h := (HighSharedKernelMagnitude.initial_sandwich
    (by norm_num : (3 : ℝ) ≤ 5) le_rfl).2
  have u1 := log_upper (by norm_num : (1 : ℝ) ≤ 4 / 3)
  have l2 := log_lower (by norm_num : (1 : ℝ) ≤ 3 / 2)
  have u2 := log_upper (by norm_num : (1 : ℝ) ≤ 3 / 2)
  have h4 : log (4 : ℝ) = 2 * log 2 := by
    have h := log_pow (2 : ℝ) 2
    norm_num at h
    exact h
  have he : log (3 : ℝ) = log 2 + log (3 / 2 : ℝ) := by
    rw [← log_mul (by norm_num) (by norm_num)]
    norm_num
  have he2 : log (2 : ℝ) = log (4 / 3 : ℝ) + log (3 / 2 : ℝ) := by
    rw [← log_mul (by norm_num) (by norm_num)]
    norm_num
  norm_num [HighSharedKernelMagnitude.lowerPrimitive, SharpLogRecurrence.upperPrimitive, h4] at h
  unfold upperFive
  linarith only [h, u1, l2, u2, he, he2]

def middleSurplus (v : ℝ) : ℝ :=
  (5 - v) * (287 / 250 - upperFour) +
    (v - 4) * (9044059 / 6431250 - upperFive) +
    chordDefect v - (v - 4) * (5 - v) / 144

theorem middle_pointwise {v : ℝ} (hv : v ∈ Icc (4 : ℝ) 5) :
    JointSharedTightEnclosure.middleLo v + middleSurplus v ≤
      GConvexChord.C + GConvexChord.m * v - wuUpperCoefficient v := by
  have hc := variable_chord_defect hv
  have h4 := mul_le_mul_of_nonneg_left upperFour_paid (show 0 ≤ 5 - v by linarith [hv.2])
  have h5 := mul_le_mul_of_nonneg_left upperFive_paid (show 0 ≤ v - 4 by linarith [hv.1])
  unfold JointSharedTightEnclosure.middleLo middleSurplus GConvexChord.C GConvexChord.m
  linarith only [hc, h4, h5]

def middleGain : ℝ := ∫ t in c 5..c 4,
  SharedRationalEnvelope.weight t * middleSurplus (u t)

theorem middle_gain_paid :
    ExactWeightTripleEnclosure.middleLower + middleGain ≤
      BaseGSharedActualRecovery.middleKernel := by
  have hl : a ≤ c 5 := by norm_num [a, c, truncatedSixthLowerAlpha]
  have hr : c 4 ≤ s := SharedRationalEnvelope.window_order.2.1
  have ho : c 5 ≤ c 4 := by norm_num [a, c, truncatedSixthLowerAlpha]
  have hp : Continuous middleSurplus := by
    unfold middleSurplus chordDefect curvaturePrimitive
    fun_prop
  have hsum : Continuous (fun v => JointSharedTightEnclosure.middleLo v + middleSurplus v) :=
    (by unfold JointSharedTightEnclosure.middleLo; fun_prop).add hp
  have hi := JointSharedTightEnclosure.weighted_integrable _ hsum hl hr ho
  have hk := BaseGSharedActualRecovery.kernel_integrable
    (fun v => GConvexChord.C + GConvexChord.m * v) hl hr ho (by fun_prop)
  have hm := intervalIntegral.integral_mono_on ho hi hk (fun t ht => ?_)
  · have he : (∫ t in c 5..c 4,
        SharedRationalEnvelope.weight t * JointSharedTightEnclosure.middleLo (u t)) =
        ExactWeightTripleEnclosure.middleLower := by
      unfold ExactWeightTripleEnclosure.middleLower
      rw [← ExactWeightTripleEnclosure.shifted_ftc _ _ _ _ _ _ _
        (by norm_num [a, c, truncatedSixthLowerAlpha])
        (by norm_num [a, c, truncatedSixthLowerAlpha]) ho]
      apply intervalIntegral.integral_congr
      intro t ht
      dsimp [JointSharedTightEnclosure.middleLo, ExactWeightTripleEnclosure.shifted,
        ExactWeightTripleEnclosure.poly]
      ring
    simp_rw [mul_add] at hm
    rw [intervalIntegral.integral_add
      (JointSharedTightEnclosure.weighted_integrable _
        (by unfold JointSharedTightEnclosure.middleLo; fun_prop) hl hr ho)
      (JointSharedTightEnclosure.weighted_integrable _ hp hl hr ho), he] at hm
    exact hm
  rw [HighSharedKernelMagnitude.kernel_density]
  exact mul_le_mul_of_nonneg_left
    (middle_pointwise (JointSharedTightEnclosure.middle_geometry ht).2.2)
    (HighSharedKernelMagnitude.middle_weight ht).1

end WuTarget.E09JointMainMajor

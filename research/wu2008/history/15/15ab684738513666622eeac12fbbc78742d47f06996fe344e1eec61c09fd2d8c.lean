import E09JointMainMajorMiddlePayment

noncomputable section
open Real Set MeasureTheory Wu2008DoubleSieve
open scoped Interval

namespace WuTarget.E09JointMainMajor
open FixedCoefficientUpperEnclosure (a s)
open FixedCoefficientHLowerEnclosure (c)
open Phase22 (u)

theorem log_lower_quadratic {y : ℝ} (hy : 0 ≤ y) :
    y - y ^ 2 / 2 ≤ log (1 + y) := by
  let F : ℝ → ℝ := fun y => log (1 + y) - y + y ^ 2 / 2
  have hd (x : ℝ) (hx : 0 ≤ x) : HasDerivAt F (x ^ 2 / (1 + x)) x := by
    have hn : 1 + x ≠ 0 := by linarith
    convert! ((((hasDerivAt_id x).const_add 1).log hn).sub (hasDerivAt_id x)).add
      (((hasDerivAt_id x).pow 2).div_const 2) using 1
    dsimp
    field_simp [hn]
    ring
  have hm : MonotoneOn F (Ici 0) := by
    apply monotoneOn_of_deriv_nonneg (convex_Ici _)
    · intro x hx; exact (hd x hx).continuousAt.continuousWithinAt
    · intro x hx; exact (hd x (interior_subset hx)).differentiableAt.differentiableWithinAt
    · intro x hx
      rw [(hd x (interior_subset hx)).deriv]
      exact div_nonneg (sq_nonneg x) (by linarith [interior_subset hx])
  have h := hm (by simp) hy hy
  have hz : F 0 = 0 := by norm_num [F]
  rw [hz] at h
  dsimp [F] at h
  linarith only [h]

theorem initial_upper_quadratic {z : ℝ} (hz : z ∈ Icc (3 : ℝ) 4) :
    wuUpperCoefficient z ≤ 1 + (z - 3) ^ 2 / 4 := by
  have h := SharedRationalEnvelope.upper_log hz.1 hz.2
  have hl := log_lower_quadratic (show 0 ≤ z - 3 by linarith [hz.1])
  rw [show 1 + (z - 3) = z - 2 by ring] at hl
  linarith only [h, hl]

theorem lower_delayed_upper {y : ℝ} (hy : 0 ≤ y) (hy1 : y ≤ 1) :
    wuLowerCoefficient (4 + y) ≤ log (3 + y) + y ^ 3 / 36 := by
  have ho : (3 : ℝ) ≤ 3 + y := by linarith
  have hr := wuLowerCoefficient_sub_eq_integral (by norm_num : (2 : ℝ) ≤ 4)
    (show 4 ≤ 4 + y by linarith)
  have hi : IntervalIntegrable (fun z : ℝ => 1 / z + (z - 3) ^ 2 / 12) volume 3 (3 + y) := by
    apply ContinuousOn.intervalIntegrable
    apply ContinuousOn.add
    · exact continuousOn_const.div continuousOn_id (fun z hz => by
        rw [uIcc_of_le ho] at hz
        linarith [hz.1])
    · fun_prop
  have hm := intervalIntegral.integral_mono_on ho
    (wuUpperCoefficient_div_intervalIntegrable (by norm_num) ho) hi (fun z hz => ?_)
  · have hd (z : ℝ) (hz : z ∈ uIcc (3 : ℝ) (3 + y)) :
        HasDerivAt (fun z => log z + (z - 3) ^ 3 / 36) (1 / z + (z - 3) ^ 2 / 12) z := by
      rw [uIcc_of_le ho] at hz
      convert! (hasDerivAt_log (by linarith [hz.1] : z ≠ 0)).add
        ((((hasDerivAt_id z).sub_const 3).pow 3).div_const 36) using 1
      dsimp
      ring
    rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hd hi] at hm
    norm_num only [show (4 : ℝ) - 1 = 3 by norm_num,
      show 4 + y - 1 = 3 + y by ring, BaseRecurrenceLower.lower_four_value] at hr
    norm_num at hm
    linarith only [hr, hm]
  have hz0 : 0 < z := by linarith [hz.1]
  have hu := initial_upper_quadratic ⟨hz.1, by linarith [hz.2]⟩
  apply (div_le_iff₀ hz0).2
  have hcancel : 1 / z * z = 1 := by field_simp
  have hp := mul_nonneg (sq_nonneg (z - 3)) (show 0 ≤ z - 3 by linarith [hz.1])
  rw [add_mul, hcancel]
  nlinarith only [hu, hp]

theorem log_three_cubic {y : ℝ} (hy : 0 ≤ y) :
    log (3 + y) ≤ log 3 + y / 3 - y ^ 2 / 18 + y ^ 3 / 81 := by
  let F : ℝ → ℝ := fun y => log 3 + y / 3 - y ^ 2 / 18 + y ^ 3 / 81 - log (3 + y)
  have hd (x : ℝ) (hx : 0 ≤ x) : HasDerivAt F (x ^ 3 / (27 * (3 + x))) x := by
    have hn : 3 + x ≠ 0 := by linarith
    convert! (((((hasDerivAt_const x (log (3 : ℝ))).add
      ((hasDerivAt_id x).div_const 3)).sub (((hasDerivAt_id x).pow 2).div_const 18)).add
      (((hasDerivAt_id x).pow 3).div_const 81)).sub
      (((hasDerivAt_id x).const_add 3).log hn) using 1
    dsimp
    field_simp [hn]
    ring
  have hm : MonotoneOn F (Ici 0) := by
    apply monotoneOn_of_deriv_nonneg (convex_Ici _)
    · intro x hx; exact (hd x hx).continuousAt.continuousWithinAt
    · intro x hx; exact (hd x (interior_subset hx)).differentiableAt.differentiableWithinAt
    · intro x hx
      have hh := interior_subset hx
      rw [(hd x hh).deriv]
      exact div_nonneg (pow_nonneg hh 3) (by linarith)
  have h := hm (by simp) hy hy
  have hz : F 0 = 0 := by norm_num [F]
  rw [hz] at h
  dsimp [F] at h
  linarith only [h]

def logThreeCap : ℝ := upperLog (4 / 3) + 2 * upperLog (3 / 2)
def highA0 : ℝ := logThreeCap / 4
def highA1 : ℝ := 1 / 12 - logThreeCap / 16
def highA2 : ℝ := logThreeCap / 64 - 5 / 144
def highA3 : ℝ := 13 / 1296 - logThreeCap / 256 + 5 / 576
def highDensity (y : ℝ) : ℝ := highA0 + highA1 * y + highA2 * y ^ 2 + highA3 * y ^ 3
def highIncrement (y : ℝ) : ℝ :=
  highA0 * y + highA1 * y ^ 2 / 2 + highA2 * y ^ 3 / 3 + highA3 * y ^ 4 / 4

theorem logThreeCap_paid : log (3 : ℝ) ≤ logThreeCap := by
  have h1 := log_upper (by norm_num : (1 : ℝ) ≤ 4 / 3)
  have h2 := log_upper (by norm_num : (1 : ℝ) ≤ 3 / 2)
  rw [W11Credit.log_three_identity]
  unfold logThreeCap
  linarith only [h1, h2]

theorem delayed_density_upper {y : ℝ} (hy : 0 ≤ y) (hy1 : y ≤ 1) :
    wuLowerCoefficient (4 + y) / (4 + y) ≤ highDensity y := by
  have hl := lower_delayed_upper hy hy1
  have hu := log_three_cubic hy
  have hlog := logThreeCap_paid
  have h3 : 0 ≤ highA3 := by norm_num [highA3, logThreeCap, upperLog, lowerLog]
  apply (div_le_iff₀ (show 0 < 4 + y by linarith)).2
  have he : highDensity y * (4 + y) =
      logThreeCap + y / 3 - y ^ 2 / 18 + (13 / 324) * y ^ 3 + highA3 * y ^ 4 := by
    unfold highDensity highA0 highA1 highA2 highA3
    ring
  rw [he]
  nlinarith only [hl, hu, hlog, mul_nonneg h3 (pow_nonneg hy 4)]

theorem highIncrement_derivative (y : ℝ) :
    HasDerivAt highIncrement (highDensity y) y := by
  convert! ((((hasDerivAt_id y).const_mul highA0).add
    ((((hasDerivAt_id y).pow 2).const_mul highA1).div_const 2)).add
    ((((hasDerivAt_id y).pow 3).const_mul highA2).div_const 3)).add
    ((((hasDerivAt_id y).pow 4).const_mul highA3).div_const 4) using 1
  dsimp [highDensity]
  ring

theorem upper_delayed_high {v : ℝ} (hv : 5 ≤ v) (hv6 : v ≤ 6) :
    wuUpperCoefficient v ≤ upperFive + highIncrement (v - 5) := by
  have ho : (4 : ℝ) ≤ v - 1 := by linarith
  have hr := wuUpperCoefficient_sub_eq_integral (by norm_num : (2 : ℝ) ≤ 5) hv
  have hc : Continuous (fun x : ℝ => highDensity (x - 4)) := by
    unfold highDensity; fun_prop
  have hm := intervalIntegral.integral_mono_on ho
    (wuLowerCoefficient_div_intervalIntegrable (by norm_num) ho) (hc.intervalIntegrable _ _)
    (fun x hx => ?_)
  · have hd (x : ℝ) : HasDerivAt (fun x => highIncrement (x - 4)) (highDensity (x - 4)) x := by
      simpa using (highIncrement_derivative (x - 4)).comp x ((hasDerivAt_id x).sub_const 4)
    rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (fun x _ => hd x)
      (hc.intervalIntegrable _ _)] at hm
    norm_num only [show (5 : ℝ) - 1 = 4 by norm_num] at hr
    norm_num [highIncrement, show v - 1 - 4 = v - 5 by ring] at hm
    linarith only [hr, hm, upperFive_paid]
  have h := delayed_density_upper (show 0 ≤ x - 4 by linarith [hx.1])
    (show x - 4 ≤ 1 by linarith [hx.2])
  simpa only [add_sub_cancel] using h

def highSurplus (v : ℝ) : ℝ :=
  (9044059 / 6431250) * v / 5 - upperFive - highIncrement (v - 5)

theorem high_pointwise {v : ℝ} (hv : 5 ≤ v) (hvc : v ≤ 1127 / 200) :
    ExactWeightTripleEnclosure.highLo v + highSurplus v ≤
      (42823 / 151875) * v - wuUpperCoefficient v := by
  have h := upper_delayed_high hv (by linarith)
  unfold ExactWeightTripleEnclosure.highLo highSurplus
  linarith only [h]

def highGain : ℝ := ∫ t in a..c 5, SharedRationalEnvelope.weight t * highSurplus (u t)

theorem high_gain_paid :
    ExactWeightTripleEnclosure.highLower + highGain ≤ BaseGSharedActualRecovery.highKernel := by
  have ho : a ≤ c 5 := by norm_num [c, a, truncatedSixthLowerAlpha]
  have hs : c 5 ≤ s := by norm_num [c, a, s, truncatedSixthLowerAlpha, truncatedSixthLowerSigma]
  have hp : Continuous highSurplus := by unfold highSurplus highIncrement; fun_prop
  have hsum : Continuous (fun v => ExactWeightTripleEnclosure.highLo v + highSurplus v) :=
    (by unfold ExactWeightTripleEnclosure.highLo; fun_prop :
      Continuous ExactWeightTripleEnclosure.highLo).add hp
  have hi := JointSharedTightEnclosure.weighted_integrable _ hsum le_rfl hs ho
  have hk := BaseGSharedActualRecovery.kernel_integrable
    (fun v => (42823 / 151875) * v) le_rfl hs ho (by fun_prop)
  have hm := intervalIntegral.integral_mono_on ho hi hk (fun t ht => ?_)
  · have he : (∫ t in a..c 5, SharedRationalEnvelope.weight t *
        ExactWeightTripleEnclosure.highLo (u t)) = ExactWeightTripleEnclosure.highLower := by
      unfold ExactWeightTripleEnclosure.highLower
      rw [← ExactWeightTripleEnclosure.shifted_ftc _ _ _ _ _ _ _
        truncatedSixthLower_parameters.1 (by norm_num [c, a, truncatedSixthLowerAlpha]) ho]
      apply intervalIntegral.integral_congr
      intro t ht
      dsimp [ExactWeightTripleEnclosure.highLo, ExactWeightTripleEnclosure.shifted,
        ExactWeightTripleEnclosure.poly]
      ring
    simp_rw [mul_add] at hm
    rw [intervalIntegral.integral_add
      (JointSharedTightEnclosure.weighted_integrable _
        (by unfold ExactWeightTripleEnclosure.highLo; fun_prop) le_rfl hs ho)
      (JointSharedTightEnclosure.weighted_integrable _ hp le_rfl hs ho), he] at hm
    exact hm
  rw [HighSharedKernelMagnitude.kernel_density (fun v => (42823 / 151875) * v)]
  have hg := HighSharedKernelMagnitude.high_geometry ht
  exact mul_le_mul_of_nonneg_left (high_pointwise hg.2.2.1 hg.2.2.2)
    (by linarith only [(HighSharedKernelMagnitude.high_weight ht).1])

end WuTarget.E09JointMainMajor

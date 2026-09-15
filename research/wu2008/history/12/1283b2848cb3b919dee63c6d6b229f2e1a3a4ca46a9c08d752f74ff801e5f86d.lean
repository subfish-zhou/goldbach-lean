import W11CreditPayment

noncomputable section
open Real Set MeasureTheory Wu2008DoubleSieve
open scoped Interval

namespace WuTarget.E09JointMain
open FixedCoefficientUpperEnclosure (a s)
open FixedCoefficientHLowerEnclosure (c)
open Phase22 (u)

def jointGain : ℝ := 2 * a ^ 2 / 9

def surplusDensity (t : ℝ) : ℝ := (4 / 3) * a * (u t - 3) ^ 5

def lowDensity (t : ℝ) : ℝ := BaseSharedSlack.density t + surplusDensity t

theorem lowDensity_exact (t : ℝ) :
    lowDensity t = 16 * (8 - 24 * t) * (u t - 3) ^ 4 / 288 := by
  unfold lowDensity surplusDensity BaseSharedSlack.density BaseSharedSlack.rate u
  norm_num [a, s, truncatedSixthLowerAlpha, truncatedSixthLowerSigma]
  ring

theorem low_density_paid {t : ℝ} (ht : t ∈ Icc (c 4) s) :
    lowDensity t ≤ SharedRationalEnvelope.weight t *
      (SharedRationalEnvelope.p (u t) - wuUpperCoefficient (u t)) := by
  obtain ⟨ht0, hd, hu3, hu4⟩ := SharedRationalEnvelope.geometry ht
  have hs : 0 < 8 - 24 * s := by
    linarith [SharedRationalEnvelope.window_order.2.2]
  have hn : 0 ≤ 8 - 24 * t := by linarith [ht.2]
  have hden : t * (1 / 2 - t) ≤ 1 / 16 := by
    nlinarith [sq_nonneg (t - 1 / 4)]
  have hw : 16 * (8 - 24 * t) ≤ SharedRationalEnvelope.weight t := by
    apply (le_div_iff₀ (mul_pos ht0 hd)).2
    nlinarith only [mul_nonneg hn (sub_nonneg.mpr hden)]
  have hp := BaseSharedSlack.low_pointwise_gain hu3 hu4
  have hm := mul_le_mul hw hp (by positivity : 0 ≤ (u t - 3) ^ 4 / 288)
    (by linarith : 0 ≤ SharedRationalEnvelope.weight t)
  rw [lowDensity_exact]
  linarith only [hm]

theorem surplus_ftc :
    (∫ t in c 4..s, surplusDensity t) = jointGain := by
  have hc : Continuous surplusDensity := by unfold surplusDensity u; fun_prop
  have hd (t : ℝ) : HasDerivAt
      (fun t => -(2 / 9) * a ^ 2 * (u t - 3) ^ 6) (surplusDensity t) t := by
    convert (((((hasDerivAt_const t (1 / 2 : ℝ)).sub (hasDerivAt_id t)).div_const a).
      sub_const 3).pow 6 |>.const_mul (-(2 / 9) * a ^ 2)) using 1 <;>
      first | rfl | (dsimp [surplusDensity, u];
        field_simp [truncatedSixthLower_parameters.1.ne']; ring)
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun t _ => hd t) (hc.intervalIntegrable _ _)]
  have h4 : u (c 4) = 4 := by norm_num [u, a, c, truncatedSixthLowerAlpha]
  have h3 : u s = 3 := by
    norm_num [u, a, s, truncatedSixthLowerAlpha, truncatedSixthLowerSigma]
  rw [h4, h3]
  unfold jointGain
  ring

theorem low_ftc :
    (∫ t in c 4..s, lowDensity t) = BaseSharedSlack.lowGain + jointGain := by
  have hc : Continuous BaseSharedSlack.density := by
    unfold BaseSharedSlack.density u; fun_prop
  have hd : Continuous surplusDensity := by unfold surplusDensity u; fun_prop
  unfold lowDensity
  rw [intervalIntegral.integral_add (hc.intervalIntegrable _ _)
    (hd.intervalIntegrable _ _), BaseSharedSlack.lowGain_ftc, surplus_ftc]

theorem low_gain_paid :
    BaseSharedSlack.lowGain + jointGain ≤ BaseGSharedActualRecovery.lowKernel := by
  have ho := SharedRationalEnvelope.window_order
  have hU : ContinuousOn (fun t => wuUpperCoefficient (u t)) (Icc (c 4) s) := by
    apply continuousOn_wuUpperCoefficient.comp (by unfold u; fun_prop)
    intro t ht
    change 0 < u t
    linarith [(SharedRationalEnvelope.geometry ht).2.2.1]
  have hw : ContinuousOn SharedRationalEnvelope.weight (Icc (c 4) s) := by
    unfold SharedRationalEnvelope.weight
    apply ContinuousOn.div (by fun_prop) (by fun_prop)
    intro t ht
    exact mul_ne_zero (SharedRationalEnvelope.geometry ht).1.ne'
      (SharedRationalEnvelope.geometry ht).2.1.ne'
  have hi := (hw.mul (SharedRationalEnvelope.p_continuous.sub hU)).
    intervalIntegrable_of_Icc (μ := volume) ho.2.1
  have hd : Continuous lowDensity := by
    unfold lowDensity BaseSharedSlack.density surplusDensity u; fun_prop
  have hm := intervalIntegral.integral_mono_on ho.2.1
    (hd.intervalIntegrable _ _) hi (fun t ht => low_density_paid ht)
  rw [low_ftc] at hm
  rw [BaseGSharedActualRecovery.low_explicit]
  exact hm

theorem jointGain_exact : jointGain = (20000 / 15848361 : ℝ) := by
  norm_num [jointGain, a, truncatedSixthLowerAlpha]

theorem jointGain_pos : 0 < jointGain := by rw [jointGain_exact]; norm_num

theorem shared_recovery_paid :
    W11.sharedRecovery + jointGain ≤ AnalyticTotalThreshold.sharedLoss := by
  have hw := ExactWeightTripleEnclosure.window_payments
  have hl := low_gain_paid
  rw [BaseGSharedActualRecovery.shared_exact]
  unfold W11.sharedRecovery
  linarith only [hw.1, hw.2.2.1, hl]

theorem correlated_gain_le_actual :
    W11.correlatedCredit + jointGain ≤
      3 * Wu08TerminalAlignment.firstMain -
        Wu08TerminalAlignment.thirdMain - Wu08TerminalAlignment.fourthMain := by
  have h := shared_recovery_paid
  unfold AnalyticTotalThreshold.sharedLoss at h
  rw [← Wu08TerminalAlignment.first_exact]
  unfold W11.correlatedCredit Wu08TerminalAlignment.thirdMain
    Wu08TerminalAlignment.fourthMain
  change W11.sharedRecovery + jointGain ≤
    24 * wuLowerCoefficient (1 / (2 * truncatedSixthLowerAlpha)) -
      (SingleUpperClassicalLimit.Glin (1 / 3) +
        SingleUpperClassicalLimit.Glin truncatedSixthLowerSigma) -
      (24 * Phase23.alphaModel - Phase23.gModel +
        SharedRationalEnvelope.deltaShared) at h
  linarith only [h]

end WuTarget.E09JointMain

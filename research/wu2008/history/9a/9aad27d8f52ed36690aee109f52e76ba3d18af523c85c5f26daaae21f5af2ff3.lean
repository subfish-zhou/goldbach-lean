import W14FifthGainV3

namespace WuTarget.E07Fifth
open Real Set MeasureTheory Wu2008DoubleSieve SharpMassBalance
open scoped Interval
noncomputable section

def profileBase : ℝ := 11/2 - FifthClassicalShape.q

def profileY (y : ℝ) : ℝ := (profileBase + (y-a)/a)^3/70875

def polynomialMinorant (v : ℝ × ℝ) : ℝ :=
  fifthPairRegion.indicator (fun v => profileY v.2 / W14.fifthDenominator) v

def polynomialPrimitive (y : ℝ) : ℝ :=
  (profileBase^3*(y-a)^2/2 + profileBase^2*(y-a)^3/a +
    3*profileBase*(y-a)^4/(4*a^2) + (y-a)^5/(5*a^3)) /
      (70875*W14.fifthDenominator)

def netCredit : ℝ := 87760644803325371/14970763715034960000000

theorem capped_parameter_upper {v : ℝ × ℝ} (hv : v ∈ fifthPairRegion) :
    max 4 (truncatedSixthLowerS 0 v.1 v.2) ≤
      FifthClassicalShape.q - (v.2-a)/a := by
  have ha : 0 < a := truncatedSixthLower_parameters.1
  have hy := div_le_div_of_nonneg_right
    (show v.2-a ≤ b-a by linarith [hv.2.2]) ha.le
  have h4 : 4 ≤ FifthClassicalShape.q - (b-a)/a := by
    norm_num [FifthClassicalShape.q, a, b, truncatedSixthLowerAlpha,
      truncatedSixthLowerBeta]
  refine max_le (by linarith only [hy, h4]) ?_
  dsimp only [truncatedSixthLowerS, truncatedSixthLowerC, sub_zero]
  change (1/2-v.1-v.2)/a ≤ FifthClassicalShape.q - (v.2-a)/a
  dsimp only [FifthClassicalShape.q]
  rw [← sub_div]
  apply div_le_div_of_nonneg_right _ ha.le
  linarith [hv.1]

theorem profileY_nonneg {y : ℝ} (hy : a ≤ y) : 0 ≤ profileY y := by
  have hA : 0 ≤ profileBase := by
    norm_num [profileBase, FifthClassicalShape.q, a, truncatedSixthLowerAlpha]
  have ht : 0 ≤ (y-a)/a :=
    div_nonneg (sub_nonneg.mpr hy) truncatedSixthLower_parameters.1.le
  exact div_nonneg (pow_nonneg (add_nonneg hA ht) _) (by norm_num)

theorem profileY_lower {v : ℝ × ℝ} (hv : v ∈ fifthPairRegion) :
    profileY v.2 ≤ PositiveCoreResume.fifthProfile v := by
  have hA : 0 ≤ profileBase := by
    norm_num [profileBase, FifthClassicalShape.q, a, truncatedSixthLowerAlpha]
  have ht : 0 ≤ (v.2-a)/a := div_nonneg
    (sub_nonneg.mpr (hv.1.trans hv.2.1)) truncatedSixthLower_parameters.1.le
  have hp := pow_le_pow_left₀ (add_nonneg hA ht)
    (show profileBase + (v.2-a)/a ≤
      11/2-max 4 (truncatedSixthLowerS 0 v.1 v.2) by
        dsimp only [profileBase]
        linarith only [capped_parameter_upper hv]) 3
  exact div_le_div_of_nonneg_right hp (by norm_num)

theorem polynomial_integrable : Integrable polynomialMinorant := by
  have hc : Continuous (fun v : ℝ × ℝ => profileY v.2 / W14.fifthDenominator) := by
    unfold profileY
    fun_prop
  exact (hc.continuousOn.integrableOn_compact fifthPair_region_compact).integrable_indicator
    fifthPair_region_compact.measurableSet

theorem polynomial_le_original (v : ℝ × ℝ) :
    polynomialMinorant v ≤ PositiveCoreResume.fifthMinorant v := by
  by_cases hv : v ∈ fifthPairRegion
  · rw [polynomialMinorant, indicator_of_mem hv,
      PositiveCoreResume.fifthMinorant, indicator_of_mem hv]
    have hb := fifthPair_region_bounds (δ := 0) le_rfl (by norm_num) hv
    have hd : 0 < v.1*v.2*(truncatedSixthLowerC 0-v.1-v.2) :=
      mul_pos (mul_pos hb.1 hb.2.1)
        (by linarith [hb.2.2.1, truncatedSixthLower_parameters.1])
    exact (div_le_div_of_nonneg_left (profileY_nonneg (hv.1.trans hv.2.1)) hd
      (W14.fifth_denominator_upper hv)).trans
        (div_le_div_of_nonneg_right (profileY_lower hv) hd.le)
  · simp [polynomialMinorant, PositiveCoreResume.fifthMinorant, hv]

theorem polynomial_derivative (y : ℝ) :
    HasDerivAt polynomialPrimitive
      ((y-a)*(profileY y/W14.fifthDenominator)) y := by
  have ht := (hasDerivAt_id y).sub_const a
  have hd := (((((ht.pow 2).const_mul (profileBase^3)).div_const 2).add
    (((ht.pow 3).const_mul (profileBase^2)).div_const a)).add
    (((ht.pow 4).const_mul (3*profileBase)).div_const (4*a^2))).add
    ((ht.pow 5).div_const (5*a^3))
  convert hd.div_const (70875*W14.fifthDenominator) using 1 <;>
    first | rfl | (dsimp only [profileY]; field_simp; ring)

theorem polynomial_integral :
    (∫ v : ℝ × ℝ, polynomialMinorant v) = polynomialPrimitive b := by
  rw [fifthH_triangle_integral polynomial_integrable (by
    intro v hv
    by_contra hn
    exact hv (indicator_of_notMem hn _))]
  have he : (∫ y in a..b, ∫ x in a..y, polynomialMinorant (x,y)) =
      ∫ y in a..b, (y-a)*(profileY y/W14.fifthDenominator) := by
    apply intervalIntegral.integral_congr
    intro y hy
    rw [uIcc_of_le truncatedSixthLower_parameters.2.1.le] at hy
    have hi : (∫ x in a..y, polynomialMinorant (x,y)) =
        ∫ _x in a..y, profileY y/W14.fifthDenominator := by
      apply intervalIntegral.integral_congr
      intro x hx
      rw [uIcc_of_le hy.1] at hx
      exact indicator_of_mem (show (x,y) ∈ fifthPairRegion from
        ⟨hx.1, hx.2, hy.2⟩) _
    rw [hi, intervalIntegral.integral_const, smul_eq_mul]
  change (∫ y in a..b, ∫ x in a..y, polynomialMinorant (x,y)) = _
  rw [he]
  have hi : IntervalIntegrable (fun y => (y-a)*(profileY y/W14.fifthDenominator))
      volume a b := by
    apply Continuous.intervalIntegrable
    unfold profileY
    fun_prop
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun y _ => polynomial_derivative y) hi]
  simp [polynomialPrimitive]

theorem polynomial_gain_lower :
    4*polynomialPrimitive b ≤ PositiveCoreResume.fifthGain := by
  have hi := integral_mono polynomial_integrable PositiveCoreResume.minorant_integrable
    polynomial_le_original
  rw [polynomial_integral] at hi
  exact mul_le_mul_of_nonneg_left hi (by norm_num)

theorem polynomial_gain_exact :
    4*polynomialPrimitive b = 9445012770325413487/280701819656905500000000 := by
  norm_num [polynomialPrimitive, profileBase, W14.fifthDenominator,
    FifthClassicalShape.q, a, b, truncatedSixthLowerAlpha, truncatedSixthLowerBeta]

theorem net_identity :
    polynomialPrimitive b - W14.fifthGainLower/4 = netCredit := by
  have hg := polynomial_gain_exact
  have hf := W14.fifth_gain_lower_exact
  unfold netCredit
  linarith only [hg, hf]

theorem netCredit_pos : 0 < netCredit := by norm_num [netCredit]

theorem fifth_balance_lower :
    netCredit ≤ (PositiveCoreResume.fifthGain-W14.fifthGainLower)/4 := by
  have hg := polynomial_gain_lower
  rw [← net_identity]
  linarith only [hg]

end
end WuTarget.E07Fifth

import MathlibNt.Wu2008DoubleSieve.BaseRecurrencePrimitives

namespace Wu2008DoubleSieve.BaseRecurrenceLower
open Real Set MeasureTheory ClassicalAnalyticLeaves SharpLogRecurrence
open scoped Interval

noncomputable def newBase : ℝ :=
  17802218270055394229441432/332478382709785244428125
noncomputable def baseGain : ℝ :=
  233560459810704852486281/1329913530839140977712500

/-- All logarithmic coefficients in the two affine increments are positive. -/
theorem affine_log_coefficients_pos :
    (0 : ℝ) < 34832/30375-4*(56/243) ∧ 0 < 340/243-5*(2776/10125) := by
  norm_num

/-- Rational payment is made only after the actual recurrence and FTC. -/
theorem base_recurrence_lower :
    newBase ≤ 24*wuLowerCoefficient (1/(2*truncatedSixthLowerAlpha))+
      8*wuLowerCoefficient (1/(2*truncatedSixthLowerBeta)) := by
  have ha := alpha_real_lower
  have hb := beta_real_lower
  rw [Q_difference (by norm_num) (by norm_num),
    P_difference 4 (34832/30375) (56/243) (by norm_num) (by norm_num),
    P_difference 5 (340/243) (2776/10125) (by norm_num) (by norm_num)] at ha
  rw [Q_difference (by norm_num) (by norm_num)] at hb
  have hl3 := log_three_bounds.1
  have hl43 := log_lower (by norm_num : (1 : ℝ) ≤ 4/3)
  have hl54 := log_lower (by norm_num : (1 : ℝ) ≤ 5/4)
  have hlr5 := log_lower (by norm_num : (1 : ℝ) ≤ (1127/200)/5)
  have hlb3 := log_lower (by norm_num : (1 : ℝ) ≤ (78/25)/3)
  norm_num [lowerLog,newBase] at hl43 hl54 hlr5 hlb3 ha hb ⊢
  linarith

theorem exact_base_gain : newBase-54035471/1012500 = baseGain := by
  norm_num [newBase,baseGain]

theorem base_gain_pos : 0 < baseGain := by norm_num [baseGain]

theorem base_strictly_improved : (54035471/1012500 : ℝ) < newBase := by
  linarith [exact_base_gain,base_gain_pos]

noncomputable def newBalance : ℝ :=
  newBase+3/2+RationalMovingSixth.rationalSixth+47/481250-
    VariableCoefficientBalance.rationalG-12-21/20

theorem exact_balance_gain :
    newBalance = RationalMovingSixth.balance+baseGain := by
  unfold newBalance RationalMovingSixth.balance
  linarith [exact_base_gain]

/-- Termwise reassembly of the SAME full coefficient, using UPPER negative payments. -/
theorem complete_coefficient_gt_newBalance :
    newBalance < TruncatedElevenClassicalCountLower.classicalCoefficient := by
  have hb := base_recurrence_lower
  have hg := VariableCoefficientBalance.full_G_rational
  have hj := SharpJBalance.weighted_J_lt_twelve
  have h4 := SharpMassBalance.four_weighted_lt_21_twentieths
  have hp := SharpMassBalance.fifth_gt_three_halves
  have hq := RationalMovingSixth.actual_sixth_ge_rational
  change SingleUpperClassicalLimit.Glin (1/3)+
    SingleUpperClassicalLimit.Glin truncatedSixthLowerSigma ≤ VariableCoefficientBalance.rationalG at hg
  unfold TruncatedElevenClassicalCountLower.classicalCoefficient newBalance
  linarith

#print axioms base_recurrence_lower
#print axioms exact_balance_gain
#print axioms complete_coefficient_gt_newBalance
end Wu2008DoubleSieve.BaseRecurrenceLower

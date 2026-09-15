import WE06SecondAnalytic

noncomputable section
namespace WuTarget.E06Second
open Wu08OriginalFirstSteps

theorem second_credit_positive : (0:ℝ) < 3/36517 := by norm_num

theorem second_remainder_nonneg : (0:ℝ) ≤ 2*C (103/25)-3/36517 := by
  linarith only [second_slack_lower]

theorem recurrence_normalization :
    (W14.secondLower+8*C (103/25)-W14.secondLower)/4 = 2*C (103/25) := by
  ring

theorem second_main_unpaid_lower :
    (3/36517 : ℝ) ≤ (Wu08TerminalAlignment.secondMain-W14.secondLower)/4 := by
  linarith only [W14.second_lower_with_recurrence, second_slack_lower]

theorem second_main_normalized_lower :
    W14.secondLower/4 + (3/36517 : ℝ) ≤ Wu08TerminalAlignment.secondMain/4 := by
  linarith only [second_main_unpaid_lower]

theorem retained_slack_split :
    W14Accepted.retainedSlack =
      (3/36517 : ℝ) + (2*C (103/25)-3/36517) +
        (PositiveCoreResume.fifthGain-W14.fifthGainLower)/4 := by
  unfold W14Accepted.retainedSlack
  ring

theorem retained_slack_net_identity :
    W14Accepted.retainedSlack -
      (PositiveCoreResume.fifthGain-W14.fifthGainLower)/4 = 2*C (103/25) := by
  unfold W14Accepted.retainedSlack
  ring

theorem retained_slack_lower_with_fifth_unchanged :
    (3/36517 : ℝ) + (PositiveCoreResume.fifthGain-W14.fifthGainLower)/4 ≤
      W14Accepted.retainedSlack := by
  unfold W14Accepted.retainedSlack
  linarith only [second_slack_lower]

theorem retained_slack_lower : (3/36517 : ℝ) ≤ W14Accepted.retainedSlack := by
  linarith only [retained_slack_lower_with_fifth_unchanged, W14.fifth_gain_lower]

theorem retained_slack_strict : (1/12500 : ℝ) < W14Accepted.retainedSlack := by
  exact lt_of_lt_of_le (by norm_num) retained_slack_lower

#check @kernel_lower
#check @inner_lower
#check @outer_kernel_lower
#check @C_lower
#check @original_double_integral
#check @double_integral_lower
#check @second_slack_lower
#check @second_slack_strict
#check @second_credit_positive
#check @second_remainder_nonneg
#check @W14.second_lower_with_recurrence
#check @recurrence_normalization
#check @second_main_unpaid_lower
#check @second_main_normalized_lower
#check @retained_slack_split
#check @retained_slack_net_identity
#check @retained_slack_lower_with_fifth_unchanged
#check @retained_slack_lower
#check @retained_slack_strict

#print axioms kernel_lower
#print axioms inner_lower
#print axioms outer_kernel_lower
#print axioms C_lower
#print axioms original_double_integral
#print axioms double_integral_lower
#print axioms second_slack_lower
#print axioms second_slack_strict
#print axioms second_credit_positive
#print axioms second_remainder_nonneg
#print axioms W14.second_lower_with_recurrence
#print axioms recurrence_normalization
#print axioms second_main_unpaid_lower
#print axioms second_main_normalized_lower
#print axioms retained_slack_split
#print axioms retained_slack_net_identity
#print axioms retained_slack_lower_with_fifth_unchanged
#print axioms retained_slack_lower
#print axioms retained_slack_strict

end WuTarget.E06Second

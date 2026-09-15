import WE09JointMainBudget

noncomputable section
namespace WuTarget.E09JointMain

theorem actual_rational_payment :
    (83078419629618575238304346189387006860549400910521240176775087 : ℝ) /
        61155381611119450770290424186958629545268860216769067968750000 ≤
      3 * Wu08TerminalAlignment.firstMain -
        Wu08TerminalAlignment.thirdMain - Wu08TerminalAlignment.fourthMain := by
  rw [← payment_exact]
  exact payment_le_actual

theorem actual_coefficient_gain :
    W17Accepted.paidCoefficient + (5000 / 15848361 : ℝ) <
      W01.ordinaryCoefficient W17Accepted.enhanced := by
  rw [← netGain_exact]
  exact paid_lt_actual

set_option pp.fullNames true

#print jointGain
#print surplusDensity
#print lowDensity
#print payment
#print netGain
#print selectedCredit
#print paidCoefficient
#print remainingCoefficient

#check lowDensity_exact
#print axioms lowDensity_exact
#check low_density_paid
#print axioms low_density_paid
#check surplus_ftc
#print axioms surplus_ftc
#check low_ftc
#print axioms low_ftc
#check low_gain_paid
#print axioms low_gain_paid
#check jointGain_exact
#print axioms jointGain_exact
#check jointGain_pos
#print axioms jointGain_pos
#check shared_recovery_paid
#print axioms shared_recovery_paid
#check correlated_gain_le_actual
#print axioms correlated_gain_le_actual
#check payment_exact
#print axioms payment_exact
#check netGain_exact
#print axioms netGain_exact
#check netGain_pos
#print axioms netGain_pos
#check payment_net
#print axioms payment_net
#check payment_strict
#print axioms payment_strict
#check payment_le_actual
#print axioms payment_le_actual
#check actual_normalized_payment
#print axioms actual_normalized_payment
#check correlated_remaining_exact
#print axioms correlated_remaining_exact
#check payment_remaining_exact
#print axioms payment_remaining_exact
#check selectedCredit_le_actual
#print axioms selectedCredit_le_actual
#check previous_selected_le
#print axioms previous_selected_le
#check payment_le_selected
#print axioms payment_le_selected
#check first_lower_transport
#print axioms first_lower_transport
#check shifted_w11_le_actual_core
#print axioms shifted_w11_le_actual_core
#check shifted_w13_lt_actual
#print axioms shifted_w13_lt_actual
#check paid_net
#print axioms paid_net
#check remaining_net
#print axioms remaining_net
#check paid_strict
#print axioms paid_strict
#check paid_lt_actual
#print axioms paid_lt_actual
#check paid_exact
#print axioms paid_exact
#check ordinary_P2_paid
#print axioms ordinary_P2_paid
#check paid_threshold_iff
#print axioms paid_threshold_iff
#check old_remaining_threshold_iff
#print axioms old_remaining_threshold_iff
#check refined_target
#print axioms refined_target
#check actual_rational_payment
#print axioms actual_rational_payment
#check actual_coefficient_gain
#print axioms actual_coefficient_gain

end WuTarget.E09JointMain

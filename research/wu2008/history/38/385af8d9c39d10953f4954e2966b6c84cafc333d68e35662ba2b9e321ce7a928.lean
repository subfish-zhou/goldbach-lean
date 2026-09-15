import WE05SixthRational
import Wu08TerminalAlignment

noncomputable section
open Wu2008DoubleSieve
open Wu08TerminalAlignment

namespace WuTarget.E05Sixth

theorem fixed_parameters :
    truncatedSixthLowerAlpha = (100/1327:ℝ) ∧
    truncatedSixthLowerBeta = (25/206:ℝ) := ⟨rfl,rfl⟩

theorem old_certificate_reused : Phase25.newSixth ≤ sixthMain :=
  Phase25.actual_sixth_ge_new

theorem actual_sixth_lower : sixthLower ≤ sixthMain :=
  newSixth_add_credit_le_actual

theorem actual_new_income :
    Phase25.newSixth+
      (8066984221372818175051714346501/852403217090079068048245351272000:ℝ) ≤
        Wu08TerminalAlignment.sixthMain := by
  rw [← sixthCredit_exact]
  exact newSixth_add_credit_le_actual

theorem actual_rational_floor :
    (3783117/1000000:ℝ) ≤ Wu08TerminalAlignment.sixthMain :=
  sixthLower_bounds.1.trans actual_sixth_lower

theorem actual_sixth_remainder_nonnegative : 0 ≤ sixthMain-sixthLower :=
  sub_nonneg.mpr actual_sixth_lower

theorem sixth_net_identity :
    (sixthMain-Phase25.newSixth)/4 =
      ordinaryCredit+(sixthMain-sixthLower)/4 := by
  rw [ordinaryCredit_eq]
  unfold sixthLower
  ring

def coefficientWithSixth (q : ℝ) : ℝ :=
  (3*firstMain+secondMain-thirdMain-fourthMain+fifthMain+q-
    2*seventhMain-eighthMain-ninthMain-tenthCurrent-eleventhCurrent+
    8*PositiveSecondPayment.secondGain+PositiveCoreResume.fifthGain+
    FeedbackLimit.Cinf+4*Phase20.rawPsi+4*Phase18.g18)/4

theorem full_terminal_identity :
    coefficientWithSixth sixthMain = PositiveTwoPayment.Qtwo :=
  Qtwo_terminal_exact.symm

theorem full_terminal_lower :
    coefficientWithSixth sixthLower ≤ PositiveTwoPayment.Qtwo := by
  rw [← full_terminal_identity]
  unfold coefficientWithSixth
  linarith only [actual_sixth_lower]

theorem full_terminal_net_identity :
    coefficientWithSixth sixthLower-coefficientWithSixth Phase25.newSixth =
      8066984221372818175051714346501/3409612868360316272192981405088000 := by
  change _ = ordinaryCredit
  rw [ordinaryCredit_eq]
  unfold coefficientWithSixth sixthLower
  ring

theorem full_terminal_new_income :
    coefficientWithSixth Phase25.newSixth+
      (8066984221372818175051714346501/3409612868360316272192981405088000:ℝ) ≤
        PositiveTwoPayment.Qtwo := by
  linarith only [full_terminal_lower,full_terminal_net_identity]

theorem recurrence_unspent :
    0 ≤ sixthMain-ClassicalLossBottleneck.sixthLogIntegral ∧
    sixthMain-ClassicalLossBottleneck.sixthLogIntegral < (1/100000:ℝ) :=
  ClassicalLossBottleneck.sixth_recurrence_integral_cap

#check fixed_parameters
#check old_certificate_reused
#check sixthCredit_exact
#check sixthLower_exact
#check baseline_strictly_preserved
#check newSixth_add_credit_le_log
#check actual_new_income
#check actual_rational_floor
#check actual_sixth_remainder_nonnegative
#check sixth_net_identity
#check ordinaryCredit_bounds
#check full_terminal_identity
#check full_terminal_lower
#check full_terminal_net_identity
#check full_terminal_new_income
#check recurrence_unspent

#print axioms old_certificate_reused
#print axioms sixthCredit_exact
#print axioms sixthLower_exact
#print axioms baseline_strictly_preserved
#print axioms newSixth_add_credit_le_log
#print axioms actual_new_income
#print axioms actual_rational_floor
#print axioms actual_sixth_remainder_nonnegative
#print axioms sixth_net_identity
#print axioms full_terminal_identity
#print axioms full_terminal_lower
#print axioms full_terminal_net_identity
#print axioms full_terminal_new_income
#print axioms recurrence_unspent

end WuTarget.E05Sixth

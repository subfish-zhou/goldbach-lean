import MathlibNt.Wu2008DoubleSieve.MotherPairGamma5FeedbackPaid
import MathlibNt.Wu2008DoubleSieve.MotherPairFullFeedbackIntegrals
import MathlibNt.Wu2008DoubleSieve.MotherPairGamma5Paid
import MathlibNt.Wu2008DoubleSieve.Gamma5AllRowsLossBudget
import MathlibNt.Wu2004MeanValue.GammaFiveSectionBudget
import MathlibNt.Wu2004MeanValue.GammaFiveTriangleLog
import MathlibNt.Wu2004MeanValue.RefinementLossBudget
import WR2Gamma5Original
import MathlibNt.Wu2008DoubleSieve.FourthRowGamma5Paid
import MathlibNt.Wu2004MeanValue.GammaFiveLossBudgetMeasurable
import MathlibNt.Wu2008DoubleSieve.Gamma5FeedbackLossBudget

namespace WuPaper.R2Gamma5

run_cmd do
  for (name, _) in (← Lean.getEnv).constants.toList do
    if name.getPrefix == `WuPaper.R2Gamma5 then
      Lean.Elab.Command.elabCommand (← `(#check @$(Lean.mkIdent name)))
      Lean.Elab.Command.elabCommand (← `(#print axioms $(Lean.mkIdent name)))

end WuPaper.R2Gamma5

#print axioms Wu2008DoubleSieve.gamma5Feedback_actual_loss_lt
#print axioms Wu2008DoubleSieve.gamma5Feedback_full_gain_sub_legal_lt

#print axioms Wu2008DoubleSieve.gamma5Feedback_full_count_upper_paid

#print axioms Wu2008DoubleSieve.fourthRowGamma5Link_full_gain_paid
#print axioms Wu2004MeanValue.GammaFiveLossBudget.original_row_budget_of_measurable

#print axioms Wu2004MeanValue.GammaFiveLossBudget.original_row_triangle_budget

#print axioms Wu2004MeanValue.GammaFiveLossBudget.original_row_full_sub_legal_budget
#print axioms Wu2004MeanValue.GammaFiveLossBudget.triangle_literal_transport
#print axioms Wu2004MeanValue.GammaFiveLossBudget.masked_section_integral
#print axioms LiLiuPrereqBuchstab.roughCount_uniform_buchstab_fixed

#print axioms Wu2008DoubleSieve.gamma5_row_triangle_unclip
#print axioms Wu2008DoubleSieve.gamma5_original_row_loss_lt
#print axioms Wu2008DoubleSieve.gamma5_original_row_normalized_loss_lt

#print axioms Wu2008DoubleSieve.MotherPair.gamma5_original_row_count_upper_paid
#print axioms Wu2008DoubleSieve.MotherPair.gamma5_original_row_full_sub_legal_lt

#print axioms Wu2008DoubleSieve.MotherPair.gamma5_full_gain_original_integral
#print axioms Wu2008DoubleSieve.MotherPair.fullH_gammaSix_original_integral
#print axioms Wu2008DoubleSieve.MotherPair.fullH_gammaSevenEight_original_integral

#print axioms Wu2008DoubleSieve.SecondFunctionalCoupled.gamma5_paid_actual_limit

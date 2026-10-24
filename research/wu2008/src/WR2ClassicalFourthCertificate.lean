import WR2ClassicalFourthConcrete
import WR2ClassicalFourthAllLog
import WR2ClassicalFourthAllBPay
import WR2ClassicalFourthAllCPay
import WR2ClassicalFourthAllDPay
import WR2ClassicalFourthAllouterPay
import WR2ClassicalFourthAllOuterPoint

noncomputable section
namespace WuPaper.ClassicalFourthConditions

/-- The original fourth slot, with every finite numerical condition discharged. -/
theorem fourth_main_upper : Wu08TerminalAlignment.fourthMain ≤ (1964373:ℝ)/100000 :=
  fourth_upper_of_certificates all_Log all_BPay all_CPay all_DPay all_outerPay all_OuterPoint

end WuPaper.ClassicalFourthConditions
#print axioms WuPaper.ClassicalFourthConditions.fourth_main_upper

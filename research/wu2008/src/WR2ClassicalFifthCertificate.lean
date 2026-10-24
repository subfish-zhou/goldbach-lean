import WR2ClassicalFifthInitialRoot
import WR2ClassicalFifthMiddleRoot
import WR2ClassicalFifthTerminalRoot
noncomputable section
namespace WuPaper.ClassicalFifthRational

theorem fifth_main_lower : (165533:ℝ)/100000 ≤ Wu08TerminalAlignment.fifthMain :=
  ClassicalFifthAssembly.fifth_lower_of_payments initialPayment middlePayment terminalPayment
    all_initial_paid all_middle_paid all_terminal_paid initial_total middle_total terminal_total

end WuPaper.ClassicalFifthRational
#print axioms WuPaper.ClassicalFifthRational.fifth_main_lower

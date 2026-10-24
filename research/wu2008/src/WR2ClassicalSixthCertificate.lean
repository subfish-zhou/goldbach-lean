import WR2ClassicalSixthLowerRoot
import WR2ClassicalSixthUpperRoot
noncomputable section
namespace WuPaper.ClassicalSixthRational

theorem sixth_main_lower : (381909:ℝ)/100000 ≤ Wu08TerminalAlignment.sixthMain :=
  ClassicalSixthAssembly.sixth_lower_of_payments lowerPayment upperPayment
    all_lower_paid all_upper_paid lower_total upper_total

end WuPaper.ClassicalSixthRational
#print axioms WuPaper.ClassicalSixthRational.sixth_main_lower

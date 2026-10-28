import WR2ClassicalCIntegerSoundness
import WR2ClassicalCPayments
import WR2ClassicalFirstBudget
noncomputable section
namespace WuPaper.ClassicalC
open Finset

theorem all_midpoints_paid (i : ℕ) (hi : i < 4096) : cPayment (i) ≤ lowerKernel 1 (1327/200)
    ((point (1327/200) 4096 (i)+point (1327/200) 4096 ((i)+1))/2) :=
  CIntegerPayment.integer_paid_real hi

theorem first_C_lower : (1336108:ℝ)/10000000 ≤ Wu08OriginalFirstSteps.C (1327/200) :=
  cPayment_total.trans (uniform_lower (by norm_num) (by norm_num) 1 4096
    (by norm_num) cPayment all_midpoints_paid)

theorem first_main_lower : (1490088:ℝ)/100000 ≤ Wu08TerminalAlignment.firstMain :=
  ClassicalFirst.first_lower_of_C first_C_lower

end WuPaper.ClassicalC
#print axioms WuPaper.ClassicalC.first_C_lower
#print axioms WuPaper.ClassicalC.first_main_lower

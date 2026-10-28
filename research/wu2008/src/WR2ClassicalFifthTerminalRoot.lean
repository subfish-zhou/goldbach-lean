import WR2ClassicalFifthTerminalPayments
import WR2ClassicalFifthIntegerSoundness
noncomputable section
namespace WuPaper.ClassicalFifthRational
open ClassicalFifthSource ClassicalUniformMidpoint
set_option maxHeartbeats 4000000 in
theorem all_terminal_paid (i : ℕ) (hindex : i < 1024) : terminalPayment i ≤
    terminalValue ((point cut hi 1024 i+point cut hi 1024 (i+1))/2) := by
  simpa only [terminalPayment, terminalNumerator] using
    FifthIntegerPayment.terminal_payment_sound hindex
end WuPaper.ClassicalFifthRational
#print axioms WuPaper.ClassicalFifthRational.all_terminal_paid

import WR2ClassicalFifthInitialPayments
import WR2ClassicalFifthIntegerSoundness
noncomputable section
namespace WuPaper.ClassicalFifthRational
open ClassicalFifthSource ClassicalUniformMidpoint
set_option maxHeartbeats 4000000 in
theorem all_initial_paid (i : ℕ) (hindex : i < 1024) : initialPayment i ≤
    initialValue ((point lo 4 1024 i+point lo 4 1024 (i+1))/2) := by
  simpa only [initialPayment, initialNumerator] using
    FifthIntegerPayment.initial_payment_sound hindex
end WuPaper.ClassicalFifthRational
#print axioms WuPaper.ClassicalFifthRational.all_initial_paid

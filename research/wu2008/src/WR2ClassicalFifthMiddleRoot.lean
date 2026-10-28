import WR2ClassicalFifthMiddlePayments
import WR2ClassicalFifthIntegerSoundness
noncomputable section
namespace WuPaper.ClassicalFifthRational
open ClassicalFifthSource ClassicalUniformMidpoint
set_option maxHeartbeats 4000000 in
theorem all_middle_paid (i : ℕ) (hindex : i < 1024) : middlePayment i ≤
    middleValue ((point 4 cut 1024 i+point 4 cut 1024 (i+1))/2) := by
  simpa only [middlePayment, middleNumerator] using
    FifthIntegerPayment.middle_payment_sound hindex
end WuPaper.ClassicalFifthRational
#print axioms WuPaper.ClassicalFifthRational.all_middle_paid

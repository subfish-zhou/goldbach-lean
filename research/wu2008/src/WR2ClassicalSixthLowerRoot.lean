import WR2ClassicalSixthLowerPayments
import WR2ClassicalSixthIntegerSoundness
namespace WuPaper.ClassicalSixthRational
open WuSource.SrcSixthGain ClassicalSixthQuadrature

theorem all_lower_paid (i : ℕ) (hindex : i < 4096) : lowerPayment i ≤
    lowerValue ((point 2 split 4096 i+point 2 split 4096 (i+1))/2) :=
  ClassicalSixthTableCheck.lowerCondition_sound (SixthIntegerPayment.lower_paid hindex)

end WuPaper.ClassicalSixthRational
#print axioms WuPaper.ClassicalSixthRational.all_lower_paid

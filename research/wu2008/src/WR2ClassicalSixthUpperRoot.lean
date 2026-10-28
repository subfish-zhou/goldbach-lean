import WR2ClassicalSixthUpperPayments
import WR2ClassicalSixthIntegerSoundness
namespace WuPaper.ClassicalSixthRational
open WuSource.SrcSixthGain ClassicalSixthQuadrature

theorem all_upper_paid (i : ℕ) (hindex : i < 4096) : upperPayment i ≤
    upperValue ((point split endpoint 4096 i+point split endpoint 4096 (i+1))/2) :=
  ClassicalSixthTableCheck.upperCondition_sound (SixthIntegerPayment.upper_paid hindex)

end WuPaper.ClassicalSixthRational
#print axioms WuPaper.ClassicalSixthRational.all_upper_paid

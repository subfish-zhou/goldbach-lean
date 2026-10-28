import WR2ClassicalEighthRawIntegerSoundness
noncomputable section
namespace WuPaper.ClassicalEighth
open Finset

theorem all_paid (i : ℕ) (hi : i < 2048) : upperValue ((point (i)+point ((i)+1))/2) ≤ payment (i) := by
  apply ClassicalEighthTableCheck.condition_sound
  simpa only [ClassicalEighthTableCheck.condition,EighthIntegerPayment.scale,Nat.cast_ofNat] using
    EighthIntegerPayment.integer_paid_rat hi

theorem raw_upper : 8*Wu2008DoubleSieve.SeventhEighth.J8 ≤ (52990343:ℝ)/10000000 := by
  apply (uniform_upper payment all_paid).trans
  simp only [payment,← sum_div,← Nat.cast_sum,numerator_sum]
  norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
end WuPaper.ClassicalEighth
#print axioms WuPaper.ClassicalEighth.raw_upper

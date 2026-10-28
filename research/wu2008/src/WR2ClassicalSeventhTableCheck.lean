import WR2ClassicalSeventhPayments
import WR2ExactRationalLog

namespace WuPaper.ClassicalSeventhTableCheck
open ExactRational

def value (t : ℚ) : ℚ := logHi ((1-2*t)/t)/(t*(1-t))

@[simp] theorem cast_value (t : ℚ) :
    (value t : ℝ) = ClassicalSeventh.upperValue (t : ℝ) := by
  simp [value, ClassicalSeventh.upperValue]

def condition (i : ℕ) : Prop :=
  value (midpoint (727/2654) (1/3) 256 i) ≤
    (ClassicalSeventh.numerator i : ℚ)/1000000000000

theorem condition_sound {i : ℕ} (h : condition i) :
    ClassicalSeventh.upperValue ((ClassicalSeventh.point i+ClassicalSeventh.point (i+1))/2) ≤
      ClassicalSeventh.payment i := by
  have hh := Rat.cast_le (K := ℝ) |>.mpr h
  norm_num [ClassicalSeventh.payment, ExactRational.midpoint, ClassicalSeventh.point,
    ClassicalSeventh.step, ClassicalSeventh.lowerEndpoint,
    Wu2008DoubleSieve.SeventhEighth.sigma, Wu2008DoubleSieve.SeventhEighth.alpha] at hh ⊢
  exact hh

end WuPaper.ClassicalSeventhTableCheck

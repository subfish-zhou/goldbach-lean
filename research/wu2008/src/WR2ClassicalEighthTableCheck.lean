import WR2ClassicalEighthRawPayments
import WR2ExactRationalLog

namespace WuPaper.ClassicalEighthTableCheck
open ExactRational

def value (t : ℚ) : ℚ := logHi (2-3*t)/(t*(1-t))

@[simp] theorem cast_value (t : ℚ) :
    (value t : ℝ) = ClassicalEighth.upperValue (t : ℝ) := by
  simp [value, ClassicalEighth.upperValue]

def condition (i : ℕ) : Prop :=
  value (midpoint (100/1327) (1/3) 2048 i) ≤
    (ClassicalEighth.numerator i : ℚ)/1000000000000

theorem condition_sound {i : ℕ} (h : condition i) :
    ClassicalEighth.upperValue ((ClassicalEighth.point i+ClassicalEighth.point (i+1))/2) ≤
      ClassicalEighth.payment i := by
  have hh := Rat.cast_le (K := ℝ) |>.mpr h
  simpa [ClassicalEighth.payment, ExactRational.midpoint, ClassicalEighth.point,
    ClassicalEighth.step, ClassicalEighth.lowerEndpoint, Wu2008DoubleSieve.SeventhEighth.alpha] using hh

end WuPaper.ClassicalEighthTableCheck

import WR2ClassicalNinthPayments
import WR2ExactRationalLog

namespace WuPaper.ClassicalNinthTableCheck
open ExactRational

def sigma : ℚ := 1/2-3*(100/1327)
def value (t : ℚ) : ℚ := logHi ((1-sigma-t)/sigma)/(t*(1-t))

@[simp] theorem cast_sigma : (sigma : ℝ) = ClassicalNinth.upperEndpoint := by
  simp [sigma, ClassicalNinth.upperEndpoint, Wu2008DoubleSieve.ninthProfileSigma,
    Wu2008DoubleSieve.ninthProfileK1]

@[simp] theorem cast_value (t : ℚ) :
    (value t : ℝ) = ClassicalNinth.upperValue (t : ℝ) := by
  simp [value, ClassicalNinth.upperValue]

def condition (i : ℕ) : Prop :=
  value (midpoint (25/206) sigma 512 i) ≤
    (ClassicalNinth.numerator i : ℚ)/1000000000000

theorem condition_sound {i : ℕ} (h : condition i) :
    ClassicalNinth.upperValue ((ClassicalNinth.point i+ClassicalNinth.point (i+1))/2) ≤
      ClassicalNinth.payment i := by
  have hh := Rat.cast_le (K := ℝ) |>.mpr h
  simpa [ClassicalNinth.payment, ExactRational.midpoint, ClassicalNinth.point,
    ClassicalNinth.step, ClassicalNinth.lowerEndpoint, Wu2008DoubleSieve.ninthProfileK2] using hh

end WuPaper.ClassicalNinthTableCheck

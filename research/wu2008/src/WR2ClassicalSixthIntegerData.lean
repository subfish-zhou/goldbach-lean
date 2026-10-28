import Mathlib.Data.Real.Basic
import WR2IntegerLogHorner
namespace WuPaper.SixthIntegerPayment
open IntegerLogHorner

def scale : ℕ := 1000000000000
def gridDenominator : ℕ := 168755200
def gridNumerator (upper : Bool) (i : ℕ) : ℕ :=
  if upper then 576151552+12575*(2*i+1) else 337510400+29131*(2*i+1)
def uNumerator (upper : Bool) (i : ℕ) : ℕ :=
  1127*gridDenominator-200*gridNumerator upper i
def vNumerator (upper : Bool) (i : ℕ) : ℕ :=
  828048*gridDenominator-164800*gridNumerator upper i
def weightNumerator (upper : Bool) (i : ℕ) : ℕ :=
  1327*gridDenominator-200*gridNumerator upper i
def ratioNumerator (upper : Bool) (i : ℕ) : ℕ :=
  if upper then uNumerator upper i*vNumerator upper i else 1327*uNumerator upper i
def ratioDenominator (upper : Bool) (i : ℕ) : ℕ :=
  if upper then 53080000*gridDenominator^2 else vNumerator upper i
def rawNumerator (upper : Bool) (i : ℕ) : ℕ :=
  scale*1327*gridDenominator^2*
    numerator (ratioNumerator upper i-ratioDenominator upper i)
      (ratioNumerator upper i+ratioDenominator upper i)*
    numerator (gridNumerator upper i-2*gridDenominator) (gridNumerator upper i)
def rawDenominator (upper : Bool) (i : ℕ) : ℕ :=
  denominator (ratioNumerator upper i+ratioDenominator upper i)*
    denominator (gridNumerator upper i)*gridNumerator upper i*weightNumerator upper i
def paymentNumerator (upper : Bool) (i : ℕ) : ℕ :=
  if i < 4096 then rawNumerator upper i/rawDenominator upper i else 0
end WuPaper.SixthIntegerPayment

namespace WuPaper.ClassicalSixthRational
abbrev lowerNumerator := SixthIntegerPayment.paymentNumerator false
noncomputable def lowerPayment (i : ℕ) : ℝ := (lowerNumerator i:ℝ)/1000000000000
def lowerPaymentBlockSum (b : ℕ) : ℕ := ∑ j ∈ Finset.range 64, lowerNumerator (64*b+j)
end WuPaper.ClassicalSixthRational

namespace WuPaper.ClassicalSixthRational
abbrev upperNumerator := SixthIntegerPayment.paymentNumerator true
noncomputable def upperPayment (i : ℕ) : ℝ := (upperNumerator i:ℝ)/1000000000000
def upperPaymentBlockSum (b : ℕ) : ℕ := ∑ j ∈ Finset.range 64, upperNumerator (64*b+j)
end WuPaper.ClassicalSixthRational

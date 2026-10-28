import Mathlib.Data.Real.Basic
import WR2IntegerLogHorner

/-! Exact integer C payments. The outside-grid value remains zero. -/
namespace WuPaper.CIntegerPayment
open IntegerLogHorner

def scale : ℕ := 1000000000000
def gridDenominator : ℕ := 1638400
def gridNumerator (i : ℕ) : ℕ := 3276800+527*(2*i+1)

def rawNumerator (i : ℕ) : ℕ :=
  scale*gridDenominator*
    splitNumerator (gridNumerator i-gridDenominator) gridDenominator*
    splitNumerator (1127*gridDenominator) (200*(gridNumerator i+gridDenominator))
def rawDenominator (i : ℕ) : ℕ :=
  gridNumerator i*
    splitDenominator (gridNumerator i-gridDenominator) gridDenominator*
    splitDenominator (1127*gridDenominator) (200*(gridNumerator i+gridDenominator))
def paymentNumerator (i : ℕ) : ℕ :=
  if i < 4096 then rawNumerator i/rawDenominator i else 0

end WuPaper.CIntegerPayment

namespace WuPaper.ClassicalC
abbrev cPaymentNumerator := CIntegerPayment.paymentNumerator
noncomputable def cPayment (i : ℕ) : ℝ := (cPaymentNumerator i:ℝ)/1000000000000
def cPaymentBlockSum (b : ℕ) : ℕ := ∑ j ∈ Finset.range 64, cPaymentNumerator (64*b+j)
end WuPaper.ClassicalC

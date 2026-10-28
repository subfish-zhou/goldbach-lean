import Mathlib.Data.Real.Basic
import WR2IntegerLogUpper
namespace WuPaper.EighthIntegerPayment

def scale : ℕ := 1000000000000
def gridDenominator : ℕ := 16306176
def gridNumerator (i : ℕ) : ℕ := 1228800+1027*(2*i+1)
def cayleyP (i : ℕ) : ℕ := gridDenominator-3*gridNumerator i
def cayleyQ (i : ℕ) : ℕ := 3*gridDenominator-3*gridNumerator i

def rawNumerator (i : ℕ) : ℕ :=
  scale*gridDenominator^2*IntegerLogUpper.hiNumerator (cayleyP i) (cayleyQ i)
def rawDenominator (i : ℕ) : ℕ :=
  IntegerLogUpper.hiDenominator (cayleyP i) (cayleyQ i)*
    gridNumerator i*(gridDenominator-gridNumerator i)
def paymentNumerator (i : ℕ) : ℕ :=
  if i < 2048 then ClassicalCumulativeDivision.ceilDiv (rawNumerator i) (rawDenominator i) else 0
end WuPaper.EighthIntegerPayment

namespace WuPaper.ClassicalEighth
abbrev numerator := EighthIntegerPayment.paymentNumerator
noncomputable def payment (i : ℕ) : ℝ := (numerator i:ℝ)/1000000000000
def paymentBlockSum (b : ℕ) : ℕ := ∑ j ∈ Finset.range 64, numerator (64*b+j)
end WuPaper.ClassicalEighth

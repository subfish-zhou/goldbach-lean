import WR2ClassicalFifthIntegerPolynomial

/-! Exact integer payment formulas on the original Fifth grids.
Soundness uses grid bounds, positive ratio denominators, ratio>=1, and
0<=s-4<=1 on middle/terminal before rewriting each Nat subtraction. -/
namespace WuPaper.FifthIntegerPayment
open IntegerLogHorner

inductive Branch where
  | initial | middle | terminal
  deriving DecidableEq

def scale : ℕ := 1000000000000
def gridDenominator : Branch → ℕ
  | .middle => 21094400
  | _ => 42188800
def gridNumerator : Branch → ℕ → ℕ
  | .initial, i => 144037888+12069*(2*i+1)
  | .middle, i => 84377600+253*(2*i+1)
  | .terminal, i => 169791488+12575*(2*i+1)

def extraNumerator (branch : Branch) (i : ℕ) : ℕ :=
  match branch with
  | .initial => 0
  | _ => FifthIntegerPolynomial.homogeneous
      (gridNumerator branch i-4*gridDenominator branch) (gridDenominator branch)
def extraDenominator (branch : Branch) : ℕ :=
  match branch with
  | .initial => 1
  | _ => FifthIntegerPolynomial.commonDen*(gridDenominator branch)^12

def ratioNumerator (branch : Branch) (i : ℕ) : ℕ :=
  match branch with
  | .terminal => 1127*gridDenominator branch-200*gridNumerator branch i
  | _ => 265400*gridDenominator branch
def ratioDenominator (branch : Branch) (i : ℕ) : ℕ :=
  match branch with
  | .terminal => 200*gridDenominator branch
  | _ => 828048*gridDenominator branch-164800*gridNumerator branch i

def rawNumerator (branch : Branch) (i : ℕ) : ℕ :=
  scale*2654*(gridDenominator branch)^2*
    (numerator (gridNumerator branch i-2*gridDenominator branch) (gridNumerator branch i)*
      extraDenominator branch+
      extraNumerator branch i*denominator (gridNumerator branch i))*
    numerator (ratioNumerator branch i-ratioDenominator branch i)
      (ratioNumerator branch i+ratioDenominator branch i)
def rawDenominator (branch : Branch) (i : ℕ) : ℕ :=
  denominator (gridNumerator branch i)*extraDenominator branch*
    denominator (ratioNumerator branch i+ratioDenominator branch i)*
    gridNumerator branch i*(1327*gridDenominator branch-200*gridNumerator branch i)
def paymentNumerator (branch : Branch) (i : ℕ) : ℕ :=
  if i < 1024 then rawNumerator branch i/rawDenominator branch i else 0

end WuPaper.FifthIntegerPayment

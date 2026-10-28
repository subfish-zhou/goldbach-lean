import WR2IntegerLogUpper
namespace WuPaper.ClassicalFourthData
open IntegerLogUpper

def BqRawNumerator (i : ℕ) : ℕ :=
  1000000000000000*4000*(hiNumerator i (16000+i)*hiDenominator i (16000+3*i)+
    hiNumerator i (16000+3*i)*hiDenominator i (16000+i))
def BqRawDenominator (i : ℕ) : ℕ :=
  (8000+i)*hiDenominator i (16000+i)*hiDenominator i (16000+3*i)
def Bq (i : ℕ) : ℕ :=
  if i ≤ 10540 then ClassicalCumulativeDivision.ceilDiv (BqRawNumerator i) (BqRawDenominator i) else 0
end WuPaper.ClassicalFourthData

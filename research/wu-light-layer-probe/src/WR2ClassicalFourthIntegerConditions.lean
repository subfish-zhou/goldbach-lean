import WR2ClassicalFourthDataBq
import WR2ClassicalFourthDataB
import WR2ClassicalFourthDataC
import WR2ClassicalFourthDataD
import WR2ClassicalFourthDataouterq
import WR2ClassicalFourthDataouter

namespace WuPaper.ClassicalFourthConditions
open ClassicalFourthData

def BPay (i : ℕ) : Prop :=
  6*4000^3*B i+3*4000^2*(Bq i+Bq (i+1))+2*1000000000000000 ≤ 6*4000^3*B (i+1)
def CPay (i : ℕ) : Prop :=
  let m := 12000+i
  6*4000^3*m*(m+1)*C i+3*4000^3*((m+1)*B i+m*B (i+1))+2*1000000000000000*m*(m+1) ≤
    6*4000^3*m*(m+1)*C (i+1)
def DPay (i : ℕ) : Prop :=
  let m := 16000+i
  6*4000^3*m*(m+1)*D i+3*4000^3*((m+1)*C i+m*C (i+1))+1*1000000000000000*m*(m+1) ≤
    6*4000^3*m*(m+1)*D (i+1)
def OuterPay (i : ℕ) : Prop :=
  6*4000^3*outer i+3*4000^2*(outerq i+outerq (i+1))+56*1000000000000000 ≤ 6*4000^3*outer (i+1)
def tail (i : ℕ) : ℕ := if 8000 ≤ i then D (i-8000) else 0
def OuterPoint (i : ℕ) : Prop :=
  2654*4000^2*(1000000000000000+B i+tail i) ≤ (12000+i)*(5308000-200*(12000+i))*outerq i

end WuPaper.ClassicalFourthConditions

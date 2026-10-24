import WR2ClassicalFourthDataBq
import WR2ClassicalFourthDataB
import WR2ClassicalFourthDataC
import WR2ClassicalFourthDataD
import WR2ClassicalFourthDataouterq
import WR2ClassicalFourthDataouter
import WR2ClassicalFourthAssembly

noncomputable section
namespace WuPaper.ClassicalFourthConditions
open Real ClassicalFourthData ClassicalFourthRecurrence

abbrev val (f : ℕ → ℕ) (i : ℕ) : ℝ := (f i:ℝ)/1000000000000000

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

theorem B_payment {i : ℕ} (h : BPay i) :
    (1:ℝ)/4000*(val Bq i+val Bq (i+1))/2+2*((1:ℝ)/4000)^3/6 ≤ val B (i+1)-val B i :=
  ClassicalIntegerPayments.direct_payment _ _ _ _ 2 h

theorem C_payment {i : ℕ} (h : CPay i) :
    (1:ℝ)/4000*(val B i/node 3 i+val B (i+1)/node 3 (i+1))/2+
      2*((1:ℝ)/4000)^3/6 ≤ val C (i+1)-val C i := by
  have hm : node 3 i = ((12000+i:ℕ):ℝ)/4000 := by simp [node]; ring
  have hn : node 3 (i+1) = (((12000+i:ℕ):ℝ)+1)/4000 := by simp [node]; ring
  rw [hm,hn]
  exact ClassicalIntegerPayments.divided_payment (12000+i) _ _ _ _ 2 (by omega) h

theorem D_payment {i : ℕ} (h : DPay i) :
    (1:ℝ)/4000*(val C i/node 4 i+val C (i+1)/node 4 (i+1))/2+
      1*((1:ℝ)/4000)^3/6 ≤ val D (i+1)-val D i := by
  have hm : node 4 i = ((16000+i:ℕ):ℝ)/4000 := by simp [node]; ring
  have hn : node 4 (i+1) = (((16000+i:ℕ):ℝ)+1)/4000 := by simp [node]; ring
  rw [hm,hn]
  simpa only [Nat.cast_one] using ClassicalIntegerPayments.divided_payment (16000+i) _ _ _ _ 1 (by omega) h

theorem outer_payment {i : ℕ} (h : OuterPay i) :
    (1:ℝ)/4000*(val outerq i+val outerq (i+1))/2+56*((1:ℝ)/4000)^3/6 ≤
      val outer (i+1)-val outer i := ClassicalIntegerPayments.direct_payment _ _ _ _ 56 h

theorem outer_point {i : ℕ} (hi : i ≤ 10540) (h : OuterPoint i) :
    (1+val B i+val tail i)/(node 3 i*((1:ℝ)/2-(100/1327)*node 3 i)) ≤ val outerq i := by
  have hm : node 3 i = ((12000+i:ℕ):ℝ)/4000 := by simp [node]; ring
  have hw : 0 < 5308000-200*(12000+i) := by omega
  have hsub : 200*(12000+i) ≤ 5308000 := by omega
  have ht : (1:ℝ)/2-(100/1327)*node 3 i =
      ((5308000-200*(12000+i):ℕ):ℝ)/(2654*4000) := by
    rw [Nat.cast_sub hsub]
    push_cast
    unfold node
    ring
  rw [ht,hm]
  exact ClassicalIntegerPayments.outer_payment (12000+i) (5308000-200*(12000+i)) _ _ _ (by omega) hw h

end WuPaper.ClassicalFourthConditions
#print axioms WuPaper.ClassicalFourthConditions.C_payment
#print axioms WuPaper.ClassicalFourthConditions.outer_point

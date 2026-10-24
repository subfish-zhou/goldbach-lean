import WR2ClassicalFourthConditions
import WR2ClassicalFourthLogPoints347
noncomputable section
namespace WuPaper.ClassicalFourthConditions
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem Log_block_347 (j : Fin 16) (hj : 16*347+j.val < 10541) :
    WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 (16*347+j.val)) ≤ val WuPaper.ClassicalFourthData.Bq (16*347+j.val) := by
  fin_cases j
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 5552) ≤ val WuPaper.ClassicalFourthData.Bq 5552
    have hp : val WuPaper.ClassicalFourthData.Bq 5552 = (256923316272244:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 5552 = 256923316272244 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 5552 = (847:ℝ)/250 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_5552
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 5553) ≤ val WuPaper.ClassicalFourthData.Bq 5553
    have hp : val WuPaper.ClassicalFourthData.Bq 5553 = (256935255712532:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 5553 = 256935255712532 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 5553 = (13553:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_5553
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 5554) ≤ val WuPaper.ClassicalFourthData.Bq 5554
    have hp : val WuPaper.ClassicalFourthData.Bq 5554 = (256947190157263:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 5554 = 256947190157263 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 5554 = (6777:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_5554
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 5555) ≤ val WuPaper.ClassicalFourthData.Bq 5555
    have hp : val WuPaper.ClassicalFourthData.Bq 5555 = (256959119608219:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 5555 = 256959119608219 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 5555 = (2711:ℝ)/800 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_5555
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 5556) ≤ val WuPaper.ClassicalFourthData.Bq 5556
    have hp : val WuPaper.ClassicalFourthData.Bq 5556 = (256971044067181:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 5556 = 256971044067181 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 5556 = (3389:ℝ)/1000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_5556
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 5557) ≤ val WuPaper.ClassicalFourthData.Bq 5557
    have hp : val WuPaper.ClassicalFourthData.Bq 5557 = (256982963535932:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 5557 = 256982963535932 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 5557 = (13557:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_5557
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 5558) ≤ val WuPaper.ClassicalFourthData.Bq 5558
    have hp : val WuPaper.ClassicalFourthData.Bq 5558 = (256994878016251:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 5558 = 256994878016251 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 5558 = (6779:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_5558
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 5559) ≤ val WuPaper.ClassicalFourthData.Bq 5559
    have hp : val WuPaper.ClassicalFourthData.Bq 5559 = (257006787509917:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 5559 = 257006787509917 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 5559 = (13559:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_5559
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 5560) ≤ val WuPaper.ClassicalFourthData.Bq 5560
    have hp : val WuPaper.ClassicalFourthData.Bq 5560 = (257018692018709:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 5560 = 257018692018709 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 5560 = (339:ℝ)/100 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_5560
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 5561) ≤ val WuPaper.ClassicalFourthData.Bq 5561
    have hp : val WuPaper.ClassicalFourthData.Bq 5561 = (257030591544406:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 5561 = 257030591544406 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 5561 = (13561:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_5561
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 5562) ≤ val WuPaper.ClassicalFourthData.Bq 5562
    have hp : val WuPaper.ClassicalFourthData.Bq 5562 = (257042486088785:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 5562 = 257042486088785 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 5562 = (6781:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_5562
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 5563) ≤ val WuPaper.ClassicalFourthData.Bq 5563
    have hp : val WuPaper.ClassicalFourthData.Bq 5563 = (257054375653623:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 5563 = 257054375653623 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 5563 = (13563:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_5563
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 5564) ≤ val WuPaper.ClassicalFourthData.Bq 5564
    have hp : val WuPaper.ClassicalFourthData.Bq 5564 = (257066260240694:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 5564 = 257066260240694 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 5564 = (3391:ℝ)/1000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_5564
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 5565) ≤ val WuPaper.ClassicalFourthData.Bq 5565
    have hp : val WuPaper.ClassicalFourthData.Bq 5565 = (257078139851775:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 5565 = 257078139851775 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 5565 = (2713:ℝ)/800 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_5565
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 5566) ≤ val WuPaper.ClassicalFourthData.Bq 5566
    have hp : val WuPaper.ClassicalFourthData.Bq 5566 = (257090014488639:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 5566 = 257090014488639 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 5566 = (6783:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_5566
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 5567) ≤ val WuPaper.ClassicalFourthData.Bq 5567
    have hp : val WuPaper.ClassicalFourthData.Bq 5567 = (257101884153061:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 5567 = 257101884153061 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 5567 = (13567:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_5567
end WuPaper.ClassicalFourthConditions
#print axioms WuPaper.ClassicalFourthConditions.Log_block_347

import WR2ClassicalFourthConditions
import WR2ClassicalFourthLogPoints409
noncomputable section
namespace WuPaper.ClassicalFourthConditions
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem Log_block_409 (j : Fin 16) (hj : 16*409+j.val < 10541) :
    WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 (16*409+j.val)) ≤ val WuPaper.ClassicalFourthData.Bq (16*409+j.val) := by
  fin_cases j
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 6544) ≤ val WuPaper.ClassicalFourthData.Bq 6544
    have hp : val WuPaper.ClassicalFourthData.Bq 6544 = (266573876963790:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 6544 = 266573876963790 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 6544 = (909:ℝ)/250 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_6544
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 6545) ≤ val WuPaper.ClassicalFourthData.Bq 6545
    have hp : val WuPaper.ClassicalFourthData.Bq 6545 = (266581630198949:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 6545 = 266581630198949 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 6545 = (2909:ℝ)/800 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_6545
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 6546) ≤ val WuPaper.ClassicalFourthData.Bq 6546
    have hp : val WuPaper.ClassicalFourthData.Bq 6546 = (266589379895083:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 6546 = 266589379895083 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 6546 = (7273:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_6546
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 6547) ≤ val WuPaper.ClassicalFourthData.Bq 6547
    have hp : val WuPaper.ClassicalFourthData.Bq 6547 = (266597126053390:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 6547 = 266597126053390 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 6547 = (14547:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_6547
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 6548) ≤ val WuPaper.ClassicalFourthData.Bq 6548
    have hp : val WuPaper.ClassicalFourthData.Bq 6548 = (266604868675070:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 6548 = 266604868675070 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 6548 = (3637:ℝ)/1000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_6548
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 6549) ≤ val WuPaper.ClassicalFourthData.Bq 6549
    have hp : val WuPaper.ClassicalFourthData.Bq 6549 = (266612607761320:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 6549 = 266612607761320 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 6549 = (14549:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_6549
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 6550) ≤ val WuPaper.ClassicalFourthData.Bq 6550
    have hp : val WuPaper.ClassicalFourthData.Bq 6550 = (266620343313338:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 6550 = 266620343313338 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 6550 = (291:ℝ)/80 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_6550
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 6551) ≤ val WuPaper.ClassicalFourthData.Bq 6551
    have hp : val WuPaper.ClassicalFourthData.Bq 6551 = (266628075332320:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 6551 = 266628075332320 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 6551 = (14551:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_6551
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 6552) ≤ val WuPaper.ClassicalFourthData.Bq 6552
    have hp : val WuPaper.ClassicalFourthData.Bq 6552 = (266635803819462:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 6552 = 266635803819462 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 6552 = (1819:ℝ)/500 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_6552
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 6553) ≤ val WuPaper.ClassicalFourthData.Bq 6553
    have hp : val WuPaper.ClassicalFourthData.Bq 6553 = (266643528775962:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 6553 = 266643528775962 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 6553 = (14553:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_6553
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 6554) ≤ val WuPaper.ClassicalFourthData.Bq 6554
    have hp : val WuPaper.ClassicalFourthData.Bq 6554 = (266651250203014:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 6554 = 266651250203014 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 6554 = (7277:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_6554
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 6555) ≤ val WuPaper.ClassicalFourthData.Bq 6555
    have hp : val WuPaper.ClassicalFourthData.Bq 6555 = (266658968101814:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 6555 = 266658968101814 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 6555 = (2911:ℝ)/800 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_6555
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 6556) ≤ val WuPaper.ClassicalFourthData.Bq 6556
    have hp : val WuPaper.ClassicalFourthData.Bq 6556 = (266666682473556:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 6556 = 266666682473556 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 6556 = (3639:ℝ)/1000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_6556
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 6557) ≤ val WuPaper.ClassicalFourthData.Bq 6557
    have hp : val WuPaper.ClassicalFourthData.Bq 6557 = (266674393319434:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 6557 = 266674393319434 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 6557 = (14557:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_6557
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 6558) ≤ val WuPaper.ClassicalFourthData.Bq 6558
    have hp : val WuPaper.ClassicalFourthData.Bq 6558 = (266682100640642:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 6558 = 266682100640642 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 6558 = (7279:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_6558
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 6559) ≤ val WuPaper.ClassicalFourthData.Bq 6559
    have hp : val WuPaper.ClassicalFourthData.Bq 6559 = (266689804438373:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 6559 = 266689804438373 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 6559 = (14559:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_6559
end WuPaper.ClassicalFourthConditions
#print axioms WuPaper.ClassicalFourthConditions.Log_block_409

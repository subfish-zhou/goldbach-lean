import WR2ClassicalFourthConditions
import WR2ClassicalFourthLogPoints043
noncomputable section
namespace WuPaper.ClassicalFourthConditions
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem Log_block_043 (j : Fin 16) (hj : 16*43+j.val < 10541) :
    WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 (16*43+j.val)) ≤ val WuPaper.ClassicalFourthData.Bq (16*43+j.val) := by
  fin_cases j
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 688) ≤ val WuPaper.ClassicalFourthData.Bq 688
    have hp : val WuPaper.ClassicalFourthData.Bq 688 = (73071681010507:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 688 = 73071681010507 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 688 = (543:ℝ)/250 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_688
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 689) ≤ val WuPaper.ClassicalFourthData.Bq 689
    have hp : val WuPaper.ClassicalFourthData.Bq 689 = (73161458850298:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 689 = 73161458850298 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 689 = (8689:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_689
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 690) ≤ val WuPaper.ClassicalFourthData.Bq 690
    have hp : val WuPaper.ClassicalFourthData.Bq 690 = (73251195092427:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 690 = 73251195092427 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 690 = (869:ℝ)/400 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_690
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 691) ≤ val WuPaper.ClassicalFourthData.Bq 691
    have hp : val WuPaper.ClassicalFourthData.Bq 691 = (73340889760180:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 691 = 73340889760180 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 691 = (8691:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_691
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 692) ≤ val WuPaper.ClassicalFourthData.Bq 692
    have hp : val WuPaper.ClassicalFourthData.Bq 692 = (73430542876824:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 692 = 73430542876824 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 692 = (2173:ℝ)/1000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_692
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 693) ≤ val WuPaper.ClassicalFourthData.Bq 693
    have hp : val WuPaper.ClassicalFourthData.Bq 693 = (73520154465612:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 693 = 73520154465612 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 693 = (8693:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_693
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 694) ≤ val WuPaper.ClassicalFourthData.Bq 694
    have hp : val WuPaper.ClassicalFourthData.Bq 694 = (73609724549778:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 694 = 73609724549778 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 694 = (4347:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_694
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 695) ≤ val WuPaper.ClassicalFourthData.Bq 695
    have hp : val WuPaper.ClassicalFourthData.Bq 695 = (73699253152541:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 695 = 73699253152541 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 695 = (1739:ℝ)/800 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_695
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 696) ≤ val WuPaper.ClassicalFourthData.Bq 696
    have hp : val WuPaper.ClassicalFourthData.Bq 696 = (73788740297105:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 696 = 73788740297105 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 696 = (1087:ℝ)/500 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_696
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 697) ≤ val WuPaper.ClassicalFourthData.Bq 697
    have hp : val WuPaper.ClassicalFourthData.Bq 697 = (73878186006654:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 697 = 73878186006654 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 697 = (8697:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_697
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 698) ≤ val WuPaper.ClassicalFourthData.Bq 698
    have hp : val WuPaper.ClassicalFourthData.Bq 698 = (73967590304360:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 698 = 73967590304360 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 698 = (4349:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_698
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 699) ≤ val WuPaper.ClassicalFourthData.Bq 699
    have hp : val WuPaper.ClassicalFourthData.Bq 699 = (74056953213376:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 699 = 74056953213376 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 699 = (8699:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_699
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 700) ≤ val WuPaper.ClassicalFourthData.Bq 700
    have hp : val WuPaper.ClassicalFourthData.Bq 700 = (74146274756838:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 700 = 74146274756838 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 700 = (87:ℝ)/40 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_700
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 701) ≤ val WuPaper.ClassicalFourthData.Bq 701
    have hp : val WuPaper.ClassicalFourthData.Bq 701 = (74235554957869:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 701 = 74235554957869 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 701 = (8701:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_701
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 702) ≤ val WuPaper.ClassicalFourthData.Bq 702
    have hp : val WuPaper.ClassicalFourthData.Bq 702 = (74324793839572:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 702 = 74324793839572 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 702 = (4351:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_702
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 703) ≤ val WuPaper.ClassicalFourthData.Bq 703
    have hp : val WuPaper.ClassicalFourthData.Bq 703 = (74413991425036:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 703 = 74413991425036 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 703 = (8703:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_703
end WuPaper.ClassicalFourthConditions
#print axioms WuPaper.ClassicalFourthConditions.Log_block_043

import WR2ClassicalFourthConditions
import WR2ClassicalFourthLogPoints102
noncomputable section
namespace WuPaper.ClassicalFourthConditions
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem Log_block_102 (j : Fin 16) (hj : 16*102+j.val < 10541) :
    WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 (16*102+j.val)) ≤ val WuPaper.ClassicalFourthData.Bq (16*102+j.val) := by
  fin_cases j
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 1632) ≤ val WuPaper.ClassicalFourthData.Bq 1632
    have hp : val WuPaper.ClassicalFourthData.Bq 1632 = (142097283112895:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 1632 = 142097283112895 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 1632 = (301:ℝ)/125 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_1632
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 1633) ≤ val WuPaper.ClassicalFourthData.Bq 1633
    have hp : val WuPaper.ClassicalFourthData.Bq 1633 = (142156254040356:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 1633 = 142156254040356 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 1633 = (9633:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_1633
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 1634) ≤ val WuPaper.ClassicalFourthData.Bq 1634
    have hp : val WuPaper.ClassicalFourthData.Bq 1634 = (142215199640561:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 1634 = 142215199640561 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 1634 = (4817:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_1634
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 1635) ≤ val WuPaper.ClassicalFourthData.Bq 1635
    have hp : val WuPaper.ClassicalFourthData.Bq 1635 = (142274119926041:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 1635 = 142274119926041 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 1635 = (1927:ℝ)/800 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_1635
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 1636) ≤ val WuPaper.ClassicalFourthData.Bq 1636
    have hp : val WuPaper.ClassicalFourthData.Bq 1636 = (142333014909317:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 1636 = 142333014909317 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 1636 = (2409:ℝ)/1000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_1636
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 1637) ≤ val WuPaper.ClassicalFourthData.Bq 1637
    have hp : val WuPaper.ClassicalFourthData.Bq 1637 = (142391884602905:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 1637 = 142391884602905 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 1637 = (9637:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_1637
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 1638) ≤ val WuPaper.ClassicalFourthData.Bq 1638
    have hp : val WuPaper.ClassicalFourthData.Bq 1638 = (142450729019312:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 1638 = 142450729019312 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 1638 = (4819:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_1638
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 1639) ≤ val WuPaper.ClassicalFourthData.Bq 1639
    have hp : val WuPaper.ClassicalFourthData.Bq 1639 = (142509548171037:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 1639 = 142509548171037 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 1639 = (9639:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_1639
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 1640) ≤ val WuPaper.ClassicalFourthData.Bq 1640
    have hp : val WuPaper.ClassicalFourthData.Bq 1640 = (142568342070572:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 1640 = 142568342070572 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 1640 = (241:ℝ)/100 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_1640
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 1641) ≤ val WuPaper.ClassicalFourthData.Bq 1641
    have hp : val WuPaper.ClassicalFourthData.Bq 1641 = (142627110730401:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 1641 = 142627110730401 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 1641 = (9641:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_1641
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 1642) ≤ val WuPaper.ClassicalFourthData.Bq 1642
    have hp : val WuPaper.ClassicalFourthData.Bq 1642 = (142685854163002:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 1642 = 142685854163002 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 1642 = (4821:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_1642
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 1643) ≤ val WuPaper.ClassicalFourthData.Bq 1643
    have hp : val WuPaper.ClassicalFourthData.Bq 1643 = (142744572380841:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 1643 = 142744572380841 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 1643 = (9643:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_1643
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 1644) ≤ val WuPaper.ClassicalFourthData.Bq 1644
    have hp : val WuPaper.ClassicalFourthData.Bq 1644 = (142803265396382:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 1644 = 142803265396382 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 1644 = (2411:ℝ)/1000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_1644
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 1645) ≤ val WuPaper.ClassicalFourthData.Bq 1645
    have hp : val WuPaper.ClassicalFourthData.Bq 1645 = (142861933222078:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 1645 = 142861933222078 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 1645 = (1929:ℝ)/800 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_1645
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 1646) ≤ val WuPaper.ClassicalFourthData.Bq 1646
    have hp : val WuPaper.ClassicalFourthData.Bq 1646 = (142920575870375:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 1646 = 142920575870375 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 1646 = (4823:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_1646
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 1647) ≤ val WuPaper.ClassicalFourthData.Bq 1647
    have hp : val WuPaper.ClassicalFourthData.Bq 1647 = (142979193353710:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 1647 = 142979193353710 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 1647 = (9647:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_1647
end WuPaper.ClassicalFourthConditions
#print axioms WuPaper.ClassicalFourthConditions.Log_block_102

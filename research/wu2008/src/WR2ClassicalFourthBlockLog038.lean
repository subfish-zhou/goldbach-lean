import WR2ClassicalFourthConditions
import WR2ClassicalFourthLogPoints038
noncomputable section
namespace WuPaper.ClassicalFourthConditions
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem Log_block_038 (j : Fin 16) (hj : 16*38+j.val < 10541) :
    WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 (16*38+j.val)) ≤ val WuPaper.ClassicalFourthData.Bq (16*38+j.val) := by
  fin_cases j
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 608) ≤ val WuPaper.ClassicalFourthData.Bq 608
    have hp : val WuPaper.ClassicalFourthData.Bq 608 = (65752584699675:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 608 = 65752584699675 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 608 = (269:ℝ)/125 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_608
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 609) ≤ val WuPaper.ClassicalFourthData.Bq 609
    have hp : val WuPaper.ClassicalFourthData.Bq 609 = (65845767275401:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 609 = 65845767275401 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 609 = (8609:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_609
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 610) ≤ val WuPaper.ClassicalFourthData.Bq 610
    have hp : val WuPaper.ClassicalFourthData.Bq 610 = (65938906336199:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 610 = 65938906336199 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 610 = (861:ℝ)/400 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_610
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 611) ≤ val WuPaper.ClassicalFourthData.Bq 611
    have hp : val WuPaper.ClassicalFourthData.Bq 611 = (66032001906714:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 611 = 66032001906714 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 611 = (8611:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_611
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 612) ≤ val WuPaper.ClassicalFourthData.Bq 612
    have hp : val WuPaper.ClassicalFourthData.Bq 612 = (66125054011576:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 612 = 66125054011576 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 612 = (2153:ℝ)/1000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_612
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 613) ≤ val WuPaper.ClassicalFourthData.Bq 613
    have hp : val WuPaper.ClassicalFourthData.Bq 613 = (66218062675395:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 613 = 66218062675395 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 613 = (8613:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_613
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 614) ≤ val WuPaper.ClassicalFourthData.Bq 614
    have hp : val WuPaper.ClassicalFourthData.Bq 614 = (66311027922764:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 614 = 66311027922764 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 614 = (4307:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_614
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 615) ≤ val WuPaper.ClassicalFourthData.Bq 615
    have hp : val WuPaper.ClassicalFourthData.Bq 615 = (66403949778259:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 615 = 66403949778259 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 615 = (1723:ℝ)/800 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_615
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 616) ≤ val WuPaper.ClassicalFourthData.Bq 616
    have hp : val WuPaper.ClassicalFourthData.Bq 616 = (66496828266439:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 616 = 66496828266439 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 616 = (1077:ℝ)/500 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_616
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 617) ≤ val WuPaper.ClassicalFourthData.Bq 617
    have hp : val WuPaper.ClassicalFourthData.Bq 617 = (66589663411843:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 617 = 66589663411843 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 617 = (8617:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_617
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 618) ≤ val WuPaper.ClassicalFourthData.Bq 618
    have hp : val WuPaper.ClassicalFourthData.Bq 618 = (66682455238995:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 618 = 66682455238995 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 618 = (4309:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_618
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 619) ≤ val WuPaper.ClassicalFourthData.Bq 619
    have hp : val WuPaper.ClassicalFourthData.Bq 619 = (66775203772400:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 619 = 66775203772400 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 619 = (8619:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_619
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 620) ≤ val WuPaper.ClassicalFourthData.Bq 620
    have hp : val WuPaper.ClassicalFourthData.Bq 620 = (66867909036547:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 620 = 66867909036547 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 620 = (431:ℝ)/200 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_620
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 621) ≤ val WuPaper.ClassicalFourthData.Bq 621
    have hp : val WuPaper.ClassicalFourthData.Bq 621 = (66960571055905:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 621 = 66960571055905 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 621 = (8621:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_621
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 622) ≤ val WuPaper.ClassicalFourthData.Bq 622
    have hp : val WuPaper.ClassicalFourthData.Bq 622 = (67053189854929:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 622 = 67053189854929 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 622 = (4311:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_622
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 623) ≤ val WuPaper.ClassicalFourthData.Bq 623
    have hp : val WuPaper.ClassicalFourthData.Bq 623 = (67145765458054:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 623 = 67145765458054 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 623 = (8623:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_623
end WuPaper.ClassicalFourthConditions
#print axioms WuPaper.ClassicalFourthConditions.Log_block_038

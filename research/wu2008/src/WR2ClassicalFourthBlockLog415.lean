import WR2ClassicalFourthConditions
import WR2ClassicalFourthLogPoints415
noncomputable section
namespace WuPaper.ClassicalFourthConditions
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem Log_block_415 (j : Fin 16) (hj : 16*415+j.val < 10541) :
    WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 (16*415+j.val)) ≤ val WuPaper.ClassicalFourthData.Bq (16*415+j.val) := by
  fin_cases j
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 6640) ≤ val WuPaper.ClassicalFourthData.Bq 6640
    have hp : val WuPaper.ClassicalFourthData.Bq 6640 = (267302219342544:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 6640 = 267302219342544 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 6640 = (183:ℝ)/50 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_6640
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 6641) ≤ val WuPaper.ClassicalFourthData.Bq 6641
    have hp : val WuPaper.ClassicalFourthData.Bq 6641 = (267309638232308:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 6641 = 267309638232308 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 6641 = (14641:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_6641
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 6642) ≤ val WuPaper.ClassicalFourthData.Bq 6642
    have hp : val WuPaper.ClassicalFourthData.Bq 6642 = (267317053696050:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 6642 = 267317053696050 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 6642 = (7321:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_6642
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 6643) ≤ val WuPaper.ClassicalFourthData.Bq 6643
    have hp : val WuPaper.ClassicalFourthData.Bq 6643 = (267324465734923:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 6643 = 267324465734923 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 6643 = (14643:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_6643
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 6644) ≤ val WuPaper.ClassicalFourthData.Bq 6644
    have hp : val WuPaper.ClassicalFourthData.Bq 6644 = (267331874350084:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 6644 = 267331874350084 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 6644 = (3661:ℝ)/1000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_6644
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 6645) ≤ val WuPaper.ClassicalFourthData.Bq 6645
    have hp : val WuPaper.ClassicalFourthData.Bq 6645 = (267339279542685:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 6645 = 267339279542685 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 6645 = (2929:ℝ)/800 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_6645
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 6646) ≤ val WuPaper.ClassicalFourthData.Bq 6646
    have hp : val WuPaper.ClassicalFourthData.Bq 6646 = (267346681313882:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 6646 = 267346681313882 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 6646 = (7323:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_6646
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 6647) ≤ val WuPaper.ClassicalFourthData.Bq 6647
    have hp : val WuPaper.ClassicalFourthData.Bq 6647 = (267354079664828:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 6647 = 267354079664828 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 6647 = (14647:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_6647
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 6648) ≤ val WuPaper.ClassicalFourthData.Bq 6648
    have hp : val WuPaper.ClassicalFourthData.Bq 6648 = (267361474596675:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 6648 = 267361474596675 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 6648 = (1831:ℝ)/500 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_6648
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 6649) ≤ val WuPaper.ClassicalFourthData.Bq 6649
    have hp : val WuPaper.ClassicalFourthData.Bq 6649 = (267368866110577:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 6649 = 267368866110577 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 6649 = (14649:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_6649
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 6650) ≤ val WuPaper.ClassicalFourthData.Bq 6650
    have hp : val WuPaper.ClassicalFourthData.Bq 6650 = (267376254207686:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 6650 = 267376254207686 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 6650 = (293:ℝ)/80 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_6650
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 6651) ≤ val WuPaper.ClassicalFourthData.Bq 6651
    have hp : val WuPaper.ClassicalFourthData.Bq 6651 = (267383638889153:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 6651 = 267383638889153 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 6651 = (14651:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_6651
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 6652) ≤ val WuPaper.ClassicalFourthData.Bq 6652
    have hp : val WuPaper.ClassicalFourthData.Bq 6652 = (267391020156129:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 6652 = 267391020156129 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 6652 = (3663:ℝ)/1000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_6652
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 6653) ≤ val WuPaper.ClassicalFourthData.Bq 6653
    have hp : val WuPaper.ClassicalFourthData.Bq 6653 = (267398398009766:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 6653 = 267398398009766 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 6653 = (14653:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_6653
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 6654) ≤ val WuPaper.ClassicalFourthData.Bq 6654
    have hp : val WuPaper.ClassicalFourthData.Bq 6654 = (267405772451214:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 6654 = 267405772451214 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 6654 = (7327:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_6654
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 6655) ≤ val WuPaper.ClassicalFourthData.Bq 6655
    have hp : val WuPaper.ClassicalFourthData.Bq 6655 = (267413143481623:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 6655 = 267413143481623 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 6655 = (2931:ℝ)/800 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_6655
end WuPaper.ClassicalFourthConditions
#print axioms WuPaper.ClassicalFourthConditions.Log_block_415

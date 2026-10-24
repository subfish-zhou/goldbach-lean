import WR2ClassicalFourthConditions
import WR2ClassicalFourthLogPoints413
noncomputable section
namespace WuPaper.ClassicalFourthConditions
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem Log_block_413 (j : Fin 16) (hj : 16*413+j.val < 10541) :
    WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 (16*413+j.val)) ≤ val WuPaper.ClassicalFourthData.Bq (16*413+j.val) := by
  fin_cases j
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 6608) ≤ val WuPaper.ClassicalFourthData.Bq 6608
    have hp : val WuPaper.ClassicalFourthData.Bq 6608 = (267062998993349:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 6608 = 267062998993349 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 6608 = (913:ℝ)/250 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_6608
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 6609) ≤ val WuPaper.ClassicalFourthData.Bq 6609
    have hp : val WuPaper.ClassicalFourthData.Bq 6609 = (267070528128507:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 6609 = 267070528128507 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 6609 = (14609:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_6609
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 6610) ≤ val WuPaper.ClassicalFourthData.Bq 6610
    have hp : val WuPaper.ClassicalFourthData.Bq 6610 = (267078053800437:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 6610 = 267078053800437 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 6610 = (1461:ℝ)/400 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_6610
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 6611) ≤ val WuPaper.ClassicalFourthData.Bq 6611
    have hp : val WuPaper.ClassicalFourthData.Bq 6611 = (267085576010309:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 6611 = 267085576010309 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 6611 = (14611:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_6611
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 6612) ≤ val WuPaper.ClassicalFourthData.Bq 6612
    have hp : val WuPaper.ClassicalFourthData.Bq 6612 = (267093094759293:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 6612 = 267093094759293 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 6612 = (3653:ℝ)/1000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_6612
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 6613) ≤ val WuPaper.ClassicalFourthData.Bq 6613
    have hp : val WuPaper.ClassicalFourthData.Bq 6613 = (267100610048557:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 6613 = 267100610048557 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 6613 = (14613:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_6613
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 6614) ≤ val WuPaper.ClassicalFourthData.Bq 6614
    have hp : val WuPaper.ClassicalFourthData.Bq 6614 = (267108121879269:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 6614 = 267108121879269 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 6614 = (7307:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_6614
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 6615) ≤ val WuPaper.ClassicalFourthData.Bq 6615
    have hp : val WuPaper.ClassicalFourthData.Bq 6615 = (267115630252597:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 6615 = 267115630252597 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 6615 = (2923:ℝ)/800 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_6615
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 6616) ≤ val WuPaper.ClassicalFourthData.Bq 6616
    have hp : val WuPaper.ClassicalFourthData.Bq 6616 = (267123135169708:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 6616 = 267123135169708 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 6616 = (1827:ℝ)/500 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_6616
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 6617) ≤ val WuPaper.ClassicalFourthData.Bq 6617
    have hp : val WuPaper.ClassicalFourthData.Bq 6617 = (267130636631769:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 6617 = 267130636631769 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 6617 = (14617:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_6617
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 6618) ≤ val WuPaper.ClassicalFourthData.Bq 6618
    have hp : val WuPaper.ClassicalFourthData.Bq 6618 = (267138134639947:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 6618 = 267138134639947 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 6618 = (7309:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_6618
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 6619) ≤ val WuPaper.ClassicalFourthData.Bq 6619
    have hp : val WuPaper.ClassicalFourthData.Bq 6619 = (267145629195407:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 6619 = 267145629195407 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 6619 = (14619:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_6619
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 6620) ≤ val WuPaper.ClassicalFourthData.Bq 6620
    have hp : val WuPaper.ClassicalFourthData.Bq 6620 = (267153120299316:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 6620 = 267153120299316 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 6620 = (731:ℝ)/200 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_6620
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 6621) ≤ val WuPaper.ClassicalFourthData.Bq 6621
    have hp : val WuPaper.ClassicalFourthData.Bq 6621 = (267160607952838:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 6621 = 267160607952838 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 6621 = (14621:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_6621
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 6622) ≤ val WuPaper.ClassicalFourthData.Bq 6622
    have hp : val WuPaper.ClassicalFourthData.Bq 6622 = (267168092157137:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 6622 = 267168092157137 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 6622 = (7311:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_6622
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 6623) ≤ val WuPaper.ClassicalFourthData.Bq 6623
    have hp : val WuPaper.ClassicalFourthData.Bq 6623 = (267175572913379:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 6623 = 267175572913379 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 6623 = (14623:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_6623
end WuPaper.ClassicalFourthConditions
#print axioms WuPaper.ClassicalFourthConditions.Log_block_413

import WR2ClassicalFourthConditions
import WR2ClassicalFourthLogPoints608
noncomputable section
namespace WuPaper.ClassicalFourthConditions
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem Log_block_608 (j : Fin 16) (hj : 16*608+j.val < 10541) :
    WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 (16*608+j.val)) ≤ val WuPaper.ClassicalFourthData.Bq (16*608+j.val) := by
  fin_cases j
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 9728) ≤ val WuPaper.ClassicalFourthData.Bq 9728
    have hp : val WuPaper.ClassicalFourthData.Bq 9728 = (278236277456569:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 9728 = 278236277456569 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 9728 = (554:ℝ)/125 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_9728
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 9729) ≤ val WuPaper.ClassicalFourthData.Bq 9729
    have hp : val WuPaper.ClassicalFourthData.Bq 9729 = (278237017960962:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 9729 = 278237017960962 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 9729 = (17729:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_9729
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 9730) ≤ val WuPaper.ClassicalFourthData.Bq 9730
    have hp : val WuPaper.ClassicalFourthData.Bq 9730 = (278237757184882:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 9730 = 278237757184882 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 9730 = (1773:ℝ)/400 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_9730
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 9731) ≤ val WuPaper.ClassicalFourthData.Bq 9731
    have hp : val WuPaper.ClassicalFourthData.Bq 9731 = (278238495128718:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 9731 = 278238495128718 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 9731 = (17731:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_9731
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 9732) ≤ val WuPaper.ClassicalFourthData.Bq 9732
    have hp : val WuPaper.ClassicalFourthData.Bq 9732 = (278239231792861:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 9732 = 278239231792861 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 9732 = (4433:ℝ)/1000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_9732
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 9733) ≤ val WuPaper.ClassicalFourthData.Bq 9733
    have hp : val WuPaper.ClassicalFourthData.Bq 9733 = (278239967177704:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 9733 = 278239967177704 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 9733 = (17733:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_9733
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 9734) ≤ val WuPaper.ClassicalFourthData.Bq 9734
    have hp : val WuPaper.ClassicalFourthData.Bq 9734 = (278240701283635:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 9734 = 278240701283635 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 9734 = (8867:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_9734
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 9735) ≤ val WuPaper.ClassicalFourthData.Bq 9735
    have hp : val WuPaper.ClassicalFourthData.Bq 9735 = (278241434111046:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 9735 = 278241434111046 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 9735 = (3547:ℝ)/800 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_9735
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 9736) ≤ val WuPaper.ClassicalFourthData.Bq 9736
    have hp : val WuPaper.ClassicalFourthData.Bq 9736 = (278242165660326:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 9736 = 278242165660326 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 9736 = (2217:ℝ)/500 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_9736
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 9737) ≤ val WuPaper.ClassicalFourthData.Bq 9737
    have hp : val WuPaper.ClassicalFourthData.Bq 9737 = (278242895931867:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 9737 = 278242895931867 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 9737 = (17737:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_9737
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 9738) ≤ val WuPaper.ClassicalFourthData.Bq 9738
    have hp : val WuPaper.ClassicalFourthData.Bq 9738 = (278243624926058:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 9738 = 278243624926058 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 9738 = (8869:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_9738
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 9739) ≤ val WuPaper.ClassicalFourthData.Bq 9739
    have hp : val WuPaper.ClassicalFourthData.Bq 9739 = (278244352643290:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 9739 = 278244352643290 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 9739 = (17739:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_9739
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 9740) ≤ val WuPaper.ClassicalFourthData.Bq 9740
    have hp : val WuPaper.ClassicalFourthData.Bq 9740 = (278245079083951:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 9740 = 278245079083951 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 9740 = (887:ℝ)/200 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_9740
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 9741) ≤ val WuPaper.ClassicalFourthData.Bq 9741
    have hp : val WuPaper.ClassicalFourthData.Bq 9741 = (278245804248432:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 9741 = 278245804248432 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 9741 = (17741:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_9741
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 9742) ≤ val WuPaper.ClassicalFourthData.Bq 9742
    have hp : val WuPaper.ClassicalFourthData.Bq 9742 = (278246528137123:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 9742 = 278246528137123 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 9742 = (8871:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_9742
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 9743) ≤ val WuPaper.ClassicalFourthData.Bq 9743
    have hp : val WuPaper.ClassicalFourthData.Bq 9743 = (278247250750412:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 9743 = 278247250750412 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 9743 = (17743:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_9743
end WuPaper.ClassicalFourthConditions
#print axioms WuPaper.ClassicalFourthConditions.Log_block_608

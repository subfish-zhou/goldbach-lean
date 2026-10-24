import WR2ClassicalFourthConditions
import WR2ClassicalFourthLogPoints292
noncomputable section
namespace WuPaper.ClassicalFourthConditions
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem Log_block_292 (j : Fin 16) (hj : 16*292+j.val < 10541) :
    WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 (16*292+j.val)) ≤ val WuPaper.ClassicalFourthData.Bq (16*292+j.val) := by
  fin_cases j
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 4672) ≤ val WuPaper.ClassicalFourthData.Bq 4672
    have hp : val WuPaper.ClassicalFourthData.Bq 4672 = (244256655169634:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 4672 = 244256655169634 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 4672 = (396:ℝ)/125 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_4672
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 4673) ≤ val WuPaper.ClassicalFourthData.Bq 4673
    have hp : val WuPaper.ClassicalFourthData.Bq 4673 = (244273775927540:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 4673 = 244273775927540 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 4673 = (12673:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_4673
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 4674) ≤ val WuPaper.ClassicalFourthData.Bq 4674
    have hp : val WuPaper.ClassicalFourthData.Bq 4674 = (244290889788002:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 4674 = 244290889788002 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 4674 = (6337:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_4674
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 4675) ≤ val WuPaper.ClassicalFourthData.Bq 4675
    have hp : val WuPaper.ClassicalFourthData.Bq 4675 = (244307996753620:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 4675 = 244307996753620 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 4675 = (507:ℝ)/160 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_4675
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 4676) ≤ val WuPaper.ClassicalFourthData.Bq 4676
    have hp : val WuPaper.ClassicalFourthData.Bq 4676 = (244325096826992:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 4676 = 244325096826992 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 4676 = (3169:ℝ)/1000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_4676
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 4677) ≤ val WuPaper.ClassicalFourthData.Bq 4677
    have hp : val WuPaper.ClassicalFourthData.Bq 4677 = (244342190010717:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 4677 = 244342190010717 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 4677 = (12677:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_4677
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 4678) ≤ val WuPaper.ClassicalFourthData.Bq 4678
    have hp : val WuPaper.ClassicalFourthData.Bq 4678 = (244359276307389:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 4678 = 244359276307389 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 4678 = (6339:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_4678
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 4679) ≤ val WuPaper.ClassicalFourthData.Bq 4679
    have hp : val WuPaper.ClassicalFourthData.Bq 4679 = (244376355719605:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 4679 = 244376355719605 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 4679 = (12679:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_4679
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 4680) ≤ val WuPaper.ClassicalFourthData.Bq 4680
    have hp : val WuPaper.ClassicalFourthData.Bq 4680 = (244393428249959:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 4680 = 244393428249959 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 4680 = (317:ℝ)/100 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_4680
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 4681) ≤ val WuPaper.ClassicalFourthData.Bq 4681
    have hp : val WuPaper.ClassicalFourthData.Bq 4681 = (244410493901043:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 4681 = 244410493901043 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 4681 = (12681:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_4681
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 4682) ≤ val WuPaper.ClassicalFourthData.Bq 4682
    have hp : val WuPaper.ClassicalFourthData.Bq 4682 = (244427552675450:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 4682 = 244427552675450 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 4682 = (6341:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_4682
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 4683) ≤ val WuPaper.ClassicalFourthData.Bq 4683
    have hp : val WuPaper.ClassicalFourthData.Bq 4683 = (244444604575769:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 4683 = 244444604575769 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 4683 = (12683:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_4683
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 4684) ≤ val WuPaper.ClassicalFourthData.Bq 4684
    have hp : val WuPaper.ClassicalFourthData.Bq 4684 = (244461649604591:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 4684 = 244461649604591 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 4684 = (3171:ℝ)/1000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_4684
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 4685) ≤ val WuPaper.ClassicalFourthData.Bq 4685
    have hp : val WuPaper.ClassicalFourthData.Bq 4685 = (244478687764503:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 4685 = 244478687764503 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 4685 = (2537:ℝ)/800 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_4685
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 4686) ≤ val WuPaper.ClassicalFourthData.Bq 4686
    have hp : val WuPaper.ClassicalFourthData.Bq 4686 = (244495719058093:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 4686 = 244495719058093 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 4686 = (6343:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_4686
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 4687) ≤ val WuPaper.ClassicalFourthData.Bq 4687
    have hp : val WuPaper.ClassicalFourthData.Bq 4687 = (244512743487947:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 4687 = 244512743487947 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 4687 = (12687:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_4687
end WuPaper.ClassicalFourthConditions
#print axioms WuPaper.ClassicalFourthConditions.Log_block_292

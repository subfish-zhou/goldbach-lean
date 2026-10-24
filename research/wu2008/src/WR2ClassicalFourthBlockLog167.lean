import WR2ClassicalFourthConditions
import WR2ClassicalFourthLogPoints167
noncomputable section
namespace WuPaper.ClassicalFourthConditions
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem Log_block_167 (j : Fin 16) (hj : 16*167+j.val < 10541) :
    WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 (16*167+j.val)) ≤ val WuPaper.ClassicalFourthData.Bq (16*167+j.val) := by
  fin_cases j
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 2672) ≤ val WuPaper.ClassicalFourthData.Bq 2672
    have hp : val WuPaper.ClassicalFourthData.Bq 2672 = (191763607172622:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 2672 = 191763607172622 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 2672 = (667:ℝ)/250 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_2672
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 2673) ≤ val WuPaper.ClassicalFourthData.Bq 2673
    have hp : val WuPaper.ClassicalFourthData.Bq 2673 = (191801807477403:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 2673 = 191801807477403 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 2673 = (10673:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_2673
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 2674) ≤ val WuPaper.ClassicalFourthData.Bq 2674
    have hp : val WuPaper.ClassicalFourthData.Bq 2674 = (191839992208841:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 2674 = 191839992208841 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 2674 = (5337:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_2674
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 2675) ≤ val WuPaper.ClassicalFourthData.Bq 2675
    have hp : val WuPaper.ClassicalFourthData.Bq 2675 = (191878161373836:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 2675 = 191878161373836 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 2675 = (427:ℝ)/160 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_2675
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 2676) ≤ val WuPaper.ClassicalFourthData.Bq 2676
    have hp : val WuPaper.ClassicalFourthData.Bq 2676 = (191916314979280:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 2676 = 191916314979280 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 2676 = (2669:ℝ)/1000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_2676
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 2677) ≤ val WuPaper.ClassicalFourthData.Bq 2677
    have hp : val WuPaper.ClassicalFourthData.Bq 2677 = (191954453032066:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 2677 = 191954453032066 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 2677 = (10677:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_2677
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 2678) ≤ val WuPaper.ClassicalFourthData.Bq 2678
    have hp : val WuPaper.ClassicalFourthData.Bq 2678 = (191992575539080:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 2678 = 191992575539080 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 2678 = (5339:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_2678
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 2679) ≤ val WuPaper.ClassicalFourthData.Bq 2679
    have hp : val WuPaper.ClassicalFourthData.Bq 2679 = (192030682507205:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 2679 = 192030682507205 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 2679 = (10679:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_2679
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 2680) ≤ val WuPaper.ClassicalFourthData.Bq 2680
    have hp : val WuPaper.ClassicalFourthData.Bq 2680 = (192068773943320:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 2680 = 192068773943320 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 2680 = (267:ℝ)/100 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_2680
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 2681) ≤ val WuPaper.ClassicalFourthData.Bq 2681
    have hp : val WuPaper.ClassicalFourthData.Bq 2681 = (192106849854302:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 2681 = 192106849854302 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 2681 = (10681:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_2681
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 2682) ≤ val WuPaper.ClassicalFourthData.Bq 2682
    have hp : val WuPaper.ClassicalFourthData.Bq 2682 = (192144910247023:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 2682 = 192144910247023 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 2682 = (5341:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_2682
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 2683) ≤ val WuPaper.ClassicalFourthData.Bq 2683
    have hp : val WuPaper.ClassicalFourthData.Bq 2683 = (192182955128351:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 2683 = 192182955128351 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 2683 = (10683:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_2683
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 2684) ≤ val WuPaper.ClassicalFourthData.Bq 2684
    have hp : val WuPaper.ClassicalFourthData.Bq 2684 = (192220984505151:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 2684 = 192220984505151 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 2684 = (2671:ℝ)/1000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_2684
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 2685) ≤ val WuPaper.ClassicalFourthData.Bq 2685
    have hp : val WuPaper.ClassicalFourthData.Bq 2685 = (192258998384283:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 2685 = 192258998384283 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 2685 = (2137:ℝ)/800 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_2685
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 2686) ≤ val WuPaper.ClassicalFourthData.Bq 2686
    have hp : val WuPaper.ClassicalFourthData.Bq 2686 = (192296996772606:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 2686 = 192296996772606 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 2686 = (5343:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_2686
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 2687) ≤ val WuPaper.ClassicalFourthData.Bq 2687
    have hp : val WuPaper.ClassicalFourthData.Bq 2687 = (192334979676973:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 2687 = 192334979676973 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 2687 = (10687:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_2687
end WuPaper.ClassicalFourthConditions
#print axioms WuPaper.ClassicalFourthConditions.Log_block_167

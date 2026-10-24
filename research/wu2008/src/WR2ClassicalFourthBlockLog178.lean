import WR2ClassicalFourthConditions
import WR2ClassicalFourthLogPoints178
noncomputable section
namespace WuPaper.ClassicalFourthConditions
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem Log_block_178 (j : Fin 16) (hj : 16*178+j.val < 10541) :
    WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 (16*178+j.val)) ≤ val WuPaper.ClassicalFourthData.Bq (16*178+j.val) := by
  fin_cases j
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 2848) ≤ val WuPaper.ClassicalFourthData.Bq 2848
    have hp : val WuPaper.ClassicalFourthData.Bq 2848 = (198253052256472:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 2848 = 198253052256472 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 2848 = (339:ℝ)/125 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_2848
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 2849) ≤ val WuPaper.ClassicalFourthData.Bq 2849
    have hp : val WuPaper.ClassicalFourthData.Bq 2849 = (198288614654209:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 2849 = 198288614654209 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 2849 = (10849:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_2849
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 2850) ≤ val WuPaper.ClassicalFourthData.Bq 2850
    have hp : val WuPaper.ClassicalFourthData.Bq 2850 = (198324162637510:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 2850 = 198324162637510 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 2850 = (217:ℝ)/80 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_2850
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 2851) ≤ val WuPaper.ClassicalFourthData.Bq 2851
    have hp : val WuPaper.ClassicalFourthData.Bq 2851 = (198359696212652:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 2851 = 198359696212652 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 2851 = (10851:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_2851
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 2852) ≤ val WuPaper.ClassicalFourthData.Bq 2852
    have hp : val WuPaper.ClassicalFourthData.Bq 2852 = (198395215385914:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 2852 = 198395215385914 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 2852 = (2713:ℝ)/1000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_2852
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 2853) ≤ val WuPaper.ClassicalFourthData.Bq 2853
    have hp : val WuPaper.ClassicalFourthData.Bq 2853 = (198430720163567:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 2853 = 198430720163567 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 2853 = (10853:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_2853
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 2854) ≤ val WuPaper.ClassicalFourthData.Bq 2854
    have hp : val WuPaper.ClassicalFourthData.Bq 2854 = (198466210551881:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 2854 = 198466210551881 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 2854 = (5427:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_2854
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 2855) ≤ val WuPaper.ClassicalFourthData.Bq 2855
    have hp : val WuPaper.ClassicalFourthData.Bq 2855 = (198501686557121:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 2855 = 198501686557121 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 2855 = (2171:ℝ)/800 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_2855
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 2856) ≤ val WuPaper.ClassicalFourthData.Bq 2856
    have hp : val WuPaper.ClassicalFourthData.Bq 2856 = (198537148185552:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 2856 = 198537148185552 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 2856 = (1357:ℝ)/500 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_2856
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 2857) ≤ val WuPaper.ClassicalFourthData.Bq 2857
    have hp : val WuPaper.ClassicalFourthData.Bq 2857 = (198572595443433:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 2857 = 198572595443433 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 2857 = (10857:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_2857
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 2858) ≤ val WuPaper.ClassicalFourthData.Bq 2858
    have hp : val WuPaper.ClassicalFourthData.Bq 2858 = (198608028337019:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 2858 = 198608028337019 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 2858 = (5429:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_2858
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 2859) ≤ val WuPaper.ClassicalFourthData.Bq 2859
    have hp : val WuPaper.ClassicalFourthData.Bq 2859 = (198643446872565:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 2859 = 198643446872565 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 2859 = (10859:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_2859
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 2860) ≤ val WuPaper.ClassicalFourthData.Bq 2860
    have hp : val WuPaper.ClassicalFourthData.Bq 2860 = (198678851056318:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 2860 = 198678851056318 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 2860 = (543:ℝ)/200 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_2860
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 2861) ≤ val WuPaper.ClassicalFourthData.Bq 2861
    have hp : val WuPaper.ClassicalFourthData.Bq 2861 = (198714240894527:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 2861 = 198714240894527 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 2861 = (10861:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_2861
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 2862) ≤ val WuPaper.ClassicalFourthData.Bq 2862
    have hp : val WuPaper.ClassicalFourthData.Bq 2862 = (198749616393434:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 2862 = 198749616393434 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 2862 = (5431:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_2862
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 2863) ≤ val WuPaper.ClassicalFourthData.Bq 2863
    have hp : val WuPaper.ClassicalFourthData.Bq 2863 = (198784977559278:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 2863 = 198784977559278 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 2863 = (10863:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_2863
end WuPaper.ClassicalFourthConditions
#print axioms WuPaper.ClassicalFourthConditions.Log_block_178

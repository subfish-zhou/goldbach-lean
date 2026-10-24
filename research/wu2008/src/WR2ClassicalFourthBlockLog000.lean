import WR2ClassicalFourthConditions
import WR2ClassicalFourthLogPoints000
noncomputable section
namespace WuPaper.ClassicalFourthConditions
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem Log_block_000 (j : Fin 16) (hj : 16*0+j.val < 10541) :
    WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 (16*0+j.val)) ≤ val WuPaper.ClassicalFourthData.Bq (16*0+j.val) := by
  fin_cases j
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 0) ≤ val WuPaper.ClassicalFourthData.Bq 0
    have hp : val WuPaper.ClassicalFourthData.Bq 0 = (0:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 0 = 0 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 0 = (2:ℝ)/1 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_0
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 1) ≤ val WuPaper.ClassicalFourthData.Bq 1
    have hp : val WuPaper.ClassicalFourthData.Bq 1 = (124968756510:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 1 = 124968756510 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 1 = (8001:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_1
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 2) ≤ val WuPaper.ClassicalFourthData.Bq 2
    have hp : val WuPaper.ClassicalFourthData.Bq 2 = (249875052063:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 2 = 249875052063 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 2 = (4001:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_2
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 3) ≤ val WuPaper.ClassicalFourthData.Bq 3
    have hp : val WuPaper.ClassicalFourthData.Bq 3 = (374718925676:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 3 = 374718925676 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 3 = (8003:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_3
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 4) ≤ val WuPaper.ClassicalFourthData.Bq 4
    have hp : val WuPaper.ClassicalFourthData.Bq 4 = (499500416334:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 4 = 499500416334 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 4 = (2001:ℝ)/1000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_4
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 5) ≤ val WuPaper.ClassicalFourthData.Bq 5
    have hp : val WuPaper.ClassicalFourthData.Bq 5 = (624219562990:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 5 = 624219562990 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 5 = (1601:ℝ)/800 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_5
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 6) ≤ val WuPaper.ClassicalFourthData.Bq 6
    have hp : val WuPaper.ClassicalFourthData.Bq 6 = (748876404565:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 6 = 748876404565 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 6 = (4003:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_6
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 7) ≤ val WuPaper.ClassicalFourthData.Bq 7
    have hp : val WuPaper.ClassicalFourthData.Bq 7 = (873470979951:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 7 = 873470979951 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 7 = (8007:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_7
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 8) ≤ val WuPaper.ClassicalFourthData.Bq 8
    have hp : val WuPaper.ClassicalFourthData.Bq 8 = (998003328009:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 8 = 998003328009 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 8 = (1001:ℝ)/500 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_8
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 9) ≤ val WuPaper.ClassicalFourthData.Bq 9
    have hp : val WuPaper.ClassicalFourthData.Bq 9 = (1122473487567:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 9 = 1122473487567 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 9 = (8009:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_9
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 10) ≤ val WuPaper.ClassicalFourthData.Bq 10
    have hp : val WuPaper.ClassicalFourthData.Bq 10 = (1246881497422:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 10 = 1246881497422 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 10 = (801:ℝ)/400 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_10
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 11) ≤ val WuPaper.ClassicalFourthData.Bq 11
    have hp : val WuPaper.ClassicalFourthData.Bq 11 = (1371227396343:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 11 = 1371227396343 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 11 = (8011:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_11
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 12) ≤ val WuPaper.ClassicalFourthData.Bq 12
    have hp : val WuPaper.ClassicalFourthData.Bq 12 = (1495511223065:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 12 = 1495511223065 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 12 = (2003:ℝ)/1000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_12
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 13) ≤ val WuPaper.ClassicalFourthData.Bq 13
    have hp : val WuPaper.ClassicalFourthData.Bq 13 = (1619733016294:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 13 = 1619733016294 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 13 = (8013:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_13
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 14) ≤ val WuPaper.ClassicalFourthData.Bq 14
    have hp : val WuPaper.ClassicalFourthData.Bq 14 = (1743892814703:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 14 = 1743892814703 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 14 = (4007:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_14
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 15) ≤ val WuPaper.ClassicalFourthData.Bq 15
    have hp : val WuPaper.ClassicalFourthData.Bq 15 = (1867990656936:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 15 = 1867990656936 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 15 = (1603:ℝ)/800 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_15
end WuPaper.ClassicalFourthConditions
#print axioms WuPaper.ClassicalFourthConditions.Log_block_000

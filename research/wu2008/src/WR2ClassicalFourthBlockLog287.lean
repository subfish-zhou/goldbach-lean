import WR2ClassicalFourthConditions
import WR2ClassicalFourthLogPoints287
noncomputable section
namespace WuPaper.ClassicalFourthConditions
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem Log_block_287 (j : Fin 16) (hj : 16*287+j.val < 10541) :
    WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 (16*287+j.val)) ≤ val WuPaper.ClassicalFourthData.Bq (16*287+j.val) := by
  fin_cases j
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 4592) ≤ val WuPaper.ClassicalFourthData.Bq 4592
    have hp : val WuPaper.ClassicalFourthData.Bq 4592 = (242864414436665:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 4592 = 242864414436665 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 4592 = (787:ℝ)/250 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_4592
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 4593) ≤ val WuPaper.ClassicalFourthData.Bq 4593
    have hp : val WuPaper.ClassicalFourthData.Bq 4593 = (242882095516937:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 4593 = 242882095516937 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 4593 = (12593:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_4593
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 4594) ≤ val WuPaper.ClassicalFourthData.Bq 4594
    have hp : val WuPaper.ClassicalFourthData.Bq 4594 = (242899769487983:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 4594 = 242899769487983 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 4594 = (6297:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_4594
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 4595) ≤ val WuPaper.ClassicalFourthData.Bq 4595
    have hp : val WuPaper.ClassicalFourthData.Bq 4595 = (242917436352497:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 4595 = 242917436352497 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 4595 = (2519:ℝ)/800 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_4595
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 4596) ≤ val WuPaper.ClassicalFourthData.Bq 4596
    have hp : val WuPaper.ClassicalFourthData.Bq 4596 = (242935096113171:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 4596 = 242935096113171 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 4596 = (3149:ℝ)/1000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_4596
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 4597) ≤ val WuPaper.ClassicalFourthData.Bq 4597
    have hp : val WuPaper.ClassicalFourthData.Bq 4597 = (242952748772698:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 4597 = 242952748772698 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 4597 = (12597:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_4597
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 4598) ≤ val WuPaper.ClassicalFourthData.Bq 4598
    have hp : val WuPaper.ClassicalFourthData.Bq 4598 = (242970394333768:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 4598 = 242970394333768 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 4598 = (6299:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_4598
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 4599) ≤ val WuPaper.ClassicalFourthData.Bq 4599
    have hp : val WuPaper.ClassicalFourthData.Bq 4599 = (242988032799070:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 4599 = 242988032799070 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 4599 = (12599:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_4599
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 4600) ≤ val WuPaper.ClassicalFourthData.Bq 4600
    have hp : val WuPaper.ClassicalFourthData.Bq 4600 = (243005664171293:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 4600 = 243005664171293 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 4600 = (63:ℝ)/20 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_4600
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 4601) ≤ val WuPaper.ClassicalFourthData.Bq 4601
    have hp : val WuPaper.ClassicalFourthData.Bq 4601 = (243023288453124:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 4601 = 243023288453124 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 4601 = (12601:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_4601
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 4602) ≤ val WuPaper.ClassicalFourthData.Bq 4602
    have hp : val WuPaper.ClassicalFourthData.Bq 4602 = (243040905647248:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 4602 = 243040905647248 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 4602 = (6301:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_4602
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 4603) ≤ val WuPaper.ClassicalFourthData.Bq 4603
    have hp : val WuPaper.ClassicalFourthData.Bq 4603 = (243058515756351:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 4603 = 243058515756351 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 4603 = (12603:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_4603
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 4604) ≤ val WuPaper.ClassicalFourthData.Bq 4604
    have hp : val WuPaper.ClassicalFourthData.Bq 4604 = (243076118783115:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 4604 = 243076118783115 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 4604 = (3151:ℝ)/1000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_4604
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 4605) ≤ val WuPaper.ClassicalFourthData.Bq 4605
    have hp : val WuPaper.ClassicalFourthData.Bq 4605 = (243093714730223:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 4605 = 243093714730223 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 4605 = (2521:ℝ)/800 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_4605
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 4606) ≤ val WuPaper.ClassicalFourthData.Bq 4606
    have hp : val WuPaper.ClassicalFourthData.Bq 4606 = (243111303600355:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 4606 = 243111303600355 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 4606 = (6303:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_4606
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 4607) ≤ val WuPaper.ClassicalFourthData.Bq 4607
    have hp : val WuPaper.ClassicalFourthData.Bq 4607 = (243128885396192:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 4607 = 243128885396192 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 4607 = (12607:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_4607
end WuPaper.ClassicalFourthConditions
#print axioms WuPaper.ClassicalFourthConditions.Log_block_287

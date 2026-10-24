import WR2ClassicalFourthConditions
import WR2ClassicalFourthLogPoints315
noncomputable section
namespace WuPaper.ClassicalFourthConditions
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem Log_block_315 (j : Fin 16) (hj : 16*315+j.val < 10541) :
    WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 (16*315+j.val)) ≤ val WuPaper.ClassicalFourthData.Bq (16*315+j.val) := by
  fin_cases j
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 5040) ≤ val WuPaper.ClassicalFourthData.Bq 5040
    have hp : val WuPaper.ClassicalFourthData.Bq 5040 = (250111905915398:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 5040 = 250111905915398 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 5040 = (163:ℝ)/50 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_5040
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 5041) ≤ val WuPaper.ClassicalFourthData.Bq 5041
    have hp : val WuPaper.ClassicalFourthData.Bq 5041 = (250126654899269:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 5041 = 250126654899269 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 5041 = (13041:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_5041
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 5042) ≤ val WuPaper.ClassicalFourthData.Bq 5042
    have hp : val WuPaper.ClassicalFourthData.Bq 5042 = (250141397869200:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 5042 = 250141397869200 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 5042 = (6521:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_5042
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 5043) ≤ val WuPaper.ClassicalFourthData.Bq 5043
    have hp : val WuPaper.ClassicalFourthData.Bq 5043 = (250156134827403:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 5043 = 250156134827403 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 5043 = (13043:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_5043
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 5044) ≤ val WuPaper.ClassicalFourthData.Bq 5044
    have hp : val WuPaper.ClassicalFourthData.Bq 5044 = (250170865776092:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 5044 = 250170865776092 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 5044 = (3261:ℝ)/1000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_5044
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 5045) ≤ val WuPaper.ClassicalFourthData.Bq 5045
    have hp : val WuPaper.ClassicalFourthData.Bq 5045 = (250185590717476:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 5045 = 250185590717476 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 5045 = (2609:ℝ)/800 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_5045
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 5046) ≤ val WuPaper.ClassicalFourthData.Bq 5046
    have hp : val WuPaper.ClassicalFourthData.Bq 5046 = (250200309653768:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 5046 = 250200309653768 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 5046 = (6523:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_5046
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 5047) ≤ val WuPaper.ClassicalFourthData.Bq 5047
    have hp : val WuPaper.ClassicalFourthData.Bq 5047 = (250215022587174:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 5047 = 250215022587174 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 5047 = (13047:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_5047
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 5048) ≤ val WuPaper.ClassicalFourthData.Bq 5048
    have hp : val WuPaper.ClassicalFourthData.Bq 5048 = (250229729519905:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 5048 = 250229729519905 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 5048 = (1631:ℝ)/500 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_5048
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 5049) ≤ val WuPaper.ClassicalFourthData.Bq 5049
    have hp : val WuPaper.ClassicalFourthData.Bq 5049 = (250244430454167:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 5049 = 250244430454167 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 5049 = (13049:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_5049
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 5050) ≤ val WuPaper.ClassicalFourthData.Bq 5050
    have hp : val WuPaper.ClassicalFourthData.Bq 5050 = (250259125392167:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 5050 = 250259125392167 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 5050 = (261:ℝ)/80 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_5050
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 5051) ≤ val WuPaper.ClassicalFourthData.Bq 5051
    have hp : val WuPaper.ClassicalFourthData.Bq 5051 = (250273814336111:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 5051 = 250273814336111 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 5051 = (13051:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_5051
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 5052) ≤ val WuPaper.ClassicalFourthData.Bq 5052
    have hp : val WuPaper.ClassicalFourthData.Bq 5052 = (250288497288202:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 5052 = 250288497288202 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 5052 = (3263:ℝ)/1000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_5052
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 5053) ≤ val WuPaper.ClassicalFourthData.Bq 5053
    have hp : val WuPaper.ClassicalFourthData.Bq 5053 = (250303174250644:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 5053 = 250303174250644 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 5053 = (13053:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_5053
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 5054) ≤ val WuPaper.ClassicalFourthData.Bq 5054
    have hp : val WuPaper.ClassicalFourthData.Bq 5054 = (250317845225641:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 5054 = 250317845225641 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 5054 = (6527:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_5054
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 5055) ≤ val WuPaper.ClassicalFourthData.Bq 5055
    have hp : val WuPaper.ClassicalFourthData.Bq 5055 = (250332510215393:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 5055 = 250332510215393 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 5055 = (2611:ℝ)/800 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_5055
end WuPaper.ClassicalFourthConditions
#print axioms WuPaper.ClassicalFourthConditions.Log_block_315

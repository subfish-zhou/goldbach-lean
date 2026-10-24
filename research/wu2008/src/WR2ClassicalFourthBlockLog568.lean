import WR2ClassicalFourthConditions
import WR2ClassicalFourthLogPoints568
noncomputable section
namespace WuPaper.ClassicalFourthConditions
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem Log_block_568 (j : Fin 16) (hj : 16*568+j.val < 10541) :
    WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 (16*568+j.val)) ≤ val WuPaper.ClassicalFourthData.Bq (16*568+j.val) := by
  fin_cases j
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 9088) ≤ val WuPaper.ClassicalFourthData.Bq 9088
    have hp : val WuPaper.ClassicalFourthData.Bq 9088 = (277481605515304:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 9088 = 277481605515304 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 9088 = (534:ℝ)/125 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_9088
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 9089) ≤ val WuPaper.ClassicalFourthData.Bq 9089
    have hp : val WuPaper.ClassicalFourthData.Bq 9089 = (277483251614631:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 9089 = 277483251614631 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 9089 = (17089:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_9089
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 9090) ≤ val WuPaper.ClassicalFourthData.Bq 9090
    have hp : val WuPaper.ClassicalFourthData.Bq 9090 = (277484896155148:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 9090 = 277484896155148 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 9090 = (1709:ℝ)/400 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_9090
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 9091) ≤ val WuPaper.ClassicalFourthData.Bq 9091
    have hp : val WuPaper.ClassicalFourthData.Bq 9091 = (277486539137338:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 9091 = 277486539137338 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 9091 = (17091:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_9091
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 9092) ≤ val WuPaper.ClassicalFourthData.Bq 9092
    have hp : val WuPaper.ClassicalFourthData.Bq 9092 = (277488180561683:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 9092 = 277488180561683 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 9092 = (4273:ℝ)/1000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_9092
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 9093) ≤ val WuPaper.ClassicalFourthData.Bq 9093
    have hp : val WuPaper.ClassicalFourthData.Bq 9093 = (277489820428664:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 9093 = 277489820428664 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 9093 = (17093:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_9093
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 9094) ≤ val WuPaper.ClassicalFourthData.Bq 9094
    have hp : val WuPaper.ClassicalFourthData.Bq 9094 = (277491458738765:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 9094 = 277491458738765 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 9094 = (8547:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_9094
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 9095) ≤ val WuPaper.ClassicalFourthData.Bq 9095
    have hp : val WuPaper.ClassicalFourthData.Bq 9095 = (277493095492465:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 9095 = 277493095492465 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 9095 = (3419:ℝ)/800 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_9095
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 9096) ≤ val WuPaper.ClassicalFourthData.Bq 9096
    have hp : val WuPaper.ClassicalFourthData.Bq 9096 = (277494730690248:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 9096 = 277494730690248 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 9096 = (2137:ℝ)/500 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_9096
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 9097) ≤ val WuPaper.ClassicalFourthData.Bq 9097
    have hp : val WuPaper.ClassicalFourthData.Bq 9097 = (277496364332594:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 9097 = 277496364332594 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 9097 = (17097:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_9097
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 9098) ≤ val WuPaper.ClassicalFourthData.Bq 9098
    have hp : val WuPaper.ClassicalFourthData.Bq 9098 = (277497996419984:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 9098 = 277497996419984 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 9098 = (8549:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_9098
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 9099) ≤ val WuPaper.ClassicalFourthData.Bq 9099
    have hp : val WuPaper.ClassicalFourthData.Bq 9099 = (277499626952900:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 9099 = 277499626952900 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 9099 = (17099:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_9099
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 9100) ≤ val WuPaper.ClassicalFourthData.Bq 9100
    have hp : val WuPaper.ClassicalFourthData.Bq 9100 = (277501255931823:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 9100 = 277501255931823 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 9100 = (171:ℝ)/40 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_9100
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 9101) ≤ val WuPaper.ClassicalFourthData.Bq 9101
    have hp : val WuPaper.ClassicalFourthData.Bq 9101 = (277502883357232:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 9101 = 277502883357232 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 9101 = (17101:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_9101
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 9102) ≤ val WuPaper.ClassicalFourthData.Bq 9102
    have hp : val WuPaper.ClassicalFourthData.Bq 9102 = (277504509229610:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 9102 = 277504509229610 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 9102 = (8551:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_9102
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 9103) ≤ val WuPaper.ClassicalFourthData.Bq 9103
    have hp : val WuPaper.ClassicalFourthData.Bq 9103 = (277506133549435:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 9103 = 277506133549435 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 9103 = (17103:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_9103
end WuPaper.ClassicalFourthConditions
#print axioms WuPaper.ClassicalFourthConditions.Log_block_568

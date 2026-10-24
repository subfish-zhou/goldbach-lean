import WR2ClassicalFourthConditions
import WR2ClassicalFourthLogPoints256
noncomputable section
namespace WuPaper.ClassicalFourthConditions
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem Log_block_256 (j : Fin 16) (hj : 16*256+j.val < 10541) :
    WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 (16*256+j.val)) ≤ val WuPaper.ClassicalFourthData.Bq (16*256+j.val) := by
  fin_cases j
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 4096) ≤ val WuPaper.ClassicalFourthData.Bq 4096
    have hp : val WuPaper.ClassicalFourthData.Bq 4096 = (233159970709398:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 4096 = 233159970709398 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 4096 = (378:ℝ)/125 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_4096
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 4097) ≤ val WuPaper.ClassicalFourthData.Bq 4097
    have hp : val WuPaper.ClassicalFourthData.Bq 4097 = (233181536441792:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 4097 = 233181536441792 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 4097 = (12097:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_4097
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 4098) ≤ val WuPaper.ClassicalFourthData.Bq 4098
    have hp : val WuPaper.ClassicalFourthData.Bq 4098 = (233203093565905:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 4098 = 233203093565905 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 4098 = (6049:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_4098
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 4099) ≤ val WuPaper.ClassicalFourthData.Bq 4099
    have hp : val WuPaper.ClassicalFourthData.Bq 4099 = (233224642085119:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 4099 = 233224642085119 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 4099 = (12099:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_4099
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 4100) ≤ val WuPaper.ClassicalFourthData.Bq 4100
    have hp : val WuPaper.ClassicalFourthData.Bq 4100 = (233246182002811:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 4100 = 233246182002811 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 4100 = (121:ℝ)/40 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_4100
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 4101) ≤ val WuPaper.ClassicalFourthData.Bq 4101
    have hp : val WuPaper.ClassicalFourthData.Bq 4101 = (233267713322359:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 4101 = 233267713322359 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 4101 = (12101:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_4101
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 4102) ≤ val WuPaper.ClassicalFourthData.Bq 4102
    have hp : val WuPaper.ClassicalFourthData.Bq 4102 = (233289236047136:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 4102 = 233289236047136 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 4102 = (6051:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_4102
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 4103) ≤ val WuPaper.ClassicalFourthData.Bq 4103
    have hp : val WuPaper.ClassicalFourthData.Bq 4103 = (233310750180517:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 4103 = 233310750180517 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 4103 = (12103:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_4103
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 4104) ≤ val WuPaper.ClassicalFourthData.Bq 4104
    have hp : val WuPaper.ClassicalFourthData.Bq 4104 = (233332255725873:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 4104 = 233332255725873 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 4104 = (1513:ℝ)/500 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_4104
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 4105) ≤ val WuPaper.ClassicalFourthData.Bq 4105
    have hp : val WuPaper.ClassicalFourthData.Bq 4105 = (233353752686576:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 4105 = 233353752686576 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 4105 = (2421:ℝ)/800 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_4105
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 4106) ≤ val WuPaper.ClassicalFourthData.Bq 4106
    have hp : val WuPaper.ClassicalFourthData.Bq 4106 = (233375241065993:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 4106 = 233375241065993 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 4106 = (6053:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_4106
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 4107) ≤ val WuPaper.ClassicalFourthData.Bq 4107
    have hp : val WuPaper.ClassicalFourthData.Bq 4107 = (233396720867492:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 4107 = 233396720867492 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 4107 = (12107:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_4107
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 4108) ≤ val WuPaper.ClassicalFourthData.Bq 4108
    have hp : val WuPaper.ClassicalFourthData.Bq 4108 = (233418192094438:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 4108 = 233418192094438 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 4108 = (3027:ℝ)/1000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_4108
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 4109) ≤ val WuPaper.ClassicalFourthData.Bq 4109
    have hp : val WuPaper.ClassicalFourthData.Bq 4109 = (233439654750196:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 4109 = 233439654750196 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 4109 = (12109:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_4109
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 4110) ≤ val WuPaper.ClassicalFourthData.Bq 4110
    have hp : val WuPaper.ClassicalFourthData.Bq 4110 = (233461108838128:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 4110 = 233461108838128 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 4110 = (1211:ℝ)/400 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_4110
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 4111) ≤ val WuPaper.ClassicalFourthData.Bq 4111
    have hp : val WuPaper.ClassicalFourthData.Bq 4111 = (233482554361595:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 4111 = 233482554361595 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 4111 = (12111:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_4111
end WuPaper.ClassicalFourthConditions
#print axioms WuPaper.ClassicalFourthConditions.Log_block_256

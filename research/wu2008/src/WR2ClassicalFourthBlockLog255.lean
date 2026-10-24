import WR2ClassicalFourthConditions
import WR2ClassicalFourthLogPoints255
noncomputable section
namespace WuPaper.ClassicalFourthConditions
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem Log_block_255 (j : Fin 16) (hj : 16*255+j.val < 10541) :
    WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 (16*255+j.val)) ≤ val WuPaper.ClassicalFourthData.Bq (16*255+j.val) := by
  fin_cases j
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 4080) ≤ val WuPaper.ClassicalFourthData.Bq 4080
    have hp : val WuPaper.ClassicalFourthData.Bq 4080 = (232813745501031:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 4080 = 232813745501031 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 4080 = (151:ℝ)/50 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_4080
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 4081) ≤ val WuPaper.ClassicalFourthData.Bq 4081
    have hp : val WuPaper.ClassicalFourthData.Bq 4081 = (232835449426843:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 4081 = 232835449426843 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 4081 = (12081:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_4081
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 4082) ≤ val WuPaper.ClassicalFourthData.Bq 4082
    have hp : val WuPaper.ClassicalFourthData.Bq 4082 = (232857144690082:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 4082 = 232857144690082 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 4082 = (6041:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_4082
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 4083) ≤ val WuPaper.ClassicalFourthData.Bq 4083
    have hp : val WuPaper.ClassicalFourthData.Bq 4083 = (232878831294155:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 4083 = 232878831294155 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 4083 = (12083:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_4083
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 4084) ≤ val WuPaper.ClassicalFourthData.Bq 4084
    have hp : val WuPaper.ClassicalFourthData.Bq 4084 = (232900509242465:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 4084 = 232900509242465 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 4084 = (3021:ℝ)/1000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_4084
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 4085) ≤ val WuPaper.ClassicalFourthData.Bq 4085
    have hp : val WuPaper.ClassicalFourthData.Bq 4085 = (232922178538413:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 4085 = 232922178538413 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 4085 = (2417:ℝ)/800 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_4085
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 4086) ≤ val WuPaper.ClassicalFourthData.Bq 4086
    have hp : val WuPaper.ClassicalFourthData.Bq 4086 = (232943839185401:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 4086 = 232943839185401 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 4086 = (6043:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_4086
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 4087) ≤ val WuPaper.ClassicalFourthData.Bq 4087
    have hp : val WuPaper.ClassicalFourthData.Bq 4087 = (232965491186827:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 4087 = 232965491186827 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 4087 = (12087:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_4087
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 4088) ≤ val WuPaper.ClassicalFourthData.Bq 4088
    have hp : val WuPaper.ClassicalFourthData.Bq 4088 = (232987134546089:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 4088 = 232987134546089 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 4088 = (1511:ℝ)/500 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_4088
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 4089) ≤ val WuPaper.ClassicalFourthData.Bq 4089
    have hp : val WuPaper.ClassicalFourthData.Bq 4089 = (233008769266582:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 4089 = 233008769266582 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 4089 = (12089:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_4089
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 4090) ≤ val WuPaper.ClassicalFourthData.Bq 4090
    have hp : val WuPaper.ClassicalFourthData.Bq 4090 = (233030395351699:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 4090 = 233030395351699 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 4090 = (1209:ℝ)/400 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_4090
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 4091) ≤ val WuPaper.ClassicalFourthData.Bq 4091
    have hp : val WuPaper.ClassicalFourthData.Bq 4091 = (233052012804835:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 4091 = 233052012804835 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 4091 = (12091:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_4091
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 4092) ≤ val WuPaper.ClassicalFourthData.Bq 4092
    have hp : val WuPaper.ClassicalFourthData.Bq 4092 = (233073621629378:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 4092 = 233073621629378 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 4092 = (3023:ℝ)/1000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_4092
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 4093) ≤ val WuPaper.ClassicalFourthData.Bq 4093
    have hp : val WuPaper.ClassicalFourthData.Bq 4093 = (233095221828719:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 4093 = 233095221828719 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 4093 = (12093:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_4093
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 4094) ≤ val WuPaper.ClassicalFourthData.Bq 4094
    have hp : val WuPaper.ClassicalFourthData.Bq 4094 = (233116813406246:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 4094 = 233116813406246 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 4094 = (6047:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_4094
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 4095) ≤ val WuPaper.ClassicalFourthData.Bq 4095
    have hp : val WuPaper.ClassicalFourthData.Bq 4095 = (233138396365344:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 4095 = 233138396365344 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 4095 = (2419:ℝ)/800 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_4095
end WuPaper.ClassicalFourthConditions
#print axioms WuPaper.ClassicalFourthConditions.Log_block_255

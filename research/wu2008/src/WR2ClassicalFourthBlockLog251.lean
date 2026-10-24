import WR2ClassicalFourthConditions
import WR2ClassicalFourthLogPoints251
noncomputable section
namespace WuPaper.ClassicalFourthConditions
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem Log_block_251 (j : Fin 16) (hj : 16*251+j.val < 10541) :
    WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 (16*251+j.val)) ≤ val WuPaper.ClassicalFourthData.Bq (16*251+j.val) := by
  fin_cases j
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 4016) ≤ val WuPaper.ClassicalFourthData.Bq 4016
    have hp : val WuPaper.ClassicalFourthData.Bq 4016 = (231406519048808:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 4016 = 231406519048808 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 4016 = (751:ℝ)/250 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_4016
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 4017) ≤ val WuPaper.ClassicalFourthData.Bq 4017
    have hp : val WuPaper.ClassicalFourthData.Bq 4017 = (231428784535550:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 4017 = 231428784535550 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 4017 = (12017:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_4017
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 4018) ≤ val WuPaper.ClassicalFourthData.Bq 4018
    have hp : val WuPaper.ClassicalFourthData.Bq 4018 = (231451041138434:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 4018 = 231451041138434 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 4018 = (6009:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_4018
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 4019) ≤ val WuPaper.ClassicalFourthData.Bq 4019
    have hp : val WuPaper.ClassicalFourthData.Bq 4019 = (231473288860971:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 4019 = 231473288860971 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 4019 = (12019:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_4019
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 4020) ≤ val WuPaper.ClassicalFourthData.Bq 4020
    have hp : val WuPaper.ClassicalFourthData.Bq 4020 = (231495527706667:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 4020 = 231495527706667 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 4020 = (601:ℝ)/200 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_4020
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 4021) ≤ val WuPaper.ClassicalFourthData.Bq 4021
    have hp : val WuPaper.ClassicalFourthData.Bq 4021 = (231517757679028:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 4021 = 231517757679028 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 4021 = (12021:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_4021
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 4022) ≤ val WuPaper.ClassicalFourthData.Bq 4022
    have hp : val WuPaper.ClassicalFourthData.Bq 4022 = (231539978781558:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 4022 = 231539978781558 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 4022 = (6011:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_4022
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 4023) ≤ val WuPaper.ClassicalFourthData.Bq 4023
    have hp : val WuPaper.ClassicalFourthData.Bq 4023 = (231562191017759:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 4023 = 231562191017759 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 4023 = (12023:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_4023
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 4024) ≤ val WuPaper.ClassicalFourthData.Bq 4024
    have hp : val WuPaper.ClassicalFourthData.Bq 4024 = (231584394391133:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 4024 = 231584394391133 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 4024 = (1503:ℝ)/500 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_4024
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 4025) ≤ val WuPaper.ClassicalFourthData.Bq 4025
    have hp : val WuPaper.ClassicalFourthData.Bq 4025 = (231606588905178:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 4025 = 231606588905178 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 4025 = (481:ℝ)/160 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_4025
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 4026) ≤ val WuPaper.ClassicalFourthData.Bq 4026
    have hp : val WuPaper.ClassicalFourthData.Bq 4026 = (231628774563391:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 4026 = 231628774563391 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 4026 = (6013:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_4026
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 4027) ≤ val WuPaper.ClassicalFourthData.Bq 4027
    have hp : val WuPaper.ClassicalFourthData.Bq 4027 = (231650951369269:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 4027 = 231650951369269 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 4027 = (12027:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_4027
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 4028) ≤ val WuPaper.ClassicalFourthData.Bq 4028
    have hp : val WuPaper.ClassicalFourthData.Bq 4028 = (231673119326306:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 4028 = 231673119326306 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 4028 = (3007:ℝ)/1000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_4028
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 4029) ≤ val WuPaper.ClassicalFourthData.Bq 4029
    have hp : val WuPaper.ClassicalFourthData.Bq 4029 = (231695278437994:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 4029 = 231695278437994 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 4029 = (12029:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_4029
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 4030) ≤ val WuPaper.ClassicalFourthData.Bq 4030
    have hp : val WuPaper.ClassicalFourthData.Bq 4030 = (231717428707824:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 4030 = 231717428707824 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 4030 = (1203:ℝ)/400 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_4030
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 4031) ≤ val WuPaper.ClassicalFourthData.Bq 4031
    have hp : val WuPaper.ClassicalFourthData.Bq 4031 = (231739570139286:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 4031 = 231739570139286 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 4031 = (12031:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_4031
end WuPaper.ClassicalFourthConditions
#print axioms WuPaper.ClassicalFourthConditions.Log_block_251

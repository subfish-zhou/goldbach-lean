import WR2ClassicalFourthConditions
import WR2ClassicalFourthLogPoints388
noncomputable section
namespace WuPaper.ClassicalFourthConditions
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem Log_block_388 (j : Fin 16) (hj : 16*388+j.val < 10541) :
    WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 (16*388+j.val)) ≤ val WuPaper.ClassicalFourthData.Bq (16*388+j.val) := by
  fin_cases j
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 6208) ≤ val WuPaper.ClassicalFourthData.Bq 6208
    have hp : val WuPaper.ClassicalFourthData.Bq 6208 = (263760519561536:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 6208 = 263760519561536 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 6208 = (444:ℝ)/125 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_6208
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 6209) ≤ val WuPaper.ClassicalFourthData.Bq 6209
    have hp : val WuPaper.ClassicalFourthData.Bq 6209 = (263769532850171:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 6209 = 263769532850171 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 6209 = (14209:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_6209
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 6210) ≤ val WuPaper.ClassicalFourthData.Bq 6210
    have hp : val WuPaper.ClassicalFourthData.Bq 6210 = (263778542169378:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 6210 = 263778542169378 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 6210 = (1421:ℝ)/400 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_6210
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 6211) ≤ val WuPaper.ClassicalFourthData.Bq 6211
    have hp : val WuPaper.ClassicalFourthData.Bq 6211 = (263787547520524:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 6211 = 263787547520524 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 6211 = (14211:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_6211
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 6212) ≤ val WuPaper.ClassicalFourthData.Bq 6212
    have hp : val WuPaper.ClassicalFourthData.Bq 6212 = (263796548904976:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 6212 = 263796548904976 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 6212 = (3553:ℝ)/1000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_6212
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 6213) ≤ val WuPaper.ClassicalFourthData.Bq 6213
    have hp : val WuPaper.ClassicalFourthData.Bq 6213 = (263805546324099:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 6213 = 263805546324099 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 6213 = (14213:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_6213
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 6214) ≤ val WuPaper.ClassicalFourthData.Bq 6214
    have hp : val WuPaper.ClassicalFourthData.Bq 6214 = (263814539779258:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 6214 = 263814539779258 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 6214 = (7107:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_6214
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 6215) ≤ val WuPaper.ClassicalFourthData.Bq 6215
    have hp : val WuPaper.ClassicalFourthData.Bq 6215 = (263823529271819:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 6215 = 263823529271819 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 6215 = (2843:ℝ)/800 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_6215
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 6216) ≤ val WuPaper.ClassicalFourthData.Bq 6216
    have hp : val WuPaper.ClassicalFourthData.Bq 6216 = (263832514803146:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 6216 = 263832514803146 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 6216 = (1777:ℝ)/500 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_6216
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 6217) ≤ val WuPaper.ClassicalFourthData.Bq 6217
    have hp : val WuPaper.ClassicalFourthData.Bq 6217 = (263841496374602:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 6217 = 263841496374602 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 6217 = (14217:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_6217
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 6218) ≤ val WuPaper.ClassicalFourthData.Bq 6218
    have hp : val WuPaper.ClassicalFourthData.Bq 6218 = (263850473987551:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 6218 = 263850473987551 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 6218 = (7109:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_6218
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 6219) ≤ val WuPaper.ClassicalFourthData.Bq 6219
    have hp : val WuPaper.ClassicalFourthData.Bq 6219 = (263859447643354:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 6219 = 263859447643354 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 6219 = (14219:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_6219
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 6220) ≤ val WuPaper.ClassicalFourthData.Bq 6220
    have hp : val WuPaper.ClassicalFourthData.Bq 6220 = (263868417343376:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 6220 = 263868417343376 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 6220 = (711:ℝ)/200 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_6220
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 6221) ≤ val WuPaper.ClassicalFourthData.Bq 6221
    have hp : val WuPaper.ClassicalFourthData.Bq 6221 = (263877383088976:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 6221 = 263877383088976 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 6221 = (14221:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_6221
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 6222) ≤ val WuPaper.ClassicalFourthData.Bq 6222
    have hp : val WuPaper.ClassicalFourthData.Bq 6222 = (263886344881516:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 6222 = 263886344881516 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 6222 = (7111:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_6222
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 6223) ≤ val WuPaper.ClassicalFourthData.Bq 6223
    have hp : val WuPaper.ClassicalFourthData.Bq 6223 = (263895302722357:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 6223 = 263895302722357 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 6223 = (14223:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_6223
end WuPaper.ClassicalFourthConditions
#print axioms WuPaper.ClassicalFourthConditions.Log_block_388

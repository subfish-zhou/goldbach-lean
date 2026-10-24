import WR2ClassicalFourthConditions
import WR2ClassicalFourthLogPoints575
noncomputable section
namespace WuPaper.ClassicalFourthConditions
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem Log_block_575 (j : Fin 16) (hj : 16*575+j.val < 10541) :
    WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 (16*575+j.val)) ≤ val WuPaper.ClassicalFourthData.Bq (16*575+j.val) := by
  fin_cases j
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 9200) ≤ val WuPaper.ClassicalFourthData.Bq 9200
    have hp : val WuPaper.ClassicalFourthData.Bq 9200 = (277656388022759:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 9200 = 277656388022759 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 9200 = (43:ℝ)/10 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_9200
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 9201) ≤ val WuPaper.ClassicalFourthData.Bq 9201
    have hp : val WuPaper.ClassicalFourthData.Bq 9201 = (277657862497345:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 9201 = 277657862497345 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 9201 = (17201:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_9201
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 9202) ≤ val WuPaper.ClassicalFourthData.Bq 9202
    have hp : val WuPaper.ClassicalFourthData.Bq 9202 = (277659335466157:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 9202 = 277659335466157 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 9202 = (8601:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_9202
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 9203) ≤ val WuPaper.ClassicalFourthData.Bq 9203
    have hp : val WuPaper.ClassicalFourthData.Bq 9203 = (277660806929660:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 9203 = 277660806929660 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 9203 = (17203:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_9203
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 9204) ≤ val WuPaper.ClassicalFourthData.Bq 9204
    have hp : val WuPaper.ClassicalFourthData.Bq 9204 = (277662276888320:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 9204 = 277662276888320 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 9204 = (4301:ℝ)/1000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_9204
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 9205) ≤ val WuPaper.ClassicalFourthData.Bq 9205
    have hp : val WuPaper.ClassicalFourthData.Bq 9205 = (277663745342600:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 9205 = 277663745342600 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 9205 = (3441:ℝ)/800 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_9205
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 9206) ≤ val WuPaper.ClassicalFourthData.Bq 9206
    have hp : val WuPaper.ClassicalFourthData.Bq 9206 = (277665212292964:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 9206 = 277665212292964 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 9206 = (8603:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_9206
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 9207) ≤ val WuPaper.ClassicalFourthData.Bq 9207
    have hp : val WuPaper.ClassicalFourthData.Bq 9207 = (277666677739878:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 9207 = 277666677739878 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 9207 = (17207:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_9207
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 9208) ≤ val WuPaper.ClassicalFourthData.Bq 9208
    have hp : val WuPaper.ClassicalFourthData.Bq 9208 = (277668141683804:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 9208 = 277668141683804 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 9208 = (2151:ℝ)/500 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_9208
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 9209) ≤ val WuPaper.ClassicalFourthData.Bq 9209
    have hp : val WuPaper.ClassicalFourthData.Bq 9209 = (277669604125206:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 9209 = 277669604125206 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 9209 = (17209:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_9209
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 9210) ≤ val WuPaper.ClassicalFourthData.Bq 9210
    have hp : val WuPaper.ClassicalFourthData.Bq 9210 = (277671065064549:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 9210 = 277671065064549 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 9210 = (1721:ℝ)/400 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_9210
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 9211) ≤ val WuPaper.ClassicalFourthData.Bq 9211
    have hp : val WuPaper.ClassicalFourthData.Bq 9211 = (277672524502295:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 9211 = 277672524502295 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 9211 = (17211:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_9211
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 9212) ≤ val WuPaper.ClassicalFourthData.Bq 9212
    have hp : val WuPaper.ClassicalFourthData.Bq 9212 = (277673982438908:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 9212 = 277673982438908 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 9212 = (4303:ℝ)/1000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_9212
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 9213) ≤ val WuPaper.ClassicalFourthData.Bq 9213
    have hp : val WuPaper.ClassicalFourthData.Bq 9213 = (277675438874851:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 9213 = 277675438874851 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 9213 = (17213:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_9213
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 9214) ≤ val WuPaper.ClassicalFourthData.Bq 9214
    have hp : val WuPaper.ClassicalFourthData.Bq 9214 = (277676893810587:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 9214 = 277676893810587 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 9214 = (8607:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_9214
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 9215) ≤ val WuPaper.ClassicalFourthData.Bq 9215
    have hp : val WuPaper.ClassicalFourthData.Bq 9215 = (277678347246579:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 9215 = 277678347246579 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 9215 = (3443:ℝ)/800 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_9215
end WuPaper.ClassicalFourthConditions
#print axioms WuPaper.ClassicalFourthConditions.Log_block_575

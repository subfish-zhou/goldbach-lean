import WR2ClassicalFourthConditions
import WR2ClassicalFourthLogPoints638
noncomputable section
namespace WuPaper.ClassicalFourthConditions
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem Log_block_638 (j : Fin 16) (hj : 16*638+j.val < 10541) :
    WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 (16*638+j.val)) ≤ val WuPaper.ClassicalFourthData.Bq (16*638+j.val) := by
  fin_cases j
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 10208) ≤ val WuPaper.ClassicalFourthData.Bq 10208
    have hp : val WuPaper.ClassicalFourthData.Bq 10208 = (278451411524834:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 10208 = 278451411524834 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 10208 = (569:ℝ)/125 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_10208
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 10209) ≤ val WuPaper.ClassicalFourthData.Bq 10209
    have hp : val WuPaper.ClassicalFourthData.Bq 10209 = (278451580134519:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 10209 = 278451580134519 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 10209 = (18209:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_10209
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 10210) ≤ val WuPaper.ClassicalFourthData.Bq 10210
    have hp : val WuPaper.ClassicalFourthData.Bq 10210 = (278451747637702:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 10210 = 278451747637702 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 10210 = (1821:ℝ)/400 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_10210
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 10211) ≤ val WuPaper.ClassicalFourthData.Bq 10211
    have hp : val WuPaper.ClassicalFourthData.Bq 10211 = (278451914034716:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 10211 = 278451914034716 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 10211 = (18211:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_10211
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 10212) ≤ val WuPaper.ClassicalFourthData.Bq 10212
    have hp : val WuPaper.ClassicalFourthData.Bq 10212 = (278452079325897:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 10212 = 278452079325897 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 10212 = (4553:ℝ)/1000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_10212
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 10213) ≤ val WuPaper.ClassicalFourthData.Bq 10213
    have hp : val WuPaper.ClassicalFourthData.Bq 10213 = (278452243511580:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 10213 = 278452243511580 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 10213 = (18213:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_10213
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 10214) ≤ val WuPaper.ClassicalFourthData.Bq 10214
    have hp : val WuPaper.ClassicalFourthData.Bq 10214 = (278452406592101:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 10214 = 278452406592101 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 10214 = (9107:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_10214
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 10215) ≤ val WuPaper.ClassicalFourthData.Bq 10215
    have hp : val WuPaper.ClassicalFourthData.Bq 10215 = (278452568567794:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 10215 = 278452568567794 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 10215 = (3643:ℝ)/800 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_10215
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 10216) ≤ val WuPaper.ClassicalFourthData.Bq 10216
    have hp : val WuPaper.ClassicalFourthData.Bq 10216 = (278452729438994:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 10216 = 278452729438994 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 10216 = (2277:ℝ)/500 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_10216
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 10217) ≤ val WuPaper.ClassicalFourthData.Bq 10217
    have hp : val WuPaper.ClassicalFourthData.Bq 10217 = (278452889206036:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 10217 = 278452889206036 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 10217 = (18217:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_10217
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 10218) ≤ val WuPaper.ClassicalFourthData.Bq 10218
    have hp : val WuPaper.ClassicalFourthData.Bq 10218 = (278453047869255:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 10218 = 278453047869255 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 10218 = (9109:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_10218
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 10219) ≤ val WuPaper.ClassicalFourthData.Bq 10219
    have hp : val WuPaper.ClassicalFourthData.Bq 10219 = (278453205428985:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 10219 = 278453205428985 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 10219 = (18219:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_10219
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 10220) ≤ val WuPaper.ClassicalFourthData.Bq 10220
    have hp : val WuPaper.ClassicalFourthData.Bq 10220 = (278453361885561:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 10220 = 278453361885561 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 10220 = (911:ℝ)/200 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_10220
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 10221) ≤ val WuPaper.ClassicalFourthData.Bq 10221
    have hp : val WuPaper.ClassicalFourthData.Bq 10221 = (278453517239317:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 10221 = 278453517239317 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 10221 = (18221:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_10221
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 10222) ≤ val WuPaper.ClassicalFourthData.Bq 10222
    have hp : val WuPaper.ClassicalFourthData.Bq 10222 = (278453671490586:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 10222 = 278453671490586 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 10222 = (9111:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_10222
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 10223) ≤ val WuPaper.ClassicalFourthData.Bq 10223
    have hp : val WuPaper.ClassicalFourthData.Bq 10223 = (278453824639705:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 10223 = 278453824639705 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 10223 = (18223:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_10223
end WuPaper.ClassicalFourthConditions
#print axioms WuPaper.ClassicalFourthConditions.Log_block_638

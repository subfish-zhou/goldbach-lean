import WR2ClassicalFourthConditions
import WR2ClassicalFourthLogPoints393
noncomputable section
namespace WuPaper.ClassicalFourthConditions
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem Log_block_393 (j : Fin 16) (hj : 16*393+j.val < 10541) :
    WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 (16*393+j.val)) ≤ val WuPaper.ClassicalFourthData.Bq (16*393+j.val) := by
  fin_cases j
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 6288) ≤ val WuPaper.ClassicalFourthData.Bq 6288
    have hp : val WuPaper.ClassicalFourthData.Bq 6288 = (264469150721000:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 6288 = 264469150721000 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 6288 = (893:ℝ)/250 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_6288
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 6289) ≤ val WuPaper.ClassicalFourthData.Bq 6289
    have hp : val WuPaper.ClassicalFourthData.Bq 6289 = (264477850731002:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 6289 = 264477850731002 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 6289 = (14289:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_6289
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 6290) ≤ val WuPaper.ClassicalFourthData.Bq 6290
    have hp : val WuPaper.ClassicalFourthData.Bq 6290 = (264486546879246:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 6290 = 264486546879246 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 6290 = (1429:ℝ)/400 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_6290
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 6291) ≤ val WuPaper.ClassicalFourthData.Bq 6291
    have hp : val WuPaper.ClassicalFourthData.Bq 6291 = (264495239167057:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 6291 = 264495239167057 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 6291 = (14291:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_6291
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 6292) ≤ val WuPaper.ClassicalFourthData.Bq 6292
    have hp : val WuPaper.ClassicalFourthData.Bq 6292 = (264503927595759:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 6292 = 264503927595759 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 6292 = (3573:ℝ)/1000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_6292
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 6293) ≤ val WuPaper.ClassicalFourthData.Bq 6293
    have hp : val WuPaper.ClassicalFourthData.Bq 6293 = (264512612166675:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 6293 = 264512612166675 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 6293 = (14293:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_6293
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 6294) ≤ val WuPaper.ClassicalFourthData.Bq 6294
    have hp : val WuPaper.ClassicalFourthData.Bq 6294 = (264521292881128:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 6294 = 264521292881128 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 6294 = (7147:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_6294
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 6295) ≤ val WuPaper.ClassicalFourthData.Bq 6295
    have hp : val WuPaper.ClassicalFourthData.Bq 6295 = (264529969740441:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 6295 = 264529969740441 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 6295 = (2859:ℝ)/800 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_6295
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 6296) ≤ val WuPaper.ClassicalFourthData.Bq 6296
    have hp : val WuPaper.ClassicalFourthData.Bq 6296 = (264538642745936:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 6296 = 264538642745936 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 6296 = (1787:ℝ)/500 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_6296
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 6297) ≤ val WuPaper.ClassicalFourthData.Bq 6297
    have hp : val WuPaper.ClassicalFourthData.Bq 6297 = (264547311898934:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 6297 = 264547311898934 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 6297 = (14297:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_6297
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 6298) ≤ val WuPaper.ClassicalFourthData.Bq 6298
    have hp : val WuPaper.ClassicalFourthData.Bq 6298 = (264555977200755:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 6298 = 264555977200755 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 6298 = (7149:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_6298
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 6299) ≤ val WuPaper.ClassicalFourthData.Bq 6299
    have hp : val WuPaper.ClassicalFourthData.Bq 6299 = (264564638652721:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 6299 = 264564638652721 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 6299 = (14299:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_6299
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 6300) ≤ val WuPaper.ClassicalFourthData.Bq 6300
    have hp : val WuPaper.ClassicalFourthData.Bq 6300 = (264573296256151:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 6300 = 264573296256151 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 6300 = (143:ℝ)/40 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_6300
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 6301) ≤ val WuPaper.ClassicalFourthData.Bq 6301
    have hp : val WuPaper.ClassicalFourthData.Bq 6301 = (264581950012365:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 6301 = 264581950012365 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 6301 = (14301:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_6301
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 6302) ≤ val WuPaper.ClassicalFourthData.Bq 6302
    have hp : val WuPaper.ClassicalFourthData.Bq 6302 = (264590599922681:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 6302 = 264590599922681 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 6302 = (7151:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_6302
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 6303) ≤ val WuPaper.ClassicalFourthData.Bq 6303
    have hp : val WuPaper.ClassicalFourthData.Bq 6303 = (264599245988417:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 6303 = 264599245988417 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 6303 = (14303:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_6303
end WuPaper.ClassicalFourthConditions
#print axioms WuPaper.ClassicalFourthConditions.Log_block_393

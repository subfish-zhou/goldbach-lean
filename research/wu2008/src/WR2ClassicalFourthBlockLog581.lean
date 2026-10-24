import WR2ClassicalFourthConditions
import WR2ClassicalFourthLogPoints581
noncomputable section
namespace WuPaper.ClassicalFourthConditions
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem Log_block_581 (j : Fin 16) (hj : 16*581+j.val < 10541) :
    WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 (16*581+j.val)) ≤ val WuPaper.ClassicalFourthData.Bq (16*581+j.val) := by
  fin_cases j
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 9296) ≤ val WuPaper.ClassicalFourthData.Bq 9296
    have hp : val WuPaper.ClassicalFourthData.Bq 9296 = (277791137146910:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 9296 = 277791137146910 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 9296 = (1081:ℝ)/250 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_9296
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 9297) ≤ val WuPaper.ClassicalFourthData.Bq 9297
    have hp : val WuPaper.ClassicalFourthData.Bq 9297 = (277792469164541:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 9297 = 277792469164541 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 9297 = (17297:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_9297
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 9298) ≤ val WuPaper.ClassicalFourthData.Bq 9298
    have hp : val WuPaper.ClassicalFourthData.Bq 9298 = (277793799720317:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 9298 = 277793799720317 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 9298 = (8649:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_9298
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 9299) ≤ val WuPaper.ClassicalFourthData.Bq 9299
    have hp : val WuPaper.ClassicalFourthData.Bq 9299 = (277795128814689:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 9299 = 277795128814689 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 9299 = (17299:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_9299
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 9300) ≤ val WuPaper.ClassicalFourthData.Bq 9300
    have hp : val WuPaper.ClassicalFourthData.Bq 9300 = (277796456448107:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 9300 = 277796456448107 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 9300 = (173:ℝ)/40 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_9300
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 9301) ≤ val WuPaper.ClassicalFourthData.Bq 9301
    have hp : val WuPaper.ClassicalFourthData.Bq 9301 = (277797782621020:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 9301 = 277797782621020 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 9301 = (17301:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_9301
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 9302) ≤ val WuPaper.ClassicalFourthData.Bq 9302
    have hp : val WuPaper.ClassicalFourthData.Bq 9302 = (277799107333878:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 9302 = 277799107333878 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 9302 = (8651:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_9302
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 9303) ≤ val WuPaper.ClassicalFourthData.Bq 9303
    have hp : val WuPaper.ClassicalFourthData.Bq 9303 = (277800430587130:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 9303 = 277800430587130 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 9303 = (17303:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_9303
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 9304) ≤ val WuPaper.ClassicalFourthData.Bq 9304
    have hp : val WuPaper.ClassicalFourthData.Bq 9304 = (277801752381227:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 9304 = 277801752381227 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 9304 = (2163:ℝ)/500 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_9304
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 9305) ≤ val WuPaper.ClassicalFourthData.Bq 9305
    have hp : val WuPaper.ClassicalFourthData.Bq 9305 = (277803072716618:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 9305 = 277803072716618 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 9305 = (3461:ℝ)/800 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_9305
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 9306) ≤ val WuPaper.ClassicalFourthData.Bq 9306
    have hp : val WuPaper.ClassicalFourthData.Bq 9306 = (277804391593751:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 9306 = 277804391593751 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 9306 = (8653:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_9306
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 9307) ≤ val WuPaper.ClassicalFourthData.Bq 9307
    have hp : val WuPaper.ClassicalFourthData.Bq 9307 = (277805709013076:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 9307 = 277805709013076 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 9307 = (17307:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_9307
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 9308) ≤ val WuPaper.ClassicalFourthData.Bq 9308
    have hp : val WuPaper.ClassicalFourthData.Bq 9308 = (277807024975041:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 9308 = 277807024975041 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 9308 = (4327:ℝ)/1000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_9308
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 9309) ≤ val WuPaper.ClassicalFourthData.Bq 9309
    have hp : val WuPaper.ClassicalFourthData.Bq 9309 = (277808339480096:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 9309 = 277808339480096 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 9309 = (17309:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_9309
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 9310) ≤ val WuPaper.ClassicalFourthData.Bq 9310
    have hp : val WuPaper.ClassicalFourthData.Bq 9310 = (277809652528688:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 9310 = 277809652528688 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 9310 = (1731:ℝ)/400 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_9310
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 9311) ≤ val WuPaper.ClassicalFourthData.Bq 9311
    have hp : val WuPaper.ClassicalFourthData.Bq 9311 = (277810964121267:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 9311 = 277810964121267 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 9311 = (17311:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_9311
end WuPaper.ClassicalFourthConditions
#print axioms WuPaper.ClassicalFourthConditions.Log_block_581

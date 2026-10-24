import WR2ClassicalFourthConditions
import WR2ClassicalFourthLogPoints331
noncomputable section
namespace WuPaper.ClassicalFourthConditions
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem Log_block_331 (j : Fin 16) (hj : 16*331+j.val < 10541) :
    WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 (16*331+j.val)) ≤ val WuPaper.ClassicalFourthData.Bq (16*331+j.val) := by
  fin_cases j
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 5296) ≤ val WuPaper.ClassicalFourthData.Bq 5296
    have hp : val WuPaper.ClassicalFourthData.Bq 5296 = (253697304148516:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 5296 = 253697304148516 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 5296 = (831:ℝ)/250 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_5296
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 5297) ≤ val WuPaper.ClassicalFourthData.Bq 5297
    have hp : val WuPaper.ClassicalFourthData.Bq 5297 = (253710583245494:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 5297 = 253710583245494 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 5297 = (13297:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_5297
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 5298) ≤ val WuPaper.ClassicalFourthData.Bq 5298
    have hp : val WuPaper.ClassicalFourthData.Bq 5298 = (253723856865245:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 5298 = 253723856865245 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 5298 = (6649:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_5298
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 5299) ≤ val WuPaper.ClassicalFourthData.Bq 5299
    have hp : val WuPaper.ClassicalFourthData.Bq 5299 = (253737125009752:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 5299 = 253737125009752 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 5299 = (13299:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_5299
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 5300) ≤ val WuPaper.ClassicalFourthData.Bq 5300
    have hp : val WuPaper.ClassicalFourthData.Bq 5300 = (253750387680999:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 5300 = 253750387680999 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 5300 = (133:ℝ)/40 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_5300
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 5301) ≤ val WuPaper.ClassicalFourthData.Bq 5301
    have hp : val WuPaper.ClassicalFourthData.Bq 5301 = (253763644880969:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 5301 = 253763644880969 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 5301 = (13301:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_5301
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 5302) ≤ val WuPaper.ClassicalFourthData.Bq 5302
    have hp : val WuPaper.ClassicalFourthData.Bq 5302 = (253776896611643:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 5302 = 253776896611643 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 5302 = (6651:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_5302
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 5303) ≤ val WuPaper.ClassicalFourthData.Bq 5303
    have hp : val WuPaper.ClassicalFourthData.Bq 5303 = (253790142875001:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 5303 = 253790142875001 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 5303 = (13303:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_5303
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 5304) ≤ val WuPaper.ClassicalFourthData.Bq 5304
    have hp : val WuPaper.ClassicalFourthData.Bq 5304 = (253803383673023:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 5304 = 253803383673023 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 5304 = (1663:ℝ)/500 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_5304
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 5305) ≤ val WuPaper.ClassicalFourthData.Bq 5305
    have hp : val WuPaper.ClassicalFourthData.Bq 5305 = (253816619007689:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 5305 = 253816619007689 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 5305 = (2661:ℝ)/800 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_5305
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 5306) ≤ val WuPaper.ClassicalFourthData.Bq 5306
    have hp : val WuPaper.ClassicalFourthData.Bq 5306 = (253829848880977:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 5306 = 253829848880977 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 5306 = (6653:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_5306
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 5307) ≤ val WuPaper.ClassicalFourthData.Bq 5307
    have hp : val WuPaper.ClassicalFourthData.Bq 5307 = (253843073294863:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 5307 = 253843073294863 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 5307 = (13307:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_5307
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 5308) ≤ val WuPaper.ClassicalFourthData.Bq 5308
    have hp : val WuPaper.ClassicalFourthData.Bq 5308 = (253856292251325:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 5308 = 253856292251325 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 5308 = (3327:ℝ)/1000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_5308
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 5309) ≤ val WuPaper.ClassicalFourthData.Bq 5309
    have hp : val WuPaper.ClassicalFourthData.Bq 5309 = (253869505752338:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 5309 = 253869505752338 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 5309 = (13309:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_5309
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 5310) ≤ val WuPaper.ClassicalFourthData.Bq 5310
    have hp : val WuPaper.ClassicalFourthData.Bq 5310 = (253882713799876:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 5310 = 253882713799876 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 5310 = (1331:ℝ)/400 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_5310
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 5311) ≤ val WuPaper.ClassicalFourthData.Bq 5311
    have hp : val WuPaper.ClassicalFourthData.Bq 5311 = (253895916395915:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 5311 = 253895916395915 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 5311 = (13311:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_5311
end WuPaper.ClassicalFourthConditions
#print axioms WuPaper.ClassicalFourthConditions.Log_block_331

import WR2ClassicalFourthConditions
import WR2ClassicalFourthLogPoints334
noncomputable section
namespace WuPaper.ClassicalFourthConditions
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem Log_block_334 (j : Fin 16) (hj : 16*334+j.val < 10541) :
    WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 (16*334+j.val)) ≤ val WuPaper.ClassicalFourthData.Bq (16*334+j.val) := by
  fin_cases j
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 5344) ≤ val WuPaper.ClassicalFourthData.Bq 5344
    have hp : val WuPaper.ClassicalFourthData.Bq 5344 = (254328556644480:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 5344 = 254328556644480 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 5344 = (417:ℝ)/125 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_5344
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 5345) ≤ val WuPaper.ClassicalFourthData.Bq 5345
    have hp : val WuPaper.ClassicalFourthData.Bq 5345 = (254341575058116:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 5345 = 254341575058116 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 5345 = (2669:ℝ)/800 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_5345
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 5346) ≤ val WuPaper.ClassicalFourthData.Bq 5346
    have hp : val WuPaper.ClassicalFourthData.Bq 5346 = (254354588088820:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 5346 = 254354588088820 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 5346 = (6673:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_5346
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 5347) ≤ val WuPaper.ClassicalFourthData.Bq 5347
    have hp : val WuPaper.ClassicalFourthData.Bq 5347 = (254367595738536:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 5347 = 254367595738536 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 5347 = (13347:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_5347
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 5348) ≤ val WuPaper.ClassicalFourthData.Bq 5348
    have hp : val WuPaper.ClassicalFourthData.Bq 5348 = (254380598009207:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 5348 = 254380598009207 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 5348 = (3337:ℝ)/1000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_5348
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 5349) ≤ val WuPaper.ClassicalFourthData.Bq 5349
    have hp : val WuPaper.ClassicalFourthData.Bq 5349 = (254393594902777:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 5349 = 254393594902777 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 5349 = (13349:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_5349
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 5350) ≤ val WuPaper.ClassicalFourthData.Bq 5350
    have hp : val WuPaper.ClassicalFourthData.Bq 5350 = (254406586421186:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 5350 = 254406586421186 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 5350 = (267:ℝ)/80 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_5350
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 5351) ≤ val WuPaper.ClassicalFourthData.Bq 5351
    have hp : val WuPaper.ClassicalFourthData.Bq 5351 = (254419572566376:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 5351 = 254419572566376 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 5351 = (13351:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_5351
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 5352) ≤ val WuPaper.ClassicalFourthData.Bq 5352
    have hp : val WuPaper.ClassicalFourthData.Bq 5352 = (254432553340288:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 5352 = 254432553340288 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 5352 = (1669:ℝ)/500 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_5352
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 5353) ≤ val WuPaper.ClassicalFourthData.Bq 5353
    have hp : val WuPaper.ClassicalFourthData.Bq 5353 = (254445528744859:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 5353 = 254445528744859 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 5353 = (13353:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_5353
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 5354) ≤ val WuPaper.ClassicalFourthData.Bq 5354
    have hp : val WuPaper.ClassicalFourthData.Bq 5354 = (254458498782030:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 5354 = 254458498782030 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 5354 = (6677:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_5354
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 5355) ≤ val WuPaper.ClassicalFourthData.Bq 5355
    have hp : val WuPaper.ClassicalFourthData.Bq 5355 = (254471463453737:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 5355 = 254471463453737 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 5355 = (2671:ℝ)/800 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_5355
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 5356) ≤ val WuPaper.ClassicalFourthData.Bq 5356
    have hp : val WuPaper.ClassicalFourthData.Bq 5356 = (254484422761918:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 5356 = 254484422761918 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 5356 = (3339:ℝ)/1000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_5356
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 5357) ≤ val WuPaper.ClassicalFourthData.Bq 5357
    have hp : val WuPaper.ClassicalFourthData.Bq 5357 = (254497376708509:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 5357 = 254497376708509 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 5357 = (13357:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_5357
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 5358) ≤ val WuPaper.ClassicalFourthData.Bq 5358
    have hp : val WuPaper.ClassicalFourthData.Bq 5358 = (254510325295445:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 5358 = 254510325295445 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 5358 = (6679:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_5358
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 5359) ≤ val WuPaper.ClassicalFourthData.Bq 5359
    have hp : val WuPaper.ClassicalFourthData.Bq 5359 = (254523268524660:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 5359 = 254523268524660 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 5359 = (13359:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_5359
end WuPaper.ClassicalFourthConditions
#print axioms WuPaper.ClassicalFourthConditions.Log_block_334

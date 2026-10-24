import WR2ClassicalFourthConditions
import WR2ClassicalFourthLogPoints398
noncomputable section
namespace WuPaper.ClassicalFourthConditions
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem Log_block_398 (j : Fin 16) (hj : 16*398+j.val < 10541) :
    WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 (16*398+j.val)) ≤ val WuPaper.ClassicalFourthData.Bq (16*398+j.val) := by
  fin_cases j
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 6368) ≤ val WuPaper.ClassicalFourthData.Bq 6368
    have hp : val WuPaper.ClassicalFourthData.Bq 6368 = (265153056372516:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 6368 = 265153056372516 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 6368 = (449:ℝ)/125 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_6368
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 6369) ≤ val WuPaper.ClassicalFourthData.Bq 6369
    have hp : val WuPaper.ClassicalFourthData.Bq 6369 = (265161451585023:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 6369 = 265161451585023 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 6369 = (14369:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_6369
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 6370) ≤ val WuPaper.ClassicalFourthData.Bq 6370
    have hp : val WuPaper.ClassicalFourthData.Bq 6370 = (265169843040110:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 6370 = 265169843040110 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 6370 = (1437:ℝ)/400 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_6370
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 6371) ≤ val WuPaper.ClassicalFourthData.Bq 6371
    have hp : val WuPaper.ClassicalFourthData.Bq 6371 = (265178230739060:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 6371 = 265178230739060 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 6371 = (14371:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_6371
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 6372) ≤ val WuPaper.ClassicalFourthData.Bq 6372
    have hp : val WuPaper.ClassicalFourthData.Bq 6372 = (265186614683155:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 6372 = 265186614683155 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 6372 = (3593:ℝ)/1000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_6372
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 6373) ≤ val WuPaper.ClassicalFourthData.Bq 6373
    have hp : val WuPaper.ClassicalFourthData.Bq 6373 = (265194994873680:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 6373 = 265194994873680 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 6373 = (14373:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_6373
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 6374) ≤ val WuPaper.ClassicalFourthData.Bq 6374
    have hp : val WuPaper.ClassicalFourthData.Bq 6374 = (265203371311915:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 6374 = 265203371311915 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 6374 = (7187:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_6374
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 6375) ≤ val WuPaper.ClassicalFourthData.Bq 6375
    have hp : val WuPaper.ClassicalFourthData.Bq 6375 = (265211743999143:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 6375 = 265211743999143 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 6375 = (115:ℝ)/32 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_6375
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 6376) ≤ val WuPaper.ClassicalFourthData.Bq 6376
    have hp : val WuPaper.ClassicalFourthData.Bq 6376 = (265220112936645:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 6376 = 265220112936645 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 6376 = (1797:ℝ)/500 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_6376
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 6377) ≤ val WuPaper.ClassicalFourthData.Bq 6377
    have hp : val WuPaper.ClassicalFourthData.Bq 6377 = (265228478125701:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 6377 = 265228478125701 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 6377 = (14377:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_6377
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 6378) ≤ val WuPaper.ClassicalFourthData.Bq 6378
    have hp : val WuPaper.ClassicalFourthData.Bq 6378 = (265236839567592:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 6378 = 265236839567592 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 6378 = (7189:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_6378
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 6379) ≤ val WuPaper.ClassicalFourthData.Bq 6379
    have hp : val WuPaper.ClassicalFourthData.Bq 6379 = (265245197263596:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 6379 = 265245197263596 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 6379 = (14379:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_6379
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 6380) ≤ val WuPaper.ClassicalFourthData.Bq 6380
    have hp : val WuPaper.ClassicalFourthData.Bq 6380 = (265253551214994:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 6380 = 265253551214994 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 6380 = (719:ℝ)/200 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_6380
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 6381) ≤ val WuPaper.ClassicalFourthData.Bq 6381
    have hp : val WuPaper.ClassicalFourthData.Bq 6381 = (265261901423064:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 6381 = 265261901423064 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 6381 = (14381:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_6381
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 6382) ≤ val WuPaper.ClassicalFourthData.Bq 6382
    have hp : val WuPaper.ClassicalFourthData.Bq 6382 = (265270247889083:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 6382 = 265270247889083 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 6382 = (7191:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_6382
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 6383) ≤ val WuPaper.ClassicalFourthData.Bq 6383
    have hp : val WuPaper.ClassicalFourthData.Bq 6383 = (265278590614330:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 6383 = 265278590614330 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 6383 = (14383:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_6383
end WuPaper.ClassicalFourthConditions
#print axioms WuPaper.ClassicalFourthConditions.Log_block_398

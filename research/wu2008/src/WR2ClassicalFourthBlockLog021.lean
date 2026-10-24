import WR2ClassicalFourthConditions
import WR2ClassicalFourthLogPoints021
noncomputable section
namespace WuPaper.ClassicalFourthConditions
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem Log_block_021 (j : Fin 16) (hj : 16*21+j.val < 10541) :
    WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 (16*21+j.val)) ≤ val WuPaper.ClassicalFourthData.Bq (16*21+j.val) := by
  fin_cases j
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 336) ≤ val WuPaper.ClassicalFourthData.Bq 336
    have hp : val WuPaper.ClassicalFourthData.Bq 336 = (38703408357704:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 336 = 38703408357704 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 336 = (521:ℝ)/250 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_336
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 337) ≤ val WuPaper.ClassicalFourthData.Bq 337
    have hp : val WuPaper.ClassicalFourthData.Bq 337 = (38809405653515:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 337 = 38809405653515 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 337 = (8337:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_337
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 338) ≤ val WuPaper.ClassicalFourthData.Bq 338
    have hp : val WuPaper.ClassicalFourthData.Bq 338 = (38915352019570:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 338 = 38915352019570 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 338 = (4169:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_338
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 339) ≤ val WuPaper.ClassicalFourthData.Bq 339
    have hp : val WuPaper.ClassicalFourthData.Bq 339 = (39021247485945:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 339 = 39021247485945 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 339 = (8339:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_339
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 340) ≤ val WuPaper.ClassicalFourthData.Bq 340
    have hp : val WuPaper.ClassicalFourthData.Bq 340 = (39127092082697:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 340 = 39127092082697 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 340 = (417:ℝ)/200 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_340
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 341) ≤ val WuPaper.ClassicalFourthData.Bq 341
    have hp : val WuPaper.ClassicalFourthData.Bq 341 = (39232885839859:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 341 = 39232885839859 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 341 = (8341:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_341
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 342) ≤ val WuPaper.ClassicalFourthData.Bq 342
    have hp : val WuPaper.ClassicalFourthData.Bq 342 = (39338628787442:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 342 = 39338628787442 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 342 = (4171:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_342
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 343) ≤ val WuPaper.ClassicalFourthData.Bq 343
    have hp : val WuPaper.ClassicalFourthData.Bq 343 = (39444320955433:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 343 = 39444320955433 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 343 = (8343:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_343
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 344) ≤ val WuPaper.ClassicalFourthData.Bq 344
    have hp : val WuPaper.ClassicalFourthData.Bq 344 = (39549962373799:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 344 = 39549962373799 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 344 = (1043:ℝ)/500 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_344
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 345) ≤ val WuPaper.ClassicalFourthData.Bq 345
    have hp : val WuPaper.ClassicalFourthData.Bq 345 = (39655553072482:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 345 = 39655553072482 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 345 = (1669:ℝ)/800 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_345
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 346) ≤ val WuPaper.ClassicalFourthData.Bq 346
    have hp : val WuPaper.ClassicalFourthData.Bq 346 = (39761093081403:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 346 = 39761093081403 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 346 = (4173:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_346
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 347) ≤ val WuPaper.ClassicalFourthData.Bq 347
    have hp : val WuPaper.ClassicalFourthData.Bq 347 = (39866582430461:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 347 = 39866582430461 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 347 = (8347:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_347
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 348) ≤ val WuPaper.ClassicalFourthData.Bq 348
    have hp : val WuPaper.ClassicalFourthData.Bq 348 = (39972021149532:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 348 = 39972021149532 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 348 = (2087:ℝ)/1000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_348
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 349) ≤ val WuPaper.ClassicalFourthData.Bq 349
    have hp : val WuPaper.ClassicalFourthData.Bq 349 = (40077409268469:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 349 = 40077409268469 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 349 = (8349:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_349
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 350) ≤ val WuPaper.ClassicalFourthData.Bq 350
    have hp : val WuPaper.ClassicalFourthData.Bq 350 = (40182746817103:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 350 = 40182746817103 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 350 = (167:ℝ)/80 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_350
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 351) ≤ val WuPaper.ClassicalFourthData.Bq 351
    have hp : val WuPaper.ClassicalFourthData.Bq 351 = (40288033825244:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 351 = 40288033825244 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 351 = (8351:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_351
end WuPaper.ClassicalFourthConditions
#print axioms WuPaper.ClassicalFourthConditions.Log_block_021

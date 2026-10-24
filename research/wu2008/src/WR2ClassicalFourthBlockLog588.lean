import WR2ClassicalFourthConditions
import WR2ClassicalFourthLogPoints588
noncomputable section
namespace WuPaper.ClassicalFourthConditions
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem Log_block_588 (j : Fin 16) (hj : 16*588+j.val < 10541) :
    WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 (16*588+j.val)) ≤ val WuPaper.ClassicalFourthData.Bq (16*588+j.val) := by
  fin_cases j
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 9408) ≤ val WuPaper.ClassicalFourthData.Bq 9408
    have hp : val WuPaper.ClassicalFourthData.Bq 9408 = (277931337926518:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 9408 = 277931337926518 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 9408 = (544:ℝ)/125 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_9408
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 9409) ≤ val WuPaper.ClassicalFourthData.Bq 9409
    have hp : val WuPaper.ClassicalFourthData.Bq 9409 = (277932508981342:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 9409 = 277932508981342 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 9409 = (17409:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_9409
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 9410) ≤ val WuPaper.ClassicalFourthData.Bq 9410
    have hp : val WuPaper.ClassicalFourthData.Bq 9410 = (277933678623823:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 9410 = 277933678623823 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 9410 = (1741:ℝ)/400 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_9410
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 9411) ≤ val WuPaper.ClassicalFourthData.Bq 9411
    have hp : val WuPaper.ClassicalFourthData.Bq 9411 = (277934846854395:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 9411 = 277934846854395 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 9411 = (17411:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_9411
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 9412) ≤ val WuPaper.ClassicalFourthData.Bq 9412
    have hp : val WuPaper.ClassicalFourthData.Bq 9412 = (277936013673492:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 9412 = 277936013673492 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 9412 = (4353:ℝ)/1000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_9412
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 9413) ≤ val WuPaper.ClassicalFourthData.Bq 9413
    have hp : val WuPaper.ClassicalFourthData.Bq 9413 = (277937179081547:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 9413 = 277937179081547 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 9413 = (17413:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_9413
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 9414) ≤ val WuPaper.ClassicalFourthData.Bq 9414
    have hp : val WuPaper.ClassicalFourthData.Bq 9414 = (277938343078993:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 9414 = 277938343078993 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 9414 = (8707:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_9414
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 9415) ≤ val WuPaper.ClassicalFourthData.Bq 9415
    have hp : val WuPaper.ClassicalFourthData.Bq 9415 = (277939505666265:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 9415 = 277939505666265 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 9415 = (3483:ℝ)/800 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_9415
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 9416) ≤ val WuPaper.ClassicalFourthData.Bq 9416
    have hp : val WuPaper.ClassicalFourthData.Bq 9416 = (277940666843795:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 9416 = 277940666843795 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 9416 = (2177:ℝ)/500 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_9416
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 9417) ≤ val WuPaper.ClassicalFourthData.Bq 9417
    have hp : val WuPaper.ClassicalFourthData.Bq 9417 = (277941826612017:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 9417 = 277941826612017 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 9417 = (17417:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_9417
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 9418) ≤ val WuPaper.ClassicalFourthData.Bq 9418
    have hp : val WuPaper.ClassicalFourthData.Bq 9418 = (277942984971362:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 9418 = 277942984971362 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 9418 = (8709:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_9418
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 9419) ≤ val WuPaper.ClassicalFourthData.Bq 9419
    have hp : val WuPaper.ClassicalFourthData.Bq 9419 = (277944141922265:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 9419 = 277944141922265 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 9419 = (17419:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_9419
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 9420) ≤ val WuPaper.ClassicalFourthData.Bq 9420
    have hp : val WuPaper.ClassicalFourthData.Bq 9420 = (277945297465158:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 9420 = 277945297465158 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 9420 = (871:ℝ)/200 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_9420
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 9421) ≤ val WuPaper.ClassicalFourthData.Bq 9421
    have hp : val WuPaper.ClassicalFourthData.Bq 9421 = (277946451600473:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 9421 = 277946451600473 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 9421 = (17421:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_9421
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 9422) ≤ val WuPaper.ClassicalFourthData.Bq 9422
    have hp : val WuPaper.ClassicalFourthData.Bq 9422 = (277947604328642:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 9422 = 277947604328642 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 9422 = (8711:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_9422
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 9423) ≤ val WuPaper.ClassicalFourthData.Bq 9423
    have hp : val WuPaper.ClassicalFourthData.Bq 9423 = (277948755650098:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 9423 = 277948755650098 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 9423 = (17423:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_9423
end WuPaper.ClassicalFourthConditions
#print axioms WuPaper.ClassicalFourthConditions.Log_block_588

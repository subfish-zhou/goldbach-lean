import WR2ClassicalFourthConditions
import WR2ClassicalFourthLogPoints587
noncomputable section
namespace WuPaper.ClassicalFourthConditions
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem Log_block_587 (j : Fin 16) (hj : 16*587+j.val < 10541) :
    WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 (16*587+j.val)) ≤ val WuPaper.ClassicalFourthData.Bq (16*587+j.val) := by
  fin_cases j
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 9392) ≤ val WuPaper.ClassicalFourthData.Bq 9392
    have hp : val WuPaper.ClassicalFourthData.Bq 9392 = (277912408616059:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 9392 = 277912408616059 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 9392 = (1087:ℝ)/250 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_9392
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 9393) ≤ val WuPaper.ClassicalFourthData.Bq 9393
    have hp : val WuPaper.ClassicalFourthData.Bq 9393 = (277913602327500:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 9393 = 277913602327500 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 9393 = (17393:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_9393
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 9394) ≤ val WuPaper.ClassicalFourthData.Bq 9394
    have hp : val WuPaper.ClassicalFourthData.Bq 9394 = (277914794619635:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 9394 = 277914794619635 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 9394 = (8697:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_9394
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 9395) ≤ val WuPaper.ClassicalFourthData.Bq 9395
    have hp : val WuPaper.ClassicalFourthData.Bq 9395 = (277915985492902:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 9395 = 277915985492902 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 9395 = (3479:ℝ)/800 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_9395
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 9396) ≤ val WuPaper.ClassicalFourthData.Bq 9396
    have hp : val WuPaper.ClassicalFourthData.Bq 9396 = (277917174947736:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 9396 = 277917174947736 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 9396 = (4349:ℝ)/1000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_9396
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 9397) ≤ val WuPaper.ClassicalFourthData.Bq 9397
    have hp : val WuPaper.ClassicalFourthData.Bq 9397 = (277918362984574:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 9397 = 277918362984574 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 9397 = (17397:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_9397
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 9398) ≤ val WuPaper.ClassicalFourthData.Bq 9398
    have hp : val WuPaper.ClassicalFourthData.Bq 9398 = (277919549603850:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 9398 = 277919549603850 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 9398 = (8699:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_9398
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 9399) ≤ val WuPaper.ClassicalFourthData.Bq 9399
    have hp : val WuPaper.ClassicalFourthData.Bq 9399 = (277920734806000:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 9399 = 277920734806000 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 9399 = (17399:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_9399
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 9400) ≤ val WuPaper.ClassicalFourthData.Bq 9400
    have hp : val WuPaper.ClassicalFourthData.Bq 9400 = (277921918591461:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 9400 = 277921918591461 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 9400 = (87:ℝ)/20 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_9400
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 9401) ≤ val WuPaper.ClassicalFourthData.Bq 9401
    have hp : val WuPaper.ClassicalFourthData.Bq 9401 = (277923100960667:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 9401 = 277923100960667 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 9401 = (17401:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_9401
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 9402) ≤ val WuPaper.ClassicalFourthData.Bq 9402
    have hp : val WuPaper.ClassicalFourthData.Bq 9402 = (277924281914054:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 9402 = 277924281914054 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 9402 = (8701:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_9402
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 9403) ≤ val WuPaper.ClassicalFourthData.Bq 9403
    have hp : val WuPaper.ClassicalFourthData.Bq 9403 = (277925461452056:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 9403 = 277925461452056 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 9403 = (17403:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_9403
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 9404) ≤ val WuPaper.ClassicalFourthData.Bq 9404
    have hp : val WuPaper.ClassicalFourthData.Bq 9404 = (277926639575109:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 9404 = 277926639575109 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 9404 = (4351:ℝ)/1000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_9404
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 9405) ≤ val WuPaper.ClassicalFourthData.Bq 9405
    have hp : val WuPaper.ClassicalFourthData.Bq 9405 = (277927816283647:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 9405 = 277927816283647 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 9405 = (3481:ℝ)/800 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_9405
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 9406) ≤ val WuPaper.ClassicalFourthData.Bq 9406
    have hp : val WuPaper.ClassicalFourthData.Bq 9406 = (277928991578105:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 9406 = 277928991578105 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 9406 = (8703:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_9406
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 9407) ≤ val WuPaper.ClassicalFourthData.Bq 9407
    have hp : val WuPaper.ClassicalFourthData.Bq 9407 = (277930165458917:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 9407 = 277930165458917 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 9407 = (17407:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_9407
end WuPaper.ClassicalFourthConditions
#print axioms WuPaper.ClassicalFourthConditions.Log_block_587

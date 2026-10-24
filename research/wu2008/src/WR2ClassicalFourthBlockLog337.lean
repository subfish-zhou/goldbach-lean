import WR2ClassicalFourthConditions
import WR2ClassicalFourthLogPoints337
noncomputable section
namespace WuPaper.ClassicalFourthConditions
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem Log_block_337 (j : Fin 16) (hj : 16*337+j.val < 10541) :
    WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 (16*337+j.val)) ≤ val WuPaper.ClassicalFourthData.Bq (16*337+j.val) := by
  fin_cases j
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 5392) ≤ val WuPaper.ClassicalFourthData.Bq 5392
    have hp : val WuPaper.ClassicalFourthData.Bq 5392 = (254947402020864:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 5392 = 254947402020864 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 5392 = (837:ℝ)/250 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_5392
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 5393) ≤ val WuPaper.ClassicalFourthData.Bq 5393
    have hp : val WuPaper.ClassicalFourthData.Bq 5393 = (254960164232806:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 5393 = 254960164232806 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 5393 = (13393:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_5393
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 5394) ≤ val WuPaper.ClassicalFourthData.Bq 5394
    have hp : val WuPaper.ClassicalFourthData.Bq 5394 = (254972921154223:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 5394 = 254972921154223 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 5394 = (6697:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_5394
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 5395) ≤ val WuPaper.ClassicalFourthData.Bq 5395
    have hp : val WuPaper.ClassicalFourthData.Bq 5395 = (254985672787023:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 5395 = 254985672787023 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 5395 = (2679:ℝ)/800 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_5395
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 5396) ≤ val WuPaper.ClassicalFourthData.Bq 5396
    have hp : val WuPaper.ClassicalFourthData.Bq 5396 = (254998419133108:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 5396 = 254998419133108 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 5396 = (3349:ℝ)/1000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_5396
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 5397) ≤ val WuPaper.ClassicalFourthData.Bq 5397
    have hp : val WuPaper.ClassicalFourthData.Bq 5397 = (255011160194384:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 5397 = 255011160194384 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 5397 = (13397:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_5397
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 5398) ≤ val WuPaper.ClassicalFourthData.Bq 5398
    have hp : val WuPaper.ClassicalFourthData.Bq 5398 = (255023895972753:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 5398 = 255023895972753 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 5398 = (6699:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_5398
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 5399) ≤ val WuPaper.ClassicalFourthData.Bq 5399
    have hp : val WuPaper.ClassicalFourthData.Bq 5399 = (255036626470118:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 5399 = 255036626470118 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 5399 = (13399:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_5399
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 5400) ≤ val WuPaper.ClassicalFourthData.Bq 5400
    have hp : val WuPaper.ClassicalFourthData.Bq 5400 = (255049351688380:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 5400 = 255049351688380 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 5400 = (67:ℝ)/20 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_5400
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 5401) ≤ val WuPaper.ClassicalFourthData.Bq 5401
    have hp : val WuPaper.ClassicalFourthData.Bq 5401 = (255062071629439:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 5401 = 255062071629439 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 5401 = (13401:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_5401
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 5402) ≤ val WuPaper.ClassicalFourthData.Bq 5402
    have hp : val WuPaper.ClassicalFourthData.Bq 5402 = (255074786295195:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 5402 = 255074786295195 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 5402 = (6701:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_5402
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 5403) ≤ val WuPaper.ClassicalFourthData.Bq 5403
    have hp : val WuPaper.ClassicalFourthData.Bq 5403 = (255087495687549:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 5403 = 255087495687549 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 5403 = (13403:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_5403
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 5404) ≤ val WuPaper.ClassicalFourthData.Bq 5404
    have hp : val WuPaper.ClassicalFourthData.Bq 5404 = (255100199808396:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 5404 = 255100199808396 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 5404 = (3351:ℝ)/1000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_5404
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 5405) ≤ val WuPaper.ClassicalFourthData.Bq 5405
    have hp : val WuPaper.ClassicalFourthData.Bq 5405 = (255112898659637:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 5405 = 255112898659637 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 5405 = (2681:ℝ)/800 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_5405
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 5406) ≤ val WuPaper.ClassicalFourthData.Bq 5406
    have hp : val WuPaper.ClassicalFourthData.Bq 5406 = (255125592243166:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 5406 = 255125592243166 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 5406 = (6703:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_5406
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 5407) ≤ val WuPaper.ClassicalFourthData.Bq 5407
    have hp : val WuPaper.ClassicalFourthData.Bq 5407 = (255138280560879:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 5407 = 255138280560879 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 5407 = (13407:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_5407
end WuPaper.ClassicalFourthConditions
#print axioms WuPaper.ClassicalFourthConditions.Log_block_337

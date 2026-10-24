import WR2ClassicalFourthConditions
import WR2ClassicalFourthLogPoints087
noncomputable section
namespace WuPaper.ClassicalFourthConditions
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem Log_block_087 (j : Fin 16) (hj : 16*87+j.val < 10541) :
    WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 (16*87+j.val)) ≤ val WuPaper.ClassicalFourthData.Bq (16*87+j.val) := by
  fin_cases j
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 1392) ≤ val WuPaper.ClassicalFourthData.Bq 1392
    have hp : val WuPaper.ClassicalFourthData.Bq 1392 = (127181436324581:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 1392 = 127181436324581 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 1392 = (587:ℝ)/250 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_1392
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 1393) ≤ val WuPaper.ClassicalFourthData.Bq 1393
    have hp : val WuPaper.ClassicalFourthData.Bq 1393 = (127246866915874:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 1393 = 127246866915874 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 1393 = (9393:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_1393
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 1394) ≤ val WuPaper.ClassicalFourthData.Bq 1394
    have hp : val WuPaper.ClassicalFourthData.Bq 1394 = (127312268936619:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 1394 = 127312268936619 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 1394 = (4697:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_1394
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 1395) ≤ val WuPaper.ClassicalFourthData.Bq 1395
    have hp : val WuPaper.ClassicalFourthData.Bq 1395 = (127377642401366:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 1395 = 127377642401366 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 1395 = (1879:ℝ)/800 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_1395
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 1396) ≤ val WuPaper.ClassicalFourthData.Bq 1396
    have hp : val WuPaper.ClassicalFourthData.Bq 1396 = (127442987324657:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 1396 = 127442987324657 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 1396 = (2349:ℝ)/1000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_1396
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 1397) ≤ val WuPaper.ClassicalFourthData.Bq 1397
    have hp : val WuPaper.ClassicalFourthData.Bq 1397 = (127508303721024:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 1397 = 127508303721024 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 1397 = (9397:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_1397
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 1398) ≤ val WuPaper.ClassicalFourthData.Bq 1398
    have hp : val WuPaper.ClassicalFourthData.Bq 1398 = (127573591604990:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 1398 = 127573591604990 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 1398 = (4699:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_1398
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 1399) ≤ val WuPaper.ClassicalFourthData.Bq 1399
    have hp : val WuPaper.ClassicalFourthData.Bq 1399 = (127638850991067:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 1399 = 127638850991067 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 1399 = (9399:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_1399
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 1400) ≤ val WuPaper.ClassicalFourthData.Bq 1400
    have hp : val WuPaper.ClassicalFourthData.Bq 1400 = (127704081893761:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 1400 = 127704081893761 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 1400 = (47:ℝ)/20 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_1400
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 1401) ≤ val WuPaper.ClassicalFourthData.Bq 1401
    have hp : val WuPaper.ClassicalFourthData.Bq 1401 = (127769284327567:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 1401 = 127769284327567 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 1401 = (9401:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_1401
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 1402) ≤ val WuPaper.ClassicalFourthData.Bq 1402
    have hp : val WuPaper.ClassicalFourthData.Bq 1402 = (127834458306971:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 1402 = 127834458306971 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 1402 = (4701:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_1402
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 1403) ≤ val WuPaper.ClassicalFourthData.Bq 1403
    have hp : val WuPaper.ClassicalFourthData.Bq 1403 = (127899603846449:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 1403 = 127899603846449 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 1403 = (9403:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_1403
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 1404) ≤ val WuPaper.ClassicalFourthData.Bq 1404
    have hp : val WuPaper.ClassicalFourthData.Bq 1404 = (127964720960469:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 1404 = 127964720960469 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 1404 = (2351:ℝ)/1000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_1404
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 1405) ≤ val WuPaper.ClassicalFourthData.Bq 1405
    have hp : val WuPaper.ClassicalFourthData.Bq 1405 = (128029809663491:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 1405 = 128029809663491 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 1405 = (1881:ℝ)/800 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_1405
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 1406) ≤ val WuPaper.ClassicalFourthData.Bq 1406
    have hp : val WuPaper.ClassicalFourthData.Bq 1406 = (128094869969962:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 1406 = 128094869969962 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 1406 = (4703:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_1406
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 1407) ≤ val WuPaper.ClassicalFourthData.Bq 1407
    have hp : val WuPaper.ClassicalFourthData.Bq 1407 = (128159901894325:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 1407 = 128159901894325 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 1407 = (9407:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_1407
end WuPaper.ClassicalFourthConditions
#print axioms WuPaper.ClassicalFourthConditions.Log_block_087

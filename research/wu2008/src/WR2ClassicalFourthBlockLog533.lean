import WR2ClassicalFourthConditions
import WR2ClassicalFourthLogPoints533
noncomputable section
namespace WuPaper.ClassicalFourthConditions
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem Log_block_533 (j : Fin 16) (hj : 16*533+j.val < 10541) :
    WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 (16*533+j.val)) ≤ val WuPaper.ClassicalFourthData.Bq (16*533+j.val) := by
  fin_cases j
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 8528) ≤ val WuPaper.ClassicalFourthData.Bq 8528
    have hp : val WuPaper.ClassicalFourthData.Bq 8528 = (276300043111316:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 8528 = 276300043111316 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 8528 = (1033:ℝ)/250 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_8528
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 8529) ≤ val WuPaper.ClassicalFourthData.Bq 8529
    have hp : val WuPaper.ClassicalFourthData.Bq 8529 = (276302642906634:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 8529 = 276302642906634 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 8529 = (16529:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_8529
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 8530) ≤ val WuPaper.ClassicalFourthData.Bq 8530
    have hp : val WuPaper.ClassicalFourthData.Bq 8530 = (276305240845859:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 8530 = 276305240845859 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 8530 = (1653:ℝ)/400 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_8530
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 8531) ≤ val WuPaper.ClassicalFourthData.Bq 8531
    have hp : val WuPaper.ClassicalFourthData.Bq 8531 = (276307836929575:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 8531 = 276307836929575 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 8531 = (16531:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_8531
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 8532) ≤ val WuPaper.ClassicalFourthData.Bq 8532
    have hp : val WuPaper.ClassicalFourthData.Bq 8532 = (276310431158362:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 8532 = 276310431158362 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 8532 = (4133:ℝ)/1000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_8532
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 8533) ≤ val WuPaper.ClassicalFourthData.Bq 8533
    have hp : val WuPaper.ClassicalFourthData.Bq 8533 = (276313023532805:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 8533 = 276313023532805 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 8533 = (16533:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_8533
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 8534) ≤ val WuPaper.ClassicalFourthData.Bq 8534
    have hp : val WuPaper.ClassicalFourthData.Bq 8534 = (276315614053485:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 8534 = 276315614053485 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 8534 = (8267:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_8534
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 8535) ≤ val WuPaper.ClassicalFourthData.Bq 8535
    have hp : val WuPaper.ClassicalFourthData.Bq 8535 = (276318202720984:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 8535 = 276318202720984 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 8535 = (3307:ℝ)/800 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_8535
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 8536) ≤ val WuPaper.ClassicalFourthData.Bq 8536
    have hp : val WuPaper.ClassicalFourthData.Bq 8536 = (276320789535884:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 8536 = 276320789535884 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 8536 = (2067:ℝ)/500 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_8536
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 8537) ≤ val WuPaper.ClassicalFourthData.Bq 8537
    have hp : val WuPaper.ClassicalFourthData.Bq 8537 = (276323374498767:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 8537 = 276323374498767 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 8537 = (16537:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_8537
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 8538) ≤ val WuPaper.ClassicalFourthData.Bq 8538
    have hp : val WuPaper.ClassicalFourthData.Bq 8538 = (276325957610214:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 8538 = 276325957610214 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 8538 = (8269:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_8538
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 8539) ≤ val WuPaper.ClassicalFourthData.Bq 8539
    have hp : val WuPaper.ClassicalFourthData.Bq 8539 = (276328538870807:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 8539 = 276328538870807 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 8539 = (16539:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_8539
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 8540) ≤ val WuPaper.ClassicalFourthData.Bq 8540
    have hp : val WuPaper.ClassicalFourthData.Bq 8540 = (276331118281126:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 8540 = 276331118281126 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 8540 = (827:ℝ)/200 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_8540
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 8541) ≤ val WuPaper.ClassicalFourthData.Bq 8541
    have hp : val WuPaper.ClassicalFourthData.Bq 8541 = (276333695841753:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 8541 = 276333695841753 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 8541 = (16541:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_8541
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 8542) ≤ val WuPaper.ClassicalFourthData.Bq 8542
    have hp : val WuPaper.ClassicalFourthData.Bq 8542 = (276336271553268:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 8542 = 276336271553268 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 8542 = (8271:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_8542
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 8543) ≤ val WuPaper.ClassicalFourthData.Bq 8543
    have hp : val WuPaper.ClassicalFourthData.Bq 8543 = (276338845416252:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 8543 = 276338845416252 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 8543 = (16543:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_8543
end WuPaper.ClassicalFourthConditions
#print axioms WuPaper.ClassicalFourthConditions.Log_block_533

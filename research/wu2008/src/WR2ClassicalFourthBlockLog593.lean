import WR2ClassicalFourthConditions
import WR2ClassicalFourthLogPoints593
noncomputable section
namespace WuPaper.ClassicalFourthConditions
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem Log_block_593 (j : Fin 16) (hj : 16*593+j.val < 10541) :
    WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 (16*593+j.val)) ≤ val WuPaper.ClassicalFourthData.Bq (16*593+j.val) := by
  fin_cases j
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 9488) ≤ val WuPaper.ClassicalFourthData.Bq 9488
    have hp : val WuPaper.ClassicalFourthData.Bq 9488 = (278020594734956:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 9488 = 278020594734956 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 9488 = (1093:ℝ)/250 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_9488
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 9489) ≤ val WuPaper.ClassicalFourthData.Bq 9489
    have hp : val WuPaper.ClassicalFourthData.Bq 9489 = (278021654161894:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 9489 = 278021654161894 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 9489 = (17489:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_9489
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 9490) ≤ val WuPaper.ClassicalFourthData.Bq 9490
    have hp : val WuPaper.ClassicalFourthData.Bq 9490 = (278022712210756:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 9490 = 278022712210756 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 9490 = (1749:ℝ)/400 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_9490
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 9491) ≤ val WuPaper.ClassicalFourthData.Bq 9491
    have hp : val WuPaper.ClassicalFourthData.Bq 9491 = (278023768881966:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 9491 = 278023768881966 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 9491 = (17491:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_9491
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 9492) ≤ val WuPaper.ClassicalFourthData.Bq 9492
    have hp : val WuPaper.ClassicalFourthData.Bq 9492 = (278024824175946:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 9492 = 278024824175946 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 9492 = (4373:ℝ)/1000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_9492
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 9493) ≤ val WuPaper.ClassicalFourthData.Bq 9493
    have hp : val WuPaper.ClassicalFourthData.Bq 9493 = (278025878093118:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 9493 = 278025878093118 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 9493 = (17493:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_9493
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 9494) ≤ val WuPaper.ClassicalFourthData.Bq 9494
    have hp : val WuPaper.ClassicalFourthData.Bq 9494 = (278026930633905:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 9494 = 278026930633905 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 9494 = (8747:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_9494
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 9495) ≤ val WuPaper.ClassicalFourthData.Bq 9495
    have hp : val WuPaper.ClassicalFourthData.Bq 9495 = (278027981798728:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 9495 = 278027981798728 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 9495 = (3499:ℝ)/800 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_9495
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 9496) ≤ val WuPaper.ClassicalFourthData.Bq 9496
    have hp : val WuPaper.ClassicalFourthData.Bq 9496 = (278029031588010:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 9496 = 278029031588010 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 9496 = (2187:ℝ)/500 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_9496
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 9497) ≤ val WuPaper.ClassicalFourthData.Bq 9497
    have hp : val WuPaper.ClassicalFourthData.Bq 9497 = (278030080002173:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 9497 = 278030080002173 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 9497 = (17497:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_9497
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 9498) ≤ val WuPaper.ClassicalFourthData.Bq 9498
    have hp : val WuPaper.ClassicalFourthData.Bq 9498 = (278031127041638:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 9498 = 278031127041638 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 9498 = (8749:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_9498
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 9499) ≤ val WuPaper.ClassicalFourthData.Bq 9499
    have hp : val WuPaper.ClassicalFourthData.Bq 9499 = (278032172706827:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 9499 = 278032172706827 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 9499 = (17499:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_9499
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 9500) ≤ val WuPaper.ClassicalFourthData.Bq 9500
    have hp : val WuPaper.ClassicalFourthData.Bq 9500 = (278033216998161:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 9500 = 278033216998161 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 9500 = (35:ℝ)/8 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_9500
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 9501) ≤ val WuPaper.ClassicalFourthData.Bq 9501
    have hp : val WuPaper.ClassicalFourthData.Bq 9501 = (278034259916063:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 9501 = 278034259916063 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 9501 = (17501:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_9501
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 9502) ≤ val WuPaper.ClassicalFourthData.Bq 9502
    have hp : val WuPaper.ClassicalFourthData.Bq 9502 = (278035301460952:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 9502 = 278035301460952 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 9502 = (8751:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_9502
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 9503) ≤ val WuPaper.ClassicalFourthData.Bq 9503
    have hp : val WuPaper.ClassicalFourthData.Bq 9503 = (278036341633250:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 9503 = 278036341633250 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 9503 = (17503:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_9503
end WuPaper.ClassicalFourthConditions
#print axioms WuPaper.ClassicalFourthConditions.Log_block_593

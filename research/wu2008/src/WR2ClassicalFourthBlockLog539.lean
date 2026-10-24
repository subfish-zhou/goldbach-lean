import WR2ClassicalFourthConditions
import WR2ClassicalFourthLogPoints539
noncomputable section
namespace WuPaper.ClassicalFourthConditions
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem Log_block_539 (j : Fin 16) (hj : 16*539+j.val < 10541) :
    WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 (16*539+j.val)) ≤ val WuPaper.ClassicalFourthData.Bq (16*539+j.val) := by
  fin_cases j
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 8624) ≤ val WuPaper.ClassicalFourthData.Bq 8624
    have hp : val WuPaper.ClassicalFourthData.Bq 8624 = (276541242298490:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 8624 = 276541242298490 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 8624 = (1039:ℝ)/250 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_8624
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 8625) ≤ val WuPaper.ClassicalFourthData.Bq 8625
    have hp : val WuPaper.ClassicalFourthData.Bq 8625 = (276543666538453:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 8625 = 276543666538453 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 8625 = (133:ℝ)/32 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_8625
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 8626) ≤ val WuPaper.ClassicalFourthData.Bq 8626
    have hp : val WuPaper.ClassicalFourthData.Bq 8626 = (276546088977378:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 8626 = 276546088977378 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 8626 = (8313:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_8626
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 8627) ≤ val WuPaper.ClassicalFourthData.Bq 8627
    have hp : val WuPaper.ClassicalFourthData.Bq 8627 = (276548509615829:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 8627 = 276548509615829 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 8627 = (16627:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_8627
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 8628) ≤ val WuPaper.ClassicalFourthData.Bq 8628
    have hp : val WuPaper.ClassicalFourthData.Bq 8628 = (276550928454370:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 8628 = 276550928454370 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 8628 = (4157:ℝ)/1000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_8628
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 8629) ≤ val WuPaper.ClassicalFourthData.Bq 8629
    have hp : val WuPaper.ClassicalFourthData.Bq 8629 = (276553345493565:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 8629 = 276553345493565 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 8629 = (16629:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_8629
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 8630) ≤ val WuPaper.ClassicalFourthData.Bq 8630
    have hp : val WuPaper.ClassicalFourthData.Bq 8630 = (276555760733976:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 8630 = 276555760733976 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 8630 = (1663:ℝ)/400 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_8630
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 8631) ≤ val WuPaper.ClassicalFourthData.Bq 8631
    have hp : val WuPaper.ClassicalFourthData.Bq 8631 = (276558174176168:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 8631 = 276558174176168 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 8631 = (16631:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_8631
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 8632) ≤ val WuPaper.ClassicalFourthData.Bq 8632
    have hp : val WuPaper.ClassicalFourthData.Bq 8632 = (276560585820703:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 8632 = 276560585820703 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 8632 = (2079:ℝ)/500 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_8632
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 8633) ≤ val WuPaper.ClassicalFourthData.Bq 8633
    have hp : val WuPaper.ClassicalFourthData.Bq 8633 = (276562995668144:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 8633 = 276562995668144 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 8633 = (16633:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_8633
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 8634) ≤ val WuPaper.ClassicalFourthData.Bq 8634
    have hp : val WuPaper.ClassicalFourthData.Bq 8634 = (276565403719054:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 8634 = 276565403719054 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 8634 = (8317:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_8634
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 8635) ≤ val WuPaper.ClassicalFourthData.Bq 8635
    have hp : val WuPaper.ClassicalFourthData.Bq 8635 = (276567809973995:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 8635 = 276567809973995 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 8635 = (3327:ℝ)/800 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_8635
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 8636) ≤ val WuPaper.ClassicalFourthData.Bq 8636
    have hp : val WuPaper.ClassicalFourthData.Bq 8636 = (276570214433529:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 8636 = 276570214433529 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 8636 = (4159:ℝ)/1000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_8636
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 8637) ≤ val WuPaper.ClassicalFourthData.Bq 8637
    have hp : val WuPaper.ClassicalFourthData.Bq 8637 = (276572617098220:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 8637 = 276572617098220 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 8637 = (16637:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_8637
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 8638) ≤ val WuPaper.ClassicalFourthData.Bq 8638
    have hp : val WuPaper.ClassicalFourthData.Bq 8638 = (276575017968628:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 8638 = 276575017968628 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 8638 = (8319:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_8638
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 8639) ≤ val WuPaper.ClassicalFourthData.Bq 8639
    have hp : val WuPaper.ClassicalFourthData.Bq 8639 = (276577417045316:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 8639 = 276577417045316 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 8639 = (16639:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_8639
end WuPaper.ClassicalFourthConditions
#print axioms WuPaper.ClassicalFourthConditions.Log_block_539

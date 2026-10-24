import WR2ClassicalFourthConditions
import WR2ClassicalFourthLogPoints039
noncomputable section
namespace WuPaper.ClassicalFourthConditions
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem Log_block_039 (j : Fin 16) (hj : 16*39+j.val < 10541) :
    WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 (16*39+j.val)) ≤ val WuPaper.ClassicalFourthData.Bq (16*39+j.val) := by
  fin_cases j
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 624) ≤ val WuPaper.ClassicalFourthData.Bq 624
    have hp : val WuPaper.ClassicalFourthData.Bq 624 = (67238297889697:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 624 = 67238297889697 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 624 = (539:ℝ)/250 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_624
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 625) ≤ val WuPaper.ClassicalFourthData.Bq 625
    have hp : val WuPaper.ClassicalFourthData.Bq 625 = (67330787174260:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 625 = 67330787174260 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 625 = (69:ℝ)/32 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_625
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 626) ≤ val WuPaper.ClassicalFourthData.Bq 626
    have hp : val WuPaper.ClassicalFourthData.Bq 626 = (67423233336127:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 626 = 67423233336127 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 626 = (4313:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_626
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 627) ≤ val WuPaper.ClassicalFourthData.Bq 627
    have hp : val WuPaper.ClassicalFourthData.Bq 627 = (67515636399663:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 627 = 67515636399663 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 627 = (8627:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_627
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 628) ≤ val WuPaper.ClassicalFourthData.Bq 628
    have hp : val WuPaper.ClassicalFourthData.Bq 628 = (67607996389217:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 628 = 67607996389217 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 628 = (2157:ℝ)/1000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_628
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 629) ≤ val WuPaper.ClassicalFourthData.Bq 629
    have hp : val WuPaper.ClassicalFourthData.Bq 629 = (67700313329120:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 629 = 67700313329120 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 629 = (8629:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_629
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 630) ≤ val WuPaper.ClassicalFourthData.Bq 630
    have hp : val WuPaper.ClassicalFourthData.Bq 630 = (67792587243686:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 630 = 67792587243686 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 630 = (863:ℝ)/400 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_630
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 631) ≤ val WuPaper.ClassicalFourthData.Bq 631
    have hp : val WuPaper.ClassicalFourthData.Bq 631 = (67884818157213:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 631 = 67884818157213 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 631 = (8631:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_631
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 632) ≤ val WuPaper.ClassicalFourthData.Bq 632
    have hp : val WuPaper.ClassicalFourthData.Bq 632 = (67977006093978:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 632 = 67977006093978 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 632 = (1079:ℝ)/500 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_632
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 633) ≤ val WuPaper.ClassicalFourthData.Bq 633
    have hp : val WuPaper.ClassicalFourthData.Bq 633 = (68069151078245:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 633 = 68069151078245 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 633 = (8633:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_633
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 634) ≤ val WuPaper.ClassicalFourthData.Bq 634
    have hp : val WuPaper.ClassicalFourthData.Bq 634 = (68161253134258:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 634 = 68161253134258 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 634 = (4317:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_634
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 635) ≤ val WuPaper.ClassicalFourthData.Bq 635
    have hp : val WuPaper.ClassicalFourthData.Bq 635 = (68253312286244:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 635 = 68253312286244 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 635 = (1727:ℝ)/800 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_635
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 636) ≤ val WuPaper.ClassicalFourthData.Bq 636
    have hp : val WuPaper.ClassicalFourthData.Bq 636 = (68345328558414:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 636 = 68345328558414 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 636 = (2159:ℝ)/1000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_636
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 637) ≤ val WuPaper.ClassicalFourthData.Bq 637
    have hp : val WuPaper.ClassicalFourthData.Bq 637 = (68437301974961:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 637 = 68437301974961 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 637 = (8637:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_637
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 638) ≤ val WuPaper.ClassicalFourthData.Bq 638
    have hp : val WuPaper.ClassicalFourthData.Bq 638 = (68529232560060:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 638 = 68529232560060 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 638 = (4319:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_638
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 639) ≤ val WuPaper.ClassicalFourthData.Bq 639
    have hp : val WuPaper.ClassicalFourthData.Bq 639 = (68621120337871:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 639 = 68621120337871 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 639 = (8639:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_639
end WuPaper.ClassicalFourthConditions
#print axioms WuPaper.ClassicalFourthConditions.Log_block_039

import WR2ClassicalFourthConditions
import WR2ClassicalFourthLogPoints357
noncomputable section
namespace WuPaper.ClassicalFourthConditions
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem Log_block_357 (j : Fin 16) (hj : 16*357+j.val < 10541) :
    WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 (16*357+j.val)) ≤ val WuPaper.ClassicalFourthData.Bq (16*357+j.val) := by
  fin_cases j
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 5712) ≤ val WuPaper.ClassicalFourthData.Bq 5712
    have hp : val WuPaper.ClassicalFourthData.Bq 5712 = (258771258225572:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 5712 = 258771258225572 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 5712 = (857:ℝ)/250 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_5712
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 5713) ≤ val WuPaper.ClassicalFourthData.Bq 5713
    have hp : val WuPaper.ClassicalFourthData.Bq 5713 = (258782420564519:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 5713 = 258782420564519 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 5713 = (13713:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_5713
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 5714) ≤ val WuPaper.ClassicalFourthData.Bq 5714
    have hp : val WuPaper.ClassicalFourthData.Bq 5714 = (258793578183949:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 5714 = 258793578183949 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 5714 = (6857:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_5714
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 5715) ≤ val WuPaper.ClassicalFourthData.Bq 5715
    have hp : val WuPaper.ClassicalFourthData.Bq 5715 = (258804731085533:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 5715 = 258804731085533 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 5715 = (2743:ℝ)/800 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_5715
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 5716) ≤ val WuPaper.ClassicalFourthData.Bq 5716
    have hp : val WuPaper.ClassicalFourthData.Bq 5716 = (258815879270937:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 5716 = 258815879270937 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 5716 = (3429:ℝ)/1000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_5716
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 5717) ≤ val WuPaper.ClassicalFourthData.Bq 5717
    have hp : val WuPaper.ClassicalFourthData.Bq 5717 = (258827022741830:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 5717 = 258827022741830 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 5717 = (13717:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_5717
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 5718) ≤ val WuPaper.ClassicalFourthData.Bq 5718
    have hp : val WuPaper.ClassicalFourthData.Bq 5718 = (258838161499877:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 5718 = 258838161499877 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 5718 = (6859:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_5718
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 5719) ≤ val WuPaper.ClassicalFourthData.Bq 5719
    have hp : val WuPaper.ClassicalFourthData.Bq 5719 = (258849295546746:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 5719 = 258849295546746 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 5719 = (13719:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_5719
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 5720) ≤ val WuPaper.ClassicalFourthData.Bq 5720
    have hp : val WuPaper.ClassicalFourthData.Bq 5720 = (258860424884101:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 5720 = 258860424884101 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 5720 = (343:ℝ)/100 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_5720
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 5721) ≤ val WuPaper.ClassicalFourthData.Bq 5721
    have hp : val WuPaper.ClassicalFourthData.Bq 5721 = (258871549513607:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 5721 = 258871549513607 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 5721 = (13721:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_5721
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 5722) ≤ val WuPaper.ClassicalFourthData.Bq 5722
    have hp : val WuPaper.ClassicalFourthData.Bq 5722 = (258882669436928:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 5722 = 258882669436928 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 5722 = (6861:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_5722
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 5723) ≤ val WuPaper.ClassicalFourthData.Bq 5723
    have hp : val WuPaper.ClassicalFourthData.Bq 5723 = (258893784655728:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 5723 = 258893784655728 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 5723 = (13723:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_5723
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 5724) ≤ val WuPaper.ClassicalFourthData.Bq 5724
    have hp : val WuPaper.ClassicalFourthData.Bq 5724 = (258904895171669:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 5724 = 258904895171669 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 5724 = (3431:ℝ)/1000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_5724
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 5725) ≤ val WuPaper.ClassicalFourthData.Bq 5725
    have hp : val WuPaper.ClassicalFourthData.Bq 5725 = (258916000986413:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 5725 = 258916000986413 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 5725 = (549:ℝ)/160 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_5725
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 5726) ≤ val WuPaper.ClassicalFourthData.Bq 5726
    have hp : val WuPaper.ClassicalFourthData.Bq 5726 = (258927102101621:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 5726 = 258927102101621 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 5726 = (6863:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_5726
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 5727) ≤ val WuPaper.ClassicalFourthData.Bq 5727
    have hp : val WuPaper.ClassicalFourthData.Bq 5727 = (258938198518954:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 5727 = 258938198518954 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 5727 = (13727:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_5727
end WuPaper.ClassicalFourthConditions
#print axioms WuPaper.ClassicalFourthConditions.Log_block_357

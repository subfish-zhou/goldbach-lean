import WR2ClassicalFourthConditions
import WR2ClassicalFourthLogPoints228
noncomputable section
namespace WuPaper.ClassicalFourthConditions
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem Log_block_228 (j : Fin 16) (hj : 16*228+j.val < 10541) :
    WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 (16*228+j.val)) ≤ val WuPaper.ClassicalFourthData.Bq (16*228+j.val) := by
  fin_cases j
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 3648) ≤ val WuPaper.ClassicalFourthData.Bq 3648
    have hp : val WuPaper.ClassicalFourthData.Bq 3648 = (222578919858932:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 3648 = 222578919858932 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 3648 = (364:ℝ)/125 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_3648
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 3649) ≤ val WuPaper.ClassicalFourthData.Bq 3649
    have hp : val WuPaper.ClassicalFourthData.Bq 3649 = (222604707432343:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 3649 = 222604707432343 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 3649 = (11649:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_3649
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 3650) ≤ val WuPaper.ClassicalFourthData.Bq 3650
    have hp : val WuPaper.ClassicalFourthData.Bq 3650 = (222630484710234:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 3650 = 222630484710234 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 3650 = (233:ℝ)/80 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_3650
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 3651) ≤ val WuPaper.ClassicalFourthData.Bq 3651
    have hp : val WuPaper.ClassicalFourthData.Bq 3651 = (222656251696790:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 3651 = 222656251696790 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 3651 = (11651:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_3651
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 3652) ≤ val WuPaper.ClassicalFourthData.Bq 3652
    have hp : val WuPaper.ClassicalFourthData.Bq 3652 = (222682008396195:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 3652 = 222682008396195 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 3652 = (2913:ℝ)/1000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_3652
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 3653) ≤ val WuPaper.ClassicalFourthData.Bq 3653
    have hp : val WuPaper.ClassicalFourthData.Bq 3653 = (222707754812630:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 3653 = 222707754812630 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 3653 = (11653:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_3653
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 3654) ≤ val WuPaper.ClassicalFourthData.Bq 3654
    have hp : val WuPaper.ClassicalFourthData.Bq 3654 = (222733490950273:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 3654 = 222733490950273 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 3654 = (5827:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_3654
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 3655) ≤ val WuPaper.ClassicalFourthData.Bq 3655
    have hp : val WuPaper.ClassicalFourthData.Bq 3655 = (222759216813302:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 3655 = 222759216813302 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 3655 = (2331:ℝ)/800 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_3655
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 3656) ≤ val WuPaper.ClassicalFourthData.Bq 3656
    have hp : val WuPaper.ClassicalFourthData.Bq 3656 = (222784932405890:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 3656 = 222784932405890 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 3656 = (1457:ℝ)/500 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_3656
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 3657) ≤ val WuPaper.ClassicalFourthData.Bq 3657
    have hp : val WuPaper.ClassicalFourthData.Bq 3657 = (222810637732211:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 3657 = 222810637732211 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 3657 = (11657:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_3657
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 3658) ≤ val WuPaper.ClassicalFourthData.Bq 3658
    have hp : val WuPaper.ClassicalFourthData.Bq 3658 = (222836332796436:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 3658 = 222836332796436 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 3658 = (5829:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_3658
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 3659) ≤ val WuPaper.ClassicalFourthData.Bq 3659
    have hp : val WuPaper.ClassicalFourthData.Bq 3659 = (222862017602733:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 3659 = 222862017602733 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 3659 = (11659:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_3659
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 3660) ≤ val WuPaper.ClassicalFourthData.Bq 3660
    have hp : val WuPaper.ClassicalFourthData.Bq 3660 = (222887692155270:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 3660 = 222887692155270 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 3660 = (583:ℝ)/200 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_3660
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 3661) ≤ val WuPaper.ClassicalFourthData.Bq 3661
    have hp : val WuPaper.ClassicalFourthData.Bq 3661 = (222913356458209:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 3661 = 222913356458209 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 3661 = (11661:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_3661
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 3662) ≤ val WuPaper.ClassicalFourthData.Bq 3662
    have hp : val WuPaper.ClassicalFourthData.Bq 3662 = (222939010515715:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 3662 = 222939010515715 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 3662 = (5831:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_3662
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 3663) ≤ val WuPaper.ClassicalFourthData.Bq 3663
    have hp : val WuPaper.ClassicalFourthData.Bq 3663 = (222964654331948:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 3663 = 222964654331948 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 3663 = (11663:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_3663
end WuPaper.ClassicalFourthConditions
#print axioms WuPaper.ClassicalFourthConditions.Log_block_228

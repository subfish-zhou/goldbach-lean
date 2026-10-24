import WR2ClassicalFourthConditions
import WR2ClassicalFourthLogPoints603
noncomputable section
namespace WuPaper.ClassicalFourthConditions
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem Log_block_603 (j : Fin 16) (hj : 16*603+j.val < 10541) :
    WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 (16*603+j.val)) ≤ val WuPaper.ClassicalFourthData.Bq (16*603+j.val) := by
  fin_cases j
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 9648) ≤ val WuPaper.ClassicalFourthData.Bq 9648
    have hp : val WuPaper.ClassicalFourthData.Bq 9648 = (278172853509447:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 9648 = 278172853509447 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 9648 = (1103:ℝ)/250 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_9648
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 9649) ≤ val WuPaper.ClassicalFourthData.Bq 9649
    have hp : val WuPaper.ClassicalFourthData.Bq 9649 = (278173697729844:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 9649 = 278173697729844 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 9649 = (17649:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_9649
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 9650) ≤ val WuPaper.ClassicalFourthData.Bq 9650
    have hp : val WuPaper.ClassicalFourthData.Bq 9650 = (278174540638075:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 9650 = 278174540638075 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 9650 = (353:ℝ)/80 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_9650
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 9651) ≤ val WuPaper.ClassicalFourthData.Bq 9651
    have hp : val WuPaper.ClassicalFourthData.Bq 9651 = (278175382234540:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 9651 = 278175382234540 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 9651 = (17651:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_9651
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 9652) ≤ val WuPaper.ClassicalFourthData.Bq 9652
    have hp : val WuPaper.ClassicalFourthData.Bq 9652 = (278176222519641:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 9652 = 278176222519641 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 9652 = (4413:ℝ)/1000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_9652
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 9653) ≤ val WuPaper.ClassicalFourthData.Bq 9653
    have hp : val WuPaper.ClassicalFourthData.Bq 9653 = (278177061493779:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 9653 = 278177061493779 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 9653 = (17653:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_9653
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 9654) ≤ val WuPaper.ClassicalFourthData.Bq 9654
    have hp : val WuPaper.ClassicalFourthData.Bq 9654 = (278177899157354:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 9654 = 278177899157354 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 9654 = (8827:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_9654
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 9655) ≤ val WuPaper.ClassicalFourthData.Bq 9655
    have hp : val WuPaper.ClassicalFourthData.Bq 9655 = (278178735510768:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 9655 = 278178735510768 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 9655 = (3531:ℝ)/800 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_9655
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 9656) ≤ val WuPaper.ClassicalFourthData.Bq 9656
    have hp : val WuPaper.ClassicalFourthData.Bq 9656 = (278179570554421:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 9656 = 278179570554421 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 9656 = (2207:ℝ)/500 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_9656
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 9657) ≤ val WuPaper.ClassicalFourthData.Bq 9657
    have hp : val WuPaper.ClassicalFourthData.Bq 9657 = (278180404288713:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 9657 = 278180404288713 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 9657 = (17657:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_9657
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 9658) ≤ val WuPaper.ClassicalFourthData.Bq 9658
    have hp : val WuPaper.ClassicalFourthData.Bq 9658 = (278181236714045:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 9658 = 278181236714045 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 9658 = (8829:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_9658
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 9659) ≤ val WuPaper.ClassicalFourthData.Bq 9659
    have hp : val WuPaper.ClassicalFourthData.Bq 9659 = (278182067830817:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 9659 = 278182067830817 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 9659 = (17659:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_9659
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 9660) ≤ val WuPaper.ClassicalFourthData.Bq 9660
    have hp : val WuPaper.ClassicalFourthData.Bq 9660 = (278182897639429:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 9660 = 278182897639429 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 9660 = (883:ℝ)/200 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_9660
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 9661) ≤ val WuPaper.ClassicalFourthData.Bq 9661
    have hp : val WuPaper.ClassicalFourthData.Bq 9661 = (278183726140281:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 9661 = 278183726140281 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 9661 = (17661:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_9661
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 9662) ≤ val WuPaper.ClassicalFourthData.Bq 9662
    have hp : val WuPaper.ClassicalFourthData.Bq 9662 = (278184553333773:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 9662 = 278184553333773 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 9662 = (8831:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_9662
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 9663) ≤ val WuPaper.ClassicalFourthData.Bq 9663
    have hp : val WuPaper.ClassicalFourthData.Bq 9663 = (278185379220304:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 9663 = 278185379220304 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 9663 = (17663:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_9663
end WuPaper.ClassicalFourthConditions
#print axioms WuPaper.ClassicalFourthConditions.Log_block_603

import WR2ClassicalFourthConditions
import WR2ClassicalFourthLogPoints353
noncomputable section
namespace WuPaper.ClassicalFourthConditions
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem Log_block_353 (j : Fin 16) (hj : 16*353+j.val < 10541) :
    WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 (16*353+j.val)) ≤ val WuPaper.ClassicalFourthData.Bq (16*353+j.val) := by
  fin_cases j
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 5648) ≤ val WuPaper.ClassicalFourthData.Bq 5648
    have hp : val WuPaper.ClassicalFourthData.Bq 5648 = (258046975048343:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 5648 = 258046975048343 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 5648 = (853:ℝ)/250 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_5648
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 5649) ≤ val WuPaper.ClassicalFourthData.Bq 5649
    have hp : val WuPaper.ClassicalFourthData.Bq 5649 = (258058442938930:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 5649 = 258058442938930 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 5649 = (13649:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_5649
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 5650) ≤ val WuPaper.ClassicalFourthData.Bq 5650
    have hp : val WuPaper.ClassicalFourthData.Bq 5650 = (258069906001761:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 5650 = 258069906001761 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 5650 = (273:ℝ)/80 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_5650
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 5651) ≤ val WuPaper.ClassicalFourthData.Bq 5651
    have hp : val WuPaper.ClassicalFourthData.Bq 5651 = (258081364238551:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 5651 = 258081364238551 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 5651 = (13651:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_5651
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 5652) ≤ val WuPaper.ClassicalFourthData.Bq 5652
    have hp : val WuPaper.ClassicalFourthData.Bq 5652 = (258092817651011:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 5652 = 258092817651011 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 5652 = (3413:ℝ)/1000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_5652
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 5653) ≤ val WuPaper.ClassicalFourthData.Bq 5653
    have hp : val WuPaper.ClassicalFourthData.Bq 5653 = (258104266240854:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 5653 = 258104266240854 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 5653 = (13653:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_5653
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 5654) ≤ val WuPaper.ClassicalFourthData.Bq 5654
    have hp : val WuPaper.ClassicalFourthData.Bq 5654 = (258115710009790:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 5654 = 258115710009790 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 5654 = (6827:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_5654
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 5655) ≤ val WuPaper.ClassicalFourthData.Bq 5655
    have hp : val WuPaper.ClassicalFourthData.Bq 5655 = (258127148959530:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 5655 = 258127148959530 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 5655 = (2731:ℝ)/800 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_5655
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 5656) ≤ val WuPaper.ClassicalFourthData.Bq 5656
    have hp : val WuPaper.ClassicalFourthData.Bq 5656 = (258138583091783:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 5656 = 258138583091783 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 5656 = (1707:ℝ)/500 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_5656
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 5657) ≤ val WuPaper.ClassicalFourthData.Bq 5657
    have hp : val WuPaper.ClassicalFourthData.Bq 5657 = (258150012408259:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 5657 = 258150012408259 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 5657 = (13657:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_5657
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 5658) ≤ val WuPaper.ClassicalFourthData.Bq 5658
    have hp : val WuPaper.ClassicalFourthData.Bq 5658 = (258161436910665:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 5658 = 258161436910665 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 5658 = (6829:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_5658
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 5659) ≤ val WuPaper.ClassicalFourthData.Bq 5659
    have hp : val WuPaper.ClassicalFourthData.Bq 5659 = (258172856600710:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 5659 = 258172856600710 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 5659 = (13659:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_5659
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 5660) ≤ val WuPaper.ClassicalFourthData.Bq 5660
    have hp : val WuPaper.ClassicalFourthData.Bq 5660 = (258184271480101:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 5660 = 258184271480101 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 5660 = (683:ℝ)/200 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_5660
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 5661) ≤ val WuPaper.ClassicalFourthData.Bq 5661
    have hp : val WuPaper.ClassicalFourthData.Bq 5661 = (258195681550542:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 5661 = 258195681550542 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 5661 = (13661:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_5661
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 5662) ≤ val WuPaper.ClassicalFourthData.Bq 5662
    have hp : val WuPaper.ClassicalFourthData.Bq 5662 = (258207086813741:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 5662 = 258207086813741 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 5662 = (6831:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_5662
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 5663) ≤ val WuPaper.ClassicalFourthData.Bq 5663
    have hp : val WuPaper.ClassicalFourthData.Bq 5663 = (258218487271401:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 5663 = 258218487271401 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 5663 = (13663:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_5663
end WuPaper.ClassicalFourthConditions
#print axioms WuPaper.ClassicalFourthConditions.Log_block_353

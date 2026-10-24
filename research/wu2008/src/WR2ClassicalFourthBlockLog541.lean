import WR2ClassicalFourthConditions
import WR2ClassicalFourthLogPoints541
noncomputable section
namespace WuPaper.ClassicalFourthConditions
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem Log_block_541 (j : Fin 16) (hj : 16*541+j.val < 10541) :
    WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 (16*541+j.val)) ≤ val WuPaper.ClassicalFourthData.Bq (16*541+j.val) := by
  fin_cases j
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 8656) ≤ val WuPaper.ClassicalFourthData.Bq 8656
    have hp : val WuPaper.ClassicalFourthData.Bq 8656 = (276617927453137:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 8656 = 276617927453137 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 8656 = (1041:ℝ)/250 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_8656
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 8657) ≤ val WuPaper.ClassicalFourthData.Bq 8657
    have hp : val WuPaper.ClassicalFourthData.Bq 8657 = (276620294338690:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 8657 = 276620294338690 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 8657 = (16657:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_8657
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 8658) ≤ val WuPaper.ClassicalFourthData.Bq 8658
    have hp : val WuPaper.ClassicalFourthData.Bq 8658 = (276622659441160:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 8658 = 276622659441160 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 8658 = (8329:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_8658
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 8659) ≤ val WuPaper.ClassicalFourthData.Bq 8659
    have hp : val WuPaper.ClassicalFourthData.Bq 8659 = (276625022761104:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 8659 = 276625022761104 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 8659 = (16659:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_8659
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 8660) ≤ val WuPaper.ClassicalFourthData.Bq 8660
    have hp : val WuPaper.ClassicalFourthData.Bq 8660 = (276627384299079:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 8660 = 276627384299079 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 8660 = (833:ℝ)/200 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_8660
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 8661) ≤ val WuPaper.ClassicalFourthData.Bq 8661
    have hp : val WuPaper.ClassicalFourthData.Bq 8661 = (276629744055643:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 8661 = 276629744055643 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 8661 = (16661:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_8661
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 8662) ≤ val WuPaper.ClassicalFourthData.Bq 8662
    have hp : val WuPaper.ClassicalFourthData.Bq 8662 = (276632102031354:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 8662 = 276632102031354 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 8662 = (8331:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_8662
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 8663) ≤ val WuPaper.ClassicalFourthData.Bq 8663
    have hp : val WuPaper.ClassicalFourthData.Bq 8663 = (276634458226768:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 8663 = 276634458226768 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 8663 = (16663:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_8663
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 8664) ≤ val WuPaper.ClassicalFourthData.Bq 8664
    have hp : val WuPaper.ClassicalFourthData.Bq 8664 = (276636812642443:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 8664 = 276636812642443 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 8664 = (2083:ℝ)/500 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_8664
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 8665) ≤ val WuPaper.ClassicalFourthData.Bq 8665
    have hp : val WuPaper.ClassicalFourthData.Bq 8665 = (276639165278935:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 8665 = 276639165278935 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 8665 = (3333:ℝ)/800 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_8665
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 8666) ≤ val WuPaper.ClassicalFourthData.Bq 8666
    have hp : val WuPaper.ClassicalFourthData.Bq 8666 = (276641516136801:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 8666 = 276641516136801 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 8666 = (8333:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_8666
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 8667) ≤ val WuPaper.ClassicalFourthData.Bq 8667
    have hp : val WuPaper.ClassicalFourthData.Bq 8667 = (276643865216597:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 8667 = 276643865216597 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 8667 = (16667:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_8667
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 8668) ≤ val WuPaper.ClassicalFourthData.Bq 8668
    have hp : val WuPaper.ClassicalFourthData.Bq 8668 = (276646212518880:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 8668 = 276646212518880 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 8668 = (4167:ℝ)/1000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_8668
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 8669) ≤ val WuPaper.ClassicalFourthData.Bq 8669
    have hp : val WuPaper.ClassicalFourthData.Bq 8669 = (276648558044205:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 8669 = 276648558044205 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 8669 = (16669:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_8669
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 8670) ≤ val WuPaper.ClassicalFourthData.Bq 8670
    have hp : val WuPaper.ClassicalFourthData.Bq 8670 = (276650901793129:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 8670 = 276650901793129 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 8670 = (1667:ℝ)/400 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_8670
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 8671) ≤ val WuPaper.ClassicalFourthData.Bq 8671
    have hp : val WuPaper.ClassicalFourthData.Bq 8671 = (276653243766206:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 8671 = 276653243766206 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 8671 = (16671:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_8671
end WuPaper.ClassicalFourthConditions
#print axioms WuPaper.ClassicalFourthConditions.Log_block_541

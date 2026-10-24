import WR2ClassicalFourthConditions
import WR2ClassicalFourthLogPoints549
noncomputable section
namespace WuPaper.ClassicalFourthConditions
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem Log_block_549 (j : Fin 16) (hj : 16*549+j.val < 10541) :
    WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 (16*549+j.val)) ≤ val WuPaper.ClassicalFourthData.Bq (16*549+j.val) := by
  fin_cases j
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 8784) ≤ val WuPaper.ClassicalFourthData.Bq 8784
    have hp : val WuPaper.ClassicalFourthData.Bq 8784 = (276906584346055:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 8784 = 276906584346055 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 8784 = (1049:ℝ)/250 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_8784
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 8785) ≤ val WuPaper.ClassicalFourthData.Bq 8785
    have hp : val WuPaper.ClassicalFourthData.Bq 8785 = (276908727467453:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 8785 = 276908727467453 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 8785 = (3357:ℝ)/800 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_8785
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 8786) ≤ val WuPaper.ClassicalFourthData.Bq 8786
    have hp : val WuPaper.ClassicalFourthData.Bq 8786 = (276910868875660:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 8786 = 276910868875660 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 8786 = (8393:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_8786
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 8787) ≤ val WuPaper.ClassicalFourthData.Bq 8787
    have hp : val WuPaper.ClassicalFourthData.Bq 8787 = (276913008571210:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 8787 = 276913008571210 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 8787 = (16787:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_8787
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 8788) ≤ val WuPaper.ClassicalFourthData.Bq 8788
    have hp : val WuPaper.ClassicalFourthData.Bq 8788 = (276915146554637:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 8788 = 276915146554637 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 8788 = (4197:ℝ)/1000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_8788
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 8789) ≤ val WuPaper.ClassicalFourthData.Bq 8789
    have hp : val WuPaper.ClassicalFourthData.Bq 8789 = (276917282826475:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 8789 = 276917282826475 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 8789 = (16789:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_8789
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 8790) ≤ val WuPaper.ClassicalFourthData.Bq 8790
    have hp : val WuPaper.ClassicalFourthData.Bq 8790 = (276919417387258:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 8790 = 276919417387258 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 8790 = (1679:ℝ)/400 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_8790
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 8791) ≤ val WuPaper.ClassicalFourthData.Bq 8791
    have hp : val WuPaper.ClassicalFourthData.Bq 8791 = (276921550237518:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 8791 = 276921550237518 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 8791 = (16791:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_8791
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 8792) ≤ val WuPaper.ClassicalFourthData.Bq 8792
    have hp : val WuPaper.ClassicalFourthData.Bq 8792 = (276923681377790:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 8792 = 276923681377790 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 8792 = (2099:ℝ)/500 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_8792
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 8793) ≤ val WuPaper.ClassicalFourthData.Bq 8793
    have hp : val WuPaper.ClassicalFourthData.Bq 8793 = (276925810808606:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 8793 = 276925810808606 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 8793 = (16793:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_8793
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 8794) ≤ val WuPaper.ClassicalFourthData.Bq 8794
    have hp : val WuPaper.ClassicalFourthData.Bq 8794 = (276927938530499:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 8794 = 276927938530499 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 8794 = (8397:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_8794
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 8795) ≤ val WuPaper.ClassicalFourthData.Bq 8795
    have hp : val WuPaper.ClassicalFourthData.Bq 8795 = (276930064544002:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 8795 = 276930064544002 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 8795 = (3359:ℝ)/800 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_8795
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 8796) ≤ val WuPaper.ClassicalFourthData.Bq 8796
    have hp : val WuPaper.ClassicalFourthData.Bq 8796 = (276932188849648:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 8796 = 276932188849648 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 8796 = (4199:ℝ)/1000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_8796
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 8797) ≤ val WuPaper.ClassicalFourthData.Bq 8797
    have hp : val WuPaper.ClassicalFourthData.Bq 8797 = (276934311447968:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 8797 = 276934311447968 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 8797 = (16797:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_8797
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 8798) ≤ val WuPaper.ClassicalFourthData.Bq 8798
    have hp : val WuPaper.ClassicalFourthData.Bq 8798 = (276936432339496:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 8798 = 276936432339496 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 8798 = (8399:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_8798
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 8799) ≤ val WuPaper.ClassicalFourthData.Bq 8799
    have hp : val WuPaper.ClassicalFourthData.Bq 8799 = (276938551524763:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 8799 = 276938551524763 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 8799 = (16799:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_8799
end WuPaper.ClassicalFourthConditions
#print axioms WuPaper.ClassicalFourthConditions.Log_block_549

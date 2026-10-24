import WR2ClassicalFourthConditions
import WR2ClassicalFourthLogPoints299
noncomputable section
namespace WuPaper.ClassicalFourthConditions
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem Log_block_299 (j : Fin 16) (hj : 16*299+j.val < 10541) :
    WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 (16*299+j.val)) ≤ val WuPaper.ClassicalFourthData.Bq (16*299+j.val) := by
  fin_cases j
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 4784) ≤ val WuPaper.ClassicalFourthData.Bq 4784
    have hp : val WuPaper.ClassicalFourthData.Bq 4784 = (246131891003531:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 4784 = 246131891003531 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 4784 = (799:ℝ)/250 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_4784
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 4785) ≤ val WuPaper.ClassicalFourthData.Bq 4785
    have hp : val WuPaper.ClassicalFourthData.Bq 4785 = (246148255148744:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 4785 = 246148255148744 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 4785 = (2557:ℝ)/800 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_4785
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 4786) ≤ val WuPaper.ClassicalFourthData.Bq 4786
    have hp : val WuPaper.ClassicalFourthData.Bq 4786 = (246164612680650:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 4786 = 246164612680650 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 4786 = (6393:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_4786
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 4787) ≤ val WuPaper.ClassicalFourthData.Bq 4787
    have hp : val WuPaper.ClassicalFourthData.Bq 4787 = (246180963601726:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 4787 = 246180963601726 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 4787 = (12787:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_4787
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 4788) ≤ val WuPaper.ClassicalFourthData.Bq 4788
    have hp : val WuPaper.ClassicalFourthData.Bq 4788 = (246197307914443:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 4788 = 246197307914443 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 4788 = (3197:ℝ)/1000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_4788
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 4789) ≤ val WuPaper.ClassicalFourthData.Bq 4789
    have hp : val WuPaper.ClassicalFourthData.Bq 4789 = (246213645621274:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 4789 = 246213645621274 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 4789 = (12789:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_4789
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 4790) ≤ val WuPaper.ClassicalFourthData.Bq 4790
    have hp : val WuPaper.ClassicalFourthData.Bq 4790 = (246229976724690:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 4790 = 246229976724690 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 4790 = (1279:ℝ)/400 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_4790
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 4791) ≤ val WuPaper.ClassicalFourthData.Bq 4791
    have hp : val WuPaper.ClassicalFourthData.Bq 4791 = (246246301227161:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 4791 = 246246301227161 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 4791 = (12791:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_4791
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 4792) ≤ val WuPaper.ClassicalFourthData.Bq 4792
    have hp : val WuPaper.ClassicalFourthData.Bq 4792 = (246262619131154:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 4792 = 246262619131154 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 4792 = (1599:ℝ)/500 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_4792
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 4793) ≤ val WuPaper.ClassicalFourthData.Bq 4793
    have hp : val WuPaper.ClassicalFourthData.Bq 4793 = (246278930439139:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 4793 = 246278930439139 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 4793 = (12793:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_4793
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 4794) ≤ val WuPaper.ClassicalFourthData.Bq 4794
    have hp : val WuPaper.ClassicalFourthData.Bq 4794 = (246295235153581:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 4794 = 246295235153581 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 4794 = (6397:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_4794
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 4795) ≤ val WuPaper.ClassicalFourthData.Bq 4795
    have hp : val WuPaper.ClassicalFourthData.Bq 4795 = (246311533276947:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 4795 = 246311533276947 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 4795 = (2559:ℝ)/800 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_4795
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 4796) ≤ val WuPaper.ClassicalFourthData.Bq 4796
    have hp : val WuPaper.ClassicalFourthData.Bq 4796 = (246327824811699:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 4796 = 246327824811699 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 4796 = (3199:ℝ)/1000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_4796
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 4797) ≤ val WuPaper.ClassicalFourthData.Bq 4797
    have hp : val WuPaper.ClassicalFourthData.Bq 4797 = (246344109760303:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 4797 = 246344109760303 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 4797 = (12797:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_4797
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 4798) ≤ val WuPaper.ClassicalFourthData.Bq 4798
    have hp : val WuPaper.ClassicalFourthData.Bq 4798 = (246360388125219:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 4798 = 246360388125219 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 4798 = (6399:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_4798
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 4799) ≤ val WuPaper.ClassicalFourthData.Bq 4799
    have hp : val WuPaper.ClassicalFourthData.Bq 4799 = (246376659908910:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 4799 = 246376659908910 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 4799 = (12799:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_4799
end WuPaper.ClassicalFourthConditions
#print axioms WuPaper.ClassicalFourthConditions.Log_block_299

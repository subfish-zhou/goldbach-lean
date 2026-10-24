import WR2ClassicalFourthConditions
import WR2ClassicalFourthLogPoints112
noncomputable section
namespace WuPaper.ClassicalFourthConditions
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem Log_block_112 (j : Fin 16) (hj : 16*112+j.val < 10541) :
    WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 (16*112+j.val)) ≤ val WuPaper.ClassicalFourthData.Bq (16*112+j.val) := by
  fin_cases j
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 1792) ≤ val WuPaper.ClassicalFourthData.Bq 1792
    have hp : val WuPaper.ClassicalFourthData.Bq 1792 = (151218665834774:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 1792 = 151218665834774 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 1792 = (306:ℝ)/125 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_1792
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 1793) ≤ val WuPaper.ClassicalFourthData.Bq 1793
    have hp : val WuPaper.ClassicalFourthData.Bq 1793 = (151273738790809:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 1793 = 151273738790809 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 1793 = (9793:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_1793
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 1794) ≤ val WuPaper.ClassicalFourthData.Bq 1794
    have hp : val WuPaper.ClassicalFourthData.Bq 1794 = (151328788330516:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 1794 = 151328788330516 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 1794 = (4897:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_1794
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 1795) ≤ val WuPaper.ClassicalFourthData.Bq 1795
    have hp : val WuPaper.ClassicalFourthData.Bq 1795 = (151383814465268:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 1795 = 151383814465268 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 1795 = (1959:ℝ)/800 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_1795
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 1796) ≤ val WuPaper.ClassicalFourthData.Bq 1796
    have hp : val WuPaper.ClassicalFourthData.Bq 1796 = (151438817206430:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 1796 = 151438817206430 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 1796 = (2449:ℝ)/1000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_1796
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 1797) ≤ val WuPaper.ClassicalFourthData.Bq 1797
    have hp : val WuPaper.ClassicalFourthData.Bq 1797 = (151493796565359:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 1797 = 151493796565359 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 1797 = (9797:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_1797
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 1798) ≤ val WuPaper.ClassicalFourthData.Bq 1798
    have hp : val WuPaper.ClassicalFourthData.Bq 1798 = (151548752553409:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 1798 = 151548752553409 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 1798 = (4899:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_1798
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 1799) ≤ val WuPaper.ClassicalFourthData.Bq 1799
    have hp : val WuPaper.ClassicalFourthData.Bq 1799 = (151603685181922:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 1799 = 151603685181922 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 1799 = (9799:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_1799
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 1800) ≤ val WuPaper.ClassicalFourthData.Bq 1800
    have hp : val WuPaper.ClassicalFourthData.Bq 1800 = (151658594462238:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 1800 = 151658594462238 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 1800 = (49:ℝ)/20 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_1800
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 1801) ≤ val WuPaper.ClassicalFourthData.Bq 1801
    have hp : val WuPaper.ClassicalFourthData.Bq 1801 = (151713480405688:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 1801 = 151713480405688 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 1801 = (9801:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_1801
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 1802) ≤ val WuPaper.ClassicalFourthData.Bq 1802
    have hp : val WuPaper.ClassicalFourthData.Bq 1802 = (151768343023596:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 1802 = 151768343023596 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 1802 = (4901:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_1802
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 1803) ≤ val WuPaper.ClassicalFourthData.Bq 1803
    have hp : val WuPaper.ClassicalFourthData.Bq 1803 = (151823182327280:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 1803 = 151823182327280 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 1803 = (9803:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_1803
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 1804) ≤ val WuPaper.ClassicalFourthData.Bq 1804
    have hp : val WuPaper.ClassicalFourthData.Bq 1804 = (151877998328051:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 1804 = 151877998328051 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 1804 = (2451:ℝ)/1000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_1804
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 1805) ≤ val WuPaper.ClassicalFourthData.Bq 1805
    have hp : val WuPaper.ClassicalFourthData.Bq 1805 = (151932791037212:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 1805 = 151932791037212 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 1805 = (1961:ℝ)/800 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_1805
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 1806) ≤ val WuPaper.ClassicalFourthData.Bq 1806
    have hp : val WuPaper.ClassicalFourthData.Bq 1806 = (151987560466061:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 1806 = 151987560466061 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 1806 = (4903:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_1806
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 1807) ≤ val WuPaper.ClassicalFourthData.Bq 1807
    have hp : val WuPaper.ClassicalFourthData.Bq 1807 = (152042306625889:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 1807 = 152042306625889 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 1807 = (9807:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_1807
end WuPaper.ClassicalFourthConditions
#print axioms WuPaper.ClassicalFourthConditions.Log_block_112

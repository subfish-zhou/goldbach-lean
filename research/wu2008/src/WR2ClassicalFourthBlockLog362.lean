import WR2ClassicalFourthConditions
import WR2ClassicalFourthLogPoints362
noncomputable section
namespace WuPaper.ClassicalFourthConditions
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem Log_block_362 (j : Fin 16) (hj : 16*362+j.val < 10541) :
    WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 (16*362+j.val)) ≤ val WuPaper.ClassicalFourthData.Bq (16*362+j.val) := by
  fin_cases j
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 5792) ≤ val WuPaper.ClassicalFourthData.Bq 5792
    have hp : val WuPaper.ClassicalFourthData.Bq 5792 = (259649467705943:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 5792 = 259649467705943 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 5792 = (431:ℝ)/125 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_5792
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 5793) ≤ val WuPaper.ClassicalFourthData.Bq 5793
    have hp : val WuPaper.ClassicalFourthData.Bq 5793 = (259660257701378:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 5793 = 259660257701378 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 5793 = (13793:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_5793
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 5794) ≤ val WuPaper.ClassicalFourthData.Bq 5794
    have hp : val WuPaper.ClassicalFourthData.Bq 5794 = (259671043108669:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 5794 = 259671043108669 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 5794 = (6897:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_5794
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 5795) ≤ val WuPaper.ClassicalFourthData.Bq 5795
    have hp : val WuPaper.ClassicalFourthData.Bq 5795 = (259681823929431:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 5795 = 259681823929431 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 5795 = (2759:ℝ)/800 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_5795
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 5796) ≤ val WuPaper.ClassicalFourthData.Bq 5796
    have hp : val WuPaper.ClassicalFourthData.Bq 5796 = (259692600165277:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 5796 = 259692600165277 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 5796 = (3449:ℝ)/1000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_5796
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 5797) ≤ val WuPaper.ClassicalFourthData.Bq 5797
    have hp : val WuPaper.ClassicalFourthData.Bq 5797 = (259703371817823:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 5797 = 259703371817823 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 5797 = (13797:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_5797
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 5798) ≤ val WuPaper.ClassicalFourthData.Bq 5798
    have hp : val WuPaper.ClassicalFourthData.Bq 5798 = (259714138888680:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 5798 = 259714138888680 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 5798 = (6899:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_5798
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 5799) ≤ val WuPaper.ClassicalFourthData.Bq 5799
    have hp : val WuPaper.ClassicalFourthData.Bq 5799 = (259724901379463:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 5799 = 259724901379463 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 5799 = (13799:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_5799
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 5800) ≤ val WuPaper.ClassicalFourthData.Bq 5800
    have hp : val WuPaper.ClassicalFourthData.Bq 5800 = (259735659291781:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 5800 = 259735659291781 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 5800 = (69:ℝ)/20 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_5800
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 5801) ≤ val WuPaper.ClassicalFourthData.Bq 5801
    have hp : val WuPaper.ClassicalFourthData.Bq 5801 = (259746412627248:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 5801 = 259746412627248 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 5801 = (13801:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_5801
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 5802) ≤ val WuPaper.ClassicalFourthData.Bq 5802
    have hp : val WuPaper.ClassicalFourthData.Bq 5802 = (259757161387473:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 5802 = 259757161387473 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 5802 = (6901:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_5802
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 5803) ≤ val WuPaper.ClassicalFourthData.Bq 5803
    have hp : val WuPaper.ClassicalFourthData.Bq 5803 = (259767905574066:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 5803 = 259767905574066 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 5803 = (13803:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_5803
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 5804) ≤ val WuPaper.ClassicalFourthData.Bq 5804
    have hp : val WuPaper.ClassicalFourthData.Bq 5804 = (259778645188637:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 5804 = 259778645188637 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 5804 = (3451:ℝ)/1000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_5804
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 5805) ≤ val WuPaper.ClassicalFourthData.Bq 5805
    have hp : val WuPaper.ClassicalFourthData.Bq 5805 = (259789380232794:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 5805 = 259789380232794 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 5805 = (2761:ℝ)/800 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_5805
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 5806) ≤ val WuPaper.ClassicalFourthData.Bq 5806
    have hp : val WuPaper.ClassicalFourthData.Bq 5806 = (259800110708145:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 5806 = 259800110708145 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 5806 = (6903:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_5806
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 5807) ≤ val WuPaper.ClassicalFourthData.Bq 5807
    have hp : val WuPaper.ClassicalFourthData.Bq 5807 = (259810836616297:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 5807 = 259810836616297 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 5807 = (13807:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_5807
end WuPaper.ClassicalFourthConditions
#print axioms WuPaper.ClassicalFourthConditions.Log_block_362

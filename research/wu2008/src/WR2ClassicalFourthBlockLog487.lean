import WR2ClassicalFourthConditions
import WR2ClassicalFourthLogPoints487
noncomputable section
namespace WuPaper.ClassicalFourthConditions
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem Log_block_487 (j : Fin 16) (hj : 16*487+j.val < 10541) :
    WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 (16*487+j.val)) ≤ val WuPaper.ClassicalFourthData.Bq (16*487+j.val) := by
  fin_cases j
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 7792) ≤ val WuPaper.ClassicalFourthData.Bq 7792
    have hp : val WuPaper.ClassicalFourthData.Bq 7792 = (273841685493598:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 7792 = 273841685493598 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 7792 = (987:ℝ)/250 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_7792
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 7793) ≤ val WuPaper.ClassicalFourthData.Bq 7793
    have hp : val WuPaper.ClassicalFourthData.Bq 7793 = (273845823843369:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 7793 = 273845823843369 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 7793 = (15793:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_7793
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 7794) ≤ val WuPaper.ClassicalFourthData.Bq 7794
    have hp : val WuPaper.ClassicalFourthData.Bq 7794 = (273849959848060:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 7794 = 273849959848060 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 7794 = (7897:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_7794
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 7795) ≤ val WuPaper.ClassicalFourthData.Bq 7795
    have hp : val WuPaper.ClassicalFourthData.Bq 7795 = (273854093508425:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 7795 = 273854093508425 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 7795 = (3159:ℝ)/800 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_7795
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 7796) ≤ val WuPaper.ClassicalFourthData.Bq 7796
    have hp : val WuPaper.ClassicalFourthData.Bq 7796 = (273858224825219:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 7796 = 273858224825219 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 7796 = (3949:ℝ)/1000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_7796
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 7797) ≤ val WuPaper.ClassicalFourthData.Bq 7797
    have hp : val WuPaper.ClassicalFourthData.Bq 7797 = (273862353799194:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 7797 = 273862353799194 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 7797 = (15797:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_7797
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 7798) ≤ val WuPaper.ClassicalFourthData.Bq 7798
    have hp : val WuPaper.ClassicalFourthData.Bq 7798 = (273866480431105:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 7798 = 273866480431105 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 7798 = (7899:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_7798
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 7799) ≤ val WuPaper.ClassicalFourthData.Bq 7799
    have hp : val WuPaper.ClassicalFourthData.Bq 7799 = (273870604721705:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 7799 = 273870604721705 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 7799 = (15799:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_7799
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 7800) ≤ val WuPaper.ClassicalFourthData.Bq 7800
    have hp : val WuPaper.ClassicalFourthData.Bq 7800 = (273874726671745:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 7800 = 273874726671745 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 7800 = (79:ℝ)/20 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_7800
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 7801) ≤ val WuPaper.ClassicalFourthData.Bq 7801
    have hp : val WuPaper.ClassicalFourthData.Bq 7801 = (273878846281979:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 7801 = 273878846281979 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 7801 = (15801:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_7801
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 7802) ≤ val WuPaper.ClassicalFourthData.Bq 7802
    have hp : val WuPaper.ClassicalFourthData.Bq 7802 = (273882963553160:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 7802 = 273882963553160 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 7802 = (7901:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_7802
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 7803) ≤ val WuPaper.ClassicalFourthData.Bq 7803
    have hp : val WuPaper.ClassicalFourthData.Bq 7803 = (273887078486039:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 7803 = 273887078486039 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 7803 = (15803:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_7803
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 7804) ≤ val WuPaper.ClassicalFourthData.Bq 7804
    have hp : val WuPaper.ClassicalFourthData.Bq 7804 = (273891191081367:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 7804 = 273891191081367 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 7804 = (3951:ℝ)/1000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_7804
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 7805) ≤ val WuPaper.ClassicalFourthData.Bq 7805
    have hp : val WuPaper.ClassicalFourthData.Bq 7805 = (273895301339897:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 7805 = 273895301339897 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 7805 = (3161:ℝ)/800 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_7805
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 7806) ≤ val WuPaper.ClassicalFourthData.Bq 7806
    have hp : val WuPaper.ClassicalFourthData.Bq 7806 = (273899409262380:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 7806 = 273899409262380 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 7806 = (7903:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_7806
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 7807) ≤ val WuPaper.ClassicalFourthData.Bq 7807
    have hp : val WuPaper.ClassicalFourthData.Bq 7807 = (273903514849566:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 7807 = 273903514849566 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 7807 = (15807:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_7807
end WuPaper.ClassicalFourthConditions
#print axioms WuPaper.ClassicalFourthConditions.Log_block_487

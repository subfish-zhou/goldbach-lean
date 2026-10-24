import WR2ClassicalFourthConditions
import WR2ClassicalFourthLogPoints441
noncomputable section
namespace WuPaper.ClassicalFourthConditions
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem Log_block_441 (j : Fin 16) (hj : 16*441+j.val < 10541) :
    WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 (16*441+j.val)) ≤ val WuPaper.ClassicalFourthData.Bq (16*441+j.val) := by
  fin_cases j
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 7056) ≤ val WuPaper.ClassicalFourthData.Bq 7056
    have hp : val WuPaper.ClassicalFourthData.Bq 7056 = (270105979252317:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 7056 = 270105979252317 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 7056 = (941:ℝ)/250 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_7056
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 7057) ≤ val WuPaper.ClassicalFourthData.Bq 7057
    have hp : val WuPaper.ClassicalFourthData.Bq 7057 = (270112067593989:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 7057 = 270112067593989 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 7057 = (15057:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_7057
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 7058) ≤ val WuPaper.ClassicalFourthData.Bq 7058
    have hp : val WuPaper.ClassicalFourthData.Bq 7058 = (270118152954217:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 7058 = 270118152954217 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 7058 = (7529:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_7058
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 7059) ≤ val WuPaper.ClassicalFourthData.Bq 7059
    have hp : val WuPaper.ClassicalFourthData.Bq 7059 = (270124235333988:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 7059 = 270124235333988 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 7059 = (15059:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_7059
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 7060) ≤ val WuPaper.ClassicalFourthData.Bq 7060
    have hp : val WuPaper.ClassicalFourthData.Bq 7060 = (270130314734289:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 7060 = 270130314734289 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 7060 = (753:ℝ)/200 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_7060
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 7061) ≤ val WuPaper.ClassicalFourthData.Bq 7061
    have hp : val WuPaper.ClassicalFourthData.Bq 7061 = (270136391156106:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 7061 = 270136391156106 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 7061 = (15061:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_7061
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 7062) ≤ val WuPaper.ClassicalFourthData.Bq 7062
    have hp : val WuPaper.ClassicalFourthData.Bq 7062 = (270142464600424:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 7062 = 270142464600424 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 7062 = (7531:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_7062
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 7063) ≤ val WuPaper.ClassicalFourthData.Bq 7063
    have hp : val WuPaper.ClassicalFourthData.Bq 7063 = (270148535068230:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 7063 = 270148535068230 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 7063 = (15063:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_7063
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 7064) ≤ val WuPaper.ClassicalFourthData.Bq 7064
    have hp : val WuPaper.ClassicalFourthData.Bq 7064 = (270154602560507:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 7064 = 270154602560507 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 7064 = (1883:ℝ)/500 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_7064
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 7065) ≤ val WuPaper.ClassicalFourthData.Bq 7065
    have hp : val WuPaper.ClassicalFourthData.Bq 7065 = (270160667078241:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 7065 = 270160667078241 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 7065 = (3013:ℝ)/800 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_7065
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 7066) ≤ val WuPaper.ClassicalFourthData.Bq 7066
    have hp : val WuPaper.ClassicalFourthData.Bq 7066 = (270166728622417:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 7066 = 270166728622417 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 7066 = (7533:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_7066
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 7067) ≤ val WuPaper.ClassicalFourthData.Bq 7067
    have hp : val WuPaper.ClassicalFourthData.Bq 7067 = (270172787194017:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 7067 = 270172787194017 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 7067 = (15067:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_7067
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 7068) ≤ val WuPaper.ClassicalFourthData.Bq 7068
    have hp : val WuPaper.ClassicalFourthData.Bq 7068 = (270178842794026:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 7068 = 270178842794026 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 7068 = (3767:ℝ)/1000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_7068
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 7069) ≤ val WuPaper.ClassicalFourthData.Bq 7069
    have hp : val WuPaper.ClassicalFourthData.Bq 7069 = (270184895423426:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 7069 = 270184895423426 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 7069 = (15069:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_7069
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 7070) ≤ val WuPaper.ClassicalFourthData.Bq 7070
    have hp : val WuPaper.ClassicalFourthData.Bq 7070 = (270190945083202:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 7070 = 270190945083202 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 7070 = (1507:ℝ)/400 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_7070
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 7071) ≤ val WuPaper.ClassicalFourthData.Bq 7071
    have hp : val WuPaper.ClassicalFourthData.Bq 7071 = (270196991774334:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 7071 = 270196991774334 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 7071 = (15071:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_7071
end WuPaper.ClassicalFourthConditions
#print axioms WuPaper.ClassicalFourthConditions.Log_block_441

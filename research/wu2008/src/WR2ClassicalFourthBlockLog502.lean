import WR2ClassicalFourthConditions
import WR2ClassicalFourthLogPoints502
noncomputable section
namespace WuPaper.ClassicalFourthConditions
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem Log_block_502 (j : Fin 16) (hj : 16*502+j.val < 10541) :
    WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 (16*502+j.val)) ≤ val WuPaper.ClassicalFourthData.Bq (16*502+j.val) := by
  fin_cases j
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 8032) ≤ val WuPaper.ClassicalFourthData.Bq 8032
    have hp : val WuPaper.ClassicalFourthData.Bq 8032 = (274769312896787:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 8032 = 274769312896787 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 8032 = (501:ℝ)/125 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_8032
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 8033) ≤ val WuPaper.ClassicalFourthData.Bq 8033
    have hp : val WuPaper.ClassicalFourthData.Bq 8033 = (274772909458958:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 8033 = 274772909458958 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 8033 = (16033:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_8033
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 8034) ≤ val WuPaper.ClassicalFourthData.Bq 8034
    have hp : val WuPaper.ClassicalFourthData.Bq 8034 = (274776503849572:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 8034 = 274776503849572 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 8034 = (8017:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_8034
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 8035) ≤ val WuPaper.ClassicalFourthData.Bq 8035
    have hp : val WuPaper.ClassicalFourthData.Bq 8035 = (274780096069321:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 8035 = 274780096069321 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 8035 = (3207:ℝ)/800 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_8035
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 8036) ≤ val WuPaper.ClassicalFourthData.Bq 8036
    have hp : val WuPaper.ClassicalFourthData.Bq 8036 = (274783686118898:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 8036 = 274783686118898 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 8036 = (4009:ℝ)/1000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_8036
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 8037) ≤ val WuPaper.ClassicalFourthData.Bq 8037
    have hp : val WuPaper.ClassicalFourthData.Bq 8037 = (274787273998994:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 8037 = 274787273998994 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 8037 = (16037:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_8037
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 8038) ≤ val WuPaper.ClassicalFourthData.Bq 8038
    have hp : val WuPaper.ClassicalFourthData.Bq 8038 = (274790859710301:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 8038 = 274790859710301 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 8038 = (8019:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_8038
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 8039) ≤ val WuPaper.ClassicalFourthData.Bq 8039
    have hp : val WuPaper.ClassicalFourthData.Bq 8039 = (274794443253512:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 8039 = 274794443253512 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 8039 = (16039:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_8039
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 8040) ≤ val WuPaper.ClassicalFourthData.Bq 8040
    have hp : val WuPaper.ClassicalFourthData.Bq 8040 = (274798024629317:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 8040 = 274798024629317 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 8040 = (401:ℝ)/100 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_8040
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 8041) ≤ val WuPaper.ClassicalFourthData.Bq 8041
    have hp : val WuPaper.ClassicalFourthData.Bq 8041 = (274801603838407:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 8041 = 274801603838407 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 8041 = (16041:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_8041
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 8042) ≤ val WuPaper.ClassicalFourthData.Bq 8042
    have hp : val WuPaper.ClassicalFourthData.Bq 8042 = (274805180881474:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 8042 = 274805180881474 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 8042 = (8021:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_8042
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 8043) ≤ val WuPaper.ClassicalFourthData.Bq 8043
    have hp : val WuPaper.ClassicalFourthData.Bq 8043 = (274808755759208:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 8043 = 274808755759208 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 8043 = (16043:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_8043
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 8044) ≤ val WuPaper.ClassicalFourthData.Bq 8044
    have hp : val WuPaper.ClassicalFourthData.Bq 8044 = (274812328472300:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 8044 = 274812328472300 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 8044 = (4011:ℝ)/1000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_8044
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 8045) ≤ val WuPaper.ClassicalFourthData.Bq 8045
    have hp : val WuPaper.ClassicalFourthData.Bq 8045 = (274815899021439:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 8045 = 274815899021439 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 8045 = (3209:ℝ)/800 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_8045
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 8046) ≤ val WuPaper.ClassicalFourthData.Bq 8046
    have hp : val WuPaper.ClassicalFourthData.Bq 8046 = (274819467407316:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 8046 = 274819467407316 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 8046 = (8023:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_8046
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 8047) ≤ val WuPaper.ClassicalFourthData.Bq 8047
    have hp : val WuPaper.ClassicalFourthData.Bq 8047 = (274823033630620:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 8047 = 274823033630620 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 8047 = (16047:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_8047
end WuPaper.ClassicalFourthConditions
#print axioms WuPaper.ClassicalFourthConditions.Log_block_502

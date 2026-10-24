import WR2ClassicalFourthConditions
import WR2ClassicalFourthLogPoints062
noncomputable section
namespace WuPaper.ClassicalFourthConditions
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem Log_block_062 (j : Fin 16) (hj : 16*62+j.val < 10541) :
    WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 (16*62+j.val)) ≤ val WuPaper.ClassicalFourthData.Bq (16*62+j.val) := by
  fin_cases j
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 992) ≤ val WuPaper.ClassicalFourthData.Bq 992
    have hp : val WuPaper.ClassicalFourthData.Bq 992 = (98550831827063:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 992 = 98550831827063 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 992 = (281:ℝ)/125 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_992
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 993) ≤ val WuPaper.ClassicalFourthData.Bq 993
    have hp : val WuPaper.ClassicalFourthData.Bq 993 = (98628964927647:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 993 = 98628964927647 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 993 = (8993:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_993
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 994) ≤ val WuPaper.ClassicalFourthData.Bq 994
    have hp : val WuPaper.ClassicalFourthData.Bq 994 = (98707062814184:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 994 = 98707062814184 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 994 = (4497:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_994
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 995) ≤ val WuPaper.ClassicalFourthData.Bq 995
    have hp : val WuPaper.ClassicalFourthData.Bq 995 = (98785125505560:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 995 = 98785125505560 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 995 = (1799:ℝ)/800 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_995
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 996) ≤ val WuPaper.ClassicalFourthData.Bq 996
    have hp : val WuPaper.ClassicalFourthData.Bq 996 = (98863153020650:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 996 = 98863153020650 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 996 = (2249:ℝ)/1000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_996
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 997) ≤ val WuPaper.ClassicalFourthData.Bq 997
    have hp : val WuPaper.ClassicalFourthData.Bq 997 = (98941145378317:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 997 = 98941145378317 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 997 = (8997:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_997
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 998) ≤ val WuPaper.ClassicalFourthData.Bq 998
    have hp : val WuPaper.ClassicalFourthData.Bq 998 = (99019102597409:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 998 = 99019102597409 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 998 = (4499:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_998
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 999) ≤ val WuPaper.ClassicalFourthData.Bq 999
    have hp : val WuPaper.ClassicalFourthData.Bq 999 = (99097024696764:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 999 = 99097024696764 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 999 = (8999:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_999
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 1000) ≤ val WuPaper.ClassicalFourthData.Bq 1000
    have hp : val WuPaper.ClassicalFourthData.Bq 1000 = (99174911695205:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 1000 = 99174911695205 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 1000 = (9:ℝ)/4 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_1000
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 1001) ≤ val WuPaper.ClassicalFourthData.Bq 1001
    have hp : val WuPaper.ClassicalFourthData.Bq 1001 = (99252763611544:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 1001 = 99252763611544 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 1001 = (9001:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_1001
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 1002) ≤ val WuPaper.ClassicalFourthData.Bq 1002
    have hp : val WuPaper.ClassicalFourthData.Bq 1002 = (99330580464580:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 1002 = 99330580464580 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 1002 = (4501:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_1002
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 1003) ≤ val WuPaper.ClassicalFourthData.Bq 1003
    have hp : val WuPaper.ClassicalFourthData.Bq 1003 = (99408362273099:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 1003 = 99408362273099 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 1003 = (9003:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_1003
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 1004) ≤ val WuPaper.ClassicalFourthData.Bq 1004
    have hp : val WuPaper.ClassicalFourthData.Bq 1004 = (99486109055875:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 1004 = 99486109055875 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 1004 = (2251:ℝ)/1000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_1004
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 1005) ≤ val WuPaper.ClassicalFourthData.Bq 1005
    have hp : val WuPaper.ClassicalFourthData.Bq 1005 = (99563820831669:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 1005 = 99563820831669 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 1005 = (1801:ℝ)/800 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_1005
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 1006) ≤ val WuPaper.ClassicalFourthData.Bq 1006
    have hp : val WuPaper.ClassicalFourthData.Bq 1006 = (99641497619229:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 1006 = 99641497619229 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 1006 = (4503:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_1006
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 1007) ≤ val WuPaper.ClassicalFourthData.Bq 1007
    have hp : val WuPaper.ClassicalFourthData.Bq 1007 = (99719139437290:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 1007 = 99719139437290 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 1007 = (9007:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_1007
end WuPaper.ClassicalFourthConditions
#print axioms WuPaper.ClassicalFourthConditions.Log_block_062

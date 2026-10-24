import WR2ClassicalFourthConditions
import WR2ClassicalFourthLogPoints625
noncomputable section
namespace WuPaper.ClassicalFourthConditions
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem Log_block_625 (j : Fin 16) (hj : 16*625+j.val < 10541) :
    WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 (16*625+j.val)) ≤ val WuPaper.ClassicalFourthData.Bq (16*625+j.val) := by
  fin_cases j
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 10000) ≤ val WuPaper.ClassicalFourthData.Bq 10000
    have hp : val WuPaper.ClassicalFourthData.Bq 10000 = (278391770797909:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 10000 = 278391770797909 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 10000 = (9:ℝ)/2 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_10000
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 10001) ≤ val WuPaper.ClassicalFourthData.Bq 10001
    have hp : val WuPaper.ClassicalFourthData.Bq 10001 = (278392177014892:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 10001 = 278392177014892 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 10001 = (18001:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_10001
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 10002) ≤ val WuPaper.ClassicalFourthData.Bq 10002
    have hp : val WuPaper.ClassicalFourthData.Bq 10002 = (278392582053246:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 10002 = 278392582053246 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 10002 = (9001:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_10002
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 10003) ≤ val WuPaper.ClassicalFourthData.Bq 10003
    have hp : val WuPaper.ClassicalFourthData.Bq 10003 = (278392985913329:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 10003 = 278392985913329 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 10003 = (18003:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_10003
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 10004) ≤ val WuPaper.ClassicalFourthData.Bq 10004
    have hp : val WuPaper.ClassicalFourthData.Bq 10004 = (278393388595500:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 10004 = 278393388595500 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 10004 = (4501:ℝ)/1000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_10004
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 10005) ≤ val WuPaper.ClassicalFourthData.Bq 10005
    have hp : val WuPaper.ClassicalFourthData.Bq 10005 = (278393790100116:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 10005 = 278393790100116 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 10005 = (3601:ℝ)/800 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_10005
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 10006) ≤ val WuPaper.ClassicalFourthData.Bq 10006
    have hp : val WuPaper.ClassicalFourthData.Bq 10006 = (278394190427535:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 10006 = 278394190427535 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 10006 = (9003:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_10006
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 10007) ≤ val WuPaper.ClassicalFourthData.Bq 10007
    have hp : val WuPaper.ClassicalFourthData.Bq 10007 = (278394589578116:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 10007 = 278394589578116 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 10007 = (18007:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_10007
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 10008) ≤ val WuPaper.ClassicalFourthData.Bq 10008
    have hp : val WuPaper.ClassicalFourthData.Bq 10008 = (278394987552216:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 10008 = 278394987552216 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 10008 = (2251:ℝ)/500 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_10008
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 10009) ≤ val WuPaper.ClassicalFourthData.Bq 10009
    have hp : val WuPaper.ClassicalFourthData.Bq 10009 = (278395384350192:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 10009 = 278395384350192 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 10009 = (18009:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_10009
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 10010) ≤ val WuPaper.ClassicalFourthData.Bq 10010
    have hp : val WuPaper.ClassicalFourthData.Bq 10010 = (278395779972402:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 10010 = 278395779972402 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 10010 = (1801:ℝ)/400 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_10010
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 10011) ≤ val WuPaper.ClassicalFourthData.Bq 10011
    have hp : val WuPaper.ClassicalFourthData.Bq 10011 = (278396174419204:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 10011 = 278396174419204 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 10011 = (18011:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_10011
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 10012) ≤ val WuPaper.ClassicalFourthData.Bq 10012
    have hp : val WuPaper.ClassicalFourthData.Bq 10012 = (278396567690954:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 10012 = 278396567690954 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 10012 = (4503:ℝ)/1000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_10012
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 10013) ≤ val WuPaper.ClassicalFourthData.Bq 10013
    have hp : val WuPaper.ClassicalFourthData.Bq 10013 = (278396959788011:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 10013 = 278396959788011 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 10013 = (18013:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_10013
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 10014) ≤ val WuPaper.ClassicalFourthData.Bq 10014
    have hp : val WuPaper.ClassicalFourthData.Bq 10014 = (278397350710730:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 10014 = 278397350710730 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 10014 = (9007:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_10014
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 10015) ≤ val WuPaper.ClassicalFourthData.Bq 10015
    have hp : val WuPaper.ClassicalFourthData.Bq 10015 = (278397740459469:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 10015 = 278397740459469 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 10015 = (3603:ℝ)/800 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_10015
end WuPaper.ClassicalFourthConditions
#print axioms WuPaper.ClassicalFourthConditions.Log_block_625

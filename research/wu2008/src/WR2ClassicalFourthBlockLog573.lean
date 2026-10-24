import WR2ClassicalFourthConditions
import WR2ClassicalFourthLogPoints573
noncomputable section
namespace WuPaper.ClassicalFourthConditions
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem Log_block_573 (j : Fin 16) (hj : 16*573+j.val < 10541) :
    WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 (16*573+j.val)) ≤ val WuPaper.ClassicalFourthData.Bq (16*573+j.val) := by
  fin_cases j
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 9168) ≤ val WuPaper.ClassicalFourthData.Bq 9168
    have hp : val WuPaper.ClassicalFourthData.Bq 9168 = (277608406998804:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 9168 = 277608406998804 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 9168 = (1073:ℝ)/250 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_9168
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 9169) ≤ val WuPaper.ClassicalFourthData.Bq 9169
    have hp : val WuPaper.ClassicalFourthData.Bq 9169 = (277609929904428:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 9169 = 277609929904428 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 9169 = (17169:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_9169
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 9170) ≤ val WuPaper.ClassicalFourthData.Bq 9170
    have hp : val WuPaper.ClassicalFourthData.Bq 9170 = (277611451289325:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 9170 = 277611451289325 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 9170 = (1717:ℝ)/400 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_9170
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 9171) ≤ val WuPaper.ClassicalFourthData.Bq 9171
    have hp : val WuPaper.ClassicalFourthData.Bq 9171 = (277612971153967:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 9171 = 277612971153967 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 9171 = (17171:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_9171
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 9172) ≤ val WuPaper.ClassicalFourthData.Bq 9172
    have hp : val WuPaper.ClassicalFourthData.Bq 9172 = (277614489498822:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 9172 = 277614489498822 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 9172 = (4293:ℝ)/1000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_9172
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 9173) ≤ val WuPaper.ClassicalFourthData.Bq 9173
    have hp : val WuPaper.ClassicalFourthData.Bq 9173 = (277616006324359:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 9173 = 277616006324359 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 9173 = (17173:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_9173
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 9174) ≤ val WuPaper.ClassicalFourthData.Bq 9174
    have hp : val WuPaper.ClassicalFourthData.Bq 9174 = (277617521631049:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 9174 = 277617521631049 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 9174 = (8587:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_9174
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 9175) ≤ val WuPaper.ClassicalFourthData.Bq 9175
    have hp : val WuPaper.ClassicalFourthData.Bq 9175 = (277619035419360:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 9175 = 277619035419360 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 9175 = (687:ℝ)/160 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_9175
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 9176) ≤ val WuPaper.ClassicalFourthData.Bq 9176
    have hp : val WuPaper.ClassicalFourthData.Bq 9176 = (277620547689761:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 9176 = 277620547689761 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 9176 = (2147:ℝ)/500 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_9176
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 9177) ≤ val WuPaper.ClassicalFourthData.Bq 9177
    have hp : val WuPaper.ClassicalFourthData.Bq 9177 = (277622058442720:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 9177 = 277622058442720 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 9177 = (17177:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_9177
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 9178) ≤ val WuPaper.ClassicalFourthData.Bq 9178
    have hp : val WuPaper.ClassicalFourthData.Bq 9178 = (277623567678707:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 9178 = 277623567678707 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 9178 = (8589:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_9178
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 9179) ≤ val WuPaper.ClassicalFourthData.Bq 9179
    have hp : val WuPaper.ClassicalFourthData.Bq 9179 = (277625075398189:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 9179 = 277625075398189 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 9179 = (17179:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_9179
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 9180) ≤ val WuPaper.ClassicalFourthData.Bq 9180
    have hp : val WuPaper.ClassicalFourthData.Bq 9180 = (277626581601636:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 9180 = 277626581601636 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 9180 = (859:ℝ)/200 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_9180
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 9181) ≤ val WuPaper.ClassicalFourthData.Bq 9181
    have hp : val WuPaper.ClassicalFourthData.Bq 9181 = (277628086289514:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 9181 = 277628086289514 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 9181 = (17181:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_9181
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 9182) ≤ val WuPaper.ClassicalFourthData.Bq 9182
    have hp : val WuPaper.ClassicalFourthData.Bq 9182 = (277629589462293:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 9182 = 277629589462293 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 9182 = (8591:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_9182
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 9183) ≤ val WuPaper.ClassicalFourthData.Bq 9183
    have hp : val WuPaper.ClassicalFourthData.Bq 9183 = (277631091120439:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 9183 = 277631091120439 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 9183 = (17183:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_9183
end WuPaper.ClassicalFourthConditions
#print axioms WuPaper.ClassicalFourthConditions.Log_block_573

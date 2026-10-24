import WR2ClassicalFourthConditions
import WR2ClassicalFourthLogPoints504
noncomputable section
namespace WuPaper.ClassicalFourthConditions
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem Log_block_504 (j : Fin 16) (hj : 16*504+j.val < 10541) :
    WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 (16*504+j.val)) ≤ val WuPaper.ClassicalFourthData.Bq (16*504+j.val) := by
  fin_cases j
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 8064) ≤ val WuPaper.ClassicalFourthData.Bq 8064
    have hp : val WuPaper.ClassicalFourthData.Bq 8064 = (274883329220276:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 8064 = 274883329220276 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 8064 = (502:ℝ)/125 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_8064
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 8065) ≤ val WuPaper.ClassicalFourthData.Bq 8065
    have hp : val WuPaper.ClassicalFourthData.Bq 8065 = (274886856634928:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 8065 = 274886856634928 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 8065 = (3213:ℝ)/800 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_8065
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 8066) ≤ val WuPaper.ClassicalFourthData.Bq 8066
    have hp : val WuPaper.ClassicalFourthData.Bq 8066 = (274890381900065:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 8066 = 274890381900065 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 8066 = (8033:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_8066
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 8067) ≤ val WuPaper.ClassicalFourthData.Bq 8067
    have hp : val WuPaper.ClassicalFourthData.Bq 8067 = (274893905016371:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 8067 = 274893905016371 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 8067 = (16067:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_8067
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 8068) ≤ val WuPaper.ClassicalFourthData.Bq 8068
    have hp : val WuPaper.ClassicalFourthData.Bq 8068 = (274897425984532:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 8068 = 274897425984532 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 8068 = (4017:ℝ)/1000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_8068
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 8069) ≤ val WuPaper.ClassicalFourthData.Bq 8069
    have hp : val WuPaper.ClassicalFourthData.Bq 8069 = (274900944805232:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 8069 = 274900944805232 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 8069 = (16069:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_8069
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 8070) ≤ val WuPaper.ClassicalFourthData.Bq 8070
    have hp : val WuPaper.ClassicalFourthData.Bq 8070 = (274904461479155:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 8070 = 274904461479155 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 8070 = (1607:ℝ)/400 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_8070
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 8071) ≤ val WuPaper.ClassicalFourthData.Bq 8071
    have hp : val WuPaper.ClassicalFourthData.Bq 8071 = (274907976006984:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 8071 = 274907976006984 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 8071 = (16071:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_8071
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 8072) ≤ val WuPaper.ClassicalFourthData.Bq 8072
    have hp : val WuPaper.ClassicalFourthData.Bq 8072 = (274911488389404:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 8072 = 274911488389404 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 8072 = (2009:ℝ)/500 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_8072
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 8073) ≤ val WuPaper.ClassicalFourthData.Bq 8073
    have hp : val WuPaper.ClassicalFourthData.Bq 8073 = (274914998627097:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 8073 = 274914998627097 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 8073 = (16073:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_8073
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 8074) ≤ val WuPaper.ClassicalFourthData.Bq 8074
    have hp : val WuPaper.ClassicalFourthData.Bq 8074 = (274918506720747:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 8074 = 274918506720747 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 8074 = (8037:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_8074
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 8075) ≤ val WuPaper.ClassicalFourthData.Bq 8075
    have hp : val WuPaper.ClassicalFourthData.Bq 8075 = (274922012671037:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 8075 = 274922012671037 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 8075 = (643:ℝ)/160 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_8075
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 8076) ≤ val WuPaper.ClassicalFourthData.Bq 8076
    have hp : val WuPaper.ClassicalFourthData.Bq 8076 = (274925516478650:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 8076 = 274925516478650 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 8076 = (4019:ℝ)/1000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_8076
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 8077) ≤ val WuPaper.ClassicalFourthData.Bq 8077
    have hp : val WuPaper.ClassicalFourthData.Bq 8077 = (274929018144267:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 8077 = 274929018144267 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 8077 = (16077:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_8077
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 8078) ≤ val WuPaper.ClassicalFourthData.Bq 8078
    have hp : val WuPaper.ClassicalFourthData.Bq 8078 = (274932517668571:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 8078 = 274932517668571 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 8078 = (8039:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_8078
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 8079) ≤ val WuPaper.ClassicalFourthData.Bq 8079
    have hp : val WuPaper.ClassicalFourthData.Bq 8079 = (274936015052245:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 8079 = 274936015052245 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 8079 = (16079:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_8079
end WuPaper.ClassicalFourthConditions
#print axioms WuPaper.ClassicalFourthConditions.Log_block_504

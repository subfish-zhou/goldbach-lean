import WR2ClassicalFourthConditions
import WR2ClassicalFourthLogPoints382
noncomputable section
namespace WuPaper.ClassicalFourthConditions
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem Log_block_382 (j : Fin 16) (hj : 16*382+j.val < 10541) :
    WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 (16*382+j.val)) ≤ val WuPaper.ClassicalFourthData.Bq (16*382+j.val) := by
  fin_cases j
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 6112) ≤ val WuPaper.ClassicalFourthData.Bq 6112
    have hp : val WuPaper.ClassicalFourthData.Bq 6112 = (262876552234874:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 6112 = 262876552234874 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 6112 = (441:ℝ)/125 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_6112
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 6113) ≤ val WuPaper.ClassicalFourthData.Bq 6113
    have hp : val WuPaper.ClassicalFourthData.Bq 6113 = (262885953036255:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 6113 = 262885953036255 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 6113 = (14113:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_6113
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 6114) ≤ val WuPaper.ClassicalFourthData.Bq 6114
    have hp : val WuPaper.ClassicalFourthData.Bq 6114 = (262895349734427:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 6114 = 262895349734427 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 6114 = (7057:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_6114
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 6115) ≤ val WuPaper.ClassicalFourthData.Bq 6115
    have hp : val WuPaper.ClassicalFourthData.Bq 6115 = (262904742330809:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 6115 = 262904742330809 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 6115 = (2823:ℝ)/800 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_6115
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 6116) ≤ val WuPaper.ClassicalFourthData.Bq 6116
    have hp : val WuPaper.ClassicalFourthData.Bq 6116 = (262914130826821:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 6116 = 262914130826821 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 6116 = (3529:ℝ)/1000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_6116
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 6117) ≤ val WuPaper.ClassicalFourthData.Bq 6117
    have hp : val WuPaper.ClassicalFourthData.Bq 6117 = (262923515223883:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 6117 = 262923515223883 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 6117 = (14117:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_6117
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 6118) ≤ val WuPaper.ClassicalFourthData.Bq 6118
    have hp : val WuPaper.ClassicalFourthData.Bq 6118 = (262932895523411:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 6118 = 262932895523411 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 6118 = (7059:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_6118
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 6119) ≤ val WuPaper.ClassicalFourthData.Bq 6119
    have hp : val WuPaper.ClassicalFourthData.Bq 6119 = (262942271726824:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 6119 = 262942271726824 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 6119 = (14119:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_6119
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 6120) ≤ val WuPaper.ClassicalFourthData.Bq 6120
    have hp : val WuPaper.ClassicalFourthData.Bq 6120 = (262951643835539:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 6120 = 262951643835539 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 6120 = (353:ℝ)/100 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_6120
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 6121) ≤ val WuPaper.ClassicalFourthData.Bq 6121
    have hp : val WuPaper.ClassicalFourthData.Bq 6121 = (262961011850973:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 6121 = 262961011850973 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 6121 = (14121:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_6121
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 6122) ≤ val WuPaper.ClassicalFourthData.Bq 6122
    have hp : val WuPaper.ClassicalFourthData.Bq 6122 = (262970375774542:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 6122 = 262970375774542 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 6122 = (7061:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_6122
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 6123) ≤ val WuPaper.ClassicalFourthData.Bq 6123
    have hp : val WuPaper.ClassicalFourthData.Bq 6123 = (262979735607661:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 6123 = 262979735607661 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 6123 = (14123:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_6123
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 6124) ≤ val WuPaper.ClassicalFourthData.Bq 6124
    have hp : val WuPaper.ClassicalFourthData.Bq 6124 = (262989091351745:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 6124 = 262989091351745 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 6124 = (3531:ℝ)/1000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_6124
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 6125) ≤ val WuPaper.ClassicalFourthData.Bq 6125
    have hp : val WuPaper.ClassicalFourthData.Bq 6125 = (262998443008209:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 6125 = 262998443008209 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 6125 = (113:ℝ)/32 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_6125
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 6126) ≤ val WuPaper.ClassicalFourthData.Bq 6126
    have hp : val WuPaper.ClassicalFourthData.Bq 6126 = (263007790578466:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 6126 = 263007790578466 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 6126 = (7063:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_6126
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 6127) ≤ val WuPaper.ClassicalFourthData.Bq 6127
    have hp : val WuPaper.ClassicalFourthData.Bq 6127 = (263017134063929:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 6127 = 263017134063929 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 6127 = (14127:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_6127
end WuPaper.ClassicalFourthConditions
#print axioms WuPaper.ClassicalFourthConditions.Log_block_382

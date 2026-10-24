import WR2ClassicalFourthConditions
import WR2ClassicalFourthLogPoints320
noncomputable section
namespace WuPaper.ClassicalFourthConditions
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem Log_block_320 (j : Fin 16) (hj : 16*320+j.val < 10541) :
    WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 (16*320+j.val)) ≤ val WuPaper.ClassicalFourthData.Bq (16*320+j.val) := by
  fin_cases j
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 5120) ≤ val WuPaper.ClassicalFourthData.Bq 5120
    have hp : val WuPaper.ClassicalFourthData.Bq 5120 = (251273000904376:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 5120 = 251273000904376 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 5120 = (82:ℝ)/25 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_5120
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 5121) ≤ val WuPaper.ClassicalFourthData.Bq 5121
    have hp : val WuPaper.ClassicalFourthData.Bq 5121 = (251287275688784:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 5121 = 251287275688784 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 5121 = (13121:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_5121
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 5122) ≤ val WuPaper.ClassicalFourthData.Bq 5122
    have hp : val WuPaper.ClassicalFourthData.Bq 5122 = (251301544633324:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 5122 = 251301544633324 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 5122 = (6561:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_5122
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 5123) ≤ val WuPaper.ClassicalFourthData.Bq 5123
    have hp : val WuPaper.ClassicalFourthData.Bq 5123 = (251315807740135:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 5123 = 251315807740135 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 5123 = (13123:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_5123
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 5124) ≤ val WuPaper.ClassicalFourthData.Bq 5124
    have hp : val WuPaper.ClassicalFourthData.Bq 5124 = (251330065011354:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 5124 = 251330065011354 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 5124 = (3281:ℝ)/1000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_5124
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 5125) ≤ val WuPaper.ClassicalFourthData.Bq 5125
    have hp : val WuPaper.ClassicalFourthData.Bq 5125 = (251344316449118:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 5125 = 251344316449118 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 5125 = (105:ℝ)/32 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_5125
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 5126) ≤ val WuPaper.ClassicalFourthData.Bq 5126
    have hp : val WuPaper.ClassicalFourthData.Bq 5126 = (251358562055561:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 5126 = 251358562055561 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 5126 = (6563:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_5126
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 5127) ≤ val WuPaper.ClassicalFourthData.Bq 5127
    have hp : val WuPaper.ClassicalFourthData.Bq 5127 = (251372801832819:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 5127 = 251372801832819 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 5127 = (13127:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_5127
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 5128) ≤ val WuPaper.ClassicalFourthData.Bq 5128
    have hp : val WuPaper.ClassicalFourthData.Bq 5128 = (251387035783024:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 5128 = 251387035783024 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 5128 = (1641:ℝ)/500 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_5128
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 5129) ≤ val WuPaper.ClassicalFourthData.Bq 5129
    have hp : val WuPaper.ClassicalFourthData.Bq 5129 = (251401263908312:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 5129 = 251401263908312 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 5129 = (13129:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_5129
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 5130) ≤ val WuPaper.ClassicalFourthData.Bq 5130
    have hp : val WuPaper.ClassicalFourthData.Bq 5130 = (251415486210812:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 5130 = 251415486210812 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 5130 = (1313:ℝ)/400 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_5130
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 5131) ≤ val WuPaper.ClassicalFourthData.Bq 5131
    have hp : val WuPaper.ClassicalFourthData.Bq 5131 = (251429702692656:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 5131 = 251429702692656 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 5131 = (13131:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_5131
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 5132) ≤ val WuPaper.ClassicalFourthData.Bq 5132
    have hp : val WuPaper.ClassicalFourthData.Bq 5132 = (251443913355973:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 5132 = 251443913355973 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 5132 = (3283:ℝ)/1000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_5132
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 5133) ≤ val WuPaper.ClassicalFourthData.Bq 5133
    have hp : val WuPaper.ClassicalFourthData.Bq 5133 = (251458118202895:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 5133 = 251458118202895 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 5133 = (13133:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_5133
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 5134) ≤ val WuPaper.ClassicalFourthData.Bq 5134
    have hp : val WuPaper.ClassicalFourthData.Bq 5134 = (251472317235547:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 5134 = 251472317235547 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 5134 = (6567:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_5134
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 5135) ≤ val WuPaper.ClassicalFourthData.Bq 5135
    have hp : val WuPaper.ClassicalFourthData.Bq 5135 = (251486510456058:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 5135 = 251486510456058 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 5135 = (2627:ℝ)/800 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_5135
end WuPaper.ClassicalFourthConditions
#print axioms WuPaper.ClassicalFourthConditions.Log_block_320

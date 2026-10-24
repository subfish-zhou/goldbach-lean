import WR2ClassicalFourthConditions
import WR2ClassicalFourthLogPoints507
noncomputable section
namespace WuPaper.ClassicalFourthConditions
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem Log_block_507 (j : Fin 16) (hj : 16*507+j.val < 10541) :
    WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 (16*507+j.val)) ≤ val WuPaper.ClassicalFourthData.Bq (16*507+j.val) := by
  fin_cases j
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 8112) ≤ val WuPaper.ClassicalFourthData.Bq 8112
    have hp : val WuPaper.ClassicalFourthData.Bq 8112 = (275050232268725:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 8112 = 275050232268725 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 8112 = (1007:ℝ)/250 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_8112
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 8113) ≤ val WuPaper.ClassicalFourthData.Bq 8113
    have hp : val WuPaper.ClassicalFourthData.Bq 8113 = (275053657274996:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 8113 = 275053657274996 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 8113 = (16113:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_8113
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 8114) ≤ val WuPaper.ClassicalFourthData.Bq 8114
    have hp : val WuPaper.ClassicalFourthData.Bq 8114 = (275057080164354:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 8114 = 275057080164354 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 8114 = (8057:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_8114
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 8115) ≤ val WuPaper.ClassicalFourthData.Bq 8115
    have hp : val WuPaper.ClassicalFourthData.Bq 8115 = (275060500937472:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 8115 = 275060500937472 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 8115 = (3223:ℝ)/800 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_8115
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 8116) ≤ val WuPaper.ClassicalFourthData.Bq 8116
    have hp : val WuPaper.ClassicalFourthData.Bq 8116 = (275063919595024:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 8116 = 275063919595024 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 8116 = (4029:ℝ)/1000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_8116
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 8117) ≤ val WuPaper.ClassicalFourthData.Bq 8117
    have hp : val WuPaper.ClassicalFourthData.Bq 8117 = (275067336137681:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 8117 = 275067336137681 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 8117 = (16117:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_8117
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 8118) ≤ val WuPaper.ClassicalFourthData.Bq 8118
    have hp : val WuPaper.ClassicalFourthData.Bq 8118 = (275070750566117:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 8118 = 275070750566117 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 8118 = (8059:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_8118
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 8119) ≤ val WuPaper.ClassicalFourthData.Bq 8119
    have hp : val WuPaper.ClassicalFourthData.Bq 8119 = (275074162881005:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 8119 = 275074162881005 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 8119 = (16119:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_8119
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 8120) ≤ val WuPaper.ClassicalFourthData.Bq 8120
    have hp : val WuPaper.ClassicalFourthData.Bq 8120 = (275077573083016:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 8120 = 275077573083016 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 8120 = (403:ℝ)/100 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_8120
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 8121) ≤ val WuPaper.ClassicalFourthData.Bq 8121
    have hp : val WuPaper.ClassicalFourthData.Bq 8121 = (275080981172822:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 8121 = 275080981172822 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 8121 = (16121:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_8121
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 8122) ≤ val WuPaper.ClassicalFourthData.Bq 8122
    have hp : val WuPaper.ClassicalFourthData.Bq 8122 = (275084387151096:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 8122 = 275084387151096 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 8122 = (8061:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_8122
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 8123) ≤ val WuPaper.ClassicalFourthData.Bq 8123
    have hp : val WuPaper.ClassicalFourthData.Bq 8123 = (275087791018508:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 8123 = 275087791018508 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 8123 = (16123:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_8123
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 8124) ≤ val WuPaper.ClassicalFourthData.Bq 8124
    have hp : val WuPaper.ClassicalFourthData.Bq 8124 = (275091192775731:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 8124 = 275091192775731 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 8124 = (4031:ℝ)/1000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_8124
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 8125) ≤ val WuPaper.ClassicalFourthData.Bq 8125
    have hp : val WuPaper.ClassicalFourthData.Bq 8125 = (275094592423434:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 8125 = 275094592423434 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 8125 = (129:ℝ)/32 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_8125
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 8126) ≤ val WuPaper.ClassicalFourthData.Bq 8126
    have hp : val WuPaper.ClassicalFourthData.Bq 8126 = (275097989962288:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 8126 = 275097989962288 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 8126 = (8063:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_8126
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 8127) ≤ val WuPaper.ClassicalFourthData.Bq 8127
    have hp : val WuPaper.ClassicalFourthData.Bq 8127 = (275101385392965:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 8127 = 275101385392965 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 8127 = (16127:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_8127
end WuPaper.ClassicalFourthConditions
#print axioms WuPaper.ClassicalFourthConditions.Log_block_507

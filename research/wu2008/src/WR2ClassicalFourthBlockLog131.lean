import WR2ClassicalFourthConditions
import WR2ClassicalFourthLogPoints131
noncomputable section
namespace WuPaper.ClassicalFourthConditions
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem Log_block_131 (j : Fin 16) (hj : 16*131+j.val < 10541) :
    WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 (16*131+j.val)) ≤ val WuPaper.ClassicalFourthData.Bq (16*131+j.val) := by
  fin_cases j
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 2096) ≤ val WuPaper.ClassicalFourthData.Bq 2096
    have hp : val WuPaper.ClassicalFourthData.Bq 2096 = (166932827759293:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 2096 = 166932827759293 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 2096 = (631:ℝ)/250 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_2096
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 2097) ≤ val WuPaper.ClassicalFourthData.Bq 2097
    have hp : val WuPaper.ClassicalFourthData.Bq 2097 = (166981275945643:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 2097 = 166981275945643 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 2097 = (10097:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_2097
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 2098) ≤ val WuPaper.ClassicalFourthData.Bq 2098
    have hp : val WuPaper.ClassicalFourthData.Bq 2098 = (167029703880441:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 2098 = 167029703880441 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 2098 = (5049:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_2098
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 2099) ≤ val WuPaper.ClassicalFourthData.Bq 2099
    have hp : val WuPaper.ClassicalFourthData.Bq 2099 = (167078111573197:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 2099 = 167078111573197 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 2099 = (10099:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_2099
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 2100) ≤ val WuPaper.ClassicalFourthData.Bq 2100
    have hp : val WuPaper.ClassicalFourthData.Bq 2100 = (167126499033416:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 2100 = 167126499033416 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 2100 = (101:ℝ)/40 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_2100
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 2101) ≤ val WuPaper.ClassicalFourthData.Bq 2101
    have hp : val WuPaper.ClassicalFourthData.Bq 2101 = (167174866270597:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 2101 = 167174866270597 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 2101 = (10101:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_2101
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 2102) ≤ val WuPaper.ClassicalFourthData.Bq 2102
    have hp : val WuPaper.ClassicalFourthData.Bq 2102 = (167223213294234:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 2102 = 167223213294234 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 2102 = (5051:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_2102
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 2103) ≤ val WuPaper.ClassicalFourthData.Bq 2103
    have hp : val WuPaper.ClassicalFourthData.Bq 2103 = (167271540113815:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 2103 = 167271540113815 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 2103 = (10103:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_2103
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 2104) ≤ val WuPaper.ClassicalFourthData.Bq 2104
    have hp : val WuPaper.ClassicalFourthData.Bq 2104 = (167319846738823:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 2104 = 167319846738823 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 2104 = (1263:ℝ)/500 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_2104
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 2105) ≤ val WuPaper.ClassicalFourthData.Bq 2105
    have hp : val WuPaper.ClassicalFourthData.Bq 2105 = (167368133178735:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 2105 = 167368133178735 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 2105 = (2021:ℝ)/800 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_2105
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 2106) ≤ val WuPaper.ClassicalFourthData.Bq 2106
    have hp : val WuPaper.ClassicalFourthData.Bq 2106 = (167416399443023:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 2106 = 167416399443023 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 2106 = (5053:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_2106
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 2107) ≤ val WuPaper.ClassicalFourthData.Bq 2107
    have hp : val WuPaper.ClassicalFourthData.Bq 2107 = (167464645541153:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 2107 = 167464645541153 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 2107 = (10107:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_2107
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 2108) ≤ val WuPaper.ClassicalFourthData.Bq 2108
    have hp : val WuPaper.ClassicalFourthData.Bq 2108 = (167512871482587:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 2108 = 167512871482587 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 2108 = (2527:ℝ)/1000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_2108
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 2109) ≤ val WuPaper.ClassicalFourthData.Bq 2109
    have hp : val WuPaper.ClassicalFourthData.Bq 2109 = (167561077276779:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 2109 = 167561077276779 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 2109 = (10109:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_2109
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 2110) ≤ val WuPaper.ClassicalFourthData.Bq 2110
    have hp : val WuPaper.ClassicalFourthData.Bq 2110 = (167609262933181:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 2110 = 167609262933181 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 2110 = (1011:ℝ)/400 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_2110
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 2111) ≤ val WuPaper.ClassicalFourthData.Bq 2111
    have hp : val WuPaper.ClassicalFourthData.Bq 2111 = (167657428461236:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 2111 = 167657428461236 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 2111 = (10111:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_2111
end WuPaper.ClassicalFourthConditions
#print axioms WuPaper.ClassicalFourthConditions.Log_block_131

import WR2ClassicalFourthConditions
import WR2ClassicalFourthLogPoints569
noncomputable section
namespace WuPaper.ClassicalFourthConditions
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem Log_block_569 (j : Fin 16) (hj : 16*569+j.val < 10541) :
    WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 (16*569+j.val)) ≤ val WuPaper.ClassicalFourthData.Bq (16*569+j.val) := by
  fin_cases j
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 9104) ≤ val WuPaper.ClassicalFourthData.Bq 9104
    have hp : val WuPaper.ClassicalFourthData.Bq 9104 = (277507756317189:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 9104 = 277507756317189 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 9104 = (1069:ℝ)/250 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_9104
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 9105) ≤ val WuPaper.ClassicalFourthData.Bq 9105
    have hp : val WuPaper.ClassicalFourthData.Bq 9105 = (277509377533352:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 9105 = 277509377533352 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 9105 = (3421:ℝ)/800 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_9105
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 9106) ≤ val WuPaper.ClassicalFourthData.Bq 9106
    have hp : val WuPaper.ClassicalFourthData.Bq 9106 = (277510997198403:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 9106 = 277510997198403 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 9106 = (8553:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_9106
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 9107) ≤ val WuPaper.ClassicalFourthData.Bq 9107
    have hp : val WuPaper.ClassicalFourthData.Bq 9107 = (277512615312822:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 9107 = 277512615312822 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 9107 = (17107:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_9107
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 9108) ≤ val WuPaper.ClassicalFourthData.Bq 9108
    have hp : val WuPaper.ClassicalFourthData.Bq 9108 = (277514231877089:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 9108 = 277514231877089 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 9108 = (4277:ℝ)/1000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_9108
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 9109) ≤ val WuPaper.ClassicalFourthData.Bq 9109
    have hp : val WuPaper.ClassicalFourthData.Bq 9109 = (277515846891683:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 9109 = 277515846891683 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 9109 = (17109:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_9109
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 9110) ≤ val WuPaper.ClassicalFourthData.Bq 9110
    have hp : val WuPaper.ClassicalFourthData.Bq 9110 = (277517460357084:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 9110 = 277517460357084 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 9110 = (1711:ℝ)/400 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_9110
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 9111) ≤ val WuPaper.ClassicalFourthData.Bq 9111
    have hp : val WuPaper.ClassicalFourthData.Bq 9111 = (277519072273770:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 9111 = 277519072273770 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 9111 = (17111:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_9111
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 9112) ≤ val WuPaper.ClassicalFourthData.Bq 9112
    have hp : val WuPaper.ClassicalFourthData.Bq 9112 = (277520682642221:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 9112 = 277520682642221 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 9112 = (2139:ℝ)/500 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_9112
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 9113) ≤ val WuPaper.ClassicalFourthData.Bq 9113
    have hp : val WuPaper.ClassicalFourthData.Bq 9113 = (277522291462916:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 9113 = 277522291462916 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 9113 = (17113:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_9113
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 9114) ≤ val WuPaper.ClassicalFourthData.Bq 9114
    have hp : val WuPaper.ClassicalFourthData.Bq 9114 = (277523898736333:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 9114 = 277523898736333 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 9114 = (8557:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_9114
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 9115) ≤ val WuPaper.ClassicalFourthData.Bq 9115
    have hp : val WuPaper.ClassicalFourthData.Bq 9115 = (277525504462950:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 9115 = 277525504462950 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 9115 = (3423:ℝ)/800 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_9115
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 9116) ≤ val WuPaper.ClassicalFourthData.Bq 9116
    have hp : val WuPaper.ClassicalFourthData.Bq 9116 = (277527108643246:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 9116 = 277527108643246 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 9116 = (4279:ℝ)/1000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_9116
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 9117) ≤ val WuPaper.ClassicalFourthData.Bq 9117
    have hp : val WuPaper.ClassicalFourthData.Bq 9117 = (277528711277700:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 9117 = 277528711277700 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 9117 = (17117:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_9117
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 9118) ≤ val WuPaper.ClassicalFourthData.Bq 9118
    have hp : val WuPaper.ClassicalFourthData.Bq 9118 = (277530312366788:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 9118 = 277530312366788 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 9118 = (8559:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_9118
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 9119) ≤ val WuPaper.ClassicalFourthData.Bq 9119
    have hp : val WuPaper.ClassicalFourthData.Bq 9119 = (277531911910990:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 9119 = 277531911910990 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 9119 = (17119:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_9119
end WuPaper.ClassicalFourthConditions
#print axioms WuPaper.ClassicalFourthConditions.Log_block_569

import WR2ClassicalFourthConditions
import WR2ClassicalFourthLogPoints007
noncomputable section
namespace WuPaper.ClassicalFourthConditions
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem Log_block_007 (j : Fin 16) (hj : 16*7+j.val < 10541) :
    WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 (16*7+j.val)) ≤ val WuPaper.ClassicalFourthData.Bq (16*7+j.val) := by
  fin_cases j
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 112) ≤ val WuPaper.ClassicalFourthData.Bq 112
    have hp : val WuPaper.ClassicalFourthData.Bq 112 = (13616946268725:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 112 = 13616946268725 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 112 = (507:ℝ)/250 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_112
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 113) ≤ val WuPaper.ClassicalFourthData.Bq 113
    have hp : val WuPaper.ClassicalFourthData.Bq 113 = (13735154999826:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 113 = 13735154999826 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 113 = (8113:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_113
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 114) ≤ val WuPaper.ClassicalFourthData.Bq 114
    have hp : val WuPaper.ClassicalFourthData.Bq 114 = (13853305452736:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 114 = 13853305452736 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 114 = (4057:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_114
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 115) ≤ val WuPaper.ClassicalFourthData.Bq 115
    have hp : val WuPaper.ClassicalFourthData.Bq 115 = (13971397663164:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 115 = 13971397663164 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 115 = (1623:ℝ)/800 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_115
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 116) ≤ val WuPaper.ClassicalFourthData.Bq 116
    have hp : val WuPaper.ClassicalFourthData.Bq 116 = (14089431666788:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 116 = 14089431666788 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 116 = (2029:ℝ)/1000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_116
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 117) ≤ val WuPaper.ClassicalFourthData.Bq 117
    have hp : val WuPaper.ClassicalFourthData.Bq 117 = (14207407499262:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 117 = 14207407499262 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 117 = (8117:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_117
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 118) ≤ val WuPaper.ClassicalFourthData.Bq 118
    have hp : val WuPaper.ClassicalFourthData.Bq 118 = (14325325196210:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 118 = 14325325196210 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 118 = (4059:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_118
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 119) ≤ val WuPaper.ClassicalFourthData.Bq 119
    have hp : val WuPaper.ClassicalFourthData.Bq 119 = (14443184793228:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 119 = 14443184793228 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 119 = (8119:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_119
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 120) ≤ val WuPaper.ClassicalFourthData.Bq 120
    have hp : val WuPaper.ClassicalFourthData.Bq 120 = (14560986325884:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 120 = 14560986325884 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 120 = (203:ℝ)/100 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_120
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 121) ≤ val WuPaper.ClassicalFourthData.Bq 121
    have hp : val WuPaper.ClassicalFourthData.Bq 121 = (14678729829721:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 121 = 14678729829721 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 121 = (8121:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_121
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 122) ≤ val WuPaper.ClassicalFourthData.Bq 122
    have hp : val WuPaper.ClassicalFourthData.Bq 122 = (14796415340250:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 122 = 14796415340250 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 122 = (4061:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_122
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 123) ≤ val WuPaper.ClassicalFourthData.Bq 123
    have hp : val WuPaper.ClassicalFourthData.Bq 123 = (14914042892957:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 123 = 14914042892957 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 123 = (8123:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_123
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 124) ≤ val WuPaper.ClassicalFourthData.Bq 124
    have hp : val WuPaper.ClassicalFourthData.Bq 124 = (15031612523301:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 124 = 15031612523301 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 124 = (2031:ℝ)/1000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_124
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 125) ≤ val WuPaper.ClassicalFourthData.Bq 125
    have hp : val WuPaper.ClassicalFourthData.Bq 125 = (15149124266710:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 125 = 15149124266710 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 125 = (65:ℝ)/32 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_125
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 126) ≤ val WuPaper.ClassicalFourthData.Bq 126
    have hp : val WuPaper.ClassicalFourthData.Bq 126 = (15266578158587:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 126 = 15266578158587 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 126 = (4063:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_126
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 127) ≤ val WuPaper.ClassicalFourthData.Bq 127
    have hp : val WuPaper.ClassicalFourthData.Bq 127 = (15383974234308:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 127 = 15383974234308 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 127 = (8127:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_127
end WuPaper.ClassicalFourthConditions
#print axioms WuPaper.ClassicalFourthConditions.Log_block_007

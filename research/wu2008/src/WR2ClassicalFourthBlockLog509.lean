import WR2ClassicalFourthConditions
import WR2ClassicalFourthLogPoints509
noncomputable section
namespace WuPaper.ClassicalFourthConditions
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem Log_block_509 (j : Fin 16) (hj : 16*509+j.val < 10541) :
    WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 (16*509+j.val)) ≤ val WuPaper.ClassicalFourthData.Bq (16*509+j.val) := by
  fin_cases j
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 8144) ≤ val WuPaper.ClassicalFourthData.Bq 8144
    have hp : val WuPaper.ClassicalFourthData.Bq 8144 = (275158785811899:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 8144 = 275158785811899 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 8144 = (1009:ℝ)/250 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_8144
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 8145) ≤ val WuPaper.ClassicalFourthData.Bq 8145
    have hp : val WuPaper.ClassicalFourthData.Bq 8145 = (275162143409773:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 8145 = 275162143409773 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 8145 = (3229:ℝ)/800 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_8145
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 8146) ≤ val WuPaper.ClassicalFourthData.Bq 8146
    have hp : val WuPaper.ClassicalFourthData.Bq 8146 = (275165498912164:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 8146 = 275165498912164 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 8146 = (8073:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_8146
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 8147) ≤ val WuPaper.ClassicalFourthData.Bq 8147
    have hp : val WuPaper.ClassicalFourthData.Bq 8147 = (275168852319739:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 8147 = 275168852319739 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 8147 = (16147:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_8147
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 8148) ≤ val WuPaper.ClassicalFourthData.Bq 8148
    have hp : val WuPaper.ClassicalFourthData.Bq 8148 = (275172203633164:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 8148 = 275172203633164 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 8148 = (4037:ℝ)/1000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_8148
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 8149) ≤ val WuPaper.ClassicalFourthData.Bq 8149
    have hp : val WuPaper.ClassicalFourthData.Bq 8149 = (275175552853104:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 8149 = 275175552853104 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 8149 = (16149:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_8149
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 8150) ≤ val WuPaper.ClassicalFourthData.Bq 8150
    have hp : val WuPaper.ClassicalFourthData.Bq 8150 = (275178899980223:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 8150 = 275178899980223 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 8150 = (323:ℝ)/80 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_8150
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 8151) ≤ val WuPaper.ClassicalFourthData.Bq 8151
    have hp : val WuPaper.ClassicalFourthData.Bq 8151 = (275182245015188:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 8151 = 275182245015188 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 8151 = (16151:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_8151
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 8152) ≤ val WuPaper.ClassicalFourthData.Bq 8152
    have hp : val WuPaper.ClassicalFourthData.Bq 8152 = (275185587958663:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 8152 = 275185587958663 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 8152 = (2019:ℝ)/500 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_8152
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 8153) ≤ val WuPaper.ClassicalFourthData.Bq 8153
    have hp : val WuPaper.ClassicalFourthData.Bq 8153 = (275188928811312:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 8153 = 275188928811312 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 8153 = (16153:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_8153
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 8154) ≤ val WuPaper.ClassicalFourthData.Bq 8154
    have hp : val WuPaper.ClassicalFourthData.Bq 8154 = (275192267573799:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 8154 = 275192267573799 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 8154 = (8077:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_8154
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 8155) ≤ val WuPaper.ClassicalFourthData.Bq 8155
    have hp : val WuPaper.ClassicalFourthData.Bq 8155 = (275195604246789:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 8155 = 275195604246789 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 8155 = (3231:ℝ)/800 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_8155
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 8156) ≤ val WuPaper.ClassicalFourthData.Bq 8156
    have hp : val WuPaper.ClassicalFourthData.Bq 8156 = (275198938830944:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 8156 = 275198938830944 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 8156 = (4039:ℝ)/1000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_8156
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 8157) ≤ val WuPaper.ClassicalFourthData.Bq 8157
    have hp : val WuPaper.ClassicalFourthData.Bq 8157 = (275202271326930:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 8157 = 275202271326930 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 8157 = (16157:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_8157
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 8158) ≤ val WuPaper.ClassicalFourthData.Bq 8158
    have hp : val WuPaper.ClassicalFourthData.Bq 8158 = (275205601735409:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 8158 = 275205601735409 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 8158 = (8079:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_8158
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 8159) ≤ val WuPaper.ClassicalFourthData.Bq 8159
    have hp : val WuPaper.ClassicalFourthData.Bq 8159 = (275208930057043:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 8159 = 275208930057043 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 8159 = (16159:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_8159
end WuPaper.ClassicalFourthConditions
#print axioms WuPaper.ClassicalFourthConditions.Log_block_509

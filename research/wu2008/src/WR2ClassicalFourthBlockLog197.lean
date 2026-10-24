import WR2ClassicalFourthConditions
import WR2ClassicalFourthLogPoints197
noncomputable section
namespace WuPaper.ClassicalFourthConditions
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem Log_block_197 (j : Fin 16) (hj : 16*197+j.val < 10541) :
    WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 (16*197+j.val)) ≤ val WuPaper.ClassicalFourthData.Bq (16*197+j.val) := by
  fin_cases j
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 3152) ≤ val WuPaper.ClassicalFourthData.Bq 3152
    have hp : val WuPaper.ClassicalFourthData.Bq 3152 = (208428148045669:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 3152 = 208428148045669 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 3152 = (697:ℝ)/250 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_3152
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 3153) ≤ val WuPaper.ClassicalFourthData.Bq 3153
    have hp : val WuPaper.ClassicalFourthData.Bq 3153 = (208459602979058:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 3153 = 208459602979058 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 3153 = (11153:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_3153
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 3154) ≤ val WuPaper.ClassicalFourthData.Bq 3154
    have hp : val WuPaper.ClassicalFourthData.Bq 3154 = (208491045263381:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 3154 = 208491045263381 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 3154 = (5577:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_3154
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 3155) ≤ val WuPaper.ClassicalFourthData.Bq 3155
    have hp : val WuPaper.ClassicalFourthData.Bq 3155 = (208522474903998:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 3155 = 208522474903998 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 3155 = (2231:ℝ)/800 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_3155
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 3156) ≤ val WuPaper.ClassicalFourthData.Bq 3156
    have hp : val WuPaper.ClassicalFourthData.Bq 3156 = (208553891906269:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 3156 = 208553891906269 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 3156 = (2789:ℝ)/1000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_3156
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 3157) ≤ val WuPaper.ClassicalFourthData.Bq 3157
    have hp : val WuPaper.ClassicalFourthData.Bq 3157 = (208585296275548:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 3157 = 208585296275548 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 3157 = (11157:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_3157
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 3158) ≤ val WuPaper.ClassicalFourthData.Bq 3158
    have hp : val WuPaper.ClassicalFourthData.Bq 3158 = (208616688017188:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 3158 = 208616688017188 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 3158 = (5579:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_3158
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 3159) ≤ val WuPaper.ClassicalFourthData.Bq 3159
    have hp : val WuPaper.ClassicalFourthData.Bq 3159 = (208648067136539:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 3159 = 208648067136539 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 3159 = (11159:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_3159
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 3160) ≤ val WuPaper.ClassicalFourthData.Bq 3160
    have hp : val WuPaper.ClassicalFourthData.Bq 3160 = (208679433638948:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 3160 = 208679433638948 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 3160 = (279:ℝ)/100 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_3160
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 3161) ≤ val WuPaper.ClassicalFourthData.Bq 3161
    have hp : val WuPaper.ClassicalFourthData.Bq 3161 = (208710787529760:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 3161 = 208710787529760 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 3161 = (11161:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_3161
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 3162) ≤ val WuPaper.ClassicalFourthData.Bq 3162
    have hp : val WuPaper.ClassicalFourthData.Bq 3162 = (208742128814317:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 3162 = 208742128814317 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 3162 = (5581:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_3162
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 3163) ≤ val WuPaper.ClassicalFourthData.Bq 3163
    have hp : val WuPaper.ClassicalFourthData.Bq 3163 = (208773457497958:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 3163 = 208773457497958 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 3163 = (11163:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_3163
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 3164) ≤ val WuPaper.ClassicalFourthData.Bq 3164
    have hp : val WuPaper.ClassicalFourthData.Bq 3164 = (208804773586018:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 3164 = 208804773586018 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 3164 = (2791:ℝ)/1000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_3164
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 3165) ≤ val WuPaper.ClassicalFourthData.Bq 3165
    have hp : val WuPaper.ClassicalFourthData.Bq 3165 = (208836077083832:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 3165 = 208836077083832 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 3165 = (2233:ℝ)/800 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_3165
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 3166) ≤ val WuPaper.ClassicalFourthData.Bq 3166
    have hp : val WuPaper.ClassicalFourthData.Bq 3166 = (208867367996730:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 3166 = 208867367996730 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 3166 = (5583:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_3166
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 3167) ≤ val WuPaper.ClassicalFourthData.Bq 3167
    have hp : val WuPaper.ClassicalFourthData.Bq 3167 = (208898646330041:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 3167 = 208898646330041 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 3167 = (11167:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_3167
end WuPaper.ClassicalFourthConditions
#print axioms WuPaper.ClassicalFourthConditions.Log_block_197

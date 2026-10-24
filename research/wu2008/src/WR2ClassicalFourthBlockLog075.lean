import WR2ClassicalFourthConditions
import WR2ClassicalFourthLogPoints075
noncomputable section
namespace WuPaper.ClassicalFourthConditions
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem Log_block_075 (j : Fin 16) (hj : 16*75+j.val < 10541) :
    WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 (16*75+j.val)) ≤ val WuPaper.ClassicalFourthData.Bq (16*75+j.val) := by
  fin_cases j
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 1200) ≤ val WuPaper.ClassicalFourthData.Bq 1200
    have hp : val WuPaper.ClassicalFourthData.Bq 1200 = (114071419333692:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 1200 = 114071419333692 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 1200 = (23:ℝ)/10 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_1200
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 1201) ≤ val WuPaper.ClassicalFourthData.Bq 1201
    have hp : val WuPaper.ClassicalFourthData.Bq 1201 = (114142616529093:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 1201 = 114142616529093 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 1201 = (9201:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_1201
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 1202) ≤ val WuPaper.ClassicalFourthData.Bq 1202
    have hp : val WuPaper.ClassicalFourthData.Bq 1202 = (114213782180643:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 1202 = 114213782180643 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 1202 = (4601:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_1202
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 1203) ≤ val WuPaper.ClassicalFourthData.Bq 1203
    have hp : val WuPaper.ClassicalFourthData.Bq 1203 = (114284916304804:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 1203 = 114284916304804 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 1203 = (9203:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_1203
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 1204) ≤ val WuPaper.ClassicalFourthData.Bq 1204
    have hp : val WuPaper.ClassicalFourthData.Bq 1204 = (114356018918022:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 1204 = 114356018918022 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 1204 = (2301:ℝ)/1000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_1204
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 1205) ≤ val WuPaper.ClassicalFourthData.Bq 1205
    have hp : val WuPaper.ClassicalFourthData.Bq 1205 = (114427090036738:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 1205 = 114427090036738 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 1205 = (1841:ℝ)/800 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_1205
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 1206) ≤ val WuPaper.ClassicalFourthData.Bq 1206
    have hp : val WuPaper.ClassicalFourthData.Bq 1206 = (114498129677377:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 1206 = 114498129677377 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 1206 = (4603:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_1206
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 1207) ≤ val WuPaper.ClassicalFourthData.Bq 1207
    have hp : val WuPaper.ClassicalFourthData.Bq 1207 = (114569137856358:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 1207 = 114569137856358 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 1207 = (9207:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_1207
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 1208) ≤ val WuPaper.ClassicalFourthData.Bq 1208
    have hp : val WuPaper.ClassicalFourthData.Bq 1208 = (114640114590086:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 1208 = 114640114590086 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 1208 = (1151:ℝ)/500 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_1208
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 1209) ≤ val WuPaper.ClassicalFourthData.Bq 1209
    have hp : val WuPaper.ClassicalFourthData.Bq 1209 = (114711059894957:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 1209 = 114711059894957 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 1209 = (9209:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_1209
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 1210) ≤ val WuPaper.ClassicalFourthData.Bq 1210
    have hp : val WuPaper.ClassicalFourthData.Bq 1210 = (114781973787356:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 1210 = 114781973787356 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 1210 = (921:ℝ)/400 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_1210
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 1211) ≤ val WuPaper.ClassicalFourthData.Bq 1211
    have hp : val WuPaper.ClassicalFourthData.Bq 1211 = (114852856283656:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 1211 = 114852856283656 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 1211 = (9211:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_1211
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 1212) ≤ val WuPaper.ClassicalFourthData.Bq 1212
    have hp : val WuPaper.ClassicalFourthData.Bq 1212 = (114923707400221:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 1212 = 114923707400221 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 1212 = (2303:ℝ)/1000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_1212
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 1213) ≤ val WuPaper.ClassicalFourthData.Bq 1213
    have hp : val WuPaper.ClassicalFourthData.Bq 1213 = (114994527153405:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 1213 = 114994527153405 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 1213 = (9213:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_1213
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 1214) ≤ val WuPaper.ClassicalFourthData.Bq 1214
    have hp : val WuPaper.ClassicalFourthData.Bq 1214 = (115065315559549:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 1214 = 115065315559549 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 1214 = (4607:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_1214
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 1215) ≤ val WuPaper.ClassicalFourthData.Bq 1215
    have hp : val WuPaper.ClassicalFourthData.Bq 1215 = (115136072634985:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 1215 = 115136072634985 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 1215 = (1843:ℝ)/800 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_1215
end WuPaper.ClassicalFourthConditions
#print axioms WuPaper.ClassicalFourthConditions.Log_block_075

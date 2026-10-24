import WR2ClassicalFourthConditions
import WR2ClassicalFourthLogPoints200
noncomputable section
namespace WuPaper.ClassicalFourthConditions
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem Log_block_200 (j : Fin 16) (hj : 16*200+j.val < 10541) :
    WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 (16*200+j.val)) ≤ val WuPaper.ClassicalFourthData.Bq (16*200+j.val) := by
  fin_cases j
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 3200) ≤ val WuPaper.ClassicalFourthData.Bq 3200
    have hp : val WuPaper.ClassicalFourthData.Bq 3200 = (209923808893614:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 3200 = 209923808893614 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 3200 = (14:ℝ)/5 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_3200
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 3201) ≤ val WuPaper.ClassicalFourthData.Bq 3201
    have hp : val WuPaper.ClassicalFourthData.Bq 3201 = (209954662671847:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 3201 = 209954662671847 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 3201 = (11201:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_3201
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 3202) ≤ val WuPaper.ClassicalFourthData.Bq 3202
    have hp : val WuPaper.ClassicalFourthData.Bq 3202 = (209985504055274:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 3202 = 209985504055274 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 3202 = (5601:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_3202
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 3203) ≤ val WuPaper.ClassicalFourthData.Bq 3203
    have hp : val WuPaper.ClassicalFourthData.Bq 3203 = (210016333049125:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 3203 = 210016333049125 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 3203 = (11203:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_3203
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 3204) ≤ val WuPaper.ClassicalFourthData.Bq 3204
    have hp : val WuPaper.ClassicalFourthData.Bq 3204 = (210047149658629:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 3204 = 210047149658629 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 3204 = (2801:ℝ)/1000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_3204
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 3205) ≤ val WuPaper.ClassicalFourthData.Bq 3205
    have hp : val WuPaper.ClassicalFourthData.Bq 3205 = (210077953889012:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 3205 = 210077953889012 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 3205 = (2241:ℝ)/800 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_3205
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 3206) ≤ val WuPaper.ClassicalFourthData.Bq 3206
    have hp : val WuPaper.ClassicalFourthData.Bq 3206 = (210108745745498:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 3206 = 210108745745498 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 3206 = (5603:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_3206
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 3207) ≤ val WuPaper.ClassicalFourthData.Bq 3207
    have hp : val WuPaper.ClassicalFourthData.Bq 3207 = (210139525233306:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 3207 = 210139525233306 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 3207 = (11207:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_3207
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 3208) ≤ val WuPaper.ClassicalFourthData.Bq 3208
    have hp : val WuPaper.ClassicalFourthData.Bq 3208 = (210170292357654:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 3208 = 210170292357654 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 3208 = (1401:ℝ)/500 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_3208
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 3209) ≤ val WuPaper.ClassicalFourthData.Bq 3209
    have hp : val WuPaper.ClassicalFourthData.Bq 3209 = (210201047123759:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 3209 = 210201047123759 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 3209 = (11209:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_3209
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 3210) ≤ val WuPaper.ClassicalFourthData.Bq 3210
    have hp : val WuPaper.ClassicalFourthData.Bq 3210 = (210231789536831:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 3210 = 210231789536831 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 3210 = (1121:ℝ)/400 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_3210
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 3211) ≤ val WuPaper.ClassicalFourthData.Bq 3211
    have hp : val WuPaper.ClassicalFourthData.Bq 3211 = (210262519602081:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 3211 = 210262519602081 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 3211 = (11211:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_3211
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 3212) ≤ val WuPaper.ClassicalFourthData.Bq 3212
    have hp : val WuPaper.ClassicalFourthData.Bq 3212 = (210293237324717:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 3212 = 210293237324717 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 3212 = (2803:ℝ)/1000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_3212
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 3213) ≤ val WuPaper.ClassicalFourthData.Bq 3213
    have hp : val WuPaper.ClassicalFourthData.Bq 3213 = (210323942709943:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 3213 = 210323942709943 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 3213 = (11213:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_3213
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 3214) ≤ val WuPaper.ClassicalFourthData.Bq 3214
    have hp : val WuPaper.ClassicalFourthData.Bq 3214 = (210354635762960:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 3214 = 210354635762960 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 3214 = (5607:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_3214
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 3215) ≤ val WuPaper.ClassicalFourthData.Bq 3215
    have hp : val WuPaper.ClassicalFourthData.Bq 3215 = (210385316488968:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 3215 = 210385316488968 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 3215 = (2243:ℝ)/800 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_3215
end WuPaper.ClassicalFourthConditions
#print axioms WuPaper.ClassicalFourthConditions.Log_block_200

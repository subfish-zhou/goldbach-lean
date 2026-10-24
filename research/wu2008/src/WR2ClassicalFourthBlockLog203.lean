import WR2ClassicalFourthConditions
import WR2ClassicalFourthLogPoints203
noncomputable section
namespace WuPaper.ClassicalFourthConditions
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem Log_block_203 (j : Fin 16) (hj : 16*203+j.val < 10541) :
    WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 (16*203+j.val)) ≤ val WuPaper.ClassicalFourthData.Bq (16*203+j.val) := by
  fin_cases j
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 3248) ≤ val WuPaper.ClassicalFourthData.Bq 3248
    have hp : val WuPaper.ClassicalFourthData.Bq 3248 = (211390898869413:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 3248 = 211390898869413 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 3248 = (703:ℝ)/250 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_3248
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 3249) ≤ val WuPaper.ClassicalFourthData.Bq 3249
    have hp : val WuPaper.ClassicalFourthData.Bq 3249 = (211421163551907:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 3249 = 211421163551907 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 3249 = (11249:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_3249
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 3250) ≤ val WuPaper.ClassicalFourthData.Bq 3250
    have hp : val WuPaper.ClassicalFourthData.Bq 3250 = (211451416087713:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 3250 = 211451416087713 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 3250 = (45:ℝ)/16 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_3250
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 3251) ≤ val WuPaper.ClassicalFourthData.Bq 3251
    have hp : val WuPaper.ClassicalFourthData.Bq 3251 = (211481656481936:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 3251 = 211481656481936 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 3251 = (11251:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_3251
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 3252) ≤ val WuPaper.ClassicalFourthData.Bq 3252
    have hp : val WuPaper.ClassicalFourthData.Bq 3252 = (211511884739678:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 3252 = 211511884739678 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 3252 = (2813:ℝ)/1000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_3252
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 3253) ≤ val WuPaper.ClassicalFourthData.Bq 3253
    have hp : val WuPaper.ClassicalFourthData.Bq 3253 = (211542100866040:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 3253 = 211542100866040 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 3253 = (11253:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_3253
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 3254) ≤ val WuPaper.ClassicalFourthData.Bq 3254
    have hp : val WuPaper.ClassicalFourthData.Bq 3254 = (211572304866117:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 3254 = 211572304866117 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 3254 = (5627:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_3254
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 3255) ≤ val WuPaper.ClassicalFourthData.Bq 3255
    have hp : val WuPaper.ClassicalFourthData.Bq 3255 = (211602496745006:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 3255 = 211602496745006 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 3255 = (2251:ℝ)/800 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_3255
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 3256) ≤ val WuPaper.ClassicalFourthData.Bq 3256
    have hp : val WuPaper.ClassicalFourthData.Bq 3256 = (211632676507799:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 3256 = 211632676507799 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 3256 = (1407:ℝ)/500 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_3256
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 3257) ≤ val WuPaper.ClassicalFourthData.Bq 3257
    have hp : val WuPaper.ClassicalFourthData.Bq 3257 = (211662844159585:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 3257 = 211662844159585 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 3257 = (11257:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_3257
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 3258) ≤ val WuPaper.ClassicalFourthData.Bq 3258
    have hp : val WuPaper.ClassicalFourthData.Bq 3258 = (211692999705450:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 3258 = 211692999705450 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 3258 = (5629:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_3258
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 3259) ≤ val WuPaper.ClassicalFourthData.Bq 3259
    have hp : val WuPaper.ClassicalFourthData.Bq 3259 = (211723143150480:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 3259 = 211723143150480 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 3259 = (11259:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_3259
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 3260) ≤ val WuPaper.ClassicalFourthData.Bq 3260
    have hp : val WuPaper.ClassicalFourthData.Bq 3260 = (211753274499757:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 3260 = 211753274499757 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 3260 = (563:ℝ)/200 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_3260
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 3261) ≤ val WuPaper.ClassicalFourthData.Bq 3261
    have hp : val WuPaper.ClassicalFourthData.Bq 3261 = (211783393758359:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 3261 = 211783393758359 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 3261 = (11261:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_3261
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 3262) ≤ val WuPaper.ClassicalFourthData.Bq 3262
    have hp : val WuPaper.ClassicalFourthData.Bq 3262 = (211813500931364:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 3262 = 211813500931364 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 3262 = (5631:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_3262
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 3263) ≤ val WuPaper.ClassicalFourthData.Bq 3263
    have hp : val WuPaper.ClassicalFourthData.Bq 3263 = (211843596023845:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 3263 = 211843596023845 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 3263 = (11263:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_3263
end WuPaper.ClassicalFourthConditions
#print axioms WuPaper.ClassicalFourthConditions.Log_block_203

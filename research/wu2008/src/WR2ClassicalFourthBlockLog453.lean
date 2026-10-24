import WR2ClassicalFourthConditions
import WR2ClassicalFourthLogPoints453
noncomputable section
namespace WuPaper.ClassicalFourthConditions
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem Log_block_453 (j : Fin 16) (hj : 16*453+j.val < 10541) :
    WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 (16*453+j.val)) ≤ val WuPaper.ClassicalFourthData.Bq (16*453+j.val) := by
  fin_cases j
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 7248) ≤ val WuPaper.ClassicalFourthData.Bq 7248
    have hp : val WuPaper.ClassicalFourthData.Bq 7248 = (271221399252070:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 7248 = 271221399252070 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 7248 = (953:ℝ)/250 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_7248
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 7249) ≤ val WuPaper.ClassicalFourthData.Bq 7249
    have hp : val WuPaper.ClassicalFourthData.Bq 7249 = (271226932832651:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 7249 = 271226932832651 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 7249 = (15249:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_7249
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 7250) ≤ val WuPaper.ClassicalFourthData.Bq 7250
    have hp : val WuPaper.ClassicalFourthData.Bq 7250 = (271232463614692:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 7250 = 271232463614692 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 7250 = (61:ℝ)/16 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_7250
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 7251) ≤ val WuPaper.ClassicalFourthData.Bq 7251
    have hp : val WuPaper.ClassicalFourthData.Bq 7251 = (271237991599114:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 7251 = 271237991599114 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 7251 = (15251:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_7251
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 7252) ≤ val WuPaper.ClassicalFourthData.Bq 7252
    have hp : val WuPaper.ClassicalFourthData.Bq 7252 = (271243516786834:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 7252 = 271243516786834 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 7252 = (3813:ℝ)/1000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_7252
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 7253) ≤ val WuPaper.ClassicalFourthData.Bq 7253
    have hp : val WuPaper.ClassicalFourthData.Bq 7253 = (271249039178771:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 7253 = 271249039178771 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 7253 = (15253:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_7253
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 7254) ≤ val WuPaper.ClassicalFourthData.Bq 7254
    have hp : val WuPaper.ClassicalFourthData.Bq 7254 = (271254558775843:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 7254 = 271254558775843 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 7254 = (7627:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_7254
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 7255) ≤ val WuPaper.ClassicalFourthData.Bq 7255
    have hp : val WuPaper.ClassicalFourthData.Bq 7255 = (271260075578967:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 7255 = 271260075578967 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 7255 = (3051:ℝ)/800 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_7255
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 7256) ≤ val WuPaper.ClassicalFourthData.Bq 7256
    have hp : val WuPaper.ClassicalFourthData.Bq 7256 = (271265589589061:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 7256 = 271265589589061 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 7256 = (1907:ℝ)/500 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_7256
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 7257) ≤ val WuPaper.ClassicalFourthData.Bq 7257
    have hp : val WuPaper.ClassicalFourthData.Bq 7257 = (271271100807042:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 7257 = 271271100807042 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 7257 = (15257:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_7257
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 7258) ≤ val WuPaper.ClassicalFourthData.Bq 7258
    have hp : val WuPaper.ClassicalFourthData.Bq 7258 = (271276609233826:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 7258 = 271276609233826 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 7258 = (7629:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_7258
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 7259) ≤ val WuPaper.ClassicalFourthData.Bq 7259
    have hp : val WuPaper.ClassicalFourthData.Bq 7259 = (271282114870329:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 7259 = 271282114870329 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 7259 = (15259:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_7259
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 7260) ≤ val WuPaper.ClassicalFourthData.Bq 7260
    have hp : val WuPaper.ClassicalFourthData.Bq 7260 = (271287617717468:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 7260 = 271287617717468 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 7260 = (763:ℝ)/200 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_7260
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 7261) ≤ val WuPaper.ClassicalFourthData.Bq 7261
    have hp : val WuPaper.ClassicalFourthData.Bq 7261 = (271293117776158:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 7261 = 271293117776158 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 7261 = (15261:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_7261
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 7262) ≤ val WuPaper.ClassicalFourthData.Bq 7262
    have hp : val WuPaper.ClassicalFourthData.Bq 7262 = (271298615047314:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 7262 = 271298615047314 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 7262 = (7631:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_7262
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 7263) ≤ val WuPaper.ClassicalFourthData.Bq 7263
    have hp : val WuPaper.ClassicalFourthData.Bq 7263 = (271304109531851:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 7263 = 271304109531851 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 7263 = (15263:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_7263
end WuPaper.ClassicalFourthConditions
#print axioms WuPaper.ClassicalFourthConditions.Log_block_453

import WR2ClassicalFourthConditions
import WR2ClassicalFourthLogPoints328
noncomputable section
namespace WuPaper.ClassicalFourthConditions
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem Log_block_328 (j : Fin 16) (hj : 16*328+j.val < 10541) :
    WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 (16*328+j.val)) ≤ val WuPaper.ClassicalFourthData.Bq (16*328+j.val) := by
  fin_cases j
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 5248) ≤ val WuPaper.ClassicalFourthData.Bq 5248
    have hp : val WuPaper.ClassicalFourthData.Bq 5248 = (253053427176973:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 5248 = 253053427176973 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 5248 = (414:ℝ)/125 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_5248
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 5249) ≤ val WuPaper.ClassicalFourthData.Bq 5249
    have hp : val WuPaper.ClassicalFourthData.Bq 5249 = (253066971530602:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 5249 = 253066971530602 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 5249 = (13249:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_5249
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 5250) ≤ val WuPaper.ClassicalFourthData.Bq 5250
    have hp : val WuPaper.ClassicalFourthData.Bq 5250 = (253080510310776:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 5250 = 253080510310776 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 5250 = (53:ℝ)/16 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_5250
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 5251) ≤ val WuPaper.ClassicalFourthData.Bq 5251
    have hp : val WuPaper.ClassicalFourthData.Bq 5251 = (253094043519521:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 5251 = 253094043519521 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 5251 = (13251:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_5251
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 5252) ≤ val WuPaper.ClassicalFourthData.Bq 5252
    have hp : val WuPaper.ClassicalFourthData.Bq 5252 = (253107571158861:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 5252 = 253107571158861 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 5252 = (3313:ℝ)/1000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_5252
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 5253) ≤ val WuPaper.ClassicalFourthData.Bq 5253
    have hp : val WuPaper.ClassicalFourthData.Bq 5253 = (253121093230817:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 5253 = 253121093230817 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 5253 = (13253:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_5253
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 5254) ≤ val WuPaper.ClassicalFourthData.Bq 5254
    have hp : val WuPaper.ClassicalFourthData.Bq 5254 = (253134609737414:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 5254 = 253134609737414 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 5254 = (6627:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_5254
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 5255) ≤ val WuPaper.ClassicalFourthData.Bq 5255
    have hp : val WuPaper.ClassicalFourthData.Bq 5255 = (253148120680671:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 5255 = 253148120680671 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 5255 = (2651:ℝ)/800 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_5255
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 5256) ≤ val WuPaper.ClassicalFourthData.Bq 5256
    have hp : val WuPaper.ClassicalFourthData.Bq 5256 = (253161626062609:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 5256 = 253161626062609 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 5256 = (1657:ℝ)/500 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_5256
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 5257) ≤ val WuPaper.ClassicalFourthData.Bq 5257
    have hp : val WuPaper.ClassicalFourthData.Bq 5257 = (253175125885249:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 5257 = 253175125885249 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 5257 = (13257:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_5257
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 5258) ≤ val WuPaper.ClassicalFourthData.Bq 5258
    have hp : val WuPaper.ClassicalFourthData.Bq 5258 = (253188620150608:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 5258 = 253188620150608 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 5258 = (6629:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_5258
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 5259) ≤ val WuPaper.ClassicalFourthData.Bq 5259
    have hp : val WuPaper.ClassicalFourthData.Bq 5259 = (253202108860705:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 5259 = 253202108860705 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 5259 = (13259:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_5259
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 5260) ≤ val WuPaper.ClassicalFourthData.Bq 5260
    have hp : val WuPaper.ClassicalFourthData.Bq 5260 = (253215592017557:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 5260 = 253215592017557 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 5260 = (663:ℝ)/200 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_5260
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 5261) ≤ val WuPaper.ClassicalFourthData.Bq 5261
    have hp : val WuPaper.ClassicalFourthData.Bq 5261 = (253229069623179:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 5261 = 253229069623179 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 5261 = (13261:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_5261
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 5262) ≤ val WuPaper.ClassicalFourthData.Bq 5262
    have hp : val WuPaper.ClassicalFourthData.Bq 5262 = (253242541679588:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 5262 = 253242541679588 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 5262 = (6631:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_5262
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 5263) ≤ val WuPaper.ClassicalFourthData.Bq 5263
    have hp : val WuPaper.ClassicalFourthData.Bq 5263 = (253256008188797:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 5263 = 253256008188797 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 5263 = (13263:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_5263
end WuPaper.ClassicalFourthConditions
#print axioms WuPaper.ClassicalFourthConditions.Log_block_328

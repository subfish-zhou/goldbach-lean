import WR2ClassicalFourthConditions
import WR2ClassicalFourthLogPoints206
noncomputable section
namespace WuPaper.ClassicalFourthConditions
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem Log_block_206 (j : Fin 16) (hj : 16*206+j.val < 10541) :
    WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 (16*206+j.val)) ≤ val WuPaper.ClassicalFourthData.Bq (16*206+j.val) := by
  fin_cases j
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 3296) ≤ val WuPaper.ClassicalFourthData.Bq 3296
    have hp : val WuPaper.ClassicalFourthData.Bq 3296 = (212829989961806:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 3296 = 212829989961806 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 3296 = (353:ℝ)/125 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_3296
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 3297) ≤ val WuPaper.ClassicalFourthData.Bq 3297
    have hp : val WuPaper.ClassicalFourthData.Bq 3297 = (212859677317374:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 3297 = 212859677317374 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 3297 = (11297:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_3297
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 3298) ≤ val WuPaper.ClassicalFourthData.Bq 3298
    have hp : val WuPaper.ClassicalFourthData.Bq 3298 = (212889352768407:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 3298 = 212889352768407 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 3298 = (5649:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_3298
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 3299) ≤ val WuPaper.ClassicalFourthData.Bq 3299
    have hp : val WuPaper.ClassicalFourthData.Bq 3299 = (212919016319889:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 3299 = 212919016319889 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 3299 = (11299:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_3299
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 3300) ≤ val WuPaper.ClassicalFourthData.Bq 3300
    have hp : val WuPaper.ClassicalFourthData.Bq 3300 = (212948667976799:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 3300 = 212948667976799 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 3300 = (113:ℝ)/40 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_3300
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 3301) ≤ val WuPaper.ClassicalFourthData.Bq 3301
    have hp : val WuPaper.ClassicalFourthData.Bq 3301 = (212978307744115:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 3301 = 212978307744115 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 3301 = (11301:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_3301
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 3302) ≤ val WuPaper.ClassicalFourthData.Bq 3302
    have hp : val WuPaper.ClassicalFourthData.Bq 3302 = (213007935626812:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 3302 = 213007935626812 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 3302 = (5651:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_3302
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 3303) ≤ val WuPaper.ClassicalFourthData.Bq 3303
    have hp : val WuPaper.ClassicalFourthData.Bq 3303 = (213037551629862:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 3303 = 213037551629862 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 3303 = (11303:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_3303
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 3304) ≤ val WuPaper.ClassicalFourthData.Bq 3304
    have hp : val WuPaper.ClassicalFourthData.Bq 3304 = (213067155758237:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 3304 = 213067155758237 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 3304 = (1413:ℝ)/500 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_3304
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 3305) ≤ val WuPaper.ClassicalFourthData.Bq 3305
    have hp : val WuPaper.ClassicalFourthData.Bq 3305 = (213096748016904:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 3305 = 213096748016904 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 3305 = (2261:ℝ)/800 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_3305
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 3306) ≤ val WuPaper.ClassicalFourthData.Bq 3306
    have hp : val WuPaper.ClassicalFourthData.Bq 3306 = (213126328410827:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 3306 = 213126328410827 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 3306 = (5653:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_3306
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 3307) ≤ val WuPaper.ClassicalFourthData.Bq 3307
    have hp : val WuPaper.ClassicalFourthData.Bq 3307 = (213155896944969:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 3307 = 213155896944969 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 3307 = (11307:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_3307
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 3308) ≤ val WuPaper.ClassicalFourthData.Bq 3308
    have hp : val WuPaper.ClassicalFourthData.Bq 3308 = (213185453624291:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 3308 = 213185453624291 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 3308 = (2827:ℝ)/1000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_3308
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 3309) ≤ val WuPaper.ClassicalFourthData.Bq 3309
    have hp : val WuPaper.ClassicalFourthData.Bq 3309 = (213214998453750:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 3309 = 213214998453750 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 3309 = (11309:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_3309
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 3310) ≤ val WuPaper.ClassicalFourthData.Bq 3310
    have hp : val WuPaper.ClassicalFourthData.Bq 3310 = (213244531438302:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 3310 = 213244531438302 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 3310 = (1131:ℝ)/400 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_3310
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 3311) ≤ val WuPaper.ClassicalFourthData.Bq 3311
    have hp : val WuPaper.ClassicalFourthData.Bq 3311 = (213274052582898:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 3311 = 213274052582898 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 3311 = (11311:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_3311
end WuPaper.ClassicalFourthConditions
#print axioms WuPaper.ClassicalFourthConditions.Log_block_206

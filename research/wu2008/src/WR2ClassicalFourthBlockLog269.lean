import WR2ClassicalFourthConditions
import WR2ClassicalFourthLogPoints269
noncomputable section
namespace WuPaper.ClassicalFourthConditions
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem Log_block_269 (j : Fin 16) (hj : 16*269+j.val < 10541) :
    WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 (16*269+j.val)) ≤ val WuPaper.ClassicalFourthData.Bq (16*269+j.val) := by
  fin_cases j
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 4304) ≤ val WuPaper.ClassicalFourthData.Bq 4304
    have hp : val WuPaper.ClassicalFourthData.Bq 4304 = (237465203284670:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 4304 = 237465203284670 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 4304 = (769:ℝ)/250 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_4304
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 4305) ≤ val WuPaper.ClassicalFourthData.Bq 4305
    have hp : val WuPaper.ClassicalFourthData.Bq 4305 = (237485048986711:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 4305 = 237485048986711 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 4305 = (2461:ℝ)/800 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_4305
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 4306) ≤ val WuPaper.ClassicalFourthData.Bq 4306
    have hp : val WuPaper.ClassicalFourthData.Bq 4306 = (237504886750747:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 4306 = 237504886750747 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 4306 = (6153:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_4306
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 4307) ≤ val WuPaper.ClassicalFourthData.Bq 4307
    have hp : val WuPaper.ClassicalFourthData.Bq 4307 = (237524716579847:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 4307 = 237524716579847 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 4307 = (12307:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_4307
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 4308) ≤ val WuPaper.ClassicalFourthData.Bq 4308
    have hp : val WuPaper.ClassicalFourthData.Bq 4308 = (237544538477081:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 4308 = 237544538477081 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 4308 = (3077:ℝ)/1000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_4308
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 4309) ≤ val WuPaper.ClassicalFourthData.Bq 4309
    have hp : val WuPaper.ClassicalFourthData.Bq 4309 = (237564352445513:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 4309 = 237564352445513 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 4309 = (12309:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_4309
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 4310) ≤ val WuPaper.ClassicalFourthData.Bq 4310
    have hp : val WuPaper.ClassicalFourthData.Bq 4310 = (237584158488210:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 4310 = 237584158488210 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 4310 = (1231:ℝ)/400 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_4310
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 4311) ≤ val WuPaper.ClassicalFourthData.Bq 4311
    have hp : val WuPaper.ClassicalFourthData.Bq 4311 = (237603956608237:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 4311 = 237603956608237 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 4311 = (12311:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_4311
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 4312) ≤ val WuPaper.ClassicalFourthData.Bq 4312
    have hp : val WuPaper.ClassicalFourthData.Bq 4312 = (237623746808654:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 4312 = 237623746808654 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 4312 = (1539:ℝ)/500 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_4312
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 4313) ≤ val WuPaper.ClassicalFourthData.Bq 4313
    have hp : val WuPaper.ClassicalFourthData.Bq 4313 = (237643529092524:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 4313 = 237643529092524 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 4313 = (12313:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_4313
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 4314) ≤ val WuPaper.ClassicalFourthData.Bq 4314
    have hp : val WuPaper.ClassicalFourthData.Bq 4314 = (237663303462906:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 4314 = 237663303462906 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 4314 = (6157:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_4314
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 4315) ≤ val WuPaper.ClassicalFourthData.Bq 4315
    have hp : val WuPaper.ClassicalFourthData.Bq 4315 = (237683069922859:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 4315 = 237683069922859 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 4315 = (2463:ℝ)/800 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_4315
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 4316) ≤ val WuPaper.ClassicalFourthData.Bq 4316
    have hp : val WuPaper.ClassicalFourthData.Bq 4316 = (237702828475439:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 4316 = 237702828475439 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 4316 = (3079:ℝ)/1000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_4316
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 4317) ≤ val WuPaper.ClassicalFourthData.Bq 4317
    have hp : val WuPaper.ClassicalFourthData.Bq 4317 = (237722579123703:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 4317 = 237722579123703 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 4317 = (12317:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_4317
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 4318) ≤ val WuPaper.ClassicalFourthData.Bq 4318
    have hp : val WuPaper.ClassicalFourthData.Bq 4318 = (237742321870703:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 4318 = 237742321870703 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 4318 = (6159:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_4318
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 4319) ≤ val WuPaper.ClassicalFourthData.Bq 4319
    have hp : val WuPaper.ClassicalFourthData.Bq 4319 = (237762056719494:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 4319 = 237762056719494 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 4319 = (12319:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_4319
end WuPaper.ClassicalFourthConditions
#print axioms WuPaper.ClassicalFourthConditions.Log_block_269

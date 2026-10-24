import WR2ClassicalFourthConditions
import WR2ClassicalFourthLogPoints274
noncomputable section
namespace WuPaper.ClassicalFourthConditions
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem Log_block_274 (j : Fin 16) (hj : 16*274+j.val < 10541) :
    WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 (16*274+j.val)) ≤ val WuPaper.ClassicalFourthData.Bq (16*274+j.val) := by
  fin_cases j
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 4384) ≤ val WuPaper.ClassicalFourthData.Bq 4384
    have hp : val WuPaper.ClassicalFourthData.Bq 4384 = (239028025341989:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 4384 = 239028025341989 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 4384 = (387:ℝ)/125 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_4384
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 4385) ≤ val WuPaper.ClassicalFourthData.Bq 4385
    have hp : val WuPaper.ClassicalFourthData.Bq 4385 = (239047245589110:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 4385 = 239047245589110 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 4385 = (2477:ℝ)/800 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_4385
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 4386) ≤ val WuPaper.ClassicalFourthData.Bq 4386
    have hp : val WuPaper.ClassicalFourthData.Bq 4386 = (239066458139410:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 4386 = 239066458139410 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 4386 = (6193:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_4386
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 4387) ≤ val WuPaper.ClassicalFourthData.Bq 4387
    have hp : val WuPaper.ClassicalFourthData.Bq 4387 = (239085662995846:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 4387 = 239085662995846 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 4387 = (12387:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_4387
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 4388) ≤ val WuPaper.ClassicalFourthData.Bq 4388
    have hp : val WuPaper.ClassicalFourthData.Bq 4388 = (239104860161377:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 4388 = 239104860161377 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 4388 = (3097:ℝ)/1000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_4388
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 4389) ≤ val WuPaper.ClassicalFourthData.Bq 4389
    have hp : val WuPaper.ClassicalFourthData.Bq 4389 = (239124049638960:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 4389 = 239124049638960 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 4389 = (12389:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_4389
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 4390) ≤ val WuPaper.ClassicalFourthData.Bq 4390
    have hp : val WuPaper.ClassicalFourthData.Bq 4390 = (239143231431550:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 4390 = 239143231431550 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 4390 = (1239:ℝ)/400 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_4390
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 4391) ≤ val WuPaper.ClassicalFourthData.Bq 4391
    have hp : val WuPaper.ClassicalFourthData.Bq 4391 = (239162405542101:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 4391 = 239162405542101 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 4391 = (12391:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_4391
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 4392) ≤ val WuPaper.ClassicalFourthData.Bq 4392
    have hp : val WuPaper.ClassicalFourthData.Bq 4392 = (239181571973566:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 4392 = 239181571973566 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 4392 = (1549:ℝ)/500 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_4392
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 4393) ≤ val WuPaper.ClassicalFourthData.Bq 4393
    have hp : val WuPaper.ClassicalFourthData.Bq 4393 = (239200730728896:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 4393 = 239200730728896 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 4393 = (12393:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_4393
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 4394) ≤ val WuPaper.ClassicalFourthData.Bq 4394
    have hp : val WuPaper.ClassicalFourthData.Bq 4394 = (239219881811041:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 4394 = 239219881811041 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 4394 = (6197:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_4394
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 4395) ≤ val WuPaper.ClassicalFourthData.Bq 4395
    have hp : val WuPaper.ClassicalFourthData.Bq 4395 = (239239025222950:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 4395 = 239239025222950 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 4395 = (2479:ℝ)/800 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_4395
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 4396) ≤ val WuPaper.ClassicalFourthData.Bq 4396
    have hp : val WuPaper.ClassicalFourthData.Bq 4396 = (239258160967569:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 4396 = 239258160967569 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 4396 = (3099:ℝ)/1000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_4396
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 4397) ≤ val WuPaper.ClassicalFourthData.Bq 4397
    have hp : val WuPaper.ClassicalFourthData.Bq 4397 = (239277289047846:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 4397 = 239277289047846 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 4397 = (12397:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_4397
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 4398) ≤ val WuPaper.ClassicalFourthData.Bq 4398
    have hp : val WuPaper.ClassicalFourthData.Bq 4398 = (239296409466724:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 4398 = 239296409466724 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 4398 = (6199:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_4398
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 4399) ≤ val WuPaper.ClassicalFourthData.Bq 4399
    have hp : val WuPaper.ClassicalFourthData.Bq 4399 = (239315522227148:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 4399 = 239315522227148 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 4399 = (12399:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_4399
end WuPaper.ClassicalFourthConditions
#print axioms WuPaper.ClassicalFourthConditions.Log_block_274

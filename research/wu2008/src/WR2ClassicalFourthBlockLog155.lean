import WR2ClassicalFourthConditions
import WR2ClassicalFourthLogPoints155
noncomputable section
namespace WuPaper.ClassicalFourthConditions
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem Log_block_155 (j : Fin 16) (hj : 16*155+j.val < 10541) :
    WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 (16*155+j.val)) ≤ val WuPaper.ClassicalFourthData.Bq (16*155+j.val) := by
  fin_cases j
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 2480) ≤ val WuPaper.ClassicalFourthData.Bq 2480
    have hp : val WuPaper.ClassicalFourthData.Bq 2480 = (184132118032173:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 2480 = 184132118032173 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 2480 = (131:ℝ)/50 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_2480
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 2481) ≤ val WuPaper.ClassicalFourthData.Bq 2481
    have hp : val WuPaper.ClassicalFourthData.Bq 2481 = (184173440826520:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 2481 = 184173440826520 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 2481 = (10481:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_2481
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 2482) ≤ val WuPaper.ClassicalFourthData.Bq 2482
    have hp : val WuPaper.ClassicalFourthData.Bq 2482 = (184214746651199:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 2482 = 184214746651199 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 2482 = (5241:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_2482
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 2483) ≤ val WuPaper.ClassicalFourthData.Bq 2483
    have hp : val WuPaper.ClassicalFourthData.Bq 2483 = (184256035513868:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 2483 = 184256035513868 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 2483 = (10483:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_2483
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 2484) ≤ val WuPaper.ClassicalFourthData.Bq 2484
    have hp : val WuPaper.ClassicalFourthData.Bq 2484 = (184297307422183:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 2484 = 184297307422183 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 2484 = (2621:ℝ)/1000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_2484
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 2485) ≤ val WuPaper.ClassicalFourthData.Bq 2485
    have hp : val WuPaper.ClassicalFourthData.Bq 2485 = (184338562383793:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 2485 = 184338562383793 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 2485 = (2097:ℝ)/800 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_2485
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 2486) ≤ val WuPaper.ClassicalFourthData.Bq 2486
    have hp : val WuPaper.ClassicalFourthData.Bq 2486 = (184379800406346:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 2486 = 184379800406346 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 2486 = (5243:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_2486
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 2487) ≤ val WuPaper.ClassicalFourthData.Bq 2487
    have hp : val WuPaper.ClassicalFourthData.Bq 2487 = (184421021497484:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 2487 = 184421021497484 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 2487 = (10487:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_2487
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 2488) ≤ val WuPaper.ClassicalFourthData.Bq 2488
    have hp : val WuPaper.ClassicalFourthData.Bq 2488 = (184462225664845:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 2488 = 184462225664845 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 2488 = (1311:ℝ)/500 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_2488
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 2489) ≤ val WuPaper.ClassicalFourthData.Bq 2489
    have hp : val WuPaper.ClassicalFourthData.Bq 2489 = (184503412916061:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 2489 = 184503412916061 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 2489 = (10489:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_2489
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 2490) ≤ val WuPaper.ClassicalFourthData.Bq 2490
    have hp : val WuPaper.ClassicalFourthData.Bq 2490 = (184544583258764:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 2490 = 184544583258764 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 2490 = (1049:ℝ)/400 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_2490
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 2491) ≤ val WuPaper.ClassicalFourthData.Bq 2491
    have hp : val WuPaper.ClassicalFourthData.Bq 2491 = (184585736700578:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 2491 = 184585736700578 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 2491 = (10491:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_2491
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 2492) ≤ val WuPaper.ClassicalFourthData.Bq 2492
    have hp : val WuPaper.ClassicalFourthData.Bq 2492 = (184626873249125:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 2492 = 184626873249125 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 2492 = (2623:ℝ)/1000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_2492
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 2493) ≤ val WuPaper.ClassicalFourthData.Bq 2493
    have hp : val WuPaper.ClassicalFourthData.Bq 2493 = (184667992912021:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 2493 = 184667992912021 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 2493 = (10493:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_2493
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 2494) ≤ val WuPaper.ClassicalFourthData.Bq 2494
    have hp : val WuPaper.ClassicalFourthData.Bq 2494 = (184709095696880:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 2494 = 184709095696880 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 2494 = (5247:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_2494
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 2495) ≤ val WuPaper.ClassicalFourthData.Bq 2495
    have hp : val WuPaper.ClassicalFourthData.Bq 2495 = (184750181611310:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 2495 = 184750181611310 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 2495 = (2099:ℝ)/800 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_2495
end WuPaper.ClassicalFourthConditions
#print axioms WuPaper.ClassicalFourthConditions.Log_block_155

import WR2ClassicalFourthConditions
import WR2ClassicalFourthLogPoints335
noncomputable section
namespace WuPaper.ClassicalFourthConditions
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem Log_block_335 (j : Fin 16) (hj : 16*335+j.val < 10541) :
    WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 (16*335+j.val)) ≤ val WuPaper.ClassicalFourthData.Bq (16*335+j.val) := by
  fin_cases j
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 5360) ≤ val WuPaper.ClassicalFourthData.Bq 5360
    have hp : val WuPaper.ClassicalFourthData.Bq 5360 = (254536206398088:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 5360 = 254536206398088 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 5360 = (167:ℝ)/50 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_5360
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 5361) ≤ val WuPaper.ClassicalFourthData.Bq 5361
    have hp : val WuPaper.ClassicalFourthData.Bq 5361 = (254549138917662:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 5361 = 254549138917662 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 5361 = (13361:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_5361
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 5362) ≤ val WuPaper.ClassicalFourthData.Bq 5362
    have hp : val WuPaper.ClassicalFourthData.Bq 5362 = (254562066085314:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 5362 = 254562066085314 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 5362 = (6681:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_5362
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 5363) ≤ val WuPaper.ClassicalFourthData.Bq 5363
    have hp : val WuPaper.ClassicalFourthData.Bq 5363 = (254574987902975:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 5363 = 254574987902975 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 5363 = (13363:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_5363
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 5364) ≤ val WuPaper.ClassicalFourthData.Bq 5364
    have hp : val WuPaper.ClassicalFourthData.Bq 5364 = (254587904372576:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 5364 = 254587904372576 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 5364 = (3341:ℝ)/1000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_5364
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 5365) ≤ val WuPaper.ClassicalFourthData.Bq 5365
    have hp : val WuPaper.ClassicalFourthData.Bq 5365 = (254600815496046:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 5365 = 254600815496046 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 5365 = (2673:ℝ)/800 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_5365
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 5366) ≤ val WuPaper.ClassicalFourthData.Bq 5366
    have hp : val WuPaper.ClassicalFourthData.Bq 5366 = (254613721275314:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 5366 = 254613721275314 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 5366 = (6683:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_5366
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 5367) ≤ val WuPaper.ClassicalFourthData.Bq 5367
    have hp : val WuPaper.ClassicalFourthData.Bq 5367 = (254626621712308:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 5367 = 254626621712308 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 5367 = (13367:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_5367
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 5368) ≤ val WuPaper.ClassicalFourthData.Bq 5368
    have hp : val WuPaper.ClassicalFourthData.Bq 5368 = (254639516808956:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 5368 = 254639516808956 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 5368 = (1671:ℝ)/500 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_5368
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 5369) ≤ val WuPaper.ClassicalFourthData.Bq 5369
    have hp : val WuPaper.ClassicalFourthData.Bq 5369 = (254652406567182:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 5369 = 254652406567182 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 5369 = (13369:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_5369
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 5370) ≤ val WuPaper.ClassicalFourthData.Bq 5370
    have hp : val WuPaper.ClassicalFourthData.Bq 5370 = (254665290988914:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 5370 = 254665290988914 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 5370 = (1337:ℝ)/400 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_5370
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 5371) ≤ val WuPaper.ClassicalFourthData.Bq 5371
    have hp : val WuPaper.ClassicalFourthData.Bq 5371 = (254678170076075:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 5371 = 254678170076075 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 5371 = (13371:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_5371
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 5372) ≤ val WuPaper.ClassicalFourthData.Bq 5372
    have hp : val WuPaper.ClassicalFourthData.Bq 5372 = (254691043830590:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 5372 = 254691043830590 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 5372 = (3343:ℝ)/1000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_5372
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 5373) ≤ val WuPaper.ClassicalFourthData.Bq 5373
    have hp : val WuPaper.ClassicalFourthData.Bq 5373 = (254703912254382:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 5373 = 254703912254382 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 5373 = (13373:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_5373
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 5374) ≤ val WuPaper.ClassicalFourthData.Bq 5374
    have hp : val WuPaper.ClassicalFourthData.Bq 5374 = (254716775349373:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 5374 = 254716775349373 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 5374 = (6687:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_5374
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 5375) ≤ val WuPaper.ClassicalFourthData.Bq 5375
    have hp : val WuPaper.ClassicalFourthData.Bq 5375 = (254729633117484:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 5375 = 254729633117484 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 5375 = (107:ℝ)/32 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_5375
end WuPaper.ClassicalFourthConditions
#print axioms WuPaper.ClassicalFourthConditions.Log_block_335

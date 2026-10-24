import WR2ClassicalFourthConditions
import WR2ClassicalFourthLogPoints342
noncomputable section
namespace WuPaper.ClassicalFourthConditions
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem Log_block_342 (j : Fin 16) (hj : 16*342+j.val < 10541) :
    WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 (16*342+j.val)) ≤ val WuPaper.ClassicalFourthData.Bq (16*342+j.val) := by
  fin_cases j
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 5472) ≤ val WuPaper.ClassicalFourthData.Bq 5472
    have hp : val WuPaper.ClassicalFourthData.Bq 5472 = (255951816217863:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 5472 = 255951816217863 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 5472 = (421:ℝ)/125 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_5472
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 5473) ≤ val WuPaper.ClassicalFourthData.Bq 5473
    have hp : val WuPaper.ClassicalFourthData.Bq 5473 = (255964161144069:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 5473 = 255964161144069 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 5473 = (13473:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_5473
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 5474) ≤ val WuPaper.ClassicalFourthData.Bq 5474
    have hp : val WuPaper.ClassicalFourthData.Bq 5474 = (255976500929694:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 5474 = 255976500929694 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 5474 = (6737:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_5474
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 5475) ≤ val WuPaper.ClassicalFourthData.Bq 5475
    have hp : val WuPaper.ClassicalFourthData.Bq 5475 = (255988835576580:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 5475 = 255988835576580 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 5475 = (539:ℝ)/160 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_5475
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 5476) ≤ val WuPaper.ClassicalFourthData.Bq 5476
    have hp : val WuPaper.ClassicalFourthData.Bq 5476 = (256001165086570:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 5476 = 256001165086570 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 5476 = (3369:ℝ)/1000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_5476
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 5477) ≤ val WuPaper.ClassicalFourthData.Bq 5477
    have hp : val WuPaper.ClassicalFourthData.Bq 5477 = (256013489461504:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 5477 = 256013489461504 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 5477 = (13477:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_5477
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 5478) ≤ val WuPaper.ClassicalFourthData.Bq 5478
    have hp : val WuPaper.ClassicalFourthData.Bq 5478 = (256025808703223:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 5478 = 256025808703223 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 5478 = (6739:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_5478
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 5479) ≤ val WuPaper.ClassicalFourthData.Bq 5479
    have hp : val WuPaper.ClassicalFourthData.Bq 5479 = (256038122813567:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 5479 = 256038122813567 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 5479 = (13479:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_5479
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 5480) ≤ val WuPaper.ClassicalFourthData.Bq 5480
    have hp : val WuPaper.ClassicalFourthData.Bq 5480 = (256050431794375:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 5480 = 256050431794375 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 5480 = (337:ℝ)/100 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_5480
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 5481) ≤ val WuPaper.ClassicalFourthData.Bq 5481
    have hp : val WuPaper.ClassicalFourthData.Bq 5481 = (256062735647485:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 5481 = 256062735647485 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 5481 = (13481:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_5481
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 5482) ≤ val WuPaper.ClassicalFourthData.Bq 5482
    have hp : val WuPaper.ClassicalFourthData.Bq 5482 = (256075034374734:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 5482 = 256075034374734 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 5482 = (6741:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_5482
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 5483) ≤ val WuPaper.ClassicalFourthData.Bq 5483
    have hp : val WuPaper.ClassicalFourthData.Bq 5483 = (256087327977959:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 5483 = 256087327977959 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 5483 = (13483:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_5483
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 5484) ≤ val WuPaper.ClassicalFourthData.Bq 5484
    have hp : val WuPaper.ClassicalFourthData.Bq 5484 = (256099616458995:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 5484 = 256099616458995 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 5484 = (3371:ℝ)/1000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_5484
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 5485) ≤ val WuPaper.ClassicalFourthData.Bq 5485
    have hp : val WuPaper.ClassicalFourthData.Bq 5485 = (256111899819679:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 5485 = 256111899819679 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 5485 = (2697:ℝ)/800 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_5485
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 5486) ≤ val WuPaper.ClassicalFourthData.Bq 5486
    have hp : val WuPaper.ClassicalFourthData.Bq 5486 = (256124178061843:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 5486 = 256124178061843 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 5486 = (6743:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_5486
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 5487) ≤ val WuPaper.ClassicalFourthData.Bq 5487
    have hp : val WuPaper.ClassicalFourthData.Bq 5487 = (256136451187322:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 5487 = 256136451187322 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 5487 = (13487:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_5487
end WuPaper.ClassicalFourthConditions
#print axioms WuPaper.ClassicalFourthConditions.Log_block_342

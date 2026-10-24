import WR2ClassicalFourthConditions
import WR2ClassicalFourthLogPoints649
noncomputable section
namespace WuPaper.ClassicalFourthConditions
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem Log_block_649 (j : Fin 16) (hj : 16*649+j.val < 10541) :
    WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 (16*649+j.val)) ≤ val WuPaper.ClassicalFourthData.Bq (16*649+j.val) := by
  fin_cases j
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 10384) ≤ val WuPaper.ClassicalFourthData.Bq 10384
    have hp : val WuPaper.ClassicalFourthData.Bq 10384 = (278464342206283:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 10384 = 278464342206283 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 10384 = (1149:ℝ)/250 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_10384
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 10385) ≤ val WuPaper.ClassicalFourthData.Bq 10385
    have hp : val WuPaper.ClassicalFourthData.Bq 10385 = (278464321143231:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 10385 = 278464321143231 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 10385 = (3677:ℝ)/800 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_10385
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 10386) ≤ val WuPaper.ClassicalFourthData.Bq 10386
    have hp : val WuPaper.ClassicalFourthData.Bq 10386 = (278464299031107:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 10386 = 278464299031107 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 10386 = (9193:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_10386
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 10387) ≤ val WuPaper.ClassicalFourthData.Bq 10387
    have hp : val WuPaper.ClassicalFourthData.Bq 10387 = (278464275870227:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 10387 = 278464275870227 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 10387 = (18387:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_10387
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 10388) ≤ val WuPaper.ClassicalFourthData.Bq 10388
    have hp : val WuPaper.ClassicalFourthData.Bq 10388 = (278464251660910:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 10388 = 278464251660910 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 10388 = (4597:ℝ)/1000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_10388
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 10389) ≤ val WuPaper.ClassicalFourthData.Bq 10389
    have hp : val WuPaper.ClassicalFourthData.Bq 10389 = (278464226403472:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 10389 = 278464226403472 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 10389 = (18389:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_10389
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 10390) ≤ val WuPaper.ClassicalFourthData.Bq 10390
    have hp : val WuPaper.ClassicalFourthData.Bq 10390 = (278464200098230:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 10390 = 278464200098230 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 10390 = (1839:ℝ)/400 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_10390
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 10391) ≤ val WuPaper.ClassicalFourthData.Bq 10391
    have hp : val WuPaper.ClassicalFourthData.Bq 10391 = (278464172745501:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 10391 = 278464172745501 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 10391 = (18391:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_10391
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 10392) ≤ val WuPaper.ClassicalFourthData.Bq 10392
    have hp : val WuPaper.ClassicalFourthData.Bq 10392 = (278464144345602:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 10392 = 278464144345602 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 10392 = (2299:ℝ)/500 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_10392
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 10393) ≤ val WuPaper.ClassicalFourthData.Bq 10393
    have hp : val WuPaper.ClassicalFourthData.Bq 10393 = (278464114898850:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 10393 = 278464114898850 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 10393 = (18393:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_10393
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 10394) ≤ val WuPaper.ClassicalFourthData.Bq 10394
    have hp : val WuPaper.ClassicalFourthData.Bq 10394 = (278464084405561:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 10394 = 278464084405561 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 10394 = (9197:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_10394
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 10395) ≤ val WuPaper.ClassicalFourthData.Bq 10395
    have hp : val WuPaper.ClassicalFourthData.Bq 10395 = (278464052866051:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 10395 = 278464052866051 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 10395 = (3679:ℝ)/800 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_10395
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 10396) ≤ val WuPaper.ClassicalFourthData.Bq 10396
    have hp : val WuPaper.ClassicalFourthData.Bq 10396 = (278464020280638:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 10396 = 278464020280638 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 10396 = (4599:ℝ)/1000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_10396
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 10397) ≤ val WuPaper.ClassicalFourthData.Bq 10397
    have hp : val WuPaper.ClassicalFourthData.Bq 10397 = (278463986649638:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 10397 = 278463986649638 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 10397 = (18397:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_10397
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 10398) ≤ val WuPaper.ClassicalFourthData.Bq 10398
    have hp : val WuPaper.ClassicalFourthData.Bq 10398 = (278463951973366:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 10398 = 278463951973366 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 10398 = (9199:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_10398
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 10399) ≤ val WuPaper.ClassicalFourthData.Bq 10399
    have hp : val WuPaper.ClassicalFourthData.Bq 10399 = (278463916252139:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 10399 = 278463916252139 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 10399 = (18399:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_10399
end WuPaper.ClassicalFourthConditions
#print axioms WuPaper.ClassicalFourthConditions.Log_block_649

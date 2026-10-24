import WR2ClassicalFourthConditions
import WR2ClassicalFourthLogPoints218
noncomputable section
namespace WuPaper.ClassicalFourthConditions
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem Log_block_218 (j : Fin 16) (hj : 16*218+j.val < 10541) :
    WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 (16*218+j.val)) ≤ val WuPaper.ClassicalFourthData.Bq (16*218+j.val) := by
  fin_cases j
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 3488) ≤ val WuPaper.ClassicalFourthData.Bq 3488
    have hp : val WuPaper.ClassicalFourthData.Bq 3488 = (218317332191992:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 3488 = 218317332191992 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 3488 = (359:ℝ)/125 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_3488
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 3489) ≤ val WuPaper.ClassicalFourthData.Bq 3489
    have hp : val WuPaper.ClassicalFourthData.Bq 3489 = (218344822403113:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 3489 = 218344822403113 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 3489 = (11489:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_3489
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 3490) ≤ val WuPaper.ClassicalFourthData.Bq 3490
    have hp : val WuPaper.ClassicalFourthData.Bq 3490 = (218372301622015:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 3490 = 218372301622015 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 3490 = (1149:ℝ)/400 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_3490
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 3491) ≤ val WuPaper.ClassicalFourthData.Bq 3491
    have hp : val WuPaper.ClassicalFourthData.Bq 3491 = (218399769853227:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 3491 = 218399769853227 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 3491 = (11491:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_3491
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 3492) ≤ val WuPaper.ClassicalFourthData.Bq 3492
    have hp : val WuPaper.ClassicalFourthData.Bq 3492 = (218427227101271:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 3492 = 218427227101271 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 3492 = (2873:ℝ)/1000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_3492
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 3493) ≤ val WuPaper.ClassicalFourthData.Bq 3493
    have hp : val WuPaper.ClassicalFourthData.Bq 3493 = (218454673370672:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 3493 = 218454673370672 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 3493 = (11493:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_3493
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 3494) ≤ val WuPaper.ClassicalFourthData.Bq 3494
    have hp : val WuPaper.ClassicalFourthData.Bq 3494 = (218482108665950:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 3494 = 218482108665950 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 3494 = (5747:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_3494
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 3495) ≤ val WuPaper.ClassicalFourthData.Bq 3495
    have hp : val WuPaper.ClassicalFourthData.Bq 3495 = (218509532991621:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 3495 = 218509532991621 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 3495 = (2299:ℝ)/800 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_3495
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 3496) ≤ val WuPaper.ClassicalFourthData.Bq 3496
    have hp : val WuPaper.ClassicalFourthData.Bq 3496 = (218536946352203:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 3496 = 218536946352203 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 3496 = (1437:ℝ)/500 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_3496
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 3497) ≤ val WuPaper.ClassicalFourthData.Bq 3497
    have hp : val WuPaper.ClassicalFourthData.Bq 3497 = (218564348752209:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 3497 = 218564348752209 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 3497 = (11497:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_3497
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 3498) ≤ val WuPaper.ClassicalFourthData.Bq 3498
    have hp : val WuPaper.ClassicalFourthData.Bq 3498 = (218591740196149:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 3498 = 218591740196149 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 3498 = (5749:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_3498
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 3499) ≤ val WuPaper.ClassicalFourthData.Bq 3499
    have hp : val WuPaper.ClassicalFourthData.Bq 3499 = (218619120688534:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 3499 = 218619120688534 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 3499 = (11499:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_3499
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 3500) ≤ val WuPaper.ClassicalFourthData.Bq 3500
    have hp : val WuPaper.ClassicalFourthData.Bq 3500 = (218646490233870:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 3500 = 218646490233870 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 3500 = (23:ℝ)/8 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_3500
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 3501) ≤ val WuPaper.ClassicalFourthData.Bq 3501
    have hp : val WuPaper.ClassicalFourthData.Bq 3501 = (218673848836661:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 3501 = 218673848836661 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 3501 = (11501:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_3501
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 3502) ≤ val WuPaper.ClassicalFourthData.Bq 3502
    have hp : val WuPaper.ClassicalFourthData.Bq 3502 = (218701196501411:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 3502 = 218701196501411 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 3502 = (5751:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_3502
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 3503) ≤ val WuPaper.ClassicalFourthData.Bq 3503
    have hp : val WuPaper.ClassicalFourthData.Bq 3503 = (218728533232618:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 3503 = 218728533232618 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 3503 = (11503:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_3503
end WuPaper.ClassicalFourthConditions
#print axioms WuPaper.ClassicalFourthConditions.Log_block_218

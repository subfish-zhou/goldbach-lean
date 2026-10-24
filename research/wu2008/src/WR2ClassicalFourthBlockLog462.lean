import WR2ClassicalFourthConditions
import WR2ClassicalFourthLogPoints462
noncomputable section
namespace WuPaper.ClassicalFourthConditions
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem Log_block_462 (j : Fin 16) (hj : 16*462+j.val < 10541) :
    WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 (16*462+j.val)) ≤ val WuPaper.ClassicalFourthData.Bq (16*462+j.val) := by
  fin_cases j
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 7392) ≤ val WuPaper.ClassicalFourthData.Bq 7392
    have hp : val WuPaper.ClassicalFourthData.Bq 7392 = (271989863188772:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 7392 = 271989863188772 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 7392 = (481:ℝ)/125 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_7392
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 7393) ≤ val WuPaper.ClassicalFourthData.Bq 7393
    have hp : val WuPaper.ClassicalFourthData.Bq 7393 = (271995003078478:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 7393 = 271995003078478 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 7393 = (15393:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_7393
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 7394) ≤ val WuPaper.ClassicalFourthData.Bq 7394
    have hp : val WuPaper.ClassicalFourthData.Bq 7394 = (272000140298553:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 7394 = 272000140298553 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 7394 = (7697:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_7394
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 7395) ≤ val WuPaper.ClassicalFourthData.Bq 7395
    have hp : val WuPaper.ClassicalFourthData.Bq 7395 = (272005274849867:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 7395 = 272005274849867 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 7395 = (3079:ℝ)/800 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_7395
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 7396) ≤ val WuPaper.ClassicalFourthData.Bq 7396
    have hp : val WuPaper.ClassicalFourthData.Bq 7396 = (272010406733292:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 7396 = 272010406733292 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 7396 = (3849:ℝ)/1000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_7396
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 7397) ≤ val WuPaper.ClassicalFourthData.Bq 7397
    have hp : val WuPaper.ClassicalFourthData.Bq 7397 = (272015535949699:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 7397 = 272015535949699 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 7397 = (15397:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_7397
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 7398) ≤ val WuPaper.ClassicalFourthData.Bq 7398
    have hp : val WuPaper.ClassicalFourthData.Bq 7398 = (272020662499959:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 7398 = 272020662499959 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 7398 = (7699:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_7398
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 7399) ≤ val WuPaper.ClassicalFourthData.Bq 7399
    have hp : val WuPaper.ClassicalFourthData.Bq 7399 = (272025786384941:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 7399 = 272025786384941 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 7399 = (15399:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_7399
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 7400) ≤ val WuPaper.ClassicalFourthData.Bq 7400
    have hp : val WuPaper.ClassicalFourthData.Bq 7400 = (272030907605516:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 7400 = 272030907605516 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 7400 = (77:ℝ)/20 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_7400
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 7401) ≤ val WuPaper.ClassicalFourthData.Bq 7401
    have hp : val WuPaper.ClassicalFourthData.Bq 7401 = (272036026162553:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 7401 = 272036026162553 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 7401 = (15401:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_7401
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 7402) ≤ val WuPaper.ClassicalFourthData.Bq 7402
    have hp : val WuPaper.ClassicalFourthData.Bq 7402 = (272041142056922:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 7402 = 272041142056922 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 7402 = (7701:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_7402
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 7403) ≤ val WuPaper.ClassicalFourthData.Bq 7403
    have hp : val WuPaper.ClassicalFourthData.Bq 7403 = (272046255289492:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 7403 = 272046255289492 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 7403 = (15403:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_7403
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 7404) ≤ val WuPaper.ClassicalFourthData.Bq 7404
    have hp : val WuPaper.ClassicalFourthData.Bq 7404 = (272051365861132:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 7404 = 272051365861132 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 7404 = (3851:ℝ)/1000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_7404
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 7405) ≤ val WuPaper.ClassicalFourthData.Bq 7405
    have hp : val WuPaper.ClassicalFourthData.Bq 7405 = (272056473772709:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 7405 = 272056473772709 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 7405 = (3081:ℝ)/800 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_7405
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 7406) ≤ val WuPaper.ClassicalFourthData.Bq 7406
    have hp : val WuPaper.ClassicalFourthData.Bq 7406 = (272061579025092:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 7406 = 272061579025092 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 7406 = (7703:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_7406
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 7407) ≤ val WuPaper.ClassicalFourthData.Bq 7407
    have hp : val WuPaper.ClassicalFourthData.Bq 7407 = (272066681619149:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 7407 = 272066681619149 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 7407 = (15407:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_7407
end WuPaper.ClassicalFourthConditions
#print axioms WuPaper.ClassicalFourthConditions.Log_block_462

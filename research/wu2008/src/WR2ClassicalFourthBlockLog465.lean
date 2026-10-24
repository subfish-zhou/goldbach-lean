import WR2ClassicalFourthConditions
import WR2ClassicalFourthLogPoints465
noncomputable section
namespace WuPaper.ClassicalFourthConditions
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem Log_block_465 (j : Fin 16) (hj : 16*465+j.val < 10541) :
    WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 (16*465+j.val)) ≤ val WuPaper.ClassicalFourthData.Bq (16*465+j.val) := by
  fin_cases j
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 7440) ≤ val WuPaper.ClassicalFourthData.Bq 7440
    have hp : val WuPaper.ClassicalFourthData.Bq 7440 = (272233581562825:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 7440 = 272233581562825 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 7440 = (193:ℝ)/50 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_7440
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 7441) ≤ val WuPaper.ClassicalFourthData.Bq 7441
    have hp : val WuPaper.ClassicalFourthData.Bq 7441 = (272238594287847:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 7441 = 272238594287847 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 7441 = (15441:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_7441
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 7442) ≤ val WuPaper.ClassicalFourthData.Bq 7442
    have hp : val WuPaper.ClassicalFourthData.Bq 7442 = (272243604384715:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 7442 = 272243604384715 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 7442 = (7721:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_7442
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 7443) ≤ val WuPaper.ClassicalFourthData.Bq 7443
    have hp : val WuPaper.ClassicalFourthData.Bq 7443 = (272248611854286:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 7443 = 272248611854286 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 7443 = (15443:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_7443
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 7444) ≤ val WuPaper.ClassicalFourthData.Bq 7444
    have hp : val WuPaper.ClassicalFourthData.Bq 7444 = (272253616697416:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 7444 = 272253616697416 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 7444 = (3861:ℝ)/1000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_7444
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 7445) ≤ val WuPaper.ClassicalFourthData.Bq 7445
    have hp : val WuPaper.ClassicalFourthData.Bq 7445 = (272258618914960:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 7445 = 272258618914960 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 7445 = (3089:ℝ)/800 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_7445
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 7446) ≤ val WuPaper.ClassicalFourthData.Bq 7446
    have hp : val WuPaper.ClassicalFourthData.Bq 7446 = (272263618507775:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 7446 = 272263618507775 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 7446 = (7723:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_7446
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 7447) ≤ val WuPaper.ClassicalFourthData.Bq 7447
    have hp : val WuPaper.ClassicalFourthData.Bq 7447 = (272268615476715:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 7447 = 272268615476715 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 7447 = (15447:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_7447
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 7448) ≤ val WuPaper.ClassicalFourthData.Bq 7448
    have hp : val WuPaper.ClassicalFourthData.Bq 7448 = (272273609822635:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 7448 = 272273609822635 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 7448 = (1931:ℝ)/500 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_7448
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 7449) ≤ val WuPaper.ClassicalFourthData.Bq 7449
    have hp : val WuPaper.ClassicalFourthData.Bq 7449 = (272278601546390:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 7449 = 272278601546390 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 7449 = (15449:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_7449
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 7450) ≤ val WuPaper.ClassicalFourthData.Bq 7450
    have hp : val WuPaper.ClassicalFourthData.Bq 7450 = (272283590648833:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 7450 = 272283590648833 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 7450 = (309:ℝ)/80 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_7450
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 7451) ≤ val WuPaper.ClassicalFourthData.Bq 7451
    have hp : val WuPaper.ClassicalFourthData.Bq 7451 = (272288577130820:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 7451 = 272288577130820 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 7451 = (15451:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_7451
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 7452) ≤ val WuPaper.ClassicalFourthData.Bq 7452
    have hp : val WuPaper.ClassicalFourthData.Bq 7452 = (272293560993203:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 7452 = 272293560993203 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 7452 = (3863:ℝ)/1000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_7452
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 7453) ≤ val WuPaper.ClassicalFourthData.Bq 7453
    have hp : val WuPaper.ClassicalFourthData.Bq 7453 = (272298542236835:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 7453 = 272298542236835 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 7453 = (15453:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_7453
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 7454) ≤ val WuPaper.ClassicalFourthData.Bq 7454
    have hp : val WuPaper.ClassicalFourthData.Bq 7454 = (272303520862571:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 7454 = 272303520862571 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 7454 = (7727:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_7454
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 7455) ≤ val WuPaper.ClassicalFourthData.Bq 7455
    have hp : val WuPaper.ClassicalFourthData.Bq 7455 = (272308496871262:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 7455 = 272308496871262 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 7455 = (3091:ℝ)/800 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_7455
end WuPaper.ClassicalFourthConditions
#print axioms WuPaper.ClassicalFourthConditions.Log_block_465

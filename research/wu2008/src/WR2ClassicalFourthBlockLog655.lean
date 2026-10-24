import WR2ClassicalFourthConditions
import WR2ClassicalFourthLogPoints655
noncomputable section
namespace WuPaper.ClassicalFourthConditions
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem Log_block_655 (j : Fin 16) (hj : 16*655+j.val < 10541) :
    WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 (16*655+j.val)) ≤ val WuPaper.ClassicalFourthData.Bq (16*655+j.val) := by
  fin_cases j
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 10480) ≤ val WuPaper.ClassicalFourthData.Bq 10480
    have hp : val WuPaper.ClassicalFourthData.Bq 10480 = (278457581392704:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 10480 = 278457581392704 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 10480 = (231:ℝ)/50 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_10480
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 10481) ≤ val WuPaper.ClassicalFourthData.Bq 10481
    have hp : val WuPaper.ClassicalFourthData.Bq 10481 = (278457461051562:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 10481 = 278457461051562 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 10481 = (18481:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_10481
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 10482) ≤ val WuPaper.ClassicalFourthData.Bq 10482
    have hp : val WuPaper.ClassicalFourthData.Bq 10482 = (278457339691360:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 10482 = 278457339691360 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 10482 = (9241:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_10482
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 10483) ≤ val WuPaper.ClassicalFourthData.Bq 10483
    have hp : val WuPaper.ClassicalFourthData.Bq 10483 = (278457217312408:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 10483 = 278457217312408 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 10483 = (18483:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_10483
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 10484) ≤ val WuPaper.ClassicalFourthData.Bq 10484
    have hp : val WuPaper.ClassicalFourthData.Bq 10484 = (278457093915012:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 10484 = 278457093915012 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 10484 = (4621:ℝ)/1000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_10484
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 10485) ≤ val WuPaper.ClassicalFourthData.Bq 10485
    have hp : val WuPaper.ClassicalFourthData.Bq 10485 = (278456969499482:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 10485 = 278456969499482 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 10485 = (3697:ℝ)/800 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_10485
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 10486) ≤ val WuPaper.ClassicalFourthData.Bq 10486
    have hp : val WuPaper.ClassicalFourthData.Bq 10486 = (278456844066124:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 10486 = 278456844066124 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 10486 = (9243:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_10486
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 10487) ≤ val WuPaper.ClassicalFourthData.Bq 10487
    have hp : val WuPaper.ClassicalFourthData.Bq 10487 = (278456717615246:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 10487 = 278456717615246 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 10487 = (18487:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_10487
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 10488) ≤ val WuPaper.ClassicalFourthData.Bq 10488
    have hp : val WuPaper.ClassicalFourthData.Bq 10488 = (278456590147155:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 10488 = 278456590147155 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 10488 = (2311:ℝ)/500 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_10488
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 10489) ≤ val WuPaper.ClassicalFourthData.Bq 10489
    have hp : val WuPaper.ClassicalFourthData.Bq 10489 = (278456461662159:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 10489 = 278456461662159 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 10489 = (18489:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_10489
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 10490) ≤ val WuPaper.ClassicalFourthData.Bq 10490
    have hp : val WuPaper.ClassicalFourthData.Bq 10490 = (278456332160565:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 10490 = 278456332160565 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 10490 = (1849:ℝ)/400 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_10490
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 10491) ≤ val WuPaper.ClassicalFourthData.Bq 10491
    have hp : val WuPaper.ClassicalFourthData.Bq 10491 = (278456201642680:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 10491 = 278456201642680 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 10491 = (18491:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_10491
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 10492) ≤ val WuPaper.ClassicalFourthData.Bq 10492
    have hp : val WuPaper.ClassicalFourthData.Bq 10492 = (278456070108811:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 10492 = 278456070108811 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 10492 = (4623:ℝ)/1000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_10492
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 10493) ≤ val WuPaper.ClassicalFourthData.Bq 10493
    have hp : val WuPaper.ClassicalFourthData.Bq 10493 = (278455937559266:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 10493 = 278455937559266 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 10493 = (18493:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_10493
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 10494) ≤ val WuPaper.ClassicalFourthData.Bq 10494
    have hp : val WuPaper.ClassicalFourthData.Bq 10494 = (278455803994350:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 10494 = 278455803994350 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 10494 = (9247:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_10494
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 10495) ≤ val WuPaper.ClassicalFourthData.Bq 10495
    have hp : val WuPaper.ClassicalFourthData.Bq 10495 = (278455669414372:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 10495 = 278455669414372 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 10495 = (3699:ℝ)/800 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_10495
end WuPaper.ClassicalFourthConditions
#print axioms WuPaper.ClassicalFourthConditions.Log_block_655

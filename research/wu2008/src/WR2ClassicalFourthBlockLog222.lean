import WR2ClassicalFourthConditions
import WR2ClassicalFourthLogPoints222
noncomputable section
namespace WuPaper.ClassicalFourthConditions
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem Log_block_222 (j : Fin 16) (hj : 16*222+j.val < 10541) :
    WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 (16*222+j.val)) ≤ val WuPaper.ClassicalFourthData.Bq (16*222+j.val) := by
  fin_cases j
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 3552) ≤ val WuPaper.ClassicalFourthData.Bq 3552
    have hp : val WuPaper.ClassicalFourthData.Bq 3552 = (220054732591174:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 3552 = 220054732591174 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 3552 = (361:ℝ)/125 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_3552
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 3553) ≤ val WuPaper.ClassicalFourthData.Bq 3553
    have hp : val WuPaper.ClassicalFourthData.Bq 3553 = (220081528334258:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 3553 = 220081528334258 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 3553 = (11553:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_3553
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 3554) ≤ val WuPaper.ClassicalFourthData.Bq 3554
    have hp : val WuPaper.ClassicalFourthData.Bq 3554 = (220108313370392:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 3554 = 220108313370392 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 3554 = (5777:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_3554
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 3555) ≤ val WuPaper.ClassicalFourthData.Bq 3555
    have hp : val WuPaper.ClassicalFourthData.Bq 3555 = (220135087703960:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 3555 = 220135087703960 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 3555 = (2311:ℝ)/800 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_3555
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 3556) ≤ val WuPaper.ClassicalFourthData.Bq 3556
    have hp : val WuPaper.ClassicalFourthData.Bq 3556 = (220161851339347:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 3556 = 220161851339347 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 3556 = (2889:ℝ)/1000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_3556
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 3557) ≤ val WuPaper.ClassicalFourthData.Bq 3557
    have hp : val WuPaper.ClassicalFourthData.Bq 3557 = (220188604280936:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 3557 = 220188604280936 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 3557 = (11557:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_3557
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 3558) ≤ val WuPaper.ClassicalFourthData.Bq 3558
    have hp : val WuPaper.ClassicalFourthData.Bq 3558 = (220215346533105:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 3558 = 220215346533105 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 3558 = (5779:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_3558
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 3559) ≤ val WuPaper.ClassicalFourthData.Bq 3559
    have hp : val WuPaper.ClassicalFourthData.Bq 3559 = (220242078100234:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 3559 = 220242078100234 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 3559 = (11559:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_3559
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 3560) ≤ val WuPaper.ClassicalFourthData.Bq 3560
    have hp : val WuPaper.ClassicalFourthData.Bq 3560 = (220268798986696:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 3560 = 220268798986696 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 3560 = (289:ℝ)/100 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_3560
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 3561) ≤ val WuPaper.ClassicalFourthData.Bq 3561
    have hp : val WuPaper.ClassicalFourthData.Bq 3561 = (220295509196867:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 3561 = 220295509196867 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 3561 = (11561:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_3561
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 3562) ≤ val WuPaper.ClassicalFourthData.Bq 3562
    have hp : val WuPaper.ClassicalFourthData.Bq 3562 = (220322208735116:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 3562 = 220322208735116 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 3562 = (5781:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_3562
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 3563) ≤ val WuPaper.ClassicalFourthData.Bq 3563
    have hp : val WuPaper.ClassicalFourthData.Bq 3563 = (220348897605813:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 3563 = 220348897605813 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 3563 = (11563:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_3563
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 3564) ≤ val WuPaper.ClassicalFourthData.Bq 3564
    have hp : val WuPaper.ClassicalFourthData.Bq 3564 = (220375575813325:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 3564 = 220375575813325 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 3564 = (2891:ℝ)/1000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_3564
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 3565) ≤ val WuPaper.ClassicalFourthData.Bq 3565
    have hp : val WuPaper.ClassicalFourthData.Bq 3565 = (220402243362016:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 3565 = 220402243362016 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 3565 = (2313:ℝ)/800 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_3565
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 3566) ≤ val WuPaper.ClassicalFourthData.Bq 3566
    have hp : val WuPaper.ClassicalFourthData.Bq 3566 = (220428900256251:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 3566 = 220428900256251 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 3566 = (5783:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_3566
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 3567) ≤ val WuPaper.ClassicalFourthData.Bq 3567
    have hp : val WuPaper.ClassicalFourthData.Bq 3567 = (220455546500387:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 3567 = 220455546500387 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 3567 = (11567:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_3567
end WuPaper.ClassicalFourthConditions
#print axioms WuPaper.ClassicalFourthConditions.Log_block_222

import WR2ClassicalFourthConditions
import WR2ClassicalFourthLogPoints281
noncomputable section
namespace WuPaper.ClassicalFourthConditions
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem Log_block_281 (j : Fin 16) (hj : 16*281+j.val < 10541) :
    WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 (16*281+j.val)) ≤ val WuPaper.ClassicalFourthData.Bq (16*281+j.val) := by
  fin_cases j
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 4496) ≤ val WuPaper.ClassicalFourthData.Bq 4496
    have hp : val WuPaper.ClassicalFourthData.Bq 4496 = (241133515806560:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 4496 = 241133515806560 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 4496 = (781:ℝ)/250 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_4496
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 4497) ≤ val WuPaper.ClassicalFourthData.Bq 4497
    have hp : val WuPaper.ClassicalFourthData.Bq 4497 = (241151892102590:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 4497 = 241151892102590 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 4497 = (12497:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_4497
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 4498) ≤ val WuPaper.ClassicalFourthData.Bq 4498
    have hp : val WuPaper.ClassicalFourthData.Bq 4498 = (241170261025038:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 4498 = 241170261025038 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 4498 = (6249:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_4498
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 4499) ≤ val WuPaper.ClassicalFourthData.Bq 4499
    have hp : val WuPaper.ClassicalFourthData.Bq 4499 = (241188622576718:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 4499 = 241188622576718 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 4499 = (12499:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_4499
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 4500) ≤ val WuPaper.ClassicalFourthData.Bq 4500
    have hp : val WuPaper.ClassicalFourthData.Bq 4500 = (241206976760442:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 4500 = 241206976760442 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 4500 = (25:ℝ)/8 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_4500
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 4501) ≤ val WuPaper.ClassicalFourthData.Bq 4501
    have hp : val WuPaper.ClassicalFourthData.Bq 4501 = (241225323579020:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 4501 = 241225323579020 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 4501 = (12501:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_4501
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 4502) ≤ val WuPaper.ClassicalFourthData.Bq 4502
    have hp : val WuPaper.ClassicalFourthData.Bq 4502 = (241243663035261:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 4502 = 241243663035261 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 4502 = (6251:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_4502
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 4503) ≤ val WuPaper.ClassicalFourthData.Bq 4503
    have hp : val WuPaper.ClassicalFourthData.Bq 4503 = (241261995131974:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 4503 = 241261995131974 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 4503 = (12503:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_4503
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 4504) ≤ val WuPaper.ClassicalFourthData.Bq 4504
    have hp : val WuPaper.ClassicalFourthData.Bq 4504 = (241280319871963:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 4504 = 241280319871963 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 4504 = (1563:ℝ)/500 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_4504
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 4505) ≤ val WuPaper.ClassicalFourthData.Bq 4505
    have hp : val WuPaper.ClassicalFourthData.Bq 4505 = (241298637258036:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 4505 = 241298637258036 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 4505 = (2501:ℝ)/800 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_4505
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 4506) ≤ val WuPaper.ClassicalFourthData.Bq 4506
    have hp : val WuPaper.ClassicalFourthData.Bq 4506 = (241316947292996:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 4506 = 241316947292996 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 4506 = (6253:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_4506
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 4507) ≤ val WuPaper.ClassicalFourthData.Bq 4507
    have hp : val WuPaper.ClassicalFourthData.Bq 4507 = (241335249979646:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 4507 = 241335249979646 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 4507 = (12507:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_4507
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 4508) ≤ val WuPaper.ClassicalFourthData.Bq 4508
    have hp : val WuPaper.ClassicalFourthData.Bq 4508 = (241353545320787:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 4508 = 241353545320787 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 4508 = (3127:ℝ)/1000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_4508
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 4509) ≤ val WuPaper.ClassicalFourthData.Bq 4509
    have hp : val WuPaper.ClassicalFourthData.Bq 4509 = (241371833319220:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 4509 = 241371833319220 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 4509 = (12509:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_4509
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 4510) ≤ val WuPaper.ClassicalFourthData.Bq 4510
    have hp : val WuPaper.ClassicalFourthData.Bq 4510 = (241390113977744:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 4510 = 241390113977744 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 4510 = (1251:ℝ)/400 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_4510
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 4511) ≤ val WuPaper.ClassicalFourthData.Bq 4511
    have hp : val WuPaper.ClassicalFourthData.Bq 4511 = (241408387299156:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 4511 = 241408387299156 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 4511 = (12511:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_4511
end WuPaper.ClassicalFourthConditions
#print axioms WuPaper.ClassicalFourthConditions.Log_block_281

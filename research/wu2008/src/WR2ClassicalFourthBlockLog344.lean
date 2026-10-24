import WR2ClassicalFourthConditions
import WR2ClassicalFourthLogPoints344
noncomputable section
namespace WuPaper.ClassicalFourthConditions
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem Log_block_344 (j : Fin 16) (hj : 16*344+j.val < 10541) :
    WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 (16*344+j.val)) ≤ val WuPaper.ClassicalFourthData.Bq (16*344+j.val) := by
  fin_cases j
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 5504) ≤ val WuPaper.ClassicalFourthData.Bq 5504
    have hp : val WuPaper.ClassicalFourthData.Bq 5504 = (256344313240641:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 5504 = 256344313240641 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 5504 = (422:ℝ)/125 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_5504
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 5505) ≤ val WuPaper.ClassicalFourthData.Bq 5505
    have hp : val WuPaper.ClassicalFourthData.Bq 5505 = (256356494578454:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 5505 = 256356494578454 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 5505 = (2701:ℝ)/800 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_5505
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 5506) ≤ val WuPaper.ClassicalFourthData.Bq 5506
    have hp : val WuPaper.ClassicalFourthData.Bq 5506 = (256368670834276:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 5506 = 256368670834276 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 5506 = (6753:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_5506
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 5507) ≤ val WuPaper.ClassicalFourthData.Bq 5507
    have hp : val WuPaper.ClassicalFourthData.Bq 5507 = (256380842009923:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 5507 = 256380842009923 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 5507 = (13507:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_5507
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 5508) ≤ val WuPaper.ClassicalFourthData.Bq 5508
    have hp : val WuPaper.ClassicalFourthData.Bq 5508 = (256393008107214:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 5508 = 256393008107214 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 5508 = (3377:ℝ)/1000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_5508
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 5509) ≤ val WuPaper.ClassicalFourthData.Bq 5509
    have hp : val WuPaper.ClassicalFourthData.Bq 5509 = (256405169127966:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 5509 = 256405169127966 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 5509 = (13509:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_5509
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 5510) ≤ val WuPaper.ClassicalFourthData.Bq 5510
    have hp : val WuPaper.ClassicalFourthData.Bq 5510 = (256417325073994:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 5510 = 256417325073994 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 5510 = (1351:ℝ)/400 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_5510
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 5511) ≤ val WuPaper.ClassicalFourthData.Bq 5511
    have hp : val WuPaper.ClassicalFourthData.Bq 5511 = (256429475947114:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 5511 = 256429475947114 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 5511 = (13511:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_5511
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 5512) ≤ val WuPaper.ClassicalFourthData.Bq 5512
    have hp : val WuPaper.ClassicalFourthData.Bq 5512 = (256441621749140:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 5512 = 256441621749140 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 5512 = (1689:ℝ)/500 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_5512
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 5513) ≤ val WuPaper.ClassicalFourthData.Bq 5513
    have hp : val WuPaper.ClassicalFourthData.Bq 5513 = (256453762481887:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 5513 = 256453762481887 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 5513 = (13513:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_5513
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 5514) ≤ val WuPaper.ClassicalFourthData.Bq 5514
    have hp : val WuPaper.ClassicalFourthData.Bq 5514 = (256465898147167:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 5514 = 256465898147167 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 5514 = (6757:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_5514
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 5515) ≤ val WuPaper.ClassicalFourthData.Bq 5515
    have hp : val WuPaper.ClassicalFourthData.Bq 5515 = (256478028746793:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 5515 = 256478028746793 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 5515 = (2703:ℝ)/800 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_5515
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 5516) ≤ val WuPaper.ClassicalFourthData.Bq 5516
    have hp : val WuPaper.ClassicalFourthData.Bq 5516 = (256490154282576:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 5516 = 256490154282576 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 5516 = (3379:ℝ)/1000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_5516
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 5517) ≤ val WuPaper.ClassicalFourthData.Bq 5517
    have hp : val WuPaper.ClassicalFourthData.Bq 5517 = (256502274756328:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 5517 = 256502274756328 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 5517 = (13517:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_5517
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 5518) ≤ val WuPaper.ClassicalFourthData.Bq 5518
    have hp : val WuPaper.ClassicalFourthData.Bq 5518 = (256514390169857:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 5518 = 256514390169857 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 5518 = (6759:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_5518
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 5519) ≤ val WuPaper.ClassicalFourthData.Bq 5519
    have hp : val WuPaper.ClassicalFourthData.Bq 5519 = (256526500524975:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 5519 = 256526500524975 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 5519 = (13519:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_5519
end WuPaper.ClassicalFourthConditions
#print axioms WuPaper.ClassicalFourthConditions.Log_block_344

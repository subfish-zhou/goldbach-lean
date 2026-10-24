import WR2ClassicalFourthConditions
import WR2ClassicalFourthLogPoints031
noncomputable section
namespace WuPaper.ClassicalFourthConditions
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem Log_block_031 (j : Fin 16) (hj : 16*31+j.val < 10541) :
    WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 (16*31+j.val)) ≤ val WuPaper.ClassicalFourthData.Bq (16*31+j.val) := by
  fin_cases j
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 496) ≤ val WuPaper.ClassicalFourthData.Bq 496
    have hp : val WuPaper.ClassicalFourthData.Bq 496 = (55034722915019:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 496 = 55034722915019 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 496 = (531:ℝ)/250 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_496
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 497) ≤ val WuPaper.ClassicalFourthData.Bq 497
    have hp : val WuPaper.ClassicalFourthData.Bq 497 = (55132939469780:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 497 = 55132939469780 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 497 = (8497:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_497
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 498) ≤ val WuPaper.ClassicalFourthData.Bq 498
    have hp : val WuPaper.ClassicalFourthData.Bq 498 = (55231109633907:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 498 = 55231109633907 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 498 = (4249:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_498
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 499) ≤ val WuPaper.ClassicalFourthData.Bq 499
    have hp : val WuPaper.ClassicalFourthData.Bq 499 = (55329233434120:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 499 = 55329233434120 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 499 = (8499:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_499
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 500) ≤ val WuPaper.ClassicalFourthData.Bq 500
    have hp : val WuPaper.ClassicalFourthData.Bq 500 = (55427310897122:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 500 = 55427310897122 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 500 = (17:ℝ)/8 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_500
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 501) ≤ val WuPaper.ClassicalFourthData.Bq 501
    have hp : val WuPaper.ClassicalFourthData.Bq 501 = (55525342049597:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 501 = 55525342049597 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 501 = (8501:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_501
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 502) ≤ val WuPaper.ClassicalFourthData.Bq 502
    have hp : val WuPaper.ClassicalFourthData.Bq 502 = (55623326918208:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 502 = 55623326918208 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 502 = (4251:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_502
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 503) ≤ val WuPaper.ClassicalFourthData.Bq 503
    have hp : val WuPaper.ClassicalFourthData.Bq 503 = (55721265529599:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 503 = 55721265529599 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 503 = (8503:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_503
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 504) ≤ val WuPaper.ClassicalFourthData.Bq 504
    have hp : val WuPaper.ClassicalFourthData.Bq 504 = (55819157910395:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 504 = 55819157910395 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 504 = (1063:ℝ)/500 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_504
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 505) ≤ val WuPaper.ClassicalFourthData.Bq 505
    have hp : val WuPaper.ClassicalFourthData.Bq 505 = (55917004087201:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 505 = 55917004087201 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 505 = (1701:ℝ)/800 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_505
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 506) ≤ val WuPaper.ClassicalFourthData.Bq 506
    have hp : val WuPaper.ClassicalFourthData.Bq 506 = (56014804086604:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 506 = 56014804086604 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 506 = (4253:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_506
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 507) ≤ val WuPaper.ClassicalFourthData.Bq 507
    have hp : val WuPaper.ClassicalFourthData.Bq 507 = (56112557935169:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 507 = 56112557935169 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 507 = (8507:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_507
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 508) ≤ val WuPaper.ClassicalFourthData.Bq 508
    have hp : val WuPaper.ClassicalFourthData.Bq 508 = (56210265659445:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 508 = 56210265659445 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 508 = (2127:ℝ)/1000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_508
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 509) ≤ val WuPaper.ClassicalFourthData.Bq 509
    have hp : val WuPaper.ClassicalFourthData.Bq 509 = (56307927285960:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 509 = 56307927285960 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 509 = (8509:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_509
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 510) ≤ val WuPaper.ClassicalFourthData.Bq 510
    have hp : val WuPaper.ClassicalFourthData.Bq 510 = (56405542841221:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 510 = 56405542841221 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 510 = (851:ℝ)/400 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_510
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 511) ≤ val WuPaper.ClassicalFourthData.Bq 511
    have hp : val WuPaper.ClassicalFourthData.Bq 511 = (56503112351719:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 511 = 56503112351719 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 511 = (8511:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_511
end WuPaper.ClassicalFourthConditions
#print axioms WuPaper.ClassicalFourthConditions.Log_block_031

import WR2ClassicalFourthConditions
import WR2ClassicalFourthLogPoints298
noncomputable section
namespace WuPaper.ClassicalFourthConditions
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem Log_block_298 (j : Fin 16) (hj : 16*298+j.val < 10541) :
    WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 (16*298+j.val)) ≤ val WuPaper.ClassicalFourthData.Bq (16*298+j.val) := by
  fin_cases j
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 4768) ≤ val WuPaper.ClassicalFourthData.Bq 4768
    have hp : val WuPaper.ClassicalFourthData.Bq 4768 = (245869163247422:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 4768 = 245869163247422 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 4768 = (399:ℝ)/125 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_4768
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 4769) ≤ val WuPaper.ClassicalFourthData.Bq 4769
    have hp : val WuPaper.ClassicalFourthData.Bq 4769 = (245885633542902:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 4769 = 245885633542902 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 4769 = (12769:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_4769
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 4770) ≤ val WuPaper.ClassicalFourthData.Bq 4770
    have hp : val WuPaper.ClassicalFourthData.Bq 4770 = (245902097185342:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 4770 = 245902097185342 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 4770 = (1277:ℝ)/400 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_4770
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 4771) ≤ val WuPaper.ClassicalFourthData.Bq 4771
    have hp : val WuPaper.ClassicalFourthData.Bq 4771 = (245918554177231:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 4771 = 245918554177231 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 4771 = (12771:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_4771
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 4772) ≤ val WuPaper.ClassicalFourthData.Bq 4772
    have hp : val WuPaper.ClassicalFourthData.Bq 4772 = (245935004521063:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 4772 = 245935004521063 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 4772 = (3193:ℝ)/1000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_4772
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 4773) ≤ val WuPaper.ClassicalFourthData.Bq 4773
    have hp : val WuPaper.ClassicalFourthData.Bq 4773 = (245951448219325:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 4773 = 245951448219325 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 4773 = (12773:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_4773
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 4774) ≤ val WuPaper.ClassicalFourthData.Bq 4774
    have hp : val WuPaper.ClassicalFourthData.Bq 4774 = (245967885274506:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 4774 = 245967885274506 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 4774 = (6387:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_4774
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 4775) ≤ val WuPaper.ClassicalFourthData.Bq 4775
    have hp : val WuPaper.ClassicalFourthData.Bq 4775 = (245984315689093:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 4775 = 245984315689093 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 4775 = (511:ℝ)/160 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_4775
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 4776) ≤ val WuPaper.ClassicalFourthData.Bq 4776
    have hp : val WuPaper.ClassicalFourthData.Bq 4776 = (246000739465573:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 4776 = 246000739465573 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 4776 = (1597:ℝ)/500 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_4776
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 4777) ≤ val WuPaper.ClassicalFourthData.Bq 4777
    have hp : val WuPaper.ClassicalFourthData.Bq 4777 = (246017156606431:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 4777 = 246017156606431 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 4777 = (12777:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_4777
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 4778) ≤ val WuPaper.ClassicalFourthData.Bq 4778
    have hp : val WuPaper.ClassicalFourthData.Bq 4778 = (246033567114150:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 4778 = 246033567114150 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 4778 = (6389:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_4778
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 4779) ≤ val WuPaper.ClassicalFourthData.Bq 4779
    have hp : val WuPaper.ClassicalFourthData.Bq 4779 = (246049970991215:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 4779 = 246049970991215 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 4779 = (12779:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_4779
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 4780) ≤ val WuPaper.ClassicalFourthData.Bq 4780
    have hp : val WuPaper.ClassicalFourthData.Bq 4780 = (246066368240105:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 4780 = 246066368240105 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 4780 = (639:ℝ)/200 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_4780
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 4781) ≤ val WuPaper.ClassicalFourthData.Bq 4781
    have hp : val WuPaper.ClassicalFourthData.Bq 4781 = (246082758863303:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 4781 = 246082758863303 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 4781 = (12781:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_4781
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 4782) ≤ val WuPaper.ClassicalFourthData.Bq 4782
    have hp : val WuPaper.ClassicalFourthData.Bq 4782 = (246099142863288:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 4782 = 246099142863288 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 4782 = (6391:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_4782
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 4783) ≤ val WuPaper.ClassicalFourthData.Bq 4783
    have hp : val WuPaper.ClassicalFourthData.Bq 4783 = (246115520242538:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 4783 = 246115520242538 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 4783 = (12783:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_4783
end WuPaper.ClassicalFourthConditions
#print axioms WuPaper.ClassicalFourthConditions.Log_block_298

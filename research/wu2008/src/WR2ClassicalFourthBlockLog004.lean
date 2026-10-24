import WR2ClassicalFourthConditions
import WR2ClassicalFourthLogPoints004
noncomputable section
namespace WuPaper.ClassicalFourthConditions
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem Log_block_004 (j : Fin 16) (hj : 16*4+j.val < 10541) :
    WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 (16*4+j.val)) ≤ val WuPaper.ClassicalFourthData.Bq (16*4+j.val) := by
  fin_cases j
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 64) ≤ val WuPaper.ClassicalFourthData.Bq 64
    have hp : val WuPaper.ClassicalFourthData.Bq 64 = (7873685097367:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 64 = 7873685097367 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 64 = (252:ℝ)/125 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_64
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 65) ≤ val WuPaper.ClassicalFourthData.Bq 65
    have hp : val WuPaper.ClassicalFourthData.Bq 65 = (7994733728399:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 65 = 7994733728399 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 65 = (1613:ℝ)/800 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_65
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 66) ≤ val WuPaper.ClassicalFourthData.Bq 66
    have hp : val WuPaper.ClassicalFourthData.Bq 66 = (8115722333878:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 66 = 8115722333878 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 66 = (4033:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_66
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 67) ≤ val WuPaper.ClassicalFourthData.Bq 67
    have hp : val WuPaper.ClassicalFourthData.Bq 67 = (8236650950885:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 67 = 8236650950885 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 67 = (8067:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_67
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 68) ≤ val WuPaper.ClassicalFourthData.Bq 68
    have hp : val WuPaper.ClassicalFourthData.Bq 68 = (8357519616472:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 68 = 8357519616472 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 68 = (2017:ℝ)/1000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_68
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 69) ≤ val WuPaper.ClassicalFourthData.Bq 69
    have hp : val WuPaper.ClassicalFourthData.Bq 69 = (8478328367661:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 69 = 8478328367661 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 69 = (8069:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_69
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 70) ≤ val WuPaper.ClassicalFourthData.Bq 70
    have hp : val WuPaper.ClassicalFourthData.Bq 70 = (8599077241444:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 70 = 8599077241444 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 70 = (807:ℝ)/400 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_70
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 71) ≤ val WuPaper.ClassicalFourthData.Bq 71
    have hp : val WuPaper.ClassicalFourthData.Bq 71 = (8719766274787:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 71 = 8719766274787 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 71 = (8071:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_71
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 72) ≤ val WuPaper.ClassicalFourthData.Bq 72
    have hp : val WuPaper.ClassicalFourthData.Bq 72 = (8840395504624:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 72 = 8840395504624 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 72 = (1009:ℝ)/500 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_72
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 73) ≤ val WuPaper.ClassicalFourthData.Bq 73
    have hp : val WuPaper.ClassicalFourthData.Bq 73 = (8960964967861:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 73 = 8960964967861 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 73 = (8073:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_73
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 74) ≤ val WuPaper.ClassicalFourthData.Bq 74
    have hp : val WuPaper.ClassicalFourthData.Bq 74 = (9081474701375:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 74 = 9081474701375 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 74 = (4037:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_74
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 75) ≤ val WuPaper.ClassicalFourthData.Bq 75
    have hp : val WuPaper.ClassicalFourthData.Bq 75 = (9201924742012:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 75 = 9201924742012 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 75 = (323:ℝ)/160 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_75
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 76) ≤ val WuPaper.ClassicalFourthData.Bq 76
    have hp : val WuPaper.ClassicalFourthData.Bq 76 = (9322315126592:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 76 = 9322315126592 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 76 = (2019:ℝ)/1000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_76
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 77) ≤ val WuPaper.ClassicalFourthData.Bq 77
    have hp : val WuPaper.ClassicalFourthData.Bq 77 = (9442645891904:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 77 = 9442645891904 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 77 = (8077:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_77
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 78) ≤ val WuPaper.ClassicalFourthData.Bq 78
    have hp : val WuPaper.ClassicalFourthData.Bq 78 = (9562917074709:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 78 = 9562917074709 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 78 = (4039:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_78
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 79) ≤ val WuPaper.ClassicalFourthData.Bq 79
    have hp : val WuPaper.ClassicalFourthData.Bq 79 = (9683128711737:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 79 = 9683128711737 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 79 = (8079:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_79
end WuPaper.ClassicalFourthConditions
#print axioms WuPaper.ClassicalFourthConditions.Log_block_004

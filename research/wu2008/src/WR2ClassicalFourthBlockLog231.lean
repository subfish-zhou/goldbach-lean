import WR2ClassicalFourthConditions
import WR2ClassicalFourthLogPoints231
noncomputable section
namespace WuPaper.ClassicalFourthConditions
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem Log_block_231 (j : Fin 16) (hj : 16*231+j.val < 10541) :
    WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 (16*231+j.val)) ≤ val WuPaper.ClassicalFourthData.Bq (16*231+j.val) := by
  fin_cases j
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 3696) ≤ val WuPaper.ClassicalFourthData.Bq 3696
    have hp : val WuPaper.ClassicalFourthData.Bq 3696 = (223805182025826:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 3696 = 223805182025826 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 3696 = (731:ℝ)/250 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_3696
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 3697) ≤ val WuPaper.ClassicalFourthData.Bq 3697
    have hp : val WuPaper.ClassicalFourthData.Bq 3697 = (223830480099954:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 3697 = 223830480099954 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 3697 = (11697:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_3697
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 3698) ≤ val WuPaper.ClassicalFourthData.Bq 3698
    have hp : val WuPaper.ClassicalFourthData.Bq 3698 = (223855768077164:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 3698 = 223855768077164 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 3698 = (5849:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_3698
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 3699) ≤ val WuPaper.ClassicalFourthData.Bq 3699
    have hp : val WuPaper.ClassicalFourthData.Bq 3699 = (223881045961543:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 3699 = 223881045961543 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 3699 = (11699:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_3699
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 3700) ≤ val WuPaper.ClassicalFourthData.Bq 3700
    have hp : val WuPaper.ClassicalFourthData.Bq 3700 = (223906313757179:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 3700 = 223906313757179 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 3700 = (117:ℝ)/40 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_3700
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 3701) ≤ val WuPaper.ClassicalFourthData.Bq 3701
    have hp : val WuPaper.ClassicalFourthData.Bq 3701 = (223931571468156:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 3701 = 223931571468156 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 3701 = (11701:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_3701
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 3702) ≤ val WuPaper.ClassicalFourthData.Bq 3702
    have hp : val WuPaper.ClassicalFourthData.Bq 3702 = (223956819098557:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 3702 = 223956819098557 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 3702 = (5851:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_3702
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 3703) ≤ val WuPaper.ClassicalFourthData.Bq 3703
    have hp : val WuPaper.ClassicalFourthData.Bq 3703 = (223982056652462:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 3703 = 223982056652462 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 3703 = (11703:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_3703
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 3704) ≤ val WuPaper.ClassicalFourthData.Bq 3704
    have hp : val WuPaper.ClassicalFourthData.Bq 3704 = (224007284133949:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 3704 = 224007284133949 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 3704 = (1463:ℝ)/500 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_3704
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 3705) ≤ val WuPaper.ClassicalFourthData.Bq 3705
    have hp : val WuPaper.ClassicalFourthData.Bq 3705 = (224032501547096:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 3705 = 224032501547096 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 3705 = (2341:ℝ)/800 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_3705
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 3706) ≤ val WuPaper.ClassicalFourthData.Bq 3706
    have hp : val WuPaper.ClassicalFourthData.Bq 3706 = (224057708895977:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 3706 = 224057708895977 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 3706 = (5853:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_3706
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 3707) ≤ val WuPaper.ClassicalFourthData.Bq 3707
    have hp : val WuPaper.ClassicalFourthData.Bq 3707 = (224082906184665:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 3707 = 224082906184665 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 3707 = (11707:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_3707
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 3708) ≤ val WuPaper.ClassicalFourthData.Bq 3708
    have hp : val WuPaper.ClassicalFourthData.Bq 3708 = (224108093417230:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 3708 = 224108093417230 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 3708 = (2927:ℝ)/1000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_3708
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 3709) ≤ val WuPaper.ClassicalFourthData.Bq 3709
    have hp : val WuPaper.ClassicalFourthData.Bq 3709 = (224133270597741:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 3709 = 224133270597741 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 3709 = (11709:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_3709
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 3710) ≤ val WuPaper.ClassicalFourthData.Bq 3710
    have hp : val WuPaper.ClassicalFourthData.Bq 3710 = (224158437730264:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 3710 = 224158437730264 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 3710 = (1171:ℝ)/400 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_3710
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 3711) ≤ val WuPaper.ClassicalFourthData.Bq 3711
    have hp : val WuPaper.ClassicalFourthData.Bq 3711 = (224183594818866:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 3711 = 224183594818866 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 3711 = (11711:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_3711
end WuPaper.ClassicalFourthConditions
#print axioms WuPaper.ClassicalFourthConditions.Log_block_231

import WR2ClassicalFourthConditions
import WR2ClassicalFourthLogPoints235
noncomputable section
namespace WuPaper.ClassicalFourthConditions
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem Log_block_235 (j : Fin 16) (hj : 16*235+j.val < 10541) :
    WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 (16*235+j.val)) ≤ val WuPaper.ClassicalFourthData.Bq (16*235+j.val) := by
  fin_cases j
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 3760) ≤ val WuPaper.ClassicalFourthData.Bq 3760
    have hp : val WuPaper.ClassicalFourthData.Bq 3760 = (225404072474571:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 3760 = 225404072474571 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 3760 = (147:ℝ)/50 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_3760
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 3761) ≤ val WuPaper.ClassicalFourthData.Bq 3761
    have hp : val WuPaper.ClassicalFourthData.Bq 3761 = (225428732506458:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 3761 = 225428732506458 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 3761 = (11761:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_3761
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 3762) ≤ val WuPaper.ClassicalFourthData.Bq 3762
    have hp : val WuPaper.ClassicalFourthData.Bq 3762 = (225453382699141:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 3762 = 225453382699141 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 3762 = (5881:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_3762
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 3763) ≤ val WuPaper.ClassicalFourthData.Bq 3763
    have hp : val WuPaper.ClassicalFourthData.Bq 3763 = (225478023056586:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 3763 = 225478023056586 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 3763 = (11763:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_3763
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 3764) ≤ val WuPaper.ClassicalFourthData.Bq 3764
    have hp : val WuPaper.ClassicalFourthData.Bq 3764 = (225502653582752:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 3764 = 225502653582752 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 3764 = (2941:ℝ)/1000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_3764
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 3765) ≤ val WuPaper.ClassicalFourthData.Bq 3765
    have hp : val WuPaper.ClassicalFourthData.Bq 3765 = (225527274281602:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 3765 = 225527274281602 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 3765 = (2353:ℝ)/800 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_3765
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 3766) ≤ val WuPaper.ClassicalFourthData.Bq 3766
    have hp : val WuPaper.ClassicalFourthData.Bq 3766 = (225551885157092:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 3766 = 225551885157092 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 3766 = (5883:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_3766
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 3767) ≤ val WuPaper.ClassicalFourthData.Bq 3767
    have hp : val WuPaper.ClassicalFourthData.Bq 3767 = (225576486213180:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 3767 = 225576486213180 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 3767 = (11767:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_3767
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 3768) ≤ val WuPaper.ClassicalFourthData.Bq 3768
    have hp : val WuPaper.ClassicalFourthData.Bq 3768 = (225601077453819:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 3768 = 225601077453819 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 3768 = (1471:ℝ)/500 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_3768
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 3769) ≤ val WuPaper.ClassicalFourthData.Bq 3769
    have hp : val WuPaper.ClassicalFourthData.Bq 3769 = (225625658882962:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 3769 = 225625658882962 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 3769 = (11769:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_3769
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 3770) ≤ val WuPaper.ClassicalFourthData.Bq 3770
    have hp : val WuPaper.ClassicalFourthData.Bq 3770 = (225650230504560:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 3770 = 225650230504560 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 3770 = (1177:ℝ)/400 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_3770
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 3771) ≤ val WuPaper.ClassicalFourthData.Bq 3771
    have hp : val WuPaper.ClassicalFourthData.Bq 3771 = (225674792322561:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 3771 = 225674792322561 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 3771 = (11771:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_3771
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 3772) ≤ val WuPaper.ClassicalFourthData.Bq 3772
    have hp : val WuPaper.ClassicalFourthData.Bq 3772 = (225699344340912:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 3772 = 225699344340912 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 3772 = (2943:ℝ)/1000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_3772
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 3773) ≤ val WuPaper.ClassicalFourthData.Bq 3773
    have hp : val WuPaper.ClassicalFourthData.Bq 3773 = (225723886563558:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 3773 = 225723886563558 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 3773 = (11773:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_3773
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 3774) ≤ val WuPaper.ClassicalFourthData.Bq 3774
    have hp : val WuPaper.ClassicalFourthData.Bq 3774 = (225748418994443:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 3774 = 225748418994443 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 3774 = (5887:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_3774
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 3775) ≤ val WuPaper.ClassicalFourthData.Bq 3775
    have hp : val WuPaper.ClassicalFourthData.Bq 3775 = (225772941637506:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 3775 = 225772941637506 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 3775 = (471:ℝ)/160 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_3775
end WuPaper.ClassicalFourthConditions
#print axioms WuPaper.ClassicalFourthConditions.Log_block_235

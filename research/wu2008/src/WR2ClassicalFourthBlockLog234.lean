import WR2ClassicalFourthConditions
import WR2ClassicalFourthLogPoints234
noncomputable section
namespace WuPaper.ClassicalFourthConditions
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem Log_block_234 (j : Fin 16) (hj : 16*234+j.val < 10541) :
    WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 (16*234+j.val)) ≤ val WuPaper.ClassicalFourthData.Bq (16*234+j.val) := by
  fin_cases j
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 3744) ≤ val WuPaper.ClassicalFourthData.Bq 3744
    have hp : val WuPaper.ClassicalFourthData.Bq 3744 = (225008170590731:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 3744 = 225008170590731 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 3744 = (367:ℝ)/125 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_3744
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 3745) ≤ val WuPaper.ClassicalFourthData.Bq 3745
    have hp : val WuPaper.ClassicalFourthData.Bq 3745 = (225032988590530:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 3745 = 225032988590530 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 3745 = (2349:ℝ)/800 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_3745
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 3746) ≤ val WuPaper.ClassicalFourthData.Bq 3746
    have hp : val WuPaper.ClassicalFourthData.Bq 3746 = (225057796687441:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 3746 = 225057796687441 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 3746 = (5873:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_3746
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 3747) ≤ val WuPaper.ClassicalFourthData.Bq 3747
    have hp : val WuPaper.ClassicalFourthData.Bq 3747 = (225082594885461:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 3747 = 225082594885461 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 3747 = (11747:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_3747
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 3748) ≤ val WuPaper.ClassicalFourthData.Bq 3748
    have hp : val WuPaper.ClassicalFourthData.Bq 3748 = (225107383188580:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 3748 = 225107383188580 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 3748 = (2937:ℝ)/1000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_3748
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 3749) ≤ val WuPaper.ClassicalFourthData.Bq 3749
    have hp : val WuPaper.ClassicalFourthData.Bq 3749 = (225132161600791:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 3749 = 225132161600791 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 3749 = (11749:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_3749
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 3750) ≤ val WuPaper.ClassicalFourthData.Bq 3750
    have hp : val WuPaper.ClassicalFourthData.Bq 3750 = (225156930126082:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 3750 = 225156930126082 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 3750 = (47:ℝ)/16 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_3750
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 3751) ≤ val WuPaper.ClassicalFourthData.Bq 3751
    have hp : val WuPaper.ClassicalFourthData.Bq 3751 = (225181688768440:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 3751 = 225181688768440 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 3751 = (11751:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_3751
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 3752) ≤ val WuPaper.ClassicalFourthData.Bq 3752
    have hp : val WuPaper.ClassicalFourthData.Bq 3752 = (225206437531850:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 3752 = 225206437531850 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 3752 = (1469:ℝ)/500 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_3752
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 3753) ≤ val WuPaper.ClassicalFourthData.Bq 3753
    have hp : val WuPaper.ClassicalFourthData.Bq 3753 = (225231176420295:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 3753 = 225231176420295 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 3753 = (11753:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_3753
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 3754) ≤ val WuPaper.ClassicalFourthData.Bq 3754
    have hp : val WuPaper.ClassicalFourthData.Bq 3754 = (225255905437757:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 3754 = 225255905437757 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 3754 = (5877:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_3754
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 3755) ≤ val WuPaper.ClassicalFourthData.Bq 3755
    have hp : val WuPaper.ClassicalFourthData.Bq 3755 = (225280624588214:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 3755 = 225280624588214 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 3755 = (2351:ℝ)/800 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_3755
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 3756) ≤ val WuPaper.ClassicalFourthData.Bq 3756
    have hp : val WuPaper.ClassicalFourthData.Bq 3756 = (225305333875643:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 3756 = 225305333875643 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 3756 = (2939:ℝ)/1000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_3756
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 3757) ≤ val WuPaper.ClassicalFourthData.Bq 3757
    have hp : val WuPaper.ClassicalFourthData.Bq 3757 = (225330033304022:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 3757 = 225330033304022 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 3757 = (11757:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_3757
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 3758) ≤ val WuPaper.ClassicalFourthData.Bq 3758
    have hp : val WuPaper.ClassicalFourthData.Bq 3758 = (225354722877321:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 3758 = 225354722877321 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 3758 = (5879:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_3758
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 3759) ≤ val WuPaper.ClassicalFourthData.Bq 3759
    have hp : val WuPaper.ClassicalFourthData.Bq 3759 = (225379402599515:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 3759 = 225379402599515 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 3759 = (11759:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_3759
end WuPaper.ClassicalFourthConditions
#print axioms WuPaper.ClassicalFourthConditions.Log_block_234

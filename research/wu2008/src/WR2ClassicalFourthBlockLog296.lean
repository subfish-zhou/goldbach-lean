import WR2ClassicalFourthConditions
import WR2ClassicalFourthLogPoints296
noncomputable section
namespace WuPaper.ClassicalFourthConditions
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem Log_block_296 (j : Fin 16) (hj : 16*296+j.val < 10541) :
    WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 (16*296+j.val)) ≤ val WuPaper.ClassicalFourthData.Bq (16*296+j.val) := by
  fin_cases j
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 4736) ≤ val WuPaper.ClassicalFourthData.Bq 4736
    have hp : val WuPaper.ClassicalFourthData.Bq 4736 = (245338586018423:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 4736 = 245338586018423 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 4736 = (398:ℝ)/125 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_4736
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 4737) ≤ val WuPaper.ClassicalFourthData.Bq 4737
    have hp : val WuPaper.ClassicalFourthData.Bq 4737 = (245355270533428:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 4737 = 245355270533428 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 4737 = (12737:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_4737
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 4738) ≤ val WuPaper.ClassicalFourthData.Bq 4738
    have hp : val WuPaper.ClassicalFourthData.Bq 4738 = (245371948315075:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 4738 = 245371948315075 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 4738 = (6369:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_4738
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 4739) ≤ val WuPaper.ClassicalFourthData.Bq 4739
    have hp : val WuPaper.ClassicalFourthData.Bq 4739 = (245388619365890:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 4739 = 245388619365890 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 4739 = (12739:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_4739
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 4740) ≤ val WuPaper.ClassicalFourthData.Bq 4740
    have hp : val WuPaper.ClassicalFourthData.Bq 4740 = (245405283688400:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 4740 = 245405283688400 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 4740 = (637:ℝ)/200 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_4740
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 4741) ≤ val WuPaper.ClassicalFourthData.Bq 4741
    have hp : val WuPaper.ClassicalFourthData.Bq 4741 = (245421941285131:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 4741 = 245421941285131 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 4741 = (12741:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_4741
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 4742) ≤ val WuPaper.ClassicalFourthData.Bq 4742
    have hp : val WuPaper.ClassicalFourthData.Bq 4742 = (245438592158604:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 4742 = 245438592158604 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 4742 = (6371:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_4742
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 4743) ≤ val WuPaper.ClassicalFourthData.Bq 4743
    have hp : val WuPaper.ClassicalFourthData.Bq 4743 = (245455236311344:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 4743 = 245455236311344 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 4743 = (12743:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_4743
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 4744) ≤ val WuPaper.ClassicalFourthData.Bq 4744
    have hp : val WuPaper.ClassicalFourthData.Bq 4744 = (245471873745872:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 4744 = 245471873745872 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 4744 = (1593:ℝ)/500 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_4744
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 4745) ≤ val WuPaper.ClassicalFourthData.Bq 4745
    have hp : val WuPaper.ClassicalFourthData.Bq 4745 = (245488504464708:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 4745 = 245488504464708 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 4745 = (2549:ℝ)/800 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_4745
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 4746) ≤ val WuPaper.ClassicalFourthData.Bq 4746
    have hp : val WuPaper.ClassicalFourthData.Bq 4746 = (245505128470372:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 4746 = 245505128470372 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 4746 = (6373:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_4746
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 4747) ≤ val WuPaper.ClassicalFourthData.Bq 4747
    have hp : val WuPaper.ClassicalFourthData.Bq 4747 = (245521745765381:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 4747 = 245521745765381 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 4747 = (12747:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_4747
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 4748) ≤ val WuPaper.ClassicalFourthData.Bq 4748
    have hp : val WuPaper.ClassicalFourthData.Bq 4748 = (245538356352254:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 4748 = 245538356352254 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 4748 = (3187:ℝ)/1000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_4748
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 4749) ≤ val WuPaper.ClassicalFourthData.Bq 4749
    have hp : val WuPaper.ClassicalFourthData.Bq 4749 = (245554960233505:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 4749 = 245554960233505 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 4749 = (12749:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_4749
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 4750) ≤ val WuPaper.ClassicalFourthData.Bq 4750
    have hp : val WuPaper.ClassicalFourthData.Bq 4750 = (245571557411650:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 4750 = 245571557411650 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 4750 = (51:ℝ)/16 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_4750
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 4751) ≤ val WuPaper.ClassicalFourthData.Bq 4751
    have hp : val WuPaper.ClassicalFourthData.Bq 4751 = (245588147889202:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 4751 = 245588147889202 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 4751 = (12751:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_4751
end WuPaper.ClassicalFourthConditions
#print axioms WuPaper.ClassicalFourthConditions.Log_block_296

import WR2ClassicalFourthConditions
import WR2ClassicalFourthLogPoints240
noncomputable section
namespace WuPaper.ClassicalFourthConditions
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem Log_block_240 (j : Fin 16) (hj : 16*240+j.val < 10541) :
    WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 (16*240+j.val)) ≤ val WuPaper.ClassicalFourthData.Bq (16*240+j.val) := by
  fin_cases j
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 3840) ≤ val WuPaper.ClassicalFourthData.Bq 3840
    have hp : val WuPaper.ClassicalFourthData.Bq 3840 = (227346105825144:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 3840 = 227346105825144 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 3840 = (74:ℝ)/25 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_3840
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 3841) ≤ val WuPaper.ClassicalFourthData.Bq 3841
    have hp : val WuPaper.ClassicalFourthData.Bq 3841 = (227369991091596:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 3841 = 227369991091596 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 3841 = (11841:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_3841
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 3842) ≤ val WuPaper.ClassicalFourthData.Bq 3842
    have hp : val WuPaper.ClassicalFourthData.Bq 3842 = (227393866830012:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 3842 = 227393866830012 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 3842 = (5921:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_3842
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 3843) ≤ val WuPaper.ClassicalFourthData.Bq 3843
    have hp : val WuPaper.ClassicalFourthData.Bq 3843 = (227417733044208:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 3843 = 227417733044208 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 3843 = (11843:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_3843
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 3844) ≤ val WuPaper.ClassicalFourthData.Bq 3844
    have hp : val WuPaper.ClassicalFourthData.Bq 3844 = (227441589737998:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 3844 = 227441589737998 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 3844 = (2961:ℝ)/1000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_3844
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 3845) ≤ val WuPaper.ClassicalFourthData.Bq 3845
    have hp : val WuPaper.ClassicalFourthData.Bq 3845 = (227465436915190:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 3845 = 227465436915190 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 3845 = (2369:ℝ)/800 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_3845
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 3846) ≤ val WuPaper.ClassicalFourthData.Bq 3846
    have hp : val WuPaper.ClassicalFourthData.Bq 3846 = (227489274579595:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 3846 = 227489274579595 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 3846 = (5923:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_3846
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 3847) ≤ val WuPaper.ClassicalFourthData.Bq 3847
    have hp : val WuPaper.ClassicalFourthData.Bq 3847 = (227513102735021:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 3847 = 227513102735021 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 3847 = (11847:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_3847
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 3848) ≤ val WuPaper.ClassicalFourthData.Bq 3848
    have hp : val WuPaper.ClassicalFourthData.Bq 3848 = (227536921385271:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 3848 = 227536921385271 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 3848 = (1481:ℝ)/500 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_3848
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 3849) ≤ val WuPaper.ClassicalFourthData.Bq 3849
    have hp : val WuPaper.ClassicalFourthData.Bq 3849 = (227560730534151:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 3849 = 227560730534151 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 3849 = (11849:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_3849
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 3850) ≤ val WuPaper.ClassicalFourthData.Bq 3850
    have hp : val WuPaper.ClassicalFourthData.Bq 3850 = (227584530185461:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 3850 = 227584530185461 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 3850 = (237:ℝ)/80 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_3850
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 3851) ≤ val WuPaper.ClassicalFourthData.Bq 3851
    have hp : val WuPaper.ClassicalFourthData.Bq 3851 = (227608320343002:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 3851 = 227608320343002 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 3851 = (11851:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_3851
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 3852) ≤ val WuPaper.ClassicalFourthData.Bq 3852
    have hp : val WuPaper.ClassicalFourthData.Bq 3852 = (227632101010572:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 3852 = 227632101010572 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 3852 = (2963:ℝ)/1000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_3852
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 3853) ≤ val WuPaper.ClassicalFourthData.Bq 3853
    have hp : val WuPaper.ClassicalFourthData.Bq 3853 = (227655872191968:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 3853 = 227655872191968 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 3853 = (11853:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_3853
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 3854) ≤ val WuPaper.ClassicalFourthData.Bq 3854
    have hp : val WuPaper.ClassicalFourthData.Bq 3854 = (227679633890983:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 3854 = 227679633890983 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 3854 = (5927:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_3854
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 3855) ≤ val WuPaper.ClassicalFourthData.Bq 3855
    have hp : val WuPaper.ClassicalFourthData.Bq 3855 = (227703386111411:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 3855 = 227703386111411 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 3855 = (2371:ℝ)/800 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_3855
end WuPaper.ClassicalFourthConditions
#print axioms WuPaper.ClassicalFourthConditions.Log_block_240

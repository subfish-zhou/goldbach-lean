import WR2ClassicalFourthConditions
import WR2ClassicalFourthLogPoints057
noncomputable section
namespace WuPaper.ClassicalFourthConditions
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem Log_block_057 (j : Fin 16) (hj : 16*57+j.val < 10541) :
    WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 (16*57+j.val)) ≤ val WuPaper.ClassicalFourthData.Bq (16*57+j.val) := by
  fin_cases j
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 912) ≤ val WuPaper.ClassicalFourthData.Bq 912
    have hp : val WuPaper.ClassicalFourthData.Bq 912 = (92184393951953:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 912 = 92184393951953 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 912 = (557:ℝ)/250 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_912
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 913) ≤ val WuPaper.ClassicalFourthData.Bq 913
    have hp : val WuPaper.ClassicalFourthData.Bq 913 = (92265406514808:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 913 = 92265406514808 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 913 = (8913:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_913
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 914) ≤ val WuPaper.ClassicalFourthData.Bq 914
    have hp : val WuPaper.ClassicalFourthData.Bq 914 = (92346382310567:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 914 = 92346382310567 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 914 = (4457:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_914
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 915) ≤ val WuPaper.ClassicalFourthData.Bq 915
    have hp : val WuPaper.ClassicalFourthData.Bq 915 = (92427321359166:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 915 = 92427321359166 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 915 = (1783:ℝ)/800 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_915
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 916) ≤ val WuPaper.ClassicalFourthData.Bq 916
    have hp : val WuPaper.ClassicalFourthData.Bq 916 = (92508223680529:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 916 = 92508223680529 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 916 = (2229:ℝ)/1000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_916
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 917) ≤ val WuPaper.ClassicalFourthData.Bq 917
    have hp : val WuPaper.ClassicalFourthData.Bq 917 = (92589089294567:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 917 = 92589089294567 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 917 = (8917:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_917
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 918) ≤ val WuPaper.ClassicalFourthData.Bq 918
    have hp : val WuPaper.ClassicalFourthData.Bq 918 = (92669918221176:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 918 = 92669918221176 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 918 = (4459:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_918
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 919) ≤ val WuPaper.ClassicalFourthData.Bq 919
    have hp : val WuPaper.ClassicalFourthData.Bq 919 = (92750710480239:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 919 = 92750710480239 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 919 = (8919:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_919
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 920) ≤ val WuPaper.ClassicalFourthData.Bq 920
    have hp : val WuPaper.ClassicalFourthData.Bq 920 = (92831466091627:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 920 = 92831466091627 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 920 = (223:ℝ)/100 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_920
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 921) ≤ val WuPaper.ClassicalFourthData.Bq 921
    have hp : val WuPaper.ClassicalFourthData.Bq 921 = (92912185075194:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 921 = 92912185075194 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 921 = (8921:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_921
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 922) ≤ val WuPaper.ClassicalFourthData.Bq 922
    have hp : val WuPaper.ClassicalFourthData.Bq 922 = (92992867450784:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 922 = 92992867450784 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 922 = (4461:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_922
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 923) ≤ val WuPaper.ClassicalFourthData.Bq 923
    have hp : val WuPaper.ClassicalFourthData.Bq 923 = (93073513238227:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 923 = 93073513238227 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 923 = (8923:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_923
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 924) ≤ val WuPaper.ClassicalFourthData.Bq 924
    have hp : val WuPaper.ClassicalFourthData.Bq 924 = (93154122457336:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 924 = 93154122457336 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 924 = (2231:ℝ)/1000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_924
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 925) ≤ val WuPaper.ClassicalFourthData.Bq 925
    have hp : val WuPaper.ClassicalFourthData.Bq 925 = (93234695127916:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 925 = 93234695127916 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 925 = (357:ℝ)/160 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_925
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 926) ≤ val WuPaper.ClassicalFourthData.Bq 926
    have hp : val WuPaper.ClassicalFourthData.Bq 926 = (93315231269754:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 926 = 93315231269754 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 926 = (4463:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_926
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 927) ≤ val WuPaper.ClassicalFourthData.Bq 927
    have hp : val WuPaper.ClassicalFourthData.Bq 927 = (93395730902626:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 927 = 93395730902626 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 927 = (8927:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_927
end WuPaper.ClassicalFourthConditions
#print axioms WuPaper.ClassicalFourthConditions.Log_block_057

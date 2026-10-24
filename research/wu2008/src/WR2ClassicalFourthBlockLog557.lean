import WR2ClassicalFourthConditions
import WR2ClassicalFourthLogPoints557
noncomputable section
namespace WuPaper.ClassicalFourthConditions
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem Log_block_557 (j : Fin 16) (hj : 16*557+j.val < 10541) :
    WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 (16*557+j.val)) ≤ val WuPaper.ClassicalFourthData.Bq (16*557+j.val) := by
  fin_cases j
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 8912) ≤ val WuPaper.ClassicalFourthData.Bq 8912
    have hp : val WuPaper.ClassicalFourthData.Bq 8912 = (277167159513461:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 8912 = 277167159513461 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 8912 = (1057:ℝ)/250 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_8912
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 8913) ≤ val WuPaper.ClassicalFourthData.Bq 8913
    have hp : val WuPaper.ClassicalFourthData.Bq 8913 = (277169087627237:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 8913 = 277169087627237 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 8913 = (16913:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_8913
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 8914) ≤ val WuPaper.ClassicalFourthData.Bq 8914
    have hp : val WuPaper.ClassicalFourthData.Bq 8914 = (277171014094750:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 8914 = 277171014094750 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 8914 = (8457:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_8914
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 8915) ≤ val WuPaper.ClassicalFourthData.Bq 8915
    have hp : val WuPaper.ClassicalFourthData.Bq 8915 = (277172938916514:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 8915 = 277172938916514 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 8915 = (3383:ℝ)/800 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_8915
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 8916) ≤ val WuPaper.ClassicalFourthData.Bq 8916
    have hp : val WuPaper.ClassicalFourthData.Bq 8916 = (277174862093039:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 8916 = 277174862093039 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 8916 = (4229:ℝ)/1000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_8916
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 8917) ≤ val WuPaper.ClassicalFourthData.Bq 8917
    have hp : val WuPaper.ClassicalFourthData.Bq 8917 = (277176783624836:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 8917 = 277176783624836 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 8917 = (16917:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_8917
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 8918) ≤ val WuPaper.ClassicalFourthData.Bq 8918
    have hp : val WuPaper.ClassicalFourthData.Bq 8918 = (277178703512417:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 8918 = 277178703512417 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 8918 = (8459:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_8918
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 8919) ≤ val WuPaper.ClassicalFourthData.Bq 8919
    have hp : val WuPaper.ClassicalFourthData.Bq 8919 = (277180621756293:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 8919 = 277180621756293 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 8919 = (16919:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_8919
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 8920) ≤ val WuPaper.ClassicalFourthData.Bq 8920
    have hp : val WuPaper.ClassicalFourthData.Bq 8920 = (277182538356974:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 8920 = 277182538356974 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 8920 = (423:ℝ)/100 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_8920
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 8921) ≤ val WuPaper.ClassicalFourthData.Bq 8921
    have hp : val WuPaper.ClassicalFourthData.Bq 8921 = (277184453314971:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 8921 = 277184453314971 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 8921 = (16921:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_8921
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 8922) ≤ val WuPaper.ClassicalFourthData.Bq 8922
    have hp : val WuPaper.ClassicalFourthData.Bq 8922 = (277186366630794:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 8922 = 277186366630794 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 8922 = (8461:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_8922
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 8923) ≤ val WuPaper.ClassicalFourthData.Bq 8923
    have hp : val WuPaper.ClassicalFourthData.Bq 8923 = (277188278304954:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 8923 = 277188278304954 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 8923 = (16923:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_8923
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 8924) ≤ val WuPaper.ClassicalFourthData.Bq 8924
    have hp : val WuPaper.ClassicalFourthData.Bq 8924 = (277190188337960:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 8924 = 277190188337960 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 8924 = (4231:ℝ)/1000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_8924
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 8925) ≤ val WuPaper.ClassicalFourthData.Bq 8925
    have hp : val WuPaper.ClassicalFourthData.Bq 8925 = (277192096730323:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 8925 = 277192096730323 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 8925 = (677:ℝ)/160 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_8925
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 8926) ≤ val WuPaper.ClassicalFourthData.Bq 8926
    have hp : val WuPaper.ClassicalFourthData.Bq 8926 = (277194003482552:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 8926 = 277194003482552 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 8926 = (8463:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_8926
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 8927) ≤ val WuPaper.ClassicalFourthData.Bq 8927
    have hp : val WuPaper.ClassicalFourthData.Bq 8927 = (277195908595156:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 8927 = 277195908595156 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 8927 = (16927:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_8927
end WuPaper.ClassicalFourthConditions
#print axioms WuPaper.ClassicalFourthConditions.Log_block_557

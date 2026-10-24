import WR2ClassicalFourthConditions
import WR2ClassicalFourthLogPoints377
noncomputable section
namespace WuPaper.ClassicalFourthConditions
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem Log_block_377 (j : Fin 16) (hj : 16*377+j.val < 10541) :
    WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 (16*377+j.val)) ≤ val WuPaper.ClassicalFourthData.Bq (16*377+j.val) := by
  fin_cases j
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 6032) ≤ val WuPaper.ClassicalFourthData.Bq 6032
    have hp : val WuPaper.ClassicalFourthData.Bq 6032 = (262111066924371:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 6032 = 262111066924371 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 6032 = (877:ℝ)/250 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_6032
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 6033) ≤ val WuPaper.ClassicalFourthData.Bq 6033
    have hp : val WuPaper.ClassicalFourthData.Bq 6033 = (262120800633822:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 6033 = 262120800633822 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 6033 = (14033:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_6033
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 6034) ≤ val WuPaper.ClassicalFourthData.Bq 6034
    have hp : val WuPaper.ClassicalFourthData.Bq 6034 = (262130530124609:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 6034 = 262130530124609 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 6034 = (7017:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_6034
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 6035) ≤ val WuPaper.ClassicalFourthData.Bq 6035
    have hp : val WuPaper.ClassicalFourthData.Bq 6035 = (262140255398199:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 6035 = 262140255398199 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 6035 = (2807:ℝ)/800 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_6035
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 6036) ≤ val WuPaper.ClassicalFourthData.Bq 6036
    have hp : val WuPaper.ClassicalFourthData.Bq 6036 = (262149976456057:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 6036 = 262149976456057 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 6036 = (3509:ℝ)/1000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_6036
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 6037) ≤ val WuPaper.ClassicalFourthData.Bq 6037
    have hp : val WuPaper.ClassicalFourthData.Bq 6037 = (262159693299649:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 6037 = 262159693299649 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 6037 = (14037:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_6037
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 6038) ≤ val WuPaper.ClassicalFourthData.Bq 6038
    have hp : val WuPaper.ClassicalFourthData.Bq 6038 = (262169405930438:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 6038 = 262169405930438 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 6038 = (7019:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_6038
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 6039) ≤ val WuPaper.ClassicalFourthData.Bq 6039
    have hp : val WuPaper.ClassicalFourthData.Bq 6039 = (262179114349888:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 6039 = 262179114349888 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 6039 = (14039:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_6039
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 6040) ≤ val WuPaper.ClassicalFourthData.Bq 6040
    have hp : val WuPaper.ClassicalFourthData.Bq 6040 = (262188818559462:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 6040 = 262188818559462 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 6040 = (351:ℝ)/100 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_6040
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 6041) ≤ val WuPaper.ClassicalFourthData.Bq 6041
    have hp : val WuPaper.ClassicalFourthData.Bq 6041 = (262198518560624:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 6041 = 262198518560624 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 6041 = (14041:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_6041
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 6042) ≤ val WuPaper.ClassicalFourthData.Bq 6042
    have hp : val WuPaper.ClassicalFourthData.Bq 6042 = (262208214354834:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 6042 = 262208214354834 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 6042 = (7021:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_6042
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 6043) ≤ val WuPaper.ClassicalFourthData.Bq 6043
    have hp : val WuPaper.ClassicalFourthData.Bq 6043 = (262217905943554:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 6043 = 262217905943554 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 6043 = (14043:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_6043
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 6044) ≤ val WuPaper.ClassicalFourthData.Bq 6044
    have hp : val WuPaper.ClassicalFourthData.Bq 6044 = (262227593328245:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 6044 = 262227593328245 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 6044 = (3511:ℝ)/1000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_6044
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 6045) ≤ val WuPaper.ClassicalFourthData.Bq 6045
    have hp : val WuPaper.ClassicalFourthData.Bq 6045 = (262237276510367:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 6045 = 262237276510367 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 6045 = (2809:ℝ)/800 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_6045
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 6046) ≤ val WuPaper.ClassicalFourthData.Bq 6046
    have hp : val WuPaper.ClassicalFourthData.Bq 6046 = (262246955491381:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 6046 = 262246955491381 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 6046 = (7023:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_6046
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 6047) ≤ val WuPaper.ClassicalFourthData.Bq 6047
    have hp : val WuPaper.ClassicalFourthData.Bq 6047 = (262256630272744:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 6047 = 262256630272744 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 6047 = (14047:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_6047
end WuPaper.ClassicalFourthConditions
#print axioms WuPaper.ClassicalFourthConditions.Log_block_377

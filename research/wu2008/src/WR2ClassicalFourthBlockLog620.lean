import WR2ClassicalFourthConditions
import WR2ClassicalFourthLogPoints620
noncomputable section
namespace WuPaper.ClassicalFourthConditions
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem Log_block_620 (j : Fin 16) (hj : 16*620+j.val < 10541) :
    WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 (16*620+j.val)) ≤ val WuPaper.ClassicalFourthData.Bq (16*620+j.val) := by
  fin_cases j
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 9920) ≤ val WuPaper.ClassicalFourthData.Bq 9920
    have hp : val WuPaper.ClassicalFourthData.Bq 9920 = (278355422738923:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 9920 = 278355422738923 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 9920 = (112:ℝ)/25 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_9920
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 9921) ≤ val WuPaper.ClassicalFourthData.Bq 9921
    have hp : val WuPaper.ClassicalFourthData.Bq 9921 = (278355924417312:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 9921 = 278355924417312 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 9921 = (17921:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_9921
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 9922) ≤ val WuPaper.ClassicalFourthData.Bq 9922
    have hp : val WuPaper.ClassicalFourthData.Bq 9922 = (278356424888035:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 9922 = 278356424888035 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 9922 = (8961:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_9922
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 9923) ≤ val WuPaper.ClassicalFourthData.Bq 9923
    have hp : val WuPaper.ClassicalFourthData.Bq 9923 = (278356924151459:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 9923 = 278356924151459 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 9923 = (17923:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_9923
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 9924) ≤ val WuPaper.ClassicalFourthData.Bq 9924
    have hp : val WuPaper.ClassicalFourthData.Bq 9924 = (278357422207950:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 9924 = 278357422207950 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 9924 = (4481:ℝ)/1000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_9924
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 9925) ≤ val WuPaper.ClassicalFourthData.Bq 9925
    have hp : val WuPaper.ClassicalFourthData.Bq 9925 = (278357919057877:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 9925 = 278357919057877 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 9925 = (717:ℝ)/160 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_9925
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 9926) ≤ val WuPaper.ClassicalFourthData.Bq 9926
    have hp : val WuPaper.ClassicalFourthData.Bq 9926 = (278358414701608:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 9926 = 278358414701608 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 9926 = (8963:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_9926
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 9927) ≤ val WuPaper.ClassicalFourthData.Bq 9927
    have hp : val WuPaper.ClassicalFourthData.Bq 9927 = (278358909139508:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 9927 = 278358909139508 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 9927 = (17927:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_9927
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 9928) ≤ val WuPaper.ClassicalFourthData.Bq 9928
    have hp : val WuPaper.ClassicalFourthData.Bq 9928 = (278359402371944:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 9928 = 278359402371944 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 9928 = (2241:ℝ)/500 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_9928
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 9929) ≤ val WuPaper.ClassicalFourthData.Bq 9929
    have hp : val WuPaper.ClassicalFourthData.Bq 9929 = (278359894399285:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 9929 = 278359894399285 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 9929 = (17929:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_9929
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 9930) ≤ val WuPaper.ClassicalFourthData.Bq 9930
    have hp : val WuPaper.ClassicalFourthData.Bq 9930 = (278360385221896:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 9930 = 278360385221896 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 9930 = (1793:ℝ)/400 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_9930
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 9931) ≤ val WuPaper.ClassicalFourthData.Bq 9931
    have hp : val WuPaper.ClassicalFourthData.Bq 9931 = (278360874840144:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 9931 = 278360874840144 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 9931 = (17931:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_9931
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 9932) ≤ val WuPaper.ClassicalFourthData.Bq 9932
    have hp : val WuPaper.ClassicalFourthData.Bq 9932 = (278361363254396:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 9932 = 278361363254396 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 9932 = (4483:ℝ)/1000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_9932
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 9933) ≤ val WuPaper.ClassicalFourthData.Bq 9933
    have hp : val WuPaper.ClassicalFourthData.Bq 9933 = (278361850465018:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 9933 = 278361850465018 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 9933 = (17933:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_9933
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 9934) ≤ val WuPaper.ClassicalFourthData.Bq 9934
    have hp : val WuPaper.ClassicalFourthData.Bq 9934 = (278362336472377:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 9934 = 278362336472377 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 9934 = (8967:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_9934
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 9935) ≤ val WuPaper.ClassicalFourthData.Bq 9935
    have hp : val WuPaper.ClassicalFourthData.Bq 9935 = (278362821276838:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 9935 = 278362821276838 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 9935 = (3587:ℝ)/800 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_9935
end WuPaper.ClassicalFourthConditions
#print axioms WuPaper.ClassicalFourthConditions.Log_block_620

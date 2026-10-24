import WR2ClassicalFourthConditions
import WR2ClassicalFourthLogPoints560
noncomputable section
namespace WuPaper.ClassicalFourthConditions
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem Log_block_560 (j : Fin 16) (hj : 16*560+j.val < 10541) :
    WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 (16*560+j.val)) ≤ val WuPaper.ClassicalFourthData.Bq (16*560+j.val) := by
  fin_cases j
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 8960) ≤ val WuPaper.ClassicalFourthData.Bq 8960
    have hp : val WuPaper.ClassicalFourthData.Bq 8960 = (277257860806801:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 8960 = 277257860806801 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 8960 = (106:ℝ)/25 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_8960
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 8961) ≤ val WuPaper.ClassicalFourthData.Bq 8961
    have hp : val WuPaper.ClassicalFourthData.Bq 8961 = (277259710474141:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 8961 = 277259710474141 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 8961 = (16961:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_8961
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 8962) ≤ val WuPaper.ClassicalFourthData.Bq 8962
    have hp : val WuPaper.ClassicalFourthData.Bq 8962 = (277261558519583:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 8962 = 277261558519583 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 8962 = (8481:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_8962
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 8963) ≤ val WuPaper.ClassicalFourthData.Bq 8963
    have hp : val WuPaper.ClassicalFourthData.Bq 8963 = (277263404943631:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 8963 = 277263404943631 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 8963 = (16963:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_8963
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 8964) ≤ val WuPaper.ClassicalFourthData.Bq 8964
    have hp : val WuPaper.ClassicalFourthData.Bq 8964 = (277265249746788:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 8964 = 277265249746788 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 8964 = (4241:ℝ)/1000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_8964
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 8965) ≤ val WuPaper.ClassicalFourthData.Bq 8965
    have hp : val WuPaper.ClassicalFourthData.Bq 8965 = (277267092929557:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 8965 = 277267092929557 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 8965 = (3393:ℝ)/800 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_8965
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 8966) ≤ val WuPaper.ClassicalFourthData.Bq 8966
    have hp : val WuPaper.ClassicalFourthData.Bq 8966 = (277268934492442:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 8966 = 277268934492442 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 8966 = (8483:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_8966
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 8967) ≤ val WuPaper.ClassicalFourthData.Bq 8967
    have hp : val WuPaper.ClassicalFourthData.Bq 8967 = (277270774435944:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 8967 = 277270774435944 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 8967 = (16967:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_8967
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 8968) ≤ val WuPaper.ClassicalFourthData.Bq 8968
    have hp : val WuPaper.ClassicalFourthData.Bq 8968 = (277272612760567:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 8968 = 277272612760567 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 8968 = (2121:ℝ)/500 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_8968
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 8969) ≤ val WuPaper.ClassicalFourthData.Bq 8969
    have hp : val WuPaper.ClassicalFourthData.Bq 8969 = (277274449466812:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 8969 = 277274449466812 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 8969 = (16969:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_8969
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 8970) ≤ val WuPaper.ClassicalFourthData.Bq 8970
    have hp : val WuPaper.ClassicalFourthData.Bq 8970 = (277276284555183:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 8970 = 277276284555183 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 8970 = (1697:ℝ)/400 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_8970
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 8971) ≤ val WuPaper.ClassicalFourthData.Bq 8971
    have hp : val WuPaper.ClassicalFourthData.Bq 8971 = (277278118026180:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 8971 = 277278118026180 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 8971 = (16971:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_8971
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 8972) ≤ val WuPaper.ClassicalFourthData.Bq 8972
    have hp : val WuPaper.ClassicalFourthData.Bq 8972 = (277279949880307:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 8972 = 277279949880307 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 8972 = (4243:ℝ)/1000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_8972
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 8973) ≤ val WuPaper.ClassicalFourthData.Bq 8973
    have hp : val WuPaper.ClassicalFourthData.Bq 8973 = (277281780118065:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 8973 = 277281780118065 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 8973 = (16973:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_8973
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 8974) ≤ val WuPaper.ClassicalFourthData.Bq 8974
    have hp : val WuPaper.ClassicalFourthData.Bq 8974 = (277283608739954:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 8974 = 277283608739954 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 8974 = (8487:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_8974
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 8975) ≤ val WuPaper.ClassicalFourthData.Bq 8975
    have hp : val WuPaper.ClassicalFourthData.Bq 8975 = (277285435746478:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 8975 = 277285435746478 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 8975 = (679:ℝ)/160 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_8975
end WuPaper.ClassicalFourthConditions
#print axioms WuPaper.ClassicalFourthConditions.Log_block_560

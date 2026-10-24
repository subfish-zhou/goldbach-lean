import WR2ClassicalFourthConditions
import WR2ClassicalFourthLogPoints624
noncomputable section
namespace WuPaper.ClassicalFourthConditions
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem Log_block_624 (j : Fin 16) (hj : 16*624+j.val < 10541) :
    WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 (16*624+j.val)) ≤ val WuPaper.ClassicalFourthData.Bq (16*624+j.val) := by
  fin_cases j
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 9984) ≤ val WuPaper.ClassicalFourthData.Bq 9984
    have hp : val WuPaper.ClassicalFourthData.Bq 9984 = (278385110739804:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 9984 = 278385110739804 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 9984 = (562:ℝ)/125 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_9984
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 9985) ≤ val WuPaper.ClassicalFourthData.Bq 9985
    have hp : val WuPaper.ClassicalFourthData.Bq 9985 = (278385535863675:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 9985 = 278385535863675 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 9985 = (3597:ℝ)/800 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_9985
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 9986) ≤ val WuPaper.ClassicalFourthData.Bq 9986
    have hp : val WuPaper.ClassicalFourthData.Bq 9986 = (278385959803168:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 9986 = 278385959803168 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 9986 = (8993:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_9986
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 9987) ≤ val WuPaper.ClassicalFourthData.Bq 9987
    have hp : val WuPaper.ClassicalFourthData.Bq 9987 = (278386382558644:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 9987 = 278386382558644 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 9987 = (17987:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_9987
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 9988) ≤ val WuPaper.ClassicalFourthData.Bq 9988
    have hp : val WuPaper.ClassicalFourthData.Bq 9988 = (278386804130463:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 9988 = 278386804130463 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 9988 = (4497:ℝ)/1000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_9988
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 9989) ≤ val WuPaper.ClassicalFourthData.Bq 9989
    have hp : val WuPaper.ClassicalFourthData.Bq 9989 = (278387224518984:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 9989 = 278387224518984 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 9989 = (17989:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_9989
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 9990) ≤ val WuPaper.ClassicalFourthData.Bq 9990
    have hp : val WuPaper.ClassicalFourthData.Bq 9990 = (278387643724568:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 9990 = 278387643724568 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 9990 = (1799:ℝ)/400 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_9990
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 9991) ≤ val WuPaper.ClassicalFourthData.Bq 9991
    have hp : val WuPaper.ClassicalFourthData.Bq 9991 = (278388061747574:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 9991 = 278388061747574 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 9991 = (17991:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_9991
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 9992) ≤ val WuPaper.ClassicalFourthData.Bq 9992
    have hp : val WuPaper.ClassicalFourthData.Bq 9992 = (278388478588361:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 9992 = 278388478588361 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 9992 = (2249:ℝ)/500 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_9992
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 9993) ≤ val WuPaper.ClassicalFourthData.Bq 9993
    have hp : val WuPaper.ClassicalFourthData.Bq 9993 = (278388894247290:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 9993 = 278388894247290 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 9993 = (17993:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_9993
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 9994) ≤ val WuPaper.ClassicalFourthData.Bq 9994
    have hp : val WuPaper.ClassicalFourthData.Bq 9994 = (278389308724719:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 9994 = 278389308724719 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 9994 = (8997:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_9994
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 9995) ≤ val WuPaper.ClassicalFourthData.Bq 9995
    have hp : val WuPaper.ClassicalFourthData.Bq 9995 = (278389722021007:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 9995 = 278389722021007 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 9995 = (3599:ℝ)/800 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_9995
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 9996) ≤ val WuPaper.ClassicalFourthData.Bq 9996
    have hp : val WuPaper.ClassicalFourthData.Bq 9996 = (278390134136515:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 9996 = 278390134136515 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 9996 = (4499:ℝ)/1000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_9996
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 9997) ≤ val WuPaper.ClassicalFourthData.Bq 9997
    have hp : val WuPaper.ClassicalFourthData.Bq 9997 = (278390545071599:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 9997 = 278390545071599 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 9997 = (17997:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_9997
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 9998) ≤ val WuPaper.ClassicalFourthData.Bq 9998
    have hp : val WuPaper.ClassicalFourthData.Bq 9998 = (278390954826621:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 9998 = 278390954826621 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 9998 = (8999:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_9998
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 9999) ≤ val WuPaper.ClassicalFourthData.Bq 9999
    have hp : val WuPaper.ClassicalFourthData.Bq 9999 = (278391363401938:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 9999 = 278391363401938 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 9999 = (17999:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_9999
end WuPaper.ClassicalFourthConditions
#print axioms WuPaper.ClassicalFourthConditions.Log_block_624

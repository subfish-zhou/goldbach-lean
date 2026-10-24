import WR2ClassicalFourthConditions
import WR2ClassicalFourthLogPoints562
noncomputable section
namespace WuPaper.ClassicalFourthConditions
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem Log_block_562 (j : Fin 16) (hj : 16*562+j.val < 10541) :
    WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 (16*562+j.val)) ≤ val WuPaper.ClassicalFourthData.Bq (16*562+j.val) := by
  fin_cases j
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 8992) ≤ val WuPaper.ClassicalFourthData.Bq 8992
    have hp : val WuPaper.ClassicalFourthData.Bq 8992 = (277316248191388:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 8992 = 277316248191388 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 8992 = (531:ℝ)/125 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_8992
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 8993) ≤ val WuPaper.ClassicalFourthData.Bq 8993
    have hp : val WuPaper.ClassicalFourthData.Bq 8993 = (277318046206868:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 8993 = 277318046206868 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 8993 = (16993:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_8993
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 8994) ≤ val WuPaper.ClassicalFourthData.Bq 8994
    have hp : val WuPaper.ClassicalFourthData.Bq 8994 = (277319842616476:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 8994 = 277319842616476 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 8994 = (8497:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_8994
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 8995) ≤ val WuPaper.ClassicalFourthData.Bq 8995
    have hp : val WuPaper.ClassicalFourthData.Bq 8995 = (277321637420710:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 8995 = 277321637420710 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 8995 = (3399:ℝ)/800 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_8995
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 8996) ≤ val WuPaper.ClassicalFourthData.Bq 8996
    have hp : val WuPaper.ClassicalFourthData.Bq 8996 = (277323430620069:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 8996 = 277323430620069 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 8996 = (4249:ℝ)/1000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_8996
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 8997) ≤ val WuPaper.ClassicalFourthData.Bq 8997
    have hp : val WuPaper.ClassicalFourthData.Bq 8997 = (277325222215051:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 8997 = 277325222215051 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 8997 = (16997:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_8997
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 8998) ≤ val WuPaper.ClassicalFourthData.Bq 8998
    have hp : val WuPaper.ClassicalFourthData.Bq 8998 = (277327012206152:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 8998 = 277327012206152 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 8998 = (8499:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_8998
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 8999) ≤ val WuPaper.ClassicalFourthData.Bq 8999
    have hp : val WuPaper.ClassicalFourthData.Bq 8999 = (277328800593870:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 8999 = 277328800593870 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 8999 = (16999:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_8999
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 9000) ≤ val WuPaper.ClassicalFourthData.Bq 9000
    have hp : val WuPaper.ClassicalFourthData.Bq 9000 = (277330587378703:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 9000 = 277330587378703 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 9000 = (17:ℝ)/4 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_9000
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 9001) ≤ val WuPaper.ClassicalFourthData.Bq 9001
    have hp : val WuPaper.ClassicalFourthData.Bq 9001 = (277332372561147:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 9001 = 277332372561147 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 9001 = (17001:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_9001
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 9002) ≤ val WuPaper.ClassicalFourthData.Bq 9002
    have hp : val WuPaper.ClassicalFourthData.Bq 9002 = (277334156141699:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 9002 = 277334156141699 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 9002 = (8501:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_9002
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 9003) ≤ val WuPaper.ClassicalFourthData.Bq 9003
    have hp : val WuPaper.ClassicalFourthData.Bq 9003 = (277335938120856:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 9003 = 277335938120856 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 9003 = (17003:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_9003
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 9004) ≤ val WuPaper.ClassicalFourthData.Bq 9004
    have hp : val WuPaper.ClassicalFourthData.Bq 9004 = (277337718499115:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 9004 = 277337718499115 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 9004 = (4251:ℝ)/1000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_9004
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 9005) ≤ val WuPaper.ClassicalFourthData.Bq 9005
    have hp : val WuPaper.ClassicalFourthData.Bq 9005 = (277339497276972:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 9005 = 277339497276972 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 9005 = (3401:ℝ)/800 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_9005
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 9006) ≤ val WuPaper.ClassicalFourthData.Bq 9006
    have hp : val WuPaper.ClassicalFourthData.Bq 9006 = (277341274454922:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 9006 = 277341274454922 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 9006 = (8503:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_9006
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 9007) ≤ val WuPaper.ClassicalFourthData.Bq 9007
    have hp : val WuPaper.ClassicalFourthData.Bq 9007 = (277343050033464:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 9007 = 277343050033464 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 9007 = (17007:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_9007
end WuPaper.ClassicalFourthConditions
#print axioms WuPaper.ClassicalFourthConditions.Log_block_562

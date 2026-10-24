import WR2ClassicalFourthConditions
import WR2ClassicalFourthLogPoints618
noncomputable section
namespace WuPaper.ClassicalFourthConditions
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem Log_block_618 (j : Fin 16) (hj : 16*618+j.val < 10541) :
    WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 (16*618+j.val)) ≤ val WuPaper.ClassicalFourthData.Bq (16*618+j.val) := by
  fin_cases j
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 9888) ≤ val WuPaper.ClassicalFourthData.Bq 9888
    have hp : val WuPaper.ClassicalFourthData.Bq 9888 = (278338729176644:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 9888 = 278338729176644 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 9888 = (559:ℝ)/125 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_9888
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 9889) ≤ val WuPaper.ClassicalFourthData.Bq 9889
    have hp : val WuPaper.ClassicalFourthData.Bq 9889 = (278339269695157:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 9889 = 278339269695157 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 9889 = (17889:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_9889
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 9890) ≤ val WuPaper.ClassicalFourthData.Bq 9890
    have hp : val WuPaper.ClassicalFourthData.Bq 9890 = (278339808994179:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 9890 = 278339808994179 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 9890 = (1789:ℝ)/400 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_9890
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 9891) ≤ val WuPaper.ClassicalFourthData.Bq 9891
    have hp : val WuPaper.ClassicalFourthData.Bq 9891 = (278340347074080:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 9891 = 278340347074080 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 9891 = (17891:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_9891
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 9892) ≤ val WuPaper.ClassicalFourthData.Bq 9892
    have hp : val WuPaper.ClassicalFourthData.Bq 9892 = (278340883935232:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 9892 = 278340883935232 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 9892 = (4473:ℝ)/1000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_9892
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 9893) ≤ val WuPaper.ClassicalFourthData.Bq 9893
    have hp : val WuPaper.ClassicalFourthData.Bq 9893 = (278341419578007:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 9893 = 278341419578007 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 9893 = (17893:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_9893
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 9894) ≤ val WuPaper.ClassicalFourthData.Bq 9894
    have hp : val WuPaper.ClassicalFourthData.Bq 9894 = (278341954002774:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 9894 = 278341954002774 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 9894 = (8947:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_9894
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 9895) ≤ val WuPaper.ClassicalFourthData.Bq 9895
    have hp : val WuPaper.ClassicalFourthData.Bq 9895 = (278342487209906:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 9895 = 278342487209906 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 9895 = (3579:ℝ)/800 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_9895
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 9896) ≤ val WuPaper.ClassicalFourthData.Bq 9896
    have hp : val WuPaper.ClassicalFourthData.Bq 9896 = (278343019199772:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 9896 = 278343019199772 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 9896 = (2237:ℝ)/500 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_9896
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 9897) ≤ val WuPaper.ClassicalFourthData.Bq 9897
    have hp : val WuPaper.ClassicalFourthData.Bq 9897 = (278343549972744:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 9897 = 278343549972744 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 9897 = (17897:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_9897
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 9898) ≤ val WuPaper.ClassicalFourthData.Bq 9898
    have hp : val WuPaper.ClassicalFourthData.Bq 9898 = (278344079529192:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 9898 = 278344079529192 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 9898 = (8949:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_9898
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 9899) ≤ val WuPaper.ClassicalFourthData.Bq 9899
    have hp : val WuPaper.ClassicalFourthData.Bq 9899 = (278344607869486:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 9899 = 278344607869486 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 9899 = (17899:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_9899
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 9900) ≤ val WuPaper.ClassicalFourthData.Bq 9900
    have hp : val WuPaper.ClassicalFourthData.Bq 9900 = (278345134993997:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 9900 = 278345134993997 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 9900 = (179:ℝ)/40 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_9900
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 9901) ≤ val WuPaper.ClassicalFourthData.Bq 9901
    have hp : val WuPaper.ClassicalFourthData.Bq 9901 = (278345660903095:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 9901 = 278345660903095 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 9901 = (17901:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_9901
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 9902) ≤ val WuPaper.ClassicalFourthData.Bq 9902
    have hp : val WuPaper.ClassicalFourthData.Bq 9902 = (278346185597149:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 9902 = 278346185597149 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 9902 = (8951:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_9902
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 9903) ≤ val WuPaper.ClassicalFourthData.Bq 9903
    have hp : val WuPaper.ClassicalFourthData.Bq 9903 = (278346709076531:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 9903 = 278346709076531 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 9903 = (17903:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_9903
end WuPaper.ClassicalFourthConditions
#print axioms WuPaper.ClassicalFourthConditions.Log_block_618

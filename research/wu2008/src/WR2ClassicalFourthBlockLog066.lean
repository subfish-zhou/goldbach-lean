import WR2ClassicalFourthConditions
import WR2ClassicalFourthLogPoints066
noncomputable section
namespace WuPaper.ClassicalFourthConditions
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem Log_block_066 (j : Fin 16) (hj : 16*66+j.val < 10541) :
    WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 (16*66+j.val)) ≤ val WuPaper.ClassicalFourthData.Bq (16*66+j.val) := by
  fin_cases j
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 1056) ≤ val WuPaper.ClassicalFourthData.Bq 1056
    have hp : val WuPaper.ClassicalFourthData.Bq 1056 = (103481137687574:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 1056 = 103481137687574 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 1056 = (283:ℝ)/125 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_1056
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 1057) ≤ val WuPaper.ClassicalFourthData.Bq 1057
    have hp : val WuPaper.ClassicalFourthData.Bq 1057 = (103557054644123:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 1057 = 103557054644123 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 1057 = (9057:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_1057
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 1058) ≤ val WuPaper.ClassicalFourthData.Bq 1058
    have hp : val WuPaper.ClassicalFourthData.Bq 1058 = (103632937570273:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 1058 = 103632937570273 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 1058 = (4529:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_1058
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 1059) ≤ val WuPaper.ClassicalFourthData.Bq 1059
    have hp : val WuPaper.ClassicalFourthData.Bq 1059 = (103708786484119:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 1059 = 103708786484119 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 1059 = (9059:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_1059
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 1060) ≤ val WuPaper.ClassicalFourthData.Bq 1060
    have hp : val WuPaper.ClassicalFourthData.Bq 1060 = (103784601403746:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 1060 = 103784601403746 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 1060 = (453:ℝ)/200 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_1060
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 1061) ≤ val WuPaper.ClassicalFourthData.Bq 1061
    have hp : val WuPaper.ClassicalFourthData.Bq 1061 = (103860382347225:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 1061 = 103860382347225 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 1061 = (9061:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_1061
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 1062) ≤ val WuPaper.ClassicalFourthData.Bq 1062
    have hp : val WuPaper.ClassicalFourthData.Bq 1062 = (103936129332617:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 1062 = 103936129332617 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 1062 = (4531:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_1062
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 1063) ≤ val WuPaper.ClassicalFourthData.Bq 1063
    have hp : val WuPaper.ClassicalFourthData.Bq 1063 = (104011842377969:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 1063 = 104011842377969 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 1063 = (9063:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_1063
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 1064) ≤ val WuPaper.ClassicalFourthData.Bq 1064
    have hp : val WuPaper.ClassicalFourthData.Bq 1064 = (104087521501318:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 1064 = 104087521501318 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 1064 = (1133:ℝ)/500 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_1064
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 1065) ≤ val WuPaper.ClassicalFourthData.Bq 1065
    have hp : val WuPaper.ClassicalFourthData.Bq 1065 = (104163166720687:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 1065 = 104163166720687 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 1065 = (1813:ℝ)/800 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_1065
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 1066) ≤ val WuPaper.ClassicalFourthData.Bq 1066
    have hp : val WuPaper.ClassicalFourthData.Bq 1066 = (104238778054090:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 1066 = 104238778054090 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 1066 = (4533:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_1066
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 1067) ≤ val WuPaper.ClassicalFourthData.Bq 1067
    have hp : val WuPaper.ClassicalFourthData.Bq 1067 = (104314355519525:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 1067 = 104314355519525 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 1067 = (9067:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_1067
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 1068) ≤ val WuPaper.ClassicalFourthData.Bq 1068
    have hp : val WuPaper.ClassicalFourthData.Bq 1068 = (104389899134982:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 1068 = 104389899134982 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 1068 = (2267:ℝ)/1000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_1068
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 1069) ≤ val WuPaper.ClassicalFourthData.Bq 1069
    have hp : val WuPaper.ClassicalFourthData.Bq 1069 = (104465408918435:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 1069 = 104465408918435 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 1069 = (9069:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_1069
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 1070) ≤ val WuPaper.ClassicalFourthData.Bq 1070
    have hp : val WuPaper.ClassicalFourthData.Bq 1070 = (104540884887851:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 1070 = 104540884887851 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 1070 = (907:ℝ)/400 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_1070
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 1071) ≤ val WuPaper.ClassicalFourthData.Bq 1071
    have hp : val WuPaper.ClassicalFourthData.Bq 1071 = (104616327061181:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 1071 = 104616327061181 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 1071 = (9071:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_1071
end WuPaper.ClassicalFourthConditions
#print axioms WuPaper.ClassicalFourthConditions.Log_block_066

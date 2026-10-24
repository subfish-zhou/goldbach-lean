import WR2ClassicalFourthConditions
import WR2ClassicalFourthLogPoints632
noncomputable section
namespace WuPaper.ClassicalFourthConditions
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem Log_block_632 (j : Fin 16) (hj : 16*632+j.val < 10541) :
    WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 (16*632+j.val)) ≤ val WuPaper.ClassicalFourthData.Bq (16*632+j.val) := by
  fin_cases j
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 10112) ≤ val WuPaper.ClassicalFourthData.Bq 10112
    have hp : val WuPaper.ClassicalFourthData.Bq 10112 = (278430021700042:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 10112 = 278430021700042 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 10112 = (566:ℝ)/125 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_10112
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 10113) ≤ val WuPaper.ClassicalFourthData.Bq 10113
    have hp : val WuPaper.ClassicalFourthData.Bq 10113 = (278430298111942:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 10113 = 278430298111942 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 10113 = (18113:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_10113
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 10114) ≤ val WuPaper.ClassicalFourthData.Bq 10114
    have hp : val WuPaper.ClassicalFourthData.Bq 10114 = (278430573384640:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 10114 = 278430573384640 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 10114 = (9057:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_10114
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 10115) ≤ val WuPaper.ClassicalFourthData.Bq 10115
    have hp : val WuPaper.ClassicalFourthData.Bq 10115 = (278430847518484:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 10115 = 278430847518484 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 10115 = (3623:ℝ)/800 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_10115
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 10116) ≤ val WuPaper.ClassicalFourthData.Bq 10116
    have hp : val WuPaper.ClassicalFourthData.Bq 10116 = (278431120513817:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 10116 = 278431120513817 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 10116 = (4529:ℝ)/1000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_10116
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 10117) ≤ val WuPaper.ClassicalFourthData.Bq 10117
    have hp : val WuPaper.ClassicalFourthData.Bq 10117 = (278431392370987:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 10117 = 278431392370987 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 10117 = (18117:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_10117
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 10118) ≤ val WuPaper.ClassicalFourthData.Bq 10118
    have hp : val WuPaper.ClassicalFourthData.Bq 10118 = (278431663090338:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 10118 = 278431663090338 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 10118 = (9059:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_10118
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 10119) ≤ val WuPaper.ClassicalFourthData.Bq 10119
    have hp : val WuPaper.ClassicalFourthData.Bq 10119 = (278431932672216:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 10119 = 278431932672216 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 10119 = (18119:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_10119
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 10120) ≤ val WuPaper.ClassicalFourthData.Bq 10120
    have hp : val WuPaper.ClassicalFourthData.Bq 10120 = (278432201116965:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 10120 = 278432201116965 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 10120 = (453:ℝ)/100 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_10120
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 10121) ≤ val WuPaper.ClassicalFourthData.Bq 10121
    have hp : val WuPaper.ClassicalFourthData.Bq 10121 = (278432468424932:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 10121 = 278432468424932 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 10121 = (18121:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_10121
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 10122) ≤ val WuPaper.ClassicalFourthData.Bq 10122
    have hp : val WuPaper.ClassicalFourthData.Bq 10122 = (278432734596460:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 10122 = 278432734596460 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 10122 = (9061:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_10122
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 10123) ≤ val WuPaper.ClassicalFourthData.Bq 10123
    have hp : val WuPaper.ClassicalFourthData.Bq 10123 = (278432999631896:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 10123 = 278432999631896 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 10123 = (18123:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_10123
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 10124) ≤ val WuPaper.ClassicalFourthData.Bq 10124
    have hp : val WuPaper.ClassicalFourthData.Bq 10124 = (278433263531583:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 10124 = 278433263531583 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 10124 = (4531:ℝ)/1000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_10124
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 10125) ≤ val WuPaper.ClassicalFourthData.Bq 10125
    have hp : val WuPaper.ClassicalFourthData.Bq 10125 = (278433526295866:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 10125 = 278433526295866 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 10125 = (145:ℝ)/32 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_10125
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 10126) ≤ val WuPaper.ClassicalFourthData.Bq 10126
    have hp : val WuPaper.ClassicalFourthData.Bq 10126 = (278433787925090:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 10126 = 278433787925090 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 10126 = (9063:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_10126
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 10127) ≤ val WuPaper.ClassicalFourthData.Bq 10127
    have hp : val WuPaper.ClassicalFourthData.Bq 10127 = (278434048419600:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 10127 = 278434048419600 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 10127 = (18127:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_10127
end WuPaper.ClassicalFourthConditions
#print axioms WuPaper.ClassicalFourthConditions.Log_block_632

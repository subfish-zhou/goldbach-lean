import WR2ClassicalFourthConditions
import WR2ClassicalFourthLogPoints376
noncomputable section
namespace WuPaper.ClassicalFourthConditions
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem Log_block_376 (j : Fin 16) (hj : 16*376+j.val < 10541) :
    WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 (16*376+j.val)) ≤ val WuPaper.ClassicalFourthData.Bq (16*376+j.val) := by
  fin_cases j
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 6016) ≤ val WuPaper.ClassicalFourthData.Bq 6016
    have hp : val WuPaper.ClassicalFourthData.Bq 6016 = (261954752636379:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 6016 = 261954752636379 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 6016 = (438:ℝ)/125 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_6016
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 6017) ≤ val WuPaper.ClassicalFourthData.Bq 6017
    have hp : val WuPaper.ClassicalFourthData.Bq 6017 = (261964554044305:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 6017 = 261964554044305 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 6017 = (14017:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_6017
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 6018) ≤ val WuPaper.ClassicalFourthData.Bq 6018
    have hp : val WuPaper.ClassicalFourthData.Bq 6018 = (261974351210031:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 6018 = 261974351210031 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 6018 = (7009:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_6018
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 6019) ≤ val WuPaper.ClassicalFourthData.Bq 6019
    have hp : val WuPaper.ClassicalFourthData.Bq 6019 = (261984144135032:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 6019 = 261984144135032 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 6019 = (14019:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_6019
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 6020) ≤ val WuPaper.ClassicalFourthData.Bq 6020
    have hp : val WuPaper.ClassicalFourthData.Bq 6020 = (261993932820784:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 6020 = 261993932820784 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 6020 = (701:ℝ)/200 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_6020
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 6021) ≤ val WuPaper.ClassicalFourthData.Bq 6021
    have hp : val WuPaper.ClassicalFourthData.Bq 6021 = (262003717268760:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 6021 = 262003717268760 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 6021 = (14021:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_6021
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 6022) ≤ val WuPaper.ClassicalFourthData.Bq 6022
    have hp : val WuPaper.ClassicalFourthData.Bq 6022 = (262013497480434:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 6022 = 262013497480434 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 6022 = (7011:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_6022
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 6023) ≤ val WuPaper.ClassicalFourthData.Bq 6023
    have hp : val WuPaper.ClassicalFourthData.Bq 6023 = (262023273457280:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 6023 = 262023273457280 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 6023 = (14023:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_6023
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 6024) ≤ val WuPaper.ClassicalFourthData.Bq 6024
    have hp : val WuPaper.ClassicalFourthData.Bq 6024 = (262033045200769:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 6024 = 262033045200769 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 6024 = (1753:ℝ)/500 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_6024
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 6025) ≤ val WuPaper.ClassicalFourthData.Bq 6025
    have hp : val WuPaper.ClassicalFourthData.Bq 6025 = (262042812712374:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 6025 = 262042812712374 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 6025 = (561:ℝ)/160 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_6025
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 6026) ≤ val WuPaper.ClassicalFourthData.Bq 6026
    have hp : val WuPaper.ClassicalFourthData.Bq 6026 = (262052575993566:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 6026 = 262052575993566 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 6026 = (7013:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_6026
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 6027) ≤ val WuPaper.ClassicalFourthData.Bq 6027
    have hp : val WuPaper.ClassicalFourthData.Bq 6027 = (262062335045817:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 6027 = 262062335045817 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 6027 = (14027:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_6027
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 6028) ≤ val WuPaper.ClassicalFourthData.Bq 6028
    have hp : val WuPaper.ClassicalFourthData.Bq 6028 = (262072089870595:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 6028 = 262072089870595 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 6028 = (3507:ℝ)/1000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_6028
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 6029) ≤ val WuPaper.ClassicalFourthData.Bq 6029
    have hp : val WuPaper.ClassicalFourthData.Bq 6029 = (262081840469371:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 6029 = 262081840469371 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 6029 = (14029:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_6029
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 6030) ≤ val WuPaper.ClassicalFourthData.Bq 6030
    have hp : val WuPaper.ClassicalFourthData.Bq 6030 = (262091586843613:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 6030 = 262091586843613 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 6030 = (1403:ℝ)/400 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_6030
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 6031) ≤ val WuPaper.ClassicalFourthData.Bq 6031
    have hp : val WuPaper.ClassicalFourthData.Bq 6031 = (262101328994791:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 6031 = 262101328994791 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 6031 = (14031:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_6031
end WuPaper.ClassicalFourthConditions
#print axioms WuPaper.ClassicalFourthConditions.Log_block_376

import WR2ClassicalFourthConditions
import WR2ClassicalFourthLogPoints650
noncomputable section
namespace WuPaper.ClassicalFourthConditions
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem Log_block_650 (j : Fin 16) (hj : 16*650+j.val < 10541) :
    WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 (16*650+j.val)) ≤ val WuPaper.ClassicalFourthData.Bq (16*650+j.val) := by
  fin_cases j
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 10400) ≤ val WuPaper.ClassicalFourthData.Bq 10400
    have hp : val WuPaper.ClassicalFourthData.Bq 10400 = (278463879486273:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 10400 = 278463879486273 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 10400 = (23:ℝ)/5 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_10400
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 10401) ≤ val WuPaper.ClassicalFourthData.Bq 10401
    have hp : val WuPaper.ClassicalFourthData.Bq 10401 = (278463841676084:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 10401 = 278463841676084 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 10401 = (18401:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_10401
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 10402) ≤ val WuPaper.ClassicalFourthData.Bq 10402
    have hp : val WuPaper.ClassicalFourthData.Bq 10402 = (278463802821888:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 10402 = 278463802821888 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 10402 = (9201:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_10402
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 10403) ≤ val WuPaper.ClassicalFourthData.Bq 10403
    have hp : val WuPaper.ClassicalFourthData.Bq 10403 = (278463762924000:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 10403 = 278463762924000 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 10403 = (18403:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_10403
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 10404) ≤ val WuPaper.ClassicalFourthData.Bq 10404
    have hp : val WuPaper.ClassicalFourthData.Bq 10404 = (278463721982736:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 10404 = 278463721982736 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 10404 = (4601:ℝ)/1000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_10404
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 10405) ≤ val WuPaper.ClassicalFourthData.Bq 10405
    have hp : val WuPaper.ClassicalFourthData.Bq 10405 = (278463679998411:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 10405 = 278463679998411 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 10405 = (3681:ℝ)/800 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_10405
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 10406) ≤ val WuPaper.ClassicalFourthData.Bq 10406
    have hp : val WuPaper.ClassicalFourthData.Bq 10406 = (278463636971342:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 10406 = 278463636971342 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 10406 = (9203:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_10406
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 10407) ≤ val WuPaper.ClassicalFourthData.Bq 10407
    have hp : val WuPaper.ClassicalFourthData.Bq 10407 = (278463592901843:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 10407 = 278463592901843 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 10407 = (18407:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_10407
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 10408) ≤ val WuPaper.ClassicalFourthData.Bq 10408
    have hp : val WuPaper.ClassicalFourthData.Bq 10408 = (278463547790229:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 10408 = 278463547790229 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 10408 = (2301:ℝ)/500 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_10408
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 10409) ≤ val WuPaper.ClassicalFourthData.Bq 10409
    have hp : val WuPaper.ClassicalFourthData.Bq 10409 = (278463501636816:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 10409 = 278463501636816 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 10409 = (18409:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_10409
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 10410) ≤ val WuPaper.ClassicalFourthData.Bq 10410
    have hp : val WuPaper.ClassicalFourthData.Bq 10410 = (278463454441919:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 10410 = 278463454441919 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 10410 = (1841:ℝ)/400 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_10410
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 10411) ≤ val WuPaper.ClassicalFourthData.Bq 10411
    have hp : val WuPaper.ClassicalFourthData.Bq 10411 = (278463406205853:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 10411 = 278463406205853 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 10411 = (18411:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_10411
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 10412) ≤ val WuPaper.ClassicalFourthData.Bq 10412
    have hp : val WuPaper.ClassicalFourthData.Bq 10412 = (278463356928932:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 10412 = 278463356928932 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 10412 = (4603:ℝ)/1000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_10412
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 10413) ≤ val WuPaper.ClassicalFourthData.Bq 10413
    have hp : val WuPaper.ClassicalFourthData.Bq 10413 = (278463306611472:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 10413 = 278463306611472 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 10413 = (18413:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_10413
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 10414) ≤ val WuPaper.ClassicalFourthData.Bq 10414
    have hp : val WuPaper.ClassicalFourthData.Bq 10414 = (278463255253786:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 10414 = 278463255253786 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 10414 = (9207:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_10414
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 10415) ≤ val WuPaper.ClassicalFourthData.Bq 10415
    have hp : val WuPaper.ClassicalFourthData.Bq 10415 = (278463202856190:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 10415 = 278463202856190 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 10415 = (3683:ℝ)/800 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_10415
end WuPaper.ClassicalFourthConditions
#print axioms WuPaper.ClassicalFourthConditions.Log_block_650

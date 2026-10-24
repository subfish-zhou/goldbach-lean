import WR2ClassicalFourthConditions
import WR2ClassicalFourthLogPoints025
noncomputable section
namespace WuPaper.ClassicalFourthConditions
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem Log_block_025 (j : Fin 16) (hj : 16*25+j.val < 10541) :
    WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 (16*25+j.val)) ≤ val WuPaper.ClassicalFourthData.Bq (16*25+j.val) := by
  fin_cases j
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 400) ≤ val WuPaper.ClassicalFourthData.Bq 400
    have hp : val WuPaper.ClassicalFourthData.Bq 400 = (45385799906822:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 400 = 45385799906822 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 400 = (21:ℝ)/10 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_400
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 401) ≤ val WuPaper.ClassicalFourthData.Bq 401
    have hp : val WuPaper.ClassicalFourthData.Bq 401 = (45488597409387:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 401 = 45488597409387 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 401 = (8401:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_401
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 402) ≤ val WuPaper.ClassicalFourthData.Bq 402
    have hp : val WuPaper.ClassicalFourthData.Bq 402 = (45591345862595:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 402 = 45591345862595 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 402 = (4201:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_402
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 403) ≤ val WuPaper.ClassicalFourthData.Bq 403
    have hp : val WuPaper.ClassicalFourthData.Bq 403 = (45694045295122:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 403 = 45694045295122 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 403 = (8403:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_403
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 404) ≤ val WuPaper.ClassicalFourthData.Bq 404
    have hp : val WuPaper.ClassicalFourthData.Bq 404 = (45796695735623:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 404 = 45796695735623 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 404 = (2101:ℝ)/1000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_404
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 405) ≤ val WuPaper.ClassicalFourthData.Bq 405
    have hp : val WuPaper.ClassicalFourthData.Bq 405 = (45899297212732:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 405 = 45899297212732 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 405 = (1681:ℝ)/800 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_405
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 406) ≤ val WuPaper.ClassicalFourthData.Bq 406
    have hp : val WuPaper.ClassicalFourthData.Bq 406 = (46001849755062:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 406 = 46001849755062 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 406 = (4203:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_406
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 407) ≤ val WuPaper.ClassicalFourthData.Bq 407
    have hp : val WuPaper.ClassicalFourthData.Bq 407 = (46104353391203:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 407 = 46104353391203 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 407 = (8407:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_407
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 408) ≤ val WuPaper.ClassicalFourthData.Bq 408
    have hp : val WuPaper.ClassicalFourthData.Bq 408 = (46206808149726:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 408 = 46206808149726 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 408 = (1051:ℝ)/500 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_408
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 409) ≤ val WuPaper.ClassicalFourthData.Bq 409
    have hp : val WuPaper.ClassicalFourthData.Bq 409 = (46309214059180:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 409 = 46309214059180 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 409 = (8409:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_409
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 410) ≤ val WuPaper.ClassicalFourthData.Bq 410
    have hp : val WuPaper.ClassicalFourthData.Bq 410 = (46411571148093:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 410 = 46411571148093 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 410 = (841:ℝ)/400 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_410
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 411) ≤ val WuPaper.ClassicalFourthData.Bq 411
    have hp : val WuPaper.ClassicalFourthData.Bq 411 = (46513879444971:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 411 = 46513879444971 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 411 = (8411:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_411
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 412) ≤ val WuPaper.ClassicalFourthData.Bq 412
    have hp : val WuPaper.ClassicalFourthData.Bq 412 = (46616138978301:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 412 = 46616138978301 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 412 = (2103:ℝ)/1000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_412
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 413) ≤ val WuPaper.ClassicalFourthData.Bq 413
    have hp : val WuPaper.ClassicalFourthData.Bq 413 = (46718349776546:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 413 = 46718349776546 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 413 = (8413:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_413
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 414) ≤ val WuPaper.ClassicalFourthData.Bq 414
    have hp : val WuPaper.ClassicalFourthData.Bq 414 = (46820511868151:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 414 = 46820511868151 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 414 = (4207:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_414
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 415) ≤ val WuPaper.ClassicalFourthData.Bq 415
    have hp : val WuPaper.ClassicalFourthData.Bq 415 = (46922625281537:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 415 = 46922625281537 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 415 = (1683:ℝ)/800 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_415
end WuPaper.ClassicalFourthConditions
#print axioms WuPaper.ClassicalFourthConditions.Log_block_025

import WR2ClassicalFourthConditions
import WR2ClassicalFourthLogPoints512
noncomputable section
namespace WuPaper.ClassicalFourthConditions
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem Log_block_512 (j : Fin 16) (hj : 16*512+j.val < 10541) :
    WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 (16*512+j.val)) ≤ val WuPaper.ClassicalFourthData.Bq (16*512+j.val) := by
  fin_cases j
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 8192) ≤ val WuPaper.ClassicalFourthData.Bq 8192
    have hp : val WuPaper.ClassicalFourthData.Bq 8192 = (275317598277717:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 8192 = 275317598277717 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 8192 = (506:ℝ)/125 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_8192
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 8193) ≤ val WuPaper.ClassicalFourthData.Bq 8193
    have hp : val WuPaper.ClassicalFourthData.Bq 8193 = (275320856039534:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 8193 = 275320856039534 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 8193 = (16193:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_8193
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 8194) ≤ val WuPaper.ClassicalFourthData.Bq 8194
    have hp : val WuPaper.ClassicalFourthData.Bq 8194 = (275324111737569:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 8194 = 275324111737569 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 8194 = (8097:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_8194
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 8195) ≤ val WuPaper.ClassicalFourthData.Bq 8195
    have hp : val WuPaper.ClassicalFourthData.Bq 8195 = (275327365372477:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 8195 = 275327365372477 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 8195 = (3239:ℝ)/800 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_8195
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 8196) ≤ val WuPaper.ClassicalFourthData.Bq 8196
    have hp : val WuPaper.ClassicalFourthData.Bq 8196 = (275330616944912:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 8196 = 275330616944912 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 8196 = (4049:ℝ)/1000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_8196
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 8197) ≤ val WuPaper.ClassicalFourthData.Bq 8197
    have hp : val WuPaper.ClassicalFourthData.Bq 8197 = (275333866455528:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 8197 = 275333866455528 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 8197 = (16197:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_8197
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 8198) ≤ val WuPaper.ClassicalFourthData.Bq 8198
    have hp : val WuPaper.ClassicalFourthData.Bq 8198 = (275337113904981:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 8198 = 275337113904981 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 8198 = (8099:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_8198
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 8199) ≤ val WuPaper.ClassicalFourthData.Bq 8199
    have hp : val WuPaper.ClassicalFourthData.Bq 8199 = (275340359293922:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 8199 = 275340359293922 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 8199 = (16199:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_8199
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 8200) ≤ val WuPaper.ClassicalFourthData.Bq 8200
    have hp : val WuPaper.ClassicalFourthData.Bq 8200 = (275343602623008:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 8200 = 275343602623008 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 8200 = (81:ℝ)/20 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_8200
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 8201) ≤ val WuPaper.ClassicalFourthData.Bq 8201
    have hp : val WuPaper.ClassicalFourthData.Bq 8201 = (275346843892889:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 8201 = 275346843892889 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 8201 = (16201:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_8201
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 8202) ≤ val WuPaper.ClassicalFourthData.Bq 8202
    have hp : val WuPaper.ClassicalFourthData.Bq 8202 = (275350083104221:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 8202 = 275350083104221 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 8202 = (8101:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_8202
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 8203) ≤ val WuPaper.ClassicalFourthData.Bq 8203
    have hp : val WuPaper.ClassicalFourthData.Bq 8203 = (275353320257655:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 8203 = 275353320257655 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 8203 = (16203:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_8203
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 8204) ≤ val WuPaper.ClassicalFourthData.Bq 8204
    have hp : val WuPaper.ClassicalFourthData.Bq 8204 = (275356555353845:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 8204 = 275356555353845 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 8204 = (4051:ℝ)/1000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_8204
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 8205) ≤ val WuPaper.ClassicalFourthData.Bq 8205
    have hp : val WuPaper.ClassicalFourthData.Bq 8205 = (275359788393442:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 8205 = 275359788393442 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 8205 = (3241:ℝ)/800 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_8205
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 8206) ≤ val WuPaper.ClassicalFourthData.Bq 8206
    have hp : val WuPaper.ClassicalFourthData.Bq 8206 = (275363019377100:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 8206 = 275363019377100 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 8206 = (8103:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_8206
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 8207) ≤ val WuPaper.ClassicalFourthData.Bq 8207
    have hp : val WuPaper.ClassicalFourthData.Bq 8207 = (275366248305470:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 8207 = 275366248305470 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 8207 = (16207:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_8207
end WuPaper.ClassicalFourthConditions
#print axioms WuPaper.ClassicalFourthConditions.Log_block_512

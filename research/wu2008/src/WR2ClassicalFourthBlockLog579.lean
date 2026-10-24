import WR2ClassicalFourthConditions
import WR2ClassicalFourthLogPoints579
noncomputable section
namespace WuPaper.ClassicalFourthConditions
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem Log_block_579 (j : Fin 16) (hj : 16*579+j.val < 10541) :
    WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 (16*579+j.val)) ≤ val WuPaper.ClassicalFourthData.Bq (16*579+j.val) := by
  fin_cases j
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 9264) ≤ val WuPaper.ClassicalFourthData.Bq 9264
    have hp : val WuPaper.ClassicalFourthData.Bq 9264 = (277747738021657:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 9264 = 277747738021657 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 9264 = (1079:ℝ)/250 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_9264
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 9265) ≤ val WuPaper.ClassicalFourthData.Bq 9265
    have hp : val WuPaper.ClassicalFourthData.Bq 9265 = (277749117057233:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 9265 = 277749117057233 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 9265 = (3453:ℝ)/800 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_9265
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 9266) ≤ val WuPaper.ClassicalFourthData.Bq 9266
    have hp : val WuPaper.ClassicalFourthData.Bq 9266 = (277750494616470:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 9266 = 277750494616470 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 9266 = (8633:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_9266
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 9267) ≤ val WuPaper.ClassicalFourthData.Bq 9267
    have hp : val WuPaper.ClassicalFourthData.Bq 9267 = (277751870699823:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 9267 = 277751870699823 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 9267 = (17267:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_9267
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 9268) ≤ val WuPaper.ClassicalFourthData.Bq 9268
    have hp : val WuPaper.ClassicalFourthData.Bq 9268 = (277753245307745:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 9268 = 277753245307745 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 9268 = (4317:ℝ)/1000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_9268
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 9269) ≤ val WuPaper.ClassicalFourthData.Bq 9269
    have hp : val WuPaper.ClassicalFourthData.Bq 9269 = (277754618440692:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 9269 = 277754618440692 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 9269 = (17269:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_9269
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 9270) ≤ val WuPaper.ClassicalFourthData.Bq 9270
    have hp : val WuPaper.ClassicalFourthData.Bq 9270 = (277755990099119:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 9270 = 277755990099119 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 9270 = (1727:ℝ)/400 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_9270
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 9271) ≤ val WuPaper.ClassicalFourthData.Bq 9271
    have hp : val WuPaper.ClassicalFourthData.Bq 9271 = (277757360283479:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 9271 = 277757360283479 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 9271 = (17271:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_9271
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 9272) ≤ val WuPaper.ClassicalFourthData.Bq 9272
    have hp : val WuPaper.ClassicalFourthData.Bq 9272 = (277758728994227:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 9272 = 277758728994227 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 9272 = (2159:ℝ)/500 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_9272
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 9273) ≤ val WuPaper.ClassicalFourthData.Bq 9273
    have hp : val WuPaper.ClassicalFourthData.Bq 9273 = (277760096231817:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 9273 = 277760096231817 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 9273 = (17273:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_9273
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 9274) ≤ val WuPaper.ClassicalFourthData.Bq 9274
    have hp : val WuPaper.ClassicalFourthData.Bq 9274 = (277761461996703:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 9274 = 277761461996703 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 9274 = (8637:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_9274
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 9275) ≤ val WuPaper.ClassicalFourthData.Bq 9275
    have hp : val WuPaper.ClassicalFourthData.Bq 9275 = (277762826289338:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 9275 = 277762826289338 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 9275 = (691:ℝ)/160 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_9275
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 9276) ≤ val WuPaper.ClassicalFourthData.Bq 9276
    have hp : val WuPaper.ClassicalFourthData.Bq 9276 = (277764189110177:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 9276 = 277764189110177 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 9276 = (4319:ℝ)/1000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_9276
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 9277) ≤ val WuPaper.ClassicalFourthData.Bq 9277
    have hp : val WuPaper.ClassicalFourthData.Bq 9277 = (277765550459673:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 9277 = 277765550459673 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 9277 = (17277:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_9277
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 9278) ≤ val WuPaper.ClassicalFourthData.Bq 9278
    have hp : val WuPaper.ClassicalFourthData.Bq 9278 = (277766910338279:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 9278 = 277766910338279 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 9278 = (8639:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_9278
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 9279) ≤ val WuPaper.ClassicalFourthData.Bq 9279
    have hp : val WuPaper.ClassicalFourthData.Bq 9279 = (277768268746448:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 9279 = 277768268746448 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 9279 = (17279:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_9279
end WuPaper.ClassicalFourthConditions
#print axioms WuPaper.ClassicalFourthConditions.Log_block_579

import WR2ClassicalFourthConditions
import WR2ClassicalFourthLogPoints517
noncomputable section
namespace WuPaper.ClassicalFourthConditions
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem Log_block_517 (j : Fin 16) (hj : 16*517+j.val < 10541) :
    WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 (16*517+j.val)) ≤ val WuPaper.ClassicalFourthData.Bq (16*517+j.val) := by
  fin_cases j
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 8272) ≤ val WuPaper.ClassicalFourthData.Bq 8272
    have hp : val WuPaper.ClassicalFourthData.Bq 8272 = (275571751108524:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 8272 = 275571751108524 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 8272 = (1017:ℝ)/250 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_8272
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 8273) ≤ val WuPaper.ClassicalFourthData.Bq 8273
    have hp : val WuPaper.ClassicalFourthData.Bq 8273 = (275574845818216:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 8273 = 275574845818216 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 8273 = (16273:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_8273
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 8274) ≤ val WuPaper.ClassicalFourthData.Bq 8274
    have hp : val WuPaper.ClassicalFourthData.Bq 8274 = (275577938515792:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 8274 = 275577938515792 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 8274 = (8137:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_8274
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 8275) ≤ val WuPaper.ClassicalFourthData.Bq 8275
    have hp : val WuPaper.ClassicalFourthData.Bq 8275 = (275581029201889:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 8275 = 275581029201889 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 8275 = (651:ℝ)/160 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_8275
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 8276) ≤ val WuPaper.ClassicalFourthData.Bq 8276
    have hp : val WuPaper.ClassicalFourthData.Bq 8276 = (275584117877145:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 8276 = 275584117877145 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 8276 = (4069:ℝ)/1000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_8276
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 8277) ≤ val WuPaper.ClassicalFourthData.Bq 8277
    have hp : val WuPaper.ClassicalFourthData.Bq 8277 = (275587204542194:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 8277 = 275587204542194 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 8277 = (16277:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_8277
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 8278) ≤ val WuPaper.ClassicalFourthData.Bq 8278
    have hp : val WuPaper.ClassicalFourthData.Bq 8278 = (275590289197674:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 8278 = 275590289197674 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 8278 = (8139:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_8278
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 8279) ≤ val WuPaper.ClassicalFourthData.Bq 8279
    have hp : val WuPaper.ClassicalFourthData.Bq 8279 = (275593371844220:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 8279 = 275593371844220 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 8279 = (16279:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_8279
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 8280) ≤ val WuPaper.ClassicalFourthData.Bq 8280
    have hp : val WuPaper.ClassicalFourthData.Bq 8280 = (275596452482468:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 8280 = 275596452482468 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 8280 = (407:ℝ)/100 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_8280
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 8281) ≤ val WuPaper.ClassicalFourthData.Bq 8281
    have hp : val WuPaper.ClassicalFourthData.Bq 8281 = (275599531113053:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 8281 = 275599531113053 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 8281 = (16281:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_8281
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 8282) ≤ val WuPaper.ClassicalFourthData.Bq 8282
    have hp : val WuPaper.ClassicalFourthData.Bq 8282 = (275602607736611:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 8282 = 275602607736611 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 8282 = (8141:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_8282
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 8283) ≤ val WuPaper.ClassicalFourthData.Bq 8283
    have hp : val WuPaper.ClassicalFourthData.Bq 8283 = (275605682353776:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 8283 = 275605682353776 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 8283 = (16283:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_8283
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 8284) ≤ val WuPaper.ClassicalFourthData.Bq 8284
    have hp : val WuPaper.ClassicalFourthData.Bq 8284 = (275608754965183:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 8284 = 275608754965183 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 8284 = (4071:ℝ)/1000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_8284
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 8285) ≤ val WuPaper.ClassicalFourthData.Bq 8285
    have hp : val WuPaper.ClassicalFourthData.Bq 8285 = (275611825571467:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 8285 = 275611825571467 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 8285 = (3257:ℝ)/800 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_8285
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 8286) ≤ val WuPaper.ClassicalFourthData.Bq 8286
    have hp : val WuPaper.ClassicalFourthData.Bq 8286 = (275614894173263:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 8286 = 275614894173263 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 8286 = (8143:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_8286
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 8287) ≤ val WuPaper.ClassicalFourthData.Bq 8287
    have hp : val WuPaper.ClassicalFourthData.Bq 8287 = (275617960771203:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 8287 = 275617960771203 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 8287 = (16287:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_8287
end WuPaper.ClassicalFourthConditions
#print axioms WuPaper.ClassicalFourthConditions.Log_block_517

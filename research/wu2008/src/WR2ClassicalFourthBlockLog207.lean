import WR2ClassicalFourthConditions
import WR2ClassicalFourthLogPoints207
noncomputable section
namespace WuPaper.ClassicalFourthConditions
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem Log_block_207 (j : Fin 16) (hj : 16*207+j.val < 10541) :
    WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 (16*207+j.val)) ≤ val WuPaper.ClassicalFourthData.Bq (16*207+j.val) := by
  fin_cases j
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 3312) ≤ val WuPaper.ClassicalFourthData.Bq 3312
    have hp : val WuPaper.ClassicalFourthData.Bq 3312 = (213303561892489:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 3312 = 213303561892489 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 3312 = (707:ℝ)/250 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_3312
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 3313) ≤ val WuPaper.ClassicalFourthData.Bq 3313
    have hp : val WuPaper.ClassicalFourthData.Bq 3313 = (213333059372023:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 3313 = 213333059372023 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 3313 = (11313:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_3313
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 3314) ≤ val WuPaper.ClassicalFourthData.Bq 3314
    have hp : val WuPaper.ClassicalFourthData.Bq 3314 = (213362545026445:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 3314 = 213362545026445 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 3314 = (5657:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_3314
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 3315) ≤ val WuPaper.ClassicalFourthData.Bq 3315
    have hp : val WuPaper.ClassicalFourthData.Bq 3315 = (213392018860698:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 3315 = 213392018860698 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 3315 = (2263:ℝ)/800 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_3315
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 3316) ≤ val WuPaper.ClassicalFourthData.Bq 3316
    have hp : val WuPaper.ClassicalFourthData.Bq 3316 = (213421480879721:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 3316 = 213421480879721 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 3316 = (2829:ℝ)/1000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_3316
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 3317) ≤ val WuPaper.ClassicalFourthData.Bq 3317
    have hp : val WuPaper.ClassicalFourthData.Bq 3317 = (213450931088452:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 3317 = 213450931088452 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 3317 = (11317:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_3317
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 3318) ≤ val WuPaper.ClassicalFourthData.Bq 3318
    have hp : val WuPaper.ClassicalFourthData.Bq 3318 = (213480369491827:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 3318 = 213480369491827 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 3318 = (5659:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_3318
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 3319) ≤ val WuPaper.ClassicalFourthData.Bq 3319
    have hp : val WuPaper.ClassicalFourthData.Bq 3319 = (213509796094779:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 3319 = 213509796094779 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 3319 = (11319:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_3319
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 3320) ≤ val WuPaper.ClassicalFourthData.Bq 3320
    have hp : val WuPaper.ClassicalFourthData.Bq 3320 = (213539210902237:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 3320 = 213539210902237 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 3320 = (283:ℝ)/100 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_3320
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 3321) ≤ val WuPaper.ClassicalFourthData.Bq 3321
    have hp : val WuPaper.ClassicalFourthData.Bq 3321 = (213568613919130:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 3321 = 213568613919130 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 3321 = (11321:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_3321
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 3322) ≤ val WuPaper.ClassicalFourthData.Bq 3322
    have hp : val WuPaper.ClassicalFourthData.Bq 3322 = (213598005150382:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 3322 = 213598005150382 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 3322 = (5661:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_3322
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 3323) ≤ val WuPaper.ClassicalFourthData.Bq 3323
    have hp : val WuPaper.ClassicalFourthData.Bq 3323 = (213627384600916:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 3323 = 213627384600916 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 3323 = (11323:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_3323
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 3324) ≤ val WuPaper.ClassicalFourthData.Bq 3324
    have hp : val WuPaper.ClassicalFourthData.Bq 3324 = (213656752275654:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 3324 = 213656752275654 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 3324 = (2831:ℝ)/1000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_3324
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 3325) ≤ val WuPaper.ClassicalFourthData.Bq 3325
    have hp : val WuPaper.ClassicalFourthData.Bq 3325 = (213686108179511:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 3325 = 213686108179511 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 3325 = (453:ℝ)/160 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_3325
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 3326) ≤ val WuPaper.ClassicalFourthData.Bq 3326
    have hp : val WuPaper.ClassicalFourthData.Bq 3326 = (213715452317405:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 3326 = 213715452317405 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 3326 = (5663:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_3326
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 3327) ≤ val WuPaper.ClassicalFourthData.Bq 3327
    have hp : val WuPaper.ClassicalFourthData.Bq 3327 = (213744784694248:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 3327 = 213744784694248 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 3327 = (11327:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_3327
end WuPaper.ClassicalFourthConditions
#print axioms WuPaper.ClassicalFourthConditions.Log_block_207

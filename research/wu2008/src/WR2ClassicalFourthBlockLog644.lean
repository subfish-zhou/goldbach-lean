import WR2ClassicalFourthConditions
import WR2ClassicalFourthLogPoints644
noncomputable section
namespace WuPaper.ClassicalFourthConditions
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem Log_block_644 (j : Fin 16) (hj : 16*644+j.val < 10541) :
    WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 (16*644+j.val)) ≤ val WuPaper.ClassicalFourthData.Bq (16*644+j.val) := by
  fin_cases j
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 10304) ≤ val WuPaper.ClassicalFourthData.Bq 10304
    have hp : val WuPaper.ClassicalFourthData.Bq 10304 = (278462599970017:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 10304 = 278462599970017 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 10304 = (572:ℝ)/125 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_10304
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 10305) ≤ val WuPaper.ClassicalFourthData.Bq 10305
    have hp : val WuPaper.ClassicalFourthData.Bq 10305 = (278462663869749:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 10305 = 278462663869749 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 10305 = (3661:ℝ)/800 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_10305
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 10306) ≤ val WuPaper.ClassicalFourthData.Bq 10306
    have hp : val WuPaper.ClassicalFourthData.Bq 10306 = (278462726694698:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 10306 = 278462726694698 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 10306 = (9153:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_10306
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 10307) ≤ val WuPaper.ClassicalFourthData.Bq 10307
    have hp : val WuPaper.ClassicalFourthData.Bq 10307 = (278462788445189:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 10307 = 278462788445189 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 10307 = (18307:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_10307
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 10308) ≤ val WuPaper.ClassicalFourthData.Bq 10308
    have hp : val WuPaper.ClassicalFourthData.Bq 10308 = (278462849121547:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 10308 = 278462849121547 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 10308 = (4577:ℝ)/1000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_10308
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 10309) ≤ val WuPaper.ClassicalFourthData.Bq 10309
    have hp : val WuPaper.ClassicalFourthData.Bq 10309 = (278462908724097:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 10309 = 278462908724097 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 10309 = (18309:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_10309
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 10310) ≤ val WuPaper.ClassicalFourthData.Bq 10310
    have hp : val WuPaper.ClassicalFourthData.Bq 10310 = (278462967253165:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 10310 = 278462967253165 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 10310 = (1831:ℝ)/400 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_10310
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 10311) ≤ val WuPaper.ClassicalFourthData.Bq 10311
    have hp : val WuPaper.ClassicalFourthData.Bq 10311 = (278463024709076:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 10311 = 278463024709076 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 10311 = (18311:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_10311
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 10312) ≤ val WuPaper.ClassicalFourthData.Bq 10312
    have hp : val WuPaper.ClassicalFourthData.Bq 10312 = (278463081092154:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 10312 = 278463081092154 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 10312 = (2289:ℝ)/500 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_10312
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 10313) ≤ val WuPaper.ClassicalFourthData.Bq 10313
    have hp : val WuPaper.ClassicalFourthData.Bq 10313 = (278463136402724:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 10313 = 278463136402724 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 10313 = (18313:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_10313
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 10314) ≤ val WuPaper.ClassicalFourthData.Bq 10314
    have hp : val WuPaper.ClassicalFourthData.Bq 10314 = (278463190641111:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 10314 = 278463190641111 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 10314 = (9157:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_10314
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 10315) ≤ val WuPaper.ClassicalFourthData.Bq 10315
    have hp : val WuPaper.ClassicalFourthData.Bq 10315 = (278463243807640:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 10315 = 278463243807640 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 10315 = (3663:ℝ)/800 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_10315
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 10316) ≤ val WuPaper.ClassicalFourthData.Bq 10316
    have hp : val WuPaper.ClassicalFourthData.Bq 10316 = (278463295902634:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 10316 = 278463295902634 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 10316 = (4579:ℝ)/1000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_10316
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 10317) ≤ val WuPaper.ClassicalFourthData.Bq 10317
    have hp : val WuPaper.ClassicalFourthData.Bq 10317 = (278463346926419:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 10317 = 278463346926419 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 10317 = (18317:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_10317
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 10318) ≤ val WuPaper.ClassicalFourthData.Bq 10318
    have hp : val WuPaper.ClassicalFourthData.Bq 10318 = (278463396879318:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 10318 = 278463396879318 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 10318 = (9159:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_10318
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 10319) ≤ val WuPaper.ClassicalFourthData.Bq 10319
    have hp : val WuPaper.ClassicalFourthData.Bq 10319 = (278463445761656:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 10319 = 278463445761656 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 10319 = (18319:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_10319
end WuPaper.ClassicalFourthConditions
#print axioms WuPaper.ClassicalFourthConditions.Log_block_644

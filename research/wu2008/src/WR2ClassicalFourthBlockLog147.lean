import WR2ClassicalFourthConditions
import WR2ClassicalFourthLogPoints147
noncomputable section
namespace WuPaper.ClassicalFourthConditions
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem Log_block_147 (j : Fin 16) (hj : 16*147+j.val < 10541) :
    WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 (16*147+j.val)) ≤ val WuPaper.ClassicalFourthData.Bq (16*147+j.val) := by
  fin_cases j
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 2352) ≤ val WuPaper.ClassicalFourthData.Bq 2352
    have hp : val WuPaper.ClassicalFourthData.Bq 2352 = (178699908355852:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 2352 = 178699908355852 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 2352 = (647:ℝ)/250 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_2352
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 2353) ≤ val WuPaper.ClassicalFourthData.Bq 2353
    have hp : val WuPaper.ClassicalFourthData.Bq 2353 = (178743468043855:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 2353 = 178743468043855 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 2353 = (10353:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_2353
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 2354) ≤ val WuPaper.ClassicalFourthData.Bq 2354
    have hp : val WuPaper.ClassicalFourthData.Bq 2354 = (178787009745967:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 2354 = 178787009745967 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 2354 = (5177:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_2354
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 2355) ≤ val WuPaper.ClassicalFourthData.Bq 2355
    have hp : val WuPaper.ClassicalFourthData.Bq 2355 = (178830533470412:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 2355 = 178830533470412 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 2355 = (2071:ℝ)/800 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_2355
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 2356) ≤ val WuPaper.ClassicalFourthData.Bq 2356
    have hp : val WuPaper.ClassicalFourthData.Bq 2356 = (178874039225408:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 2356 = 178874039225408 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 2356 = (2589:ℝ)/1000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_2356
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 2357) ≤ val WuPaper.ClassicalFourthData.Bq 2357
    have hp : val WuPaper.ClassicalFourthData.Bq 2357 = (178917527019169:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 2357 = 178917527019169 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 2357 = (10357:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_2357
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 2358) ≤ val WuPaper.ClassicalFourthData.Bq 2358
    have hp : val WuPaper.ClassicalFourthData.Bq 2358 = (178960996859904:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 2358 = 178960996859904 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 2358 = (5179:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_2358
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 2359) ≤ val WuPaper.ClassicalFourthData.Bq 2359
    have hp : val WuPaper.ClassicalFourthData.Bq 2359 = (179004448755819:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 2359 = 179004448755819 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 2359 = (10359:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_2359
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 2360) ≤ val WuPaper.ClassicalFourthData.Bq 2360
    have hp : val WuPaper.ClassicalFourthData.Bq 2360 = (179047882715113:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 2360 = 179047882715113 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 2360 = (259:ℝ)/100 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_2360
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 2361) ≤ val WuPaper.ClassicalFourthData.Bq 2361
    have hp : val WuPaper.ClassicalFourthData.Bq 2361 = (179091298745981:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 2361 = 179091298745981 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 2361 = (10361:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_2361
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 2362) ≤ val WuPaper.ClassicalFourthData.Bq 2362
    have hp : val WuPaper.ClassicalFourthData.Bq 2362 = (179134696856616:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 2362 = 179134696856616 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 2362 = (5181:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_2362
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 2363) ≤ val WuPaper.ClassicalFourthData.Bq 2363
    have hp : val WuPaper.ClassicalFourthData.Bq 2363 = (179178077055202:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 2363 = 179178077055202 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 2363 = (10363:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_2363
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 2364) ≤ val WuPaper.ClassicalFourthData.Bq 2364
    have hp : val WuPaper.ClassicalFourthData.Bq 2364 = (179221439349923:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 2364 = 179221439349923 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 2364 = (2591:ℝ)/1000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_2364
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 2365) ≤ val WuPaper.ClassicalFourthData.Bq 2365
    have hp : val WuPaper.ClassicalFourthData.Bq 2365 = (179264783748955:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 2365 = 179264783748955 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 2365 = (2073:ℝ)/800 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_2365
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 2366) ≤ val WuPaper.ClassicalFourthData.Bq 2366
    have hp : val WuPaper.ClassicalFourthData.Bq 2366 = (179308110260471:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 2366 = 179308110260471 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 2366 = (5183:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_2366
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 2367) ≤ val WuPaper.ClassicalFourthData.Bq 2367
    have hp : val WuPaper.ClassicalFourthData.Bq 2367 = (179351418892640:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 2367 = 179351418892640 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 2367 = (10367:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_2367
end WuPaper.ClassicalFourthConditions
#print axioms WuPaper.ClassicalFourthConditions.Log_block_147

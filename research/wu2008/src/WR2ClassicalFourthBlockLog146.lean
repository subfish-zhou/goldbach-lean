import WR2ClassicalFourthConditions
import WR2ClassicalFourthLogPoints146
noncomputable section
namespace WuPaper.ClassicalFourthConditions
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem Log_block_146 (j : Fin 16) (hj : 16*146+j.val < 10541) :
    WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 (16*146+j.val)) ≤ val WuPaper.ClassicalFourthData.Bq (16*146+j.val) := by
  fin_cases j
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 2336) ≤ val WuPaper.ClassicalFourthData.Bq 2336
    have hp : val WuPaper.ClassicalFourthData.Bq 2336 = (178000500538791:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 2336 = 178000500538791 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 2336 = (323:ℝ)/125 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_2336
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 2337) ≤ val WuPaper.ClassicalFourthData.Bq 2337
    have hp : val WuPaper.ClassicalFourthData.Bq 2337 = (178044349123146:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 2337 = 178044349123146 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 2337 = (10337:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_2337
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 2338) ≤ val WuPaper.ClassicalFourthData.Bq 2338
    have hp : val WuPaper.ClassicalFourthData.Bq 2338 = (178088179589414:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 2338 = 178088179589414 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 2338 = (5169:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_2338
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 2339) ≤ val WuPaper.ClassicalFourthData.Bq 2339
    have hp : val WuPaper.ClassicalFourthData.Bq 2339 = (178131991945890:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 2339 = 178131991945890 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 2339 = (10339:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_2339
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 2340) ≤ val WuPaper.ClassicalFourthData.Bq 2340
    have hp : val WuPaper.ClassicalFourthData.Bq 2340 = (178175786200869:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 2340 = 178175786200869 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 2340 = (517:ℝ)/200 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_2340
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 2341) ≤ val WuPaper.ClassicalFourthData.Bq 2341
    have hp : val WuPaper.ClassicalFourthData.Bq 2341 = (178219562362636:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 2341 = 178219562362636 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 2341 = (10341:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_2341
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 2342) ≤ val WuPaper.ClassicalFourthData.Bq 2342
    have hp : val WuPaper.ClassicalFourthData.Bq 2342 = (178263320439476:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 2342 = 178263320439476 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 2342 = (5171:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_2342
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 2343) ≤ val WuPaper.ClassicalFourthData.Bq 2343
    have hp : val WuPaper.ClassicalFourthData.Bq 2343 = (178307060439668:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 2343 = 178307060439668 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 2343 = (10343:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_2343
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 2344) ≤ val WuPaper.ClassicalFourthData.Bq 2344
    have hp : val WuPaper.ClassicalFourthData.Bq 2344 = (178350782371484:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 2344 = 178350782371484 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 2344 = (1293:ℝ)/500 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_2344
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 2345) ≤ val WuPaper.ClassicalFourthData.Bq 2345
    have hp : val WuPaper.ClassicalFourthData.Bq 2345 = (178394486243194:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 2345 = 178394486243194 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 2345 = (2069:ℝ)/800 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_2345
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 2346) ≤ val WuPaper.ClassicalFourthData.Bq 2346
    have hp : val WuPaper.ClassicalFourthData.Bq 2346 = (178438172063064:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 2346 = 178438172063064 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 2346 = (5173:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_2346
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 2347) ≤ val WuPaper.ClassicalFourthData.Bq 2347
    have hp : val WuPaper.ClassicalFourthData.Bq 2347 = (178481839839352:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 2347 = 178481839839352 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 2347 = (10347:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_2347
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 2348) ≤ val WuPaper.ClassicalFourthData.Bq 2348
    have hp : val WuPaper.ClassicalFourthData.Bq 2348 = (178525489580314:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 2348 = 178525489580314 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 2348 = (2587:ℝ)/1000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_2348
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 2349) ≤ val WuPaper.ClassicalFourthData.Bq 2349
    have hp : val WuPaper.ClassicalFourthData.Bq 2349 = (178569121294202:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 2349 = 178569121294202 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 2349 = (10349:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_2349
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 2350) ≤ val WuPaper.ClassicalFourthData.Bq 2350
    have hp : val WuPaper.ClassicalFourthData.Bq 2350 = (178612734989260:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 2350 = 178612734989260 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 2350 = (207:ℝ)/80 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_2350
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 2351) ≤ val WuPaper.ClassicalFourthData.Bq 2351
    have hp : val WuPaper.ClassicalFourthData.Bq 2351 = (178656330673731:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 2351 = 178656330673731 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 2351 = (10351:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_2351
end WuPaper.ClassicalFourthConditions
#print axioms WuPaper.ClassicalFourthConditions.Log_block_146

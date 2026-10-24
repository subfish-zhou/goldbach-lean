import WR2ClassicalFourthConditions
import WR2ClassicalFourthLogPoints144
noncomputable section
namespace WuPaper.ClassicalFourthConditions
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem Log_block_144 (j : Fin 16) (hj : 16*144+j.val < 10541) :
    WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 (16*144+j.val)) ≤ val WuPaper.ClassicalFourthData.Bq (16*144+j.val) := by
  fin_cases j
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 2304) ≤ val WuPaper.ClassicalFourthData.Bq 2304
    have hp : val WuPaper.ClassicalFourthData.Bq 2304 = (176587729594600:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 2304 = 176587729594600 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 2304 = (322:ℝ)/125 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_2304
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 2305) ≤ val WuPaper.ClassicalFourthData.Bq 2305
    have hp : val WuPaper.ClassicalFourthData.Bq 2305 = (176632162366616:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 2305 = 176632162366616 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 2305 = (2061:ℝ)/800 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_2305
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 2306) ≤ val WuPaper.ClassicalFourthData.Bq 2306
    have hp : val WuPaper.ClassicalFourthData.Bq 2306 = (176676576752563:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 2306 = 176676576752563 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 2306 = (5153:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_2306
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 2307) ≤ val WuPaper.ClassicalFourthData.Bq 2307
    have hp : val WuPaper.ClassicalFourthData.Bq 2307 = (176720972760891:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 2307 = 176720972760891 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 2307 = (10307:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_2307
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 2308) ≤ val WuPaper.ClassicalFourthData.Bq 2308
    have hp : val WuPaper.ClassicalFourthData.Bq 2308 = (176765350400040:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 2308 = 176765350400040 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 2308 = (2577:ℝ)/1000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_2308
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 2309) ≤ val WuPaper.ClassicalFourthData.Bq 2309
    have hp : val WuPaper.ClassicalFourthData.Bq 2309 = (176809709678449:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 2309 = 176809709678449 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 2309 = (10309:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_2309
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 2310) ≤ val WuPaper.ClassicalFourthData.Bq 2310
    have hp : val WuPaper.ClassicalFourthData.Bq 2310 = (176854050604552:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 2310 = 176854050604552 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 2310 = (1031:ℝ)/400 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_2310
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 2311) ≤ val WuPaper.ClassicalFourthData.Bq 2311
    have hp : val WuPaper.ClassicalFourthData.Bq 2311 = (176898373186777:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 2311 = 176898373186777 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 2311 = (10311:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_2311
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 2312) ≤ val WuPaper.ClassicalFourthData.Bq 2312
    have hp : val WuPaper.ClassicalFourthData.Bq 2312 = (176942677433547:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 2312 = 176942677433547 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 2312 = (1289:ℝ)/500 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_2312
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 2313) ≤ val WuPaper.ClassicalFourthData.Bq 2313
    have hp : val WuPaper.ClassicalFourthData.Bq 2313 = (176986963353282:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 2313 = 176986963353282 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 2313 = (10313:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_2313
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 2314) ≤ val WuPaper.ClassicalFourthData.Bq 2314
    have hp : val WuPaper.ClassicalFourthData.Bq 2314 = (177031230954396:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 2314 = 177031230954396 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 2314 = (5157:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_2314
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 2315) ≤ val WuPaper.ClassicalFourthData.Bq 2315
    have hp : val WuPaper.ClassicalFourthData.Bq 2315 = (177075480245299:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 2315 = 177075480245299 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 2315 = (2063:ℝ)/800 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_2315
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 2316) ≤ val WuPaper.ClassicalFourthData.Bq 2316
    have hp : val WuPaper.ClassicalFourthData.Bq 2316 = (177119711234396:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 2316 = 177119711234396 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 2316 = (2579:ℝ)/1000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_2316
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 2317) ≤ val WuPaper.ClassicalFourthData.Bq 2317
    have hp : val WuPaper.ClassicalFourthData.Bq 2317 = (177163923930086:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 2317 = 177163923930086 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 2317 = (10317:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_2317
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 2318) ≤ val WuPaper.ClassicalFourthData.Bq 2318
    have hp : val WuPaper.ClassicalFourthData.Bq 2318 = (177208118340765:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 2318 = 177208118340765 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 2318 = (5159:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_2318
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 2319) ≤ val WuPaper.ClassicalFourthData.Bq 2319
    have hp : val WuPaper.ClassicalFourthData.Bq 2319 = (177252294474825:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 2319 = 177252294474825 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 2319 = (10319:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_2319
end WuPaper.ClassicalFourthConditions
#print axioms WuPaper.ClassicalFourthConditions.Log_block_144

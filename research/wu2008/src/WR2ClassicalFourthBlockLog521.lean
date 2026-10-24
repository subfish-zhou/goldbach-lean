import WR2ClassicalFourthConditions
import WR2ClassicalFourthLogPoints521
noncomputable section
namespace WuPaper.ClassicalFourthConditions
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem Log_block_521 (j : Fin 16) (hj : 16*521+j.val < 10541) :
    WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 (16*521+j.val)) ≤ val WuPaper.ClassicalFourthData.Bq (16*521+j.val) := by
  fin_cases j
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 8336) ≤ val WuPaper.ClassicalFourthData.Bq 8336
    have hp : val WuPaper.ClassicalFourthData.Bq 8336 = (275765782494162:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 8336 = 275765782494162 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 8336 = (1021:ℝ)/250 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_8336
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 8337) ≤ val WuPaper.ClassicalFourthData.Bq 8337
    have hp : val WuPaper.ClassicalFourthData.Bq 8337 = (275768749703011:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 8337 = 275768749703011 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 8337 = (16337:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_8337
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 8338) ≤ val WuPaper.ClassicalFourthData.Bq 8338
    have hp : val WuPaper.ClassicalFourthData.Bq 8338 = (275771714940055:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 8338 = 275771714940055 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 8338 = (8169:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_8338
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 8339) ≤ val WuPaper.ClassicalFourthData.Bq 8339
    have hp : val WuPaper.ClassicalFourthData.Bq 8339 = (275774678205915:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 8339 = 275774678205915 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 8339 = (16339:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_8339
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 8340) ≤ val WuPaper.ClassicalFourthData.Bq 8340
    have hp : val WuPaper.ClassicalFourthData.Bq 8340 = (275777639501216:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 8340 = 275777639501216 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 8340 = (817:ℝ)/200 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_8340
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 8341) ≤ val WuPaper.ClassicalFourthData.Bq 8341
    have hp : val WuPaper.ClassicalFourthData.Bq 8341 = (275780598826579:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 8341 = 275780598826579 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 8341 = (16341:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_8341
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 8342) ≤ val WuPaper.ClassicalFourthData.Bq 8342
    have hp : val WuPaper.ClassicalFourthData.Bq 8342 = (275783556182627:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 8342 = 275783556182627 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 8342 = (8171:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_8342
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 8343) ≤ val WuPaper.ClassicalFourthData.Bq 8343
    have hp : val WuPaper.ClassicalFourthData.Bq 8343 = (275786511569981:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 8343 = 275786511569981 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 8343 = (16343:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_8343
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 8344) ≤ val WuPaper.ClassicalFourthData.Bq 8344
    have hp : val WuPaper.ClassicalFourthData.Bq 8344 = (275789464989263:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 8344 = 275789464989263 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 8344 = (2043:ℝ)/500 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_8344
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 8345) ≤ val WuPaper.ClassicalFourthData.Bq 8345
    have hp : val WuPaper.ClassicalFourthData.Bq 8345 = (275792416441094:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 8345 = 275792416441094 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 8345 = (3269:ℝ)/800 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_8345
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 8346) ≤ val WuPaper.ClassicalFourthData.Bq 8346
    have hp : val WuPaper.ClassicalFourthData.Bq 8346 = (275795365926096:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 8346 = 275795365926096 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 8346 = (8173:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_8346
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 8347) ≤ val WuPaper.ClassicalFourthData.Bq 8347
    have hp : val WuPaper.ClassicalFourthData.Bq 8347 = (275798313444890:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 8347 = 275798313444890 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 8347 = (16347:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_8347
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 8348) ≤ val WuPaper.ClassicalFourthData.Bq 8348
    have hp : val WuPaper.ClassicalFourthData.Bq 8348 = (275801258998097:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 8348 = 275801258998097 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 8348 = (4087:ℝ)/1000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_8348
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 8349) ≤ val WuPaper.ClassicalFourthData.Bq 8349
    have hp : val WuPaper.ClassicalFourthData.Bq 8349 = (275804202586337:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 8349 = 275804202586337 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 8349 = (16349:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_8349
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 8350) ≤ val WuPaper.ClassicalFourthData.Bq 8350
    have hp : val WuPaper.ClassicalFourthData.Bq 8350 = (275807144210230:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 8350 = 275807144210230 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 8350 = (327:ℝ)/80 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_8350
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 8351) ≤ val WuPaper.ClassicalFourthData.Bq 8351
    have hp : val WuPaper.ClassicalFourthData.Bq 8351 = (275810083870397:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 8351 = 275810083870397 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 8351 = (16351:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_8351
end WuPaper.ClassicalFourthConditions
#print axioms WuPaper.ClassicalFourthConditions.Log_block_521

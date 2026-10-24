import WR2ClassicalFourthConditions
import WR2ClassicalFourthLogPoints522
noncomputable section
namespace WuPaper.ClassicalFourthConditions
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem Log_block_522 (j : Fin 16) (hj : 16*522+j.val < 10541) :
    WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 (16*522+j.val)) ≤ val WuPaper.ClassicalFourthData.Bq (16*522+j.val) := by
  fin_cases j
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 8352) ≤ val WuPaper.ClassicalFourthData.Bq 8352
    have hp : val WuPaper.ClassicalFourthData.Bq 8352 = (275813021567459:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 8352 = 275813021567459 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 8352 = (511:ℝ)/125 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_8352
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 8353) ≤ val WuPaper.ClassicalFourthData.Bq 8353
    have hp : val WuPaper.ClassicalFourthData.Bq 8353 = (275815957302033:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 8353 = 275815957302033 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 8353 = (16353:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_8353
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 8354) ≤ val WuPaper.ClassicalFourthData.Bq 8354
    have hp : val WuPaper.ClassicalFourthData.Bq 8354 = (275818891074741:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 8354 = 275818891074741 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 8354 = (8177:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_8354
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 8355) ≤ val WuPaper.ClassicalFourthData.Bq 8355
    have hp : val WuPaper.ClassicalFourthData.Bq 8355 = (275821822886201:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 8355 = 275821822886201 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 8355 = (3271:ℝ)/800 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_8355
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 8356) ≤ val WuPaper.ClassicalFourthData.Bq 8356
    have hp : val WuPaper.ClassicalFourthData.Bq 8356 = (275824752737033:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 8356 = 275824752737033 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 8356 = (4089:ℝ)/1000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_8356
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 8357) ≤ val WuPaper.ClassicalFourthData.Bq 8357
    have hp : val WuPaper.ClassicalFourthData.Bq 8357 = (275827680627855:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 8357 = 275827680627855 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 8357 = (16357:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_8357
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 8358) ≤ val WuPaper.ClassicalFourthData.Bq 8358
    have hp : val WuPaper.ClassicalFourthData.Bq 8358 = (275830606559286:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 8358 = 275830606559286 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 8358 = (8179:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_8358
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 8359) ≤ val WuPaper.ClassicalFourthData.Bq 8359
    have hp : val WuPaper.ClassicalFourthData.Bq 8359 = (275833530531945:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 8359 = 275833530531945 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 8359 = (16359:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_8359
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 8360) ≤ val WuPaper.ClassicalFourthData.Bq 8360
    have hp : val WuPaper.ClassicalFourthData.Bq 8360 = (275836452546450:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 8360 = 275836452546450 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 8360 = (409:ℝ)/100 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_8360
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 8361) ≤ val WuPaper.ClassicalFourthData.Bq 8361
    have hp : val WuPaper.ClassicalFourthData.Bq 8361 = (275839372603418:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 8361 = 275839372603418 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 8361 = (16361:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_8361
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 8362) ≤ val WuPaper.ClassicalFourthData.Bq 8362
    have hp : val WuPaper.ClassicalFourthData.Bq 8362 = (275842290703468:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 8362 = 275842290703468 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 8362 = (8181:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_8362
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 8363) ≤ val WuPaper.ClassicalFourthData.Bq 8363
    have hp : val WuPaper.ClassicalFourthData.Bq 8363 = (275845206847218:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 8363 = 275845206847218 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 8363 = (16363:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_8363
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 8364) ≤ val WuPaper.ClassicalFourthData.Bq 8364
    have hp : val WuPaper.ClassicalFourthData.Bq 8364 = (275848121035284:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 8364 = 275848121035284 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 8364 = (4091:ℝ)/1000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_8364
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 8365) ≤ val WuPaper.ClassicalFourthData.Bq 8365
    have hp : val WuPaper.ClassicalFourthData.Bq 8365 = (275851033268284:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 8365 = 275851033268284 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 8365 = (3273:ℝ)/800 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_8365
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 8366) ≤ val WuPaper.ClassicalFourthData.Bq 8366
    have hp : val WuPaper.ClassicalFourthData.Bq 8366 = (275853943546835:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 8366 = 275853943546835 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 8366 = (8183:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_8366
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 8367) ≤ val WuPaper.ClassicalFourthData.Bq 8367
    have hp : val WuPaper.ClassicalFourthData.Bq 8367 = (275856851871553:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 8367 = 275856851871553 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 8367 = (16367:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_8367
end WuPaper.ClassicalFourthConditions
#print axioms WuPaper.ClassicalFourthConditions.Log_block_522

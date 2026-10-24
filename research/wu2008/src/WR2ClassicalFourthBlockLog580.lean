import WR2ClassicalFourthConditions
import WR2ClassicalFourthLogPoints580
noncomputable section
namespace WuPaper.ClassicalFourthConditions
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem Log_block_580 (j : Fin 16) (hj : 16*580+j.val < 10541) :
    WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 (16*580+j.val)) ≤ val WuPaper.ClassicalFourthData.Bq (16*580+j.val) := by
  fin_cases j
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 9280) ≤ val WuPaper.ClassicalFourthData.Bq 9280
    have hp : val WuPaper.ClassicalFourthData.Bq 9280 = (277769625684633:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 9280 = 277769625684633 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 9280 = (108:ℝ)/25 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_9280
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 9281) ≤ val WuPaper.ClassicalFourthData.Bq 9281
    have hp : val WuPaper.ClassicalFourthData.Bq 9281 = (277770981153288:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 9281 = 277770981153288 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 9281 = (17281:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_9281
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 9282) ≤ val WuPaper.ClassicalFourthData.Bq 9282
    have hp : val WuPaper.ClassicalFourthData.Bq 9282 = (277772335152865:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 9282 = 277772335152865 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 9282 = (8641:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_9282
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 9283) ≤ val WuPaper.ClassicalFourthData.Bq 9283
    have hp : val WuPaper.ClassicalFourthData.Bq 9283 = (277773687683816:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 9283 = 277773687683816 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 9283 = (17283:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_9283
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 9284) ≤ val WuPaper.ClassicalFourthData.Bq 9284
    have hp : val WuPaper.ClassicalFourthData.Bq 9284 = (277775038746594:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 9284 = 277775038746594 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 9284 = (4321:ℝ)/1000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_9284
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 9285) ≤ val WuPaper.ClassicalFourthData.Bq 9285
    have hp : val WuPaper.ClassicalFourthData.Bq 9285 = (277776388341651:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 9285 = 277776388341651 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 9285 = (3457:ℝ)/800 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_9285
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 9286) ≤ val WuPaper.ClassicalFourthData.Bq 9286
    have hp : val WuPaper.ClassicalFourthData.Bq 9286 = (277777736469439:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 9286 = 277777736469439 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 9286 = (8643:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_9286
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 9287) ≤ val WuPaper.ClassicalFourthData.Bq 9287
    have hp : val WuPaper.ClassicalFourthData.Bq 9287 = (277779083130411:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 9287 = 277779083130411 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 9287 = (17287:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_9287
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 9288) ≤ val WuPaper.ClassicalFourthData.Bq 9288
    have hp : val WuPaper.ClassicalFourthData.Bq 9288 = (277780428325018:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 9288 = 277780428325018 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 9288 = (2161:ℝ)/500 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_9288
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 9289) ≤ val WuPaper.ClassicalFourthData.Bq 9289
    have hp : val WuPaper.ClassicalFourthData.Bq 9289 = (277781772053712:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 9289 = 277781772053712 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 9289 = (17289:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_9289
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 9290) ≤ val WuPaper.ClassicalFourthData.Bq 9290
    have hp : val WuPaper.ClassicalFourthData.Bq 9290 = (277783114316944:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 9290 = 277783114316944 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 9290 = (1729:ℝ)/400 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_9290
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 9291) ≤ val WuPaper.ClassicalFourthData.Bq 9291
    have hp : val WuPaper.ClassicalFourthData.Bq 9291 = (277784455115166:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 9291 = 277784455115166 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 9291 = (17291:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_9291
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 9292) ≤ val WuPaper.ClassicalFourthData.Bq 9292
    have hp : val WuPaper.ClassicalFourthData.Bq 9292 = (277785794448829:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 9292 = 277785794448829 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 9292 = (4323:ℝ)/1000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_9292
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 9293) ≤ val WuPaper.ClassicalFourthData.Bq 9293
    have hp : val WuPaper.ClassicalFourthData.Bq 9293 = (277787132318384:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 9293 = 277787132318384 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 9293 = (17293:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_9293
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 9294) ≤ val WuPaper.ClassicalFourthData.Bq 9294
    have hp : val WuPaper.ClassicalFourthData.Bq 9294 = (277788468724282:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 9294 = 277788468724282 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 9294 = (8647:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_9294
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 9295) ≤ val WuPaper.ClassicalFourthData.Bq 9295
    have hp : val WuPaper.ClassicalFourthData.Bq 9295 = (277789803666974:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 9295 = 277789803666974 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 9295 = (3459:ℝ)/800 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_9295
end WuPaper.ClassicalFourthConditions
#print axioms WuPaper.ClassicalFourthConditions.Log_block_580

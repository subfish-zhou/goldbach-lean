import WR2ClassicalFourthConditions
import WR2ClassicalFourthLogPoints277
noncomputable section
namespace WuPaper.ClassicalFourthConditions
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem Log_block_277 (j : Fin 16) (hj : 16*277+j.val < 10541) :
    WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 (16*277+j.val)) ≤ val WuPaper.ClassicalFourthData.Bq (16*277+j.val) := by
  fin_cases j
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 4432) ≤ val WuPaper.ClassicalFourthData.Bq 4432
    have hp : val WuPaper.ClassicalFourthData.Bq 4432 = (239941966112972:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 4432 = 239941966112972 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 4432 = (777:ℝ)/250 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_4432
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 4433) ≤ val WuPaper.ClassicalFourthData.Bq 4433
    have hp : val WuPaper.ClassicalFourthData.Bq 4433 = (239960820227657:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 4433 = 239960820227657 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 4433 = (12433:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_4433
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 4434) ≤ val WuPaper.ClassicalFourthData.Bq 4434
    have hp : val WuPaper.ClassicalFourthData.Bq 4434 = (239979666786064:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 4434 = 239979666786064 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 4434 = (6217:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_4434
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 4435) ≤ val WuPaper.ClassicalFourthData.Bq 4435
    have hp : val WuPaper.ClassicalFourthData.Bq 4435 = (239998505791087:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 4435 = 239998505791087 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 4435 = (2487:ℝ)/800 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_4435
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 4436) ≤ val WuPaper.ClassicalFourthData.Bq 4436
    have hp : val WuPaper.ClassicalFourthData.Bq 4436 = (240017337245622:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 4436 = 240017337245622 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 4436 = (3109:ℝ)/1000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_4436
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 4437) ≤ val WuPaper.ClassicalFourthData.Bq 4437
    have hp : val WuPaper.ClassicalFourthData.Bq 4437 = (240036161152561:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 4437 = 240036161152561 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 4437 = (12437:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_4437
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 4438) ≤ val WuPaper.ClassicalFourthData.Bq 4438
    have hp : val WuPaper.ClassicalFourthData.Bq 4438 = (240054977514796:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 4438 = 240054977514796 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 4438 = (6219:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_4438
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 4439) ≤ val WuPaper.ClassicalFourthData.Bq 4439
    have hp : val WuPaper.ClassicalFourthData.Bq 4439 = (240073786335217:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 4439 = 240073786335217 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 4439 = (12439:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_4439
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 4440) ≤ val WuPaper.ClassicalFourthData.Bq 4440
    have hp : val WuPaper.ClassicalFourthData.Bq 4440 = (240092587616713:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 4440 = 240092587616713 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 4440 = (311:ℝ)/100 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_4440
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 4441) ≤ val WuPaper.ClassicalFourthData.Bq 4441
    have hp : val WuPaper.ClassicalFourthData.Bq 4441 = (240111381362171:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 4441 = 240111381362171 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 4441 = (12441:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_4441
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 4442) ≤ val WuPaper.ClassicalFourthData.Bq 4442
    have hp : val WuPaper.ClassicalFourthData.Bq 4442 = (240130167574479:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 4442 = 240130167574479 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 4442 = (6221:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_4442
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 4443) ≤ val WuPaper.ClassicalFourthData.Bq 4443
    have hp : val WuPaper.ClassicalFourthData.Bq 4443 = (240148946256521:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 4443 = 240148946256521 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 4443 = (12443:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_4443
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 4444) ≤ val WuPaper.ClassicalFourthData.Bq 4444
    have hp : val WuPaper.ClassicalFourthData.Bq 4444 = (240167717411181:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 4444 = 240167717411181 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 4444 = (3111:ℝ)/1000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_4444
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 4445) ≤ val WuPaper.ClassicalFourthData.Bq 4445
    have hp : val WuPaper.ClassicalFourthData.Bq 4445 = (240186481041342:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 4445 = 240186481041342 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 4445 = (2489:ℝ)/800 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_4445
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 4446) ≤ val WuPaper.ClassicalFourthData.Bq 4446
    have hp : val WuPaper.ClassicalFourthData.Bq 4446 = (240205237149884:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 4446 = 240205237149884 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 4446 = (6223:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_4446
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 4447) ≤ val WuPaper.ClassicalFourthData.Bq 4447
    have hp : val WuPaper.ClassicalFourthData.Bq 4447 = (240223985739687:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 4447 = 240223985739687 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 4447 = (12447:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_4447
end WuPaper.ClassicalFourthConditions
#print axioms WuPaper.ClassicalFourthConditions.Log_block_277

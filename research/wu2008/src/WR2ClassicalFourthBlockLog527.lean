import WR2ClassicalFourthConditions
import WR2ClassicalFourthLogPoints527
noncomputable section
namespace WuPaper.ClassicalFourthConditions
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem Log_block_527 (j : Fin 16) (hj : 16*527+j.val < 10541) :
    WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 (16*527+j.val)) ≤ val WuPaper.ClassicalFourthData.Bq (16*527+j.val) := by
  fin_cases j
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 8432) ≤ val WuPaper.ClassicalFourthData.Bq 8432
    have hp : val WuPaper.ClassicalFourthData.Bq 8432 = (276041731380608:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 8432 = 276041731380608 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 8432 = (1027:ℝ)/250 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_8432
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 8433) ≤ val WuPaper.ClassicalFourthData.Bq 8433
    have hp : val WuPaper.ClassicalFourthData.Bq 8433 = (276044512105412:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 8433 = 276044512105412 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 8433 = (16433:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_8433
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 8434) ≤ val WuPaper.ClassicalFourthData.Bq 8434
    have hp : val WuPaper.ClassicalFourthData.Bq 8434 = (276047290917224:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 8434 = 276047290917224 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 8434 = (8217:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_8434
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 8435) ≤ val WuPaper.ClassicalFourthData.Bq 8435
    have hp : val WuPaper.ClassicalFourthData.Bq 8435 = (276050067816648:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 8435 = 276050067816648 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 8435 = (3287:ℝ)/800 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_8435
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 8436) ≤ val WuPaper.ClassicalFourthData.Bq 8436
    have hp : val WuPaper.ClassicalFourthData.Bq 8436 = (276052842804284:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 8436 = 276052842804284 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 8436 = (4109:ℝ)/1000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_8436
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 8437) ≤ val WuPaper.ClassicalFourthData.Bq 8437
    have hp : val WuPaper.ClassicalFourthData.Bq 8437 = (276055615880735:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 8437 = 276055615880735 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 8437 = (16437:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_8437
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 8438) ≤ val WuPaper.ClassicalFourthData.Bq 8438
    have hp : val WuPaper.ClassicalFourthData.Bq 8438 = (276058387046603:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 8438 = 276058387046603 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 8438 = (8219:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_8438
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 8439) ≤ val WuPaper.ClassicalFourthData.Bq 8439
    have hp : val WuPaper.ClassicalFourthData.Bq 8439 = (276061156302490:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 8439 = 276061156302490 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 8439 = (16439:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_8439
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 8440) ≤ val WuPaper.ClassicalFourthData.Bq 8440
    have hp : val WuPaper.ClassicalFourthData.Bq 8440 = (276063923648997:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 8440 = 276063923648997 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 8440 = (411:ℝ)/100 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_8440
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 8441) ≤ val WuPaper.ClassicalFourthData.Bq 8441
    have hp : val WuPaper.ClassicalFourthData.Bq 8441 = (276066689086725:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 8441 = 276066689086725 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 8441 = (16441:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_8441
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 8442) ≤ val WuPaper.ClassicalFourthData.Bq 8442
    have hp : val WuPaper.ClassicalFourthData.Bq 8442 = (276069452616275:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 8442 = 276069452616275 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 8442 = (8221:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_8442
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 8443) ≤ val WuPaper.ClassicalFourthData.Bq 8443
    have hp : val WuPaper.ClassicalFourthData.Bq 8443 = (276072214238247:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 8443 = 276072214238247 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 8443 = (16443:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_8443
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 8444) ≤ val WuPaper.ClassicalFourthData.Bq 8444
    have hp : val WuPaper.ClassicalFourthData.Bq 8444 = (276074973953243:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 8444 = 276074973953243 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 8444 = (4111:ℝ)/1000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_8444
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 8445) ≤ val WuPaper.ClassicalFourthData.Bq 8445
    have hp : val WuPaper.ClassicalFourthData.Bq 8445 = (276077731761863:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 8445 = 276077731761863 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 8445 = (3289:ℝ)/800 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_8445
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 8446) ≤ val WuPaper.ClassicalFourthData.Bq 8446
    have hp : val WuPaper.ClassicalFourthData.Bq 8446 = (276080487664707:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 8446 = 276080487664707 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 8446 = (8223:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_8446
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 8447) ≤ val WuPaper.ClassicalFourthData.Bq 8447
    have hp : val WuPaper.ClassicalFourthData.Bq 8447 = (276083241662375:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 8447 = 276083241662375 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 8447 = (16447:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_8447
end WuPaper.ClassicalFourthConditions
#print axioms WuPaper.ClassicalFourthConditions.Log_block_527

import WR2ClassicalFourthConditions
import WR2ClassicalFourthLogPoints405
noncomputable section
namespace WuPaper.ClassicalFourthConditions
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem Log_block_405 (j : Fin 16) (hj : 16*405+j.val < 10541) :
    WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 (16*405+j.val)) ≤ val WuPaper.ClassicalFourthData.Bq (16*405+j.val) := by
  fin_cases j
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 6480) ≤ val WuPaper.ClassicalFourthData.Bq 6480
    have hp : val WuPaper.ClassicalFourthData.Bq 6480 = (266070253528473:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 6480 = 266070253528473 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 6480 = (181:ℝ)/50 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_6480
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 6481) ≤ val WuPaper.ClassicalFourthData.Bq 6481
    have hp : val WuPaper.ClassicalFourthData.Bq 6481 = (266078235776042:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 6481 = 266078235776042 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 6481 = (14481:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_6481
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 6482) ≤ val WuPaper.ClassicalFourthData.Bq 6482
    have hp : val WuPaper.ClassicalFourthData.Bq 6482 = (266086214406892:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 6482 = 266086214406892 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 6482 = (7241:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_6482
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 6483) ≤ val WuPaper.ClassicalFourthData.Bq 6483
    have hp : val WuPaper.ClassicalFourthData.Bq 6483 = (266094189422250:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 6483 = 266094189422250 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 6483 = (14483:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_6483
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 6484) ≤ val WuPaper.ClassicalFourthData.Bq 6484
    have hp : val WuPaper.ClassicalFourthData.Bq 6484 = (266102160823346:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 6484 = 266102160823346 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 6484 = (3621:ℝ)/1000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_6484
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 6485) ≤ val WuPaper.ClassicalFourthData.Bq 6485
    have hp : val WuPaper.ClassicalFourthData.Bq 6485 = (266110128611408:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 6485 = 266110128611408 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 6485 = (2897:ℝ)/800 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_6485
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 6486) ≤ val WuPaper.ClassicalFourthData.Bq 6486
    have hp : val WuPaper.ClassicalFourthData.Bq 6486 = (266118092787662:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 6486 = 266118092787662 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 6486 = (7243:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_6486
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 6487) ≤ val WuPaper.ClassicalFourthData.Bq 6487
    have hp : val WuPaper.ClassicalFourthData.Bq 6487 = (266126053353336:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 6487 = 266126053353336 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 6487 = (14487:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_6487
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 6488) ≤ val WuPaper.ClassicalFourthData.Bq 6488
    have hp : val WuPaper.ClassicalFourthData.Bq 6488 = (266134010309657:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 6488 = 266134010309657 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 6488 = (1811:ℝ)/500 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_6488
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 6489) ≤ val WuPaper.ClassicalFourthData.Bq 6489
    have hp : val WuPaper.ClassicalFourthData.Bq 6489 = (266141963657849:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 6489 = 266141963657849 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 6489 = (14489:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_6489
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 6490) ≤ val WuPaper.ClassicalFourthData.Bq 6490
    have hp : val WuPaper.ClassicalFourthData.Bq 6490 = (266149913399140:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 6490 = 266149913399140 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 6490 = (1449:ℝ)/400 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_6490
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 6491) ≤ val WuPaper.ClassicalFourthData.Bq 6491
    have hp : val WuPaper.ClassicalFourthData.Bq 6491 = (266157859534753:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 6491 = 266157859534753 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 6491 = (14491:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_6491
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 6492) ≤ val WuPaper.ClassicalFourthData.Bq 6492
    have hp : val WuPaper.ClassicalFourthData.Bq 6492 = (266165802065914:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 6492 = 266165802065914 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 6492 = (3623:ℝ)/1000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_6492
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 6493) ≤ val WuPaper.ClassicalFourthData.Bq 6493
    have hp : val WuPaper.ClassicalFourthData.Bq 6493 = (266173740993846:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 6493 = 266173740993846 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 6493 = (14493:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_6493
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 6494) ≤ val WuPaper.ClassicalFourthData.Bq 6494
    have hp : val WuPaper.ClassicalFourthData.Bq 6494 = (266181676319773:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 6494 = 266181676319773 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 6494 = (7247:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_6494
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 6495) ≤ val WuPaper.ClassicalFourthData.Bq 6495
    have hp : val WuPaper.ClassicalFourthData.Bq 6495 = (266189608044919:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 6495 = 266189608044919 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 6495 = (2899:ℝ)/800 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_6495
end WuPaper.ClassicalFourthConditions
#print axioms WuPaper.ClassicalFourthConditions.Log_block_405

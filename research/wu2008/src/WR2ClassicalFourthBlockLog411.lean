import WR2ClassicalFourthConditions
import WR2ClassicalFourthLogPoints411
noncomputable section
namespace WuPaper.ClassicalFourthConditions
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem Log_block_411 (j : Fin 16) (hj : 16*411+j.val < 10541) :
    WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 (16*411+j.val)) ≤ val WuPaper.ClassicalFourthData.Bq (16*411+j.val) := by
  fin_cases j
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 6576) ≤ val WuPaper.ClassicalFourthData.Bq 6576
    have hp : val WuPaper.ClassicalFourthData.Bq 6576 = (266820231061890:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 6576 = 266820231061890 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 6576 = (911:ℝ)/250 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_6576
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 6577) ≤ val WuPaper.ClassicalFourthData.Bq 6577
    have hp : val WuPaper.ClassicalFourthData.Bq 6577 = (266827871640560:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 6577 = 266827871640560 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 6577 = (14577:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_6577
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 6578) ≤ val WuPaper.ClassicalFourthData.Bq 6578
    have hp : val WuPaper.ClassicalFourthData.Bq 6578 = (266835508718339:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 6578 = 266835508718339 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 6578 = (7289:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_6578
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 6579) ≤ val WuPaper.ClassicalFourthData.Bq 6579
    have hp : val WuPaper.ClassicalFourthData.Bq 6579 = (266843142296408:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 6579 = 266843142296408 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 6579 = (14579:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_6579
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 6580) ≤ val WuPaper.ClassicalFourthData.Bq 6580
    have hp : val WuPaper.ClassicalFourthData.Bq 6580 = (266850772375954:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 6580 = 266850772375954 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 6580 = (729:ℝ)/200 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_6580
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 6581) ≤ val WuPaper.ClassicalFourthData.Bq 6581
    have hp : val WuPaper.ClassicalFourthData.Bq 6581 = (266858398958157:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 6581 = 266858398958157 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 6581 = (14581:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_6581
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 6582) ≤ val WuPaper.ClassicalFourthData.Bq 6582
    have hp : val WuPaper.ClassicalFourthData.Bq 6582 = (266866022044202:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 6582 = 266866022044202 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 6582 = (7291:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_6582
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 6583) ≤ val WuPaper.ClassicalFourthData.Bq 6583
    have hp : val WuPaper.ClassicalFourthData.Bq 6583 = (266873641635270:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 6583 = 266873641635270 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 6583 = (14583:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_6583
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 6584) ≤ val WuPaper.ClassicalFourthData.Bq 6584
    have hp : val WuPaper.ClassicalFourthData.Bq 6584 = (266881257732543:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 6584 = 266881257732543 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 6584 = (1823:ℝ)/500 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_6584
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 6585) ≤ val WuPaper.ClassicalFourthData.Bq 6585
    have hp : val WuPaper.ClassicalFourthData.Bq 6585 = (266888870337203:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 6585 = 266888870337203 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 6585 = (2917:ℝ)/800 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_6585
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 6586) ≤ val WuPaper.ClassicalFourthData.Bq 6586
    have hp : val WuPaper.ClassicalFourthData.Bq 6586 = (266896479450430:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 6586 = 266896479450430 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 6586 = (7293:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_6586
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 6587) ≤ val WuPaper.ClassicalFourthData.Bq 6587
    have hp : val WuPaper.ClassicalFourthData.Bq 6587 = (266904085073406:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 6587 = 266904085073406 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 6587 = (14587:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_6587
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 6588) ≤ val WuPaper.ClassicalFourthData.Bq 6588
    have hp : val WuPaper.ClassicalFourthData.Bq 6588 = (266911687207308:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 6588 = 266911687207308 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 6588 = (3647:ℝ)/1000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_6588
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 6589) ≤ val WuPaper.ClassicalFourthData.Bq 6589
    have hp : val WuPaper.ClassicalFourthData.Bq 6589 = (266919285853319:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 6589 = 266919285853319 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 6589 = (14589:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_6589
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 6590) ≤ val WuPaper.ClassicalFourthData.Bq 6590
    have hp : val WuPaper.ClassicalFourthData.Bq 6590 = (266926881012615:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 6590 = 266926881012615 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 6590 = (1459:ℝ)/400 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_6590
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 6591) ≤ val WuPaper.ClassicalFourthData.Bq 6591
    have hp : val WuPaper.ClassicalFourthData.Bq 6591 = (266934472686377:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 6591 = 266934472686377 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 6591 = (14591:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_6591
end WuPaper.ClassicalFourthConditions
#print axioms WuPaper.ClassicalFourthConditions.Log_block_411

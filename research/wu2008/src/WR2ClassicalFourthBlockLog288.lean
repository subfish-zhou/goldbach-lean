import WR2ClassicalFourthConditions
import WR2ClassicalFourthLogPoints288
noncomputable section
namespace WuPaper.ClassicalFourthConditions
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem Log_block_288 (j : Fin 16) (hj : 16*288+j.val < 10541) :
    WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 (16*288+j.val)) ≤ val WuPaper.ClassicalFourthData.Bq (16*288+j.val) := by
  fin_cases j
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 4608) ≤ val WuPaper.ClassicalFourthData.Bq 4608
    have hp : val WuPaper.ClassicalFourthData.Bq 4608 = (243146460120412:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 4608 = 243146460120412 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 4608 = (394:ℝ)/125 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_4608
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 4609) ≤ val WuPaper.ClassicalFourthData.Bq 4609
    have hp : val WuPaper.ClassicalFourthData.Bq 4609 = (243164027775693:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 4609 = 243164027775693 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 4609 = (12609:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_4609
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 4610) ≤ val WuPaper.ClassicalFourthData.Bq 4610
    have hp : val WuPaper.ClassicalFourthData.Bq 4610 = (243181588364711:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 4610 = 243181588364711 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 4610 = (1261:ℝ)/400 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_4610
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 4611) ≤ val WuPaper.ClassicalFourthData.Bq 4611
    have hp : val WuPaper.ClassicalFourthData.Bq 4611 = (243199141890140:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 4611 = 243199141890140 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 4611 = (12611:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_4611
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 4612) ≤ val WuPaper.ClassicalFourthData.Bq 4612
    have hp : val WuPaper.ClassicalFourthData.Bq 4612 = (243216688354655:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 4612 = 243216688354655 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 4612 = (3153:ℝ)/1000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_4612
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 4613) ≤ val WuPaper.ClassicalFourthData.Bq 4613
    have hp : val WuPaper.ClassicalFourthData.Bq 4613 = (243234227760928:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 4613 = 243234227760928 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 4613 = (12613:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_4613
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 4614) ≤ val WuPaper.ClassicalFourthData.Bq 4614
    have hp : val WuPaper.ClassicalFourthData.Bq 4614 = (243251760111631:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 4614 = 243251760111631 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 4614 = (6307:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_4614
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 4615) ≤ val WuPaper.ClassicalFourthData.Bq 4615
    have hp : val WuPaper.ClassicalFourthData.Bq 4615 = (243269285409434:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 4615 = 243269285409434 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 4615 = (2523:ℝ)/800 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_4615
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 4616) ≤ val WuPaper.ClassicalFourthData.Bq 4616
    have hp : val WuPaper.ClassicalFourthData.Bq 4616 = (243286803657007:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 4616 = 243286803657007 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 4616 = (1577:ℝ)/500 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_4616
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 4617) ≤ val WuPaper.ClassicalFourthData.Bq 4617
    have hp : val WuPaper.ClassicalFourthData.Bq 4617 = (243304314857015:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 4617 = 243304314857015 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 4617 = (12617:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_4617
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 4618) ≤ val WuPaper.ClassicalFourthData.Bq 4618
    have hp : val WuPaper.ClassicalFourthData.Bq 4618 = (243321819012128:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 4618 = 243321819012128 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 4618 = (6309:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_4618
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 4619) ≤ val WuPaper.ClassicalFourthData.Bq 4619
    have hp : val WuPaper.ClassicalFourthData.Bq 4619 = (243339316125009:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 4619 = 243339316125009 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 4619 = (12619:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_4619
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 4620) ≤ val WuPaper.ClassicalFourthData.Bq 4620
    have hp : val WuPaper.ClassicalFourthData.Bq 4620 = (243356806198324:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 4620 = 243356806198324 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 4620 = (631:ℝ)/200 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_4620
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 4621) ≤ val WuPaper.ClassicalFourthData.Bq 4621
    have hp : val WuPaper.ClassicalFourthData.Bq 4621 = (243374289234735:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 4621 = 243374289234735 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 4621 = (12621:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_4621
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 4622) ≤ val WuPaper.ClassicalFourthData.Bq 4622
    have hp : val WuPaper.ClassicalFourthData.Bq 4622 = (243391765236905:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 4622 = 243391765236905 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 4622 = (6311:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_4622
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 4623) ≤ val WuPaper.ClassicalFourthData.Bq 4623
    have hp : val WuPaper.ClassicalFourthData.Bq 4623 = (243409234207494:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 4623 = 243409234207494 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 4623 = (12623:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_4623
end WuPaper.ClassicalFourthConditions
#print axioms WuPaper.ClassicalFourthConditions.Log_block_288

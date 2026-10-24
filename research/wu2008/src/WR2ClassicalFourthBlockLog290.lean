import WR2ClassicalFourthConditions
import WR2ClassicalFourthLogPoints290
noncomputable section
namespace WuPaper.ClassicalFourthConditions
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem Log_block_290 (j : Fin 16) (hj : 16*290+j.val < 10541) :
    WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 (16*290+j.val)) ≤ val WuPaper.ClassicalFourthData.Bq (16*290+j.val) := by
  fin_cases j
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 4640) ≤ val WuPaper.ClassicalFourthData.Bq 4640
    have hp : val WuPaper.ClassicalFourthData.Bq 4640 = (243705133448125:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 4640 = 243705133448125 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 4640 = (79:ℝ)/25 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_4640
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 4641) ≤ val WuPaper.ClassicalFourthData.Bq 4641
    have hp : val WuPaper.ClassicalFourthData.Bq 4641 = (243722476303892:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 4641 = 243722476303892 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 4641 = (12641:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_4641
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 4642) ≤ val WuPaper.ClassicalFourthData.Bq 4642
    have hp : val WuPaper.ClassicalFourthData.Bq 4642 = (243739812178406:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 4642 = 243739812178406 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 4642 = (6321:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_4642
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 4643) ≤ val WuPaper.ClassicalFourthData.Bq 4643
    have hp : val WuPaper.ClassicalFourthData.Bq 4643 = (243757141074306:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 4643 = 243757141074306 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 4643 = (12643:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_4643
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 4644) ≤ val WuPaper.ClassicalFourthData.Bq 4644
    have hp : val WuPaper.ClassicalFourthData.Bq 4644 = (243774462994227:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 4644 = 243774462994227 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 4644 = (3161:ℝ)/1000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_4644
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 4645) ≤ val WuPaper.ClassicalFourthData.Bq 4645
    have hp : val WuPaper.ClassicalFourthData.Bq 4645 = (243791777940803:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 4645 = 243791777940803 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 4645 = (2529:ℝ)/800 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_4645
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 4646) ≤ val WuPaper.ClassicalFourthData.Bq 4646
    have hp : val WuPaper.ClassicalFourthData.Bq 4646 = (243809085916670:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 4646 = 243809085916670 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 4646 = (6323:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_4646
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 4647) ≤ val WuPaper.ClassicalFourthData.Bq 4647
    have hp : val WuPaper.ClassicalFourthData.Bq 4647 = (243826386924458:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 4647 = 243826386924458 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 4647 = (12647:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_4647
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 4648) ≤ val WuPaper.ClassicalFourthData.Bq 4648
    have hp : val WuPaper.ClassicalFourthData.Bq 4648 = (243843680966799:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 4648 = 243843680966799 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 4648 = (1581:ℝ)/500 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_4648
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 4649) ≤ val WuPaper.ClassicalFourthData.Bq 4649
    have hp : val WuPaper.ClassicalFourthData.Bq 4649 = (243860968046323:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 4649 = 243860968046323 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 4649 = (12649:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_4649
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 4650) ≤ val WuPaper.ClassicalFourthData.Bq 4650
    have hp : val WuPaper.ClassicalFourthData.Bq 4650 = (243878248165660:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 4650 = 243878248165660 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 4650 = (253:ℝ)/80 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_4650
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 4651) ≤ val WuPaper.ClassicalFourthData.Bq 4651
    have hp : val WuPaper.ClassicalFourthData.Bq 4651 = (243895521327436:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 4651 = 243895521327436 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 4651 = (12651:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_4651
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 4652) ≤ val WuPaper.ClassicalFourthData.Bq 4652
    have hp : val WuPaper.ClassicalFourthData.Bq 4652 = (243912787534279:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 4652 = 243912787534279 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 4652 = (3163:ℝ)/1000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_4652
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 4653) ≤ val WuPaper.ClassicalFourthData.Bq 4653
    have hp : val WuPaper.ClassicalFourthData.Bq 4653 = (243930046788813:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 4653 = 243930046788813 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 4653 = (12653:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_4653
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 4654) ≤ val WuPaper.ClassicalFourthData.Bq 4654
    have hp : val WuPaper.ClassicalFourthData.Bq 4654 = (243947299093663:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 4654 = 243947299093663 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 4654 = (6327:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_4654
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 4655) ≤ val WuPaper.ClassicalFourthData.Bq 4655
    have hp : val WuPaper.ClassicalFourthData.Bq 4655 = (243964544451453:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 4655 = 243964544451453 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 4655 = (2531:ℝ)/800 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_4655
end WuPaper.ClassicalFourthConditions
#print axioms WuPaper.ClassicalFourthConditions.Log_block_290

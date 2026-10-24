import WR2ClassicalFourthConditions
import WR2ClassicalFourthLogPoints351
noncomputable section
namespace WuPaper.ClassicalFourthConditions
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem Log_block_351 (j : Fin 16) (hj : 16*351+j.val < 10541) :
    WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 (16*351+j.val)) ≤ val WuPaper.ClassicalFourthData.Bq (16*351+j.val) := by
  fin_cases j
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 5616) ≤ val WuPaper.ClassicalFourthData.Bq 5616
    have hp : val WuPaper.ClassicalFourthData.Bq 5616 = (257677443205925:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 5616 = 257677443205925 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 5616 = (851:ℝ)/250 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_5616
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 5617) ≤ val WuPaper.ClassicalFourthData.Bq 5617
    have hp : val WuPaper.ClassicalFourthData.Bq 5617 = (257689066493489:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 5617 = 257689066493489 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 5617 = (13617:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_5617
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 5618) ≤ val WuPaper.ClassicalFourthData.Bq 5618
    have hp : val WuPaper.ClassicalFourthData.Bq 5618 = (257700684898102:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 5618 = 257700684898102 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 5618 = (6809:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_5618
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 5619) ≤ val WuPaper.ClassicalFourthData.Bq 5619
    have hp : val WuPaper.ClassicalFourthData.Bq 5619 = (257712298421498:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 5619 = 257712298421498 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 5619 = (13619:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_5619
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 5620) ≤ val WuPaper.ClassicalFourthData.Bq 5620
    have hp : val WuPaper.ClassicalFourthData.Bq 5620 = (257723907065413:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 5620 = 257723907065413 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 5620 = (681:ℝ)/200 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_5620
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 5621) ≤ val WuPaper.ClassicalFourthData.Bq 5621
    have hp : val WuPaper.ClassicalFourthData.Bq 5621 = (257735510831582:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 5621 = 257735510831582 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 5621 = (13621:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_5621
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 5622) ≤ val WuPaper.ClassicalFourthData.Bq 5622
    have hp : val WuPaper.ClassicalFourthData.Bq 5622 = (257747109721738:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 5622 = 257747109721738 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 5622 = (6811:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_5622
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 5623) ≤ val WuPaper.ClassicalFourthData.Bq 5623
    have hp : val WuPaper.ClassicalFourthData.Bq 5623 = (257758703737614:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 5623 = 257758703737614 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 5623 = (13623:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_5623
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 5624) ≤ val WuPaper.ClassicalFourthData.Bq 5624
    have hp : val WuPaper.ClassicalFourthData.Bq 5624 = (257770292880944:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 5624 = 257770292880944 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 5624 = (1703:ℝ)/500 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_5624
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 5625) ≤ val WuPaper.ClassicalFourthData.Bq 5625
    have hp : val WuPaper.ClassicalFourthData.Bq 5625 = (257781877153457:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 5625 = 257781877153457 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 5625 = (109:ℝ)/32 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_5625
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 5626) ≤ val WuPaper.ClassicalFourthData.Bq 5626
    have hp : val WuPaper.ClassicalFourthData.Bq 5626 = (257793456556886:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 5626 = 257793456556886 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 5626 = (6813:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_5626
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 5627) ≤ val WuPaper.ClassicalFourthData.Bq 5627
    have hp : val WuPaper.ClassicalFourthData.Bq 5627 = (257805031092961:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 5627 = 257805031092961 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 5627 = (13627:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_5627
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 5628) ≤ val WuPaper.ClassicalFourthData.Bq 5628
    have hp : val WuPaper.ClassicalFourthData.Bq 5628 = (257816600763411:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 5628 = 257816600763411 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 5628 = (3407:ℝ)/1000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_5628
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 5629) ≤ val WuPaper.ClassicalFourthData.Bq 5629
    have hp : val WuPaper.ClassicalFourthData.Bq 5629 = (257828165569965:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 5629 = 257828165569965 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 5629 = (13629:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_5629
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 5630) ≤ val WuPaper.ClassicalFourthData.Bq 5630
    have hp : val WuPaper.ClassicalFourthData.Bq 5630 = (257839725514351:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 5630 = 257839725514351 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 5630 = (1363:ℝ)/400 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_5630
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 5631) ≤ val WuPaper.ClassicalFourthData.Bq 5631
    have hp : val WuPaper.ClassicalFourthData.Bq 5631 = (257851280598296:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 5631 = 257851280598296 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 5631 = (13631:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_5631
end WuPaper.ClassicalFourthConditions
#print axioms WuPaper.ClassicalFourthConditions.Log_block_351

import WR2ClassicalFourthConditions
import WR2ClassicalFourthLogPoints170
noncomputable section
namespace WuPaper.ClassicalFourthConditions
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem Log_block_170 (j : Fin 16) (hj : 16*170+j.val < 10541) :
    WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 (16*170+j.val)) ≤ val WuPaper.ClassicalFourthData.Bq (16*170+j.val) := by
  fin_cases j
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 2720) ≤ val WuPaper.ClassicalFourthData.Bq 2720
    have hp : val WuPaper.ClassicalFourthData.Bq 2720 = (193579773662376:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 2720 = 193579773662376 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 2720 = (67:ℝ)/25 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_2720
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 2721) ≤ val WuPaper.ClassicalFourthData.Bq 2721
    have hp : val WuPaper.ClassicalFourthData.Bq 2721 = (193617234163955:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 2721 = 193617234163955 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 2721 = (10721:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_2721
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 2722) ≤ val WuPaper.ClassicalFourthData.Bq 2722
    have hp : val WuPaper.ClassicalFourthData.Bq 2722 = (193654679419147:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 2722 = 193654679419147 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 2722 = (5361:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_2722
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 2723) ≤ val WuPaper.ClassicalFourthData.Bq 2723
    have hp : val WuPaper.ClassicalFourthData.Bq 2723 = (193692109434677:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 2723 = 193692109434677 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 2723 = (10723:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_2723
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 2724) ≤ val WuPaper.ClassicalFourthData.Bq 2724
    have hp : val WuPaper.ClassicalFourthData.Bq 2724 = (193729524217262:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 2724 = 193729524217262 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 2724 = (2681:ℝ)/1000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_2724
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 2725) ≤ val WuPaper.ClassicalFourthData.Bq 2725
    have hp : val WuPaper.ClassicalFourthData.Bq 2725 = (193766923773618:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 2725 = 193766923773618 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 2725 = (429:ℝ)/160 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_2725
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 2726) ≤ val WuPaper.ClassicalFourthData.Bq 2726
    have hp : val WuPaper.ClassicalFourthData.Bq 2726 = (193804308110456:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 2726 = 193804308110456 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 2726 = (5363:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_2726
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 2727) ≤ val WuPaper.ClassicalFourthData.Bq 2727
    have hp : val WuPaper.ClassicalFourthData.Bq 2727 = (193841677234485:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 2727 = 193841677234485 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 2727 = (10727:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_2727
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 2728) ≤ val WuPaper.ClassicalFourthData.Bq 2728
    have hp : val WuPaper.ClassicalFourthData.Bq 2728 = (193879031152408:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 2728 = 193879031152408 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 2728 = (1341:ℝ)/500 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_2728
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 2729) ≤ val WuPaper.ClassicalFourthData.Bq 2729
    have hp : val WuPaper.ClassicalFourthData.Bq 2729 = (193916369870926:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 2729 = 193916369870926 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 2729 = (10729:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_2729
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 2730) ≤ val WuPaper.ClassicalFourthData.Bq 2730
    have hp : val WuPaper.ClassicalFourthData.Bq 2730 = (193953693396737:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 2730 = 193953693396737 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 2730 = (1073:ℝ)/400 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_2730
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 2731) ≤ val WuPaper.ClassicalFourthData.Bq 2731
    have hp : val WuPaper.ClassicalFourthData.Bq 2731 = (193991001736534:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 2731 = 193991001736534 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 2731 = (10731:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_2731
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 2732) ≤ val WuPaper.ClassicalFourthData.Bq 2732
    have hp : val WuPaper.ClassicalFourthData.Bq 2732 = (194028294897007:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 2732 = 194028294897007 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 2732 = (2683:ℝ)/1000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_2732
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 2733) ≤ val WuPaper.ClassicalFourthData.Bq 2733
    have hp : val WuPaper.ClassicalFourthData.Bq 2733 = (194065572884843:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 2733 = 194065572884843 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 2733 = (10733:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_2733
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 2734) ≤ val WuPaper.ClassicalFourthData.Bq 2734
    have hp : val WuPaper.ClassicalFourthData.Bq 2734 = (194102835706724:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 2734 = 194102835706724 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 2734 = (5367:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_2734
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 2735) ≤ val WuPaper.ClassicalFourthData.Bq 2735
    have hp : val WuPaper.ClassicalFourthData.Bq 2735 = (194140083369329:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 2735 = 194140083369329 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 2735 = (2147:ℝ)/800 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_2735
end WuPaper.ClassicalFourthConditions
#print axioms WuPaper.ClassicalFourthConditions.Log_block_170

import WR2ClassicalFourthConditions
import WR2ClassicalFourthLogPoints225
noncomputable section
namespace WuPaper.ClassicalFourthConditions
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem Log_block_225 (j : Fin 16) (hj : 16*225+j.val < 10541) :
    WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 (16*225+j.val)) ≤ val WuPaper.ClassicalFourthData.Bq (16*225+j.val) := by
  fin_cases j
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 3600) ≤ val WuPaper.ClassicalFourthData.Bq 3600
    have hp : val WuPaper.ClassicalFourthData.Bq 3600 = (221328926266344:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 3600 = 221328926266344 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 3600 = (29:ℝ)/10 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_3600
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 3601) ≤ val WuPaper.ClassicalFourthData.Bq 3601
    have hp : val WuPaper.ClassicalFourthData.Bq 3601 = (221355212986472:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 3601 = 221355212986472 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 3601 = (11601:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_3601
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 3602) ≤ val WuPaper.ClassicalFourthData.Bq 3602
    have hp : val WuPaper.ClassicalFourthData.Bq 3602 = (221381489207781:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 3602 = 221381489207781 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 3602 = (5801:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_3602
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 3603) ≤ val WuPaper.ClassicalFourthData.Bq 3603
    have hp : val WuPaper.ClassicalFourthData.Bq 3603 = (221407754934555:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 3603 = 221407754934555 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 3603 = (11603:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_3603
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 3604) ≤ val WuPaper.ClassicalFourthData.Bq 3604
    have hp : val WuPaper.ClassicalFourthData.Bq 3604 = (221434010171077:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 3604 = 221434010171077 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 3604 = (2901:ℝ)/1000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_3604
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 3605) ≤ val WuPaper.ClassicalFourthData.Bq 3605
    have hp : val WuPaper.ClassicalFourthData.Bq 3605 = (221460254921626:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 3605 = 221460254921626 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 3605 = (2321:ℝ)/800 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_3605
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 3606) ≤ val WuPaper.ClassicalFourthData.Bq 3606
    have hp : val WuPaper.ClassicalFourthData.Bq 3606 = (221486489190480:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 3606 = 221486489190480 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 3606 = (5803:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_3606
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 3607) ≤ val WuPaper.ClassicalFourthData.Bq 3607
    have hp : val WuPaper.ClassicalFourthData.Bq 3607 = (221512712981916:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 3607 = 221512712981916 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 3607 = (11607:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_3607
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 3608) ≤ val WuPaper.ClassicalFourthData.Bq 3608
    have hp : val WuPaper.ClassicalFourthData.Bq 3608 = (221538926300207:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 3608 = 221538926300207 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 3608 = (1451:ℝ)/500 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_3608
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 3609) ≤ val WuPaper.ClassicalFourthData.Bq 3609
    have hp : val WuPaper.ClassicalFourthData.Bq 3609 = (221565129149624:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 3609 = 221565129149624 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 3609 = (11609:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_3609
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 3610) ≤ val WuPaper.ClassicalFourthData.Bq 3610
    have hp : val WuPaper.ClassicalFourthData.Bq 3610 = (221591321534438:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 3610 = 221591321534438 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 3610 = (1161:ℝ)/400 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_3610
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 3611) ≤ val WuPaper.ClassicalFourthData.Bq 3611
    have hp : val WuPaper.ClassicalFourthData.Bq 3611 = (221617503458915:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 3611 = 221617503458915 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 3611 = (11611:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_3611
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 3612) ≤ val WuPaper.ClassicalFourthData.Bq 3612
    have hp : val WuPaper.ClassicalFourthData.Bq 3612 = (221643674927321:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 3612 = 221643674927321 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 3612 = (2903:ℝ)/1000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_3612
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 3613) ≤ val WuPaper.ClassicalFourthData.Bq 3613
    have hp : val WuPaper.ClassicalFourthData.Bq 3613 = (221669835943920:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 3613 = 221669835943920 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 3613 = (11613:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_3613
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 3614) ≤ val WuPaper.ClassicalFourthData.Bq 3614
    have hp : val WuPaper.ClassicalFourthData.Bq 3614 = (221695986512973:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 3614 = 221695986512973 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 3614 = (5807:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_3614
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 3615) ≤ val WuPaper.ClassicalFourthData.Bq 3615
    have hp : val WuPaper.ClassicalFourthData.Bq 3615 = (221722126638738:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 3615 = 221722126638738 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 3615 = (2323:ℝ)/800 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_3615
end WuPaper.ClassicalFourthConditions
#print axioms WuPaper.ClassicalFourthConditions.Log_block_225

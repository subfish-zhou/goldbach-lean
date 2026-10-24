import WR2ClassicalFourthConditions
import WR2ClassicalFourthLogPoints481
noncomputable section
namespace WuPaper.ClassicalFourthConditions
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem Log_block_481 (j : Fin 16) (hj : 16*481+j.val < 10541) :
    WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 (16*481+j.val)) ≤ val WuPaper.ClassicalFourthData.Bq (16*481+j.val) := by
  fin_cases j
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 7696) ≤ val WuPaper.ClassicalFourthData.Bq 7696
    have hp : val WuPaper.ClassicalFourthData.Bq 7696 = (273433369492573:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 7696 = 273433369492573 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 7696 = (981:ℝ)/250 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_7696
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 7697) ≤ val WuPaper.ClassicalFourthData.Bq 7697
    have hp : val WuPaper.ClassicalFourthData.Bq 7697 = (273437736522904:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 7697 = 273437736522904 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 7697 = (15697:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_7697
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 7698) ≤ val WuPaper.ClassicalFourthData.Bq 7698
    have hp : val WuPaper.ClassicalFourthData.Bq 7698 = (273442101134482:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 7698 = 273442101134482 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 7698 = (7849:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_7698
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 7699) ≤ val WuPaper.ClassicalFourthData.Bq 7699
    have hp : val WuPaper.ClassicalFourthData.Bq 7699 = (273446463328087:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 7699 = 273446463328087 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 7699 = (15699:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_7699
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 7700) ≤ val WuPaper.ClassicalFourthData.Bq 7700
    have hp : val WuPaper.ClassicalFourthData.Bq 7700 = (273450823104499:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 7700 = 273450823104499 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 7700 = (157:ℝ)/40 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_7700
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 7701) ≤ val WuPaper.ClassicalFourthData.Bq 7701
    have hp : val WuPaper.ClassicalFourthData.Bq 7701 = (273455180464498:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 7701 = 273455180464498 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 7701 = (15701:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_7701
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 7702) ≤ val WuPaper.ClassicalFourthData.Bq 7702
    have hp : val WuPaper.ClassicalFourthData.Bq 7702 = (273459535408864:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 7702 = 273459535408864 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 7702 = (7851:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_7702
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 7703) ≤ val WuPaper.ClassicalFourthData.Bq 7703
    have hp : val WuPaper.ClassicalFourthData.Bq 7703 = (273463887938377:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 7703 = 273463887938377 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 7703 = (15703:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_7703
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 7704) ≤ val WuPaper.ClassicalFourthData.Bq 7704
    have hp : val WuPaper.ClassicalFourthData.Bq 7704 = (273468238053816:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 7704 = 273468238053816 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 7704 = (1963:ℝ)/500 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_7704
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 7705) ≤ val WuPaper.ClassicalFourthData.Bq 7705
    have hp : val WuPaper.ClassicalFourthData.Bq 7705 = (273472585755959:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 7705 = 273472585755959 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 7705 = (3141:ℝ)/800 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_7705
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 7706) ≤ val WuPaper.ClassicalFourthData.Bq 7706
    have hp : val WuPaper.ClassicalFourthData.Bq 7706 = (273476931045586:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 7706 = 273476931045586 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 7706 = (7853:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_7706
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 7707) ≤ val WuPaper.ClassicalFourthData.Bq 7707
    have hp : val WuPaper.ClassicalFourthData.Bq 7707 = (273481273923474:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 7707 = 273481273923474 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 7707 = (15707:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_7707
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 7708) ≤ val WuPaper.ClassicalFourthData.Bq 7708
    have hp : val WuPaper.ClassicalFourthData.Bq 7708 = (273485614390402:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 7708 = 273485614390402 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 7708 = (3927:ℝ)/1000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_7708
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 7709) ≤ val WuPaper.ClassicalFourthData.Bq 7709
    have hp : val WuPaper.ClassicalFourthData.Bq 7709 = (273489952447148:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 7709 = 273489952447148 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 7709 = (15709:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_7709
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 7710) ≤ val WuPaper.ClassicalFourthData.Bq 7710
    have hp : val WuPaper.ClassicalFourthData.Bq 7710 = (273494288094488:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 7710 = 273494288094488 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 7710 = (1571:ℝ)/400 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_7710
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 7711) ≤ val WuPaper.ClassicalFourthData.Bq 7711
    have hp : val WuPaper.ClassicalFourthData.Bq 7711 = (273498621333201:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 7711 = 273498621333201 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 7711 = (15711:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_7711
end WuPaper.ClassicalFourthConditions
#print axioms WuPaper.ClassicalFourthConditions.Log_block_481

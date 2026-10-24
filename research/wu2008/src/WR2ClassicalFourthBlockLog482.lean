import WR2ClassicalFourthConditions
import WR2ClassicalFourthLogPoints482
noncomputable section
namespace WuPaper.ClassicalFourthConditions
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem Log_block_482 (j : Fin 16) (hj : 16*482+j.val < 10541) :
    WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 (16*482+j.val)) ≤ val WuPaper.ClassicalFourthData.Bq (16*482+j.val) := by
  fin_cases j
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 7712) ≤ val WuPaper.ClassicalFourthData.Bq 7712
    have hp : val WuPaper.ClassicalFourthData.Bq 7712 = (273502952164063:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 7712 = 273502952164063 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 7712 = (491:ℝ)/125 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_7712
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 7713) ≤ val WuPaper.ClassicalFourthData.Bq 7713
    have hp : val WuPaper.ClassicalFourthData.Bq 7713 = (273507280587850:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 7713 = 273507280587850 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 7713 = (15713:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_7713
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 7714) ≤ val WuPaper.ClassicalFourthData.Bq 7714
    have hp : val WuPaper.ClassicalFourthData.Bq 7714 = (273511606605340:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 7714 = 273511606605340 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 7714 = (7857:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_7714
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 7715) ≤ val WuPaper.ClassicalFourthData.Bq 7715
    have hp : val WuPaper.ClassicalFourthData.Bq 7715 = (273515930217308:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 7715 = 273515930217308 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 7715 = (3143:ℝ)/800 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_7715
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 7716) ≤ val WuPaper.ClassicalFourthData.Bq 7716
    have hp : val WuPaper.ClassicalFourthData.Bq 7716 = (273520251424531:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 7716 = 273520251424531 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 7716 = (3929:ℝ)/1000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_7716
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 7717) ≤ val WuPaper.ClassicalFourthData.Bq 7717
    have hp : val WuPaper.ClassicalFourthData.Bq 7717 = (273524570227783:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 7717 = 273524570227783 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 7717 = (15717:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_7717
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 7718) ≤ val WuPaper.ClassicalFourthData.Bq 7718
    have hp : val WuPaper.ClassicalFourthData.Bq 7718 = (273528886627840:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 7718 = 273528886627840 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 7718 = (7859:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_7718
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 7719) ≤ val WuPaper.ClassicalFourthData.Bq 7719
    have hp : val WuPaper.ClassicalFourthData.Bq 7719 = (273533200625477:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 7719 = 273533200625477 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 7719 = (15719:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_7719
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 7720) ≤ val WuPaper.ClassicalFourthData.Bq 7720
    have hp : val WuPaper.ClassicalFourthData.Bq 7720 = (273537512221469:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 7720 = 273537512221469 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 7720 = (393:ℝ)/100 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_7720
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 7721) ≤ val WuPaper.ClassicalFourthData.Bq 7721
    have hp : val WuPaper.ClassicalFourthData.Bq 7721 = (273541821416590:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 7721 = 273541821416590 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 7721 = (15721:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_7721
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 7722) ≤ val WuPaper.ClassicalFourthData.Bq 7722
    have hp : val WuPaper.ClassicalFourthData.Bq 7722 = (273546128211614:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 7722 = 273546128211614 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 7722 = (7861:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_7722
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 7723) ≤ val WuPaper.ClassicalFourthData.Bq 7723
    have hp : val WuPaper.ClassicalFourthData.Bq 7723 = (273550432607316:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 7723 = 273550432607316 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 7723 = (15723:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_7723
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 7724) ≤ val WuPaper.ClassicalFourthData.Bq 7724
    have hp : val WuPaper.ClassicalFourthData.Bq 7724 = (273554734604468:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 7724 = 273554734604468 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 7724 = (3931:ℝ)/1000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_7724
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 7725) ≤ val WuPaper.ClassicalFourthData.Bq 7725
    have hp : val WuPaper.ClassicalFourthData.Bq 7725 = (273559034203845:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 7725 = 273559034203845 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 7725 = (629:ℝ)/160 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_7725
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 7726) ≤ val WuPaper.ClassicalFourthData.Bq 7726
    have hp : val WuPaper.ClassicalFourthData.Bq 7726 = (273563331406219:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 7726 = 273563331406219 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 7726 = (7863:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_7726
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 7727) ≤ val WuPaper.ClassicalFourthData.Bq 7727
    have hp : val WuPaper.ClassicalFourthData.Bq 7727 = (273567626212362:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 7727 = 273567626212362 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 7727 = (15727:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_7727
end WuPaper.ClassicalFourthConditions
#print axioms WuPaper.ClassicalFourthConditions.Log_block_482

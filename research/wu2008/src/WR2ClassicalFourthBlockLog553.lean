import WR2ClassicalFourthConditions
import WR2ClassicalFourthLogPoints553
noncomputable section
namespace WuPaper.ClassicalFourthConditions
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem Log_block_553 (j : Fin 16) (hj : 16*553+j.val < 10541) :
    WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 (16*553+j.val)) ≤ val WuPaper.ClassicalFourthData.Bq (16*553+j.val) := by
  fin_cases j
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 8848) ≤ val WuPaper.ClassicalFourthData.Bq 8848
    have hp : val WuPaper.ClassicalFourthData.Bq 8848 = (277040312463923:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 8848 = 277040312463923 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 8848 = (1053:ℝ)/250 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_8848
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 8849) ≤ val WuPaper.ClassicalFourthData.Bq 8849
    have hp : val WuPaper.ClassicalFourthData.Bq 8849 = (277042347010507:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 8849 = 277042347010507 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 8849 = (16849:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_8849
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 8850) ≤ val WuPaper.ClassicalFourthData.Bq 8850
    have hp : val WuPaper.ClassicalFourthData.Bq 8850 = (277044379877725:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 8850 = 277044379877725 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 8850 = (337:ℝ)/80 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_8850
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 8851) ≤ val WuPaper.ClassicalFourthData.Bq 8851
    have hp : val WuPaper.ClassicalFourthData.Bq 8851 = (277046411066101:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 8851 = 277046411066101 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 8851 = (16851:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_8851
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 8852) ≤ val WuPaper.ClassicalFourthData.Bq 8852
    have hp : val WuPaper.ClassicalFourthData.Bq 8852 = (277048440576157:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 8852 = 277048440576157 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 8852 = (4213:ℝ)/1000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_8852
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 8853) ≤ val WuPaper.ClassicalFourthData.Bq 8853
    have hp : val WuPaper.ClassicalFourthData.Bq 8853 = (277050468408416:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 8853 = 277050468408416 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 8853 = (16853:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_8853
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 8854) ≤ val WuPaper.ClassicalFourthData.Bq 8854
    have hp : val WuPaper.ClassicalFourthData.Bq 8854 = (277052494563399:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 8854 = 277052494563399 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 8854 = (8427:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_8854
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 8855) ≤ val WuPaper.ClassicalFourthData.Bq 8855
    have hp : val WuPaper.ClassicalFourthData.Bq 8855 = (277054519041630:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 8855 = 277054519041630 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 8855 = (3371:ℝ)/800 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_8855
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 8856) ≤ val WuPaper.ClassicalFourthData.Bq 8856
    have hp : val WuPaper.ClassicalFourthData.Bq 8856 = (277056541843629:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 8856 = 277056541843629 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 8856 = (2107:ℝ)/500 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_8856
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 8857) ≤ val WuPaper.ClassicalFourthData.Bq 8857
    have hp : val WuPaper.ClassicalFourthData.Bq 8857 = (277058562969918:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 8857 = 277058562969918 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 8857 = (16857:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_8857
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 8858) ≤ val WuPaper.ClassicalFourthData.Bq 8858
    have hp : val WuPaper.ClassicalFourthData.Bq 8858 = (277060582421019:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 8858 = 277060582421019 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 8858 = (8429:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_8858
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 8859) ≤ val WuPaper.ClassicalFourthData.Bq 8859
    have hp : val WuPaper.ClassicalFourthData.Bq 8859 = (277062600197454:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 8859 = 277062600197454 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 8859 = (16859:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_8859
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 8860) ≤ val WuPaper.ClassicalFourthData.Bq 8860
    have hp : val WuPaper.ClassicalFourthData.Bq 8860 = (277064616299742:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 8860 = 277064616299742 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 8860 = (843:ℝ)/200 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_8860
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 8861) ≤ val WuPaper.ClassicalFourthData.Bq 8861
    have hp : val WuPaper.ClassicalFourthData.Bq 8861 = (277066630728407:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 8861 = 277066630728407 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 8861 = (16861:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_8861
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 8862) ≤ val WuPaper.ClassicalFourthData.Bq 8862
    have hp : val WuPaper.ClassicalFourthData.Bq 8862 = (277068643483967:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 8862 = 277068643483967 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 8862 = (8431:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_8862
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 8863) ≤ val WuPaper.ClassicalFourthData.Bq 8863
    have hp : val WuPaper.ClassicalFourthData.Bq 8863 = (277070654566944:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 8863 = 277070654566944 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 8863 = (16863:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_8863
end WuPaper.ClassicalFourthConditions
#print axioms WuPaper.ClassicalFourthConditions.Log_block_553

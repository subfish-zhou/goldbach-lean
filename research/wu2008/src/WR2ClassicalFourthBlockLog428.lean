import WR2ClassicalFourthConditions
import WR2ClassicalFourthLogPoints428
noncomputable section
namespace WuPaper.ClassicalFourthConditions
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem Log_block_428 (j : Fin 16) (hj : 16*428+j.val < 10541) :
    WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 (16*428+j.val)) ≤ val WuPaper.ClassicalFourthData.Bq (16*428+j.val) := by
  fin_cases j
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 6848) ≤ val WuPaper.ClassicalFourthData.Bq 6848
    have hp : val WuPaper.ClassicalFourthData.Bq 6848 = (268773267801273:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 6848 = 268773267801273 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 6848 = (464:ℝ)/125 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_6848
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 6849) ≤ val WuPaper.ClassicalFourthData.Bq 6849
    have hp : val WuPaper.ClassicalFourthData.Bq 6849 = (268779998308465:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 6849 = 268779998308465 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 6849 = (14849:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_6849
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 6850) ≤ val WuPaper.ClassicalFourthData.Bq 6850
    have hp : val WuPaper.ClassicalFourthData.Bq 6850 = (268786725620675:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 6850 = 268786725620675 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 6850 = (297:ℝ)/80 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_6850
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 6851) ≤ val WuPaper.ClassicalFourthData.Bq 6851
    have hp : val WuPaper.ClassicalFourthData.Bq 6851 = (268793449738969:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 6851 = 268793449738969 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 6851 = (14851:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_6851
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 6852) ≤ val WuPaper.ClassicalFourthData.Bq 6852
    have hp : val WuPaper.ClassicalFourthData.Bq 6852 = (268800170664415:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 6852 = 268800170664415 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 6852 = (3713:ℝ)/1000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_6852
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 6853) ≤ val WuPaper.ClassicalFourthData.Bq 6853
    have hp : val WuPaper.ClassicalFourthData.Bq 6853 = (268806888398079:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 6853 = 268806888398079 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 6853 = (14853:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_6853
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 6854) ≤ val WuPaper.ClassicalFourthData.Bq 6854
    have hp : val WuPaper.ClassicalFourthData.Bq 6854 = (268813602941026:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 6854 = 268813602941026 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 6854 = (7427:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_6854
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 6855) ≤ val WuPaper.ClassicalFourthData.Bq 6855
    have hp : val WuPaper.ClassicalFourthData.Bq 6855 = (268820314294324:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 6855 = 268820314294324 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 6855 = (2971:ℝ)/800 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_6855
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 6856) ≤ val WuPaper.ClassicalFourthData.Bq 6856
    have hp : val WuPaper.ClassicalFourthData.Bq 6856 = (268827022459035:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 6856 = 268827022459035 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 6856 = (1857:ℝ)/500 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_6856
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 6857) ≤ val WuPaper.ClassicalFourthData.Bq 6857
    have hp : val WuPaper.ClassicalFourthData.Bq 6857 = (268833727436227:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 6857 = 268833727436227 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 6857 = (14857:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_6857
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 6858) ≤ val WuPaper.ClassicalFourthData.Bq 6858
    have hp : val WuPaper.ClassicalFourthData.Bq 6858 = (268840429226962:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 6858 = 268840429226962 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 6858 = (7429:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_6858
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 6859) ≤ val WuPaper.ClassicalFourthData.Bq 6859
    have hp : val WuPaper.ClassicalFourthData.Bq 6859 = (268847127832305:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 6859 = 268847127832305 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 6859 = (14859:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_6859
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 6860) ≤ val WuPaper.ClassicalFourthData.Bq 6860
    have hp : val WuPaper.ClassicalFourthData.Bq 6860 = (268853823253319:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 6860 = 268853823253319 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 6860 = (743:ℝ)/200 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_6860
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 6861) ≤ val WuPaper.ClassicalFourthData.Bq 6861
    have hp : val WuPaper.ClassicalFourthData.Bq 6861 = (268860515491068:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 6861 = 268860515491068 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 6861 = (14861:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_6861
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 6862) ≤ val WuPaper.ClassicalFourthData.Bq 6862
    have hp : val WuPaper.ClassicalFourthData.Bq 6862 = (268867204546614:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 6862 = 268867204546614 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 6862 = (7431:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_6862
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 6863) ≤ val WuPaper.ClassicalFourthData.Bq 6863
    have hp : val WuPaper.ClassicalFourthData.Bq 6863 = (268873890421020:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 6863 = 268873890421020 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 6863 = (14863:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_6863
end WuPaper.ClassicalFourthConditions
#print axioms WuPaper.ClassicalFourthConditions.Log_block_428

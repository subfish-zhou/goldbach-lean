import WR2ClassicalFourthConditions
import WR2ClassicalFourthLogPoints303
noncomputable section
namespace WuPaper.ClassicalFourthConditions
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem Log_block_303 (j : Fin 16) (hj : 16*303+j.val < 10541) :
    WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 (16*303+j.val)) ≤ val WuPaper.ClassicalFourthData.Bq (16*303+j.val) := by
  fin_cases j
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 4848) ≤ val WuPaper.ClassicalFourthData.Bq 4848
    have hp : val WuPaper.ClassicalFourthData.Bq 4848 = (247165966270265:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 4848 = 247165966270265 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 4848 = (803:ℝ)/250 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_4848
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 4849) ≤ val WuPaper.ClassicalFourthData.Bq 4849
    have hp : val WuPaper.ClassicalFourthData.Bq 4849 = (247181912106880:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 4849 = 247181912106880 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 4849 = (12849:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_4849
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 4850) ≤ val WuPaper.ClassicalFourthData.Bq 4850
    have hp : val WuPaper.ClassicalFourthData.Bq 4850 = (247197851486366:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 4850 = 247197851486366 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 4850 = (257:ℝ)/80 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_4850
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 4851) ≤ val WuPaper.ClassicalFourthData.Bq 4851
    have hp : val WuPaper.ClassicalFourthData.Bq 4851 = (247213784411128:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 4851 = 247213784411128 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 4851 = (12851:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_4851
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 4852) ≤ val WuPaper.ClassicalFourthData.Bq 4852
    have hp : val WuPaper.ClassicalFourthData.Bq 4852 = (247229710883571:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 4852 = 247229710883571 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 4852 = (3213:ℝ)/1000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_4852
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 4853) ≤ val WuPaper.ClassicalFourthData.Bq 4853
    have hp : val WuPaper.ClassicalFourthData.Bq 4853 = (247245630906099:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 4853 = 247245630906099 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 4853 = (12853:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_4853
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 4854) ≤ val WuPaper.ClassicalFourthData.Bq 4854
    have hp : val WuPaper.ClassicalFourthData.Bq 4854 = (247261544481114:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 4854 = 247261544481114 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 4854 = (6427:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_4854
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 4855) ≤ val WuPaper.ClassicalFourthData.Bq 4855
    have hp : val WuPaper.ClassicalFourthData.Bq 4855 = (247277451611018:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 4855 = 247277451611018 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 4855 = (2571:ℝ)/800 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_4855
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 4856) ≤ val WuPaper.ClassicalFourthData.Bq 4856
    have hp : val WuPaper.ClassicalFourthData.Bq 4856 = (247293352298210:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 4856 = 247293352298210 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 4856 = (1607:ℝ)/500 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_4856
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 4857) ≤ val WuPaper.ClassicalFourthData.Bq 4857
    have hp : val WuPaper.ClassicalFourthData.Bq 4857 = (247309246545091:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 4857 = 247309246545091 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 4857 = (12857:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_4857
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 4858) ≤ val WuPaper.ClassicalFourthData.Bq 4858
    have hp : val WuPaper.ClassicalFourthData.Bq 4858 = (247325134354057:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 4858 = 247325134354057 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 4858 = (6429:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_4858
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 4859) ≤ val WuPaper.ClassicalFourthData.Bq 4859
    have hp : val WuPaper.ClassicalFourthData.Bq 4859 = (247341015727508:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 4859 = 247341015727508 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 4859 = (12859:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_4859
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 4860) ≤ val WuPaper.ClassicalFourthData.Bq 4860
    have hp : val WuPaper.ClassicalFourthData.Bq 4860 = (247356890667839:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 4860 = 247356890667839 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 4860 = (643:ℝ)/200 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_4860
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 4861) ≤ val WuPaper.ClassicalFourthData.Bq 4861
    have hp : val WuPaper.ClassicalFourthData.Bq 4861 = (247372759177444:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 4861 = 247372759177444 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 4861 = (12861:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_4861
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 4862) ≤ val WuPaper.ClassicalFourthData.Bq 4862
    have hp : val WuPaper.ClassicalFourthData.Bq 4862 = (247388621258718:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 4862 = 247388621258718 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 4862 = (6431:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_4862
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 4863) ≤ val WuPaper.ClassicalFourthData.Bq 4863
    have hp : val WuPaper.ClassicalFourthData.Bq 4863 = (247404476914055:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 4863 = 247404476914055 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 4863 = (12863:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_4863
end WuPaper.ClassicalFourthConditions
#print axioms WuPaper.ClassicalFourthConditions.Log_block_303

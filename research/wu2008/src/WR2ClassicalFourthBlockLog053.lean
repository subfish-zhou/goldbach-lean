import WR2ClassicalFourthConditions
import WR2ClassicalFourthLogPoints053
noncomputable section
namespace WuPaper.ClassicalFourthConditions
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem Log_block_053 (j : Fin 16) (hj : 16*53+j.val < 10541) :
    WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 (16*53+j.val)) ≤ val WuPaper.ClassicalFourthData.Bq (16*53+j.val) := by
  fin_cases j
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 848) ≤ val WuPaper.ClassicalFourthData.Bq 848
    have hp : val WuPaper.ClassicalFourthData.Bq 848 = (86922191522208:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 848 = 86922191522208 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 848 = (553:ℝ)/250 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_848
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 849) ≤ val WuPaper.ClassicalFourthData.Bq 849
    have hp : val WuPaper.ClassicalFourthData.Bq 849 = (87005599278258:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 849 = 87005599278258 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 849 = (8849:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_849
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 850) ≤ val WuPaper.ClassicalFourthData.Bq 850
    have hp : val WuPaper.ClassicalFourthData.Bq 850 = (87088968962487:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 850 = 87088968962487 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 850 = (177:ℝ)/80 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_850
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 851) ≤ val WuPaper.ClassicalFourthData.Bq 851
    have hp : val WuPaper.ClassicalFourthData.Bq 851 = (87172300595725:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 851 = 87172300595725 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 851 = (8851:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_851
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 852) ≤ val WuPaper.ClassicalFourthData.Bq 852
    have hp : val WuPaper.ClassicalFourthData.Bq 852 = (87255594198786:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 852 = 87255594198786 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 852 = (2213:ℝ)/1000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_852
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 853) ≤ val WuPaper.ClassicalFourthData.Bq 853
    have hp : val WuPaper.ClassicalFourthData.Bq 853 = (87338849792472:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 853 = 87338849792472 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 853 = (8853:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_853
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 854) ≤ val WuPaper.ClassicalFourthData.Bq 854
    have hp : val WuPaper.ClassicalFourthData.Bq 854 = (87422067397570:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 854 = 87422067397570 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 854 = (4427:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_854
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 855) ≤ val WuPaper.ClassicalFourthData.Bq 855
    have hp : val WuPaper.ClassicalFourthData.Bq 855 = (87505247034850:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 855 = 87505247034850 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 855 = (1771:ℝ)/800 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_855
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 856) ≤ val WuPaper.ClassicalFourthData.Bq 856
    have hp : val WuPaper.ClassicalFourthData.Bq 856 = (87588388725071:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 856 = 87588388725071 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 856 = (1107:ℝ)/500 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_856
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 857) ≤ val WuPaper.ClassicalFourthData.Bq 857
    have hp : val WuPaper.ClassicalFourthData.Bq 857 = (87671492488977:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 857 = 87671492488977 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 857 = (8857:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_857
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 858) ≤ val WuPaper.ClassicalFourthData.Bq 858
    have hp : val WuPaper.ClassicalFourthData.Bq 858 = (87754558347298:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 858 = 87754558347298 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 858 = (4429:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_858
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 859) ≤ val WuPaper.ClassicalFourthData.Bq 859
    have hp : val WuPaper.ClassicalFourthData.Bq 859 = (87837586320748:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 859 = 87837586320748 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 859 = (8859:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_859
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 860) ≤ val WuPaper.ClassicalFourthData.Bq 860
    have hp : val WuPaper.ClassicalFourthData.Bq 860 = (87920576430028:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 860 = 87920576430028 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 860 = (443:ℝ)/200 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_860
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 861) ≤ val WuPaper.ClassicalFourthData.Bq 861
    have hp : val WuPaper.ClassicalFourthData.Bq 861 = (88003528695826:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 861 = 88003528695826 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 861 = (8861:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_861
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 862) ≤ val WuPaper.ClassicalFourthData.Bq 862
    have hp : val WuPaper.ClassicalFourthData.Bq 862 = (88086443138814:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 862 = 88086443138814 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 862 = (4431:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_862
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 863) ≤ val WuPaper.ClassicalFourthData.Bq 863
    have hp : val WuPaper.ClassicalFourthData.Bq 863 = (88169319779650:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 863 = 88169319779650 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 863 = (8863:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_863
end WuPaper.ClassicalFourthConditions
#print axioms WuPaper.ClassicalFourthConditions.Log_block_053

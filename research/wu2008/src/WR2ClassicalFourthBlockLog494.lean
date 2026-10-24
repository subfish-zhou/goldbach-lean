import WR2ClassicalFourthConditions
import WR2ClassicalFourthLogPoints494
noncomputable section
namespace WuPaper.ClassicalFourthConditions
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem Log_block_494 (j : Fin 16) (hj : 16*494+j.val < 10541) :
    WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 (16*494+j.val)) ≤ val WuPaper.ClassicalFourthData.Bq (16*494+j.val) := by
  fin_cases j
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 7904) ≤ val WuPaper.ClassicalFourthData.Bq 7904
    have hp : val WuPaper.ClassicalFourthData.Bq 7904 = (274290773886551:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 7904 = 274290773886551 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 7904 = (497:ℝ)/125 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_7904
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 7905) ≤ val WuPaper.ClassicalFourthData.Bq 7905
    have hp : val WuPaper.ClassicalFourthData.Bq 7905 = (274294654214655:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 7905 = 274294654214655 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 7905 = (3181:ℝ)/800 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_7905
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 7906) ≤ val WuPaper.ClassicalFourthData.Bq 7906
    have hp : val WuPaper.ClassicalFourthData.Bq 7906 = (274298532280498:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 7906 = 274298532280498 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 7906 = (7953:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_7906
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 7907) ≤ val WuPaper.ClassicalFourthData.Bq 7907
    have hp : val WuPaper.ClassicalFourthData.Bq 7907 = (274302408084804:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 7907 = 274302408084804 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 7907 = (15907:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_7907
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 7908) ≤ val WuPaper.ClassicalFourthData.Bq 7908
    have hp : val WuPaper.ClassicalFourthData.Bq 7908 = (274306281628298:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 7908 = 274306281628298 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 7908 = (3977:ℝ)/1000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_7908
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 7909) ≤ val WuPaper.ClassicalFourthData.Bq 7909
    have hp : val WuPaper.ClassicalFourthData.Bq 7909 = (274310152911704:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 7909 = 274310152911704 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 7909 = (15909:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_7909
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 7910) ≤ val WuPaper.ClassicalFourthData.Bq 7910
    have hp : val WuPaper.ClassicalFourthData.Bq 7910 = (274314021935745:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 7910 = 274314021935745 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 7910 = (1591:ℝ)/400 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_7910
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 7911) ≤ val WuPaper.ClassicalFourthData.Bq 7911
    have hp : val WuPaper.ClassicalFourthData.Bq 7911 = (274317888701147:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 7911 = 274317888701147 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 7911 = (15911:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_7911
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 7912) ≤ val WuPaper.ClassicalFourthData.Bq 7912
    have hp : val WuPaper.ClassicalFourthData.Bq 7912 = (274321753208631:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 7912 = 274321753208631 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 7912 = (1989:ℝ)/500 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_7912
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 7913) ≤ val WuPaper.ClassicalFourthData.Bq 7913
    have hp : val WuPaper.ClassicalFourthData.Bq 7913 = (274325615458922:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 7913 = 274325615458922 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 7913 = (15913:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_7913
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 7914) ≤ val WuPaper.ClassicalFourthData.Bq 7914
    have hp : val WuPaper.ClassicalFourthData.Bq 7914 = (274329475452742:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 7914 = 274329475452742 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 7914 = (7957:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_7914
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 7915) ≤ val WuPaper.ClassicalFourthData.Bq 7915
    have hp : val WuPaper.ClassicalFourthData.Bq 7915 = (274333333190813:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 7915 = 274333333190813 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 7915 = (3183:ℝ)/800 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_7915
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 7916) ≤ val WuPaper.ClassicalFourthData.Bq 7916
    have hp : val WuPaper.ClassicalFourthData.Bq 7916 = (274337188673858:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 7916 = 274337188673858 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 7916 = (3979:ℝ)/1000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_7916
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 7917) ≤ val WuPaper.ClassicalFourthData.Bq 7917
    have hp : val WuPaper.ClassicalFourthData.Bq 7917 = (274341041902600:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 7917 = 274341041902600 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 7917 = (15917:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_7917
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 7918) ≤ val WuPaper.ClassicalFourthData.Bq 7918
    have hp : val WuPaper.ClassicalFourthData.Bq 7918 = (274344892877759:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 7918 = 274344892877759 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 7918 = (7959:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_7918
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 7919) ≤ val WuPaper.ClassicalFourthData.Bq 7919
    have hp : val WuPaper.ClassicalFourthData.Bq 7919 = (274348741600058:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 7919 = 274348741600058 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 7919 = (15919:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_7919
end WuPaper.ClassicalFourthConditions
#print axioms WuPaper.ClassicalFourthConditions.Log_block_494

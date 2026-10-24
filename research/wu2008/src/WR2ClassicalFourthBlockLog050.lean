import WR2ClassicalFourthConditions
import WR2ClassicalFourthLogPoints050
noncomputable section
namespace WuPaper.ClassicalFourthConditions
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem Log_block_050 (j : Fin 16) (hj : 16*50+j.val < 10541) :
    WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 (16*50+j.val)) ≤ val WuPaper.ClassicalFourthData.Bq (16*50+j.val) := by
  fin_cases j
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 800) ≤ val WuPaper.ClassicalFourthData.Bq 800
    have hp : val WuPaper.ClassicalFourthData.Bq 800 = (82873434906344:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 800 = 82873434906344 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 800 = (11:ℝ)/5 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_800
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 801) ≤ val WuPaper.ClassicalFourthData.Bq 801
    have hp : val WuPaper.ClassicalFourthData.Bq 801 = (82958694888723:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 801 = 82958694888723 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 801 = (8801:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_801
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 802) ≤ val WuPaper.ClassicalFourthData.Bq 802
    have hp : val WuPaper.ClassicalFourthData.Bq 802 = (83043915782400:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 802 = 83043915782400 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 802 = (4401:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_802
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 803) ≤ val WuPaper.ClassicalFourthData.Bq 803
    have hp : val WuPaper.ClassicalFourthData.Bq 803 = (83129097608905:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 803 = 83129097608905 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 803 = (8803:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_803
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 804) ≤ val WuPaper.ClassicalFourthData.Bq 804
    have hp : val WuPaper.ClassicalFourthData.Bq 804 = (83214240389754:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 804 = 83214240389754 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 804 = (2201:ℝ)/1000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_804
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 805) ≤ val WuPaper.ClassicalFourthData.Bq 805
    have hp : val WuPaper.ClassicalFourthData.Bq 805 = (83299344146447:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 805 = 83299344146447 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 805 = (1761:ℝ)/800 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_805
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 806) ≤ val WuPaper.ClassicalFourthData.Bq 806
    have hp : val WuPaper.ClassicalFourthData.Bq 806 = (83384408900471:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 806 = 83384408900471 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 806 = (4403:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_806
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 807) ≤ val WuPaper.ClassicalFourthData.Bq 807
    have hp : val WuPaper.ClassicalFourthData.Bq 807 = (83469434673298:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 807 = 83469434673298 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 807 = (8807:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_807
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 808) ≤ val WuPaper.ClassicalFourthData.Bq 808
    have hp : val WuPaper.ClassicalFourthData.Bq 808 = (83554421486384:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 808 = 83554421486384 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 808 = (1101:ℝ)/500 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_808
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 809) ≤ val WuPaper.ClassicalFourthData.Bq 809
    have hp : val WuPaper.ClassicalFourthData.Bq 809 = (83639369361170:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 809 = 83639369361170 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 809 = (8809:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_809
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 810) ≤ val WuPaper.ClassicalFourthData.Bq 810
    have hp : val WuPaper.ClassicalFourthData.Bq 810 = (83724278319083:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 810 = 83724278319083 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 810 = (881:ℝ)/400 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_810
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 811) ≤ val WuPaper.ClassicalFourthData.Bq 811
    have hp : val WuPaper.ClassicalFourthData.Bq 811 = (83809148381535:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 811 = 83809148381535 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 811 = (8811:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_811
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 812) ≤ val WuPaper.ClassicalFourthData.Bq 812
    have hp : val WuPaper.ClassicalFourthData.Bq 812 = (83893979569924:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 812 = 83893979569924 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 812 = (2203:ℝ)/1000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_812
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 813) ≤ val WuPaper.ClassicalFourthData.Bq 813
    have hp : val WuPaper.ClassicalFourthData.Bq 813 = (83978771905632:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 813 = 83978771905632 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 813 = (8813:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_813
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 814) ≤ val WuPaper.ClassicalFourthData.Bq 814
    have hp : val WuPaper.ClassicalFourthData.Bq 814 = (84063525410025:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 814 = 84063525410025 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 814 = (4407:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_814
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 815) ≤ val WuPaper.ClassicalFourthData.Bq 815
    have hp : val WuPaper.ClassicalFourthData.Bq 815 = (84148240104458:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 815 = 84148240104458 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 815 = (1763:ℝ)/800 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_815
end WuPaper.ClassicalFourthConditions
#print axioms WuPaper.ClassicalFourthConditions.Log_block_050

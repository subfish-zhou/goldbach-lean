import WR2ClassicalFourthConditions
import WR2ClassicalFourthLogPoints493
noncomputable section
namespace WuPaper.ClassicalFourthConditions
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem Log_block_493 (j : Fin 16) (hj : 16*493+j.val < 10541) :
    WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 (16*493+j.val)) ≤ val WuPaper.ClassicalFourthData.Bq (16*493+j.val) := by
  fin_cases j
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 7888) ≤ val WuPaper.ClassicalFourthData.Bq 7888
    have hp : val WuPaper.ClassicalFourthData.Bq 7888 = (274228380377020:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 7888 = 274228380377020 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 7888 = (993:ℝ)/250 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_7888
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 7889) ≤ val WuPaper.ClassicalFourthData.Bq 7889
    have hp : val WuPaper.ClassicalFourthData.Bq 7889 = (274232297000071:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 7889 = 274232297000071 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 7889 = (15889:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_7889
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 7890) ≤ val WuPaper.ClassicalFourthData.Bq 7890
    have hp : val WuPaper.ClassicalFourthData.Bq 7890 = (274236211349231:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 7890 = 274236211349231 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 7890 = (1589:ℝ)/400 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_7890
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 7891) ≤ val WuPaper.ClassicalFourthData.Bq 7891
    have hp : val WuPaper.ClassicalFourthData.Bq 7891 = (274240123425228:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 7891 = 274240123425228 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 7891 = (15891:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_7891
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 7892) ≤ val WuPaper.ClassicalFourthData.Bq 7892
    have hp : val WuPaper.ClassicalFourthData.Bq 7892 = (274244033228792:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 7892 = 274244033228792 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 7892 = (3973:ℝ)/1000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_7892
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 7893) ≤ val WuPaper.ClassicalFourthData.Bq 7893
    have hp : val WuPaper.ClassicalFourthData.Bq 7893 = (274247940760650:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 7893 = 274247940760650 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 7893 = (15893:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_7893
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 7894) ≤ val WuPaper.ClassicalFourthData.Bq 7894
    have hp : val WuPaper.ClassicalFourthData.Bq 7894 = (274251846021530:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 7894 = 274251846021530 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 7894 = (7947:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_7894
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 7895) ≤ val WuPaper.ClassicalFourthData.Bq 7895
    have hp : val WuPaper.ClassicalFourthData.Bq 7895 = (274255749012161:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 7895 = 274255749012161 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 7895 = (3179:ℝ)/800 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_7895
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 7896) ≤ val WuPaper.ClassicalFourthData.Bq 7896
    have hp : val WuPaper.ClassicalFourthData.Bq 7896 = (274259649733269:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 7896 = 274259649733269 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 7896 = (1987:ℝ)/500 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_7896
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 7897) ≤ val WuPaper.ClassicalFourthData.Bq 7897
    have hp : val WuPaper.ClassicalFourthData.Bq 7897 = (274263548185582:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 7897 = 274263548185582 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 7897 = (15897:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_7897
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 7898) ≤ val WuPaper.ClassicalFourthData.Bq 7898
    have hp : val WuPaper.ClassicalFourthData.Bq 7898 = (274267444369827:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 7898 = 274267444369827 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 7898 = (7949:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_7898
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 7899) ≤ val WuPaper.ClassicalFourthData.Bq 7899
    have hp : val WuPaper.ClassicalFourthData.Bq 7899 = (274271338286732:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 7899 = 274271338286732 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 7899 = (15899:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_7899
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 7900) ≤ val WuPaper.ClassicalFourthData.Bq 7900
    have hp : val WuPaper.ClassicalFourthData.Bq 7900 = (274275229937021:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 7900 = 274275229937021 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 7900 = (159:ℝ)/40 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_7900
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 7901) ≤ val WuPaper.ClassicalFourthData.Bq 7901
    have hp : val WuPaper.ClassicalFourthData.Bq 7901 = (274279119321422:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 7901 = 274279119321422 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 7901 = (15901:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_7901
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 7902) ≤ val WuPaper.ClassicalFourthData.Bq 7902
    have hp : val WuPaper.ClassicalFourthData.Bq 7902 = (274283006440660:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 7902 = 274283006440660 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 7902 = (7951:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_7902
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 7903) ≤ val WuPaper.ClassicalFourthData.Bq 7903
    have hp : val WuPaper.ClassicalFourthData.Bq 7903 = (274286891295461:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 7903 = 274286891295461 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 7903 = (15903:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_7903
end WuPaper.ClassicalFourthConditions
#print axioms WuPaper.ClassicalFourthConditions.Log_block_493

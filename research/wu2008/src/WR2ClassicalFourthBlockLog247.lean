import WR2ClassicalFourthConditions
import WR2ClassicalFourthLogPoints247
noncomputable section
namespace WuPaper.ClassicalFourthConditions
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem Log_block_247 (j : Fin 16) (hj : 16*247+j.val < 10541) :
    WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 (16*247+j.val)) ≤ val WuPaper.ClassicalFourthData.Bq (16*247+j.val) := by
  fin_cases j
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 3952) ≤ val WuPaper.ClassicalFourthData.Bq 3952
    have hp : val WuPaper.ClassicalFourthData.Bq 3952 = (229962887628643:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 3952 = 229962887628643 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 3952 = (747:ℝ)/250 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_3952
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 3953) ≤ val WuPaper.ClassicalFourthData.Bq 3953
    have hp : val WuPaper.ClassicalFourthData.Bq 3953 = (229985729057177:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 3953 = 229985729057177 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 3953 = (11953:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_3953
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 3954) ≤ val WuPaper.ClassicalFourthData.Bq 3954
    have hp : val WuPaper.ClassicalFourthData.Bq 3954 = (230008561373803:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 3954 = 230008561373803 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 3954 = (5977:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_3954
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 3955) ≤ val WuPaper.ClassicalFourthData.Bq 3955
    have hp : val WuPaper.ClassicalFourthData.Bq 3955 = (230031384582137:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 3955 = 230031384582137 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 3955 = (2391:ℝ)/800 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_3955
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 3956) ≤ val WuPaper.ClassicalFourthData.Bq 3956
    have hp : val WuPaper.ClassicalFourthData.Bq 3956 = (230054198685793:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 3956 = 230054198685793 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 3956 = (2989:ℝ)/1000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_3956
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 3957) ≤ val WuPaper.ClassicalFourthData.Bq 3957
    have hp : val WuPaper.ClassicalFourthData.Bq 3957 = (230077003688386:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 3957 = 230077003688386 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 3957 = (11957:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_3957
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 3958) ≤ val WuPaper.ClassicalFourthData.Bq 3958
    have hp : val WuPaper.ClassicalFourthData.Bq 3958 = (230099799593527:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 3958 = 230099799593527 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 3958 = (5979:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_3958
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 3959) ≤ val WuPaper.ClassicalFourthData.Bq 3959
    have hp : val WuPaper.ClassicalFourthData.Bq 3959 = (230122586404824:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 3959 = 230122586404824 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 3959 = (11959:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_3959
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 3960) ≤ val WuPaper.ClassicalFourthData.Bq 3960
    have hp : val WuPaper.ClassicalFourthData.Bq 3960 = (230145364125887:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 3960 = 230145364125887 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 3960 = (299:ℝ)/100 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_3960
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 3961) ≤ val WuPaper.ClassicalFourthData.Bq 3961
    have hp : val WuPaper.ClassicalFourthData.Bq 3961 = (230168132760322:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 3961 = 230168132760322 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 3961 = (11961:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_3961
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 3962) ≤ val WuPaper.ClassicalFourthData.Bq 3962
    have hp : val WuPaper.ClassicalFourthData.Bq 3962 = (230190892311733:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 3962 = 230190892311733 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 3962 = (5981:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_3962
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 3963) ≤ val WuPaper.ClassicalFourthData.Bq 3963
    have hp : val WuPaper.ClassicalFourthData.Bq 3963 = (230213642783723:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 3963 = 230213642783723 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 3963 = (11963:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_3963
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 3964) ≤ val WuPaper.ClassicalFourthData.Bq 3964
    have hp : val WuPaper.ClassicalFourthData.Bq 3964 = (230236384179893:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 3964 = 230236384179893 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 3964 = (2991:ℝ)/1000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_3964
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 3965) ≤ val WuPaper.ClassicalFourthData.Bq 3965
    have hp : val WuPaper.ClassicalFourthData.Bq 3965 = (230259116503844:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 3965 = 230259116503844 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 3965 = (2393:ℝ)/800 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_3965
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 3966) ≤ val WuPaper.ClassicalFourthData.Bq 3966
    have hp : val WuPaper.ClassicalFourthData.Bq 3966 = (230281839759172:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 3966 = 230281839759172 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 3966 = (5983:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_3966
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 3967) ≤ val WuPaper.ClassicalFourthData.Bq 3967
    have hp : val WuPaper.ClassicalFourthData.Bq 3967 = (230304553949474:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 3967 = 230304553949474 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 3967 = (11967:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_3967
end WuPaper.ClassicalFourthConditions
#print axioms WuPaper.ClassicalFourthConditions.Log_block_247

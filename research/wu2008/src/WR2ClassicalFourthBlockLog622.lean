import WR2ClassicalFourthConditions
import WR2ClassicalFourthLogPoints622
noncomputable section
namespace WuPaper.ClassicalFourthConditions
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem Log_block_622 (j : Fin 16) (hj : 16*622+j.val < 10541) :
    WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 (16*622+j.val)) ≤ val WuPaper.ClassicalFourthData.Bq (16*622+j.val) := by
  fin_cases j
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 9952) ≤ val WuPaper.ClassicalFourthData.Bq 9952
    have hp : val WuPaper.ClassicalFourthData.Bq 9952 = (278370879263606:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 9952 = 278370879263606 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 9952 = (561:ℝ)/125 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_9952
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 9953) ≤ val WuPaper.ClassicalFourthData.Bq 9953
    have hp : val WuPaper.ClassicalFourthData.Bq 9953 = (278371342478393:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 9953 = 278371342478393 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 9953 = (17953:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_9953
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 9954) ≤ val WuPaper.ClassicalFourthData.Bq 9954
    have hp : val WuPaper.ClassicalFourthData.Bq 9954 = (278371804497218:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 9954 = 278371804497218 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 9954 = (8977:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_9954
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 9955) ≤ val WuPaper.ClassicalFourthData.Bq 9955
    have hp : val WuPaper.ClassicalFourthData.Bq 9955 = (278372265320444:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 9955 = 278372265320444 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 9955 = (3591:ℝ)/800 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_9955
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 9956) ≤ val WuPaper.ClassicalFourthData.Bq 9956
    have hp : val WuPaper.ClassicalFourthData.Bq 9956 = (278372724948435:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 9956 = 278372724948435 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 9956 = (4489:ℝ)/1000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_9956
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 9957) ≤ val WuPaper.ClassicalFourthData.Bq 9957
    have hp : val WuPaper.ClassicalFourthData.Bq 9957 = (278373183381554:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 9957 = 278373183381554 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 9957 = (17957:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_9957
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 9958) ≤ val WuPaper.ClassicalFourthData.Bq 9958
    have hp : val WuPaper.ClassicalFourthData.Bq 9958 = (278373640620166:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 9958 = 278373640620166 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 9958 = (8979:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_9958
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 9959) ≤ val WuPaper.ClassicalFourthData.Bq 9959
    have hp : val WuPaper.ClassicalFourthData.Bq 9959 = (278374096664633:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 9959 = 278374096664633 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 9959 = (17959:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_9959
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 9960) ≤ val WuPaper.ClassicalFourthData.Bq 9960
    have hp : val WuPaper.ClassicalFourthData.Bq 9960 = (278374551515319:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 9960 = 278374551515319 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 9960 = (449:ℝ)/100 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_9960
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 9961) ≤ val WuPaper.ClassicalFourthData.Bq 9961
    have hp : val WuPaper.ClassicalFourthData.Bq 9961 = (278375005172586:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 9961 = 278375005172586 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 9961 = (17961:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_9961
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 9962) ≤ val WuPaper.ClassicalFourthData.Bq 9962
    have hp : val WuPaper.ClassicalFourthData.Bq 9962 = (278375457636799:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 9962 = 278375457636799 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 9962 = (8981:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_9962
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 9963) ≤ val WuPaper.ClassicalFourthData.Bq 9963
    have hp : val WuPaper.ClassicalFourthData.Bq 9963 = (278375908908319:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 9963 = 278375908908319 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 9963 = (17963:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_9963
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 9964) ≤ val WuPaper.ClassicalFourthData.Bq 9964
    have hp : val WuPaper.ClassicalFourthData.Bq 9964 = (278376358987510:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 9964 = 278376358987510 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 9964 = (4491:ℝ)/1000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_9964
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 9965) ≤ val WuPaper.ClassicalFourthData.Bq 9965
    have hp : val WuPaper.ClassicalFourthData.Bq 9965 = (278376807874734:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 9965 = 278376807874734 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 9965 = (3593:ℝ)/800 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_9965
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 9966) ≤ val WuPaper.ClassicalFourthData.Bq 9966
    have hp : val WuPaper.ClassicalFourthData.Bq 9966 = (278377255570354:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 9966 = 278377255570354 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 9966 = (8983:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_9966
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 9967) ≤ val WuPaper.ClassicalFourthData.Bq 9967
    have hp : val WuPaper.ClassicalFourthData.Bq 9967 = (278377702074732:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 9967 = 278377702074732 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 9967 = (17967:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_9967
end WuPaper.ClassicalFourthConditions
#print axioms WuPaper.ClassicalFourthConditions.Log_block_622

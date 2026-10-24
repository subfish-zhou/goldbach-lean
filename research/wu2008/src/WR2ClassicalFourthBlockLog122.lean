import WR2ClassicalFourthConditions
import WR2ClassicalFourthLogPoints122
noncomputable section
namespace WuPaper.ClassicalFourthConditions
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem Log_block_122 (j : Fin 16) (hj : 16*122+j.val < 10541) :
    WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 (16*122+j.val)) ≤ val WuPaper.ClassicalFourthData.Bq (16*122+j.val) := by
  fin_cases j
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 1952) ≤ val WuPaper.ClassicalFourthData.Bq 1952
    have hp : val WuPaper.ClassicalFourthData.Bq 1952 = (159739926210169:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 1952 = 159739926210169 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 1952 = (311:ℝ)/125 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_1952
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 1953) ≤ val WuPaper.ClassicalFourthData.Bq 1953
    have hp : val WuPaper.ClassicalFourthData.Bq 1953 = (159791392766548:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 1953 = 159791392766548 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 1953 = (9953:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_1953
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 1954) ≤ val WuPaper.ClassicalFourthData.Bq 1954
    have hp : val WuPaper.ClassicalFourthData.Bq 1954 = (159842837642634:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 1954 = 159842837642634 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 1954 = (4977:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_1954
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 1955) ≤ val WuPaper.ClassicalFourthData.Bq 1955
    have hp : val WuPaper.ClassicalFourthData.Bq 1955 = (159894260848769:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 1955 = 159894260848769 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 1955 = (1991:ℝ)/800 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_1955
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 1956) ≤ val WuPaper.ClassicalFourthData.Bq 1956
    have hp : val WuPaper.ClassicalFourthData.Bq 1956 = (159945662395289:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 1956 = 159945662395289 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 1956 = (2489:ℝ)/1000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_1956
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 1957) ≤ val WuPaper.ClassicalFourthData.Bq 1957
    have hp : val WuPaper.ClassicalFourthData.Bq 1957 = (159997042292522:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 1957 = 159997042292522 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 1957 = (9957:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_1957
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 1958) ≤ val WuPaper.ClassicalFourthData.Bq 1958
    have hp : val WuPaper.ClassicalFourthData.Bq 1958 = (160048400550794:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 1958 = 160048400550794 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 1958 = (4979:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_1958
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 1959) ≤ val WuPaper.ClassicalFourthData.Bq 1959
    have hp : val WuPaper.ClassicalFourthData.Bq 1959 = (160099737180421:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 1959 = 160099737180421 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 1959 = (9959:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_1959
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 1960) ≤ val WuPaper.ClassicalFourthData.Bq 1960
    have hp : val WuPaper.ClassicalFourthData.Bq 1960 = (160151052191714:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 1960 = 160151052191714 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 1960 = (249:ℝ)/100 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_1960
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 1961) ≤ val WuPaper.ClassicalFourthData.Bq 1961
    have hp : val WuPaper.ClassicalFourthData.Bq 1961 = (160202345594980:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 1961 = 160202345594980 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 1961 = (9961:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_1961
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 1962) ≤ val WuPaper.ClassicalFourthData.Bq 1962
    have hp : val WuPaper.ClassicalFourthData.Bq 1962 = (160253617400518:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 1962 = 160253617400518 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 1962 = (4981:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_1962
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 1963) ≤ val WuPaper.ClassicalFourthData.Bq 1963
    have hp : val WuPaper.ClassicalFourthData.Bq 1963 = (160304867618621:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 1963 = 160304867618621 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 1963 = (9963:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_1963
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 1964) ≤ val WuPaper.ClassicalFourthData.Bq 1964
    have hp : val WuPaper.ClassicalFourthData.Bq 1964 = (160356096259576:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 1964 = 160356096259576 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 1964 = (2491:ℝ)/1000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_1964
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 1965) ≤ val WuPaper.ClassicalFourthData.Bq 1965
    have hp : val WuPaper.ClassicalFourthData.Bq 1965 = (160407303333664:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 1965 = 160407303333664 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 1965 = (1993:ℝ)/800 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_1965
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 1966) ≤ val WuPaper.ClassicalFourthData.Bq 1966
    have hp : val WuPaper.ClassicalFourthData.Bq 1966 = (160458488851161:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 1966 = 160458488851161 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 1966 = (4983:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_1966
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 1967) ≤ val WuPaper.ClassicalFourthData.Bq 1967
    have hp : val WuPaper.ClassicalFourthData.Bq 1967 = (160509652822336:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 1967 = 160509652822336 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 1967 = (9967:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_1967
end WuPaper.ClassicalFourthConditions
#print axioms WuPaper.ClassicalFourthConditions.Log_block_122

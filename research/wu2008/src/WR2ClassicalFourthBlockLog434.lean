import WR2ClassicalFourthConditions
import WR2ClassicalFourthLogPoints434
noncomputable section
namespace WuPaper.ClassicalFourthConditions
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem Log_block_434 (j : Fin 16) (hj : 16*434+j.val < 10541) :
    WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 (16*434+j.val)) ≤ val WuPaper.ClassicalFourthData.Bq (16*434+j.val) := by
  fin_cases j
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 6944) ≤ val WuPaper.ClassicalFourthData.Bq 6944
    have hp : val WuPaper.ClassicalFourthData.Bq 6944 = (269404978522626:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 6944 = 269404978522626 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 6944 = (467:ℝ)/125 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_6944
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 6945) ≤ val WuPaper.ClassicalFourthData.Bq 6945
    have hp : val WuPaper.ClassicalFourthData.Bq 6945 = (269411407120819:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 6945 = 269411407120819 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 6945 = (2989:ℝ)/800 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_6945
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 6946) ≤ val WuPaper.ClassicalFourthData.Bq 6946
    have hp : val WuPaper.ClassicalFourthData.Bq 6946 = (269417832624665:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 6946 = 269417832624665 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 6946 = (7473:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_6946
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 6947) ≤ val WuPaper.ClassicalFourthData.Bq 6947
    have hp : val WuPaper.ClassicalFourthData.Bq 6947 = (269424255035193:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 6947 = 269424255035193 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 6947 = (14947:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_6947
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 6948) ≤ val WuPaper.ClassicalFourthData.Bq 6948
    have hp : val WuPaper.ClassicalFourthData.Bq 6948 = (269430674353430:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 6948 = 269430674353430 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 6948 = (3737:ℝ)/1000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_6948
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 6949) ≤ val WuPaper.ClassicalFourthData.Bq 6949
    have hp : val WuPaper.ClassicalFourthData.Bq 6949 = (269437090580407:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 6949 = 269437090580407 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 6949 = (14949:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_6949
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 6950) ≤ val WuPaper.ClassicalFourthData.Bq 6950
    have hp : val WuPaper.ClassicalFourthData.Bq 6950 = (269443503717150:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 6950 = 269443503717150 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 6950 = (299:ℝ)/80 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_6950
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 6951) ≤ val WuPaper.ClassicalFourthData.Bq 6951
    have hp : val WuPaper.ClassicalFourthData.Bq 6951 = (269449913764687:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 6951 = 269449913764687 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 6951 = (14951:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_6951
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 6952) ≤ val WuPaper.ClassicalFourthData.Bq 6952
    have hp : val WuPaper.ClassicalFourthData.Bq 6952 = (269456320724047:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 6952 = 269456320724047 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 6952 = (1869:ℝ)/500 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_6952
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 6953) ≤ val WuPaper.ClassicalFourthData.Bq 6953
    have hp : val WuPaper.ClassicalFourthData.Bq 6953 = (269462724596255:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 6953 = 269462724596255 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 6953 = (14953:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_6953
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 6954) ≤ val WuPaper.ClassicalFourthData.Bq 6954
    have hp : val WuPaper.ClassicalFourthData.Bq 6954 = (269469125382338:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 6954 = 269469125382338 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 6954 = (7477:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_6954
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 6955) ≤ val WuPaper.ClassicalFourthData.Bq 6955
    have hp : val WuPaper.ClassicalFourthData.Bq 6955 = (269475523083322:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 6955 = 269475523083322 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 6955 = (2991:ℝ)/800 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_6955
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 6956) ≤ val WuPaper.ClassicalFourthData.Bq 6956
    have hp : val WuPaper.ClassicalFourthData.Bq 6956 = (269481917700233:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 6956 = 269481917700233 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 6956 = (3739:ℝ)/1000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_6956
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 6957) ≤ val WuPaper.ClassicalFourthData.Bq 6957
    have hp : val WuPaper.ClassicalFourthData.Bq 6957 = (269488309234097:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 6957 = 269488309234097 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 6957 = (14957:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_6957
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 6958) ≤ val WuPaper.ClassicalFourthData.Bq 6958
    have hp : val WuPaper.ClassicalFourthData.Bq 6958 = (269494697685938:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 6958 = 269494697685938 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 6958 = (7479:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_6958
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 6959) ≤ val WuPaper.ClassicalFourthData.Bq 6959
    have hp : val WuPaper.ClassicalFourthData.Bq 6959 = (269501083056781:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 6959 = 269501083056781 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 6959 = (14959:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_6959
end WuPaper.ClassicalFourthConditions
#print axioms WuPaper.ClassicalFourthConditions.Log_block_434

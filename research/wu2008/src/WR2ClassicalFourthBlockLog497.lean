import WR2ClassicalFourthConditions
import WR2ClassicalFourthLogPoints497
noncomputable section
namespace WuPaper.ClassicalFourthConditions
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem Log_block_497 (j : Fin 16) (hj : 16*497+j.val < 10541) :
    WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 (16*497+j.val)) ≤ val WuPaper.ClassicalFourthData.Bq (16*497+j.val) := by
  fin_cases j
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 7952) ≤ val WuPaper.ClassicalFourthData.Bq 7952
    have hp : val WuPaper.ClassicalFourthData.Bq 7952 = (274474490289087:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 7952 = 274474490289087 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 7952 = (997:ℝ)/250 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_7952
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 7953) ≤ val WuPaper.ClassicalFourthData.Bq 7953
    have hp : val WuPaper.ClassicalFourthData.Bq 7953 = (274478262841664:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 7953 = 274478262841664 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 7953 = (15953:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_7953
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 7954) ≤ val WuPaper.ClassicalFourthData.Bq 7954
    have hp : val WuPaper.ClassicalFourthData.Bq 7954 = (274482033166476:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 7954 = 274482033166476 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 7954 = (7977:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_7954
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 7955) ≤ val WuPaper.ClassicalFourthData.Bq 7955
    have hp : val WuPaper.ClassicalFourthData.Bq 7955 = (274485801264235:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 7955 = 274485801264235 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 7955 = (3191:ℝ)/800 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_7955
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 7956) ≤ val WuPaper.ClassicalFourthData.Bq 7956
    have hp : val WuPaper.ClassicalFourthData.Bq 7956 = (274489567135655:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 7956 = 274489567135655 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 7956 = (3989:ℝ)/1000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_7956
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 7957) ≤ val WuPaper.ClassicalFourthData.Bq 7957
    have hp : val WuPaper.ClassicalFourthData.Bq 7957 = (274493330781446:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 7957 = 274493330781446 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 7957 = (15957:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_7957
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 7958) ≤ val WuPaper.ClassicalFourthData.Bq 7958
    have hp : val WuPaper.ClassicalFourthData.Bq 7958 = (274497092202321:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 7958 = 274497092202321 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 7958 = (7979:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_7958
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 7959) ≤ val WuPaper.ClassicalFourthData.Bq 7959
    have hp : val WuPaper.ClassicalFourthData.Bq 7959 = (274500851398990:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 7959 = 274500851398990 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 7959 = (15959:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_7959
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 7960) ≤ val WuPaper.ClassicalFourthData.Bq 7960
    have hp : val WuPaper.ClassicalFourthData.Bq 7960 = (274504608372166:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 7960 = 274504608372166 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 7960 = (399:ℝ)/100 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_7960
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 7961) ≤ val WuPaper.ClassicalFourthData.Bq 7961
    have hp : val WuPaper.ClassicalFourthData.Bq 7961 = (274508363122558:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 7961 = 274508363122558 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 7961 = (15961:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_7961
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 7962) ≤ val WuPaper.ClassicalFourthData.Bq 7962
    have hp : val WuPaper.ClassicalFourthData.Bq 7962 = (274512115650878:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 7962 = 274512115650878 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 7962 = (7981:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_7962
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 7963) ≤ val WuPaper.ClassicalFourthData.Bq 7963
    have hp : val WuPaper.ClassicalFourthData.Bq 7963 = (274515865957837:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 7963 = 274515865957837 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 7963 = (15963:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_7963
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 7964) ≤ val WuPaper.ClassicalFourthData.Bq 7964
    have hp : val WuPaper.ClassicalFourthData.Bq 7964 = (274519614044143:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 7964 = 274519614044143 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 7964 = (3991:ℝ)/1000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_7964
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 7965) ≤ val WuPaper.ClassicalFourthData.Bq 7965
    have hp : val WuPaper.ClassicalFourthData.Bq 7965 = (274523359910508:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 7965 = 274523359910508 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 7965 = (3193:ℝ)/800 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_7965
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 7966) ≤ val WuPaper.ClassicalFourthData.Bq 7966
    have hp : val WuPaper.ClassicalFourthData.Bq 7966 = (274527103557641:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 7966 = 274527103557641 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 7966 = (7983:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_7966
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 7967) ≤ val WuPaper.ClassicalFourthData.Bq 7967
    have hp : val WuPaper.ClassicalFourthData.Bq 7967 = (274530844986251:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 7967 = 274530844986251 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 7967 = (15967:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_7967
end WuPaper.ClassicalFourthConditions
#print axioms WuPaper.ClassicalFourthConditions.Log_block_497

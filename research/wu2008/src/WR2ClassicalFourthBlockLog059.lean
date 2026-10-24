import WR2ClassicalFourthConditions
import WR2ClassicalFourthLogPoints059
noncomputable section
namespace WuPaper.ClassicalFourthConditions
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem Log_block_059 (j : Fin 16) (hj : 16*59+j.val < 10541) :
    WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 (16*59+j.val)) ≤ val WuPaper.ClassicalFourthData.Bq (16*59+j.val) := by
  fin_cases j
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 944) ≤ val WuPaper.ClassicalFourthData.Bq 944
    have hp : val WuPaper.ClassicalFourthData.Bq 944 = (94758657887075:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 944 = 94758657887075 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 944 = (559:ℝ)/250 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_944
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 945) ≤ val WuPaper.ClassicalFourthData.Bq 945
    have hp : val WuPaper.ClassicalFourthData.Bq 945 = (94838503724890:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 945 = 94838503724890 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 945 = (1789:ℝ)/800 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_945
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 946) ≤ val WuPaper.ClassicalFourthData.Bq 946
    have hp : val WuPaper.ClassicalFourthData.Bq 946 = (94918313426933:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 946 = 94918313426933 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 946 = (4473:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_946
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 947) ≤ val WuPaper.ClassicalFourthData.Bq 947
    have hp : val WuPaper.ClassicalFourthData.Bq 947 = (94998087012711:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 947 = 94998087012711 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 947 = (8947:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_947
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 948) ≤ val WuPaper.ClassicalFourthData.Bq 948
    have hp : val WuPaper.ClassicalFourthData.Bq 948 = (95077824501722:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 948 = 95077824501722 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 948 = (2237:ℝ)/1000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_948
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 949) ≤ val WuPaper.ClassicalFourthData.Bq 949
    have hp : val WuPaper.ClassicalFourthData.Bq 949 = (95157525913447:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 949 = 95157525913447 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 949 = (8949:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_949
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 950) ≤ val WuPaper.ClassicalFourthData.Bq 950
    have hp : val WuPaper.ClassicalFourthData.Bq 950 = (95237191267356:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 950 = 95237191267356 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 950 = (179:ℝ)/80 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_950
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 951) ≤ val WuPaper.ClassicalFourthData.Bq 951
    have hp : val WuPaper.ClassicalFourthData.Bq 951 = (95316820582905:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 951 = 95316820582905 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 951 = (8951:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_951
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 952) ≤ val WuPaper.ClassicalFourthData.Bq 952
    have hp : val WuPaper.ClassicalFourthData.Bq 952 = (95396413879538:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 952 = 95396413879538 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 952 = (1119:ℝ)/500 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_952
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 953) ≤ val WuPaper.ClassicalFourthData.Bq 953
    have hp : val WuPaper.ClassicalFourthData.Bq 953 = (95475971176683:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 953 = 95475971176683 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 953 = (8953:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_953
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 954) ≤ val WuPaper.ClassicalFourthData.Bq 954
    have hp : val WuPaper.ClassicalFourthData.Bq 954 = (95555492493758:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 954 = 95555492493758 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 954 = (4477:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_954
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 955) ≤ val WuPaper.ClassicalFourthData.Bq 955
    have hp : val WuPaper.ClassicalFourthData.Bq 955 = (95634977850167:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 955 = 95634977850167 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 955 = (1791:ℝ)/800 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_955
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 956) ≤ val WuPaper.ClassicalFourthData.Bq 956
    have hp : val WuPaper.ClassicalFourthData.Bq 956 = (95714427265300:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 956 = 95714427265300 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 956 = (2239:ℝ)/1000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_956
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 957) ≤ val WuPaper.ClassicalFourthData.Bq 957
    have hp : val WuPaper.ClassicalFourthData.Bq 957 = (95793840758534:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 957 = 95793840758534 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 957 = (8957:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_957
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 958) ≤ val WuPaper.ClassicalFourthData.Bq 958
    have hp : val WuPaper.ClassicalFourthData.Bq 958 = (95873218349234:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 958 = 95873218349234 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 958 = (4479:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_958
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 959) ≤ val WuPaper.ClassicalFourthData.Bq 959
    have hp : val WuPaper.ClassicalFourthData.Bq 959 = (95952560056751:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 959 = 95952560056751 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 959 = (8959:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_959
end WuPaper.ClassicalFourthConditions
#print axioms WuPaper.ClassicalFourthConditions.Log_block_059

import WR2ClassicalFourthConditions
import WR2ClassicalFourthLogPoints246
noncomputable section
namespace WuPaper.ClassicalFourthConditions
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem Log_block_246 (j : Fin 16) (hj : 16*246+j.val < 10541) :
    WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 (16*246+j.val)) ≤ val WuPaper.ClassicalFourthData.Bq (16*246+j.val) := by
  fin_cases j
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 3936) ≤ val WuPaper.ClassicalFourthData.Bq 3936
    have hp : val WuPaper.ClassicalFourthData.Bq 3936 = (229596182594733:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 3936 = 229596182594733 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 3936 = (373:ℝ)/125 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_3936
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 3937) ≤ val WuPaper.ClassicalFourthData.Bq 3937
    have hp : val WuPaper.ClassicalFourthData.Bq 3937 = (229619170307062:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 3937 = 229619170307062 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 3937 = (11937:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_3937
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 3938) ≤ val WuPaper.ClassicalFourthData.Bq 3938
    have hp : val WuPaper.ClassicalFourthData.Bq 3938 = (229642148849383:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 3938 = 229642148849383 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 3938 = (5969:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_3938
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 3939) ≤ val WuPaper.ClassicalFourthData.Bq 3939
    have hp : val WuPaper.ClassicalFourthData.Bq 3939 = (229665118225341:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 3939 = 229665118225341 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 3939 = (11939:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_3939
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 3940) ≤ val WuPaper.ClassicalFourthData.Bq 3940
    have hp : val WuPaper.ClassicalFourthData.Bq 3940 = (229688078438578:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 3940 = 229688078438578 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 3940 = (597:ℝ)/200 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_3940
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 3941) ≤ val WuPaper.ClassicalFourthData.Bq 3941
    have hp : val WuPaper.ClassicalFourthData.Bq 3941 = (229711029492734:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 3941 = 229711029492734 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 3941 = (11941:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_3941
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 3942) ≤ val WuPaper.ClassicalFourthData.Bq 3942
    have hp : val WuPaper.ClassicalFourthData.Bq 3942 = (229733971391449:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 3942 = 229733971391449 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 3942 = (5971:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_3942
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 3943) ≤ val WuPaper.ClassicalFourthData.Bq 3943
    have hp : val WuPaper.ClassicalFourthData.Bq 3943 = (229756904138359:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 3943 = 229756904138359 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 3943 = (11943:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_3943
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 3944) ≤ val WuPaper.ClassicalFourthData.Bq 3944
    have hp : val WuPaper.ClassicalFourthData.Bq 3944 = (229779827737101:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 3944 = 229779827737101 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 3944 = (1493:ℝ)/500 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_3944
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 3945) ≤ val WuPaper.ClassicalFourthData.Bq 3945
    have hp : val WuPaper.ClassicalFourthData.Bq 3945 = (229802742191307:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 3945 = 229802742191307 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 3945 = (2389:ℝ)/800 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_3945
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 3946) ≤ val WuPaper.ClassicalFourthData.Bq 3946
    have hp : val WuPaper.ClassicalFourthData.Bq 3946 = (229825647504610:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 3946 = 229825647504610 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 3946 = (5973:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_3946
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 3947) ≤ val WuPaper.ClassicalFourthData.Bq 3947
    have hp : val WuPaper.ClassicalFourthData.Bq 3947 = (229848543680641:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 3947 = 229848543680641 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 3947 = (11947:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_3947
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 3948) ≤ val WuPaper.ClassicalFourthData.Bq 3948
    have hp : val WuPaper.ClassicalFourthData.Bq 3948 = (229871430723027:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 3948 = 229871430723027 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 3948 = (2987:ℝ)/1000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_3948
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 3949) ≤ val WuPaper.ClassicalFourthData.Bq 3949
    have hp : val WuPaper.ClassicalFourthData.Bq 3949 = (229894308635396:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 3949 = 229894308635396 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 3949 = (11949:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_3949
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 3950) ≤ val WuPaper.ClassicalFourthData.Bq 3950
    have hp : val WuPaper.ClassicalFourthData.Bq 3950 = (229917177421373:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 3950 = 229917177421373 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 3950 = (239:ℝ)/80 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_3950
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 3951) ≤ val WuPaper.ClassicalFourthData.Bq 3951
    have hp : val WuPaper.ClassicalFourthData.Bq 3951 = (229940037084581:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 3951 = 229940037084581 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 3951 = (11951:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_3951
end WuPaper.ClassicalFourthConditions
#print axioms WuPaper.ClassicalFourthConditions.Log_block_246

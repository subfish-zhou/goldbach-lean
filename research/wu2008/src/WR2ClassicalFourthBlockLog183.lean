import WR2ClassicalFourthConditions
import WR2ClassicalFourthLogPoints183
noncomputable section
namespace WuPaper.ClassicalFourthConditions
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem Log_block_183 (j : Fin 16) (hj : 16*183+j.val < 10541) :
    WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 (16*183+j.val)) ≤ val WuPaper.ClassicalFourthData.Bq (16*183+j.val) := by
  fin_cases j
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 2928) ≤ val WuPaper.ClassicalFourthData.Bq 2928
    have hp : val WuPaper.ClassicalFourthData.Bq 2928 = (201053005175785:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 2928 = 201053005175785 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 2928 = (683:ℝ)/250 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_2928
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 2929) ≤ val WuPaper.ClassicalFourthData.Bq 2929
    have hp : val WuPaper.ClassicalFourthData.Bq 2929 = (201087433992261:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 2929 = 201087433992261 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 2929 = (10929:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_2929
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 2930) ≤ val WuPaper.ClassicalFourthData.Bq 2930
    have hp : val WuPaper.ClassicalFourthData.Bq 2930 = (201121848886339:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 2930 = 201121848886339 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 2930 = (1093:ℝ)/400 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_2930
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 2931) ≤ val WuPaper.ClassicalFourthData.Bq 2931
    have hp : val WuPaper.ClassicalFourthData.Bq 2931 = (201156249864041:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 2931 = 201156249864041 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 2931 = (10931:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_2931
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 2932) ≤ val WuPaper.ClassicalFourthData.Bq 2932
    have hp : val WuPaper.ClassicalFourthData.Bq 2932 = (201190636931383:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 2932 = 201190636931383 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 2932 = (2733:ℝ)/1000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_2932
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 2933) ≤ val WuPaper.ClassicalFourthData.Bq 2933
    have hp : val WuPaper.ClassicalFourthData.Bq 2933 = (201225010094380:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 2933 = 201225010094380 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 2933 = (10933:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_2933
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 2934) ≤ val WuPaper.ClassicalFourthData.Bq 2934
    have hp : val WuPaper.ClassicalFourthData.Bq 2934 = (201259369359042:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 2934 = 201259369359042 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 2934 = (5467:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_2934
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 2935) ≤ val WuPaper.ClassicalFourthData.Bq 2935
    have hp : val WuPaper.ClassicalFourthData.Bq 2935 = (201293714731378:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 2935 = 201293714731378 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 2935 = (2187:ℝ)/800 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_2935
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 2936) ≤ val WuPaper.ClassicalFourthData.Bq 2936
    have hp : val WuPaper.ClassicalFourthData.Bq 2936 = (201328046217393:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 2936 = 201328046217393 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 2936 = (1367:ℝ)/500 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_2936
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 2937) ≤ val WuPaper.ClassicalFourthData.Bq 2937
    have hp : val WuPaper.ClassicalFourthData.Bq 2937 = (201362363823087:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 2937 = 201362363823087 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 2937 = (10937:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_2937
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 2938) ≤ val WuPaper.ClassicalFourthData.Bq 2938
    have hp : val WuPaper.ClassicalFourthData.Bq 2938 = (201396667554459:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 2938 = 201396667554459 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 2938 = (5469:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_2938
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 2939) ≤ val WuPaper.ClassicalFourthData.Bq 2939
    have hp : val WuPaper.ClassicalFourthData.Bq 2939 = (201430957417505:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 2939 = 201430957417505 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 2939 = (10939:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_2939
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 2940) ≤ val WuPaper.ClassicalFourthData.Bq 2940
    have hp : val WuPaper.ClassicalFourthData.Bq 2940 = (201465233418217:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 2940 = 201465233418217 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 2940 = (547:ℝ)/200 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_2940
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 2941) ≤ val WuPaper.ClassicalFourthData.Bq 2941
    have hp : val WuPaper.ClassicalFourthData.Bq 2941 = (201499495562584:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 2941 = 201499495562584 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 2941 = (10941:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_2941
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 2942) ≤ val WuPaper.ClassicalFourthData.Bq 2942
    have hp : val WuPaper.ClassicalFourthData.Bq 2942 = (201533743856591:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 2942 = 201533743856591 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 2942 = (5471:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_2942
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 2943) ≤ val WuPaper.ClassicalFourthData.Bq 2943
    have hp : val WuPaper.ClassicalFourthData.Bq 2943 = (201567978306222:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 2943 = 201567978306222 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 2943 = (10943:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_2943
end WuPaper.ClassicalFourthConditions
#print axioms WuPaper.ClassicalFourthConditions.Log_block_183

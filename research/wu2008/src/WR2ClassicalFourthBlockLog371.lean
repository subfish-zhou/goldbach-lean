import WR2ClassicalFourthConditions
import WR2ClassicalFourthLogPoints371
noncomputable section
namespace WuPaper.ClassicalFourthConditions
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem Log_block_371 (j : Fin 16) (hj : 16*371+j.val < 10541) :
    WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 (16*371+j.val)) ≤ val WuPaper.ClassicalFourthData.Bq (16*371+j.val) := by
  fin_cases j
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 5936) ≤ val WuPaper.ClassicalFourthData.Bq 5936
    have hp : val WuPaper.ClassicalFourthData.Bq 5936 = (261156763510691:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 5936 = 261156763510691 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 5936 = (871:ℝ)/250 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_5936
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 5937) ≤ val WuPaper.ClassicalFourthData.Bq 5937
    have hp : val WuPaper.ClassicalFourthData.Bq 5937 = (261166909128034:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 5937 = 261166909128034 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 5937 = (13937:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_5937
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 5938) ≤ val WuPaper.ClassicalFourthData.Bq 5938
    have hp : val WuPaper.ClassicalFourthData.Bq 5938 = (261177050383198:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 5938 = 261177050383198 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 5938 = (6969:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_5938
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 5939) ≤ val WuPaper.ClassicalFourthData.Bq 5939
    have hp : val WuPaper.ClassicalFourthData.Bq 5939 = (261187187277708:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 5939 = 261187187277708 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 5939 = (13939:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_5939
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 5940) ≤ val WuPaper.ClassicalFourthData.Bq 5940
    have hp : val WuPaper.ClassicalFourthData.Bq 5940 = (261197319813087:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 5940 = 261197319813087 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 5940 = (697:ℝ)/200 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_5940
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 5941) ≤ val WuPaper.ClassicalFourthData.Bq 5941
    have hp : val WuPaper.ClassicalFourthData.Bq 5941 = (261207447990857:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 5941 = 261207447990857 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 5941 = (13941:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_5941
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 5942) ≤ val WuPaper.ClassicalFourthData.Bq 5942
    have hp : val WuPaper.ClassicalFourthData.Bq 5942 = (261217571812539:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 5942 = 261217571812539 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 5942 = (6971:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_5942
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 5943) ≤ val WuPaper.ClassicalFourthData.Bq 5943
    have hp : val WuPaper.ClassicalFourthData.Bq 5943 = (261227691279656:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 5943 = 261227691279656 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 5943 = (13943:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_5943
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 5944) ≤ val WuPaper.ClassicalFourthData.Bq 5944
    have hp : val WuPaper.ClassicalFourthData.Bq 5944 = (261237806393728:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 5944 = 261237806393728 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 5944 = (1743:ℝ)/500 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_5944
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 5945) ≤ val WuPaper.ClassicalFourthData.Bq 5945
    have hp : val WuPaper.ClassicalFourthData.Bq 5945 = (261247917156274:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 5945 = 261247917156274 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 5945 = (2789:ℝ)/800 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_5945
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 5946) ≤ val WuPaper.ClassicalFourthData.Bq 5946
    have hp : val WuPaper.ClassicalFourthData.Bq 5946 = (261258023568814:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 5946 = 261258023568814 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 5946 = (6973:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_5946
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 5947) ≤ val WuPaper.ClassicalFourthData.Bq 5947
    have hp : val WuPaper.ClassicalFourthData.Bq 5947 = (261268125632868:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 5947 = 261268125632868 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 5947 = (13947:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_5947
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 5948) ≤ val WuPaper.ClassicalFourthData.Bq 5948
    have hp : val WuPaper.ClassicalFourthData.Bq 5948 = (261278223349952:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 5948 = 261278223349952 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 5948 = (3487:ℝ)/1000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_5948
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 5949) ≤ val WuPaper.ClassicalFourthData.Bq 5949
    have hp : val WuPaper.ClassicalFourthData.Bq 5949 = (261288316721585:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 5949 = 261288316721585 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 5949 = (13949:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_5949
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 5950) ≤ val WuPaper.ClassicalFourthData.Bq 5950
    have hp : val WuPaper.ClassicalFourthData.Bq 5950 = (261298405749284:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 5950 = 261298405749284 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 5950 = (279:ℝ)/80 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_5950
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 5951) ≤ val WuPaper.ClassicalFourthData.Bq 5951
    have hp : val WuPaper.ClassicalFourthData.Bq 5951 = (261308490434564:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 5951 = 261308490434564 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 5951 = (13951:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_5951
end WuPaper.ClassicalFourthConditions
#print axioms WuPaper.ClassicalFourthConditions.Log_block_371

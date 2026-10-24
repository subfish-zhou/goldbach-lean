import WR2ClassicalFourthConditions
import WR2ClassicalFourthLogPoints621
noncomputable section
namespace WuPaper.ClassicalFourthConditions
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem Log_block_621 (j : Fin 16) (hj : 16*621+j.val < 10541) :
    WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 (16*621+j.val)) ≤ val WuPaper.ClassicalFourthData.Bq (16*621+j.val) := by
  fin_cases j
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 9936) ≤ val WuPaper.ClassicalFourthData.Bq 9936
    have hp : val WuPaper.ClassicalFourthData.Bq 9936 = (278363304878767:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 9936 = 278363304878767 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 9936 = (1121:ℝ)/250 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_9936
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 9937) ≤ val WuPaper.ClassicalFourthData.Bq 9937
    have hp : val WuPaper.ClassicalFourthData.Bq 9937 = (278363787278531:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 9937 = 278363787278531 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 9937 = (17937:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_9937
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 9938) ≤ val WuPaper.ClassicalFourthData.Bq 9938
    have hp : val WuPaper.ClassicalFourthData.Bq 9938 = (278364268476495:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 9938 = 278364268476495 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 9938 = (8969:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_9938
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 9939) ≤ val WuPaper.ClassicalFourthData.Bq 9939
    have hp : val WuPaper.ClassicalFourthData.Bq 9939 = (278364748473026:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 9939 = 278364748473026 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 9939 = (17939:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_9939
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 9940) ≤ val WuPaper.ClassicalFourthData.Bq 9940
    have hp : val WuPaper.ClassicalFourthData.Bq 9940 = (278365227268488:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 9940 = 278365227268488 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 9940 = (897:ℝ)/200 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_9940
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 9941) ≤ val WuPaper.ClassicalFourthData.Bq 9941
    have hp : val WuPaper.ClassicalFourthData.Bq 9941 = (278365704863246:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 9941 = 278365704863246 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 9941 = (17941:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_9941
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 9942) ≤ val WuPaper.ClassicalFourthData.Bq 9942
    have hp : val WuPaper.ClassicalFourthData.Bq 9942 = (278366181257668:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 9942 = 278366181257668 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 9942 = (8971:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_9942
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 9943) ≤ val WuPaper.ClassicalFourthData.Bq 9943
    have hp : val WuPaper.ClassicalFourthData.Bq 9943 = (278366656452117:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 9943 = 278366656452117 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 9943 = (17943:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_9943
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 9944) ≤ val WuPaper.ClassicalFourthData.Bq 9944
    have hp : val WuPaper.ClassicalFourthData.Bq 9944 = (278367130446958:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 9944 = 278367130446958 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 9944 = (2243:ℝ)/500 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_9944
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 9945) ≤ val WuPaper.ClassicalFourthData.Bq 9945
    have hp : val WuPaper.ClassicalFourthData.Bq 9945 = (278367603242558:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 9945 = 278367603242558 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 9945 = (3589:ℝ)/800 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_9945
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 9946) ≤ val WuPaper.ClassicalFourthData.Bq 9946
    have hp : val WuPaper.ClassicalFourthData.Bq 9946 = (278368074839280:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 9946 = 278368074839280 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 9946 = (8973:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_9946
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 9947) ≤ val WuPaper.ClassicalFourthData.Bq 9947
    have hp : val WuPaper.ClassicalFourthData.Bq 9947 = (278368545237489:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 9947 = 278368545237489 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 9947 = (17947:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_9947
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 9948) ≤ val WuPaper.ClassicalFourthData.Bq 9948
    have hp : val WuPaper.ClassicalFourthData.Bq 9948 = (278369014437551:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 9948 = 278369014437551 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 9948 = (4487:ℝ)/1000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_9948
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 9949) ≤ val WuPaper.ClassicalFourthData.Bq 9949
    have hp : val WuPaper.ClassicalFourthData.Bq 9949 = (278369482439829:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 9949 = 278369482439829 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 9949 = (17949:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_9949
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 9950) ≤ val WuPaper.ClassicalFourthData.Bq 9950
    have hp : val WuPaper.ClassicalFourthData.Bq 9950 = (278369949244688:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 9950 = 278369949244688 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 9950 = (359:ℝ)/80 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_9950
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 9951) ≤ val WuPaper.ClassicalFourthData.Bq 9951
    have hp : val WuPaper.ClassicalFourthData.Bq 9951 = (278370414852492:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 9951 = 278370414852492 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 9951 = (17951:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_9951
end WuPaper.ClassicalFourthConditions
#print axioms WuPaper.ClassicalFourthConditions.Log_block_621

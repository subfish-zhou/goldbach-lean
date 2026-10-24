import WR2ClassicalFourthConditions
import WR2ClassicalFourthLogPoints496
noncomputable section
namespace WuPaper.ClassicalFourthConditions
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem Log_block_496 (j : Fin 16) (hj : 16*496+j.val < 10541) :
    WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 (16*496+j.val)) ≤ val WuPaper.ClassicalFourthData.Bq (16*496+j.val) := by
  fin_cases j
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 7936) ≤ val WuPaper.ClassicalFourthData.Bq 7936
    have hp : val WuPaper.ClassicalFourthData.Bq 7936 = (274413825889494:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 7936 = 274413825889494 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 7936 = (498:ℝ)/125 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_7936
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 7937) ≤ val WuPaper.ClassicalFourthData.Bq 7937
    have hp : val WuPaper.ClassicalFourthData.Bq 7937 = (274417634183408:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 7937 = 274417634183408 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 7937 = (15937:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_7937
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 7938) ≤ val WuPaper.ClassicalFourthData.Bq 7938
    have hp : val WuPaper.ClassicalFourthData.Bq 7938 = (274421440238124:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 7938 = 274421440238124 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 7938 = (7969:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_7938
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 7939) ≤ val WuPaper.ClassicalFourthData.Bq 7939
    have hp : val WuPaper.ClassicalFourthData.Bq 7939 = (274425244054358:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 7939 = 274425244054358 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 7939 = (15939:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_7939
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 7940) ≤ val WuPaper.ClassicalFourthData.Bq 7940
    have hp : val WuPaper.ClassicalFourthData.Bq 7940 = (274429045632827:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 7940 = 274429045632827 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 7940 = (797:ℝ)/200 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_7940
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 7941) ≤ val WuPaper.ClassicalFourthData.Bq 7941
    have hp : val WuPaper.ClassicalFourthData.Bq 7941 = (274432844974245:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 7941 = 274432844974245 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 7941 = (15941:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_7941
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 7942) ≤ val WuPaper.ClassicalFourthData.Bq 7942
    have hp : val WuPaper.ClassicalFourthData.Bq 7942 = (274436642079330:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 7942 = 274436642079330 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 7942 = (7971:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_7942
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 7943) ≤ val WuPaper.ClassicalFourthData.Bq 7943
    have hp : val WuPaper.ClassicalFourthData.Bq 7943 = (274440436948796:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 7943 = 274440436948796 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 7943 = (15943:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_7943
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 7944) ≤ val WuPaper.ClassicalFourthData.Bq 7944
    have hp : val WuPaper.ClassicalFourthData.Bq 7944 = (274444229583358:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 7944 = 274444229583358 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 7944 = (1993:ℝ)/500 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_7944
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 7945) ≤ val WuPaper.ClassicalFourthData.Bq 7945
    have hp : val WuPaper.ClassicalFourthData.Bq 7945 = (274448019983733:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 7945 = 274448019983733 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 7945 = (3189:ℝ)/800 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_7945
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 7946) ≤ val WuPaper.ClassicalFourthData.Bq 7946
    have hp : val WuPaper.ClassicalFourthData.Bq 7946 = (274451808150634:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 7946 = 274451808150634 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 7946 = (7973:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_7946
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 7947) ≤ val WuPaper.ClassicalFourthData.Bq 7947
    have hp : val WuPaper.ClassicalFourthData.Bq 7947 = (274455594084775:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 7947 = 274455594084775 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 7947 = (15947:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_7947
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 7948) ≤ val WuPaper.ClassicalFourthData.Bq 7948
    have hp : val WuPaper.ClassicalFourthData.Bq 7948 = (274459377786872:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 7948 = 274459377786872 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 7948 = (3987:ℝ)/1000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_7948
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 7949) ≤ val WuPaper.ClassicalFourthData.Bq 7949
    have hp : val WuPaper.ClassicalFourthData.Bq 7949 = (274463159257638:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 7949 = 274463159257638 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 7949 = (15949:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_7949
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 7950) ≤ val WuPaper.ClassicalFourthData.Bq 7950
    have hp : val WuPaper.ClassicalFourthData.Bq 7950 = (274466938497787:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 7950 = 274466938497787 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 7950 = (319:ℝ)/80 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_7950
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 7951) ≤ val WuPaper.ClassicalFourthData.Bq 7951
    have hp : val WuPaper.ClassicalFourthData.Bq 7951 = (274470715508032:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 7951 = 274470715508032 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 7951 = (15951:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_7951
end WuPaper.ClassicalFourthConditions
#print axioms WuPaper.ClassicalFourthConditions.Log_block_496

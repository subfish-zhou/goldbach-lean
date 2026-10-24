import WR2ClassicalFourthConditions
import WR2ClassicalFourthLogPoints058
noncomputable section
namespace WuPaper.ClassicalFourthConditions
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem Log_block_058 (j : Fin 16) (hj : 16*58+j.val < 10541) :
    WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 (16*58+j.val)) ≤ val WuPaper.ClassicalFourthData.Bq (16*58+j.val) := by
  fin_cases j
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 928) ≤ val WuPaper.ClassicalFourthData.Bq 928
    have hp : val WuPaper.ClassicalFourthData.Bq 928 = (93476194046294:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 928 = 93476194046294 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 928 = (279:ℝ)/125 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_928
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 929) ≤ val WuPaper.ClassicalFourthData.Bq 929
    have hp : val WuPaper.ClassicalFourthData.Bq 929 = (93556620720507:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 929 = 93556620720507 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 929 = (8929:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_929
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 930) ≤ val WuPaper.ClassicalFourthData.Bq 930
    have hp : val WuPaper.ClassicalFourthData.Bq 930 = (93637010944999:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 930 = 93637010944999 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 930 = (893:ℝ)/400 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_930
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 931) ≤ val WuPaper.ClassicalFourthData.Bq 931
    have hp : val WuPaper.ClassicalFourthData.Bq 931 = (93717364739491:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 931 = 93717364739491 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 931 = (8931:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_931
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 932) ≤ val WuPaper.ClassicalFourthData.Bq 932
    have hp : val WuPaper.ClassicalFourthData.Bq 932 = (93797682123694:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 932 = 93797682123694 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 932 = (2233:ℝ)/1000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_932
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 933) ≤ val WuPaper.ClassicalFourthData.Bq 933
    have hp : val WuPaper.ClassicalFourthData.Bq 933 = (93877963117301:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 933 = 93877963117301 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 933 = (8933:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_933
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 934) ≤ val WuPaper.ClassicalFourthData.Bq 934
    have hp : val WuPaper.ClassicalFourthData.Bq 934 = (93958207739993:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 934 = 93958207739993 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 934 = (4467:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_934
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 935) ≤ val WuPaper.ClassicalFourthData.Bq 935
    have hp : val WuPaper.ClassicalFourthData.Bq 935 = (94038416011441:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 935 = 94038416011441 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 935 = (1787:ℝ)/800 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_935
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 936) ≤ val WuPaper.ClassicalFourthData.Bq 936
    have hp : val WuPaper.ClassicalFourthData.Bq 936 = (94118587951297:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 936 = 94118587951297 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 936 = (1117:ℝ)/500 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_936
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 937) ≤ val WuPaper.ClassicalFourthData.Bq 937
    have hp : val WuPaper.ClassicalFourthData.Bq 937 = (94198723579204:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 937 = 94198723579204 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 937 = (8937:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_937
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 938) ≤ val WuPaper.ClassicalFourthData.Bq 938
    have hp : val WuPaper.ClassicalFourthData.Bq 938 = (94278822914790:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 938 = 94278822914790 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 938 = (4469:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_938
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 939) ≤ val WuPaper.ClassicalFourthData.Bq 939
    have hp : val WuPaper.ClassicalFourthData.Bq 939 = (94358885977670:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 939 = 94358885977670 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 939 = (8939:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_939
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 940) ≤ val WuPaper.ClassicalFourthData.Bq 940
    have hp : val WuPaper.ClassicalFourthData.Bq 940 = (94438912787446:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 940 = 94438912787446 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 940 = (447:ℝ)/200 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_940
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 941) ≤ val WuPaper.ClassicalFourthData.Bq 941
    have hp : val WuPaper.ClassicalFourthData.Bq 941 = (94518903363706:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 941 = 94518903363706 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 941 = (8941:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_941
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 942) ≤ val WuPaper.ClassicalFourthData.Bq 942
    have hp : val WuPaper.ClassicalFourthData.Bq 942 = (94598857726025:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 942 = 94598857726025 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 942 = (4471:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_942
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 943) ≤ val WuPaper.ClassicalFourthData.Bq 943
    have hp : val WuPaper.ClassicalFourthData.Bq 943 = (94678775893965:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 943 = 94678775893965 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 943 = (8943:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_943
end WuPaper.ClassicalFourthConditions
#print axioms WuPaper.ClassicalFourthConditions.Log_block_058

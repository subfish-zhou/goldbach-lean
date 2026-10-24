import WR2ClassicalFourthConditions
import WR2ClassicalFourthLogPoints495
noncomputable section
namespace WuPaper.ClassicalFourthConditions
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem Log_block_495 (j : Fin 16) (hj : 16*495+j.val < 10541) :
    WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 (16*495+j.val)) ≤ val WuPaper.ClassicalFourthData.Bq (16*495+j.val) := by
  fin_cases j
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 7920) ≤ val WuPaper.ClassicalFourthData.Bq 7920
    have hp : val WuPaper.ClassicalFourthData.Bq 7920 = (274352588070218:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 7920 = 274352588070218 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 7920 = (199:ℝ)/50 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_7920
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 7921) ≤ val WuPaper.ClassicalFourthData.Bq 7921
    have hp : val WuPaper.ClassicalFourthData.Bq 7921 = (274356432288960:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 7921 = 274356432288960 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 7921 = (15921:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_7921
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 7922) ≤ val WuPaper.ClassicalFourthData.Bq 7922
    have hp : val WuPaper.ClassicalFourthData.Bq 7922 = (274360274257005:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 7922 = 274360274257005 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 7922 = (7961:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_7922
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 7923) ≤ val WuPaper.ClassicalFourthData.Bq 7923
    have hp : val WuPaper.ClassicalFourthData.Bq 7923 = (274364113975073:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 7923 = 274364113975073 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 7923 = (15923:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_7923
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 7924) ≤ val WuPaper.ClassicalFourthData.Bq 7924
    have hp : val WuPaper.ClassicalFourthData.Bq 7924 = (274367951443885:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 7924 = 274367951443885 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 7924 = (3981:ℝ)/1000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_7924
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 7925) ≤ val WuPaper.ClassicalFourthData.Bq 7925
    have hp : val WuPaper.ClassicalFourthData.Bq 7925 = (274371786664161:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 7925 = 274371786664161 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 7925 = (637:ℝ)/160 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_7925
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 7926) ≤ val WuPaper.ClassicalFourthData.Bq 7926
    have hp : val WuPaper.ClassicalFourthData.Bq 7926 = (274375619636621:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 7926 = 274375619636621 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 7926 = (7963:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_7926
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 7927) ≤ val WuPaper.ClassicalFourthData.Bq 7927
    have hp : val WuPaper.ClassicalFourthData.Bq 7927 = (274379450361984:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 7927 = 274379450361984 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 7927 = (15927:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_7927
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 7928) ≤ val WuPaper.ClassicalFourthData.Bq 7928
    have hp : val WuPaper.ClassicalFourthData.Bq 7928 = (274383278840969:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 7928 = 274383278840969 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 7928 = (1991:ℝ)/500 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_7928
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 7929) ≤ val WuPaper.ClassicalFourthData.Bq 7929
    have hp : val WuPaper.ClassicalFourthData.Bq 7929 = (274387105074296:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 7929 = 274387105074296 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 7929 = (15929:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_7929
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 7930) ≤ val WuPaper.ClassicalFourthData.Bq 7930
    have hp : val WuPaper.ClassicalFourthData.Bq 7930 = (274390929062683:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 7930 = 274390929062683 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 7930 = (1593:ℝ)/400 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_7930
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 7931) ≤ val WuPaper.ClassicalFourthData.Bq 7931
    have hp : val WuPaper.ClassicalFourthData.Bq 7931 = (274394750806849:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 7931 = 274394750806849 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 7931 = (15931:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_7931
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 7932) ≤ val WuPaper.ClassicalFourthData.Bq 7932
    have hp : val WuPaper.ClassicalFourthData.Bq 7932 = (274398570307512:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 7932 = 274398570307512 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 7932 = (3983:ℝ)/1000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_7932
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 7933) ≤ val WuPaper.ClassicalFourthData.Bq 7933
    have hp : val WuPaper.ClassicalFourthData.Bq 7933 = (274402387565391:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 7933 = 274402387565391 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 7933 = (15933:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_7933
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 7934) ≤ val WuPaper.ClassicalFourthData.Bq 7934
    have hp : val WuPaper.ClassicalFourthData.Bq 7934 = (274406202581202:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 7934 = 274406202581202 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 7934 = (7967:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_7934
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 7935) ≤ val WuPaper.ClassicalFourthData.Bq 7935
    have hp : val WuPaper.ClassicalFourthData.Bq 7935 = (274410015355664:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 7935 = 274410015355664 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 7935 = (3187:ℝ)/800 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_7935
end WuPaper.ClassicalFourthConditions
#print axioms WuPaper.ClassicalFourthConditions.Log_block_495

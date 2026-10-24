import WR2ClassicalFourthConditions
import WR2ClassicalFourthLogPoints558
noncomputable section
namespace WuPaper.ClassicalFourthConditions
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem Log_block_558 (j : Fin 16) (hj : 16*558+j.val < 10541) :
    WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 (16*558+j.val)) ≤ val WuPaper.ClassicalFourthData.Bq (16*558+j.val) := by
  fin_cases j
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 8928) ≤ val WuPaper.ClassicalFourthData.Bq 8928
    have hp : val WuPaper.ClassicalFourthData.Bq 8928 = (277197812068646:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 8928 = 277197812068646 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 8928 = (529:ℝ)/125 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_8928
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 8929) ≤ val WuPaper.ClassicalFourthData.Bq 8929
    have hp : val WuPaper.ClassicalFourthData.Bq 8929 = (277199713903530:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 8929 = 277199713903530 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 8929 = (16929:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_8929
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 8930) ≤ val WuPaper.ClassicalFourthData.Bq 8930
    have hp : val WuPaper.ClassicalFourthData.Bq 8930 = (277201614100318:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 8930 = 277201614100318 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 8930 = (1693:ℝ)/400 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_8930
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 8931) ≤ val WuPaper.ClassicalFourthData.Bq 8931
    have hp : val WuPaper.ClassicalFourthData.Bq 8931 = (277203512659517:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 8931 = 277203512659517 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 8931 = (16931:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_8931
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 8932) ≤ val WuPaper.ClassicalFourthData.Bq 8932
    have hp : val WuPaper.ClassicalFourthData.Bq 8932 = (277205409581638:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 8932 = 277205409581638 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 8932 = (4233:ℝ)/1000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_8932
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 8933) ≤ val WuPaper.ClassicalFourthData.Bq 8933
    have hp : val WuPaper.ClassicalFourthData.Bq 8933 = (277207304867187:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 8933 = 277207304867187 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 8933 = (16933:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_8933
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 8934) ≤ val WuPaper.ClassicalFourthData.Bq 8934
    have hp : val WuPaper.ClassicalFourthData.Bq 8934 = (277209198516675:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 8934 = 277209198516675 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 8934 = (8467:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_8934
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 8935) ≤ val WuPaper.ClassicalFourthData.Bq 8935
    have hp : val WuPaper.ClassicalFourthData.Bq 8935 = (277211090530609:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 8935 = 277211090530609 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 8935 = (3387:ℝ)/800 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_8935
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 8936) ≤ val WuPaper.ClassicalFourthData.Bq 8936
    have hp : val WuPaper.ClassicalFourthData.Bq 8936 = (277212980909496:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 8936 = 277212980909496 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 8936 = (2117:ℝ)/500 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_8936
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 8937) ≤ val WuPaper.ClassicalFourthData.Bq 8937
    have hp : val WuPaper.ClassicalFourthData.Bq 8937 = (277214869653845:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 8937 = 277214869653845 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 8937 = (16937:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_8937
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 8938) ≤ val WuPaper.ClassicalFourthData.Bq 8938
    have hp : val WuPaper.ClassicalFourthData.Bq 8938 = (277216756764164:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 8938 = 277216756764164 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 8938 = (8469:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_8938
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 8939) ≤ val WuPaper.ClassicalFourthData.Bq 8939
    have hp : val WuPaper.ClassicalFourthData.Bq 8939 = (277218642240959:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 8939 = 277218642240959 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 8939 = (16939:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_8939
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 8940) ≤ val WuPaper.ClassicalFourthData.Bq 8940
    have hp : val WuPaper.ClassicalFourthData.Bq 8940 = (277220526084739:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 8940 = 277220526084739 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 8940 = (847:ℝ)/200 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_8940
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 8941) ≤ val WuPaper.ClassicalFourthData.Bq 8941
    have hp : val WuPaper.ClassicalFourthData.Bq 8941 = (277222408296011:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 8941 = 277222408296011 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 8941 = (16941:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_8941
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 8942) ≤ val WuPaper.ClassicalFourthData.Bq 8942
    have hp : val WuPaper.ClassicalFourthData.Bq 8942 = (277224288875280:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 8942 = 277224288875280 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 8942 = (8471:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_8942
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 8943) ≤ val WuPaper.ClassicalFourthData.Bq 8943
    have hp : val WuPaper.ClassicalFourthData.Bq 8943 = (277226167823055:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 8943 = 277226167823055 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 8943 = (16943:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_8943
end WuPaper.ClassicalFourthConditions
#print axioms WuPaper.ClassicalFourthConditions.Log_block_558

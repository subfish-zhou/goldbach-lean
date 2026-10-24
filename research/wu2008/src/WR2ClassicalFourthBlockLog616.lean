import WR2ClassicalFourthConditions
import WR2ClassicalFourthLogPoints616
noncomputable section
namespace WuPaper.ClassicalFourthConditions
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem Log_block_616 (j : Fin 16) (hj : 16*616+j.val < 10541) :
    WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 (16*616+j.val)) ≤ val WuPaper.ClassicalFourthData.Bq (16*616+j.val) := by
  fin_cases j
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 9856) ≤ val WuPaper.ClassicalFourthData.Bq 9856
    have hp : val WuPaper.ClassicalFourthData.Bq 9856 = (278320786464176:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 9856 = 278320786464176 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 9856 = (558:ℝ)/125 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_9856
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 9857) ≤ val WuPaper.ClassicalFourthData.Bq 9857
    have hp : val WuPaper.ClassicalFourthData.Bq 9857 = (278321366203215:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 9857 = 278321366203215 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 9857 = (17857:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_9857
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 9858) ≤ val WuPaper.ClassicalFourthData.Bq 9858
    have hp : val WuPaper.ClassicalFourthData.Bq 9858 = (278321944710815:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 9858 = 278321944710815 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 9858 = (8929:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_9858
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 9859) ≤ val WuPaper.ClassicalFourthData.Bq 9859
    have hp : val WuPaper.ClassicalFourthData.Bq 9859 = (278322521987353:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 9859 = 278322521987353 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 9859 = (17859:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_9859
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 9860) ≤ val WuPaper.ClassicalFourthData.Bq 9860
    have hp : val WuPaper.ClassicalFourthData.Bq 9860 = (278323098033202:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 9860 = 278323098033202 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 9860 = (893:ℝ)/200 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_9860
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 9861) ≤ val WuPaper.ClassicalFourthData.Bq 9861
    have hp : val WuPaper.ClassicalFourthData.Bq 9861 = (278323672848738:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 9861 = 278323672848738 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 9861 = (17861:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_9861
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 9862) ≤ val WuPaper.ClassicalFourthData.Bq 9862
    have hp : val WuPaper.ClassicalFourthData.Bq 9862 = (278324246434335:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 9862 = 278324246434335 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 9862 = (8931:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_9862
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 9863) ≤ val WuPaper.ClassicalFourthData.Bq 9863
    have hp : val WuPaper.ClassicalFourthData.Bq 9863 = (278324818790369:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 9863 = 278324818790369 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 9863 = (17863:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_9863
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 9864) ≤ val WuPaper.ClassicalFourthData.Bq 9864
    have hp : val WuPaper.ClassicalFourthData.Bq 9864 = (278325389917215:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 9864 = 278325389917215 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 9864 = (2233:ℝ)/500 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_9864
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 9865) ≤ val WuPaper.ClassicalFourthData.Bq 9865
    have hp : val WuPaper.ClassicalFourthData.Bq 9865 = (278325959815245:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 9865 = 278325959815245 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 9865 = (3573:ℝ)/800 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_9865
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 9866) ≤ val WuPaper.ClassicalFourthData.Bq 9866
    have hp : val WuPaper.ClassicalFourthData.Bq 9866 = (278326528484836:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 9866 = 278326528484836 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 9866 = (8933:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_9866
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 9867) ≤ val WuPaper.ClassicalFourthData.Bq 9867
    have hp : val WuPaper.ClassicalFourthData.Bq 9867 = (278327095926360:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 9867 = 278327095926360 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 9867 = (17867:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_9867
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 9868) ≤ val WuPaper.ClassicalFourthData.Bq 9868
    have hp : val WuPaper.ClassicalFourthData.Bq 9868 = (278327662140193:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 9868 = 278327662140193 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 9868 = (4467:ℝ)/1000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_9868
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 9869) ≤ val WuPaper.ClassicalFourthData.Bq 9869
    have hp : val WuPaper.ClassicalFourthData.Bq 9869 = (278328227126708:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 9869 = 278328227126708 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 9869 = (17869:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_9869
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 9870) ≤ val WuPaper.ClassicalFourthData.Bq 9870
    have hp : val WuPaper.ClassicalFourthData.Bq 9870 = (278328790886279:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 9870 = 278328790886279 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 9870 = (1787:ℝ)/400 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_9870
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 9871) ≤ val WuPaper.ClassicalFourthData.Bq 9871
    have hp : val WuPaper.ClassicalFourthData.Bq 9871 = (278329353419280:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 9871 = 278329353419280 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 9871 = (17871:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_9871
end WuPaper.ClassicalFourthConditions
#print axioms WuPaper.ClassicalFourthConditions.Log_block_616

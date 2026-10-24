import WR2ClassicalFourthConditions
import WR2ClassicalFourthLogPoints615
noncomputable section
namespace WuPaper.ClassicalFourthConditions
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem Log_block_615 (j : Fin 16) (hj : 16*615+j.val < 10541) :
    WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 (16*615+j.val)) ≤ val WuPaper.ClassicalFourthData.Bq (16*615+j.val) := by
  fin_cases j
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 9840) ≤ val WuPaper.ClassicalFourthData.Bq 9840
    have hp : val WuPaper.ClassicalFourthData.Bq 9840 = (278311342857313:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 9840 = 278311342857313 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 9840 = (223:ℝ)/50 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_9840
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 9841) ≤ val WuPaper.ClassicalFourthData.Bq 9841
    have hp : val WuPaper.ClassicalFourthData.Bq 9841 = (278311942350491:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 9841 = 278311942350491 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 9841 = (17841:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_9841
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 9842) ≤ val WuPaper.ClassicalFourthData.Bq 9842
    have hp : val WuPaper.ClassicalFourthData.Bq 9842 = (278312540606211:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 9842 = 278312540606211 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 9842 = (8921:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_9842
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 9843) ≤ val WuPaper.ClassicalFourthData.Bq 9843
    have hp : val WuPaper.ClassicalFourthData.Bq 9843 = (278313137624849:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 9843 = 278313137624849 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 9843 = (17843:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_9843
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 9844) ≤ val WuPaper.ClassicalFourthData.Bq 9844
    have hp : val WuPaper.ClassicalFourthData.Bq 9844 = (278313733406784:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 9844 = 278313733406784 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 9844 = (4461:ℝ)/1000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_9844
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 9845) ≤ val WuPaper.ClassicalFourthData.Bq 9845
    have hp : val WuPaper.ClassicalFourthData.Bq 9845 = (278314327952393:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 9845 = 278314327952393 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 9845 = (3569:ℝ)/800 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_9845
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 9846) ≤ val WuPaper.ClassicalFourthData.Bq 9846
    have hp : val WuPaper.ClassicalFourthData.Bq 9846 = (278314921262051:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 9846 = 278314921262051 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 9846 = (8923:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_9846
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 9847) ≤ val WuPaper.ClassicalFourthData.Bq 9847
    have hp : val WuPaper.ClassicalFourthData.Bq 9847 = (278315513336135:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 9847 = 278315513336135 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 9847 = (17847:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_9847
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 9848) ≤ val WuPaper.ClassicalFourthData.Bq 9848
    have hp : val WuPaper.ClassicalFourthData.Bq 9848 = (278316104175023:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 9848 = 278316104175023 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 9848 = (2231:ℝ)/500 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_9848
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 9849) ≤ val WuPaper.ClassicalFourthData.Bq 9849
    have hp : val WuPaper.ClassicalFourthData.Bq 9849 = (278316693779090:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 9849 = 278316693779090 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 9849 = (17849:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_9849
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 9850) ≤ val WuPaper.ClassicalFourthData.Bq 9850
    have hp : val WuPaper.ClassicalFourthData.Bq 9850 = (278317282148713:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 9850 = 278317282148713 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 9850 = (357:ℝ)/80 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_9850
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 9851) ≤ val WuPaper.ClassicalFourthData.Bq 9851
    have hp : val WuPaper.ClassicalFourthData.Bq 9851 = (278317869284267:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 9851 = 278317869284267 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 9851 = (17851:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_9851
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 9852) ≤ val WuPaper.ClassicalFourthData.Bq 9852
    have hp : val WuPaper.ClassicalFourthData.Bq 9852 = (278318455186130:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 9852 = 278318455186130 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 9852 = (4463:ℝ)/1000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_9852
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 9853) ≤ val WuPaper.ClassicalFourthData.Bq 9853
    have hp : val WuPaper.ClassicalFourthData.Bq 9853 = (278319039854676:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 9853 = 278319039854676 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 9853 = (17853:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_9853
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 9854) ≤ val WuPaper.ClassicalFourthData.Bq 9854
    have hp : val WuPaper.ClassicalFourthData.Bq 9854 = (278319623290282:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 9854 = 278319623290282 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 9854 = (8927:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_9854
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 9855) ≤ val WuPaper.ClassicalFourthData.Bq 9855
    have hp : val WuPaper.ClassicalFourthData.Bq 9855 = (278320205493324:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 9855 = 278320205493324 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 9855 = (3571:ℝ)/800 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_9855
end WuPaper.ClassicalFourthConditions
#print axioms WuPaper.ClassicalFourthConditions.Log_block_615

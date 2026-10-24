import WR2ClassicalFourthConditions
import WR2ClassicalFourthLogPoints304
noncomputable section
namespace WuPaper.ClassicalFourthConditions
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem Log_block_304 (j : Fin 16) (hj : 16*304+j.val < 10541) :
    WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 (16*304+j.val)) ≤ val WuPaper.ClassicalFourthData.Bq (16*304+j.val) := by
  fin_cases j
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 4864) ≤ val WuPaper.ClassicalFourthData.Bq 4864
    have hp : val WuPaper.ClassicalFourthData.Bq 4864 = (247420326145846:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 4864 = 247420326145846 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 4864 = (402:ℝ)/125 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_4864
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 4865) ≤ val WuPaper.ClassicalFourthData.Bq 4865
    have hp : val WuPaper.ClassicalFourthData.Bq 4865 = (247436168956481:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 4865 = 247436168956481 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 4865 = (2573:ℝ)/800 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_4865
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 4866) ≤ val WuPaper.ClassicalFourthData.Bq 4866
    have hp : val WuPaper.ClassicalFourthData.Bq 4866 = (247452005348352:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 4866 = 247452005348352 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 4866 = (6433:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_4866
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 4867) ≤ val WuPaper.ClassicalFourthData.Bq 4867
    have hp : val WuPaper.ClassicalFourthData.Bq 4867 = (247467835323846:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 4867 = 247467835323846 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 4867 = (12867:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_4867
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 4868) ≤ val WuPaper.ClassicalFourthData.Bq 4868
    have hp : val WuPaper.ClassicalFourthData.Bq 4868 = (247483658885352:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 4868 = 247483658885352 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 4868 = (3217:ℝ)/1000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_4868
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 4869) ≤ val WuPaper.ClassicalFourthData.Bq 4869
    have hp : val WuPaper.ClassicalFourthData.Bq 4869 = (247499476035256:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 4869 = 247499476035256 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 4869 = (12869:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_4869
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 4870) ≤ val WuPaper.ClassicalFourthData.Bq 4870
    have hp : val WuPaper.ClassicalFourthData.Bq 4870 = (247515286775944:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 4870 = 247515286775944 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 4870 = (1287:ℝ)/400 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_4870
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 4871) ≤ val WuPaper.ClassicalFourthData.Bq 4871
    have hp : val WuPaper.ClassicalFourthData.Bq 4871 = (247531091109801:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 4871 = 247531091109801 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 4871 = (12871:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_4871
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 4872) ≤ val WuPaper.ClassicalFourthData.Bq 4872
    have hp : val WuPaper.ClassicalFourthData.Bq 4872 = (247546889039210:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 4872 = 247546889039210 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 4872 = (1609:ℝ)/500 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_4872
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 4873) ≤ val WuPaper.ClassicalFourthData.Bq 4873
    have hp : val WuPaper.ClassicalFourthData.Bq 4873 = (247562680566554:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 4873 = 247562680566554 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 4873 = (12873:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_4873
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 4874) ≤ val WuPaper.ClassicalFourthData.Bq 4874
    have hp : val WuPaper.ClassicalFourthData.Bq 4874 = (247578465694214:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 4874 = 247578465694214 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 4874 = (6437:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_4874
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 4875) ≤ val WuPaper.ClassicalFourthData.Bq 4875
    have hp : val WuPaper.ClassicalFourthData.Bq 4875 = (247594244424572:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 4875 = 247594244424572 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 4875 = (103:ℝ)/32 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_4875
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 4876) ≤ val WuPaper.ClassicalFourthData.Bq 4876
    have hp : val WuPaper.ClassicalFourthData.Bq 4876 = (247610016760006:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 4876 = 247610016760006 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 4876 = (3219:ℝ)/1000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_4876
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 4877) ≤ val WuPaper.ClassicalFourthData.Bq 4877
    have hp : val WuPaper.ClassicalFourthData.Bq 4877 = (247625782702895:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 4877 = 247625782702895 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 4877 = (12877:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_4877
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 4878) ≤ val WuPaper.ClassicalFourthData.Bq 4878
    have hp : val WuPaper.ClassicalFourthData.Bq 4878 = (247641542255616:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 4878 = 247641542255616 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 4878 = (6439:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_4878
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 4879) ≤ val WuPaper.ClassicalFourthData.Bq 4879
    have hp : val WuPaper.ClassicalFourthData.Bq 4879 = (247657295420545:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 4879 = 247657295420545 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 4879 = (12879:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_4879
end WuPaper.ClassicalFourthConditions
#print axioms WuPaper.ClassicalFourthConditions.Log_block_304

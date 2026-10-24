import WR2ClassicalFourthConditions
import WR2ClassicalFourthLogPoints179
noncomputable section
namespace WuPaper.ClassicalFourthConditions
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem Log_block_179 (j : Fin 16) (hj : 16*179+j.val < 10541) :
    WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 (16*179+j.val)) ≤ val WuPaper.ClassicalFourthData.Bq (16*179+j.val) := by
  fin_cases j
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 2864) ≤ val WuPaper.ClassicalFourthData.Bq 2864
    have hp : val WuPaper.ClassicalFourthData.Bq 2864 = (198820324398296:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 2864 = 198820324398296 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 2864 = (679:ℝ)/250 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_2864
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 2865) ≤ val WuPaper.ClassicalFourthData.Bq 2865
    have hp : val WuPaper.ClassicalFourthData.Bq 2865 = (198855656916722:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 2865 = 198855656916722 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 2865 = (2173:ℝ)/800 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_2865
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 2866) ≤ val WuPaper.ClassicalFourthData.Bq 2866
    have hp : val WuPaper.ClassicalFourthData.Bq 2866 = (198890975120784:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 2866 = 198890975120784 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 2866 = (5433:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_2866
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 2867) ≤ val WuPaper.ClassicalFourthData.Bq 2867
    have hp : val WuPaper.ClassicalFourthData.Bq 2867 = (198926279016711:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 2867 = 198926279016711 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 2867 = (10867:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_2867
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 2868) ≤ val WuPaper.ClassicalFourthData.Bq 2868
    have hp : val WuPaper.ClassicalFourthData.Bq 2868 = (198961568610725:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 2868 = 198961568610725 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 2868 = (2717:ℝ)/1000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_2868
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 2869) ≤ val WuPaper.ClassicalFourthData.Bq 2869
    have hp : val WuPaper.ClassicalFourthData.Bq 2869 = (198996843909046:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 2869 = 198996843909046 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 2869 = (10869:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_2869
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 2870) ≤ val WuPaper.ClassicalFourthData.Bq 2870
    have hp : val WuPaper.ClassicalFourthData.Bq 2870 = (199032104917891:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 2870 = 199032104917891 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 2870 = (1087:ℝ)/400 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_2870
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 2871) ≤ val WuPaper.ClassicalFourthData.Bq 2871
    have hp : val WuPaper.ClassicalFourthData.Bq 2871 = (199067351643473:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 2871 = 199067351643473 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 2871 = (10871:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_2871
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 2872) ≤ val WuPaper.ClassicalFourthData.Bq 2872
    have hp : val WuPaper.ClassicalFourthData.Bq 2872 = (199102584092003:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 2872 = 199102584092003 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 2872 = (1359:ℝ)/500 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_2872
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 2873) ≤ val WuPaper.ClassicalFourthData.Bq 2873
    have hp : val WuPaper.ClassicalFourthData.Bq 2873 = (199137802269688:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 2873 = 199137802269688 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 2873 = (10873:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_2873
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 2874) ≤ val WuPaper.ClassicalFourthData.Bq 2874
    have hp : val WuPaper.ClassicalFourthData.Bq 2874 = (199173006182731:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 2874 = 199173006182731 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 2874 = (5437:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_2874
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 2875) ≤ val WuPaper.ClassicalFourthData.Bq 2875
    have hp : val WuPaper.ClassicalFourthData.Bq 2875 = (199208195837332:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 2875 = 199208195837332 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 2875 = (87:ℝ)/32 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_2875
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 2876) ≤ val WuPaper.ClassicalFourthData.Bq 2876
    have hp : val WuPaper.ClassicalFourthData.Bq 2876 = (199243371239689:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 2876 = 199243371239689 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 2876 = (2719:ℝ)/1000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_2876
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 2877) ≤ val WuPaper.ClassicalFourthData.Bq 2877
    have hp : val WuPaper.ClassicalFourthData.Bq 2877 = (199278532395995:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 2877 = 199278532395995 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 2877 = (10877:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_2877
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 2878) ≤ val WuPaper.ClassicalFourthData.Bq 2878
    have hp : val WuPaper.ClassicalFourthData.Bq 2878 = (199313679312442:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 2878 = 199313679312442 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 2878 = (5439:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_2878
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 2879) ≤ val WuPaper.ClassicalFourthData.Bq 2879
    have hp : val WuPaper.ClassicalFourthData.Bq 2879 = (199348811995216:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 2879 = 199348811995216 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 2879 = (10879:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_2879
end WuPaper.ClassicalFourthConditions
#print axioms WuPaper.ClassicalFourthConditions.Log_block_179

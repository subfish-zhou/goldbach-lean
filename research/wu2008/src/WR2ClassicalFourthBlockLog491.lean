import WR2ClassicalFourthConditions
import WR2ClassicalFourthLogPoints491
noncomputable section
namespace WuPaper.ClassicalFourthConditions
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem Log_block_491 (j : Fin 16) (hj : 16*491+j.val < 10541) :
    WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 (16*491+j.val)) ≤ val WuPaper.ClassicalFourthData.Bq (16*491+j.val) := by
  fin_cases j
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 7856) ≤ val WuPaper.ClassicalFourthData.Bq 7856
    have hp : val WuPaper.ClassicalFourthData.Bq 7856 = (274101843449980:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 7856 = 274101843449980 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 7856 = (991:ℝ)/250 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_7856
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 7857) ≤ val WuPaper.ClassicalFourthData.Bq 7857
    have hp : val WuPaper.ClassicalFourthData.Bq 7857 = (274105833223920:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 7857 = 274105833223920 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 7857 = (15857:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_7857
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 7858) ≤ val WuPaper.ClassicalFourthData.Bq 7858
    have hp : val WuPaper.ClassicalFourthData.Bq 7858 = (274109820700510:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 7858 = 274109820700510 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 7858 = (7929:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_7858
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 7859) ≤ val WuPaper.ClassicalFourthData.Bq 7859
    have hp : val WuPaper.ClassicalFourthData.Bq 7859 = (274113805880486:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 7859 = 274113805880486 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 7859 = (15859:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_7859
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 7860) ≤ val WuPaper.ClassicalFourthData.Bq 7860
    have hp : val WuPaper.ClassicalFourthData.Bq 7860 = (274117788764586:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 7860 = 274117788764586 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 7860 = (793:ℝ)/200 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_7860
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 7861) ≤ val WuPaper.ClassicalFourthData.Bq 7861
    have hp : val WuPaper.ClassicalFourthData.Bq 7861 = (274121769353546:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 7861 = 274121769353546 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 7861 = (15861:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_7861
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 7862) ≤ val WuPaper.ClassicalFourthData.Bq 7862
    have hp : val WuPaper.ClassicalFourthData.Bq 7862 = (274125747648102:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 7862 = 274125747648102 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 7862 = (7931:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_7862
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 7863) ≤ val WuPaper.ClassicalFourthData.Bq 7863
    have hp : val WuPaper.ClassicalFourthData.Bq 7863 = (274129723648990:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 7863 = 274129723648990 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 7863 = (15863:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_7863
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 7864) ≤ val WuPaper.ClassicalFourthData.Bq 7864
    have hp : val WuPaper.ClassicalFourthData.Bq 7864 = (274133697356947:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 7864 = 274133697356947 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 7864 = (1983:ℝ)/500 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_7864
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 7865) ≤ val WuPaper.ClassicalFourthData.Bq 7865
    have hp : val WuPaper.ClassicalFourthData.Bq 7865 = (274137668772708:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 7865 = 274137668772708 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 7865 = (3173:ℝ)/800 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_7865
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 7866) ≤ val WuPaper.ClassicalFourthData.Bq 7866
    have hp : val WuPaper.ClassicalFourthData.Bq 7866 = (274141637897008:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 7866 = 274141637897008 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 7866 = (7933:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_7866
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 7867) ≤ val WuPaper.ClassicalFourthData.Bq 7867
    have hp : val WuPaper.ClassicalFourthData.Bq 7867 = (274145604730582:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 7867 = 274145604730582 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 7867 = (15867:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_7867
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 7868) ≤ val WuPaper.ClassicalFourthData.Bq 7868
    have hp : val WuPaper.ClassicalFourthData.Bq 7868 = (274149569274165:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 7868 = 274149569274165 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 7868 = (3967:ℝ)/1000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_7868
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 7869) ≤ val WuPaper.ClassicalFourthData.Bq 7869
    have hp : val WuPaper.ClassicalFourthData.Bq 7869 = (274153531528492:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 7869 = 274153531528492 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 7869 = (15869:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_7869
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 7870) ≤ val WuPaper.ClassicalFourthData.Bq 7870
    have hp : val WuPaper.ClassicalFourthData.Bq 7870 = (274157491494297:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 7870 = 274157491494297 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 7870 = (1587:ℝ)/400 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_7870
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 7871) ≤ val WuPaper.ClassicalFourthData.Bq 7871
    have hp : val WuPaper.ClassicalFourthData.Bq 7871 = (274161449172313:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 7871 = 274161449172313 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 7871 = (15871:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_7871
end WuPaper.ClassicalFourthConditions
#print axioms WuPaper.ClassicalFourthConditions.Log_block_491

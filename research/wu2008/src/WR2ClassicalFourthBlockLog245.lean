import WR2ClassicalFourthConditions
import WR2ClassicalFourthLogPoints245
noncomputable section
namespace WuPaper.ClassicalFourthConditions
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem Log_block_245 (j : Fin 16) (hj : 16*245+j.val < 10541) :
    WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 (16*245+j.val)) ≤ val WuPaper.ClassicalFourthData.Bq (16*245+j.val) := by
  fin_cases j
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 3920) ≤ val WuPaper.ClassicalFourthData.Bq 3920
    have hp : val WuPaper.ClassicalFourthData.Bq 3920 = (229227129096123:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 3920 = 229227129096123 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 3920 = (149:ℝ)/50 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_3920
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 3921) ≤ val WuPaper.ClassicalFourthData.Bq 3921
    have hp : val WuPaper.ClassicalFourthData.Bq 3921 = (229250264025586:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 3921 = 229250264025586 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 3921 = (11921:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_3921
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 3922) ≤ val WuPaper.ClassicalFourthData.Bq 3922
    have hp : val WuPaper.ClassicalFourthData.Bq 3922 = (229273389726501:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 3922 = 229273389726501 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 3922 = (5961:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_3922
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 3923) ≤ val WuPaper.ClassicalFourthData.Bq 3923
    have hp : val WuPaper.ClassicalFourthData.Bq 3923 = (229296506202538:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 3923 = 229296506202538 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 3923 = (11923:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_3923
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 3924) ≤ val WuPaper.ClassicalFourthData.Bq 3924
    have hp : val WuPaper.ClassicalFourthData.Bq 3924 = (229319613457368:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 3924 = 229319613457368 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 3924 = (2981:ℝ)/1000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_3924
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 3925) ≤ val WuPaper.ClassicalFourthData.Bq 3925
    have hp : val WuPaper.ClassicalFourthData.Bq 3925 = (229342711494660:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 3925 = 229342711494660 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 3925 = (477:ℝ)/160 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_3925
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 3926) ≤ val WuPaper.ClassicalFourthData.Bq 3926
    have hp : val WuPaper.ClassicalFourthData.Bq 3926 = (229365800318080:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 3926 = 229365800318080 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 3926 = (5963:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_3926
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 3927) ≤ val WuPaper.ClassicalFourthData.Bq 3927
    have hp : val WuPaper.ClassicalFourthData.Bq 3927 = (229388879931292:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 3927 = 229388879931292 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 3927 = (11927:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_3927
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 3928) ≤ val WuPaper.ClassicalFourthData.Bq 3928
    have hp : val WuPaper.ClassicalFourthData.Bq 3928 = (229411950337960:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 3928 = 229411950337960 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 3928 = (1491:ℝ)/500 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_3928
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 3929) ≤ val WuPaper.ClassicalFourthData.Bq 3929
    have hp : val WuPaper.ClassicalFourthData.Bq 3929 = (229435011541746:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 3929 = 229435011541746 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 3929 = (11929:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_3929
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 3930) ≤ val WuPaper.ClassicalFourthData.Bq 3930
    have hp : val WuPaper.ClassicalFourthData.Bq 3930 = (229458063546309:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 3930 = 229458063546309 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 3930 = (1193:ℝ)/400 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_3930
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 3931) ≤ val WuPaper.ClassicalFourthData.Bq 3931
    have hp : val WuPaper.ClassicalFourthData.Bq 3931 = (229481106355307:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 3931 = 229481106355307 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 3931 = (11931:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_3931
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 3932) ≤ val WuPaper.ClassicalFourthData.Bq 3932
    have hp : val WuPaper.ClassicalFourthData.Bq 3932 = (229504139972397:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 3932 = 229504139972397 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 3932 = (2983:ℝ)/1000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_3932
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 3933) ≤ val WuPaper.ClassicalFourthData.Bq 3933
    have hp : val WuPaper.ClassicalFourthData.Bq 3933 = (229527164401232:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 3933 = 229527164401232 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 3933 = (11933:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_3933
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 3934) ≤ val WuPaper.ClassicalFourthData.Bq 3934
    have hp : val WuPaper.ClassicalFourthData.Bq 3934 = (229550179645466:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 3934 = 229550179645466 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 3934 = (5967:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_3934
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 3935) ≤ val WuPaper.ClassicalFourthData.Bq 3935
    have hp : val WuPaper.ClassicalFourthData.Bq 3935 = (229573185708750:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 3935 = 229573185708750 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 3935 = (2387:ℝ)/800 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_3935
end WuPaper.ClassicalFourthConditions
#print axioms WuPaper.ClassicalFourthConditions.Log_block_245

import WR2ClassicalFourthConditions
import WR2ClassicalFourthLogPoints372
noncomputable section
namespace WuPaper.ClassicalFourthConditions
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem Log_block_372 (j : Fin 16) (hj : 16*372+j.val < 10541) :
    WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 (16*372+j.val)) ≤ val WuPaper.ClassicalFourthData.Bq (16*372+j.val) := by
  fin_cases j
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 5952) ≤ val WuPaper.ClassicalFourthData.Bq 5952
    have hp : val WuPaper.ClassicalFourthData.Bq 5952 = (261318570778942:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 5952 = 261318570778942 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 5952 = (436:ℝ)/125 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_5952
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 5953) ≤ val WuPaper.ClassicalFourthData.Bq 5953
    have hp : val WuPaper.ClassicalFourthData.Bq 5953 = (261328646783932:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 5953 = 261328646783932 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 5953 = (13953:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_5953
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 5954) ≤ val WuPaper.ClassicalFourthData.Bq 5954
    have hp : val WuPaper.ClassicalFourthData.Bq 5954 = (261338718451050:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 5954 = 261338718451050 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 5954 = (6977:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_5954
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 5955) ≤ val WuPaper.ClassicalFourthData.Bq 5955
    have hp : val WuPaper.ClassicalFourthData.Bq 5955 = (261348785781809:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 5955 = 261348785781809 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 5955 = (2791:ℝ)/800 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_5955
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 5956) ≤ val WuPaper.ClassicalFourthData.Bq 5956
    have hp : val WuPaper.ClassicalFourthData.Bq 5956 = (261358848777722:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 5956 = 261358848777722 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 5956 = (3489:ℝ)/1000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_5956
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 5957) ≤ val WuPaper.ClassicalFourthData.Bq 5957
    have hp : val WuPaper.ClassicalFourthData.Bq 5957 = (261368907440302:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 5957 = 261368907440302 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 5957 = (13957:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_5957
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 5958) ≤ val WuPaper.ClassicalFourthData.Bq 5958
    have hp : val WuPaper.ClassicalFourthData.Bq 5958 = (261378961771061:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 5958 = 261378961771061 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 5958 = (6979:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_5958
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 5959) ≤ val WuPaper.ClassicalFourthData.Bq 5959
    have hp : val WuPaper.ClassicalFourthData.Bq 5959 = (261389011771510:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 5959 = 261389011771510 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 5959 = (13959:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_5959
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 5960) ≤ val WuPaper.ClassicalFourthData.Bq 5960
    have hp : val WuPaper.ClassicalFourthData.Bq 5960 = (261399057443161:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 5960 = 261399057443161 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 5960 = (349:ℝ)/100 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_5960
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 5961) ≤ val WuPaper.ClassicalFourthData.Bq 5961
    have hp : val WuPaper.ClassicalFourthData.Bq 5961 = (261409098787524:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 5961 = 261409098787524 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 5961 = (13961:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_5961
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 5962) ≤ val WuPaper.ClassicalFourthData.Bq 5962
    have hp : val WuPaper.ClassicalFourthData.Bq 5962 = (261419135806107:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 5962 = 261419135806107 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 5962 = (6981:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_5962
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 5963) ≤ val WuPaper.ClassicalFourthData.Bq 5963
    have hp : val WuPaper.ClassicalFourthData.Bq 5963 = (261429168500421:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 5963 = 261429168500421 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 5963 = (13963:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_5963
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 5964) ≤ val WuPaper.ClassicalFourthData.Bq 5964
    have hp : val WuPaper.ClassicalFourthData.Bq 5964 = (261439196871974:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 5964 = 261439196871974 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 5964 = (3491:ℝ)/1000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_5964
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 5965) ≤ val WuPaper.ClassicalFourthData.Bq 5965
    have hp : val WuPaper.ClassicalFourthData.Bq 5965 = (261449220922272:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 5965 = 261449220922272 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 5965 = (2793:ℝ)/800 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_5965
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 5966) ≤ val WuPaper.ClassicalFourthData.Bq 5966
    have hp : val WuPaper.ClassicalFourthData.Bq 5966 = (261459240652825:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 5966 = 261459240652825 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 5966 = (6983:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_5966
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 5967) ≤ val WuPaper.ClassicalFourthData.Bq 5967
    have hp : val WuPaper.ClassicalFourthData.Bq 5967 = (261469256065138:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 5967 = 261469256065138 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 5967 = (13967:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_5967
end WuPaper.ClassicalFourthConditions
#print axioms WuPaper.ClassicalFourthConditions.Log_block_372

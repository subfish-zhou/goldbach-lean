import WR2ClassicalFourthConditions
import WR2ClassicalFourthLogPoints186
noncomputable section
namespace WuPaper.ClassicalFourthConditions
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem Log_block_186 (j : Fin 16) (hj : 16*186+j.val < 10541) :
    WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 (16*186+j.val)) ≤ val WuPaper.ClassicalFourthData.Bq (16*186+j.val) := by
  fin_cases j
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 2976) ≤ val WuPaper.ClassicalFourthData.Bq 2976
    have hp : val WuPaper.ClassicalFourthData.Bq 2976 = (202689987422299:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 2976 = 202689987422299 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 2976 = (343:ℝ)/125 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_2976
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 2977) ≤ val WuPaper.ClassicalFourthData.Bq 2977
    have hp : val WuPaper.ClassicalFourthData.Bq 2977 = (202723754700632:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 2977 = 202723754700632 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 2977 = (10977:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_2977
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 2978) ≤ val WuPaper.ClassicalFourthData.Bq 2978
    have hp : val WuPaper.ClassicalFourthData.Bq 2978 = (202757508342027:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 2978 = 202757508342027 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 2978 = (5489:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_2978
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 2979) ≤ val WuPaper.ClassicalFourthData.Bq 2979
    have hp : val WuPaper.ClassicalFourthData.Bq 2979 = (202791248352355:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 2979 = 202791248352355 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 2979 = (10979:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_2979
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 2980) ≤ val WuPaper.ClassicalFourthData.Bq 2980
    have hp : val WuPaper.ClassicalFourthData.Bq 2980 = (202824974737483:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 2980 = 202824974737483 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 2980 = (549:ℝ)/200 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_2980
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 2981) ≤ val WuPaper.ClassicalFourthData.Bq 2981
    have hp : val WuPaper.ClassicalFourthData.Bq 2981 = (202858687503278:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 2981 = 202858687503278 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 2981 = (10981:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_2981
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 2982) ≤ val WuPaper.ClassicalFourthData.Bq 2982
    have hp : val WuPaper.ClassicalFourthData.Bq 2982 = (202892386655602:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 2982 = 202892386655602 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 2982 = (5491:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_2982
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 2983) ≤ val WuPaper.ClassicalFourthData.Bq 2983
    have hp : val WuPaper.ClassicalFourthData.Bq 2983 = (202926072200313:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 2983 = 202926072200313 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 2983 = (10983:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_2983
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 2984) ≤ val WuPaper.ClassicalFourthData.Bq 2984
    have hp : val WuPaper.ClassicalFourthData.Bq 2984 = (202959744143267:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 2984 = 202959744143267 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 2984 = (1373:ℝ)/500 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_2984
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 2985) ≤ val WuPaper.ClassicalFourthData.Bq 2985
    have hp : val WuPaper.ClassicalFourthData.Bq 2985 = (202993402490318:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 2985 = 202993402490318 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 2985 = (2197:ℝ)/800 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_2985
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 2986) ≤ val WuPaper.ClassicalFourthData.Bq 2986
    have hp : val WuPaper.ClassicalFourthData.Bq 2986 = (203027047247315:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 2986 = 203027047247315 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 2986 = (5493:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_2986
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 2987) ≤ val WuPaper.ClassicalFourthData.Bq 2987
    have hp : val WuPaper.ClassicalFourthData.Bq 2987 = (203060678420105:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 2987 = 203060678420105 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 2987 = (10987:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_2987
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 2988) ≤ val WuPaper.ClassicalFourthData.Bq 2988
    have hp : val WuPaper.ClassicalFourthData.Bq 2988 = (203094296014533:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 2988 = 203094296014533 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 2988 = (2747:ℝ)/1000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_2988
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 2989) ≤ val WuPaper.ClassicalFourthData.Bq 2989
    have hp : val WuPaper.ClassicalFourthData.Bq 2989 = (203127900036437:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 2989 = 203127900036437 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 2989 = (10989:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_2989
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 2990) ≤ val WuPaper.ClassicalFourthData.Bq 2990
    have hp : val WuPaper.ClassicalFourthData.Bq 2990 = (203161490491658:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 2990 = 203161490491658 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 2990 = (1099:ℝ)/400 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_2990
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 2991) ≤ val WuPaper.ClassicalFourthData.Bq 2991
    have hp : val WuPaper.ClassicalFourthData.Bq 2991 = (203195067386028:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 2991 = 203195067386028 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 2991 = (10991:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_2991
end WuPaper.ClassicalFourthConditions
#print axioms WuPaper.ClassicalFourthConditions.Log_block_186

import WR2ClassicalFourthConditions
import WR2ClassicalFourthLogPoints561
noncomputable section
namespace WuPaper.ClassicalFourthConditions
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem Log_block_561 (j : Fin 16) (hj : 16*561+j.val < 10541) :
    WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 (16*561+j.val)) ≤ val WuPaper.ClassicalFourthData.Bq (16*561+j.val) := by
  fin_cases j
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 8976) ≤ val WuPaper.ClassicalFourthData.Bq 8976
    have hp : val WuPaper.ClassicalFourthData.Bq 8976 = (277287261138136:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 8976 = 277287261138136 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 8976 = (1061:ℝ)/250 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_8976
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 8977) ≤ val WuPaper.ClassicalFourthData.Bq 8977
    have hp : val WuPaper.ClassicalFourthData.Bq 8977 = (277289084915431:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 8977 = 277289084915431 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 8977 = (16977:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_8977
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 8978) ≤ val WuPaper.ClassicalFourthData.Bq 8978
    have hp : val WuPaper.ClassicalFourthData.Bq 8978 = (277290907078863:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 8978 = 277290907078863 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 8978 = (8489:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_8978
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 8979) ≤ val WuPaper.ClassicalFourthData.Bq 8979
    have hp : val WuPaper.ClassicalFourthData.Bq 8979 = (277292727628932:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 8979 = 277292727628932 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 8979 = (16979:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_8979
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 8980) ≤ val WuPaper.ClassicalFourthData.Bq 8980
    have hp : val WuPaper.ClassicalFourthData.Bq 8980 = (277294546566139:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 8980 = 277294546566139 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 8980 = (849:ℝ)/200 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_8980
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 8981) ≤ val WuPaper.ClassicalFourthData.Bq 8981
    have hp : val WuPaper.ClassicalFourthData.Bq 8981 = (277296363890986:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 8981 = 277296363890986 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 8981 = (16981:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_8981
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 8982) ≤ val WuPaper.ClassicalFourthData.Bq 8982
    have hp : val WuPaper.ClassicalFourthData.Bq 8982 = (277298179603971:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 8982 = 277298179603971 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 8982 = (8491:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_8982
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 8983) ≤ val WuPaper.ClassicalFourthData.Bq 8983
    have hp : val WuPaper.ClassicalFourthData.Bq 8983 = (277299993705594:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 8983 = 277299993705594 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 8983 = (16983:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_8983
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 8984) ≤ val WuPaper.ClassicalFourthData.Bq 8984
    have hp : val WuPaper.ClassicalFourthData.Bq 8984 = (277301806196357:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 8984 = 277301806196357 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 8984 = (2123:ℝ)/500 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_8984
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 8985) ≤ val WuPaper.ClassicalFourthData.Bq 8985
    have hp : val WuPaper.ClassicalFourthData.Bq 8985 = (277303617076758:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 8985 = 277303617076758 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 8985 = (3397:ℝ)/800 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_8985
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 8986) ≤ val WuPaper.ClassicalFourthData.Bq 8986
    have hp : val WuPaper.ClassicalFourthData.Bq 8986 = (277305426347298:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 8986 = 277305426347298 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 8986 = (8493:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_8986
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 8987) ≤ val WuPaper.ClassicalFourthData.Bq 8987
    have hp : val WuPaper.ClassicalFourthData.Bq 8987 = (277307234008475:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 8987 = 277307234008475 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 8987 = (16987:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_8987
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 8988) ≤ val WuPaper.ClassicalFourthData.Bq 8988
    have hp : val WuPaper.ClassicalFourthData.Bq 8988 = (277309040060788:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 8988 = 277309040060788 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 8988 = (4247:ℝ)/1000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_8988
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 8989) ≤ val WuPaper.ClassicalFourthData.Bq 8989
    have hp : val WuPaper.ClassicalFourthData.Bq 8989 = (277310844504738:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 8989 = 277310844504738 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 8989 = (16989:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_8989
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 8990) ≤ val WuPaper.ClassicalFourthData.Bq 8990
    have hp : val WuPaper.ClassicalFourthData.Bq 8990 = (277312647340821:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 8990 = 277312647340821 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 8990 = (1699:ℝ)/400 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_8990
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 8991) ≤ val WuPaper.ClassicalFourthData.Bq 8991
    have hp : val WuPaper.ClassicalFourthData.Bq 8991 = (277314448569539:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 8991 = 277314448569539 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 8991 = (16991:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_8991
end WuPaper.ClassicalFourthConditions
#print axioms WuPaper.ClassicalFourthConditions.Log_block_561

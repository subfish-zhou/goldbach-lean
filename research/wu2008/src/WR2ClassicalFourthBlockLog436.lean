import WR2ClassicalFourthConditions
import WR2ClassicalFourthLogPoints436
noncomputable section
namespace WuPaper.ClassicalFourthConditions
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem Log_block_436 (j : Fin 16) (hj : 16*436+j.val < 10541) :
    WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 (16*436+j.val)) ≤ val WuPaper.ClassicalFourthData.Bq (16*436+j.val) := by
  fin_cases j
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 6976) ≤ val WuPaper.ClassicalFourthData.Bq 6976
    have hp : val WuPaper.ClassicalFourthData.Bq 6976 = (269609163959370:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 6976 = 269609163959370 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 6976 = (468:ℝ)/125 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_6976
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 6977) ≤ val WuPaper.ClassicalFourthData.Bq 6977
    have hp : val WuPaper.ClassicalFourthData.Bq 6977 = (269615494047014:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 6977 = 269615494047014 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 6977 = (14977:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_6977
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 6978) ≤ val WuPaper.ClassicalFourthData.Bq 6978
    have hp : val WuPaper.ClassicalFourthData.Bq 6978 = (269621821073054:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 6978 = 269621821073054 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 6978 = (7489:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_6978
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 6979) ≤ val WuPaper.ClassicalFourthData.Bq 6979
    have hp : val WuPaper.ClassicalFourthData.Bq 6979 = (269628145038507:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 6979 = 269628145038507 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 6979 = (14979:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_6979
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 6980) ≤ val WuPaper.ClassicalFourthData.Bq 6980
    have hp : val WuPaper.ClassicalFourthData.Bq 6980 = (269634465944390:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 6980 = 269634465944390 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 6980 = (749:ℝ)/200 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_6980
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 6981) ≤ val WuPaper.ClassicalFourthData.Bq 6981
    have hp : val WuPaper.ClassicalFourthData.Bq 6981 = (269640783791718:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 6981 = 269640783791718 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 6981 = (14981:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_6981
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 6982) ≤ val WuPaper.ClassicalFourthData.Bq 6982
    have hp : val WuPaper.ClassicalFourthData.Bq 6982 = (269647098581508:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 6982 = 269647098581508 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 6982 = (7491:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_6982
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 6983) ≤ val WuPaper.ClassicalFourthData.Bq 6983
    have hp : val WuPaper.ClassicalFourthData.Bq 6983 = (269653410314774:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 6983 = 269653410314774 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 6983 = (14983:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_6983
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 6984) ≤ val WuPaper.ClassicalFourthData.Bq 6984
    have hp : val WuPaper.ClassicalFourthData.Bq 6984 = (269659718992533:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 6984 = 269659718992533 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 6984 = (1873:ℝ)/500 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_6984
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 6985) ≤ val WuPaper.ClassicalFourthData.Bq 6985
    have hp : val WuPaper.ClassicalFourthData.Bq 6985 = (269666024615798:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 6985 = 269666024615798 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 6985 = (2997:ℝ)/800 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_6985
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 6986) ≤ val WuPaper.ClassicalFourthData.Bq 6986
    have hp : val WuPaper.ClassicalFourthData.Bq 6986 = (269672327185583:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 6986 = 269672327185583 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 6986 = (7493:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_6986
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 6987) ≤ val WuPaper.ClassicalFourthData.Bq 6987
    have hp : val WuPaper.ClassicalFourthData.Bq 6987 = (269678626702904:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 6987 = 269678626702904 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 6987 = (14987:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_6987
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 6988) ≤ val WuPaper.ClassicalFourthData.Bq 6988
    have hp : val WuPaper.ClassicalFourthData.Bq 6988 = (269684923168772:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 6988 = 269684923168772 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 6988 = (3747:ℝ)/1000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_6988
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 6989) ≤ val WuPaper.ClassicalFourthData.Bq 6989
    have hp : val WuPaper.ClassicalFourthData.Bq 6989 = (269691216584201:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 6989 = 269691216584201 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 6989 = (14989:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_6989
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 6990) ≤ val WuPaper.ClassicalFourthData.Bq 6990
    have hp : val WuPaper.ClassicalFourthData.Bq 6990 = (269697506950205:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 6990 = 269697506950205 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 6990 = (1499:ℝ)/400 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_6990
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 6991) ≤ val WuPaper.ClassicalFourthData.Bq 6991
    have hp : val WuPaper.ClassicalFourthData.Bq 6991 = (269703794267794:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 6991 = 269703794267794 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 6991 = (14991:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_6991
end WuPaper.ClassicalFourthConditions
#print axioms WuPaper.ClassicalFourthConditions.Log_block_436

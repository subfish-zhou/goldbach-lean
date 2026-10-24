import WR2ClassicalFourthConditions
import WR2ClassicalFourthLogPoints374
noncomputable section
namespace WuPaper.ClassicalFourthConditions
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem Log_block_374 (j : Fin 16) (hj : 16*374+j.val < 10541) :
    WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 (16*374+j.val)) ≤ val WuPaper.ClassicalFourthData.Bq (16*374+j.val) := by
  fin_cases j
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 5984) ≤ val WuPaper.ClassicalFourthData.Bq 5984
    have hp : val WuPaper.ClassicalFourthData.Bq 5984 = (261638858840732:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 5984 = 261638858840732 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 5984 = (437:ℝ)/125 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_5984
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 5985) ≤ val WuPaper.ClassicalFourthData.Bq 5985
    have hp : val WuPaper.ClassicalFourthData.Bq 5985 = (261648796781668:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 5985 = 261648796781668 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 5985 = (2797:ℝ)/800 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_5985
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 5986) ≤ val WuPaper.ClassicalFourthData.Bq 5986
    have hp : val WuPaper.ClassicalFourthData.Bq 5986 = (261658730432874:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 5986 = 261658730432874 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 5986 = (6993:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_5986
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 5987) ≤ val WuPaper.ClassicalFourthData.Bq 5987
    have hp : val WuPaper.ClassicalFourthData.Bq 5987 = (261668659795846:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 5987 = 261668659795846 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 5987 = (13987:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_5987
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 5988) ≤ val WuPaper.ClassicalFourthData.Bq 5988
    have hp : val WuPaper.ClassicalFourthData.Bq 5988 = (261678584872077:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 5988 = 261678584872077 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 5988 = (3497:ℝ)/1000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_5988
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 5989) ≤ val WuPaper.ClassicalFourthData.Bq 5989
    have hp : val WuPaper.ClassicalFourthData.Bq 5989 = (261688505663061:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 5989 = 261688505663061 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 5989 = (13989:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_5989
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 5990) ≤ val WuPaper.ClassicalFourthData.Bq 5990
    have hp : val WuPaper.ClassicalFourthData.Bq 5990 = (261698422170290:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 5990 = 261698422170290 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 5990 = (1399:ℝ)/400 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_5990
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 5991) ≤ val WuPaper.ClassicalFourthData.Bq 5991
    have hp : val WuPaper.ClassicalFourthData.Bq 5991 = (261708334395257:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 5991 = 261708334395257 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 5991 = (13991:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_5991
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 5992) ≤ val WuPaper.ClassicalFourthData.Bq 5992
    have hp : val WuPaper.ClassicalFourthData.Bq 5992 = (261718242339452:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 5992 = 261718242339452 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 5992 = (1749:ℝ)/500 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_5992
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 5993) ≤ val WuPaper.ClassicalFourthData.Bq 5993
    have hp : val WuPaper.ClassicalFourthData.Bq 5993 = (261728146004368:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 5993 = 261728146004368 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 5993 = (13993:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_5993
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 5994) ≤ val WuPaper.ClassicalFourthData.Bq 5994
    have hp : val WuPaper.ClassicalFourthData.Bq 5994 = (261738045391494:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 5994 = 261738045391494 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 5994 = (6997:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_5994
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 5995) ≤ val WuPaper.ClassicalFourthData.Bq 5995
    have hp : val WuPaper.ClassicalFourthData.Bq 5995 = (261747940502320:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 5995 = 261747940502320 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 5995 = (2799:ℝ)/800 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_5995
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 5996) ≤ val WuPaper.ClassicalFourthData.Bq 5996
    have hp : val WuPaper.ClassicalFourthData.Bq 5996 = (261757831338335:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 5996 = 261757831338335 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 5996 = (3499:ℝ)/1000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_5996
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 5997) ≤ val WuPaper.ClassicalFourthData.Bq 5997
    have hp : val WuPaper.ClassicalFourthData.Bq 5997 = (261767717901028:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 5997 = 261767717901028 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 5997 = (13997:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_5997
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 5998) ≤ val WuPaper.ClassicalFourthData.Bq 5998
    have hp : val WuPaper.ClassicalFourthData.Bq 5998 = (261777600191886:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 5998 = 261777600191886 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 5998 = (6999:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_5998
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 5999) ≤ val WuPaper.ClassicalFourthData.Bq 5999
    have hp : val WuPaper.ClassicalFourthData.Bq 5999 = (261787478212398:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 5999 = 261787478212398 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 5999 = (13999:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_5999
end WuPaper.ClassicalFourthConditions
#print axioms WuPaper.ClassicalFourthConditions.Log_block_374

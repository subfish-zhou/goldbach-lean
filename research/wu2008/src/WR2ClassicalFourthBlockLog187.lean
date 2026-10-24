import WR2ClassicalFourthConditions
import WR2ClassicalFourthLogPoints187
noncomputable section
namespace WuPaper.ClassicalFourthConditions
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem Log_block_187 (j : Fin 16) (hj : 16*187+j.val < 10541) :
    WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 (16*187+j.val)) ≤ val WuPaper.ClassicalFourthData.Bq (16*187+j.val) := by
  fin_cases j
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 2992) ≤ val WuPaper.ClassicalFourthData.Bq 2992
    have hp : val WuPaper.ClassicalFourthData.Bq 2992 = (203228630725380:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 2992 = 203228630725380 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 2992 = (687:ℝ)/250 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_2992
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 2993) ≤ val WuPaper.ClassicalFourthData.Bq 2993
    have hp : val WuPaper.ClassicalFourthData.Bq 2993 = (203262180515543:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 2993 = 203262180515543 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 2993 = (10993:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_2993
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 2994) ≤ val WuPaper.ClassicalFourthData.Bq 2994
    have hp : val WuPaper.ClassicalFourthData.Bq 2994 = (203295716762341:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 2994 = 203295716762341 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 2994 = (5497:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_2994
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 2995) ≤ val WuPaper.ClassicalFourthData.Bq 2995
    have hp : val WuPaper.ClassicalFourthData.Bq 2995 = (203329239471598:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 2995 = 203329239471598 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 2995 = (2199:ℝ)/800 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_2995
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 2996) ≤ val WuPaper.ClassicalFourthData.Bq 2996
    have hp : val WuPaper.ClassicalFourthData.Bq 2996 = (203362748649133:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 2996 = 203362748649133 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 2996 = (2749:ℝ)/1000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_2996
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 2997) ≤ val WuPaper.ClassicalFourthData.Bq 2997
    have hp : val WuPaper.ClassicalFourthData.Bq 2997 = (203396244300762:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 2997 = 203396244300762 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 2997 = (10997:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_2997
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 2998) ≤ val WuPaper.ClassicalFourthData.Bq 2998
    have hp : val WuPaper.ClassicalFourthData.Bq 2998 = (203429726432299:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 2998 = 203429726432299 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 2998 = (5499:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_2998
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 2999) ≤ val WuPaper.ClassicalFourthData.Bq 2999
    have hp : val WuPaper.ClassicalFourthData.Bq 2999 = (203463195049555:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 2999 = 203463195049555 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 2999 = (10999:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_2999
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 3000) ≤ val WuPaper.ClassicalFourthData.Bq 3000
    have hp : val WuPaper.ClassicalFourthData.Bq 3000 = (203496650158336:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 3000 = 203496650158336 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 3000 = (11:ℝ)/4 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_3000
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 3001) ≤ val WuPaper.ClassicalFourthData.Bq 3001
    have hp : val WuPaper.ClassicalFourthData.Bq 3001 = (203530091764447:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 3001 = 203530091764447 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 3001 = (11001:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_3001
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 3002) ≤ val WuPaper.ClassicalFourthData.Bq 3002
    have hp : val WuPaper.ClassicalFourthData.Bq 3002 = (203563519873690:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 3002 = 203563519873690 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 3002 = (5501:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_3002
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 3003) ≤ val WuPaper.ClassicalFourthData.Bq 3003
    have hp : val WuPaper.ClassicalFourthData.Bq 3003 = (203596934491863:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 3003 = 203596934491863 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 3003 = (11003:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_3003
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 3004) ≤ val WuPaper.ClassicalFourthData.Bq 3004
    have hp : val WuPaper.ClassicalFourthData.Bq 3004 = (203630335624761:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 3004 = 203630335624761 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 3004 = (2751:ℝ)/1000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_3004
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 3005) ≤ val WuPaper.ClassicalFourthData.Bq 3005
    have hp : val WuPaper.ClassicalFourthData.Bq 3005 = (203663723278176:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 3005 = 203663723278176 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 3005 = (2201:ℝ)/800 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_3005
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 3006) ≤ val WuPaper.ClassicalFourthData.Bq 3006
    have hp : val WuPaper.ClassicalFourthData.Bq 3006 = (203697097457898:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 3006 = 203697097457898 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 3006 = (5503:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_3006
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 3007) ≤ val WuPaper.ClassicalFourthData.Bq 3007
    have hp : val WuPaper.ClassicalFourthData.Bq 3007 = (203730458169713:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 3007 = 203730458169713 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 3007 = (11007:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_3007
end WuPaper.ClassicalFourthConditions
#print axioms WuPaper.ClassicalFourthConditions.Log_block_187

import WR2ClassicalFourthConditions
import WR2ClassicalFourthLogPoints437
noncomputable section
namespace WuPaper.ClassicalFourthConditions
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem Log_block_437 (j : Fin 16) (hj : 16*437+j.val < 10541) :
    WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 (16*437+j.val)) ≤ val WuPaper.ClassicalFourthData.Bq (16*437+j.val) := by
  fin_cases j
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 6992) ≤ val WuPaper.ClassicalFourthData.Bq 6992
    have hp : val WuPaper.ClassicalFourthData.Bq 6992 = (269710078537982:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 6992 = 269710078537982 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 6992 = (937:ℝ)/250 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_6992
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 6993) ≤ val WuPaper.ClassicalFourthData.Bq 6993
    have hp : val WuPaper.ClassicalFourthData.Bq 6993 = (269716359761780:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 6993 = 269716359761780 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 6993 = (14993:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_6993
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 6994) ≤ val WuPaper.ClassicalFourthData.Bq 6994
    have hp : val WuPaper.ClassicalFourthData.Bq 6994 = (269722637940198:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 6994 = 269722637940198 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 6994 = (7497:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_6994
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 6995) ≤ val WuPaper.ClassicalFourthData.Bq 6995
    have hp : val WuPaper.ClassicalFourthData.Bq 6995 = (269728913074249:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 6995 = 269728913074249 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 6995 = (2999:ℝ)/800 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_6995
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 6996) ≤ val WuPaper.ClassicalFourthData.Bq 6996
    have hp : val WuPaper.ClassicalFourthData.Bq 6996 = (269735185164941:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 6996 = 269735185164941 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 6996 = (3749:ℝ)/1000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_6996
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 6997) ≤ val WuPaper.ClassicalFourthData.Bq 6997
    have hp : val WuPaper.ClassicalFourthData.Bq 6997 = (269741454213286:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 6997 = 269741454213286 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 6997 = (14997:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_6997
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 6998) ≤ val WuPaper.ClassicalFourthData.Bq 6998
    have hp : val WuPaper.ClassicalFourthData.Bq 6998 = (269747720220293:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 6998 = 269747720220293 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 6998 = (7499:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_6998
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 6999) ≤ val WuPaper.ClassicalFourthData.Bq 6999
    have hp : val WuPaper.ClassicalFourthData.Bq 6999 = (269753983186972:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 6999 = 269753983186972 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 6999 = (14999:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_6999
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 7000) ≤ val WuPaper.ClassicalFourthData.Bq 7000
    have hp : val WuPaper.ClassicalFourthData.Bq 7000 = (269760243114330:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 7000 = 269760243114330 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 7000 = (15:ℝ)/4 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_7000
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 7001) ≤ val WuPaper.ClassicalFourthData.Bq 7001
    have hp : val WuPaper.ClassicalFourthData.Bq 7001 = (269766500003378:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 7001 = 269766500003378 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 7001 = (15001:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_7001
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 7002) ≤ val WuPaper.ClassicalFourthData.Bq 7002
    have hp : val WuPaper.ClassicalFourthData.Bq 7002 = (269772753855122:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 7002 = 269772753855122 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 7002 = (7501:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_7002
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 7003) ≤ val WuPaper.ClassicalFourthData.Bq 7003
    have hp : val WuPaper.ClassicalFourthData.Bq 7003 = (269779004670571:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 7003 = 269779004670571 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 7003 = (15003:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_7003
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 7004) ≤ val WuPaper.ClassicalFourthData.Bq 7004
    have hp : val WuPaper.ClassicalFourthData.Bq 7004 = (269785252450733:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 7004 = 269785252450733 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 7004 = (3751:ℝ)/1000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_7004
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 7005) ≤ val WuPaper.ClassicalFourthData.Bq 7005
    have hp : val WuPaper.ClassicalFourthData.Bq 7005 = (269791497196614:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 7005 = 269791497196614 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 7005 = (3001:ℝ)/800 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_7005
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 7006) ≤ val WuPaper.ClassicalFourthData.Bq 7006
    have hp : val WuPaper.ClassicalFourthData.Bq 7006 = (269797738909220:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 7006 = 269797738909220 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 7006 = (7503:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_7006
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 7007) ≤ val WuPaper.ClassicalFourthData.Bq 7007
    have hp : val WuPaper.ClassicalFourthData.Bq 7007 = (269803977589559:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 7007 = 269803977589559 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 7007 = (15007:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_7007
end WuPaper.ClassicalFourthConditions
#print axioms WuPaper.ClassicalFourthConditions.Log_block_437

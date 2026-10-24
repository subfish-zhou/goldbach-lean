import WR2ClassicalFourthConditions
import WR2ClassicalFourthLogPoints379
noncomputable section
namespace WuPaper.ClassicalFourthConditions
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem Log_block_379 (j : Fin 16) (hj : 16*379+j.val < 10541) :
    WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 (16*379+j.val)) ≤ val WuPaper.ClassicalFourthData.Bq (16*379+j.val) := by
  fin_cases j
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 6064) ≤ val WuPaper.ClassicalFourthData.Bq 6064
    have hp : val WuPaper.ClassicalFourthData.Bq 6064 = (262420460420425:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 6064 = 262420460420425 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 6064 = (879:ℝ)/250 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_6064
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 6065) ≤ val WuPaper.ClassicalFourthData.Bq 6065
    have hp : val WuPaper.ClassicalFourthData.Bq 6065 = (262430059856917:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 6065 = 262430059856917 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 6065 = (2813:ℝ)/800 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_6065
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 6066) ≤ val WuPaper.ClassicalFourthData.Bq 6066
    have hp : val WuPaper.ClassicalFourthData.Bq 6066 = (262439655121370:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 6066 = 262439655121370 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 6066 = (7033:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_6066
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 6067) ≤ val WuPaper.ClassicalFourthData.Bq 6067
    have hp : val WuPaper.ClassicalFourthData.Bq 6067 = (262449246215232:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 6067 = 262449246215232 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 6067 = (14067:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_6067
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 6068) ≤ val WuPaper.ClassicalFourthData.Bq 6068
    have hp : val WuPaper.ClassicalFourthData.Bq 6068 = (262458833139949:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 6068 = 262458833139949 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 6068 = (3517:ℝ)/1000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_6068
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 6069) ≤ val WuPaper.ClassicalFourthData.Bq 6069
    have hp : val WuPaper.ClassicalFourthData.Bq 6069 = (262468415896968:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 6069 = 262468415896968 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 6069 = (14069:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_6069
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 6070) ≤ val WuPaper.ClassicalFourthData.Bq 6070
    have hp : val WuPaper.ClassicalFourthData.Bq 6070 = (262477994487733:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 6070 = 262477994487733 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 6070 = (1407:ℝ)/400 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_6070
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 6071) ≤ val WuPaper.ClassicalFourthData.Bq 6071
    have hp : val WuPaper.ClassicalFourthData.Bq 6071 = (262487568913692:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 6071 = 262487568913692 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 6071 = (14071:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_6071
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 6072) ≤ val WuPaper.ClassicalFourthData.Bq 6072
    have hp : val WuPaper.ClassicalFourthData.Bq 6072 = (262497139176287:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 6072 = 262497139176287 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 6072 = (1759:ℝ)/500 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_6072
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 6073) ≤ val WuPaper.ClassicalFourthData.Bq 6073
    have hp : val WuPaper.ClassicalFourthData.Bq 6073 = (262506705276963:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 6073 = 262506705276963 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 6073 = (14073:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_6073
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 6074) ≤ val WuPaper.ClassicalFourthData.Bq 6074
    have hp : val WuPaper.ClassicalFourthData.Bq 6074 = (262516267217164:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 6074 = 262516267217164 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 6074 = (7037:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_6074
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 6075) ≤ val WuPaper.ClassicalFourthData.Bq 6075
    have hp : val WuPaper.ClassicalFourthData.Bq 6075 = (262525824998331:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 6075 = 262525824998331 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 6075 = (563:ℝ)/160 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_6075
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 6076) ≤ val WuPaper.ClassicalFourthData.Bq 6076
    have hp : val WuPaper.ClassicalFourthData.Bq 6076 = (262535378621908:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 6076 = 262535378621908 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 6076 = (3519:ℝ)/1000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_6076
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 6077) ≤ val WuPaper.ClassicalFourthData.Bq 6077
    have hp : val WuPaper.ClassicalFourthData.Bq 6077 = (262544928089336:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 6077 = 262544928089336 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 6077 = (14077:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_6077
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 6078) ≤ val WuPaper.ClassicalFourthData.Bq 6078
    have hp : val WuPaper.ClassicalFourthData.Bq 6078 = (262554473402057:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 6078 = 262554473402057 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 6078 = (7039:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_6078
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 6079) ≤ val WuPaper.ClassicalFourthData.Bq 6079
    have hp : val WuPaper.ClassicalFourthData.Bq 6079 = (262564014561509:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 6079 = 262564014561509 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 6079 = (14079:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_6079
end WuPaper.ClassicalFourthConditions
#print axioms WuPaper.ClassicalFourthConditions.Log_block_379

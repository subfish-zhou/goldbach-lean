import WR2ClassicalFourthConditions
import WR2ClassicalFourthLogPoints489
noncomputable section
namespace WuPaper.ClassicalFourthConditions
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem Log_block_489 (j : Fin 16) (hj : 16*489+j.val < 10541) :
    WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 (16*489+j.val)) ≤ val WuPaper.ClassicalFourthData.Bq (16*489+j.val) := by
  fin_cases j
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 7824) ≤ val WuPaper.ClassicalFourthData.Bq 7824
    have hp : val WuPaper.ClassicalFourthData.Bq 7824 = (273972953257763:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 7824 = 273972953257763 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 7824 = (989:ℝ)/250 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_7824
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 7825) ≤ val WuPaper.ClassicalFourthData.Bq 7825
    have hp : val WuPaper.ClassicalFourthData.Bq 7825 = (273977016937722:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 7825 = 273977016937722 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 7825 = (633:ℝ)/160 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_7825
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 7826) ≤ val WuPaper.ClassicalFourthData.Bq 7826
    have hp : val WuPaper.ClassicalFourthData.Bq 7826 = (273981078296603:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 7826 = 273981078296603 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 7826 = (7913:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_7826
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 7827) ≤ val WuPaper.ClassicalFourthData.Bq 7827
    have hp : val WuPaper.ClassicalFourthData.Bq 7827 = (273985137335150:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 7827 = 273985137335150 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 7827 = (15827:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_7827
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 7828) ≤ val WuPaper.ClassicalFourthData.Bq 7828
    have hp : val WuPaper.ClassicalFourthData.Bq 7828 = (273989194054109:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 7828 = 273989194054109 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 7828 = (3957:ℝ)/1000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_7828
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 7829) ≤ val WuPaper.ClassicalFourthData.Bq 7829
    have hp : val WuPaper.ClassicalFourthData.Bq 7829 = (273993248454225:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 7829 = 273993248454225 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 7829 = (15829:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_7829
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 7830) ≤ val WuPaper.ClassicalFourthData.Bq 7830
    have hp : val WuPaper.ClassicalFourthData.Bq 7830 = (273997300536243:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 7830 = 273997300536243 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 7830 = (1583:ℝ)/400 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_7830
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 7831) ≤ val WuPaper.ClassicalFourthData.Bq 7831
    have hp : val WuPaper.ClassicalFourthData.Bq 7831 = (274001350300907:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 7831 = 274001350300907 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 7831 = (15831:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_7831
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 7832) ≤ val WuPaper.ClassicalFourthData.Bq 7832
    have hp : val WuPaper.ClassicalFourthData.Bq 7832 = (274005397748962:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 7832 = 274005397748962 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 7832 = (1979:ℝ)/500 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_7832
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 7833) ≤ val WuPaper.ClassicalFourthData.Bq 7833
    have hp : val WuPaper.ClassicalFourthData.Bq 7833 = (274009442881152:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 7833 = 274009442881152 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 7833 = (15833:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_7833
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 7834) ≤ val WuPaper.ClassicalFourthData.Bq 7834
    have hp : val WuPaper.ClassicalFourthData.Bq 7834 = (274013485698220:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 7834 = 274013485698220 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 7834 = (7917:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_7834
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 7835) ≤ val WuPaper.ClassicalFourthData.Bq 7835
    have hp : val WuPaper.ClassicalFourthData.Bq 7835 = (274017526200910:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 7835 = 274017526200910 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 7835 = (3167:ℝ)/800 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_7835
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 7836) ≤ val WuPaper.ClassicalFourthData.Bq 7836
    have hp : val WuPaper.ClassicalFourthData.Bq 7836 = (274021564389965:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 7836 = 274021564389965 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 7836 = (3959:ℝ)/1000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_7836
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 7837) ≤ val WuPaper.ClassicalFourthData.Bq 7837
    have hp : val WuPaper.ClassicalFourthData.Bq 7837 = (274025600266129:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 7837 = 274025600266129 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 7837 = (15837:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_7837
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 7838) ≤ val WuPaper.ClassicalFourthData.Bq 7838
    have hp : val WuPaper.ClassicalFourthData.Bq 7838 = (274029633830143:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 7838 = 274029633830143 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 7838 = (7919:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_7838
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 7839) ≤ val WuPaper.ClassicalFourthData.Bq 7839
    have hp : val WuPaper.ClassicalFourthData.Bq 7839 = (274033665082750:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 7839 = 274033665082750 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 7839 = (15839:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_7839
end WuPaper.ClassicalFourthConditions
#print axioms WuPaper.ClassicalFourthConditions.Log_block_489

import WR2ClassicalFourthConditions
import WR2ClassicalFourthLogPoints427
noncomputable section
namespace WuPaper.ClassicalFourthConditions
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem Log_block_427 (j : Fin 16) (hj : 16*427+j.val < 10541) :
    WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 (16*427+j.val)) ≤ val WuPaper.ClassicalFourthData.Bq (16*427+j.val) := by
  fin_cases j
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 6832) ≤ val WuPaper.ClassicalFourthData.Bq 6832
    have hp : val WuPaper.ClassicalFourthData.Bq 6832 = (268665144296170:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 6832 = 268665144296170 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 6832 = (927:ℝ)/250 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_6832
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 6833) ≤ val WuPaper.ClassicalFourthData.Bq 6833
    have hp : val WuPaper.ClassicalFourthData.Bq 6833 = (268671926068552:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 6833 = 268671926068552 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 6833 = (14833:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_6833
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 6834) ≤ val WuPaper.ClassicalFourthData.Bq 6834
    have hp : val WuPaper.ClassicalFourthData.Bq 6834 = (268678704628822:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 6834 = 268678704628822 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 6834 = (7417:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_6834
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 6835) ≤ val WuPaper.ClassicalFourthData.Bq 6835
    have hp : val WuPaper.ClassicalFourthData.Bq 6835 = (268685479978053:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 6835 = 268685479978053 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 6835 = (2967:ℝ)/800 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_6835
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 6836) ≤ val WuPaper.ClassicalFourthData.Bq 6836
    have hp : val WuPaper.ClassicalFourthData.Bq 6836 = (268692252117317:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 6836 = 268692252117317 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 6836 = (3709:ℝ)/1000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_6836
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 6837) ≤ val WuPaper.ClassicalFourthData.Bq 6837
    have hp : val WuPaper.ClassicalFourthData.Bq 6837 = (268699021047689:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 6837 = 268699021047689 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 6837 = (14837:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_6837
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 6838) ≤ val WuPaper.ClassicalFourthData.Bq 6838
    have hp : val WuPaper.ClassicalFourthData.Bq 6838 = (268705786770240:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 6838 = 268705786770240 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 6838 = (7419:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_6838
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 6839) ≤ val WuPaper.ClassicalFourthData.Bq 6839
    have hp : val WuPaper.ClassicalFourthData.Bq 6839 = (268712549286042:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 6839 = 268712549286042 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 6839 = (14839:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_6839
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 6840) ≤ val WuPaper.ClassicalFourthData.Bq 6840
    have hp : val WuPaper.ClassicalFourthData.Bq 6840 = (268719308596168:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 6840 = 268719308596168 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 6840 = (371:ℝ)/100 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_6840
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 6841) ≤ val WuPaper.ClassicalFourthData.Bq 6841
    have hp : val WuPaper.ClassicalFourthData.Bq 6841 = (268726064701688:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 6841 = 268726064701688 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 6841 = (14841:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_6841
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 6842) ≤ val WuPaper.ClassicalFourthData.Bq 6842
    have hp : val WuPaper.ClassicalFourthData.Bq 6842 = (268732817603673:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 6842 = 268732817603673 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 6842 = (7421:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_6842
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 6843) ≤ val WuPaper.ClassicalFourthData.Bq 6843
    have hp : val WuPaper.ClassicalFourthData.Bq 6843 = (268739567303194:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 6843 = 268739567303194 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 6843 = (14843:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_6843
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 6844) ≤ val WuPaper.ClassicalFourthData.Bq 6844
    have hp : val WuPaper.ClassicalFourthData.Bq 6844 = (268746313801321:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 6844 = 268746313801321 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 6844 = (3711:ℝ)/1000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_6844
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 6845) ≤ val WuPaper.ClassicalFourthData.Bq 6845
    have hp : val WuPaper.ClassicalFourthData.Bq 6845 = (268753057099124:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 6845 = 268753057099124 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 6845 = (2969:ℝ)/800 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_6845
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 6846) ≤ val WuPaper.ClassicalFourthData.Bq 6846
    have hp : val WuPaper.ClassicalFourthData.Bq 6846 = (268759797197670:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 6846 = 268759797197670 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 6846 = (7423:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_6846
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 6847) ≤ val WuPaper.ClassicalFourthData.Bq 6847
    have hp : val WuPaper.ClassicalFourthData.Bq 6847 = (268766534098031:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 6847 = 268766534098031 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 6847 = (14847:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_6847
end WuPaper.ClassicalFourthConditions
#print axioms WuPaper.ClassicalFourthConditions.Log_block_427

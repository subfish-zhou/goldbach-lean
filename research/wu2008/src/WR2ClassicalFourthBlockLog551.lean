import WR2ClassicalFourthConditions
import WR2ClassicalFourthLogPoints551
noncomputable section
namespace WuPaper.ClassicalFourthConditions
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem Log_block_551 (j : Fin 16) (hj : 16*551+j.val < 10541) :
    WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 (16*551+j.val)) ≤ val WuPaper.ClassicalFourthData.Bq (16*551+j.val) := by
  fin_cases j
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 8816) ≤ val WuPaper.ClassicalFourthData.Bq 8816
    have hp : val WuPaper.ClassicalFourthData.Bq 8816 = (276974317131034:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 8816 = 276974317131034 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 8816 = (1051:ℝ)/250 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_8816
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 8817) ≤ val WuPaper.ClassicalFourthData.Bq 8817
    have hp : val WuPaper.ClassicalFourthData.Bq 8817 = (276976405694375:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 8817 = 276976405694375 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 8817 = (16817:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_8817
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 8818) ≤ val WuPaper.ClassicalFourthData.Bq 8818
    have hp : val WuPaper.ClassicalFourthData.Bq 8818 = (276978492561528:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 8818 = 276978492561528 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 8818 = (8409:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_8818
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 8819) ≤ val WuPaper.ClassicalFourthData.Bq 8819
    have hp : val WuPaper.ClassicalFourthData.Bq 8819 = (276980577733024:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 8819 = 276980577733024 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 8819 = (16819:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_8819
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 8820) ≤ val WuPaper.ClassicalFourthData.Bq 8820
    have hp : val WuPaper.ClassicalFourthData.Bq 8820 = (276982661209389:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 8820 = 276982661209389 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 8820 = (841:ℝ)/200 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_8820
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 8821) ≤ val WuPaper.ClassicalFourthData.Bq 8821
    have hp : val WuPaper.ClassicalFourthData.Bq 8821 = (276984742991153:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 8821 = 276984742991153 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 8821 = (16821:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_8821
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 8822) ≤ val WuPaper.ClassicalFourthData.Bq 8822
    have hp : val WuPaper.ClassicalFourthData.Bq 8822 = (276986823078842:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 8822 = 276986823078842 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 8822 = (8411:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_8822
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 8823) ≤ val WuPaper.ClassicalFourthData.Bq 8823
    have hp : val WuPaper.ClassicalFourthData.Bq 8823 = (276988901472985:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 8823 = 276988901472985 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 8823 = (16823:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_8823
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 8824) ≤ val WuPaper.ClassicalFourthData.Bq 8824
    have hp : val WuPaper.ClassicalFourthData.Bq 8824 = (276990978174110:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 8824 = 276990978174110 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 8824 = (2103:ℝ)/500 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_8824
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 8825) ≤ val WuPaper.ClassicalFourthData.Bq 8825
    have hp : val WuPaper.ClassicalFourthData.Bq 8825 = (276993053182742:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 8825 = 276993053182742 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 8825 = (673:ℝ)/160 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_8825
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 8826) ≤ val WuPaper.ClassicalFourthData.Bq 8826
    have hp : val WuPaper.ClassicalFourthData.Bq 8826 = (276995126499411:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 8826 = 276995126499411 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 8826 = (8413:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_8826
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 8827) ≤ val WuPaper.ClassicalFourthData.Bq 8827
    have hp : val WuPaper.ClassicalFourthData.Bq 8827 = (276997198124642:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 8827 = 276997198124642 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 8827 = (16827:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_8827
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 8828) ≤ val WuPaper.ClassicalFourthData.Bq 8828
    have hp : val WuPaper.ClassicalFourthData.Bq 8828 = (276999268058963:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 8828 = 276999268058963 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 8828 = (4207:ℝ)/1000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_8828
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 8829) ≤ val WuPaper.ClassicalFourthData.Bq 8829
    have hp : val WuPaper.ClassicalFourthData.Bq 8829 = (277001336302900:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 8829 = 277001336302900 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 8829 = (16829:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_8829
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 8830) ≤ val WuPaper.ClassicalFourthData.Bq 8830
    have hp : val WuPaper.ClassicalFourthData.Bq 8830 = (277003402856980:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 8830 = 277003402856980 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 8830 = (1683:ℝ)/400 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_8830
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 8831) ≤ val WuPaper.ClassicalFourthData.Bq 8831
    have hp : val WuPaper.ClassicalFourthData.Bq 8831 = (277005467721728:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 8831 = 277005467721728 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 8831 = (16831:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_8831
end WuPaper.ClassicalFourthConditions
#print axioms WuPaper.ClassicalFourthConditions.Log_block_551

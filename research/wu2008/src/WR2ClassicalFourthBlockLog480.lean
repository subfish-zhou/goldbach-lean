import WR2ClassicalFourthConditions
import WR2ClassicalFourthLogPoints480
noncomputable section
namespace WuPaper.ClassicalFourthConditions
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem Log_block_480 (j : Fin 16) (hj : 16*480+j.val < 10541) :
    WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 (16*480+j.val)) ≤ val WuPaper.ClassicalFourthData.Bq (16*480+j.val) := by
  fin_cases j
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 7680) ≤ val WuPaper.ClassicalFourthData.Bq 7680
    have hp : val WuPaper.ClassicalFourthData.Bq 7680 = (273363167418742:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 7680 = 273363167418742 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 7680 = (98:ℝ)/25 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_7680
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 7681) ≤ val WuPaper.ClassicalFourthData.Bq 7681
    have hp : val WuPaper.ClassicalFourthData.Bq 7681 = (273367573255520:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 7681 = 273367573255520 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 7681 = (15681:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_7681
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 7682) ≤ val WuPaper.ClassicalFourthData.Bq 7682
    have hp : val WuPaper.ClassicalFourthData.Bq 7682 = (273371976661016:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 7682 = 273371976661016 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 7682 = (7841:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_7682
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 7683) ≤ val WuPaper.ClassicalFourthData.Bq 7683
    have hp : val WuPaper.ClassicalFourthData.Bq 7683 = (273376377636016:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 7683 = 273376377636016 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 7683 = (15683:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_7683
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 7684) ≤ val WuPaper.ClassicalFourthData.Bq 7684
    have hp : val WuPaper.ClassicalFourthData.Bq 7684 = (273380776181304:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 7684 = 273380776181304 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 7684 = (3921:ℝ)/1000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_7684
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 7685) ≤ val WuPaper.ClassicalFourthData.Bq 7685
    have hp : val WuPaper.ClassicalFourthData.Bq 7685 = (273385172297666:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 7685 = 273385172297666 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 7685 = (3137:ℝ)/800 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_7685
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 7686) ≤ val WuPaper.ClassicalFourthData.Bq 7686
    have hp : val WuPaper.ClassicalFourthData.Bq 7686 = (273389565985886:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 7686 = 273389565985886 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 7686 = (7843:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_7686
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 7687) ≤ val WuPaper.ClassicalFourthData.Bq 7687
    have hp : val WuPaper.ClassicalFourthData.Bq 7687 = (273393957246747:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 7687 = 273393957246747 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 7687 = (15687:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_7687
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 7688) ≤ val WuPaper.ClassicalFourthData.Bq 7688
    have hp : val WuPaper.ClassicalFourthData.Bq 7688 = (273398346081033:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 7688 = 273398346081033 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 7688 = (1961:ℝ)/500 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_7688
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 7689) ≤ val WuPaper.ClassicalFourthData.Bq 7689
    have hp : val WuPaper.ClassicalFourthData.Bq 7689 = (273402732489527:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 7689 = 273402732489527 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 7689 = (15689:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_7689
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 7690) ≤ val WuPaper.ClassicalFourthData.Bq 7690
    have hp : val WuPaper.ClassicalFourthData.Bq 7690 = (273407116473013:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 7690 = 273407116473013 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 7690 = (1569:ℝ)/400 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_7690
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 7691) ≤ val WuPaper.ClassicalFourthData.Bq 7691
    have hp : val WuPaper.ClassicalFourthData.Bq 7691 = (273411498032274:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 7691 = 273411498032274 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 7691 = (15691:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_7691
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 7692) ≤ val WuPaper.ClassicalFourthData.Bq 7692
    have hp : val WuPaper.ClassicalFourthData.Bq 7692 = (273415877168091:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 7692 = 273415877168091 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 7692 = (3923:ℝ)/1000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_7692
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 7693) ≤ val WuPaper.ClassicalFourthData.Bq 7693
    have hp : val WuPaper.ClassicalFourthData.Bq 7693 = (273420253881248:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 7693 = 273420253881248 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 7693 = (15693:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_7693
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 7694) ≤ val WuPaper.ClassicalFourthData.Bq 7694
    have hp : val WuPaper.ClassicalFourthData.Bq 7694 = (273424628172526:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 7694 = 273424628172526 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 7694 = (7847:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_7694
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 7695) ≤ val WuPaper.ClassicalFourthData.Bq 7695
    have hp : val WuPaper.ClassicalFourthData.Bq 7695 = (273429000042708:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 7695 = 273429000042708 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 7695 = (3139:ℝ)/800 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_7695
end WuPaper.ClassicalFourthConditions
#print axioms WuPaper.ClassicalFourthConditions.Log_block_480

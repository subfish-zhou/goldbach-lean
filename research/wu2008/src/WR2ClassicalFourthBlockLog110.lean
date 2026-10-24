import WR2ClassicalFourthConditions
import WR2ClassicalFourthLogPoints110
noncomputable section
namespace WuPaper.ClassicalFourthConditions
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem Log_block_110 (j : Fin 16) (hj : 16*110+j.val < 10541) :
    WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 (16*110+j.val)) ≤ val WuPaper.ClassicalFourthData.Bq (16*110+j.val) := by
  fin_cases j
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 1760) ≤ val WuPaper.ClassicalFourthData.Bq 1760
    have hp : val WuPaper.ClassicalFourthData.Bq 1760 = (149443899011439:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 1760 = 149443899011439 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 1760 = (61:ℝ)/25 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_1760
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 1761) ≤ val WuPaper.ClassicalFourthData.Bq 1761
    have hp : val WuPaper.ClassicalFourthData.Bq 1761 = (149499727335460:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 1761 = 149499727335460 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 1761 = (9761:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_1761
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 1762) ≤ val WuPaper.ClassicalFourthData.Bq 1762
    have hp : val WuPaper.ClassicalFourthData.Bq 1762 = (149555531875619:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 1762 = 149555531875619 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 1762 = (4881:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_1762
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 1763) ≤ val WuPaper.ClassicalFourthData.Bq 1763
    have hp : val WuPaper.ClassicalFourthData.Bq 1763 = (149611312643507:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 1763 = 149611312643507 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 1763 = (9763:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_1763
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 1764) ≤ val WuPaper.ClassicalFourthData.Bq 1764
    have hp : val WuPaper.ClassicalFourthData.Bq 1764 = (149667069650711:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 1764 = 149667069650711 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 1764 = (2441:ℝ)/1000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_1764
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 1765) ≤ val WuPaper.ClassicalFourthData.Bq 1765
    have hp : val WuPaper.ClassicalFourthData.Bq 1765 = (149722802908810:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 1765 = 149722802908810 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 1765 = (1953:ℝ)/800 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_1765
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 1766) ≤ val WuPaper.ClassicalFourthData.Bq 1766
    have hp : val WuPaper.ClassicalFourthData.Bq 1766 = (149778512429376:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 1766 = 149778512429376 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 1766 = (4883:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_1766
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 1767) ≤ val WuPaper.ClassicalFourthData.Bq 1767
    have hp : val WuPaper.ClassicalFourthData.Bq 1767 = (149834198223973:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 1767 = 149834198223973 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 1767 = (9767:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_1767
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 1768) ≤ val WuPaper.ClassicalFourthData.Bq 1768
    have hp : val WuPaper.ClassicalFourthData.Bq 1768 = (149889860304160:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 1768 = 149889860304160 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 1768 = (1221:ℝ)/500 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_1768
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 1769) ≤ val WuPaper.ClassicalFourthData.Bq 1769
    have hp : val WuPaper.ClassicalFourthData.Bq 1769 = (149945498681488:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 1769 = 149945498681488 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 1769 = (9769:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_1769
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 1770) ≤ val WuPaper.ClassicalFourthData.Bq 1770
    have hp : val WuPaper.ClassicalFourthData.Bq 1770 = (150001113367500:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 1770 = 150001113367500 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 1770 = (977:ℝ)/400 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_1770
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 1771) ≤ val WuPaper.ClassicalFourthData.Bq 1771
    have hp : val WuPaper.ClassicalFourthData.Bq 1771 = (150056704373735:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 1771 = 150056704373735 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 1771 = (9771:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_1771
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 1772) ≤ val WuPaper.ClassicalFourthData.Bq 1772
    have hp : val WuPaper.ClassicalFourthData.Bq 1772 = (150112271711721:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 1772 = 150112271711721 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 1772 = (2443:ℝ)/1000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_1772
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 1773) ≤ val WuPaper.ClassicalFourthData.Bq 1773
    have hp : val WuPaper.ClassicalFourthData.Bq 1773 = (150167815392984:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 1773 = 150167815392984 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 1773 = (9773:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_1773
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 1774) ≤ val WuPaper.ClassicalFourthData.Bq 1774
    have hp : val WuPaper.ClassicalFourthData.Bq 1774 = (150223335429038:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 1774 = 150223335429038 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 1774 = (4887:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_1774
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 1775) ≤ val WuPaper.ClassicalFourthData.Bq 1775
    have hp : val WuPaper.ClassicalFourthData.Bq 1775 = (150278831831393:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 1775 = 150278831831393 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 1775 = (391:ℝ)/160 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_1775
end WuPaper.ClassicalFourthConditions
#print axioms WuPaper.ClassicalFourthConditions.Log_block_110

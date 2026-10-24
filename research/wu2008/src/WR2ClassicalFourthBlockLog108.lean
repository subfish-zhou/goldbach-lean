import WR2ClassicalFourthConditions
import WR2ClassicalFourthLogPoints108
noncomputable section
namespace WuPaper.ClassicalFourthConditions
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem Log_block_108 (j : Fin 16) (hj : 16*108+j.val < 10541) :
    WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 (16*108+j.val)) ≤ val WuPaper.ClassicalFourthData.Bq (16*108+j.val) := by
  fin_cases j
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 1728) ≤ val WuPaper.ClassicalFourthData.Bq 1728
    have hp : val WuPaper.ClassicalFourthData.Bq 1728 = (147644765024036:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 1728 = 147644765024036 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 1728 = (304:ℝ)/125 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_1728
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 1729) ≤ val WuPaper.ClassicalFourthData.Bq 1729
    have hp : val WuPaper.ClassicalFourthData.Bq 1729 = (147701360594738:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 1729 = 147701360594738 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 1729 = (9729:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_1729
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 1730) ≤ val WuPaper.ClassicalFourthData.Bq 1730
    have hp : val WuPaper.ClassicalFourthData.Bq 1730 = (147757932006890:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 1730 = 147757932006890 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 1730 = (973:ℝ)/400 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_1730
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 1731) ≤ val WuPaper.ClassicalFourthData.Bq 1731
    have hp : val WuPaper.ClassicalFourthData.Bq 1731 = (147814479272310:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 1731 = 147814479272310 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 1731 = (9731:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_1731
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 1732) ≤ val WuPaper.ClassicalFourthData.Bq 1732
    have hp : val WuPaper.ClassicalFourthData.Bq 1732 = (147871002402810:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 1732 = 147871002402810 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 1732 = (2433:ℝ)/1000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_1732
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 1733) ≤ val WuPaper.ClassicalFourthData.Bq 1733
    have hp : val WuPaper.ClassicalFourthData.Bq 1733 = (147927501410195:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 1733 = 147927501410195 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 1733 = (9733:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_1733
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 1734) ≤ val WuPaper.ClassicalFourthData.Bq 1734
    have hp : val WuPaper.ClassicalFourthData.Bq 1734 = (147983976306262:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 1734 = 147983976306262 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 1734 = (4867:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_1734
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 1735) ≤ val WuPaper.ClassicalFourthData.Bq 1735
    have hp : val WuPaper.ClassicalFourthData.Bq 1735 = (148040427102802:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 1735 = 148040427102802 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 1735 = (1947:ℝ)/800 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_1735
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 1736) ≤ val WuPaper.ClassicalFourthData.Bq 1736
    have hp : val WuPaper.ClassicalFourthData.Bq 1736 = (148096853811598:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 1736 = 148096853811598 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 1736 = (1217:ℝ)/500 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_1736
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 1737) ≤ val WuPaper.ClassicalFourthData.Bq 1737
    have hp : val WuPaper.ClassicalFourthData.Bq 1737 = (148153256444426:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 1737 = 148153256444426 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 1737 = (9737:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_1737
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 1738) ≤ val WuPaper.ClassicalFourthData.Bq 1738
    have hp : val WuPaper.ClassicalFourthData.Bq 1738 = (148209635013056:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 1738 = 148209635013056 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 1738 = (4869:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_1738
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 1739) ≤ val WuPaper.ClassicalFourthData.Bq 1739
    have hp : val WuPaper.ClassicalFourthData.Bq 1739 = (148265989529248:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 1739 = 148265989529248 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 1739 = (9739:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_1739
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 1740) ≤ val WuPaper.ClassicalFourthData.Bq 1740
    have hp : val WuPaper.ClassicalFourthData.Bq 1740 = (148322320004758:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 1740 = 148322320004758 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 1740 = (487:ℝ)/200 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_1740
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 1741) ≤ val WuPaper.ClassicalFourthData.Bq 1741
    have hp : val WuPaper.ClassicalFourthData.Bq 1741 = (148378626451334:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 1741 = 148378626451334 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 1741 = (9741:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_1741
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 1742) ≤ val WuPaper.ClassicalFourthData.Bq 1742
    have hp : val WuPaper.ClassicalFourthData.Bq 1742 = (148434908880716:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 1742 = 148434908880716 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 1742 = (4871:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_1742
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 1743) ≤ val WuPaper.ClassicalFourthData.Bq 1743
    have hp : val WuPaper.ClassicalFourthData.Bq 1743 = (148491167304637:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 1743 = 148491167304637 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 1743 = (9743:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_1743
end WuPaper.ClassicalFourthConditions
#print axioms WuPaper.ClassicalFourthConditions.Log_block_108

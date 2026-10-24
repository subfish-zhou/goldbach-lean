import WR2ClassicalFourthConditions
import WR2ClassicalFourthLogPoints107
noncomputable section
namespace WuPaper.ClassicalFourthConditions
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem Log_block_107 (j : Fin 16) (hj : 16*107+j.val < 10541) :
    WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 (16*107+j.val)) ≤ val WuPaper.ClassicalFourthData.Bq (16*107+j.val) := by
  fin_cases j
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 1712) ≤ val WuPaper.ClassicalFourthData.Bq 1712
    have hp : val WuPaper.ClassicalFourthData.Bq 1712 = (146735940657905:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 1712 = 146735940657905 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 1712 = (607:ℝ)/250 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_1712
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 1713) ≤ val WuPaper.ClassicalFourthData.Bq 1713
    have hp : val WuPaper.ClassicalFourthData.Bq 1713 = (146792924378641:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 1713 = 146792924378641 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 1713 = (9713:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_1713
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 1714) ≤ val WuPaper.ClassicalFourthData.Bq 1714
    have hp : val WuPaper.ClassicalFourthData.Bq 1714 = (146849883750748:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 1714 = 146849883750748 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 1714 = (4857:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_1714
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 1715) ≤ val WuPaper.ClassicalFourthData.Bq 1715
    have hp : val WuPaper.ClassicalFourthData.Bq 1715 = (146906818786159:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 1715 = 146906818786159 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 1715 = (1943:ℝ)/800 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_1715
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 1716) ≤ val WuPaper.ClassicalFourthData.Bq 1716
    have hp : val WuPaper.ClassicalFourthData.Bq 1716 = (146963729496802:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 1716 = 146963729496802 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 1716 = (2429:ℝ)/1000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_1716
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 1717) ≤ val WuPaper.ClassicalFourthData.Bq 1717
    have hp : val WuPaper.ClassicalFourthData.Bq 1717 = (147020615894595:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 1717 = 147020615894595 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 1717 = (9717:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_1717
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 1718) ≤ val WuPaper.ClassicalFourthData.Bq 1718
    have hp : val WuPaper.ClassicalFourthData.Bq 1718 = (147077477991451:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 1718 = 147077477991451 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 1718 = (4859:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_1718
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 1719) ≤ val WuPaper.ClassicalFourthData.Bq 1719
    have hp : val WuPaper.ClassicalFourthData.Bq 1719 = (147134315799276:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 1719 = 147134315799276 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 1719 = (9719:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_1719
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 1720) ≤ val WuPaper.ClassicalFourthData.Bq 1720
    have hp : val WuPaper.ClassicalFourthData.Bq 1720 = (147191129329966:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 1720 = 147191129329966 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 1720 = (243:ℝ)/100 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_1720
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 1721) ≤ val WuPaper.ClassicalFourthData.Bq 1721
    have hp : val WuPaper.ClassicalFourthData.Bq 1721 = (147247918595413:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 1721 = 147247918595413 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 1721 = (9721:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_1721
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 1722) ≤ val WuPaper.ClassicalFourthData.Bq 1722
    have hp : val WuPaper.ClassicalFourthData.Bq 1722 = (147304683607500:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 1722 = 147304683607500 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 1722 = (4861:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_1722
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 1723) ≤ val WuPaper.ClassicalFourthData.Bq 1723
    have hp : val WuPaper.ClassicalFourthData.Bq 1723 = (147361424378104:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 1723 = 147361424378104 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 1723 = (9723:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_1723
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 1724) ≤ val WuPaper.ClassicalFourthData.Bq 1724
    have hp : val WuPaper.ClassicalFourthData.Bq 1724 = (147418140919093:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 1724 = 147418140919093 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 1724 = (2431:ℝ)/1000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_1724
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 1725) ≤ val WuPaper.ClassicalFourthData.Bq 1725
    have hp : val WuPaper.ClassicalFourthData.Bq 1725 = (147474833242330:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 1725 = 147474833242330 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 1725 = (389:ℝ)/160 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_1725
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 1726) ≤ val WuPaper.ClassicalFourthData.Bq 1726
    have hp : val WuPaper.ClassicalFourthData.Bq 1726 = (147531501359668:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 1726 = 147531501359668 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 1726 = (4863:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_1726
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 1727) ≤ val WuPaper.ClassicalFourthData.Bq 1727
    have hp : val WuPaper.ClassicalFourthData.Bq 1727 = (147588145282957:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 1727 = 147588145282957 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 1727 = (9727:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_1727
end WuPaper.ClassicalFourthConditions
#print axioms WuPaper.ClassicalFourthConditions.Log_block_107

import WR2ClassicalFourthConditions
import WR2ClassicalFourthLogPoints360
noncomputable section
namespace WuPaper.ClassicalFourthConditions
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem Log_block_360 (j : Fin 16) (hj : 16*360+j.val < 10541) :
    WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 (16*360+j.val)) ≤ val WuPaper.ClassicalFourthData.Bq (16*360+j.val) := by
  fin_cases j
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 5760) ≤ val WuPaper.ClassicalFourthData.Bq 5760
    have hp : val WuPaper.ClassicalFourthData.Bq 5760 = (259301755611953:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 5760 = 259301755611953 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 5760 = (86:ℝ)/25 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_5760
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 5761) ≤ val WuPaper.ClassicalFourthData.Bq 5761
    have hp : val WuPaper.ClassicalFourthData.Bq 5761 = (259312693284775:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 5761 = 259312693284775 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 5761 = (13761:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_5761
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 5762) ≤ val WuPaper.ClassicalFourthData.Bq 5762
    have hp : val WuPaper.ClassicalFourthData.Bq 5762 = (259323626317417:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 5762 = 259323626317417 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 5762 = (6881:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_5762
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 5763) ≤ val WuPaper.ClassicalFourthData.Bq 5763
    have hp : val WuPaper.ClassicalFourthData.Bq 5763 = (259334554711517:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 5763 = 259334554711517 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 5763 = (13763:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_5763
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 5764) ≤ val WuPaper.ClassicalFourthData.Bq 5764
    have hp : val WuPaper.ClassicalFourthData.Bq 5764 = (259345478468710:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 5764 = 259345478468710 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 5764 = (3441:ℝ)/1000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_5764
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 5765) ≤ val WuPaper.ClassicalFourthData.Bq 5765
    have hp : val WuPaper.ClassicalFourthData.Bq 5765 = (259356397590632:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 5765 = 259356397590632 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 5765 = (2753:ℝ)/800 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_5765
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 5766) ≤ val WuPaper.ClassicalFourthData.Bq 5766
    have hp : val WuPaper.ClassicalFourthData.Bq 5766 = (259367312078915:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 5766 = 259367312078915 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 5766 = (6883:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_5766
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 5767) ≤ val WuPaper.ClassicalFourthData.Bq 5767
    have hp : val WuPaper.ClassicalFourthData.Bq 5767 = (259378221935195:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 5767 = 259378221935195 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 5767 = (13767:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_5767
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 5768) ≤ val WuPaper.ClassicalFourthData.Bq 5768
    have hp : val WuPaper.ClassicalFourthData.Bq 5768 = (259389127161105:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 5768 = 259389127161105 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 5768 = (1721:ℝ)/500 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_5768
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 5769) ≤ val WuPaper.ClassicalFourthData.Bq 5769
    have hp : val WuPaper.ClassicalFourthData.Bq 5769 = (259400027758276:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 5769 = 259400027758276 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 5769 = (13769:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_5769
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 5770) ≤ val WuPaper.ClassicalFourthData.Bq 5770
    have hp : val WuPaper.ClassicalFourthData.Bq 5770 = (259410923728340:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 5770 = 259410923728340 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 5770 = (1377:ℝ)/400 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_5770
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 5771) ≤ val WuPaper.ClassicalFourthData.Bq 5771
    have hp : val WuPaper.ClassicalFourthData.Bq 5771 = (259421815072929:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 5771 = 259421815072929 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 5771 = (13771:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_5771
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 5772) ≤ val WuPaper.ClassicalFourthData.Bq 5772
    have hp : val WuPaper.ClassicalFourthData.Bq 5772 = (259432701793672:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 5772 = 259432701793672 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 5772 = (3443:ℝ)/1000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_5772
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 5773) ≤ val WuPaper.ClassicalFourthData.Bq 5773
    have hp : val WuPaper.ClassicalFourthData.Bq 5773 = (259443583892200:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 5773 = 259443583892200 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 5773 = (13773:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_5773
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 5774) ≤ val WuPaper.ClassicalFourthData.Bq 5774
    have hp : val WuPaper.ClassicalFourthData.Bq 5774 = (259454461370141:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 5774 = 259454461370141 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 5774 = (6887:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_5774
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 5775) ≤ val WuPaper.ClassicalFourthData.Bq 5775
    have hp : val WuPaper.ClassicalFourthData.Bq 5775 = (259465334229125:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 5775 = 259465334229125 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 5775 = (551:ℝ)/160 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_5775
end WuPaper.ClassicalFourthConditions
#print axioms WuPaper.ClassicalFourthConditions.Log_block_360

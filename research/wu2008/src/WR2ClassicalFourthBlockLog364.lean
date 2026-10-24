import WR2ClassicalFourthConditions
import WR2ClassicalFourthLogPoints364
noncomputable section
namespace WuPaper.ClassicalFourthConditions
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem Log_block_364 (j : Fin 16) (hj : 16*364+j.val < 10541) :
    WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 (16*364+j.val)) ≤ val WuPaper.ClassicalFourthData.Bq (16*364+j.val) := by
  fin_cases j
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 5824) ≤ val WuPaper.ClassicalFourthData.Bq 5824
    have hp : val WuPaper.ClassicalFourthData.Bq 5824 = (259992479827809:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 5824 = 259992479827809 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 5824 = (432:ℝ)/125 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_5824
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 5825) ≤ val WuPaper.ClassicalFourthData.Bq 5825
    have hp : val WuPaper.ClassicalFourthData.Bq 5825 = (260003123800491:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 5825 = 260003123800491 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 5825 = (553:ℝ)/160 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_5825
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 5826) ≤ val WuPaper.ClassicalFourthData.Bq 5826
    have hp : val WuPaper.ClassicalFourthData.Bq 5826 = (260013763236389:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 5826 = 260013763236389 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 5826 = (6913:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_5826
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 5827) ≤ val WuPaper.ClassicalFourthData.Bq 5827
    have hp : val WuPaper.ClassicalFourthData.Bq 5827 = (260024398137097:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 5827 = 260024398137097 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 5827 = (13827:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_5827
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 5828) ≤ val WuPaper.ClassicalFourthData.Bq 5828
    have hp : val WuPaper.ClassicalFourthData.Bq 5828 = (260035028504210:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 5828 = 260035028504210 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 5828 = (3457:ℝ)/1000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_5828
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 5829) ≤ val WuPaper.ClassicalFourthData.Bq 5829
    have hp : val WuPaper.ClassicalFourthData.Bq 5829 = (260045654339320:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 5829 = 260045654339320 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 5829 = (13829:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_5829
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 5830) ≤ val WuPaper.ClassicalFourthData.Bq 5830
    have hp : val WuPaper.ClassicalFourthData.Bq 5830 = (260056275644019:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 5830 = 260056275644019 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 5830 = (1383:ℝ)/400 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_5830
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 5831) ≤ val WuPaper.ClassicalFourthData.Bq 5831
    have hp : val WuPaper.ClassicalFourthData.Bq 5831 = (260066892419900:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 5831 = 260066892419900 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 5831 = (13831:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_5831
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 5832) ≤ val WuPaper.ClassicalFourthData.Bq 5832
    have hp : val WuPaper.ClassicalFourthData.Bq 5832 = (260077504668552:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 5832 = 260077504668552 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 5832 = (1729:ℝ)/500 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_5832
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 5833) ≤ val WuPaper.ClassicalFourthData.Bq 5833
    have hp : val WuPaper.ClassicalFourthData.Bq 5833 = (260088112391568:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 5833 = 260088112391568 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 5833 = (13833:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_5833
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 5834) ≤ val WuPaper.ClassicalFourthData.Bq 5834
    have hp : val WuPaper.ClassicalFourthData.Bq 5834 = (260098715590536:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 5834 = 260098715590536 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 5834 = (6917:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_5834
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 5835) ≤ val WuPaper.ClassicalFourthData.Bq 5835
    have hp : val WuPaper.ClassicalFourthData.Bq 5835 = (260109314267045:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 5835 = 260109314267045 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 5835 = (2767:ℝ)/800 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_5835
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 5836) ≤ val WuPaper.ClassicalFourthData.Bq 5836
    have hp : val WuPaper.ClassicalFourthData.Bq 5836 = (260119908422685:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 5836 = 260119908422685 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 5836 = (3459:ℝ)/1000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_5836
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 5837) ≤ val WuPaper.ClassicalFourthData.Bq 5837
    have hp : val WuPaper.ClassicalFourthData.Bq 5837 = (260130498059042:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 5837 = 260130498059042 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 5837 = (13837:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_5837
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 5838) ≤ val WuPaper.ClassicalFourthData.Bq 5838
    have hp : val WuPaper.ClassicalFourthData.Bq 5838 = (260141083177705:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 5838 = 260141083177705 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 5838 = (6919:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_5838
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 5839) ≤ val WuPaper.ClassicalFourthData.Bq 5839
    have hp : val WuPaper.ClassicalFourthData.Bq 5839 = (260151663780259:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 5839 = 260151663780259 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 5839 = (13839:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_5839
end WuPaper.ClassicalFourthConditions
#print axioms WuPaper.ClassicalFourthConditions.Log_block_364

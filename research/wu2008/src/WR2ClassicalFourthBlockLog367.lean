import WR2ClassicalFourthConditions
import WR2ClassicalFourthLogPoints367
noncomputable section
namespace WuPaper.ClassicalFourthConditions
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem Log_block_367 (j : Fin 16) (hj : 16*367+j.val < 10541) :
    WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 (16*367+j.val)) ≤ val WuPaper.ClassicalFourthData.Bq (16*367+j.val) := by
  fin_cases j
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 5872) ≤ val WuPaper.ClassicalFourthData.Bq 5872
    have hp : val WuPaper.ClassicalFourthData.Bq 5872 = (260498300473805:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 5872 = 260498300473805 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 5872 = (867:ℝ)/250 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_5872
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 5873) ≤ val WuPaper.ClassicalFourthData.Bq 5873
    have hp : val WuPaper.ClassicalFourthData.Bq 5873 = (260508728468085:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 5873 = 260508728468085 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 5873 = (13873:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_5873
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 5874) ≤ val WuPaper.ClassicalFourthData.Bq 5874
    have hp : val WuPaper.ClassicalFourthData.Bq 5874 = (260519152001382:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 5874 = 260519152001382 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 5874 = (6937:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_5874
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 5875) ≤ val WuPaper.ClassicalFourthData.Bq 5875
    have hp : val WuPaper.ClassicalFourthData.Bq 5875 = (260529571075260:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 5875 = 260529571075260 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 5875 = (111:ℝ)/32 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_5875
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 5876) ≤ val WuPaper.ClassicalFourthData.Bq 5876
    have hp : val WuPaper.ClassicalFourthData.Bq 5876 = (260539985691281:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 5876 = 260539985691281 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 5876 = (3469:ℝ)/1000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_5876
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 5877) ≤ val WuPaper.ClassicalFourthData.Bq 5877
    have hp : val WuPaper.ClassicalFourthData.Bq 5877 = (260550395851009:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 5877 = 260550395851009 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 5877 = (13877:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_5877
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 5878) ≤ val WuPaper.ClassicalFourthData.Bq 5878
    have hp : val WuPaper.ClassicalFourthData.Bq 5878 = (260560801556004:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 5878 = 260560801556004 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 5878 = (6939:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_5878
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 5879) ≤ val WuPaper.ClassicalFourthData.Bq 5879
    have hp : val WuPaper.ClassicalFourthData.Bq 5879 = (260571202807827:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 5879 = 260571202807827 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 5879 = (13879:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_5879
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 5880) ≤ val WuPaper.ClassicalFourthData.Bq 5880
    have hp : val WuPaper.ClassicalFourthData.Bq 5880 = (260581599608040:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 5880 = 260581599608040 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 5880 = (347:ℝ)/100 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_5880
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 5881) ≤ val WuPaper.ClassicalFourthData.Bq 5881
    have hp : val WuPaper.ClassicalFourthData.Bq 5881 = (260591991958201:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 5881 = 260591991958201 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 5881 = (13881:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_5881
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 5882) ≤ val WuPaper.ClassicalFourthData.Bq 5882
    have hp : val WuPaper.ClassicalFourthData.Bq 5882 = (260602379859871:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 5882 = 260602379859871 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 5882 = (6941:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_5882
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 5883) ≤ val WuPaper.ClassicalFourthData.Bq 5883
    have hp : val WuPaper.ClassicalFourthData.Bq 5883 = (260612763314606:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 5883 = 260612763314606 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 5883 = (13883:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_5883
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 5884) ≤ val WuPaper.ClassicalFourthData.Bq 5884
    have hp : val WuPaper.ClassicalFourthData.Bq 5884 = (260623142323966:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 5884 = 260623142323966 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 5884 = (3471:ℝ)/1000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_5884
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 5885) ≤ val WuPaper.ClassicalFourthData.Bq 5885
    have hp : val WuPaper.ClassicalFourthData.Bq 5885 = (260633516889507:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 5885 = 260633516889507 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 5885 = (2777:ℝ)/800 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_5885
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 5886) ≤ val WuPaper.ClassicalFourthData.Bq 5886
    have hp : val WuPaper.ClassicalFourthData.Bq 5886 = (260643887012787:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 5886 = 260643887012787 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 5886 = (6943:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_5886
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 5887) ≤ val WuPaper.ClassicalFourthData.Bq 5887
    have hp : val WuPaper.ClassicalFourthData.Bq 5887 = (260654252695361:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 5887 = 260654252695361 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 5887 = (13887:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_5887
end WuPaper.ClassicalFourthConditions
#print axioms WuPaper.ClassicalFourthConditions.Log_block_367

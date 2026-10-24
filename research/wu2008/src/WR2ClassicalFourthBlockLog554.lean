import WR2ClassicalFourthConditions
import WR2ClassicalFourthLogPoints554
noncomputable section
namespace WuPaper.ClassicalFourthConditions
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem Log_block_554 (j : Fin 16) (hj : 16*554+j.val < 10541) :
    WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 (16*554+j.val)) ≤ val WuPaper.ClassicalFourthData.Bq (16*554+j.val) := by
  fin_cases j
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 8864) ≤ val WuPaper.ClassicalFourthData.Bq 8864
    have hp : val WuPaper.ClassicalFourthData.Bq 8864 = (277072663977859:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 8864 = 277072663977859 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 8864 = (527:ℝ)/125 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_8864
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 8865) ≤ val WuPaper.ClassicalFourthData.Bq 8865
    have hp : val WuPaper.ClassicalFourthData.Bq 8865 = (277074671717231:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 8865 = 277074671717231 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 8865 = (3373:ℝ)/800 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_8865
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 8866) ≤ val WuPaper.ClassicalFourthData.Bq 8866
    have hp : val WuPaper.ClassicalFourthData.Bq 8866 = (277076677785581:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 8866 = 277076677785581 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 8866 = (8433:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_8866
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 8867) ≤ val WuPaper.ClassicalFourthData.Bq 8867
    have hp : val WuPaper.ClassicalFourthData.Bq 8867 = (277078682183429:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 8867 = 277078682183429 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 8867 = (16867:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_8867
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 8868) ≤ val WuPaper.ClassicalFourthData.Bq 8868
    have hp : val WuPaper.ClassicalFourthData.Bq 8868 = (277080684911294:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 8868 = 277080684911294 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 8868 = (4217:ℝ)/1000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_8868
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 8869) ≤ val WuPaper.ClassicalFourthData.Bq 8869
    have hp : val WuPaper.ClassicalFourthData.Bq 8869 = (277082685969696:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 8869 = 277082685969696 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 8869 = (16869:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_8869
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 8870) ≤ val WuPaper.ClassicalFourthData.Bq 8870
    have hp : val WuPaper.ClassicalFourthData.Bq 8870 = (277084685359154:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 8870 = 277084685359154 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 8870 = (1687:ℝ)/400 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_8870
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 8871) ≤ val WuPaper.ClassicalFourthData.Bq 8871
    have hp : val WuPaper.ClassicalFourthData.Bq 8871 = (277086683080188:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 8871 = 277086683080188 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 8871 = (16871:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_8871
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 8872) ≤ val WuPaper.ClassicalFourthData.Bq 8872
    have hp : val WuPaper.ClassicalFourthData.Bq 8872 = (277088679133317:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 8872 = 277088679133317 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 8872 = (2109:ℝ)/500 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_8872
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 8873) ≤ val WuPaper.ClassicalFourthData.Bq 8873
    have hp : val WuPaper.ClassicalFourthData.Bq 8873 = (277090673519059:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 8873 = 277090673519059 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 8873 = (16873:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_8873
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 8874) ≤ val WuPaper.ClassicalFourthData.Bq 8874
    have hp : val WuPaper.ClassicalFourthData.Bq 8874 = (277092666237934:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 8874 = 277092666237934 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 8874 = (8437:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_8874
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 8875) ≤ val WuPaper.ClassicalFourthData.Bq 8875
    have hp : val WuPaper.ClassicalFourthData.Bq 8875 = (277094657290460:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 8875 = 277094657290460 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 8875 = (135:ℝ)/32 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_8875
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 8876) ≤ val WuPaper.ClassicalFourthData.Bq 8876
    have hp : val WuPaper.ClassicalFourthData.Bq 8876 = (277096646677154:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 8876 = 277096646677154 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 8876 = (4219:ℝ)/1000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_8876
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 8877) ≤ val WuPaper.ClassicalFourthData.Bq 8877
    have hp : val WuPaper.ClassicalFourthData.Bq 8877 = (277098634398537:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 8877 = 277098634398537 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 8877 = (16877:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_8877
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 8878) ≤ val WuPaper.ClassicalFourthData.Bq 8878
    have hp : val WuPaper.ClassicalFourthData.Bq 8878 = (277100620455124:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 8878 = 277100620455124 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 8878 = (8439:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_8878
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 8879) ≤ val WuPaper.ClassicalFourthData.Bq 8879
    have hp : val WuPaper.ClassicalFourthData.Bq 8879 = (277102604847435:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 8879 = 277102604847435 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 8879 = (16879:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_8879
end WuPaper.ClassicalFourthConditions
#print axioms WuPaper.ClassicalFourthConditions.Log_block_554

import WR2ClassicalFourthConditions
import WR2ClassicalFourthLogPoints117
noncomputable section
namespace WuPaper.ClassicalFourthConditions
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem Log_block_117 (j : Fin 16) (hj : 16*117+j.val < 10541) :
    WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 (16*117+j.val)) ≤ val WuPaper.ClassicalFourthData.Bq (16*117+j.val) := by
  fin_cases j
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 1872) ≤ val WuPaper.ClassicalFourthData.Bq 1872
    have hp : val WuPaper.ClassicalFourthData.Bq 1872 = (155551430385869:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 1872 = 155551430385869 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 1872 = (617:ℝ)/250 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_1872
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 1873) ≤ val WuPaper.ClassicalFourthData.Bq 1873
    have hp : val WuPaper.ClassicalFourthData.Bq 1873 = (155604665419019:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 1873 = 155604665419019 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 1873 = (9873:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_1873
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 1874) ≤ val WuPaper.ClassicalFourthData.Bq 1874
    have hp : val WuPaper.ClassicalFourthData.Bq 1874 = (155657877924464:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 1874 = 155657877924464 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 1874 = (4937:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_1874
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 1875) ≤ val WuPaper.ClassicalFourthData.Bq 1875
    have hp : val WuPaper.ClassicalFourthData.Bq 1875 = (155711067913046:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 1875 = 155711067913046 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 1875 = (79:ℝ)/32 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_1875
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 1876) ≤ val WuPaper.ClassicalFourthData.Bq 1876
    have hp : val WuPaper.ClassicalFourthData.Bq 1876 = (155764235395602:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 1876 = 155764235395602 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 1876 = (2469:ℝ)/1000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_1876
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 1877) ≤ val WuPaper.ClassicalFourthData.Bq 1877
    have hp : val WuPaper.ClassicalFourthData.Bq 1877 = (155817380382960:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 1877 = 155817380382960 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 1877 = (9877:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_1877
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 1878) ≤ val WuPaper.ClassicalFourthData.Bq 1878
    have hp : val WuPaper.ClassicalFourthData.Bq 1878 = (155870502885943:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 1878 = 155870502885943 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 1878 = (4939:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_1878
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 1879) ≤ val WuPaper.ClassicalFourthData.Bq 1879
    have hp : val WuPaper.ClassicalFourthData.Bq 1879 = (155923602915367:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 1879 = 155923602915367 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 1879 = (9879:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_1879
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 1880) ≤ val WuPaper.ClassicalFourthData.Bq 1880
    have hp : val WuPaper.ClassicalFourthData.Bq 1880 = (155976680482043:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 1880 = 155976680482043 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 1880 = (247:ℝ)/100 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_1880
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 1881) ≤ val WuPaper.ClassicalFourthData.Bq 1881
    have hp : val WuPaper.ClassicalFourthData.Bq 1881 = (156029735596773:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 1881 = 156029735596773 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 1881 = (9881:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_1881
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 1882) ≤ val WuPaper.ClassicalFourthData.Bq 1882
    have hp : val WuPaper.ClassicalFourthData.Bq 1882 = (156082768270356:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 1882 = 156082768270356 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 1882 = (4941:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_1882
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 1883) ≤ val WuPaper.ClassicalFourthData.Bq 1883
    have hp : val WuPaper.ClassicalFourthData.Bq 1883 = (156135778513581:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 1883 = 156135778513581 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 1883 = (9883:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_1883
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 1884) ≤ val WuPaper.ClassicalFourthData.Bq 1884
    have hp : val WuPaper.ClassicalFourthData.Bq 1884 = (156188766337233:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 1884 = 156188766337233 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 1884 = (2471:ℝ)/1000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_1884
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 1885) ≤ val WuPaper.ClassicalFourthData.Bq 1885
    have hp : val WuPaper.ClassicalFourthData.Bq 1885 = (156241731752089:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 1885 = 156241731752089 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 1885 = (1977:ℝ)/800 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_1885
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 1886) ≤ val WuPaper.ClassicalFourthData.Bq 1886
    have hp : val WuPaper.ClassicalFourthData.Bq 1886 = (156294674768922:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 1886 = 156294674768922 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 1886 = (4943:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_1886
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 1887) ≤ val WuPaper.ClassicalFourthData.Bq 1887
    have hp : val WuPaper.ClassicalFourthData.Bq 1887 = (156347595398497:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 1887 = 156347595398497 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 1887 = (9887:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_1887
end WuPaper.ClassicalFourthConditions
#print axioms WuPaper.ClassicalFourthConditions.Log_block_117

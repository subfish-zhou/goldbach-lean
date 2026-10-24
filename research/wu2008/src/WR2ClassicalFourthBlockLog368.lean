import WR2ClassicalFourthConditions
import WR2ClassicalFourthLogPoints368
noncomputable section
namespace WuPaper.ClassicalFourthConditions
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem Log_block_368 (j : Fin 16) (hj : 16*368+j.val < 10541) :
    WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 (16*368+j.val)) ≤ val WuPaper.ClassicalFourthData.Bq (16*368+j.val) := by
  fin_cases j
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 5888) ≤ val WuPaper.ClassicalFourthData.Bq 5888
    have hp : val WuPaper.ClassicalFourthData.Bq 5888 = (260664613938784:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 5888 = 260664613938784 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 5888 = (434:ℝ)/125 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_5888
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 5889) ≤ val WuPaper.ClassicalFourthData.Bq 5889
    have hp : val WuPaper.ClassicalFourthData.Bq 5889 = (260674970744611:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 5889 = 260674970744611 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 5889 = (13889:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_5889
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 5890) ≤ val WuPaper.ClassicalFourthData.Bq 5890
    have hp : val WuPaper.ClassicalFourthData.Bq 5890 = (260685323114397:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 5890 = 260685323114397 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 5890 = (1389:ℝ)/400 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_5890
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 5891) ≤ val WuPaper.ClassicalFourthData.Bq 5891
    have hp : val WuPaper.ClassicalFourthData.Bq 5891 = (260695671049694:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 5891 = 260695671049694 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 5891 = (13891:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_5891
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 5892) ≤ val WuPaper.ClassicalFourthData.Bq 5892
    have hp : val WuPaper.ClassicalFourthData.Bq 5892 = (260706014552057:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 5892 = 260706014552057 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 5892 = (3473:ℝ)/1000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_5892
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 5893) ≤ val WuPaper.ClassicalFourthData.Bq 5893
    have hp : val WuPaper.ClassicalFourthData.Bq 5893 = (260716353623036:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 5893 = 260716353623036 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 5893 = (13893:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_5893
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 5894) ≤ val WuPaper.ClassicalFourthData.Bq 5894
    have hp : val WuPaper.ClassicalFourthData.Bq 5894 = (260726688264183:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 5894 = 260726688264183 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 5894 = (6947:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_5894
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 5895) ≤ val WuPaper.ClassicalFourthData.Bq 5895
    have hp : val WuPaper.ClassicalFourthData.Bq 5895 = (260737018477050:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 5895 = 260737018477050 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 5895 = (2779:ℝ)/800 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_5895
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 5896) ≤ val WuPaper.ClassicalFourthData.Bq 5896
    have hp : val WuPaper.ClassicalFourthData.Bq 5896 = (260747344263186:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 5896 = 260747344263186 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 5896 = (1737:ℝ)/500 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_5896
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 5897) ≤ val WuPaper.ClassicalFourthData.Bq 5897
    have hp : val WuPaper.ClassicalFourthData.Bq 5897 = (260757665624142:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 5897 = 260757665624142 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 5897 = (13897:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_5897
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 5898) ≤ val WuPaper.ClassicalFourthData.Bq 5898
    have hp : val WuPaper.ClassicalFourthData.Bq 5898 = (260767982561467:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 5898 = 260767982561467 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 5898 = (6949:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_5898
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 5899) ≤ val WuPaper.ClassicalFourthData.Bq 5899
    have hp : val WuPaper.ClassicalFourthData.Bq 5899 = (260778295076709:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 5899 = 260778295076709 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 5899 = (13899:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_5899
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 5900) ≤ val WuPaper.ClassicalFourthData.Bq 5900
    have hp : val WuPaper.ClassicalFourthData.Bq 5900 = (260788603171415:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 5900 = 260788603171415 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 5900 = (139:ℝ)/40 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_5900
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 5901) ≤ val WuPaper.ClassicalFourthData.Bq 5901
    have hp : val WuPaper.ClassicalFourthData.Bq 5901 = (260798906847133:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 5901 = 260798906847133 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 5901 = (13901:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_5901
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 5902) ≤ val WuPaper.ClassicalFourthData.Bq 5902
    have hp : val WuPaper.ClassicalFourthData.Bq 5902 = (260809206105411:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 5902 = 260809206105411 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 5902 = (6951:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_5902
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 5903) ≤ val WuPaper.ClassicalFourthData.Bq 5903
    have hp : val WuPaper.ClassicalFourthData.Bq 5903 = (260819500947792:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 5903 = 260819500947792 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 5903 = (13903:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_5903
end WuPaper.ClassicalFourthConditions
#print axioms WuPaper.ClassicalFourthConditions.Log_block_368

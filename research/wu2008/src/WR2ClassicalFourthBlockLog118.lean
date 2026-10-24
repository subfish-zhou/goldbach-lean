import WR2ClassicalFourthConditions
import WR2ClassicalFourthLogPoints118
noncomputable section
namespace WuPaper.ClassicalFourthConditions
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem Log_block_118 (j : Fin 16) (hj : 16*118+j.val < 10541) :
    WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 (16*118+j.val)) ≤ val WuPaper.ClassicalFourthData.Bq (16*118+j.val) := by
  fin_cases j
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 1888) ≤ val WuPaper.ClassicalFourthData.Bq 1888
    have hp : val WuPaper.ClassicalFourthData.Bq 1888 = (156400493651572:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 1888 = 156400493651572 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 1888 = (309:ℝ)/125 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_1888
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 1889) ≤ val WuPaper.ClassicalFourthData.Bq 1889
    have hp : val WuPaper.ClassicalFourthData.Bq 1889 = (156453369538900:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 1889 = 156453369538900 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 1889 = (9889:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_1889
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 1890) ≤ val WuPaper.ClassicalFourthData.Bq 1890
    have hp : val WuPaper.ClassicalFourthData.Bq 1890 = (156506223071226:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 1890 = 156506223071226 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 1890 = (989:ℝ)/400 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_1890
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 1891) ≤ val WuPaper.ClassicalFourthData.Bq 1891
    have hp : val WuPaper.ClassicalFourthData.Bq 1891 = (156559054259291:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 1891 = 156559054259291 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 1891 = (9891:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_1891
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 1892) ≤ val WuPaper.ClassicalFourthData.Bq 1892
    have hp : val WuPaper.ClassicalFourthData.Bq 1892 = (156611863113827:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 1892 = 156611863113827 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 1892 = (2473:ℝ)/1000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_1892
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 1893) ≤ val WuPaper.ClassicalFourthData.Bq 1893
    have hp : val WuPaper.ClassicalFourthData.Bq 1893 = (156664649645562:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 1893 = 156664649645562 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 1893 = (9893:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_1893
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 1894) ≤ val WuPaper.ClassicalFourthData.Bq 1894
    have hp : val WuPaper.ClassicalFourthData.Bq 1894 = (156717413865217:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 1894 = 156717413865217 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 1894 = (4947:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_1894
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 1895) ≤ val WuPaper.ClassicalFourthData.Bq 1895
    have hp : val WuPaper.ClassicalFourthData.Bq 1895 = (156770155783505:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 1895 = 156770155783505 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 1895 = (1979:ℝ)/800 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_1895
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 1896) ≤ val WuPaper.ClassicalFourthData.Bq 1896
    have hp : val WuPaper.ClassicalFourthData.Bq 1896 = (156822875411134:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 1896 = 156822875411134 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 1896 = (1237:ℝ)/500 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_1896
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 1897) ≤ val WuPaper.ClassicalFourthData.Bq 1897
    have hp : val WuPaper.ClassicalFourthData.Bq 1897 = (156875572758807:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 1897 = 156875572758807 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 1897 = (9897:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_1897
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 1898) ≤ val WuPaper.ClassicalFourthData.Bq 1898
    have hp : val WuPaper.ClassicalFourthData.Bq 1898 = (156928247837218:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 1898 = 156928247837218 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 1898 = (4949:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_1898
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 1899) ≤ val WuPaper.ClassicalFourthData.Bq 1899
    have hp : val WuPaper.ClassicalFourthData.Bq 1899 = (156980900657056:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 1899 = 156980900657056 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 1899 = (9899:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_1899
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 1900) ≤ val WuPaper.ClassicalFourthData.Bq 1900
    have hp : val WuPaper.ClassicalFourthData.Bq 1900 = (157033531229004:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 1900 = 157033531229004 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 1900 = (99:ℝ)/40 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_1900
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 1901) ≤ val WuPaper.ClassicalFourthData.Bq 1901
    have hp : val WuPaper.ClassicalFourthData.Bq 1901 = (157086139563738:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 1901 = 157086139563738 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 1901 = (9901:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_1901
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 1902) ≤ val WuPaper.ClassicalFourthData.Bq 1902
    have hp : val WuPaper.ClassicalFourthData.Bq 1902 = (157138725671928:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 1902 = 157138725671928 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 1902 = (4951:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_1902
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 1903) ≤ val WuPaper.ClassicalFourthData.Bq 1903
    have hp : val WuPaper.ClassicalFourthData.Bq 1903 = (157191289564238:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 1903 = 157191289564238 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 1903 = (9903:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_1903
end WuPaper.ClassicalFourthConditions
#print axioms WuPaper.ClassicalFourthConditions.Log_block_118

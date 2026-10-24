import WR2ClassicalFourthConditions
import WR2ClassicalFourthLogPoints121
noncomputable section
namespace WuPaper.ClassicalFourthConditions
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem Log_block_121 (j : Fin 16) (hj : 16*121+j.val < 10541) :
    WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 (16*121+j.val)) ≤ val WuPaper.ClassicalFourthData.Bq (16*121+j.val) := by
  fin_cases j
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 1936) ≤ val WuPaper.ClassicalFourthData.Bq 1936
    have hp : val WuPaper.ClassicalFourthData.Bq 1936 = (158913504325761:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 1936 = 158913504325761 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 1936 = (621:ℝ)/250 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_1936
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 1937) ≤ val WuPaper.ClassicalFourthData.Bq 1937
    have hp : val WuPaper.ClassicalFourthData.Bq 1937 = (158965319178283:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 1937 = 158965319178283 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 1937 = (9937:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_1937
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 1938) ≤ val WuPaper.ClassicalFourthData.Bq 1938
    have hp : val WuPaper.ClassicalFourthData.Bq 1938 = (159017112184214:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 1938 = 159017112184214 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 1938 = (4969:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_1938
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 1939) ≤ val WuPaper.ClassicalFourthData.Bq 1939
    have hp : val WuPaper.ClassicalFourthData.Bq 1939 = (159068883353993:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 1939 = 159068883353993 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 1939 = (9939:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_1939
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 1940) ≤ val WuPaper.ClassicalFourthData.Bq 1940
    have hp : val WuPaper.ClassicalFourthData.Bq 1940 = (159120632698054:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 1940 = 159120632698054 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 1940 = (497:ℝ)/200 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_1940
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 1941) ≤ val WuPaper.ClassicalFourthData.Bq 1941
    have hp : val WuPaper.ClassicalFourthData.Bq 1941 = (159172360226824:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 1941 = 159172360226824 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 1941 = (9941:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_1941
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 1942) ≤ val WuPaper.ClassicalFourthData.Bq 1942
    have hp : val WuPaper.ClassicalFourthData.Bq 1942 = (159224065950725:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 1942 = 159224065950725 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 1942 = (4971:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_1942
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 1943) ≤ val WuPaper.ClassicalFourthData.Bq 1943
    have hp : val WuPaper.ClassicalFourthData.Bq 1943 = (159275749880171:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 1943 = 159275749880171 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 1943 = (9943:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_1943
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 1944) ≤ val WuPaper.ClassicalFourthData.Bq 1944
    have hp : val WuPaper.ClassicalFourthData.Bq 1944 = (159327412025571:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 1944 = 159327412025571 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 1944 = (1243:ℝ)/500 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_1944
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 1945) ≤ val WuPaper.ClassicalFourthData.Bq 1945
    have hp : val WuPaper.ClassicalFourthData.Bq 1945 = (159379052397328:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 1945 = 159379052397328 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 1945 = (1989:ℝ)/800 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_1945
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 1946) ≤ val WuPaper.ClassicalFourthData.Bq 1946
    have hp : val WuPaper.ClassicalFourthData.Bq 1946 = (159430671005838:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 1946 = 159430671005838 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 1946 = (4973:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_1946
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 1947) ≤ val WuPaper.ClassicalFourthData.Bq 1947
    have hp : val WuPaper.ClassicalFourthData.Bq 1947 = (159482267861493:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 1947 = 159482267861493 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 1947 = (9947:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_1947
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 1948) ≤ val WuPaper.ClassicalFourthData.Bq 1948
    have hp : val WuPaper.ClassicalFourthData.Bq 1948 = (159533842974676:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 1948 = 159533842974676 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 1948 = (2487:ℝ)/1000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_1948
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 1949) ≤ val WuPaper.ClassicalFourthData.Bq 1949
    have hp : val WuPaper.ClassicalFourthData.Bq 1949 = (159585396355766:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 1949 = 159585396355766 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 1949 = (9949:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_1949
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 1950) ≤ val WuPaper.ClassicalFourthData.Bq 1950
    have hp : val WuPaper.ClassicalFourthData.Bq 1950 = (159636928015135:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 1950 = 159636928015135 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 1950 = (199:ℝ)/80 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_1950
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 1951) ≤ val WuPaper.ClassicalFourthData.Bq 1951
    have hp : val WuPaper.ClassicalFourthData.Bq 1951 = (159688437963150:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 1951 = 159688437963150 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 1951 = (9951:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_1951
end WuPaper.ClassicalFourthConditions
#print axioms WuPaper.ClassicalFourthConditions.Log_block_121

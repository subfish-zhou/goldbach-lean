import WR2ClassicalFourthConditions
import WR2ClassicalFourthLogPoints123
noncomputable section
namespace WuPaper.ClassicalFourthConditions
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem Log_block_123 (j : Fin 16) (hj : 16*123+j.val < 10541) :
    WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 (16*123+j.val)) ≤ val WuPaper.ClassicalFourthData.Bq (16*123+j.val) := by
  fin_cases j
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 1968) ≤ val WuPaper.ClassicalFourthData.Bq 1968
    have hp : val WuPaper.ClassicalFourthData.Bq 1968 = (160560795257452:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 1968 = 160560795257452 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 1968 = (623:ℝ)/250 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_1968
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 1969) ≤ val WuPaper.ClassicalFourthData.Bq 1969
    have hp : val WuPaper.ClassicalFourthData.Bq 1969 = (160611916166766:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 1969 = 160611916166766 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 1969 = (9969:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_1969
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 1970) ≤ val WuPaper.ClassicalFourthData.Bq 1970
    have hp : val WuPaper.ClassicalFourthData.Bq 1970 = (160663015560530:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 1970 = 160663015560530 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 1970 = (997:ℝ)/400 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_1970
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 1971) ≤ val WuPaper.ClassicalFourthData.Bq 1971
    have hp : val WuPaper.ClassicalFourthData.Bq 1971 = (160714093448988:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 1971 = 160714093448988 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 1971 = (9971:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_1971
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 1972) ≤ val WuPaper.ClassicalFourthData.Bq 1972
    have hp : val WuPaper.ClassicalFourthData.Bq 1972 = (160765149842380:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 1972 = 160765149842380 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 1972 = (2493:ℝ)/1000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_1972
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 1973) ≤ val WuPaper.ClassicalFourthData.Bq 1973
    have hp : val WuPaper.ClassicalFourthData.Bq 1973 = (160816184750939:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 1973 = 160816184750939 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 1973 = (9973:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_1973
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 1974) ≤ val WuPaper.ClassicalFourthData.Bq 1974
    have hp : val WuPaper.ClassicalFourthData.Bq 1974 = (160867198184892:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 1974 = 160867198184892 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 1974 = (4987:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_1974
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 1975) ≤ val WuPaper.ClassicalFourthData.Bq 1975
    have hp : val WuPaper.ClassicalFourthData.Bq 1975 = (160918190154460:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 1975 = 160918190154460 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 1975 = (399:ℝ)/160 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_1975
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 1976) ≤ val WuPaper.ClassicalFourthData.Bq 1976
    have hp : val WuPaper.ClassicalFourthData.Bq 1976 = (160969160669858:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 1976 = 160969160669858 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 1976 = (1247:ℝ)/500 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_1976
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 1977) ≤ val WuPaper.ClassicalFourthData.Bq 1977
    have hp : val WuPaper.ClassicalFourthData.Bq 1977 = (161020109741296:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 1977 = 161020109741296 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 1977 = (9977:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_1977
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 1978) ≤ val WuPaper.ClassicalFourthData.Bq 1978
    have hp : val WuPaper.ClassicalFourthData.Bq 1978 = (161071037378976:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 1978 = 161071037378976 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 1978 = (4989:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_1978
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 1979) ≤ val WuPaper.ClassicalFourthData.Bq 1979
    have hp : val WuPaper.ClassicalFourthData.Bq 1979 = (161121943593097:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 1979 = 161121943593097 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 1979 = (9979:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_1979
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 1980) ≤ val WuPaper.ClassicalFourthData.Bq 1980
    have hp : val WuPaper.ClassicalFourthData.Bq 1980 = (161172828393848:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 1980 = 161172828393848 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 1980 = (499:ℝ)/200 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_1980
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 1981) ≤ val WuPaper.ClassicalFourthData.Bq 1981
    have hp : val WuPaper.ClassicalFourthData.Bq 1981 = (161223691791416:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 1981 = 161223691791416 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 1981 = (9981:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_1981
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 1982) ≤ val WuPaper.ClassicalFourthData.Bq 1982
    have hp : val WuPaper.ClassicalFourthData.Bq 1982 = (161274533795980:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 1982 = 161274533795980 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 1982 = (4991:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_1982
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 1983) ≤ val WuPaper.ClassicalFourthData.Bq 1983
    have hp : val WuPaper.ClassicalFourthData.Bq 1983 = (161325354417712:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 1983 = 161325354417712 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 1983 = (9983:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_1983
end WuPaper.ClassicalFourthConditions
#print axioms WuPaper.ClassicalFourthConditions.Log_block_123

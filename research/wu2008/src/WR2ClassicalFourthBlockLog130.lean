import WR2ClassicalFourthConditions
import WR2ClassicalFourthLogPoints130
noncomputable section
namespace WuPaper.ClassicalFourthConditions
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem Log_block_130 (j : Fin 16) (hj : 16*130+j.val < 10541) :
    WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 (16*130+j.val)) ≤ val WuPaper.ClassicalFourthData.Bq (16*130+j.val) := by
  fin_cases j
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 2080) ≤ val WuPaper.ClassicalFourthData.Bq 2080
    have hp : val WuPaper.ClassicalFourthData.Bq 2080 = (166154894784995:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 2080 = 166154894784995 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 2080 = (63:ℝ)/25 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_2080
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 2081) ≤ val WuPaper.ClassicalFourthData.Bq 2081
    have hp : val WuPaper.ClassicalFourthData.Bq 2081 = (166203668294052:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 2081 = 166203668294052 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 2081 = (10081:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_2081
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 2082) ≤ val WuPaper.ClassicalFourthData.Bq 2082
    have hp : val WuPaper.ClassicalFourthData.Bq 2082 = (166252421398645:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 2082 = 166252421398645 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 2082 = (5041:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_2082
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 2083) ≤ val WuPaper.ClassicalFourthData.Bq 2083
    have hp : val WuPaper.ClassicalFourthData.Bq 2083 = (166301154108372:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 2083 = 166301154108372 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 2083 = (10083:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_2083
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 2084) ≤ val WuPaper.ClassicalFourthData.Bq 2084
    have hp : val WuPaper.ClassicalFourthData.Bq 2084 = (166349866432827:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 2084 = 166349866432827 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 2084 = (2521:ℝ)/1000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_2084
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 2085) ≤ val WuPaper.ClassicalFourthData.Bq 2085
    have hp : val WuPaper.ClassicalFourthData.Bq 2085 = (166398558381597:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 2085 = 166398558381597 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 2085 = (2017:ℝ)/800 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_2085
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 2086) ≤ val WuPaper.ClassicalFourthData.Bq 2086
    have hp : val WuPaper.ClassicalFourthData.Bq 2086 = (166447229964263:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 2086 = 166447229964263 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 2086 = (5043:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_2086
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 2087) ≤ val WuPaper.ClassicalFourthData.Bq 2087
    have hp : val WuPaper.ClassicalFourthData.Bq 2087 = (166495881190403:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 2087 = 166495881190403 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 2087 = (10087:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_2087
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 2088) ≤ val WuPaper.ClassicalFourthData.Bq 2088
    have hp : val WuPaper.ClassicalFourthData.Bq 2088 = (166544512069586:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 2088 = 166544512069586 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 2088 = (1261:ℝ)/500 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_2088
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 2089) ≤ val WuPaper.ClassicalFourthData.Bq 2089
    have hp : val WuPaper.ClassicalFourthData.Bq 2089 = (166593122611378:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 2089 = 166593122611378 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 2089 = (10089:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_2089
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 2090) ≤ val WuPaper.ClassicalFourthData.Bq 2090
    have hp : val WuPaper.ClassicalFourthData.Bq 2090 = (166641712825338:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 2090 = 166641712825338 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 2090 = (1009:ℝ)/400 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_2090
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 2091) ≤ val WuPaper.ClassicalFourthData.Bq 2091
    have hp : val WuPaper.ClassicalFourthData.Bq 2091 = (166690282721022:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 2091 = 166690282721022 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 2091 = (10091:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_2091
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 2092) ≤ val WuPaper.ClassicalFourthData.Bq 2092
    have hp : val WuPaper.ClassicalFourthData.Bq 2092 = (166738832307977:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 2092 = 166738832307977 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 2092 = (2523:ℝ)/1000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_2092
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 2093) ≤ val WuPaper.ClassicalFourthData.Bq 2093
    have hp : val WuPaper.ClassicalFourthData.Bq 2093 = (166787361595747:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 2093 = 166787361595747 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 2093 = (10093:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_2093
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 2094) ≤ val WuPaper.ClassicalFourthData.Bq 2094
    have hp : val WuPaper.ClassicalFourthData.Bq 2094 = (166835870593869:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 2094 = 166835870593869 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 2094 = (5047:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_2094
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 2095) ≤ val WuPaper.ClassicalFourthData.Bq 2095
    have hp : val WuPaper.ClassicalFourthData.Bq 2095 = (166884359311875:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 2095 = 166884359311875 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 2095 = (2019:ℝ)/800 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_2095
end WuPaper.ClassicalFourthConditions
#print axioms WuPaper.ClassicalFourthConditions.Log_block_130

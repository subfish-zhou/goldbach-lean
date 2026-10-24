import WR2ClassicalFourthConditions
import WR2ClassicalFourthLogPoints129
noncomputable section
namespace WuPaper.ClassicalFourthConditions
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem Log_block_129 (j : Fin 16) (hj : 16*129+j.val < 10541) :
    WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 (16*129+j.val)) ≤ val WuPaper.ClassicalFourthData.Bq (16*129+j.val) := by
  fin_cases j
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 2064) ≤ val WuPaper.ClassicalFourthData.Bq 2064
    have hp : val WuPaper.ClassicalFourthData.Bq 2064 = (165371735779086:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 2064 = 165371735779086 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 2064 = (629:ℝ)/250 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_2064
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 2065) ≤ val WuPaper.ClassicalFourthData.Bq 2065
    have hp : val WuPaper.ClassicalFourthData.Bq 2065 = (165420837069498:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 2065 = 165420837069498 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 2065 = (2013:ℝ)/800 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_2065
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 2066) ≤ val WuPaper.ClassicalFourthData.Bq 2066
    have hp : val WuPaper.ClassicalFourthData.Bq 2066 = (165469917801113:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 2066 = 165469917801113 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 2066 = (5033:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_2066
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 2067) ≤ val WuPaper.ClassicalFourthData.Bq 2067
    have hp : val WuPaper.ClassicalFourthData.Bq 2067 = (165518977983618:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 2067 = 165518977983618 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 2067 = (10067:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_2067
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 2068) ≤ val WuPaper.ClassicalFourthData.Bq 2068
    have hp : val WuPaper.ClassicalFourthData.Bq 2068 = (165568017626697:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 2068 = 165568017626697 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 2068 = (2517:ℝ)/1000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_2068
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 2069) ≤ val WuPaper.ClassicalFourthData.Bq 2069
    have hp : val WuPaper.ClassicalFourthData.Bq 2069 = (165617036740025:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 2069 = 165617036740025 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 2069 = (10069:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_2069
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 2070) ≤ val WuPaper.ClassicalFourthData.Bq 2070
    have hp : val WuPaper.ClassicalFourthData.Bq 2070 = (165666035333274:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 2070 = 165666035333274 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 2070 = (1007:ℝ)/400 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_2070
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 2071) ≤ val WuPaper.ClassicalFourthData.Bq 2071
    have hp : val WuPaper.ClassicalFourthData.Bq 2071 = (165715013416109:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 2071 = 165715013416109 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 2071 = (10071:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_2071
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 2072) ≤ val WuPaper.ClassicalFourthData.Bq 2072
    have hp : val WuPaper.ClassicalFourthData.Bq 2072 = (165763970998189:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 2072 = 165763970998189 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 2072 = (1259:ℝ)/500 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_2072
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 2073) ≤ val WuPaper.ClassicalFourthData.Bq 2073
    have hp : val WuPaper.ClassicalFourthData.Bq 2073 = (165812908089169:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 2073 = 165812908089169 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 2073 = (10073:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_2073
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 2074) ≤ val WuPaper.ClassicalFourthData.Bq 2074
    have hp : val WuPaper.ClassicalFourthData.Bq 2074 = (165861824698697:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 2074 = 165861824698697 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 2074 = (5037:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_2074
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 2075) ≤ val WuPaper.ClassicalFourthData.Bq 2075
    have hp : val WuPaper.ClassicalFourthData.Bq 2075 = (165910720836416:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 2075 = 165910720836416 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 2075 = (403:ℝ)/160 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_2075
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 2076) ≤ val WuPaper.ClassicalFourthData.Bq 2076
    have hp : val WuPaper.ClassicalFourthData.Bq 2076 = (165959596511964:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 2076 = 165959596511964 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 2076 = (2519:ℝ)/1000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_2076
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 2077) ≤ val WuPaper.ClassicalFourthData.Bq 2077
    have hp : val WuPaper.ClassicalFourthData.Bq 2077 = (166008451734972:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 2077 = 166008451734972 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 2077 = (10077:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_2077
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 2078) ≤ val WuPaper.ClassicalFourthData.Bq 2078
    have hp : val WuPaper.ClassicalFourthData.Bq 2078 = (166057286515067:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 2078 = 166057286515067 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 2078 = (5039:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_2078
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 2079) ≤ val WuPaper.ClassicalFourthData.Bq 2079
    have hp : val WuPaper.ClassicalFourthData.Bq 2079 = (166106100861870:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 2079 = 166106100861870 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 2079 = (10079:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_2079
end WuPaper.ClassicalFourthConditions
#print axioms WuPaper.ClassicalFourthConditions.Log_block_129

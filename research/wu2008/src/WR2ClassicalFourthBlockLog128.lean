import WR2ClassicalFourthConditions
import WR2ClassicalFourthLogPoints128
noncomputable section
namespace WuPaper.ClassicalFourthConditions
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem Log_block_128 (j : Fin 16) (hj : 16*128+j.val < 10541) :
    WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 (16*128+j.val)) ≤ val WuPaper.ClassicalFourthData.Bq (16*128+j.val) := by
  fin_cases j
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 2048) ≤ val WuPaper.ClassicalFourthData.Bq 2048
    have hp : val WuPaper.ClassicalFourthData.Bq 2048 = (164583311209133:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 2048 = 164583311209133 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 2048 = (314:ℝ)/125 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_2048
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 2049) ≤ val WuPaper.ClassicalFourthData.Bq 2049
    have hp : val WuPaper.ClassicalFourthData.Bq 2049 = (164632742762419:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 2049 = 164632742762419 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 2049 = (10049:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_2049
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 2050) ≤ val WuPaper.ClassicalFourthData.Bq 2050
    have hp : val WuPaper.ClassicalFourthData.Bq 2050 = (164682153601139:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 2050 = 164682153601139 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 2050 = (201:ℝ)/80 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_2050
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 2051) ≤ val WuPaper.ClassicalFourthData.Bq 2051
    have hp : val WuPaper.ClassicalFourthData.Bq 2051 = (164731543735069:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 2051 = 164731543735069 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 2051 = (10051:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_2051
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 2052) ≤ val WuPaper.ClassicalFourthData.Bq 2052
    have hp : val WuPaper.ClassicalFourthData.Bq 2052 = (164780913173983:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 2052 = 164780913173983 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 2052 = (2513:ℝ)/1000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_2052
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 2053) ≤ val WuPaper.ClassicalFourthData.Bq 2053
    have hp : val WuPaper.ClassicalFourthData.Bq 2053 = (164830261927648:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 2053 = 164830261927648 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 2053 = (10053:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_2053
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 2054) ≤ val WuPaper.ClassicalFourthData.Bq 2054
    have hp : val WuPaper.ClassicalFourthData.Bq 2054 = (164879590005824:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 2054 = 164879590005824 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 2054 = (5027:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_2054
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 2055) ≤ val WuPaper.ClassicalFourthData.Bq 2055
    have hp : val WuPaper.ClassicalFourthData.Bq 2055 = (164928897418266:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 2055 = 164928897418266 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 2055 = (2011:ℝ)/800 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_2055
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 2056) ≤ val WuPaper.ClassicalFourthData.Bq 2056
    have hp : val WuPaper.ClassicalFourthData.Bq 2056 = (164978184174725:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 2056 = 164978184174725 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 2056 = (1257:ℝ)/500 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_2056
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 2057) ≤ val WuPaper.ClassicalFourthData.Bq 2057
    have hp : val WuPaper.ClassicalFourthData.Bq 2057 = (165027450284944:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 2057 = 165027450284944 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 2057 = (10057:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_2057
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 2058) ≤ val WuPaper.ClassicalFourthData.Bq 2058
    have hp : val WuPaper.ClassicalFourthData.Bq 2058 = (165076695758662:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 2058 = 165076695758662 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 2058 = (5029:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_2058
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 2059) ≤ val WuPaper.ClassicalFourthData.Bq 2059
    have hp : val WuPaper.ClassicalFourthData.Bq 2059 = (165125920605612:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 2059 = 165125920605612 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 2059 = (10059:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_2059
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 2060) ≤ val WuPaper.ClassicalFourthData.Bq 2060
    have hp : val WuPaper.ClassicalFourthData.Bq 2060 = (165175124835520:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 2060 = 165175124835520 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 2060 = (503:ℝ)/200 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_2060
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 2061) ≤ val WuPaper.ClassicalFourthData.Bq 2061
    have hp : val WuPaper.ClassicalFourthData.Bq 2061 = (165224308458109:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 2061 = 165224308458109 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 2061 = (10061:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_2061
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 2062) ≤ val WuPaper.ClassicalFourthData.Bq 2062
    have hp : val WuPaper.ClassicalFourthData.Bq 2062 = (165273471483094:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 2062 = 165273471483094 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 2062 = (5031:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_2062
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 2063) ≤ val WuPaper.ClassicalFourthData.Bq 2063
    have hp : val WuPaper.ClassicalFourthData.Bq 2063 = (165322613920185:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 2063 = 165322613920185 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 2063 = (10063:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_2063
end WuPaper.ClassicalFourthConditions
#print axioms WuPaper.ClassicalFourthConditions.Log_block_128

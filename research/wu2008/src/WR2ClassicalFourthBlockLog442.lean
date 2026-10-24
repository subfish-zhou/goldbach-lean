import WR2ClassicalFourthConditions
import WR2ClassicalFourthLogPoints442
noncomputable section
namespace WuPaper.ClassicalFourthConditions
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem Log_block_442 (j : Fin 16) (hj : 16*442+j.val < 10541) :
    WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 (16*442+j.val)) ≤ val WuPaper.ClassicalFourthData.Bq (16*442+j.val) := by
  fin_cases j
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 7072) ≤ val WuPaper.ClassicalFourthData.Bq 7072
    have hp : val WuPaper.ClassicalFourthData.Bq 7072 = (270203035497806:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 7072 = 270203035497806 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 7072 = (471:ℝ)/125 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_7072
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 7073) ≤ val WuPaper.ClassicalFourthData.Bq 7073
    have hp : val WuPaper.ClassicalFourthData.Bq 7073 = (270209076254598:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 7073 = 270209076254598 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 7073 = (15073:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_7073
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 7074) ≤ val WuPaper.ClassicalFourthData.Bq 7074
    have hp : val WuPaper.ClassicalFourthData.Bq 7074 = (270215114045693:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 7074 = 270215114045693 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 7074 = (7537:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_7074
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 7075) ≤ val WuPaper.ClassicalFourthData.Bq 7075
    have hp : val WuPaper.ClassicalFourthData.Bq 7075 = (270221148872072:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 7075 = 270221148872072 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 7075 = (603:ℝ)/160 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_7075
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 7076) ≤ val WuPaper.ClassicalFourthData.Bq 7076
    have hp : val WuPaper.ClassicalFourthData.Bq 7076 = (270227180734714:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 7076 = 270227180734714 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 7076 = (3769:ℝ)/1000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_7076
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 7077) ≤ val WuPaper.ClassicalFourthData.Bq 7077
    have hp : val WuPaper.ClassicalFourthData.Bq 7077 = (270233209634601:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 7077 = 270233209634601 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 7077 = (15077:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_7077
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 7078) ≤ val WuPaper.ClassicalFourthData.Bq 7078
    have hp : val WuPaper.ClassicalFourthData.Bq 7078 = (270239235572711:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 7078 = 270239235572711 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 7078 = (7539:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_7078
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 7079) ≤ val WuPaper.ClassicalFourthData.Bq 7079
    have hp : val WuPaper.ClassicalFourthData.Bq 7079 = (270245258550026:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 7079 = 270245258550026 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 7079 = (15079:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_7079
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 7080) ≤ val WuPaper.ClassicalFourthData.Bq 7080
    have hp : val WuPaper.ClassicalFourthData.Bq 7080 = (270251278567523:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 7080 = 270251278567523 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 7080 = (377:ℝ)/100 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_7080
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 7081) ≤ val WuPaper.ClassicalFourthData.Bq 7081
    have hp : val WuPaper.ClassicalFourthData.Bq 7081 = (270257295626182:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 7081 = 270257295626182 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 7081 = (15081:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_7081
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 7082) ≤ val WuPaper.ClassicalFourthData.Bq 7082
    have hp : val WuPaper.ClassicalFourthData.Bq 7082 = (270263309726982:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 7082 = 270263309726982 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 7082 = (7541:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_7082
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 7083) ≤ val WuPaper.ClassicalFourthData.Bq 7083
    have hp : val WuPaper.ClassicalFourthData.Bq 7083 = (270269320870899:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 7083 = 270269320870899 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 7083 = (15083:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_7083
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 7084) ≤ val WuPaper.ClassicalFourthData.Bq 7084
    have hp : val WuPaper.ClassicalFourthData.Bq 7084 = (270275329058913:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 7084 = 270275329058913 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 7084 = (3771:ℝ)/1000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_7084
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 7085) ≤ val WuPaper.ClassicalFourthData.Bq 7085
    have hp : val WuPaper.ClassicalFourthData.Bq 7085 = (270281334292000:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 7085 = 270281334292000 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 7085 = (3017:ℝ)/800 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_7085
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 7086) ≤ val WuPaper.ClassicalFourthData.Bq 7086
    have hp : val WuPaper.ClassicalFourthData.Bq 7086 = (270287336571137:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 7086 = 270287336571137 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 7086 = (7543:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_7086
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 7087) ≤ val WuPaper.ClassicalFourthData.Bq 7087
    have hp : val WuPaper.ClassicalFourthData.Bq 7087 = (270293335897301:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 7087 = 270293335897301 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 7087 = (15087:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_7087
end WuPaper.ClassicalFourthConditions
#print axioms WuPaper.ClassicalFourthConditions.Log_block_442

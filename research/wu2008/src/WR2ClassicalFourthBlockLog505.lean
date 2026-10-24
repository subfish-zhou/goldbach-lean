import WR2ClassicalFourthConditions
import WR2ClassicalFourthLogPoints505
noncomputable section
namespace WuPaper.ClassicalFourthConditions
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem Log_block_505 (j : Fin 16) (hj : 16*505+j.val < 10541) :
    WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 (16*505+j.val)) ≤ val WuPaper.ClassicalFourthData.Bq (16*505+j.val) := by
  fin_cases j
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 8080) ≤ val WuPaper.ClassicalFourthData.Bq 8080
    have hp : val WuPaper.ClassicalFourthData.Bq 8080 = (274939510295969:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 8080 = 274939510295969 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 8080 = (201:ℝ)/50 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_8080
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 8081) ≤ val WuPaper.ClassicalFourthData.Bq 8081
    have hp : val WuPaper.ClassicalFourthData.Bq 8081 = (274943003400425:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 8081 = 274943003400425 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 8081 = (16081:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_8081
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 8082) ≤ val WuPaper.ClassicalFourthData.Bq 8082
    have hp : val WuPaper.ClassicalFourthData.Bq 8082 = (274946494366295:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 8082 = 274946494366295 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 8082 = (8041:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_8082
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 8083) ≤ val WuPaper.ClassicalFourthData.Bq 8083
    have hp : val WuPaper.ClassicalFourthData.Bq 8083 = (274949983194259:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 8083 = 274949983194259 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 8083 = (16083:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_8083
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 8084) ≤ val WuPaper.ClassicalFourthData.Bq 8084
    have hp : val WuPaper.ClassicalFourthData.Bq 8084 = (274953469884998:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 8084 = 274953469884998 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 8084 = (4021:ℝ)/1000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_8084
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 8085) ≤ val WuPaper.ClassicalFourthData.Bq 8085
    have hp : val WuPaper.ClassicalFourthData.Bq 8085 = (274956954439193:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 8085 = 274956954439193 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 8085 = (3217:ℝ)/800 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_8085
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 8086) ≤ val WuPaper.ClassicalFourthData.Bq 8086
    have hp : val WuPaper.ClassicalFourthData.Bq 8086 = (274960436857523:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 8086 = 274960436857523 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 8086 = (8043:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_8086
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 8087) ≤ val WuPaper.ClassicalFourthData.Bq 8087
    have hp : val WuPaper.ClassicalFourthData.Bq 8087 = (274963917140670:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 8087 = 274963917140670 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 8087 = (16087:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_8087
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 8088) ≤ val WuPaper.ClassicalFourthData.Bq 8088
    have hp : val WuPaper.ClassicalFourthData.Bq 8088 = (274967395289312:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 8088 = 274967395289312 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 8088 = (2011:ℝ)/500 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_8088
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 8089) ≤ val WuPaper.ClassicalFourthData.Bq 8089
    have hp : val WuPaper.ClassicalFourthData.Bq 8089 = (274970871304130:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 8089 = 274970871304130 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 8089 = (16089:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_8089
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 8090) ≤ val WuPaper.ClassicalFourthData.Bq 8090
    have hp : val WuPaper.ClassicalFourthData.Bq 8090 = (274974345185802:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 8090 = 274974345185802 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 8090 = (1609:ℝ)/400 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_8090
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 8091) ≤ val WuPaper.ClassicalFourthData.Bq 8091
    have hp : val WuPaper.ClassicalFourthData.Bq 8091 = (274977816935008:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 8091 = 274977816935008 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 8091 = (16091:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_8091
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 8092) ≤ val WuPaper.ClassicalFourthData.Bq 8092
    have hp : val WuPaper.ClassicalFourthData.Bq 8092 = (274981286552427:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 8092 = 274981286552427 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 8092 = (4023:ℝ)/1000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_8092
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 8093) ≤ val WuPaper.ClassicalFourthData.Bq 8093
    have hp : val WuPaper.ClassicalFourthData.Bq 8093 = (274984754038737:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 8093 = 274984754038737 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 8093 = (16093:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_8093
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 8094) ≤ val WuPaper.ClassicalFourthData.Bq 8094
    have hp : val WuPaper.ClassicalFourthData.Bq 8094 = (274988219394616:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 8094 = 274988219394616 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 8094 = (8047:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_8094
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 8095) ≤ val WuPaper.ClassicalFourthData.Bq 8095
    have hp : val WuPaper.ClassicalFourthData.Bq 8095 = (274991682620742:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 8095 = 274991682620742 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 8095 = (3219:ℝ)/800 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_8095
end WuPaper.ClassicalFourthConditions
#print axioms WuPaper.ClassicalFourthConditions.Log_block_505

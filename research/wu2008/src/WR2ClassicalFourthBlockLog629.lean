import WR2ClassicalFourthConditions
import WR2ClassicalFourthLogPoints629
noncomputable section
namespace WuPaper.ClassicalFourthConditions
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem Log_block_629 (j : Fin 16) (hj : 16*629+j.val < 10541) :
    WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 (16*629+j.val)) ≤ val WuPaper.ClassicalFourthData.Bq (16*629+j.val) := by
  fin_cases j
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 10064) ≤ val WuPaper.ClassicalFourthData.Bq 10064
    have hp : val WuPaper.ClassicalFourthData.Bq 10064 = (278415407424292:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 10064 = 278415407424292 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 10064 = (1129:ℝ)/250 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_10064
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 10065) ≤ val WuPaper.ClassicalFourthData.Bq 10065
    have hp : val WuPaper.ClassicalFourthData.Bq 10065 = (278415738926601:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 10065 = 278415738926601 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 10065 = (3613:ℝ)/800 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_10065
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 10066) ≤ val WuPaper.ClassicalFourthData.Bq 10066
    have hp : val WuPaper.ClassicalFourthData.Bq 10066 = (278416069272984:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 10066 = 278416069272984 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 10066 = (9033:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_10066
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 10067) ≤ val WuPaper.ClassicalFourthData.Bq 10067
    have hp : val WuPaper.ClassicalFourthData.Bq 10067 = (278416398463791:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 10067 = 278416398463791 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 10067 = (18067:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_10067
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 10068) ≤ val WuPaper.ClassicalFourthData.Bq 10068
    have hp : val WuPaper.ClassicalFourthData.Bq 10068 = (278416726499373:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 10068 = 278416726499373 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 10068 = (4517:ℝ)/1000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_10068
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 10069) ≤ val WuPaper.ClassicalFourthData.Bq 10069
    have hp : val WuPaper.ClassicalFourthData.Bq 10069 = (278417053380081:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 10069 = 278417053380081 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 10069 = (18069:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_10069
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 10070) ≤ val WuPaper.ClassicalFourthData.Bq 10070
    have hp : val WuPaper.ClassicalFourthData.Bq 10070 = (278417379106266:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 10070 = 278417379106266 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 10070 = (1807:ℝ)/400 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_10070
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 10071) ≤ val WuPaper.ClassicalFourthData.Bq 10071
    have hp : val WuPaper.ClassicalFourthData.Bq 10071 = (278417703678279:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 10071 = 278417703678279 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 10071 = (18071:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_10071
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 10072) ≤ val WuPaper.ClassicalFourthData.Bq 10072
    have hp : val WuPaper.ClassicalFourthData.Bq 10072 = (278418027096469:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 10072 = 278418027096469 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 10072 = (2259:ℝ)/500 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_10072
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 10073) ≤ val WuPaper.ClassicalFourthData.Bq 10073
    have hp : val WuPaper.ClassicalFourthData.Bq 10073 = (278418349361187:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 10073 = 278418349361187 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 10073 = (18073:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_10073
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 10074) ≤ val WuPaper.ClassicalFourthData.Bq 10074
    have hp : val WuPaper.ClassicalFourthData.Bq 10074 = (278418670472784:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 10074 = 278418670472784 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 10074 = (9037:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_10074
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 10075) ≤ val WuPaper.ClassicalFourthData.Bq 10075
    have hp : val WuPaper.ClassicalFourthData.Bq 10075 = (278418990431610:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 10075 = 278418990431610 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 10075 = (723:ℝ)/160 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_10075
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 10076) ≤ val WuPaper.ClassicalFourthData.Bq 10076
    have hp : val WuPaper.ClassicalFourthData.Bq 10076 = (278419309238015:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 10076 = 278419309238015 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 10076 = (4519:ℝ)/1000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_10076
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 10077) ≤ val WuPaper.ClassicalFourthData.Bq 10077
    have hp : val WuPaper.ClassicalFourthData.Bq 10077 = (278419626892348:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 10077 = 278419626892348 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 10077 = (18077:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_10077
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 10078) ≤ val WuPaper.ClassicalFourthData.Bq 10078
    have hp : val WuPaper.ClassicalFourthData.Bq 10078 = (278419943394960:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 10078 = 278419943394960 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 10078 = (9039:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_10078
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 10079) ≤ val WuPaper.ClassicalFourthData.Bq 10079
    have hp : val WuPaper.ClassicalFourthData.Bq 10079 = (278420258746200:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 10079 = 278420258746200 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 10079 = (18079:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_10079
end WuPaper.ClassicalFourthConditions
#print axioms WuPaper.ClassicalFourthConditions.Log_block_629

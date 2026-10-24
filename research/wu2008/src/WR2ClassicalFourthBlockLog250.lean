import WR2ClassicalFourthConditions
import WR2ClassicalFourthLogPoints250
noncomputable section
namespace WuPaper.ClassicalFourthConditions
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem Log_block_250 (j : Fin 16) (hj : 16*250+j.val < 10541) :
    WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 (16*250+j.val)) ≤ val WuPaper.ClassicalFourthData.Bq (16*250+j.val) := by
  fin_cases j
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 4000) ≤ val WuPaper.ClassicalFourthData.Bq 4000
    have hp : val WuPaper.ClassicalFourthData.Bq 4000 = (231049060186649:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 4000 = 231049060186649 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 4000 = (3:ℝ)/1 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_4000
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 4001) ≤ val WuPaper.ClassicalFourthData.Bq 4001
    have hp : val WuPaper.ClassicalFourthData.Bq 4001 = (231071468293675:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 4001 = 231071468293675 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 4001 = (12001:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_4001
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 4002) ≤ val WuPaper.ClassicalFourthData.Bq 4002
    have hp : val WuPaper.ClassicalFourthData.Bq 4002 = (231093867460475:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 4002 = 231093867460475 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 4002 = (6001:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_4002
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 4003) ≤ val WuPaper.ClassicalFourthData.Bq 4003
    have hp : val WuPaper.ClassicalFourthData.Bq 4003 = (231116257690584:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 4003 = 231116257690584 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 4003 = (12003:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_4003
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 4004) ≤ val WuPaper.ClassicalFourthData.Bq 4004
    have hp : val WuPaper.ClassicalFourthData.Bq 4004 = (231138638987537:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 4004 = 231138638987537 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 4004 = (3001:ℝ)/1000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_4004
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 4005) ≤ val WuPaper.ClassicalFourthData.Bq 4005
    have hp : val WuPaper.ClassicalFourthData.Bq 4005 = (231161011354865:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 4005 = 231161011354865 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 4005 = (2401:ℝ)/800 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_4005
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 4006) ≤ val WuPaper.ClassicalFourthData.Bq 4006
    have hp : val WuPaper.ClassicalFourthData.Bq 4006 = (231183374796100:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 4006 = 231183374796100 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 4006 = (6003:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_4006
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 4007) ≤ val WuPaper.ClassicalFourthData.Bq 4007
    have hp : val WuPaper.ClassicalFourthData.Bq 4007 = (231205729314769:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 4007 = 231205729314769 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 4007 = (12007:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_4007
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 4008) ≤ val WuPaper.ClassicalFourthData.Bq 4008
    have hp : val WuPaper.ClassicalFourthData.Bq 4008 = (231228074914401:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 4008 = 231228074914401 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 4008 = (1501:ℝ)/500 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_4008
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 4009) ≤ val WuPaper.ClassicalFourthData.Bq 4009
    have hp : val WuPaper.ClassicalFourthData.Bq 4009 = (231250411598520:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 4009 = 231250411598520 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 4009 = (12009:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_4009
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 4010) ≤ val WuPaper.ClassicalFourthData.Bq 4010
    have hp : val WuPaper.ClassicalFourthData.Bq 4010 = (231272739370651:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 4010 = 231272739370651 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 4010 = (1201:ℝ)/400 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_4010
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 4011) ≤ val WuPaper.ClassicalFourthData.Bq 4011
    have hp : val WuPaper.ClassicalFourthData.Bq 4011 = (231295058234315:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 4011 = 231295058234315 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 4011 = (12011:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_4011
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 4012) ≤ val WuPaper.ClassicalFourthData.Bq 4012
    have hp : val WuPaper.ClassicalFourthData.Bq 4012 = (231317368193035:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 4012 = 231317368193035 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 4012 = (3003:ℝ)/1000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_4012
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 4013) ≤ val WuPaper.ClassicalFourthData.Bq 4013
    have hp : val WuPaper.ClassicalFourthData.Bq 4013 = (231339669250327:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 4013 = 231339669250327 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 4013 = (12013:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_4013
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 4014) ≤ val WuPaper.ClassicalFourthData.Bq 4014
    have hp : val WuPaper.ClassicalFourthData.Bq 4014 = (231361961409710:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 4014 = 231361961409710 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 4014 = (6007:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_4014
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 4015) ≤ val WuPaper.ClassicalFourthData.Bq 4015
    have hp : val WuPaper.ClassicalFourthData.Bq 4015 = (231384244674699:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 4015 = 231384244674699 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 4015 = (2403:ℝ)/800 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_4015
end WuPaper.ClassicalFourthConditions
#print axioms WuPaper.ClassicalFourthConditions.Log_block_250

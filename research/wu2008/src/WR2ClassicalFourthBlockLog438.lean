import WR2ClassicalFourthConditions
import WR2ClassicalFourthLogPoints438
noncomputable section
namespace WuPaper.ClassicalFourthConditions
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem Log_block_438 (j : Fin 16) (hj : 16*438+j.val < 10541) :
    WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 (16*438+j.val)) ≤ val WuPaper.ClassicalFourthData.Bq (16*438+j.val) := by
  fin_cases j
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 7008) ≤ val WuPaper.ClassicalFourthData.Bq 7008
    have hp : val WuPaper.ClassicalFourthData.Bq 7008 = (269810213238636:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 7008 = 269810213238636 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 7008 = (469:ℝ)/125 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_7008
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 7009) ≤ val WuPaper.ClassicalFourthData.Bq 7009
    have hp : val WuPaper.ClassicalFourthData.Bq 7009 = (269816445857456:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 7009 = 269816445857456 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 7009 = (15009:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_7009
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 7010) ≤ val WuPaper.ClassicalFourthData.Bq 7010
    have hp : val WuPaper.ClassicalFourthData.Bq 7010 = (269822675447026:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 7010 = 269822675447026 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 7010 = (1501:ℝ)/400 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_7010
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 7011) ≤ val WuPaper.ClassicalFourthData.Bq 7011
    have hp : val WuPaper.ClassicalFourthData.Bq 7011 = (269828902008348:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 7011 = 269828902008348 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 7011 = (15011:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_7011
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 7012) ≤ val WuPaper.ClassicalFourthData.Bq 7012
    have hp : val WuPaper.ClassicalFourthData.Bq 7012 = (269835125542429:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 7012 = 269835125542429 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 7012 = (3753:ℝ)/1000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_7012
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 7013) ≤ val WuPaper.ClassicalFourthData.Bq 7013
    have hp : val WuPaper.ClassicalFourthData.Bq 7013 = (269841346050272:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 7013 = 269841346050272 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 7013 = (15013:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_7013
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 7014) ≤ val WuPaper.ClassicalFourthData.Bq 7014
    have hp : val WuPaper.ClassicalFourthData.Bq 7014 = (269847563532881:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 7014 = 269847563532881 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 7014 = (7507:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_7014
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 7015) ≤ val WuPaper.ClassicalFourthData.Bq 7015
    have hp : val WuPaper.ClassicalFourthData.Bq 7015 = (269853777991258:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 7015 = 269853777991258 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 7015 = (3003:ℝ)/800 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_7015
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 7016) ≤ val WuPaper.ClassicalFourthData.Bq 7016
    have hp : val WuPaper.ClassicalFourthData.Bq 7016 = (269859989426407:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 7016 = 269859989426407 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 7016 = (1877:ℝ)/500 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_7016
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 7017) ≤ val WuPaper.ClassicalFourthData.Bq 7017
    have hp : val WuPaper.ClassicalFourthData.Bq 7017 = (269866197839331:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 7017 = 269866197839331 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 7017 = (15017:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_7017
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 7018) ≤ val WuPaper.ClassicalFourthData.Bq 7018
    have hp : val WuPaper.ClassicalFourthData.Bq 7018 = (269872403231031:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 7018 = 269872403231031 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 7018 = (7509:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_7018
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 7019) ≤ val WuPaper.ClassicalFourthData.Bq 7019
    have hp : val WuPaper.ClassicalFourthData.Bq 7019 = (269878605602509:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 7019 = 269878605602509 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 7019 = (15019:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_7019
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 7020) ≤ val WuPaper.ClassicalFourthData.Bq 7020
    have hp : val WuPaper.ClassicalFourthData.Bq 7020 = (269884804954767:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 7020 = 269884804954767 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 7020 = (751:ℝ)/200 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_7020
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 7021) ≤ val WuPaper.ClassicalFourthData.Bq 7021
    have hp : val WuPaper.ClassicalFourthData.Bq 7021 = (269891001288806:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 7021 = 269891001288806 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 7021 = (15021:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_7021
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 7022) ≤ val WuPaper.ClassicalFourthData.Bq 7022
    have hp : val WuPaper.ClassicalFourthData.Bq 7022 = (269897194605625:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 7022 = 269897194605625 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 7022 = (7511:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_7022
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 7023) ≤ val WuPaper.ClassicalFourthData.Bq 7023
    have hp : val WuPaper.ClassicalFourthData.Bq 7023 = (269903384906227:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 7023 = 269903384906227 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 7023 = (15023:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_7023
end WuPaper.ClassicalFourthConditions
#print axioms WuPaper.ClassicalFourthConditions.Log_block_438

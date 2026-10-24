import WR2ClassicalFourthConditions
import WR2ClassicalFourthLogPoints550
noncomputable section
namespace WuPaper.ClassicalFourthConditions
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem Log_block_550 (j : Fin 16) (hj : 16*550+j.val < 10541) :
    WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 (16*550+j.val)) ≤ val WuPaper.ClassicalFourthData.Bq (16*550+j.val) := by
  fin_cases j
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 8800) ≤ val WuPaper.ClassicalFourthData.Bq 8800
    have hp : val WuPaper.ClassicalFourthData.Bq 8800 = (276940669004301:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 8800 = 276940669004301 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 8800 = (21:ℝ)/5 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_8800
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 8801) ≤ val WuPaper.ClassicalFourthData.Bq 8801
    have hp : val WuPaper.ClassicalFourthData.Bq 8801 = (276942784778641:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 8801 = 276942784778641 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 8801 = (16801:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_8801
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 8802) ≤ val WuPaper.ClassicalFourthData.Bq 8802
    have hp : val WuPaper.ClassicalFourthData.Bq 8802 = (276944898848315:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 8802 = 276944898848315 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 8802 = (8401:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_8802
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 8803) ≤ val WuPaper.ClassicalFourthData.Bq 8803
    have hp : val WuPaper.ClassicalFourthData.Bq 8803 = (276947011213855:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 8803 = 276947011213855 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 8803 = (16803:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_8803
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 8804) ≤ val WuPaper.ClassicalFourthData.Bq 8804
    have hp : val WuPaper.ClassicalFourthData.Bq 8804 = (276949121875791:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 8804 = 276949121875791 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 8804 = (4201:ℝ)/1000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_8804
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 8805) ≤ val WuPaper.ClassicalFourthData.Bq 8805
    have hp : val WuPaper.ClassicalFourthData.Bq 8805 = (276951230834655:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 8805 = 276951230834655 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 8805 = (3361:ℝ)/800 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_8805
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 8806) ≤ val WuPaper.ClassicalFourthData.Bq 8806
    have hp : val WuPaper.ClassicalFourthData.Bq 8806 = (276953338090977:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 8806 = 276953338090977 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 8806 = (8403:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_8806
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 8807) ≤ val WuPaper.ClassicalFourthData.Bq 8807
    have hp : val WuPaper.ClassicalFourthData.Bq 8807 = (276955443645288:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 8807 = 276955443645288 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 8807 = (16807:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_8807
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 8808) ≤ val WuPaper.ClassicalFourthData.Bq 8808
    have hp : val WuPaper.ClassicalFourthData.Bq 8808 = (276957547498117:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 8808 = 276957547498117 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 8808 = (2101:ℝ)/500 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_8808
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 8809) ≤ val WuPaper.ClassicalFourthData.Bq 8809
    have hp : val WuPaper.ClassicalFourthData.Bq 8809 = (276959649649997:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 8809 = 276959649649997 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 8809 = (16809:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_8809
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 8810) ≤ val WuPaper.ClassicalFourthData.Bq 8810
    have hp : val WuPaper.ClassicalFourthData.Bq 8810 = (276961750101455:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 8810 = 276961750101455 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 8810 = (1681:ℝ)/400 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_8810
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 8811) ≤ val WuPaper.ClassicalFourthData.Bq 8811
    have hp : val WuPaper.ClassicalFourthData.Bq 8811 = (276963848853023:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 8811 = 276963848853023 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 8811 = (16811:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_8811
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 8812) ≤ val WuPaper.ClassicalFourthData.Bq 8812
    have hp : val WuPaper.ClassicalFourthData.Bq 8812 = (276965945905230:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 8812 = 276965945905230 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 8812 = (4203:ℝ)/1000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_8812
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 8813) ≤ val WuPaper.ClassicalFourthData.Bq 8813
    have hp : val WuPaper.ClassicalFourthData.Bq 8813 = (276968041258605:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 8813 = 276968041258605 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 8813 = (16813:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_8813
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 8814) ≤ val WuPaper.ClassicalFourthData.Bq 8814
    have hp : val WuPaper.ClassicalFourthData.Bq 8814 = (276970134913678:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 8814 = 276970134913678 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 8814 = (8407:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_8814
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 8815) ≤ val WuPaper.ClassicalFourthData.Bq 8815
    have hp : val WuPaper.ClassicalFourthData.Bq 8815 = (276972226870978:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 8815 = 276972226870978 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 8815 = (3363:ℝ)/800 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_8815
end WuPaper.ClassicalFourthConditions
#print axioms WuPaper.ClassicalFourthConditions.Log_block_550

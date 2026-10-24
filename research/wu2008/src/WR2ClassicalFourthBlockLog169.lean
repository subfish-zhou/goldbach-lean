import WR2ClassicalFourthConditions
import WR2ClassicalFourthLogPoints169
noncomputable section
namespace WuPaper.ClassicalFourthConditions
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem Log_block_169 (j : Fin 16) (hj : 16*169+j.val < 10541) :
    WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 (16*169+j.val)) ≤ val WuPaper.ClassicalFourthData.Bq (16*169+j.val) := by
  fin_cases j
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 2704) ≤ val WuPaper.ClassicalFourthData.Bq 2704
    have hp : val WuPaper.ClassicalFourthData.Bq 2704 = (192978326629257:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 2704 = 192978326629257 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 2704 = (669:ℝ)/250 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_2704
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 2705) ≤ val WuPaper.ClassicalFourthData.Bq 2705
    have hp : val WuPaper.ClassicalFourthData.Bq 2705 = (193016031990192:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 2705 = 193016031990192 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 2705 = (2141:ℝ)/800 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_2705
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 2706) ≤ val WuPaper.ClassicalFourthData.Bq 2706
    have hp : val WuPaper.ClassicalFourthData.Bq 2706 = (193053721996693:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 2706 = 193053721996693 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 2706 = (5353:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_2706
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 2707) ≤ val WuPaper.ClassicalFourthData.Bq 2707
    have hp : val WuPaper.ClassicalFourthData.Bq 2707 = (193091396655538:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 2707 = 193091396655538 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 2707 = (10707:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_2707
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 2708) ≤ val WuPaper.ClassicalFourthData.Bq 2708
    have hp : val WuPaper.ClassicalFourthData.Bq 2708 = (193129055973505:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 2708 = 193129055973505 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 2708 = (2677:ℝ)/1000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_2708
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 2709) ≤ val WuPaper.ClassicalFourthData.Bq 2709
    have hp : val WuPaper.ClassicalFourthData.Bq 2709 = (193166699957367:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 2709 = 193166699957367 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 2709 = (10709:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_2709
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 2710) ≤ val WuPaper.ClassicalFourthData.Bq 2710
    have hp : val WuPaper.ClassicalFourthData.Bq 2710 = (193204328613894:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 2710 = 193204328613894 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 2710 = (1071:ℝ)/400 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_2710
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 2711) ≤ val WuPaper.ClassicalFourthData.Bq 2711
    have hp : val WuPaper.ClassicalFourthData.Bq 2711 = (193241941949851:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 2711 = 193241941949851 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 2711 = (10711:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_2711
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 2712) ≤ val WuPaper.ClassicalFourthData.Bq 2712
    have hp : val WuPaper.ClassicalFourthData.Bq 2712 = (193279539972000:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 2712 = 193279539972000 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 2712 = (1339:ℝ)/500 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_2712
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 2713) ≤ val WuPaper.ClassicalFourthData.Bq 2713
    have hp : val WuPaper.ClassicalFourthData.Bq 2713 = (193317122687100:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 2713 = 193317122687100 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 2713 = (10713:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_2713
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 2714) ≤ val WuPaper.ClassicalFourthData.Bq 2714
    have hp : val WuPaper.ClassicalFourthData.Bq 2714 = (193354690101906:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 2714 = 193354690101906 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 2714 = (5357:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_2714
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 2715) ≤ val WuPaper.ClassicalFourthData.Bq 2715
    have hp : val WuPaper.ClassicalFourthData.Bq 2715 = (193392242223168:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 2715 = 193392242223168 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 2715 = (2143:ℝ)/800 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_2715
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 2716) ≤ val WuPaper.ClassicalFourthData.Bq 2716
    have hp : val WuPaper.ClassicalFourthData.Bq 2716 = (193429779057635:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 2716 = 193429779057635 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 2716 = (2679:ℝ)/1000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_2716
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 2717) ≤ val WuPaper.ClassicalFourthData.Bq 2717
    have hp : val WuPaper.ClassicalFourthData.Bq 2717 = (193467300612051:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 2717 = 193467300612051 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 2717 = (10717:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_2717
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 2718) ≤ val WuPaper.ClassicalFourthData.Bq 2718
    have hp : val WuPaper.ClassicalFourthData.Bq 2718 = (193504806893156:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 2718 = 193504806893156 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 2718 = (5359:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_2718
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 2719) ≤ val WuPaper.ClassicalFourthData.Bq 2719
    have hp : val WuPaper.ClassicalFourthData.Bq 2719 = (193542297907687:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 2719 = 193542297907687 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 2719 = (10719:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_2719
end WuPaper.ClassicalFourthConditions
#print axioms WuPaper.ClassicalFourthConditions.Log_block_169

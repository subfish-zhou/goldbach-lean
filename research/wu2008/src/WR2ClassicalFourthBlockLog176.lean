import WR2ClassicalFourthConditions
import WR2ClassicalFourthLogPoints176
noncomputable section
namespace WuPaper.ClassicalFourthConditions
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem Log_block_176 (j : Fin 16) (hj : 16*176+j.val < 10541) :
    WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 (16*176+j.val)) ≤ val WuPaper.ClassicalFourthData.Bq (16*176+j.val) := by
  fin_cases j
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 2816) ≤ val WuPaper.ClassicalFourthData.Bq 2816
    have hp : val WuPaper.ClassicalFourthData.Bq 2816 = (197107406955298:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 2816 = 197107406955298 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 2816 = (338:ℝ)/125 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_2816
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 2817) ≤ val WuPaper.ClassicalFourthData.Bq 2817
    have hp : val WuPaper.ClassicalFourthData.Bq 2817 = (197143433950544:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 2817 = 197143433950544 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 2817 = (10817:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_2817
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 2818) ≤ val WuPaper.ClassicalFourthData.Bq 2818
    have hp : val WuPaper.ClassicalFourthData.Bq 2818 = (197179446328646:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 2818 = 197179446328646 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 2818 = (5409:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_2818
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 2819) ≤ val WuPaper.ClassicalFourthData.Bq 2819
    have hp : val WuPaper.ClassicalFourthData.Bq 2819 = (197215444095989:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 2819 = 197215444095989 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 2819 = (10819:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_2819
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 2820) ≤ val WuPaper.ClassicalFourthData.Bq 2820
    have hp : val WuPaper.ClassicalFourthData.Bq 2820 = (197251427258958:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 2820 = 197251427258958 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 2820 = (541:ℝ)/200 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_2820
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 2821) ≤ val WuPaper.ClassicalFourthData.Bq 2821
    have hp : val WuPaper.ClassicalFourthData.Bq 2821 = (197287395823932:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 2821 = 197287395823932 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 2821 = (10821:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_2821
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 2822) ≤ val WuPaper.ClassicalFourthData.Bq 2822
    have hp : val WuPaper.ClassicalFourthData.Bq 2822 = (197323349797289:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 2822 = 197323349797289 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 2822 = (5411:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_2822
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 2823) ≤ val WuPaper.ClassicalFourthData.Bq 2823
    have hp : val WuPaper.ClassicalFourthData.Bq 2823 = (197359289185400:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 2823 = 197359289185400 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 2823 = (10823:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_2823
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 2824) ≤ val WuPaper.ClassicalFourthData.Bq 2824
    have hp : val WuPaper.ClassicalFourthData.Bq 2824 = (197395213994637:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 2824 = 197395213994637 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 2824 = (1353:ℝ)/500 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_2824
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 2825) ≤ val WuPaper.ClassicalFourthData.Bq 2825
    have hp : val WuPaper.ClassicalFourthData.Bq 2825 = (197431124231366:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 2825 = 197431124231366 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 2825 = (433:ℝ)/160 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_2825
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 2826) ≤ val WuPaper.ClassicalFourthData.Bq 2826
    have hp : val WuPaper.ClassicalFourthData.Bq 2826 = (197467019901949:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 2826 = 197467019901949 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 2826 = (5413:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_2826
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 2827) ≤ val WuPaper.ClassicalFourthData.Bq 2827
    have hp : val WuPaper.ClassicalFourthData.Bq 2827 = (197502901012747:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 2827 = 197502901012747 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 2827 = (10827:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_2827
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 2828) ≤ val WuPaper.ClassicalFourthData.Bq 2828
    have hp : val WuPaper.ClassicalFourthData.Bq 2828 = (197538767570116:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 2828 = 197538767570116 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 2828 = (2707:ℝ)/1000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_2828
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 2829) ≤ val WuPaper.ClassicalFourthData.Bq 2829
    have hp : val WuPaper.ClassicalFourthData.Bq 2829 = (197574619580409:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 2829 = 197574619580409 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 2829 = (10829:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_2829
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 2830) ≤ val WuPaper.ClassicalFourthData.Bq 2830
    have hp : val WuPaper.ClassicalFourthData.Bq 2830 = (197610457049976:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 2830 = 197610457049976 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 2830 = (1083:ℝ)/400 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_2830
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 2831) ≤ val WuPaper.ClassicalFourthData.Bq 2831
    have hp : val WuPaper.ClassicalFourthData.Bq 2831 = (197646279985162:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 2831 = 197646279985162 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 2831 = (10831:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_2831
end WuPaper.ClassicalFourthConditions
#print axioms WuPaper.ClassicalFourthConditions.Log_block_176

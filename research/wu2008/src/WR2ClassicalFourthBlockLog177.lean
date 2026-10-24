import WR2ClassicalFourthConditions
import WR2ClassicalFourthLogPoints177
noncomputable section
namespace WuPaper.ClassicalFourthConditions
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem Log_block_177 (j : Fin 16) (hj : 16*177+j.val < 10541) :
    WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 (16*177+j.val)) ≤ val WuPaper.ClassicalFourthData.Bq (16*177+j.val) := by
  fin_cases j
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 2832) ≤ val WuPaper.ClassicalFourthData.Bq 2832
    have hp : val WuPaper.ClassicalFourthData.Bq 2832 = (197682088392311:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 2832 = 197682088392311 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 2832 = (677:ℝ)/250 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_2832
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 2833) ≤ val WuPaper.ClassicalFourthData.Bq 2833
    have hp : val WuPaper.ClassicalFourthData.Bq 2833 = (197717882277763:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 2833 = 197717882277763 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 2833 = (10833:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_2833
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 2834) ≤ val WuPaper.ClassicalFourthData.Bq 2834
    have hp : val WuPaper.ClassicalFourthData.Bq 2834 = (197753661647853:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 2834 = 197753661647853 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 2834 = (5417:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_2834
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 2835) ≤ val WuPaper.ClassicalFourthData.Bq 2835
    have hp : val WuPaper.ClassicalFourthData.Bq 2835 = (197789426508915:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 2835 = 197789426508915 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 2835 = (2167:ℝ)/800 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_2835
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 2836) ≤ val WuPaper.ClassicalFourthData.Bq 2836
    have hp : val WuPaper.ClassicalFourthData.Bq 2836 = (197825176867278:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 2836 = 197825176867278 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 2836 = (2709:ℝ)/1000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_2836
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 2837) ≤ val WuPaper.ClassicalFourthData.Bq 2837
    have hp : val WuPaper.ClassicalFourthData.Bq 2837 = (197860912729267:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 2837 = 197860912729267 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 2837 = (10837:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_2837
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 2838) ≤ val WuPaper.ClassicalFourthData.Bq 2838
    have hp : val WuPaper.ClassicalFourthData.Bq 2838 = (197896634101207:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 2838 = 197896634101207 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 2838 = (5419:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_2838
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 2839) ≤ val WuPaper.ClassicalFourthData.Bq 2839
    have hp : val WuPaper.ClassicalFourthData.Bq 2839 = (197932340989416:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 2839 = 197932340989416 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 2839 = (10839:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_2839
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 2840) ≤ val WuPaper.ClassicalFourthData.Bq 2840
    have hp : val WuPaper.ClassicalFourthData.Bq 2840 = (197968033400210:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 2840 = 197968033400210 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 2840 = (271:ℝ)/100 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_2840
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 2841) ≤ val WuPaper.ClassicalFourthData.Bq 2841
    have hp : val WuPaper.ClassicalFourthData.Bq 2841 = (198003711339903:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 2841 = 198003711339903 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 2841 = (10841:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_2841
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 2842) ≤ val WuPaper.ClassicalFourthData.Bq 2842
    have hp : val WuPaper.ClassicalFourthData.Bq 2842 = (198039374814803:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 2842 = 198039374814803 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 2842 = (5421:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_2842
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 2843) ≤ val WuPaper.ClassicalFourthData.Bq 2843
    have hp : val WuPaper.ClassicalFourthData.Bq 2843 = (198075023831217:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 2843 = 198075023831217 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 2843 = (10843:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_2843
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 2844) ≤ val WuPaper.ClassicalFourthData.Bq 2844
    have hp : val WuPaper.ClassicalFourthData.Bq 2844 = (198110658395447:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 2844 = 198110658395447 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 2844 = (2711:ℝ)/1000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_2844
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 2845) ≤ val WuPaper.ClassicalFourthData.Bq 2845
    have hp : val WuPaper.ClassicalFourthData.Bq 2845 = (198146278513794:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 2845 = 198146278513794 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 2845 = (2169:ℝ)/800 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_2845
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 2846) ≤ val WuPaper.ClassicalFourthData.Bq 2846
    have hp : val WuPaper.ClassicalFourthData.Bq 2846 = (198181884192552:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 2846 = 198181884192552 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 2846 = (5423:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_2846
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 2847) ≤ val WuPaper.ClassicalFourthData.Bq 2847
    have hp : val WuPaper.ClassicalFourthData.Bq 2847 = (198217475438015:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 2847 = 198217475438015 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 2847 = (10847:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_2847
end WuPaper.ClassicalFourthConditions
#print axioms WuPaper.ClassicalFourthConditions.Log_block_177

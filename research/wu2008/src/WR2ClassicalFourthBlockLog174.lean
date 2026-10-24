import WR2ClassicalFourthConditions
import WR2ClassicalFourthLogPoints174
noncomputable section
namespace WuPaper.ClassicalFourthConditions
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem Log_block_174 (j : Fin 16) (hj : 16*174+j.val < 10541) :
    WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 (16*174+j.val)) ≤ val WuPaper.ClassicalFourthData.Bq (16*174+j.val) := by
  fin_cases j
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 2784) ≤ val WuPaper.ClassicalFourthData.Bq 2784
    have hp : val WuPaper.ClassicalFourthData.Bq 2784 = (195946786858202:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 2784 = 195946786858202 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 2784 = (337:ℝ)/125 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_2784
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 2785) ≤ val WuPaper.ClassicalFourthData.Bq 2785
    have hp : val WuPaper.ClassicalFourthData.Bq 2785 = (195983284994694:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 2785 = 195983284994694 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 2785 = (2157:ℝ)/800 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_2785
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 2786) ≤ val WuPaper.ClassicalFourthData.Bq 2786
    have hp : val WuPaper.ClassicalFourthData.Bq 2786 = (196019768307862:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 2786 = 196019768307862 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 2786 = (5393:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_2786
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 2787) ≤ val WuPaper.ClassicalFourthData.Bq 2787
    have hp : val WuPaper.ClassicalFourthData.Bq 2787 = (196056236804202:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 2787 = 196056236804202 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 2787 = (10787:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_2787
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 2788) ≤ val WuPaper.ClassicalFourthData.Bq 2788
    have hp : val WuPaper.ClassicalFourthData.Bq 2788 = (196092690490208:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 2788 = 196092690490208 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 2788 = (2697:ℝ)/1000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_2788
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 2789) ≤ val WuPaper.ClassicalFourthData.Bq 2789
    have hp : val WuPaper.ClassicalFourthData.Bq 2789 = (196129129372368:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 2789 = 196129129372368 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 2789 = (10789:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_2789
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 2790) ≤ val WuPaper.ClassicalFourthData.Bq 2790
    have hp : val WuPaper.ClassicalFourthData.Bq 2790 = (196165553457170:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 2790 = 196165553457170 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 2790 = (1079:ℝ)/400 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_2790
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 2791) ≤ val WuPaper.ClassicalFourthData.Bq 2791
    have hp : val WuPaper.ClassicalFourthData.Bq 2791 = (196201962751094:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 2791 = 196201962751094 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 2791 = (10791:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_2791
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 2792) ≤ val WuPaper.ClassicalFourthData.Bq 2792
    have hp : val WuPaper.ClassicalFourthData.Bq 2792 = (196238357260622:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 2792 = 196238357260622 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 2792 = (1349:ℝ)/500 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_2792
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 2793) ≤ val WuPaper.ClassicalFourthData.Bq 2793
    have hp : val WuPaper.ClassicalFourthData.Bq 2793 = (196274736992227:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 2793 = 196274736992227 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 2793 = (10793:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_2793
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 2794) ≤ val WuPaper.ClassicalFourthData.Bq 2794
    have hp : val WuPaper.ClassicalFourthData.Bq 2794 = (196311101952382:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 2794 = 196311101952382 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 2794 = (5397:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_2794
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 2795) ≤ val WuPaper.ClassicalFourthData.Bq 2795
    have hp : val WuPaper.ClassicalFourthData.Bq 2795 = (196347452147556:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 2795 = 196347452147556 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 2795 = (2159:ℝ)/800 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_2795
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 2796) ≤ val WuPaper.ClassicalFourthData.Bq 2796
    have hp : val WuPaper.ClassicalFourthData.Bq 2796 = (196383787584215:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 2796 = 196383787584215 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 2796 = (2699:ℝ)/1000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_2796
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 2797) ≤ val WuPaper.ClassicalFourthData.Bq 2797
    have hp : val WuPaper.ClassicalFourthData.Bq 2797 = (196420108268820:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 2797 = 196420108268820 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 2797 = (10797:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_2797
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 2798) ≤ val WuPaper.ClassicalFourthData.Bq 2798
    have hp : val WuPaper.ClassicalFourthData.Bq 2798 = (196456414207829:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 2798 = 196456414207829 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 2798 = (5399:ℝ)/2000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_2798
  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 2799) ≤ val WuPaper.ClassicalFourthData.Bq 2799
    have hp : val WuPaper.ClassicalFourthData.Bq 2799 = (196492705407698:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq 2799 = 196492705407698 := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 2799 = (10799:ℝ)/4000 := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_2799
end WuPaper.ClassicalFourthConditions
#print axioms WuPaper.ClassicalFourthConditions.Log_block_174
